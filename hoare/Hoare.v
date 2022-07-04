Require Import Syntax.
Require Import Semantics.
Require Import util.
Require Import List.
Import ListNotations.

Instance LExprEq : EqDec LExpr.
    constructor.
    now repeat decide equality.
Defined.


Lemma terminalTerminated :
    forall (σ:State),
    terminal (Terminated σ).
Proof.
    intros.
    intros [c' H].
    inversion H.
Qed.

Lemma terminalAbortion :
    terminal ↯.
Proof.
    intros.
    intros [c' H].
    inversion H.
Qed.


From Equations Require Import Equations.
(* for easier dep induction *)
Require Import Coq.Program.Equality.

Section Syntactic.

    Definition Property := Expr.

    Implicit Type (P Q:Property) (e:Expr) (s:Stmt) (x:LExpr).

    Fixpoint replace P e x {struct P} :=
        match P with
        | Binary o e1 e2 => Binary o (replace e1 e x) (replace e2 e x)
        | Unary o e1 => Unary o (replace e1 e x)
        | LVal l => if eqdec l x then e else P
        | Const v => P
        end.

    Notation "P ⇒ Q" := (forall σ, σ ⊨ P -> σ ⊨ Q) (at level 60).

    Reserved Notation "{{ P }} s {{ Q }}" (at level 50).
    Inductive hoare : Property -> Stmt -> Property -> Prop :=
        | hoareConsequence P P' s Q Q':
            (P ⇒ P') ->
            (Q' ⇒ Q) ->
            {{P'}} s {{Q'}} ->
            {{P}} s {{Q}}
        | hoareAssign P x e: 
            {{ replace P e x }} (Assign x e) {{P}}
        | hoareWhile e s P Q:
            {{Binary And P e}} s {{P}} ->
            {{P}} While e s {{Binary And P (Unary Not e)}}
        | hoareIf b s1 s2 P Q:
            {{Binary And P b}} s1 {{Q}} ->
            {{Binary And P (Unary Not b)}} s2 {{Q}} ->
            {{P}} If b s1 s2 {{Q}}
        | hoareSkip P P:
            {{P}} Block [] {{P}}
        | hoareBlock s B P Q R:
            {{P}} s {{Q}} ->
            {{Q}} Block B {{R}} ->
            {{P}} Block (s::B) {{R}}
        | hoareAssert P e:
            (P ⇒ e) ->
            {{P}} (Assert e) {{P}}
        | hoareAssume P e:
            {{P}} (Assume e) {{Binary And P e}}
        where "{{ P }} s {{ Q }}" := (hoare P s Q).
    Notation "⊢ {{ P }} s {{ Q }}" := (hoare P s Q) (at level 50).
    Definition partial_correctness P s Q :=
        forall (σ:State),
        σ ⊨ P ->
        forall (c:Conf),
        ⟨ s | σ ⟩ ⇓B c ->
        c ⊨c Q.
    Notation "⊨ {{ P }} s {{ Q }}" := (partial_correctness P s Q) (at level 50).

    Ltac inv_subst H :=
        inversion H;subst;clear H.

    Derive Signature for properBigStep.
    Derive Signature for hoare.


    (* Lemma smallstep_bigstep_equiv s σ c:
        (bigStep ⟨s|σ⟩ c) ->
        (⟨s|σ⟩ ⇓B c).
    Abort. *)

    Lemma lookup_update {A B H} (μ:Env A B) a v:
      @lookup A B H (μ {a ↦ v}) a = Some v.
    Proof.
      unfold lookup, update.
      cbn. unfold eqb. destruct eqdec;auto;congruence.
    Qed.

    Lemma lookup_not_update {A B H} (μ:Env A B) a b v:
      a <> b ->
      @lookup A B H (μ {b ↦ v}) a = @lookup A B H (μ) a.
    Proof.
      intros Heq.
      unfold lookup, update.
      cbn. unfold eqb. destruct eqdec;congruence.
    Qed.

    (* should be formulated using fresh_var instead *)
    Variable (H_fresh_vars: forall (ρ:VarEnv) (x y:VarT) (a_x a_y:AddrT),
        x <> y ->
        lookup ρ x = Some a_x ->
        lookup ρ y = Some a_y ->
        a_x <> a_y
    ).

    Lemma replace_subst P e x ρ μ a v:
    let σ := (ρ, μ) in
      L⟦ x ⟧ σ = Some a ->
      R⟦ e ⟧ σ = Some v ->
      R⟦ replace P e x ⟧ σ = 
      R⟦ P ⟧ (ρ, μ {a ↦ v}).
    Proof.
    cbn.
      intros Hx He.
      induction P.
      1-3: cbn.
      - reflexivity. (* Const *)
      - now rewrite <- IHP1, <- IHP2. (* Binary *)
      - now rewrite <- IHP. (* Unary *)
      - cbn [replace].
        destruct (eqdec l x) as [-> | Hxl].
        + destruct x;cbn in *;unfold ρmap, μmap in *;cbn in *.
          rewrite He, Hx;cbn.
          now rewrite lookup_update;cbn.
        + destruct l,x;cbn in *;unfold ρmap, μmap in *;cbn in *.
          destruct (lookup _ v0) eqn: Hv;cbn;[|reflexivity].
          rewrite lookup_not_update.
          2: eapply H_fresh_vars;try eassumption;contradict Hxl;now subst.
          reflexivity.
    Qed.

    Lemma interp_and {σ a b}:
      σ ⊨ a ->
      σ ⊨ b ->
      σ ⊨ Binary And a b.
    Proof.
      intros [na [Ha Hna]] [nb [Hb Hnb]].
      exists (if match na with
            | 0 => true
            | S _ => false
            end then 0 else nb);cbn.
      rewrite Ha, Hb;cbn;split;auto.
      now destruct na, nb;auto.
    Qed.

    Lemma interp_interp_conf σ P:
      σ ⊨ P ->
      « σ » ⊨c P.
    Proof.
      intros H.
      now eexists.
    Qed.

    Lemma soundness P s Q:
        ⊢ {{ P }} s {{ Q }} ->
        ⊨ {{ P }} s {{ Q }}.
    Proof.
      intros H.
      induction H; intros σ HP c Hterm.
      - (* Consequence *)
        assert (σ ⊨ P') as HP' by now apply H.
        destruct (IHhoare _ HP' c Hterm) as [σ' [-> HQ']].
        apply interp_interp_conf;auto.
      - (* Assign *)
        depelim Hterm;try congruence.
        eexists;split;[reflexivity|].
        destruct HP as [np [Hp Hnp]].
        exists np;split;[|assumption].
        now erewrite <- replace_subst;eassumption.
      - (* While *)
        rename Hterm into HWhile.
        dependent induction HWhile;try congruence.
        + (* σ ⊨ e *)
          eapply IHHWhile2.
          all: try eauto.
          specialize (IHhoare _ (interp_and HP H0) _ HWhile1).
          destruct IHhoare as [? [[= <-] ?]].
          assumption.
        + (* σ ⊨ ~e *)
          exists σ;split;[reflexivity|];exists 1;split;[|auto];cbn.
          destruct HP as [np [-> Hnp]];cbn.
          destruct H0 as [ne [He Hne]];cbn.
          cbn in He.
          destruct (R⟦ e ⟧ σ) as [[|[]]|];cbn in *.
          all: try congruence.
          destruct np;tauto.
        + (* σ ⊨ e, s,σ ⇓ not_proper *)
          destruct c;cbn in *.
          2: contradict H0; now exists s0.
          (* specialize Hoare IH like above *)
          1-2: specialize (IHhoare _ (interp_and HP H1) _ HWhile);
          now destruct IHhoare as [? [[= <-] ?]].
      - (* If *)
        depelim Hterm.
        + eapply IHhoare1;[|eassumption].
          now apply interp_and.
        + eapply IHhoare2;[|eassumption].
          now apply interp_and.
      - (* Skip *)
        depelim Hterm. now apply interp_interp_conf.
      - (* Block *)
        depelim Hterm.
        + eapply IHhoare2;[|eassumption].
          enough (« σ' » ⊨c Q) by
            now destruct H1 as [? [[= ->] HQ]].
          eapply IHhoare1;eassumption.
        + exfalso.
          specialize (IHhoare1 _ HP _ Hterm).
          destruct c;cbn in *;firstorder.
      - (* Assert *)
        depelim Hterm. now apply interp_interp_conf.
      - (* Assume *)
        depelim Hterm. 
        now apply interp_interp_conf, interp_and.
    Qed.


End Syntactic.