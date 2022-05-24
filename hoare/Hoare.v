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






Section Syntactic.

    Definition Property := Expr.

    Implicit Type (P Q:Property) (e:Expr) (s:Stmt) (x:LExpr).

    Fixpoint replace P e x {struct P} :=
        match P with
        | Binary o e1 e2 => Binary o (replace e1 e x) (replace e2 P x)
        | LVal l => if eqdec l x then e else P
        | _ => P
        end.

    Definition interpret P σ :=
        exists n, RExprEval P σ = Some (IntVal n) /\ n<>0.
    Notation "P ⟦ σ ⟧ " := (interpret P σ) (at level 70).
    Notation "P ⇒ Q" := (forall σ, P⟦σ⟧ -> Q⟦σ⟧) (at level 60).
    (* Notation "P ⟦ E ⌿ x ⟧" := (replace P E x) (at level 50). *)

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

    Ltac inv_subst H :=
        inversion H;subst;clear H.

    Lemma bigstep_terminal_inv σ σ':
    « σ » ⇓ « σ' » -> σ = σ'.
    Proof.
        intros H.
        inv_subst H.
        - reflexivity.
        - inversion H0.
    Qed.

    Lemma And_split P Q σ:
        P ⟦ σ ⟧ ->
        Q ⟦ σ ⟧ ->
        Binary And P Q ⟦ σ ⟧.
    Proof.
        intros [n [HP Hn]] [m [HQ Hm]].
        exists m;split;[|assumption];cbn.
        rewrite HP, HQ;cbn.
        destruct n;congruence.
    Qed.

    Scheme dep_elim_hoare := Induction for hoare Sort Prop.
    Scheme dep_elim_bigStep := Induction for bigStep Sort Prop.

    From Equations Require Import Equations.
    Derive Signature for bigStep.
    Derive Signature for step.

    Lemma abort_not_terminate σ:
        ~ ↯ ⇓ « σ ».
    Proof.
        intros H.
        inv_subst H.
        inversion H0.
    Qed.

    Derive NoConfusion for Conf.
    Derive NoConfusion for Stmt.

    (* define alternative bigstep semantic for easier proofs *)

    Lemma diverge_not_terminate σ σ':
        ~ ⟨ diverge | σ ⟩ ⇓ « σ' ».
    Proof.
    (* needs dep elim *)
    Admitted.

    Lemma bigstep_block_inv s B σ σ'':
     ⟨ Block (s::B) | σ ⟩ ⇓ « σ'' » ->
     exists σ', ⟨ s | σ ⟩ ⇓ « σ' » /\ 
        ⟨ Block B | σ' ⟩ ⇓ « σ'' ».
    Proof.
        intros H.
        inv_subst H.
        inv_subst H0. (* needs dep_elim *)
        - exists σ';split.
          + econstructor.
            eassumption.
            constructor.
            apply terminalTerminated.
          + assumption.
        - (* needs dep_elim *)
          admit.
        - apply abort_not_terminate in H1.
          contradict H1.
    Admitted.

    Lemma Not_expr e σ:
        R⟦ e ⟧ σ = Some (IntVal 0) ->
        Unary Not e ⟦ σ ⟧.
    Proof.
        intros H.
        exists 1;split;[|auto].
        cbn.
        rewrite H.
        cbn. reflexivity.
    Qed.


    Lemma partial_correctness P Q s:
        hoare P s Q ->
        forall σ, (P⟦σ⟧) ->
        forall σ', ⟨ s | σ ⟩ ⇓ « σ' » ->
        (Q⟦σ'⟧).
    Proof.
        induction 1;intros σ HP σ' HTerm.
        - enough (Q' ⟦ σ' ⟧).
          {
            now apply H0.
          }
          eapply IHhoare.
          1: apply (H σ HP).
          apply HTerm.
        - inv_subst HTerm.
          inv_subst H. subst σ0.
          apply bigstep_terminal_inv in H0 as <-.
          unfold interpret in *.
          induction P;destruct HP as [n [He Hn]].
          + exists n. now split.
          + admit.
          + admit.
          + unfold replace in He.
            destruct (eqdec l x) as [<-|].
            * assert(v=IntVal n) as ->.
              {
                enough (Some v = Some (IntVal n)) by now inv_subst H.
                rewrite <- H5, <- He.
                induction e;admit.
              }
              exists n.
              split.
              2: assumption.
              cbn.
              assert(L⟦l⟧ (ρ,μ {a↦n}) = L⟦l⟧ (ρ,μ)) as -> by admit.
              rewrite H6.
              unfold μmap.
              cbn.
              assert(lookup (μ {a ↦ n}) a = Some (Defined (IntVal n))) as -> by admit.
              reflexivity.
            * exists n.
              cbn in He.
              assert(exists b, L⟦ l ⟧ (ρ,μ) = Some b) as [b Hb].
              {
                destruct (L⟦ l ⟧ (ρ,μ)).
                - now exists a0.
                - inversion He.
              }
              cbn.
              admit.
              (* assert(L⟦l⟧ (ρ,μ {a↦v}) = L⟦l⟧ (ρ,μ)) as -> by admit.
              rewrite Hb.
              unfold μmap.
              cbn.
              assert(lookup (μ {a ↦ n}) a = Some (Defined (IntVal n))) as -> by admit. *)
        - inv_subst HTerm.
          inv_subst H0.
          inv_subst H1.
          inv_subst H0.
          + apply bigstep_block_inv in H2 as [σ'' [Hs HB]].
            apply And_split.
            * admit. (* needs dep elim *)
            * admit. (* after while false *)
          + inv_subst H2.
            inv_subst H0.
            apply bigstep_terminal_inv in H1 as <-.
            apply And_split.
            * assumption.
            * now apply Not_expr.
        - inv_subst HTerm.
          inv_subst H1.
          + eapply IHhoare1.
            2: eassumption.
            apply And_split.
            * assumption.
            * exists n;split;auto.
          + eapply IHhoare2.
            2: eassumption.
            apply And_split.
            * assumption.
            * now apply Not_expr.
        - inv_subst HTerm.
          inv_subst H.
          apply bigstep_terminal_inv in H0 as <-.
          assumption.
        - apply bigstep_block_inv in HTerm as [σ'' [Hs HB]].
          eapply IHhoare2.
          2: eassumption.
          eapply IHhoare1.
          1: apply HP.
          assumption.
        - inv_subst HTerm.
          inv_subst H0.
          inv_subst H1.
          inv_subst H0.
          + inv_subst H2.
            inv_subst H0.
            apply bigstep_terminal_inv in H1 as <-.
            assumption.
          + inv_subst H2.
            inv_subst H0.
            inv_subst H1.
            inversion H0.
        - inv_subst HTerm.
          inv_subst H.
          inv_subst H0.
          inv_subst H.
          + inv_subst H1.
            inv_subst H.
            apply bigstep_terminal_inv in H0 as <-.
            apply And_split.
            * assumption.
            * exists n;split;assumption.
          + apply diverge_not_terminate in H1.
            contradict H1.
    Qed.




    (* while with termination proof *)
    (* Lemma total_correctness P Q s σ:
        hoare P s Q ->
        P σ ->
        exists σ',
        ⟨ s | σ ⟩ ⇓ « σ' » /\
        Q σ'.
    Proof. *)

End Syntactic.