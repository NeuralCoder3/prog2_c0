Load semantics.

Lemma terminalTerminated :
    forall (σ:State),
    terminal (Terminated σ).
Proof.
    intros.
    intros [c' H].
    inversion H.
Qed.

Goal forall l e σ,
let s := Assign l e in
    (exists σ', properTerm s σ σ') \/
    (exists s' σ', stuck s σ s' σ').
Proof.
  intros x e σ;cbn.
  destruct (R⟦ e ⟧ σ) eqn:He, (L⟦ x ⟧ σ) eqn:Hx;
  destruct σ as [ρ μ]. 
  2-4: 
    right; exists (Assign x e); exists (ρ,μ);
    apply BigStepEnd; intros [c' H];
    inversion H;subst; subst σ0; congruence.
  left.
  eexists. 
  eapply BigStepTrans.
  * apply AssignStep;now eassumption.
  * apply BigStepEnd. apply terminalTerminated.
Qed.

Goal forall σ,
    abortion (Abort) σ.
Proof.
    intros.
    eapply BigStepTrans;[constructor|apply BigStepEnd].
    intros [c H];inversion H.
Qed.

Import String.
Open Scope string.

Variable (S:Stmt).

Definition wp := Block
    [
        While (Binary Ge (LVal (Var "a")%string) (LVal(Var "b")%string))
        (* extra Block in Exercise *)
                (Assign (Var "a")%string (Binary Sub (LVal (Var "a")%string) (LVal (Var "b")%string)))
        ; S
    ].

    Print State.
    Print VarEnv.
    Print MemEnv.
(* Definition △ := 0. *)
Instance eqString : EqDec string.
constructor.
repeat decide equality.
Defined.


Definition ρ : VarEnv :=
    update
    (update (fun _ => None) "a" (Some 0))
    "b" (Some 1)
    . 
Definition μ : MemEnv :=
    update
    (update (fun _ => None) 0 (Some (Defined 42)))
    1 (Some (Defined 17))
    . 


Definition σ := (ρ,μ).

Goal exists T, ⟨ wp | σ ⟩ ⇓ T.
Proof.
eexists.
unfold wp.
eapply BigStepTrans.
 1: {
    apply SubstStep.
    apply WhileStep.
 }
eapply BigStepTrans.
 1: {
    apply SubstStep.
    apply IfTrueStep with (n:=1).
    all:admit.
 }
eapply BigStepTrans.
 1: {
    (* apply ExecStep. *)
    apply SubstStep. (* Not Exec as exec is going to <s,sig> not Terminal *)
    apply ExecStep.
    (* apply AssignStep. *)
    admit.
 }
eapply BigStepTrans.
 1: {
    apply ExecStep.