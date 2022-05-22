Require Import syntax.
Require Import semantics.
Require Import hoare.
Require Import List.
Import ListNotations.

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
    apply terminalAbortion.
Qed.

Import String.
Open Scope string.
    (* Definition does not work here *)

Section Exercise6_9.

    Definition W :=
            While (Binary Ge (LVal (Var "a")) (LVal(Var "b")))
            (* extra Block in Exercise *)
                    (Assign (Var "a") (Binary Sub (LVal (Var "a")) (LVal (Var "b"))))
            .

    Definition S :=
            If (Binary Eq (LVal (Var "a")) (Const (IntVal 8)))
                Abort
                (Assign (Var "b") (Const (IntVal 0))).

    Definition wp : Stmt := 
        (Block nil [W; S]).


    Definition ρ : VarEnv :=
        emptyEnv { "a" ↦ △} { "b" ↦ ○}.
    Definition μ : MemEnv :=
        emptyEnv { △ ↦ (Defined 42)} { ○ ↦ (Defined 17)}.


    Definition σ := ([ρ],μ).

    Goal abortion wp σ.
    Proof.
    unfold abortion, wp, W.
    do 13 try eapply BigStepTrans.
    - apply SubstStep.
      apply WhileStep.
    - apply SubstStep.
      apply IfTrueStep with (n:=1).
      2: easy.
      now vm_compute.
    - Fail do 2 (apply ExecStep). 
      (* Not Exec as exec is going to <s,sig> not Terminal *)
      apply SubstStep. 
      apply ExecStep.
      apply AssignStep.
      + now vm_compute.
      + now vm_compute.

      (* same as above for second while loop iteration *)
    - do 2 apply SubstStep.
      apply WhileStep.
    - do 2 apply SubstStep.
      apply IfTrueStep with (n:=1).
      2: easy.
      now vm_compute.
    - do 2 apply SubstStep. 
      apply ExecStep.
      apply AssignStep.
      + now vm_compute.
      + now vm_compute.
    
    - do 3 apply SubstStep.
      apply WhileStep.
    - do 3 apply SubstStep.
      apply IfFalseStep.
      vm_compute.
      reflexivity.

    (* now close all blocks after the while *)
    - do 2 apply SubstStep.
      apply ExecStep.
      apply EmptyStep.
    - apply SubstStep.
      apply ExecStep.
      apply EmptyStep.
    - apply ExecStep.
      apply EmptyStep.

    - unfold S.
      apply SubstStep.
      apply IfTrueStep with (n:=1).
      2: easy.
      now vm_compute.
    - (* after 12 small steps *)
      apply CrashStep.
      apply AbortStep.
    - apply BigStepEnd.
      apply terminalAbortion.
    Qed.

End Exercise6_9.