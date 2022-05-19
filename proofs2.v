Load semantics2.

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

(* Goal forall l e σ,
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
Qed. *)


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

    Definition wp := 
        [
            W;
            S
        ].


    Definition ρ1 : VarEnv :=
        (fun _ => None) [ "a" ↦ (Some △)] [ "b" ↦ (Some ○)].
    Definition μ1 : MemEnv :=
        (fun _ => None) [ △ ↦ (Some (Defined 42))] [ ○ ↦ (Some (Defined 17))].


    Definition σ := ([ρ1],μ1).

    Goal abortion wp σ.
    Proof.
    unfold abortion, wp, W.
    do 7 try eapply BigStepTrans.
    - apply WhileTrueStep with (n:=1).
      2: easy.
      now vm_compute.
    - apply AssignStep.
      + now vm_compute.
      + now vm_compute.
    - apply WhileTrueStep with (n:=1).
      2: easy.
      now vm_compute.
    - apply AssignStep.
      + now vm_compute.
      + now vm_compute.
    - apply WhileFalseStep.
      now vm_compute.
    - unfold S.
      apply IfTrueStep with (n:=1).
      + now vm_compute.
      + now vm_compute.
    - apply AbortStep.
    - apply BigStepEnd.
      apply terminalAbortion.
    Qed.

End Exercise6_9.