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