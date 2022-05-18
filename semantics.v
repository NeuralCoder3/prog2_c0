Load syntax.

Variant UndefVal :=
    | Undef
    | Defined (v:Val)
    .

Notation VarEnv := (VarT -> option Addr).
Notation MemEnv := (Addr -> option UndefVal).

(* Record State :=
    {
        var_assign: VarEnv;
        memory_assign: MemEnv
    }. *)
Definition State := (VarEnv * MemEnv)%type.

Implicit Type (ρ:VarEnv) (μ:MemEnv) (σ:State).

Load option_monad.

Definition lookupVar σ x :=
    let (ρ, μ) := σ in 
    a <- ρ x;;
    μ a.

Definition LExprEval (l:LExpr) (σ:State) : option Addr :=
    let (ρ,μ) := σ in
    match l with
    | Var x => ρ x
    end.
Definition evalOp (op:Op) (v1 v2:Val) : option Val :=
    None.
    (* match op,v1,v2 with
    | Add, Undef, Undef => Undef *)
Fixpoint ExprEval (e:Expr) (s:State) : option Val :=
    match e with 
    | Const c => ret c
    | LVal l => 
        let (ρ,μ) := s in
        a <- LExprEval l s;;
        uv <- μ a;;
        match uv with 
        | Undef => None
        | Defined v =>
            ret v
        end
    | Binary op e1 e2 =>
        v1 <- ExprEval e1 s;;
        v2 <- ExprEval e2 s;;
        evalOp op v1 v2
    end
    .


Variant Conf :=
    | Aborted
    | Terminated (s:State)
    | Running (smt:Stmt) (s:State)
    .


Class EqDec (A:Type) :=
    {eqdec:(forall (x y:A), {x = y} + {x<>y})}.

Definition update {A B} {Aeq:EqDec A} (f:A -> B) (x:A) (y:B) (x2:A) : B :=
        if @eqdec A Aeq x x2 then y else f x2.

Instance AddrEq : EqDec Addr.
    constructor.
    now decide equality.
Defined.


Notation RExprEval := ExprEval.

Notation "⟨ s | st ⟩" := (Running s st).
Notation "« st »" := (Terminated st).
Notation "R⟦ e ⟧ σ" := (ExprEval e σ) (at level 40).
Notation "L⟦ l ⟧ σ" := (LExprEval l σ) (at level 40).
Notation "↯" := (Aborted).
Coercion Terminated : State >-> Conf.
Definition bool_to_nat (b:bool) := 
    if b then 1 else 0.
Coercion bool_to_nat : bool >-> nat.
Coercion IntVal : nat >-> Val.
Coercion Defined : Val >-> UndefVal.
(* Coercion Some : UndefVal >-> (option UndefVal). *)

Reserved Notation "c1 ~> c2" (at level 50).
Inductive step : Conf -> Conf -> Prop :=
    | AssignStep l e ρ μ a v: 
        let σ := (ρ, μ) in
        R⟦e⟧σ = Some v ->
        L⟦l⟧σ = Some a ->
        ⟨ (Assign l e) | σ ⟩ ~> «(ρ, update μ a (Some (Defined v)))»
    | IfTrueStep e s1 s2 σ (n:nat) :
        R⟦e⟧σ = Some (n:Val) ->
        n <> 0 ->
        ⟨ (If e s1 s2) | σ ⟩ ~> ⟨ s1 | σ ⟩
    | IfFalseStep e s1 s2 σ :
        R⟦e⟧σ = Some (0:Val) ->
        ⟨ (If e s1 s2) | σ ⟩ ~> ⟨ s1 | σ ⟩
    | WhileStep e s σ (n:nat) :
        ⟨ (While e s) | σ ⟩ ~> ⟨ If e (Block [s; While e s]) (Block []) | σ ⟩
    | EmptyStep σ :
        ⟨ Block [] | σ ⟩ ~> « σ »
    | ExecStep s1 sr σ σ' :
        ⟨ s1 | σ ⟩ ~> « σ' » ->
        ⟨ Block (s1::sr) | σ ⟩ ~> ⟨ Block sr | σ' ⟩
    | SubstStep s1 s1' sr σ σ' :
        ⟨ s1 | σ ⟩ ~> ⟨ s1' | σ ⟩ ->
        ⟨ Block (s1::sr) | σ ⟩ ~> ⟨ Block (s1'::sr) | σ' ⟩
    | AbortStep σ :
        ⟨ Abort | σ ⟩ ~> ↯
    | CrashStep s1 sr σ :
        ⟨ s1 | σ ⟩ ~> ↯ ->
        ⟨ Block (s1::sr) | σ ⟩ ~> ↯
    where "c1 ~> c2" := (step c1 c2).

Inductive trace : list Conf -> Prop :=
    | TraceEmpty : trace []
    | TraceSingle (c:Conf) : trace [c]
    | TraceCons : forall (c c':Conf) cs,
        step c c' ->
        trace (c'::cs) ->
        trace (c::c'::cs).

Definition terminal (c:Conf) :=
    ~(exists (c':Conf), c ~> c').

Reserved Notation "conf1 ⇓ conf2" (at level 50).
Inductive bigStep : Conf -> Conf -> Prop :=
    | BigStepEnd (c1:Conf) :
        terminal c1 ->
        c1 ⇓ c1
    | BigStepTrans (c1 c2 c3:Conf):
        c1 ~> c2 ->
        c2 ⇓ c3 ->
        c1 ⇓ c3
    where "conf1 ⇓ conf2" := (bigStep conf1 conf2).

Definition properTerm s σ σ' :=
    ⟨ s | σ ⟩ ⇓ σ'.
Definition abortion s σ :=
    ⟨ s | σ ⟩ ⇓ ↯.
Definition stuck s σ s' σ' :=
    ⟨ s | σ ⟩ ⇓ ⟨ s' | σ' ⟩.


Lemma terminalTerminated :
    forall (σ:State),
    terminal (Terminated σ).
Proof.
    intros.
    intros [c' H].
    inversion H.
Qed.

Definition isWhile s :=
    match s with
    | While e s => True
    | _ => False
    end.

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

(* bigstep only for statement and conf *)
(* Reserved Notation "s , σ ⇓ conf" (at level 50).
Inductive bigStep (s:Stmt) σ : Conf -> Prop :=
    (* not necessary *)
    | BigStepEnd :
        (~exists (c2:Conf), step ⟨ s | σ ⟩ c2) ->
        s, σ ⇓ ⟨ s | σ ⟩
    | BigStepFinal (c1:Conf): 
        step ⟨ s | σ ⟩ c1 ->
        (~exists (c2:Conf), step c1 c2) ->
        s, σ ⇓ c1
    | BigStepTrans (c1):
        step ⟨ s | σ ⟩ c1 ->

    where "s , σ ⇓ conf" := (bigStep s σ conf).
 *)
