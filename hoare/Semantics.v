Require Import String.
Require Import List.
Import ListNotations.
Require Import Syntax.
Require Import util.

Arguments Env dom codom : clear implicits.

Instance AddrTEq : EqDec AddrT.
    constructor.
    now repeat decide equality.
Defined.
Instance VarTEq : EqDec VarT.
    constructor.
    now repeat decide equality.
Defined.

Variant UndefVal :=
    | Undef
    | Defined (v:Val).

Notation VarEnv := (Env VarT AddrT).
Notation MemEnv := (Env AddrT UndefVal).

(* Record State :=
    {
        var_assign: VarEnv;
        memory_assign: MemEnv
    }. *)
Definition State := (VarEnv * MemEnv)%type.

Implicit Type (ρ:VarEnv) (ρs:list VarEnv) (μ:MemEnv) (σ:State).


Definition ρmap σ := lookup (fst σ).
Definition μmap σ := lookup (snd σ).

Definition lookupVar σ x :=
    a <- ρmap σ x;;
    μmap σ a.

Definition evalOp (op:Op) (v1 v2:Val) : option Val :=
    match op, v1,v2 with 
    | Add, IntVal i1, IntVal i2 => Some (IntVal (i1+i2))
    | Sub, IntVal i1, IntVal i2 => Some (IntVal (i1-i2))
    | Mul, IntVal i1, IntVal i2 => Some (IntVal (i1*i2))
    | Ge , IntVal i1, IntVal i2 => Some (IntVal (if Nat.leb i2 i1 then 1 else 0))
    | Eq , IntVal i1, IntVal i2 => Some (IntVal (if Nat.eqb i1 i2 then 1 else 0))
    | And, IntVal i1, IntVal i2 => Some (IntVal (if Nat.eqb 0 i1 then 0 else i2))
    | Lt , IntVal i1, IntVal i2 => Some (IntVal (if Nat.ltb i1 i2 then 1 else 0))
    | _, _, _ => None
    end.

Definition evalUOp (uop:UOp) (v1:Val) : option Val :=
    match uop, v1 with 
    | Not, IntVal i1 => Some (IntVal (if Nat.eqb 0 i1 then 1 else 0))
    | _, _ => None
    end.

Definition LExprEval (l:LExpr) (σ:State) : option AddrT :=
    match l with
    | Var x => ρmap σ x
    end.
Fixpoint RExprEval (e:Expr) (σ:State) : option Val :=
    match e with 
    | Const c => ret c
    | LVal l => 
        a <- LExprEval l σ;;
        uv <- μmap σ a;;
        match uv with 
        | Undef => None
        | Defined v =>
            ret v
        end
    | Binary op e1 e2 =>
        v1 <- RExprEval e1 σ;;
        v2 <- RExprEval e2 σ;;
        evalOp op v1 v2
    | Unary op e1 =>
        v1 <- RExprEval e1 σ;;
        evalUOp op v1
    end
    .


Variant Conf :=
    | Aborted
    | Terminated (s:State)
    | Running (smt:Stmt) (s:State)
    .

Notation "f { x ↦ y }" := (update f x y) (at level 10).

Notation "⟨ s | st ⟩" := (Running s st).
Notation "« st »" := (Terminated st).
Notation "R⟦ e ⟧ σ" := (RExprEval e σ) (at level 40).
Notation "L⟦ l ⟧ σ" := (LExprEval l σ) (at level 40).
Notation "↯" := (Aborted).
Coercion Terminated : State >-> Conf.
Definition bool_to_nat (b:bool) := 
    if b then 1 else 0.
Coercion bool_to_nat : bool >-> nat.
Coercion IntVal : nat >-> Val.
Coercion Defined : Val >-> UndefVal.

Definition diverge := While (Const 1) (Block []).

Reserved Notation "c1 ~> c2" (at level 50).
Inductive step : Conf -> Conf -> Prop :=
    | AssignStep l e ρ μ a v: 
        let σ := (ρ, μ) in
        R⟦e⟧σ = Some v ->
        L⟦l⟧σ = Some a ->
        ⟨ (Assign l e) | σ ⟩ ~> «(ρ, update μ a (Defined v))»
    | IfTrueStep e s1 s2 σ (n:nat) :
        R⟦e⟧σ = Some (n:Val) ->
        n <> 0 ->
        ⟨ (If e s1 s2) | σ ⟩ ~> ⟨ s1 | σ ⟩
    | IfFalseStep e s1 s2 σ :
        R⟦e⟧σ = Some (0:Val) ->
        ⟨ (If e s1 s2) | σ ⟩ ~> ⟨ s2 | σ ⟩
    | WhileStep e s σ :
        ⟨ (While e s) | σ ⟩ ~> ⟨ If e (Block [s; While e s]) (Block []) | σ ⟩
    | EmptyStep σ :
        ⟨ Block [] | σ ⟩ ~> « σ »
    | ExecStep s1 sr σ σ' :
        ⟨ s1 | σ ⟩ ~> « σ' » ->
        ⟨ Block (s1::sr) | σ ⟩ ~> ⟨ Block sr | σ' ⟩
    | SubstStep s1 s1' sr σ σ' :
        ⟨ s1 | σ ⟩ ~> ⟨ s1' | σ' ⟩ ->
        ⟨ Block (s1::sr) | σ ⟩ ~> ⟨ Block (s1'::sr) | σ' ⟩
    | AbortStep σ :
        ⟨ Abort | σ ⟩ ~> ↯
    | CrashStep s1 sr σ :
        ⟨ s1 | σ ⟩ ~> ↯ ->
        ⟨ Block (s1::sr) | σ ⟩ ~> ↯
    | AssertStep e σ:
        ⟨ Assert e | σ ⟩ ~> ⟨ If e (Block []) (Abort) | σ ⟩
    | AssumeStep e σ:
        ⟨ Assume e | σ ⟩ ~> ⟨ If e (Block []) (diverge) | σ ⟩
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
    ⟨ s | σ ⟩ ⇓ « σ' ».
Definition abortion s σ :=
    ⟨ s | σ ⟩ ⇓ ↯.
Definition stuck s σ s' σ' :=
    ⟨ s | σ ⟩ ⇓ ⟨ s' | σ' ⟩.

Definition interpret P σ :=
    exists n, RExprEval P σ = Some (IntVal n) /\ n<>0.
Notation "σ ⊨ P" := (interpret P σ) (at level 70).

Lemma interpret_neg : forall P σ,
    σ ⊨ (Unary Not P) <->
    RExprEval P σ = Some (IntVal 0).
Proof.
    intros. split.
    - intros [n [Hv Hn]].
      cbn in Hv.
      destruct (RExprEval P σ) as [[|[]]|];cbn in *;congruence.
    - intros H. exists 1.
      cbn; rewrite H;cbn.
      firstorder.
Qed.

Definition isProperTermBool c :=
    match c with
    | Terminated _ => true
    | _ => false
    end.
Definition isProperTerm c := exists σ, c = Terminated σ.

Reserved Notation "⟨ s | σ ⟩ ⇓B conf2" (at level 50).
Inductive properBigStep : Stmt -> State -> Conf -> Prop :=
    | BigStepAssume e σ :
        ⟨Assume e | σ⟩ ⇓B « σ »
    | BigStepAssert e σ :
        ⟨Assert e | σ⟩ ⇓B « σ »
    | BigStepBlock (s:Stmt) (sr:list Stmt) σ σ' c:
        ⟨s | σ⟩ ⇓B « σ' » ->
        ⟨Block sr | σ'⟩ ⇓B c ->
        ⟨Block (s::sr) | σ⟩ ⇓B c
    | BigStepEmptyBlock σ :
        ⟨Block [] | σ⟩ ⇓B « σ »
    | BigStepAssign l e ρ μ a v:
        let σ := (ρ, μ) in
        R⟦e⟧σ = Some v ->
        L⟦l⟧σ = Some a ->
        ⟨Assign l e | σ⟩ ⇓B «(ρ, update μ a (Defined v))»
    | BigStepIfTrue e s1 s2 σ (n:nat) c:
        σ ⊨ e ->
        ⟨s1 | σ⟩ ⇓B c ->
        ⟨If e s1 s2 | σ⟩ ⇓B c
    | BigStepIfFalse e s1 s2 σ c:
        σ ⊨ (Unary Not e) ->
        ⟨s2 | σ⟩ ⇓B c ->
        ⟨If e s1 s2 | σ⟩ ⇓B c
    | BigStepWhileTrue e s σ σ' c:
        σ ⊨ e ->
        ⟨s | σ⟩ ⇓B « σ' » ->
        ⟨While e s | σ'⟩ ⇓B c ->
        ⟨While e s | σ⟩ ⇓B c
    | BigStepWhileFalse e s σ:
        σ ⊨ (Unary Not e) ->
        ⟨While e s | σ⟩ ⇓B « σ »
        (* unusual *)
    | BigStepAbort σ :
        ⟨Abort | σ⟩ ⇓B ↯
    | BigStepCrashBlock s sr σ c:
        ~ isProperTerm c ->
        ⟨s | σ⟩ ⇓B c ->
        ⟨Block (s::sr) | σ⟩ ⇓B c
    | BigStepCrashWhile e s σ c:
        σ ⊨ e ->
        ~ isProperTerm c ->
        ⟨s | σ⟩ ⇓B c ->
        ⟨While e s | σ⟩ ⇓B c
    where "⟨ s | σ ⟩ ⇓B conf2" := (properBigStep s σ conf2).


Definition confInterpret (c:Conf) P :=
    exists σ, c = Terminated σ /\ σ ⊨ P.
Notation "c '⊨c' P" := (confInterpret c P) (at level 70).