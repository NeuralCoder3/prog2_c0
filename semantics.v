Require Import syntax.

Variant UndefVal :=
    | Undef
    | Defined (v:Val)
    .

Notation VarEnv := (VarT -> option AddrT).
Notation MemEnv := (AddrT -> option UndefVal).

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

Definition evalOp (op:Op) (v1 v2:Val) : option Val :=
    match op, v1,v2 with 
    | Add, IntVal i1, IntVal i2 => Some (IntVal (i1+i2))
    | Sub, IntVal i1, IntVal i2 => Some (IntVal (i1-i2))
    | Mul, IntVal i1, IntVal i2 => Some (IntVal (i1*i2))
    | Ge , IntVal i1, IntVal i2 => Some (IntVal (if Nat.leb i2 i1 then 1 else 0))
    | Eq , IntVal i1, IntVal i2 => Some (IntVal (if Nat.eqb i1 i2 then 1 else 0))
    | _, _, _ => None
    end.

Fixpoint LExprEval (l:LExpr) (σ:State) : option AddrT :=
    let (ρ,μ) := σ in
    match l with
    | Var x => ρ x
    (* C0p *)
    | Indir e => 
        match RExprEval e σ with
        | Some (AddrVal a) => Some a
        | _ => None
        end
    end
with RExprEval (e:Expr) (σ:State) : option Val :=
    match e with 
    | Const c => ret c
    | LVal l => 
        let (ρ,μ) := σ in
        a <- LExprEval l σ;;
        uv <- μ a;;
        match uv with 
        | Undef => None
        | Defined v =>
            ret v
        end
    | Binary op e1 e2 =>
        v1 <- RExprEval e1 σ;;
        v2 <- RExprEval e2 σ;;
        evalOp op v1 v2
    (* C0p *)
    | Addr e => 
        match LExprEval e σ with
        | Some a => Some (AddrVal a)
        | _ => None
        end
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

Instance AddrTEq : EqDec AddrT.
    constructor.
    now decide equality.
Defined.

Instance StringEq : EqDec string.
    constructor.
    repeat decide equality.
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