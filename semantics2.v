Load syntax2.

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
Definition State := (list VarEnv * MemEnv)%type.

Implicit Type (ρ:VarEnv) (μ:MemEnv) (σ:State).

Load option_monad.

Fixpoint lookupStack {A B} (stack:list (A -> option B)) (v:A) :=
    match stack with
    | [] => None
    | hd::tl =>
        match hd v with
        | None => lookupStack tl v
        | Some a => Some a
        end
    end.

Definition ρ σ := lookupStack (fst σ).
Definition μ σ := snd σ.

Definition lookupVar σ x :=
    a <- ρ σ x;;
    μ σ a.


Definition LExprEval (l:LExpr) (σ:State) : option Addr :=
    match l with
    | Var x => ρ σ x
    end.
Definition evalOp (op:Op) (v1 v2:Val) : option Val :=
    match op, v1,v2 with 
    | Add, IntVal i1, IntVal i2 => Some (IntVal (i1+i2))
    | Sub, IntVal i1, IntVal i2 => Some (IntVal (i1-i2))
    | Mul, IntVal i1, IntVal i2 => Some (IntVal (i1*i2))
    | Ge , IntVal i1, IntVal i2 => Some (IntVal (if Nat.leb i2 i1 then 1 else 0))
    | Eq , IntVal i1, IntVal i2 => Some (IntVal (if Nat.eqb i1 i2 then 1 else 0))
    | _, _, _ => None
    end.
Fixpoint ExprEval (e:Expr) (σ:State) : option Val :=
    match e with 
    | Const c => ret c
    | LVal l => 
        a <- LExprEval l σ;;
        uv <- μ σ a;;
        match uv with 
        | Undef => None
        | Defined v =>
            ret v
        end
    | Binary op e1 e2 =>
        v1 <- ExprEval e1 σ;;
        v2 <- ExprEval e2 σ;;
        evalOp op v1 v2
    end
    .


Variant Conf :=
    | Aborted
    | Terminated (s:State)
    | Running (smt:Program) (s:State)
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

Open Scope string.
Notation "△" := Triangle.
Notation "○" := Circle.
Notation "■" := GarbageCollect.
Instance eqString : EqDec string.
    constructor.
    repeat decide equality.
Defined.
Notation "f [ x ↦ y ]" := (update f x y) (at level 10).

Definition emptyEnv {A} {B} (a:A) : option B := None.

Reserved Notation "c1 ~> c2" (at level 50).
Inductive step : Conf -> Conf -> Prop :=
    | AssignStep l e ρs μ a v p: 
        let σ := (ρs, μ) in
        R⟦e⟧σ = Some v ->
        L⟦l⟧σ = Some a ->
        ⟨ (Assign l e)::p | σ ⟩ ~> ⟨ p | (ρs, μ [a ↦ Some (Defined v)])  ⟩
    | IfTrueStep e s1 s2 σ (n:nat) p:
        R⟦e⟧σ = Some (n:Val) ->
        n <> 0 ->
        ⟨ (If e s1 s2)::p | σ ⟩ ~> ⟨ s1::p | σ ⟩
    | IfFalseStep e s1 s2 σ p:
        R⟦e⟧σ = Some (0:Val) ->
        ⟨ (If e s1 s2)::p | σ ⟩ ~> ⟨ s2::p | σ ⟩
    | WhileTrueStep e s σ (n:nat) p:
        R⟦e⟧σ = Some (n:Val) ->
        n <> 0 ->
        ⟨ (While e s)::p | σ ⟩ ~> ⟨ s :: While e s :: p | σ ⟩
    | WhileFalseStep e s σ p:
        R⟦e⟧σ = Some (0:Val) ->
        ⟨ (While e s)::p | σ ⟩ ~> ⟨ p | σ ⟩
    | EmptyStep σ :
        ⟨ [] | σ ⟩ ~> « σ »
    | BlockStep p q ρs μ:
        let σ := (ρs, μ) in
        ⟨ Block q :: p | σ ⟩ ~> ⟨ (p ++ [■] ++ q)%list | (emptyEnv::ρs,μ) ⟩
    | GarbageCollectStep p ρ ρs μ :
        ⟨ ■ :: p | (ρ::ρs, μ) ⟩ ~> ⟨ p | (ρs,μ) ⟩
    | AbortStep σ p :
        ⟨ Abort::p | σ ⟩ ~> ↯
    where "c1 ~> c2" := (step c1 c2).

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

Definition properTerm p σ σ' :=
    ⟨ p | σ ⟩ ⇓ σ'.
Definition abortion p σ :=
    ⟨ p | σ ⟩ ⇓ ↯.
Definition stuck p σ p' σ' :=
    ⟨ p | σ ⟩ ⇓ ⟨ p' | σ' ⟩.