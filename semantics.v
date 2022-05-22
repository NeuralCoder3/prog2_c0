Require Import String.
Require Import List.
Import ListNotations.
Require Import syntax.
Require Import util.

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

Section Environments.
    Variable (dom codom:Type).
    Variable (DomEq : EqDec dom).

    Definition Env := list (dom * codom).
    Definition lookup (e:Env) a :=
        r <- find (fun (d:dom * codom) => eqb (fst d) a) e;;
        Some (snd r).

    Fixpoint lookupStack (stack:list Env) (v:dom) :=
        match stack with
        | [] => None
        | hd::tl =>
            match lookup hd v with
            | None => lookupStack tl v
            | Some a => Some a
            end
        end.

    (* needs list representation *)
    Definition getCodom (e:Env) : list codom :=
        map (fun (d:dom * codom) => snd d) e.
    Definition getDom (e:Env) : list dom :=
        map (fun (d:dom * codom) => fst d) e.

    Definition undef (e:Env) (xs:list dom) : Env :=
        filter (fun (d:dom * codom) =>
            negb (mem (fst d) xs)) e.

    Definition update (f:Env) (x:dom) (y:codom) :=
        (x,y) :: f.
    (* if @eqdec A Aeq x x2 then y else f x2. *)

    Definition emptyEnv : Env := [].

End Environments.

Arguments lookup {dom} {codom} {DomEq}.
Arguments lookupStack {dom} {codom} {DomEq}.
Arguments undef {dom} {codom} {DomEq}.
Arguments update {dom} {codom}.
Arguments getDom {dom} {codom}.
Arguments getCodom {dom} {codom}.
Arguments emptyEnv {dom} {codom}.


Notation VarEnv := (Env VarT AddrT).
Notation MemEnv := (Env AddrT UndefVal).

(* Record State :=
    {
        var_assign: VarEnv;
        memory_assign: MemEnv
    }. *)
Definition State := (list VarEnv * MemEnv)%type.

Implicit Type (ρ:VarEnv) (ρs:list VarEnv) (μ:MemEnv) (σ:State).


Definition ρmap σ := lookupStack (fst σ).
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
    | _, _, _ => None
    end.

Fixpoint LExprEval (l:LExpr) (σ:State) : option AddrT :=
    match l with
    (* C0b *)
    | Var x => ρmap σ x
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
(* Coercion Some : UndefVal >-> (option UndefVal). *)

Definition remove_codom {A B C} {BEq:EqDec B} (μ:Env B C) (ρ:Env A B) : Env B C :=
    undef μ (getCodom ρ).

Definition maxAddr μ :=
    list_max(map (fun a =>
        match a with
        | NatAddr n => n
        | _ => 0
        end
    ) (getDom μ)).

Definition initAdresses μ xs v :=
    fold_left
    (fun e a =>
        update e a v
    ) xs μ.

Definition getNewAdresses (decl:list Declaration) μ : VarEnv :=
    let freshAddr := S(maxAddr μ) in
    fold_left_i (fun e '(t,v) i =>
        let a := NatAddr (i + freshAddr) in
        e { v ↦ a }
    ) decl emptyEnv.


Reserved Notation "c1 ~> c2" (at level 50).
Inductive step : Conf -> Conf -> Prop :=
    | AssignStep l e ρs μ a v: 
        let σ := (ρs, μ) in
        R⟦e⟧σ = Some v ->
        L⟦l⟧σ = Some a ->
        ⟨ (Assign l e) | σ ⟩ ~> «(ρs, update μ a (Defined v))»
    | IfTrueStep e s1 s2 σ (n:nat) :
        R⟦e⟧σ = Some (n:Val) ->
        n <> 0 ->
        ⟨ (If e s1 s2) | σ ⟩ ~> ⟨ s1 | σ ⟩
    | IfFalseStep e s1 s2 σ :
        R⟦e⟧σ = Some (0:Val) ->
        ⟨ (If e s1 s2) | σ ⟩ ~> ⟨ s2 | σ ⟩
    | WhileStep e s σ :
        ⟨ (While e s) | σ ⟩ ~> ⟨ If e (Block [] [s; While e s]) (Block [] []) | σ ⟩
    (* modified by C0b *)
    | EmptyStep σ :
        (* or ignore decls *)
        ⟨ Block [] [] | σ ⟩ ~> « σ »
    | ExecStep s1 sr σ σ' :
        ⟨ s1 | σ ⟩ ~> « σ' » ->
        (* or ignore decls *)
        ⟨ Block [] (s1::sr) | σ ⟩ ~> ⟨ Block [] sr | σ' ⟩
    | SubstStep s1 s1' sr σ σ' :
        ⟨ s1 | σ ⟩ ~> ⟨ s1' | σ' ⟩ ->
        (* or ignore decls *)
        ⟨ Block [] (s1::sr) | σ ⟩ ~> ⟨ Block [] (s1'::sr) | σ' ⟩
    | AbortStep σ :
        ⟨ Abort | σ ⟩ ~> ↯
    | CrashStep s1 sr σ :
        ⟨ s1 | σ ⟩ ~> ↯ ->
        (* or ignore decls *)
        ⟨ Block [] (s1::sr) | σ ⟩ ~> ↯
    (* added by C0b *)
    | BlockStep decl stmt ρs μ:
        let ρ := getNewAdresses decl μ in
        let addrs := getCodom ρ in
        ⟨ Block decl stmt | (ρs,μ) ⟩ ~> 
        ⟨ Block [] (stmt++[■]) | (ρ::ρs, initAdresses μ addrs Undef) ⟩
    | LeaveStep ρ ρs μ:
        ⟨ Block [] [■] | (ρ::ρs, μ) ⟩  ~>
        « (ρs,remove_codom μ ρ) »
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