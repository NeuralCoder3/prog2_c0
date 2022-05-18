Require Import String.
Require Import List.
Require Import Nat.
Import ListNotations.


Definition VarT := string.
Definition ValT := nat.
(* Variable (Addr:Type) (AddrEq: forall (x y:Addr), {x=y} + {x<>y}). *)
Definition Addr := nat.
Definition AddrEq := PeanoNat.Nat.eq_dec.

Variant AOp :=
    | Add
    | Sub
    | Mul
    .

Variant COp :=
    | Eq
    | Lt
    .

Variant Op :=
    | ArithOp (op:AOp)
    | CompOp (op:COp)
    .

Inductive Val :=
    | NumVal (n:ValT)
    | AddrVal (a:Addr)
    .

Inductive LExpr :=
    | Var (x:VarT)
    (* C0p *)
    | Indir (e:Expr)
with Expr :=
    | Const (c:Val)
    | Left (e:LExpr)
    | Binary (op:Op) (e1:Expr) (e2:Expr)
    (* C0p *)
    | Adress (l:LExpr)
    .

Variant ITy :=
    | Char
    | Int.

Inductive PTy :=
    | Ptr (t:Ty)
with STy :=
    | PtrScal (p:PTy)
    | IntScal (i:ITy)
with Ty :=
    | Scal (s:STy)
    | Void
    .

Inductive Stmt :=
    | Assign (l:LExpr) (e:Expr)
    | If (e:Expr) (s1:Stmt) (s2:Stmt)
    | While (e:Expr) (s:Stmt)
    (* | Block (s:list Stmt) *)
    | Abort
    (* C0b *)
    | Block (decl:list (STy*VarT)) (s:list Stmt)
    .

Variant UndefVal :=
    | Undef
    | Defined (v:Val)
    .

Notation VarEnv := (VarT -> option Addr).
Notation MemEnv := (Addr -> UndefVal).

Record State :=
    {
        var_assign: VarEnv;
        memory_assign: MemEnv
    }.

Variant Conf :=
    | Aborted
    | Terminated (s:State)
    | Running (smt:Stmt) (s:State)
    .

Notation "⟨ s | o ⟩" := (Running s o).
Coercion Terminated : State >-> Conf.
Notation Env := 
    (fun σ =>
    let '(ρ,μ) := σ in
    Build_State ρ μ).
Coercion Defined : Val >-> UndefVal.

Load option_monad.

Definition LExprEval (l:LExpr) (s:State) : option Addr :=
    let (ρ,μ) := s in
    match l with 
    | Var x =>
        ρ x
    | Indir e => None
    (* TODO C0p *)
    end
    .
Fixpoint ExprEval (e:Expr) (s:State) : option Val :=
    match e with 
    | Const c => ret c
    | Left l => 
        let (ρ,μ) := s in
        t <- LExprEval l s;;
        match (μ t) with 
        | Undef => None
        | Defined v =>
            ret v
        end
    | Binary op e1 e2 =>
        v1 <- ExprEval e1 s;;
        v2 <- ExprEval e2 s;;
        match v1,v2,op with
        | NumVal n1, NumVal n2, ArithOp Add => ret (NumVal (n1 + n2))
        | NumVal n1, NumVal n2, ArithOp Sub => ret (NumVal (n1 - n2))
        | NumVal n1, NumVal n2, ArithOp Mul => ret (NumVal (n1 * n2))
        | NumVal n1, NumVal n2, CompOp Eq => ret (if n1 =? n2 then NumVal 1 else NumVal 0)
        | NumVal n1, NumVal n2, CompOp Lt => ret (if n1 <? n2 then NumVal 1 else NumVal 0)
        | _, _, _ => None
        end
    | Adress l =>
        None (* TODO C0p *)
    end
    .


Definition update {A B} {Aeq:forall a b, {a=b} + {a<>b}} (f:A -> B) (x:A) (y:B) (x2:A) : B :=
        if Aeq x x2 then y else f x2.

Definition Skip := Block [] [].

    (* page 140 *)
Reserved Notation "c1 ~> c2" (at level 40).
(* TODO: C0b *)
Inductive step : Conf -> Conf -> Prop :=
    | EmptyStep σ: ⟨ Skip | σ ⟩ ~> σ
    | AssignStep ρ μ l e v a: 
        ExprEval e (Env (ρ,μ)) = Some v ->
        LExprEval l (Env (ρ,μ)) = Some a ->
        ⟨ Assign l e | Env (ρ,μ) ⟩ ~> 
        Env (ρ, @update _ _ AddrEq μ a (Defined v))
    | IfTrueStep σ e s1 s2 n: 
        ExprEval e σ = Some (NumVal n) ->
        n <> 0 ->
        ⟨ If e s1 s2 | σ ⟩ ~> ⟨ s1 | σ ⟩
    | IfFalseStep σ e s1 s2: 
        ExprEval e σ = Some (NumVal 0) ->
        ⟨ If e s1 s2 | σ ⟩ ~> ⟨ s2 | σ ⟩
    | WhileStep σ e s: 
        ⟨ While e s | σ ⟩ ~> 
        ⟨ If e (Block [] [s; While e s]) Skip | σ ⟩
    | AbortStep σ : ⟨ Abort | σ ⟩ ~> Aborted
    | ExecStep σ (σ':State) s1 sr:
        ⟨ s1 | σ ⟩ ~> σ' ->
        ⟨ Block [] (s1::sr) | σ ⟩ ~> 
        ⟨ Block [] sr | σ' ⟩
    | CrashStep σ s1 sr:
        ⟨ s1 | σ ⟩ ~> Aborted ->
        ⟨ Block [] (s1::sr) | σ ⟩ ~> Aborted
    | SubstStep σ (σ':State) s1 s1' sr:
        ⟨ s1 | σ ⟩ ~> ⟨ s1' | σ' ⟩ ->
        ⟨ Block [] (s1::sr) | σ ⟩ ~> 
        ⟨ Block [] (s1'::sr) | σ' ⟩
    where "c1 ~> c2" := (step c1 c2).

Definition final c := ~exists c2, c ~> c2.

Reserved Notation "c1 ⇓ c2" (at level 40).
Inductive big_step : Conf -> Conf -> Prop :=
    | BigStepEnd c:
        final c ->
        c ⇓ c
    | BigStepTrans c1 c2 c3:
        c1 ~> c2 ->
        c2 ⇓ c3 ->
        c1 ⇓ c3
    where "c1 ⇓ c2" := (big_step c1 c2).



    (* 149 => static sema *)

    (* Hoare 156 *)

Require Import String.
Local Open Scope string_scope.

Require Import Lia.

Goal forall a b, a<=b <-> a < S b.
Proof.
intros;split;intros;lia.
Qed.

Definition example5_5 :=
    Block [
        (* (Int, "x"),
        (Int, "y"),
        (Int, "z") *)
    ] [
        Assign (Var "q") (Const (NumVal 0));
        Assign (Var "r") (Left (Var "x"));
        While (Binary (CompOp Lt) (Left (Var "y")) (Binary (ArithOp Add) (Const (NumVal 1)) (Left (Var "r")))) (
            Block [
            ] [
                Assign (Var "r") (Binary (ArithOp Sub) (Left (Var "r")) (Const (NumVal 1)));
                Assign (Var "q") (Binary (ArithOp Add) (Left (Var "q")) (Const (NumVal 1)))
            ]
        )
    ]
    .

Definition empty_env {A B} (x:A) : option B := None.

Fixpoint to_single_env {A B AEq} (xs:list (A*B)) :=
    match xs with 
    | [] => empty_env
    | (a,b)::xr => @update _ _ AEq (@to_single_env A B AEq xr) a (Some b)
    end.


Fixpoint to_env_aux (xs:list (VarT*UndefVal)) :=
    match xs with 
    | [] => (empty_env, fun _ => Undef, 0)
    | (a,b)::xr => 
        let '(addr_map, val_map, n) := to_env_aux xr in
        let addr := 1000+n in
            (@update _ _ string_dec addr_map a (Some addr), @update _ _ AddrEq val_map addr b, S n)
    end.

Definition to_env xs :=
    let '(ρ,μ,n) := to_env_aux xs in
    Env (ρ,μ).

(* Notation "{ }" := empty_env (format "{ }").
Notation "{ x ↦ v }" := (update empty_env x v).
Notation "[ x ↦ v ; y ↦ w ; .. ; z ↦ r ]" := (update (update (.. (update empty_env z r) ..) y w ) x v). *)




(* Goal ⟨ example5_5 | to_env [("q", Undef); ("r",Undef); ("x", Defined(NumVal 5)); ("y", Defined(NumVal 2))] ⟩ ⇓ 
    to_env [("q", Defined( NumVal 2)); ("r",Defined(NumVal 1)); ("x", Defined(NumVal 5)); ("y", Defined(NumVal 2))].
Proof.
    cbn.
    do 12 (eapply BigStepTrans;[shelve|]).
    Unshelve.
    1-13: shelve.
    - apply ExecStep.
      apply AssignStep;now cbn.
    - apply ExecStep.
      apply AssignStep;cbn.
      all: reflexivity.
      (* unfold ExprEval.
      cbn [LExprEval].
      remember (update _ _ _ _).
      cbn in Heqy.
      1: cbn.
      2: cbn. *)
    - apply SubstStep.
      apply WhileStep.
    - apply SubstStep.
      eapply IfTrueStep;[vm_compute|].
      all: auto.
    - apply ExecStep.
      constructor.
      apply AssignStep.
      apply ExecStep.
      apply SubstStep.
      (* cbn [ExprEval].
      cbn [ExprEval LExprEval bind ret]. *) *)
