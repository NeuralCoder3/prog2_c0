Require Import String.
Require Import List.
Require Import Nat.
Import ListNotations.

Definition VarT := string.
(* Definition Addr := nat. *)
Variant Addr := Triangle | Circle | Pentagon | Square.
Variant Val :=
    | AddrVal (addr: Addr)
    | IntVal (v: nat).

Variant Op := 
    Add | Mul | Sub | Ge | Eq.
(* define Ge with Lt & Eq & Not *)
    (* Lt Eq *)

Inductive Expr :=
    | Const (c:Val)
    | Binary (o:Op) (e1 e2:Expr)
    | LVal (l:LExpr)
with LExpr :=
    | Var (v:VarT)
    .

Implicit Type (e : Expr) (c : Val) (x y : VarT).

Inductive Stmt :=
    (* | Assume e *)
    (* | Assert e *)
    | While e (s:Stmt)
    | If e (s_then s_else : Stmt)
    | Block (h:list Stmt)
    | Assign (x:LExpr) e
    | GarbageCollect (* do not use to construct programs *)
    | Abort.
Definition Program := list Stmt.
(*
we do not need explicit 
    Block (h:Program)
    Program := Prog (b:list Stmt)
*)

Implicit Type (ss : list Stmt) (s:Stmt).



