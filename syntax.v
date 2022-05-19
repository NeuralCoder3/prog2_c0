Require Import String.
Require Import List.
Require Import Nat.
Import ListNotations.

Definition VarT := string.
Definition Addr := nat.
Variant Val :=
    | AddrVal (addr: Addr)
    | IntVal (v: nat).

Variant Op := 
    Add | Mul | Sub | Ge.

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
    | Abort
    .

Implicit Type (ss : list Stmt) (s:Stmt).



