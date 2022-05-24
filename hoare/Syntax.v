Require Import String.
Require Import List.
Require Import Nat.
Import ListNotations.

Definition VarT := string.
(* Definition Addr := nat. *)
Variant AddrT := Triangle | Circle | Pentagon | Square | NatAddr (n:nat).
Variant Val :=
    | AddrVal (addr: AddrT)
    | IntVal (v: nat).


Variant Op := 
    Lt | Eq | Add | Mul | Sub | And | Ge.
     (* | Ge | Eq |
    And | Xor. *)
(* define Ge with Lt & Eq & Not *)
    (* Lt Eq *)
Variant UOp := Not.

(* Variant BinaryNotationOp :=
    And | Ge | Xor.
Variant UnaryNotationOp :=
    Not. *)

Inductive Expr :=
    | Const (c:Val)
    | Binary (o:Op) (e1 e2:Expr)
    | Unary (o:UOp) (e1:Expr)
    | LVal (l:LExpr)
with LExpr :=
    | Var (v:VarT)
    .

Implicit Type (e : Expr) (c : Val) (x y : VarT).

Inductive Stmt :=
    | Assume e
    | Assert e
    | While e (s:Stmt)
    | If e (s_then s_else : Stmt)
    | Block (h:list Stmt)
    | Assign (x:LExpr) e
    | Abort
    .

Implicit Type (ss : list Stmt) (s:Stmt).




Notation "△" := Triangle.
Notation "○" := Circle.
Notation "⬠" := Pentagon.
Notation "□" := Square.