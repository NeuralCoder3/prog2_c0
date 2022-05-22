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
    Add | Mul | Sub | Ge | Eq.
(* define Ge with Lt & Eq & Not *)
    (* Lt Eq *)

Inductive Expr :=
    | Const (c:Val)
    | Binary (o:Op) (e1 e2:Expr)
    | LVal (l:LExpr)
    (* C0p *)
    | Addr (l:LExpr)
with LExpr :=
    | Var (v:VarT)
    (* C0p *)
    | Indir (e:Expr)
    .

Implicit Type (e : Expr) (c : Val) (x y : VarT).

Inductive CType :=
    | Int 
    | Pointer (t:CType).

Definition Declaration : Type := CType*VarT.

Inductive Stmt :=
    (* | Assume e *)
    (* | Assert e *)
    | While e (s:Stmt)
    | If e (s_then s_else : Stmt)
    (* modified by C0b *)
    | Block (decl:list Declaration) (h:list Stmt)
    | Assign (x:LExpr) e
    | Abort
    | GarbageCollect
    .

Implicit Type (ss : list Stmt) (s:Stmt).



Notation "△" := Triangle.
Notation "○" := Circle.
Notation "⬠" := Pentagon.
Notation "□" := Square.
Notation "■" := GarbageCollect.