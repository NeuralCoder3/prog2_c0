Implicit Type (e:Expr)

Definition Var := string.
Definition Val := nat.

Inductive Expr :=
    | Var : Var -> Expr
    | Add : Expr -> Expr -> Expr
    | Mul : Expr -> Expr -> Expr
    | Lt : Expr -> Expr -> Expr
    | Eq : Expr -> Expr -> Expr
    | Num : Val -> Expr
    .

Definition Not := Eq (Num 0).
Definition Neq a b := Not (Eq a b)


Inductive Smt :=
    | Assume e
    | Assert e
    | While e (s:Smt)
    | If e (s_then s_else : Smt)
    | Seq (h:list Smt)
    | Assign (x:Var) e
    | Abort
    .

