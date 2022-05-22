Require Import String.
Require Import List.


Arguments Some [A] _.
Arguments None {A}.

Definition ret {A : Type} (x : A) := Some x.
 
Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.

Notation "A >>= F" := (bind A F) (at level 42, left associativity).

Notation "X <- A ;; B" := (bind A (fun X => B)) 
    (at level 61, A at next level, right associativity).

Lemma mon_left_id : forall (A B : Type) (a : A) (f : A -> option B),
  ret a >>= f = f a.
intros.
reflexivity.
Qed.
 
Lemma mon_right_id : forall (A : Type) (a : option A),
  a >>= ret = a.
intros.
induction a; repeat reflexivity.
Qed.
 
Lemma mon_assoc :
  forall (A B C : Type) (a : option A) (f : A -> option B) (g : B -> option C),
    (a >>= f) >>= g = a >>= (fun (x:A) => f x >>= g).
intros.
induction a; repeat reflexivity.
Qed.






Class EqDec (A:Type) :=
    {eqdec:(forall (x y:A), {x = y} + {x<>y})}.

Definition eqb {A} {H:EqDec A} (x y : A) : bool :=
  if @eqdec A H x y then true else false.

Instance StringEq : EqDec string.
    constructor.
    repeat decide equality.
Defined.

(* or use find *)
Definition mem {A} {AEq:EqDec A} (a:A) (xs:list A) := 
    existsb (fun x => eqb x a) xs.

Definition fold_left_i {A B:Type} (f: A -> B -> nat -> A) (xs:list B) (a:A) : A :=
    fst (fold_left (fun '(a,i) b => (f a b i, S i) ) xs (a,0)).