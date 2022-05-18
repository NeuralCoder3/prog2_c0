
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
    (a >>= f) >>= g = a >>= (fun x => f x >>= g).
intros.
induction a; repeat reflexivity.
Qed.