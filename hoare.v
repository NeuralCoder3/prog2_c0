Require Import syntax.
Require Import semantics.
Require Import List.
Import ListNotations.

Section Syntactic.

    Definition Property := Expr.
    Inductive hoare : Property -> Stmt -> Property -> Prop :=
        | hoareAssign P: 
            hoare (replace P x e) (Assign x e) P
        | hoare

    Lemma partial_correctness P Q s σ σ':
        hoare P s Q ->
        P σ ->
        ⟨ s | σ ⟩ ⇓ « σ' » ->
        Q σ'.
    Proof.

    Lemma total_correctness P Q s σ:
        hoare P s Q ->
        P σ ->
        exists σ',
        ⟨ s | σ ⟩ ⇓ « σ' » /\
        Q σ'.
    Proof.

End Syntactic.

Definition Property := State -> Prop.
Inductive hoare : Property -> Stmt -> Property -> Prop :=
    | hoareAssign P: 
        hoare () (Assign x e) P
    | hoare

Lemma partial_correctness P Q s σ σ':
    hoare P s Q ->
    P σ ->
    ⟨ s | σ ⟩ ⇓ « σ' » ->
    Q σ'.
Proof.

Lemma total_correctness P Q s σ:
    hoare P s Q ->
    P σ ->
    exists σ',
    ⟨ s | σ ⟩ ⇓ « σ' » /\
    Q σ'.
Proof.