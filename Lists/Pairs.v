Add LoadPath "../Induction".
Add LoadPath "../Basics".

Require Export Induction.

Module NatList.

(** An inductive type definition for pairs *)
Inductive natprod : Type :=
   pair : nat -> nat -> natprod.

(** Definitions for

    - fst :: (x,y) -> x
    - snd :: (x,y) -> y
*)
Definition fst (p : natprod) : nat :=
   match p with
   | pair x y => x
   end.
Definition snd (p : natprod) : nat :=
   match p with
   | pair x y => y
   end.

(* Test *)
Eval compute in (fst (pair 3 5)).
Eval compute in (snd (pair 3 5)).

(** Define natural notation for pair *)
Notation "( x , y )" := (pair x y).

(** Using our new notation in a swap function *)
Definition swap_pair (p : natprod) : natprod :=
   match p with
   | (x,y) => (y,x)
   end.

(* Test function *)
Eval compute in (swap_pair (3,5)).

(* A simple pair-related surjectivity theorem *)
Theorem surjective_pairing : forall n m : nat,
   (n,m) = (fst (n,m), snd (n,m)).

Proof.
   reflexivity. Qed.

(** If we were to use [p :: natprod] rather than [n,m :: nat], we would
    have to go through a slightly lengthier proof for the above Theorem.
    The bottom two exercises illustrate this approach. *)

(** EXERCISE [*]: Prove the following theorem *)
Theorem snd_fst_is_swap : forall p : natprod,
   (snd p, fst p) = swap_pair p.

Proof.
   intro p. destruct p as [n m].
   simpl. reflexivity. Qed.

(** EXERCISE [*]: Prove the following theorem *)
Theorem fst_swap_is_snd : forall p : natprod,
   fst (swap_pair p) = snd p.

Proof.
   intro p. destruct p as [n m].
   simpl. reflexivity. Qed.

End NatList.
