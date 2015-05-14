Add LoadPath "../Basics".
Add LoadPath "../Induction".
Require Import EnumTypes.
Require Import Induction.
Require Import NamingCases.
Require Import Lists.
Require Import Reasoning.

(** Below is an implementation of the [!!] operation. What do we do if
    the given index is too high? In this case, we return the arbitrary
    value 42. *)
Fixpoint index_bad (n:nat) (l:natlist) : nat :=
   match l with
   | nil => 42 (* arbitrary *)
   | a :: l' => match beq_nat n O with
                | true => a
                | false => index_bad (pred n) l'
                end
   end.

(** Introducing [natoption], an inductive type for handling errors. It's
    basically just [Maybe Int] *)
Inductive natoption : Type :=
   | Some : nat -> natoption
   | None : natoption.

(** Let's rewrite [index_bad] with the added convenience of [natoption] *)
Fixpoint index (n:nat) (l:natlist) : natoption :=
   match l with
   | nil => None (* arbitrary *)
   | a :: l' => match beq_nat n O with
                | true => Some a
                | false => index (pred n) l'
                end
   end.

(* Some examples *)
Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4;5;6;7] = Some 7.
Proof. reflexivity. Qed.
Example test_index3 : index 10 [4;5;6;7] = None.
Proof. reflexivity. Qed.

(** Here's a function for taking the [nat] out of a [natoption]. The
    function returns a supplied default [d] if the [natoption] is
    [None] *)
Definition option_elim (d : nat) (o : natoption) : nat :=
   match o with
   | Some n => n
   | None   => d
   end.

(** EXERCISE [**]: Fix the hd function from earlier, so we don't have to
    pass a default case *)
Definition hd_opt (l : natlist) : natoption :=
   match l with
   | []     => None
   | h :: t => Some h
   end.

(* Tests *)
Example test_hd_opt1 : hd_opt [] = None.
Proof. reflexivity. Qed.

Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
Proof. reflexivity. Qed.

(** EXERCISE [*]: Prove the following theorem, relating [hd_opt] to
    [hd] *)
Theorem option_elim_hd : forall (l : natlist) (default : nat),
   hd default l = option_elim default (hd_opt l).

Proof.
   intros l default. destruct l as [| x l'].
   Case "l = []".
      reflexivity.
   Case "l = x :: l'".
      reflexivity. Qed.
