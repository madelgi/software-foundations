Module Dictionary.

Add LoadPath "../Basics".
Add LoadPath "../Induction".
Require Import EnumTypes.
Require Import Induction.
Require Import NamingCases.
Require Import Lists.
Require Import Reasoning.
Require Import Options.

(** Definition of a simple [dictionary] type *)
Inductive dictionary : Type :=
   | empty : dictionary
   | record : nat -> nat -> dictionary -> dictionary.

(** An [insert] function for the dictionary *)
Definition insert (key value : nat) (d : dictionary) : dictionary :=
   (record key value d).

(** A [find] function to search for a certain [key] *)
Fixpoint find (key : nat) (d: dictionary) : natoption :=
   match d with
   | empty => None
   | record k v d' => if (beq_nat key k)
                      then (Some v)
                      else (find key d')
   end.

(** EXERCISE [*]: Complete the following proof. *)
Theorem dictionary_invariant1' : forall (d:dictionary) (k v : nat),
   (find k (insert k v d)) = Some v.

Proof.
   intros d k v. simpl. rewrite -> beq_nat_refl. reflexivity. Qed.

(** EXERCISE [*]: Complete the following proof. *)
Theorem dictionary_invariant2' : forall (d:dictionary) (m n o:nat),
   beq_nat m n = false -> find m d = find m (insert n o d).

Proof.
   intros d m n o.
   intro H. simpl. rewrite -> H. reflexivity. Qed.

End Dictionary.
