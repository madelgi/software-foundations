Require Import EnumTypes.

(** Some thms require more than a simple calculation. In general, unknown
    values (such as arbitrary nums, bools, lists, etc) can block a
    calculation. Here's an example of where simple fails *)
Theorem plus_1_neq_0_firsttry : forall n : nat,
   beq_nat (n + 1) 0 = false.

   Proof.
      intros n.
      simpl.
   Abort.

(** in short, simpl fails b/c it needs to consider different possible
    values for n. can't do much when n is just a general number. the
    destruct method tells coq to consider cases where [n=O] and
    [n = S n'] separately *)
Theorem plus_1_neq_0 : forall n : nat,
   beq_nat (n + 1) 0 = false.

   Proof.
      intros n. destruct n as [| n'].
         reflexivity.
         reflexivity. Qed.

(** the [as [| n']] is an intro pattern. it tells coq what var names
    to introduce for each sub goal, separated by [|] *)

Theorem negb_involutive : forall b : bool,
   negb (negb b) = b.

   Proof.
      intros b. destruct b.
         reflexivity.
         reflexivity. Qed.

(** EXERCISE [*]: Prove the following theorem *)
Theorem zero_nbeq_plus_1 : forall n : nat,
   beq_nat 0 (n + 1) = false.

   Proof.
      intros n. destruct n as [| n'].
         reflexivity.
         reflexivity. Qed.
