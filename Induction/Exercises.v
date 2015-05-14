Add LoadPath "../Basics".
Require Import EnumTypes.
Require Import CaseAnalysis.
Require Import NamingCases.
Require Import Induction.
Require Import ProofsInProofs.

(** EXERCISE [***]: Prove the following theorems. First determine
    whether they can be proven w/ simple rewriting and simplification.
    If not, determine whether it needs case analysis via [destruct], or
    full-on [induction] *)

(** INDUCTION *)
Theorem ble_nat_refl : forall n : nat,
   true = ble_nat n n.

Proof.
   intro n. induction n as [| n'].
   Case "n = 0".
      simpl. reflexivity.
   Case "n = S n'".
      simpl. rewrite -> IHn'. reflexivity. Qed.

(** REWRITE ONLY *)
Theorem zero_nbeq_S : forall n : nat,
   beq_nat 0 (S n) = false.

Proof.
   intro n. simpl. reflexivity. Qed.

(** CASE ANALYSIS *)
Theorem andb_false_r : forall b : bool,
   andb b false = false.

Proof.
   intro b. destruct b.
   Case "b = true".
      simpl. reflexivity.
   Case "b = false".
      simpl. reflexivity. Qed.

(** INDUCTION *)
Theorem plus_ble_compat_1 : forall n m p : nat,
   ble_nat n m = true ->
   ble_nat (p + n) (p + m) = true.

Proof.
   intros n m p. intro H.
   induction p as [| p'].
   Case "p = 0".
      simpl. rewrite -> H. reflexivity.
   Case "p = S p'".
      simpl. rewrite -> IHp'. reflexivity. Qed.

(** REWRITE ONLY *)
Theorem S_nbeq_0 : forall n : nat,
   beq_nat (S n) 0 = false.

Proof.
   intro n. simpl. reflexivity. Qed.

(** REWRITE ONLY *)
Theorem mult_1_1 : forall n : nat,
   1 * n = n.

Proof.
   intro n. simpl. rewrite <- plus_n_O. reflexivity. Qed.

(** CASE ANALYSIS *)
Theorem all3_spec : forall b c : bool,
   orb (andb b c) (orb (negb b) (negb c)) = true.

Proof.
   intros b c. destruct b.
   Case "b = true".
      destruct c.
      SCase "c = true".
         simpl. reflexivity.
      SCase "c = false".
         simpl. reflexivity.
   Case "b = false".
      destruct c.
      SCase "c = true".
         simpl. reflexivity.
      SCase "c = false".
         simpl. reflexivity. Qed.

(** TODO *)
Theorem mult_plus_distr_r : forall n m p : nat,
   (n + m) * p = (n * p) + (m * p).

Proof.
   Admitted.

(** INDUCTION *)
Theorem mult_assoc : forall n m p: nat,
   n * (m * p) = (n * m) * p.

Proof.
   intros n m p. induction n as [| n'].
   Case "n = 0".
      reflexivity.
   Case "n = S n'".
      simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r.
      reflexivity. Qed.

(** EXERCISE [**]: Prove the following theorem *)
Theorem beq_nat_refl : forall n : nat,
   true = beq_nat n n.

Proof.
   intro n. induction n as [| n'].
   Case "n = 0".
      reflexivity.
   Case "n = S n'".
      simpl. rewrite -> IHn'. reflexivity. Qed.

(** EXERCISE [**]: The [replace] tactice lets you specify a particular
    subterm to rewrite and what you want it rewritten to. That is,
    [replace (t) with (u)] replaces all copeis of expression [t] in
    the goal statement by expression [u], and generates [t = u] as an
    additional subgoal. Use this tactic to prove [plus_swap] without
    [assert] *)
Theorem plus_swap' : forall n m p : nat,
   n + (m + p) = m + (n + p).

Proof.
   intros n m p.
   replace (n + (m + p)) with ((m + p) + n).
   replace (n+p) with (p + n).
   rewrite -> plus_assoc.
   reflexivity.
   Case "Proof of second replacement".
      rewrite -> plus_comm. reflexivity.
   Case "Proof of first replacement".
      rewrite <- plus_comm. reflexivity. Qed.

(** EXERCISE [***]: Prove that [increment] and [binary-to-unary]
    commute. *)
