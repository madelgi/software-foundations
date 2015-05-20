Add LoadPath "../Basics".
Add LoadPath "../Induction".
Add LoadPath "../Lists".

(* Require Import Lists. *)
Require Import EnumTypes.
Require Import Induction.
Require Import NamingCases.
Require Export Reasoning.
Require Export Polymorphism.
Require Export FunctionsAsData.

Theorem beq_nat_refl : forall n : nat,
   true = beq_nat n n.

Proof.
   intro n. induction n as [| n'].
   Case "n = 0".
      reflexivity.
   Case "n = S n'".
      simpl. rewrite -> IHn'. reflexivity. Qed.

Definition plus3 := plus 3.
Check plus3.

(** A proof sometimes gets stuck b/c Coq will not expand
    a function call into its definition. Consider the following
    example *)
Theorem unfold_example_bad : forall m n,
   3 + n = m ->
   plus3 n + 1 = m + 1.

Proof.
   intros m n H.
   (** Here, we'd execute [rewrite -> H], since plus3 n is 3 + n.
       However, coq wn't automatically expand [plus3 n] to its
       definition *)
   Abort.

(** Here's the above example, now with unfold *)
Theorem unfold_example : forall m n,
   3 + n = m ->
   plus3 n + 1 = m + 1.

Proof.
   intros m n H.
   unfold plus3.
   rewrite -> H.
   reflexivity. Qed.

Theorem override_eq : forall {X:Type} x k (f:nat->X),
   (override f k x) k = x.

Proof.
   intros X x k f.
   unfold override.
   rewrite <- beq_nat_refl.
   reflexivity. Qed.

Theorem override_neq : forall (X:Type) x1 x2 k1 k2 (f : nat -> X),
   f k1 = x1 ->
   beq_nat k2 k1 = false ->
   (override f k2 x2) k1 = x1.

Proof.
   intros X x1 x2 k1 k2. intro f. intros H1 H2.
   unfold override. rewrite -> H2. rewrite -> H1.
   reflexivity. Qed.
