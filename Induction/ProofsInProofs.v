Add LoadPath "../Basics".
Require Import EnumTypes.
Require Import CaseAnalysis.
Require Import NamingCases.
Require Import Induction.

(** Sometimes proofs require small subfacts that don't really merit
    their own top-level [Theorem], [Lemma], etc statements. You can
    prove these facts within their relevant contexts (usually a more
    significant proof) by using the [assert] tactic. Here's an
    example of [assert] in action *)
Theorem mult_0_plus : forall n m : nat,
   (0 + n) * m = n * m.

Proof.
   intros n m.
   assert (H: 0 + n = n).
      Case "Proof of assertion". reflexivity.
   rewrite -> H.
   reflexivity. Qed.

(** [assert] helps us make rewrite less dumb. This example seems clear,
    but when we try to apply commutativity of addition, Coq assumes we
    want to apply it to the outer, rather than inner, + sign *)
Theorem plus_rearrange_firsttry : forall n m p q : nat,
   (n + m) + (p + q) = (m + n) + (p + q).

Proof.
   intros n m p q.
   rewrite -> plus_comm.
Abort.

(** Using assert to solve the above problem *)
Theorem plus_rearrange : forall n m p q : nat,
   (n + m) + (p + q) = (m + n) + (p + q).

Proof.
   intros n m p q.
   assert (H: n + m = m + n).
      Case "Proof of assertion".
      rewrite -> plus_comm. reflexivity.
   rewrite -> H. reflexivity. Qed.

(** EXERCISE [****]: Use [assert] to help prove this theorem, without
    using induction *)
Theorem plus_swap : forall n m p : nat,
   n + (m + p) = m + (n + p).

Proof.
   intros n m p.
   assert (H1: n + (m+p) = (m+p) + n).
      Case "Proof of assertion 1".
      rewrite -> plus_comm. reflexivity.
   assert (H2: p + n = n + p).
      Case "Proof of assertion 2".
      rewrite -> plus_comm. reflexivity.
   rewrite -> H1. rewrite <- H2. rewrite -> plus_assoc. reflexivity. Qed.

Theorem mult_comm : forall m n : nat,
   m * n = n * m.

Proof.
   intros n m. induction n as [| n'].
   Case "n = 0".
      simpl. rewrite -> mult_0_r. reflexivity.
   Case "n = S n'".
      simpl. rewrite -> IHn'. Admitted.

(** EXERCISE [**]: Prove the following fact. *)
Theorem evenb_n_oddb_Sn : forall n : nat,
   evenb n = negb (evenb (S n)).

Proof.
   intros n. induction n as [| n'].
   Case "n = 0".
      simpl. reflexivity.
   Case "n = S n'".
      assert (H: evenb (S (S n')) = evenb n').
         simpl. reflexivity.
      rewrite -> H. rewrite -> IHn'.
      rewrite -> negb_involutive. reflexivity. Qed.


