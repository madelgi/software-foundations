Add LoadPath "../Basics".
Require Export NamingCases.

(** We start with a basic example of induction : proving that
    [n + 0 = n] *)
Theorem plus_0_r : forall n : nat, n + 0 = n.

Proof.
   intros n. induction n as [| n'].
   Case "n = 0".
      simpl. reflexivity.
   Case "n = S n".
      simpl. rewrite -> IHn' . reflexivity. Qed.

(** Another induction example. This time, we prove
    that n-n = 0 *)
Theorem minus_diag : forall n,
   minus n n = 0.

Proof.
   intros n. induction n as [| n'].
   Case "n = 0".
      simpl. reflexivity.
   Case "n = S n".
      simpl. rewrite -> IHn'. reflexivity. Qed.

(** EXERCISE [**]: Basic induction proofs. Prove the
    following lemmas using induction *)

Theorem mult_0_r : forall n : nat,
   n * 0 = 0.

Proof.
   intros n. induction n as [| n'].
   Case "n = 0".
      simpl. reflexivity.
   Case "n = S n".
      simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
   S (n + m) = n + (S m).

Proof.
   intros n m. induction n as [| n'].
   Case "n = 0".
      simpl. reflexivity.
   Case "n = S n".
      simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
   n + m = m + n.

(** Addition is commutative *)
Proof.
   intros n m. induction n as [| n'].
   Case "n = 0".
      simpl. rewrite -> plus_0_r. reflexivity.
   Case "n = S n".
      simpl. rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity. Qed.

(** Addition is associative *)
Theorem plus_assoc : forall n m p : nat,
   n + (m + p) = (n + m) + p.

Proof.
   intros n m p. induction n as [| n'].
   Case "n = 0".
     simpl. reflexivity.
   Case "n = S n".
     simpl. rewrite <- IHn'. reflexivity. Qed.

(** EXERCISE [**]: Use induction to prove the given fact
    [double_plus.] *)
Fixpoint double (n : nat) :=
   match n with
   | O => O
   | S n' => S (S (double n'))
   end.

Lemma double_plus : forall n, double n = n + n.

Proof.
   intros n. induction n as [| n'].
   Case "n = 0".
      simpl. reflexivity.
   Case "n = S n'".
      simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.

(** EXERCISE [*]: Discuss the differences between the induction and
    destruct strategies *)

(** Using the [destruct] tactic results in Coq specifically going to
    the data type definition, and generating cases for each member
    of the data type. Induction is a more powerful reasoning principle:
    prove a base case P(b) (when working over the natural numbers, this is
    usually proving your proposition for [b = 0]). Then, prove that, for
    all n in N, P(n) => P(n+1). The common analogy is dominoes falling.
    You've already proved P(b), then using the proven inductive impl.,
    you get P(b+1), P(b+2), and so on and so forth. *)

