Require Export EnumTypes.

Module Rewriting.

(** A theorem that states if n=m, then n+n=m+m.
    the proof is relatively straightforward. intros
    introduces the variables n and m, and the
    hypothesis H, into the proof context. rewrite
    rewrites the current goal (n + n = m+m) by
    replacing instances of the leftside of H with
    the write side. reflexivity simplifies both
    sides of the `=` to equal values. *)
Theorem plus_id_example : forall n m : nat,
   n = m ->
   n + n = m + m.

   Proof.
      intros n m.
      intros H.
      rewrite -> H.
      reflexivity. Qed.

(** EXERCISE [*]: Prove that for all n,m,o \in N,
    n = m implies that (m = o implies that
    n+m = m+o) *)
Theorem plus_id_exercise : forall n m o : nat,
   n = m -> m = o -> n + m = m + o.

   Proof.
      intros n m o.
      intros H1.
      intros H2.
      rewrite -> H1.
      rewrite -> H2.
      reflexivity. Qed.

(** EXERCISE [**]: Prove that for all n,m in N,
    m = S n implies that m*(1+n) = m*m *)
Theorem mult_S_1 : forall n m : nat,
   m = S n ->
   m * (1 + n) = m * m.

   Proof.
      intros n m.
      intros H.
      rewrite -> H.
      reflexivity. Qed.

End Rewriting.
