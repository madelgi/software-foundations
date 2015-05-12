Module Simplification.

Theorem plus_O_n : forall n : nat, 0 + n = n.
   Proof.
      intros n. reflexivity. Qed.

Theorem plus_n_O : forall n : nat, n + 0 = 0.
   Proof.
      simpl.
   Abort.

End Simplification.
