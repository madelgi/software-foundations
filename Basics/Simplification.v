Require Export EnumTypes.

Module Simplification.

(** Simplification is the most basic form of proof, in some sense. [simpl] is
    similar to [reflexivity], but it does less. While [reflexivity] will expand
    definitions willy-nilly, [simpl] is a bit more conservative *)
Theorem plus_O_n : forall n : nat, 0 + n = n.
   Proof.
      intros n. reflexivity. Qed.

Theorem plus_n_O : forall n : nat, n + 0 = 0.
   Proof.
      simpl.
   Abort.

End Simplification.
