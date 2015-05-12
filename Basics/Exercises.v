Require Import EnumTypes.

(** EXERCISE [**]: Prove the following theorem about
    boolean functions *)
Theorem identity_fn_applied_twice : forall (f : bool -> bool),
   (forall (x : bool), f x = x) ->
   forall(b : bool), f (f b) = b.

Proof.
   intros f.
   intros H.
      intros x. destruct x.
      rewrite -> H.
      rewrite -> H.
      reflexivity.
      rewrite -> H.
      rewrite -> H.
      reflexivity. Qed.

(** EXERCISE [**]: Prove the following theorem*)
Theorem andb_eq_orb : forall (b c : bool),
   (andb b c = orb b c) ->
   b = c.

Proof.
   Admitted.

(** EXERCISE [***]: Develop a binary system for natural numbers *)

(** PART A. Write an inductive definition of the type bin corresponding
    to the given description *)
Inductive bin : Type :=
   | Ob : bin
   | Db : bin -> bin
   | Dbp : bin -> bin.

(** PART B. Write two functions:

    - [incr]: increment a binary number
    - [bin_to_nat]: converts a binary number to a natural number *)

(** increments a binary number *)
Fixpoint incr (n : bin) : bin :=
   match n with
   | Ob => Dbp Ob
   | Db n' => Dbp n'
   | Dbp n' => Db (incr n')
   end.

(** converts from binary to a natural number *)
Fixpoint bin_to_nat (b : bin) : nat :=
   match b with
   | Ob => O
   | Db b' => 2 * (bin_to_nat b')
   | Dbp b' => 2 * (bin_to_nat b') + 1
   end.

(** PART C. Write some unit tests for your functions *)
Example test_incr1: (incr (Dbp Ob)) = Db (Dbp Ob).
Proof. reflexivity. Qed.
Example test_incr2: (incr (Dbp (Db (Dbp Ob)))) = (Db (Dbp (Dbp Ob))).
Proof. reflexivity. Qed.
Example tst_bin_to_nat1: (bin_to_nat Ob) = O.
Proof. reflexivity. Qed.
Example tst_bin_to_nat2: (bin_to_nat (Dbp (Db (Dbp Ob)))) = 5.
Proof. reflexivity. Qed.
Example test_comb: (bin_to_nat (incr (Dbp (Db (Dbp Ob))))) = 6.
Proof. reflexivity. Qed.
