(********************)
(* DAYS OF THE WEEK *)
(********************)
Inductive day : Type :=
   | monday : day
   | tuesday : day
   | wednesday : day
   | thursday : day
   | friday : day
   | saturday : day
   | sunday : day.

Definition next_weekday (d:day) : day :=
   match d with
   | monday => tuesday
   | tuesday => wednesday
   | wednesday => thursday
   | thursday => friday
   | friday => monday
   | saturday => monday
   | sunday => monday
   end.

Eval compute in (next_weekday friday).
Eval compute in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
   (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.


(******************)
(* BOOLEAN VALUES *)
(******************)

Inductive bool : Type :=
   | true : bool
   | false : bool.

(* Negation *)
Definition negb (b:bool) : bool :=
   match b with
   | true => false
   | false => true
   end.

(* Logical and *)
Definition andb (b1:bool) (b2:bool) : bool :=
   match b1 with
   | true => b2
   | false => false
   end.

(* Logical or *)
Definition orb (b1:bool) (b2:bool) : bool :=
   match b1 with
   | true => true
   | false => b2
   end.

(* These four unit tests build a truth table for
 * the orb function.
 *)
Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb2: (orb true true) = true.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb false false) = false.
Proof. reflexivity. Qed.

(* EXERCISE [*]: Complete the definition of the
 * nand function
 *)
Definition nandb (b1:bool) (b2:bool) : bool :=
   match b1 with
   | true => (negb b2)
   | false => true
   end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

(* EXERCISE [*]: Complete the definition of andb3
 * based on the provided tests
 *)

(* TODO *)


(******************)
(* FUNCTION TYPES *)
(******************)

(* The `Check` command will make Coq print the type
   the type of an expression *)
Check true.        (* ===> true : bool *)
Check (negb true). (* ===> negb true : bool *)
Check negb.        (* ===> negb : bool -> bool *)


(***********)
(* NUMBERS *)
(***********)
Module Playground1.

(* A natural number type, defined using inductive
   rules. This is the standard `Nil`/Successor model
 *)
Inductive nat : Type :=
   | O : nat
   | S : nat -> nat.

Definition pred (n : nat) : nat :=
   match n with
      | O => O
      | S n' => n'
   end.

End Playground1.

Definition minustwo (n : nat) : nat :=
   match n with
      | O => O
      | S O => O
      | S (S n') => n'
   end.

(* Coq knows how to use arabic numerals *)
Check (S (S (S (S O)))).
Eval compute in (minustwo 4).

(* Type signatures of some nat functions *)
Check S.        (* nat -> nat *)
Check pred.     (* nat -> nat *)
Check minustwo. (* nat -> nat *)

(** Determines whether a number is even or not. Note
    the use of [Fixpoint]. This indicates a recursive
    definition *)
Fixpoint evenb (n:nat) : bool :=
   match n with
   | O => true
   | S O => false
   | S (S n') => evenb n'
   end.

(** Can define an oddb function in terms of evenb *)
Definition oddb (n:nat) : bool :=
   negb (evenb n).     (* defined as NOT (even x) *)

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Module Playground2.

(** Define a two arg function, plus, using
    recursion *)
Fixpoint plus (n : nat) (m : nat) : nat :=
   match n with
   | O => m
   | S n' => S (plus n' m)
   end.

Eval compute in (plus (S (S (S O)))) (S (S O)).

(** Similar mult definition. Note that when n,m are
    the same type, we don'te have to make separate
    declarations *)
Fixpoint mult (n m : nat) : nat :=
   match n with
   | O => O
   | S n' => plus m (mult n' m)
   end.

(** Can match two expressions at once by splitting
    them with a comma *)
Fixpoint minus (n m : nat) : nat :=
   match n, m with
   | O, _ => O
   | S _ , O => n
   | S n', S m' => minus n' m'
   end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
   match power with
   | O => S O
   | S p => mult base (exp base p)
   end.

(** EXERCISE [*]: Translate the factorial function
    into Coq *)
Fixpoint factorial (n : nat) : nat :=
   match n with
   | O => S O
   | S n' => mult (S n') (factorial n')
   end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

(** Coq supports defining inline notation *)
Notation "x + y" :=
   (plus x y)
      (at level 50, left associativity)
      : nat_scope.

Notation "x - y" :=
   (minus x y)
      (at level 50, left associativity)
      : nat_scope.

Notation "x * y" :=
   (mult x y)
      (at level 40, left associativity)
      : nat_scope.

Check ((0 + 1) + 1).

(** Testing for lessthan/equality of natural
    numbers. One notable feature of this function is
    that it uses nested [match] statements. Could have
    also used a simultaneous match, as we did in
    our [minus] definition *)
Fixpoint beq_nat (n m : nat) : bool :=
   match n with
   | O => match m with
          | O => true
          | S m' => false
          end
   | S n' => match m with
             | O => false
             | S m' => beq_nat n' m'
             end
   end.

(** Basically same func as above, now tests for
    less than / equality *)
Fixpoint ble_nat (n m : nat) : bool :=
   match n with
   | O => true
   | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
   end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

(** EXERCISE [**]: Create a test for less than, using
    the previosly defined two functions *)
Definition blt_nat (n m : nat) : bool :=
   match (ble_nat n m) with
   | false => false
   | true =>
      match (beq_nat n m) with
      | true => false
      | false => true
      end
   end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.
