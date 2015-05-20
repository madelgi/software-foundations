Add LoadPath "../Basics".
Add LoadPath "../Induction".
Add LoadPath "../Lists".

(* Require Import Lists. *)
Require Import EnumTypes.
Require Import Induction.
Require Import NamingCases.
Require Export Reasoning.
Require Export Polymorphism.

(** NOTE: A lot of the content in "Higher Order Functions", "Partial
    Application", and "Currying" is pretty familiar to me, so I'm not
    going to take notes. Below is the one exercise in "Currying" *)

Definition prod_curry {X Y Z : Type}
   (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x,y).

Definition prod_uncurry {X Y Z : Type}
   (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
   prod_curry (prod_uncurry f) x y = f x y.

Proof.
   reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
   prod_uncurry (prod_curry f) p = f p.

(* TODO *)
Proof.
   intros f p.
Admitted.

(**********)
(* FILTER *)
(**********)

(** [filter :: (a -> bool) -> [a] -> [a]] *)
Fixpoint filter {X:Type} (test: X->bool) (l:list X) : (list X) :=
   match l with
   | [] => []
   | h :: t => if test h
                  then h :: (filter test t)
                  else filter test t
   end.

(* Example, using [evenb] to get even numbers from a list *)
Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

(* Another example, this time defining a new funtion which checks if
   the length of a given list is 1 *)
Definition length_is_1 {X : Type} (l : list X) : bool :=
   beq_nat (length l) 1.

Example test_filter2:
   filter length_is_1 [ [1;2]; [3]; [4]; [5;6;7]; []; [8] ] =
      [ [3]; [4]; [8] ].

Proof. reflexivity. Qed.

(***********************)
(* ANONYMOUS FUNCTIONS *)
(***********************)

(** In the second example above, we use a function [length_is_1]. Taking
    the time to define it is annoying, since it's basically a single use
    function. So yeah, Coq supports anonymous functions *)

Example test_filter2':
   filter (fun l => beq_nat (length l) 1)
      [ [1;2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].

Proof. reflexivity. Qed.

(** EXERCISE [**]: Use [filter] to write a function [filter_even_gt7]
    that takes a list of natural numbers as inpute and returns a list
    of those that are even and greater than 7 *)
Definition filter_even_gt7 (l : list nat) : list nat :=
   let evens := filter (fun n => evenb n) l
   in filter (fun n => ble_nat 8 n) evens.

Example test_filter_even_gt7_1 :
   filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
   filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

(** Use [filter] to write [partition] *)
(* Most straightrforward solution: make a function that removes all
   elements that pass a given test *)
Fixpoint inv_filter {X:Type} (test: X->bool) (l:list X) : (list X) :=
   match l with
   | [] => []
   | h :: t => if test h
                  then inv_filter test t
                  else h :: (inv_filter test t)
   end.

Definition partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
   (filter test l, inv_filter test l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false)
   [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(*******)
(* MAP *)
(*******)

(** [map] applies a function to all elts in a list *)
Fixpoint map {X Y:Type} (f:X -> Y) (l:list X) : (list Y) :=
   match l with
   | [] => []
   | h :: t => (f h) :: (map f t)
   end.

(*******************)
(* MAP FOR OPTIONS *)
(*******************)

(** EXERCISE [***]: Show that [map] and [rev] commute. TODO *)
Lemma map_app : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
   map f (l1 ++ l2) = (map f l1) ++ (map f l2).

Proof.
   intros X Y f l1 l2. induction l1 as [| x l1'].
   Case "l1 = []".
      reflexivity.
   Case "l1 = x :: l1'".
      simpl. rewrite IHl1'. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
   map f (rev l) = rev (map f l).

Proof.
   intros X Y f l. induction l as [| x l'].
   Case "l = []".
      reflexivity.
   Case "l = x :: l'".
Admitted.

(** EXERCISE [**]: Define [flat_map], an alias for [concat_map] *)
Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : (list Y) :=
   match l with
   | [] => []
   | h :: t => (f h) ++ (flat_map f t)
   end.

Example test_flat_map1: flat_map (fun n => [n;n;n]) [1;5;4]
    = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

(** Can map over the [option] type, as well *)
Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                        : option Y :=
   match xo with
   | None => None
   | Some x => Some (f x)
   end.


(********)
(* FOLD *)
(********)

(** [Fold] is as it is in haskell *)
Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l:list X) (b:Y) : Y :=
   match l with
   | nil => b
   | h :: t => f h (fold f t b)
   end.

(****************************************)
(* FUNCTIONS FOR CONSTRUCTING FUNCTIONS *)
(****************************************)

(** Constant function definition *)
Definition constfun {X: Type} (x: X) : nat -> X :=
   fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** Override takes a function on natural numbers, and overrides the
    the value of that function for one input. For every other input,
    the value remains the same. *)
Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat -> X :=
   fun (k':nat) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

(** These tests show how override works. [fmostlytrue] is true for all
    natural numbers with the exception of 1 and 3 *)
Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

(** EXERCISE [*]: Prove the following theorem *)
Theorem override_example : forall (b : bool),
   (override (constfun b) 3 true) 2 = b.

Proof.
   intros b. destruct b.
   Case "b = True".
      reflexivity.
   Case "b = False".
      reflexivity. Qed.

