Add LoadPath "../Basics".
Add LoadPath "../Induction".
Add LoadPath "../Lists".

Require Import Lists.
Require Import EnumTypes.
Require Import Induction.
Require Import NamingCases.
Require Export Reasoning.
Require Export Polymorphism.
Require Export FunctionsAsData.

(** EXERCISE [**]: Prove the correctness of [fold_length] *)
Definition fold_length {X : Type} (l : list X) : nat :=
   fold (fun _ n => S n) l 0.

Theorem fold_length_correct : forall X (l : list X),
   fold_length l = length l.

Proof.
   intros X l. induction l as [| x l'].
   Case "l = []".
      reflexivity.
   Case "l = x :: l'".
      simpl. rewrite <- IHl'. reflexivity. Qed.

(** EXERCISE [***]: We can define [map] in terms of fold. Finish the
    the definition, and then prove [fold_map_corrrect] *)
Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
   fold (fun x xs => (f x) :: xs) l [].

Theorem fold_map_correct : forall (X Y : Type) (l : list X) (f : X -> Y),
   fold_map f l = map f l.

Proof.
   intros X Y l f. induction l as [| x l'].
   Case "l = []".
      reflexivity.
   Case "l = x :: l'".
      simpl. rewrite <- IHl'. reflexivity. Qed.

(** EXERCISE [**]: Write an informal proof of the following theorem:

    > For all X n l, length l = n --> @index X n l = None.

   TODO *)

(** EXERCISE [****]: Church numerals *)
Module Church.

Definition nat := forall X : Type, (X -> X) -> X -> X.

Definition zero : nat :=
   fun (X : Type) (f : X -> X) (x : X) => x.

Definition one : nat :=
   fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : nat :=
   fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : nat :=
   fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).

(* Definition of successor *)
Definition succ (n : nat) : nat :=
   fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.

Example succ_2 : succ one = two.
Proof. reflexivity. Qed.

Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

(* Definition of addition *)
Definition plus (n m : nat) : nat :=
   fun (X : Type) (f : X -> X) (x : X) => m X f (n X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 :
     plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(* Definition of multiplication *)
Definition mult (n m : nat) : nat :=
   fun (X : Type) (f : X -> X) => n X (m X f).

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

(* Definition of exponentiation TODO *)
Definition exp (n m : nat) : nat :=
   fun (X : Type) (f : X -> X) => (n X) (m X f).

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

Example exp_3 : exp three zero = one.
Proof. reflexivity. Qed.

End Church.
