Add LoadPath "../Basics".
Add LoadPath "../Induction".
Require Import EnumTypes.
Require Import Induction.
Require Import NamingCases.

(** An inductive type for lists. Uses the familiar x1 :: x2 :: ...
    :: xn :: Nil approach. *)
Inductive natlist : Type :=
   | nil : natlist
   | cons : nat -> natlist -> natlist.

Definition testlist := cons 1 (cons 2 (cons 3 nil)).

(** Some helpful notation for lists, using [::] as an infix cons
    operator. *)
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(**********)
(* REPEAT *)
(**********)

(** Takes a number [n] and a [count] and returns a length of [count] where
    every element is [n] *)
Fixpoint repeat (n count : nat) : natlist :=
   match count with
   | O => nil
   | S count' => n :: (repeat n count')
   end.

(** Test *)
Eval compute in (repeat 3 6).

(**********)
(* LENGTH *)
(**********)

(** The [length] function calculates the length of a list *)
Fixpoint length (l : natlist) : nat :=
   match l with
   | nil => 0
   | h :: t => 1 + (length t)
   end.

(** Test *)
Eval compute in (length [1;2;3;4;5;2]).

(**********)
(* APPEND *)
(**********)

(** [app]end two lists together *)
Fixpoint app (l1 l2 : natlist) : natlist :=
   match l1 with
   | nil => l2
   | h :: t => h :: (app t l2)
   end.

(** Some convenient [app]-related notation. We use the haskell [++]
    append infixr *)
Notation "x ++ y" := (app x y) (right associativity, at level 60).

(** Some [app] tests *)
Example test_app1: [1;2;3] ++ [2;3] = [1;2;3;2;3].
Proof. reflexivity. Qed.
Example test_app2: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.
Example test_app3: [] ++ [1;2;3] = [1;2;3].
Proof. reflexivity. Qed.

(*****************)
(* HEAD and TAIL *)
(*****************)

(** The haskell [head] function, but with a default value that is
    returned when the function is passed a [nil] [natlist]. *)
Definition hd (default : nat) (l : natlist) : nat :=
   match l with
   | nil => default
   | h :: t => h
   end.

(** Return every list element except for the head *)
Definition tl (l : natlist) : natlist :=
   match l with
   | nil => nil
   | h :: t => t
   end.

(** EXERCISE [**]: Complete the definitions of [nonzeros], [oddmembers],
    and [countoddmembers] below. *)

(** [nonzeros] removes all instances of [0] from the list *)
Fixpoint nonzeros (l : natlist) : natlist :=
   match l with
   | nil => nil
   | h :: t => match h with
               | O => nonzeros t
               | S h' => h :: (nonzeros t)
               end
   end.

(* Test *)
Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

(** [oddmembers] filters all even elements out of a list *)
Fixpoint oddmembers (l : natlist) : natlist :=
   match l with
   | nil => nil
   | h :: t => if oddb h
               then h :: (oddmembers t)
               else (oddmembers t)
   end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

(** [countoddmembers] counts the number of oddmembers in the list *)
Fixpoint countoddmembers (l : natlist) : nat :=
   match l with
   | nil => 0
   | h :: t => if oddb h
               then 1 + (countoddmembers t)
               else (countoddmembers t)
   end.

(* Tests *)
Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [2;4;6;10] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

(** EXERCISE [***]: Define [alternate], a function that zips up the
    elements of two lists *)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
   match l1 with
   | nil => l2
   | h1 :: t1 => match l2 with
                 | nil => l1
                 | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
                 end
   end.

(* Tests *)
Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [4;5] = [4;5].
Proof. reflexivity. Qed.

(******************)
(* BAGS VIA LISTS *)
(******************)

(** A [bag] is a synonym for a [multiset] *)
Definition bag := natlist.

(** EXERCISE [***]: Define the functions [count], [add], and
    [member] *)

(** [count n xs] determines the number of [n]'s in bag [xs] *)
Fixpoint count (v : nat) (s : bag) :=
   match s with
   | [] => 0
   | h :: t => if beq_nat h v
               then 1 + (count v t)
               else (count v t)
   end.

(* Tests *)
Example test_count1: count 1 [1;2;3;1;2] = 2.
Proof. reflexivity. Qed.
Example test_count2: count 5 [1;2;3;4;8] = 0.
Proof. reflexivity. Qed.

(** [sum xs ys] combines the contents of two bags *)
Definition sum : bag -> bag -> bag :=
   app.

(* Tests *)
Example test_sum1 : count 1 (sum [1;4;1] [1;2;1]) = 4.
Proof. reflexivity. Qed.

(** [add n xs] prepends the element n to the bag xs *)
Definition add (v:nat) (s:bag) : bag :=
   v :: s.

(* Tests *)
Example test_add1: count 1 (add 1 [1;4;3;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 1 (add 3 [1;4;2;1]) = 2.
Proof. reflexivity. Qed.

(** [member n xs] determines whether n is a member of the bag xs *)
Definition member (v:nat) (s:bag) : bool :=
   if beq_nat (count v s) 0
   then false
   else true.

(* Tests *)
Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

(** EXERCISE [***]: More bag functions: [remove_one], [remove_all], and
    [subset] *)

(** Remove the first instances of a value [v] from a bag [s] *)
Fixpoint remove_one (v:nat) (s:bag) : bag :=
   match s with
   | [] => s
   | h :: t => if beq_nat h v
               then t
               else h :: (remove_one v t)
   end.

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: remove_one 5 [2;1;5;4;5;2] = [2;1;4;5;2].
Proof. reflexivity. Qed.

(* remove all elements [v] from a bag [s] *)
Fixpoint remove_all (v:nat) (s:bag) : bag :=
   match s with
   | [] => s
   | h :: t => if beq_nat h v
               then (remove_all v t)
               else h :: (remove_all v t)
   end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;5;4;2;5;3]) = 0.
Proof. reflexivity. Qed.

(* [subset s1 s2] determines if bag s1 is a subset of bag s2 *)
Fixpoint subset (s1:bag) (s2:bag) : bool :=
   match s1 with
   | [] => true
   | h :: t => if (member h s2)
               then (subset t (remove_one h s2))
               else false
   end.

(* Test *)
Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

(** Rewriting this cuz i need it below, and some import technicalities
    are preventing me from getting it *)
Theorem beq_nat_refl : forall (n : nat),
   beq_nat n n = true.

Proof.
   intro n. induction n as [| n'].
   Case "n = 0".
      reflexivity.
   Case "n = n'".
      simpl. rewrite -> IHn'. reflexivity. Qed.


(** EXERCISE [***]: Prove something interesting about the functions
    [count] and [add] on bags *)
Theorem bag_theorem : forall (n : nat) (s : bag),
   count n (add n s) = 1 + (count n s).

Proof.
   intros n s.
   assert (H: (add n s) = n :: s).
      reflexivity.
   rewrite -> H. simpl. rewrite -> beq_nat_refl. reflexivity. Qed.

