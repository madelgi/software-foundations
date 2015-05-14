Add LoadPath "../Basics".
Add LoadPath "../Induction".

Require Import Lists.
Require Import EnumTypes.
Require Import Induction.
Require Import NamingCases.

(** Simplification can sometimes be good enough for
    lists, too *)
Theorem nil_app : forall l : natlist,
   [] ++ l = l.

Proof.
   reflexivity. Qed.

(** Case analysis can also be good *)
Theorem tl_length_pred : forall l : natlist,
   pred (length l) = length (tl l).

Proof.
   intros l. destruct l as [| n l'].
   Case "l = []".
      reflexivity.
   Case "l = cons n l'".
      reflexivity. Qed.


(**********************)
(* INDUCTION ON LISTS *)
(**********************)

(** Induction can be performed on lists in a pretty straightforward
    manner. For some proposition [P] and a list [l],

    1. Prove that [P] is true when [l = nil] (base case)
    2. Assuming [P(l')] is true, show that [P] is true for [l] when
    [l = n :: l'], where [n] is some number and [l'] is a smaller list.

*)

(** Example of induction on lists. this proves that [++] is associative *)
Theorem app_assoc : forall l1 l2 l3 : natlist,
   (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).

Proof.
   intros l1 l2 l3. induction l1 as [| n l1'].
   Case "l1 = nil".
      reflexivity.
   Case "l1 = cons n l1'".
      simpl. rewrite -> IHl1'. reflexivity. Qed.

(** Another example of list induction. *)
Theorem app_length : forall l1 l2 : natlist,
   length (l1 ++ l2) = (length l1) + (length l2).

Proof.
   intros l1 l2. induction l1 as [| n l1'].
   Case "l1 = nil".
      reflexivity.
   Case "cons n l1'".
      simpl. rewrite -> IHl1'. reflexivity. Qed.

(** Let's create a cons function that attaches an element on the right *)
Fixpoint snoc (l : natlist) (v : nat) : natlist :=
   match l with
   | nil => [v]
   | h :: t => h :: (snoc t v)
   end.

(** Now we can use [snoc] to create a list reversing funciton *)
Fixpoint rev (l : natlist) : natlist :=
   match l with
   | nil => nil
   | h :: t => snoc (rev t) h
   end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

(** Now we can prove some facts about reverse. First, we try to prove that
    reversing a list does not change its length *)
Theorem rev_length_firsttry : forall l : natlist,
   length (rev l) = length l.

Proof.
   intros l. induction l as [| n l'].
   Case "l = []".
      reflexivity.
   Case "l = n :: l'".
      simpl. rewrite <- IHl'.
Abort.

(** Above, we became stuck. Let's isolate the part we get stuck on, and
    prove that. *)
Theorem length_snoc : forall n : nat, forall l : natlist,
   length (snoc l n) = S (length l).

Proof.
   intros n l. induction l as [| x l'].
   Case "l = []".
      reflexivity.
   Case "l = x :: l'".
      simpl. rewrite -> IHl'. reflexivity. Qed.

(** with [length_snoc], we can return to the original proof. *)
Theorem rev_length : forall l : natlist,
   length (rev l) = length l.

Proof.
   intros l. induction l as [| n l'].
   Case "l = []".
      reflexivity.
   Case "l = n :: l'".
      simpl. rewrite -> length_snoc. rewrite -> IHl'. reflexivity. Qed.

(************************)
(* LIST EXERCISES PT. 1 *)
(************************)

(** EXERCISE [***]: Prove the following theorems. *)

(* appending a nil list does nothing *)
Theorem app_nil_end : forall l : natlist,
   l ++ [] = l.

Proof.
   intro l. induction l as [| n l'].
   Case "l = []".
      reflexivity.
   Case "l = n :: l'".
      simpl. rewrite -> IHl'. reflexivity. Qed.

(** Lemma for the upcoming theorem *)
Lemma rev_snoc: forall (l : natlist) (n : nat),
   rev (snoc l n) = n :: (rev l).

Proof.
   intros l n. induction l as [| x l'].
   Case "l = []".
      reflexivity.
   Case "l = x :: l'".
      simpl. rewrite -> IHl'. reflexivity. Qed.

(** rev is its own inverse *)
Theorem rev_involutive : forall l : natlist,
   rev (rev l) = l.

Proof.
   intro l. induction l as [| n l'].
   Case "l = []".
      reflexivity.
   Case "l = n :: l'".
      simpl. rewrite -> rev_snoc.
      rewrite -> IHl'. reflexivity. Qed.

(** extend associativity *)
Theorem app_assoc4: forall l1 l2 l3 l4 : natlist,
   l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.

Proof.
   intros l1 l2 l3 l4. rewrite -> app_assoc.
   rewrite -> app_assoc. reflexivity. Qed.

(** an alternate definition of [snoc], in some sense *)
Theorem snoc_append : forall (l : natlist) (n : nat),
   snoc l n = l ++ [n].

Proof.
   intros l n. induction l as [| x l'].
   Case "l = []".
      reflexivity.
   Case "l = x :: l'".
      simpl. rewrite -> IHl'. reflexivity. Qed.

(** TODO: this is a pretty bad proof. Can it be made better? *)
Theorem distr_rev : forall l1 l2 : natlist,
   rev (l1 ++ l2) = (rev l2) ++ (rev l1).

Proof.
   intros l1 l2. induction l1 as [| x l1'].
   Case "l1 = []".
      assert (H: rev [] = []).
      SCase "Assertion H".
         simpl. reflexivity.
      rewrite -> nil_app. rewrite -> H.
      rewrite -> app_nil_end. reflexivity.
   Case "l1 = x :: l1'".
      simpl. rewrite -> IHl1'. rewrite -> snoc_append.
      assert (H': snoc (rev l1') x = (rev l1') ++ [x]).
      SCase "Assertion H'".
         rewrite -> snoc_append. reflexivity.
      rewrite -> H'. rewrite -> app_assoc. reflexivity. Qed.

(* asserts that we can distribute [nonzeros] across [++] *)
Lemma nonzeros_app : forall l1 l2 : natlist,
   nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).

Proof.
   intros l1 l2. induction l1 as [| x l1'].
   Case "l1 = []".
      reflexivity.
   Case "l1 = x :: l1'".
      simpl. destruct x as [| x'].
      SCase "x = 0".
         rewrite IHl1'. reflexivity.
      SCase "x = S x'".
         rewrite IHl1'. reflexivity. Qed.

(** EXERCISE [**]: fill in the definition of [beq_natlist], which
    compares lists of numbers for equality. Next, prove that
    [beq_natlist l l = true] for all [l : natlist]. *)
Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
   match l1, l2 with
   | [], [] => true
   | [], _  => false
   | _, []  => false
   | (x :: xs), (y :: ys) => if beq_nat x y
                             then beq_natlist xs ys
                             else false
   end.

Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l : natlist,
   true = beq_natlist l l.

Proof.
   intro l. induction l as [| x l'].
   Case "l = []".
      reflexivity.
   Case "l = x :: l'".
      simpl. rewrite -> beq_nat_refl. rewrite -> IHl'.
      reflexivity. Qed.


(************************)
(* LIST EXERCISES PT. 2 *)
(************************)

(** EXERCISE [**]: Write down a non-trivial theorem [cons_snoc_app]
    involving [cons], [snoc], and [app], and then prove it TODO *)
Theorem cons_snoc_app: forall (n:nat) (l1 l2 : natlist),
   true = true.

Proof. Admitted.



(** EXERCISE [***, advanced]: Several theorems about the definition of
    [bag], from earlier in the section *)
Theorem count_member_nonzero : forall (s : bag),
   ble_nat 1 (count 1 (1 :: s)) = true.

Proof.
   intro s. reflexivity. Qed.

(* A lemma to help us with the following proof *)
(* Note to self: Coq is smart enough to infer the type of [n], here *)
Lemma ble_n_Sn : forall n,
   ble_nat n (S n) = true.

Proof.
   intros n. induction n as [| n'].
   Case "0".
      reflexivity.
   Case "S n'".
      simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_decreases_count: forall (s : bag),
   ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.

Proof.
   intros s. induction s as [| x s'].
   Case "s = []".
      reflexivity.
   Case "s = x :: s'".
      destruct x as [| x'].
      SCase "x = 0".
         simpl. rewrite ble_n_Sn. reflexivity.
      SCase "x = S x'".
         simpl. rewrite IHs'. reflexivity. Qed.

(** EXERCISE [***]: Write down an interessting theorem [bag_count_sum]
    about bags involving the functions [count] and [sum], and prove it
    TODO *)
Theorem bag_count_sum : forall (s1 s2 : bag) (n : nat),
   count n (sum s1 s2) = (count n s1) + (count n s2).

Proof.
   intros s1 s2 n. induction s1 as [| x s1'].
   Case "s1 = []".
      reflexivity.
   Case "s1 = x :: s1'".
      simpl. rewrite IHs1'. destruct x as [| x']. destruct n as [| n'].
      SCase "x = n = 0".
         reflexivity.
      SCase "x = 0, n = S n'".
         reflexivity.
      SCase "x = S x', n = 0".
Abort.

(** EXERCISE [****, advanced]: Prove that the rev function is injective,
    that is: *)
Theorem rev_inj: forall (l1 l2 : natlist),
   rev l1 = rev l2 -> l1 = l2.

Proof.
   intros l1 l2. intro H.
   rewrite <- rev_involutive. rewrite <- H.
   rewrite -> rev_involutive. reflexivity. Qed.
