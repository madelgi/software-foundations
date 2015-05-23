Add LoadPath "Basics".
Add LoadPath "Induction".
Add LoadPath "Lists".
Add LoadPath "Poly".
Require Import Lists.
Require Import EnumTypes.
Require Import Induction.
Require Import NamingCases.
Require Export Reasoning.
Require Export Polymorphism.
Require Export FunctionsAsData.

(********************)
(* THE APPLY TACTIC *)
(********************)

(** This theorem is redundant *)
Theorem silly1 : forall (n m o p : nat),
   n = m ->
   [n;o] = [n;p] ->
   [n;o] = [m;p].

Proof.
   intros n m o p eq1 eq2.
   rewrite <- eq1.
   apply eq2. Qed.

Theorem silly2 : forall (n m o p : nat),
   n = m ->
   (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
   [n;o] = [m;p].

Proof.
   intros n m o p eq1 eq2.
   apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
   (n,n) = (m,m) ->
   (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
   [n] = [m].

Proof.
   intros n m eq1 eq2.
   apply eq2. apply eq1. Qed.

(** EXERCISE [**]: Complete the following proof without using [simpl] *)
Theorem silly_ex :
   (forall n, evenb n = true -> oddb (S n) = true) ->
   evenb 3 = true ->
   oddb 4 = true.

Proof.
   intros h1 h2. apply h1. apply h2.
Qed.

(** Note that using [apply] requires that the conclusion of the fact
    being applied matches the goal exactly. Here's an example where
    apply will not work because the sides of the equality are swapped. *)
Theorem silly3_firsttry : forall (n : nat),
   true = beq_nat n 5 ->
   beq_nat (S (S n)) 7 = true.

Proof.
   intros n H.
   simpl.
Abort.

(** Can make coq not be an idiot by using [symmetry] *)
Theorem silly3 : forall (n : nat),
   true = beq_nat n 5 ->
   beq_nat (S (S n)) 7 = true.

Proof.
   intros n H.
   symmetry. apply H.
Qed.

SearchAbout rev.

(** EXERCISE [***]: Prove the following theorem. *)
Theorem rev_exercise1 : forall (l l' : list nat),
   l = rev l' ->
   l' = rev l.

Proof.
   intros l l'. intro H.
   rewrite -> H. symmetry. apply rev_involutive.
Qed.

(********************************)
(* The [apply...with...] Tactic *)
(********************************)

(** Here we use two rewrites in a row to get from [a,b] to [e,f] *)
Example trans_eq_example : forall (a b c d e f : nat),
   [a;b] = [c;d] ->
   [c;d] = [e;f] ->
   [a;b] = [e;f].

Proof.
   intros a b c d e f eq1 eq2.
   rewrite eq1. rewrite eq2. reflexivity.
Qed.

(** This is a pretty common pattern, so we can extract it out into a
    Lemma *)
Lemma trans_eq : forall (X : Type) (n m o : X),
   n = m -> m = o -> n = o.

Proof.
   intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
   reflexivity.
Qed.

(** Now, we can prove [trans_eq_example] w/ [trans_eq], but to do
    so, we need a slight modification of [trans_eq]. We need to replace
    the [m] with [[c;d]]. We can use the [apply...with...] tactic to
    do this *)
Example trans_eq_example' : forall (a b c d e f : nat),
   [a;b] = [c;d] ->
   [c;d] = [e;f] ->
   [a;b] = [e;f].

Proof.
   intros a b c d e f eq1 eq2.
   apply trans_eq with (m:=[c;d]). apply eq1. apply eq2.
Qed.

(** note we could just write [apply trans_eq with [c;d]], the [m] isn't
    necessary *)

(** EXERCISE [***]: Prove the following example *)
Example trans_eq_exercise : forall (n m o p : nat),
   m = (minustwo o) ->
   (n + p) = m ->
   (n + p) = (minustwo o).

Proof.
   intros n m o p eq1 eq2.
   apply trans_eq with m. apply eq2. apply eq1.
Qed.

(**************************)
(* The [inversion] Tactic *)
(**************************)

(** Some facts about inductively defined types:

      > Constructors are injective
      > Values built from distinct constructors are never equal.

So for lists, for example, [cons] is injective and [[]] is equal to no
non-empty lists.

Coq exploits these facts w/ an [inversion] tactic. Suppose [H] is a
hypothesis of the form

   > [c a1 a2 ... an] = [d b1 b2 ... bm]

for some constructors [c],[d] and args [a1 ... an], [b1 ... bm].
[inversion] makes COq inver this equality to extract info it contains
about the component terms:

   > if c and d are the same constructor, then we must have a1 = b1, ...,
     an = bn. [inversion H] adds these equalities to the context, and
     automatically tries to use them to rewrite the goal.
   > if c and d are different, then our hypothesis is contradictary.
     Meaning everything follows by RAA.

*)

(* Here's an example of inversion in action *)
Theorem eq_add_S : forall (n m : nat),
   S n = S m ->
   n = m.

Proof.
   intros n m eq. inversion eq. reflexivity.
Qed.

(** EXERCISE [*]: Prove the following example *)
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
   x :: y :: l = [] ->
   y :: l = z :: j ->
   x = z.

Proof.
   intros X x y z l j eq1 eq2.
   inversion eq1.
Qed.


(*******************************)
(* Using Tactics on Hypotheses *)
(*******************************)

(** Most tactics edit the goal formula, leaving the context unchanged.
    There is a way to apply tactics to context statements *)
Theorem S_inj : forall (n m : nat) (b : bool),
   beq_nat (S n) (S m) = b ->
   beq_nat n m = b.

Proof.
   intros n m b H. simpl in H. apply H.
Qed.

(** The [<tactic> in <hypothesis>] format helped us prove the above
    theorem. Here's a variant of the proof from above, using forward
    reasoning rather than backward reasoning (see text for deets on
    the differences between these two styles *)
Theorem silly3' : forall (n : nat),
   (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
      true = beq_nat n 5 ->
      true = beq_nat (S (S n)) 7.

(** NOTE: for some reason the [apply] tactic is generating an error,
    seems to be saying [eq] has no assumption, which is untrue. Maybe
    it's a typo? *)
Proof.
   intros n eq H. symmetry in H.
   (*apply H in eq*)
Admitted.

(** EXERCISE [***]: Practice with [in] variants by proving this theorem
    *)
Lemma plus_m_m_Zero : forall (m : nat),
   m + m = 0 ->
   m = 0.

Proof.
   intros m h1. induction m as [| m'].
   Case "m = 0".
      reflexivity.
   Case "m = S m'".
      inversion h1.
Qed.

(** This and the theorem below seem a bit verbose. TODO: possibly
    improve? *)
Lemma remove_S : forall (n m : nat),
   n = m ->
   S n = S m.

Proof.
   intros n m h. induction n as [| n'].
   Case "n = O".
      symmetry in h. rewrite h. reflexivity.
   Case "n = S n'".
      rewrite h. reflexivity.
Qed.

Theorem plus_n_n_injective : forall (n m : nat),
   n + n = m + m ->
   n = m.

Proof.
   intros n. induction n as [| n'].
   Case "n = 0".
      intro m. destruct m as [| m'].
      SCase "m = O".
         reflexivity.
      SCase "m = S m'".
         simpl. intro h1. inversion h1.
   Case "n = S n'".
      intro m. destruct m as [| m'].
      SCase "m = O".
         intro h2. inversion h2.
      SCase "m = S m'".
         intro h3. apply remove_S. apply IHn'. simpl in h3.
         rewrite <- plus_n_Sm in h3.
         rewrite <- plus_n_Sm in h3.
         inversion h3. reflexivity.
Qed.

(************************************)
(* Varying the induction hypothesis *)
(************************************)

(** We must be careful about which of the assumptions we move from the
    goal to the context before invoking the induction tactic *)

(* WRONG *)
Theorem double_injective_FAILED : forall (n m : nat),
   double n = double m ->
   n = m.

Proof.
   intros n m. induction n as [| n'].
   Case "n = O".
      simpl. intros eq. destruct m as [| m'].
      SCase "m = O".
         reflexivity.
      SCase "m = S m'".
         inversion eq.
   Case "n = S n'".
      intros eq. destruct m as [| m'].
      SCase "m = O".
         inversion eq.
      SCase "m = S m'".
         apply f_equal.
         (* And now we're stuck. [IHn'] does not give us [n' = m'].
            There's an extra [S] in the way! *)
Abort.

(** In the above attempt, we told Coq to consider a particular n and
    m. The proof then becomes, if [double n = double m], prove that
    [n = m] for a particular [n] and [m]. In the inductive step, we
    get stuck with this particular [m]. *)

(* Correct *)
Theorem double_injective: forall (n m : nat),
   double n = double m ->
   n = m.

Proof.
   intros n. induction n as [| n'].
   Case "n = O".
      simpl. intros m eq. destruct m as [| m'].
      SCase "m = O".
         reflexivity.
      SCase "m = S m'".
         inversion eq.
   Case "n = S n'".
      intros m eq. destruct m as [| m'].
      SCase "m = O".
         inversion eq.
      SCase "m = S m'".
         apply f_equal.
         apply IHn'. inversion eq. reflexivity.
Qed.

(** EXERCISE [**]: Prove the following theorem. *)
Theorem beq_nat_true : forall (n m : nat),
   beq_nat n m = true ->
   n = m.

Proof.
   intros n. induction n as [| n'].
   Case "n = O".
      simpl. intros m eq. destruct m as [| m'].
      SCase "m = O".
         reflexivity.
      SCase "m = S m'".
         inversion eq.
   Case "n = S n'".
      intros m eq. destruct m as [| m'].
      SCase "m = O".
         inversion eq.
      SCase "m = S m'".
         apply f_equal. apply IHn'. inversion eq. reflexivity.
Qed.

(** EXERCISE [**]: Prove the following theorem. *)
