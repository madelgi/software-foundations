Add LoadPath "../Basics".
Add LoadPath "../Induction".
Add LoadPath "../Lists".

(* Require Import Lists. *)
Require Import EnumTypes.
Require Import Induction.
Require Import NamingCases.
Require Export Reasoning.

(** We can make polymorphic lists *)
Inductive list (X:Type) : Type :=
   | nil : list X
   | cons : X -> list X -> list X.

Check nil.
Check cons.

(** Let's try and re-write our natlist functions, only now they will
    operate over generic, polymorphic lists *)
Fixpoint length (X:Type) (l:list X) : nat :=
   match l with
   | nil => 0
   | cons h t => S (length X t)
   end.

(* Some tests to make sure it works well *)
Example test_length1 : length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.
Example test_length2 : length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

(* Remaining list processing functions *)
Fixpoint app (X:Type) (l1 l2:list X) : (list X) :=
   match l1 with
   | nil => l2
   | cons h t => cons X h (app X t l2)
   end.

Fixpoint snoc (X : Type) (l : list X) (v : X) : (list X) :=
   match l with
   | nil => cons X v (nil X)
   | cons h t => cons X h (snoc X t v)
   end.

Fixpoint rev (X : Type) (l : list X) : list X :=
   match l with
   | nil => nil X
   | cons h t => snoc X (rev X t) h
   end.

Example test_rev1 : rev nat (cons nat 1 (cons nat 2 (nil nat))) =
   (cons nat 2 (cons nat 1 (nil nat))).

Proof. reflexivity. Qed.

Example test_rev2: rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Module MumbleBaz.

(** EXERCISE [**]: Consider the inductively defined types below. Which
    of the given elements are well-typed elements of grumble X *)
Inductive mumble : Type :=
   | a : mumble
   | b : mumble -> nat -> mumble
   | c : mumble.

Inductive grumble (X:Type) : Type :=
   | d : mumble -> grumble X
   | e : X -> grumble X.

(** Element          | Well-typed
    ------------------------------
    d (b a 5)        |
    d mumble (b a 5) |
    d bool (b a 5)   |
    e bool true      |
    e mumble (b c 0) |
    e bool (b c 0)   |
    c                |

    TODO *)

(** EXERCISE [**]: How many elements does the following inductive type
    have?  TODO *)
Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

End MumbleBaz.


(*****************************)
(* TYPE ANNOTATION INFERENCE *)
(*****************************)

(** Let's rewrite [app] without specifying the types of any of the
    arguments *)
Fixpoint app' X l1 l2 : list X :=
   match l1 with
   | nil => l2
   | cons h t => cons X h (app' X t l2)
   end.

(** It works b/c coq is smart enough to infer types. *)


(***************************)
(* TYPE ARGUMENT SYNTHESIS *)
(***************************)

(** We don't have to explicitly write types everywhere. Consider the
    following statement:

      length nat (cons nat 1 (cons nat 5 (nil nat)))

   why do we have to keep throwing around nat? Turns out we don't, we
   can use implicit arguments: *)
Fixpoint length' (X:Type) (l:list X) : nat :=
   match l with
   | nil => 0
   | cons h t => S (length' _ t)
   end.

(** Compare this first definition of list123, where [nat] is explicitly
    specified, to [list123'], which uses argument synthesis *)
Definition list123 :=
   cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).


(*****************)
(* IMPLICIT ARGS *)
(*****************)

(** As you might have guessed, we can even eliminate the underscores. We
    use the [Arguments] directive, which takes the function name, and
    a sequence of arguments to that function, with curly-braces
    indicating that the argument should be treated implicitly *)
Arguments nil {X}.
Arguments cons {X} _ _.
(* underscores are used for unnamed arguments *)
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

(** Another way to accomplish the same goal is by declaring an implicit
    argument in the function definition itself, using curly braces: *)
Fixpoint length'' {X:Type} (l:list X) : nat :=
   match l with
   | nil => O
   | cons h t => S (length'' t)
   end.

(** Sometimes when declaring implicit arguments, Coq will not have enough
    local information to determine a type argument. In these cases, we
    must tell Coq that we want to give the argument explicitly, even
    though the initial declaration was implicit. For example, consider
    this definition:

      Definition mynil := nil

    Uncommenting this definition wil cause an error, because Coq has
    no idea what type should be supplied to nil. We can avoid this by
    providing an explicit type declaration. *)
Definition mynil : list nat := nil.

(** Alternatively, we can force the implict arguments to be explicit by
    prefixing a function name with @ *)
Check @nil.
Definition mynil' := @nil nat.

(** Some notationz *)
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(********************************)
(* EXERCISES: POLYMORPHIC LISTS *)
(********************************)

(** EXERCISE [**]: Fill in the definitions and complete the proofs
    below *)
Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
   match count with
   | O => nil
   | S count' => cons n (repeat n count')
   end.

Example test_repeat1: repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : forall X : Type, forall l : list X,
   app [] l = l.

Proof.
   intros X l. reflexivity. Qed.

Theorem rev_snoc : forall X : Type, forall v : X, forall s : list X,
   rev (snoc s v) = v :: (rev s).

Proof.
   intros X v s. induction s as [| x s'].
   Case "s = []".
      reflexivity.
   Case "s = x :: s'".
      simpl. rewrite IHs'. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
   rev (rev l) = l.

Proof.
   intros X l. induction l as [| x l'].
   Case "l = []".
      reflexivity.
   Case "l = x :: l'".
      simpl. rewrite rev_snoc. rewrite IHl'. reflexivity.
Qed.

Theorem snoc_with_append :
   forall X : Type, forall l1 l2 : list X, forall v : X,
   snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).

Proof.
   intros X l1 l2 v. induction l1 as [| x l1'].
   Case "l1 = []".
      reflexivity.
   Case "l1 = x :: l1'".
      simpl. rewrite IHl1'. reflexivity.
Qed.


(*********************)
(* POLYMORPHIC PAIRS *)
(*********************)

(** Using the same pattern we used for polymorphic lists, we can create
    polymorphic pairs *)
Inductive prod (X Y : Type) : Type :=
   pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

(** The standard [fst] and [snd] function *)
Definition fst {X Y : Type} (p : X * Y) : X :=
     match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
     match p with (x,y) => y end.

(** The next function is [zip], but it is called [combine] for
    consistency reasons *)
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
   match (lx,ly) with
   | ([],_) => []
   | (_,[]) => []
   | (x::tx, y::ty) => (x,y) :: (combine tx ty)
   end.

(** EXERCISE [*]: Try answering the following questions and then check
    your answers in Coq *)

(* Question: What is the type of [combine]? *)
(* Answer: list X -> list Y -> list (prod X Y) *)
Check @combine.

(* Question: What does

      Eval compute in (combine [1;2] [false;true;false;true]).

   print? *)
(* Answer: [(1,false);(2,true)] *)
Eval compute in (combine [1;2] [false;true;false;true]).

(** EXERCISE [**]: The function [split] is the right inverse of combine:
    it takes a list of pairs and returns a pair of lists. Define
    [split] *)
Fixpoint split_help_fst {X Y : Type} (l : list (X*Y)) : (list X) :=
   match l with
   | [] => []
   | h :: t => (fst h) :: (split_help_fst t)
   end.

Fixpoint split_help_snd {X Y : Type} (l : list (X*Y)) : (list Y) :=
   match l with
   | [] => []
   | h :: t => (snd h) :: (split_help_snd t)
   end.

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X)*(list Y) :=
   (split_help_fst l, split_help_snd l).

Example test_split: split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

(** A much more elegant version of [split] using a [let]-expression *)
Fixpoint split' {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
   match l with
   | [] => ([],[])
   | (x,y)::t => let t' := split t
                 in  (x::(fst t'), (y::(snd t')))
   end.


(***********************)
(* POLYMORPHIC OPTIONS *)
(***********************)

(** Let's make our [natoption] type polymorphic *)
Inductive option (X:Type) : Type :=
   | Some : X -> option X
   | None : option X.

Arguments Some {X} _.
Arguments None {X}.

(** Let's make the [index] function polymorphic now *)
Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
   match l with
   | [] => None
   | a :: l' => if beq_nat n O
                  then Some a
                  else index (pred n) l'
   end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1];[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

(** EXERCISE [*]: Complete the definition of a polymorphic version of
    [hd_opt] function from the last chapter. *)
Fixpoint hd_opt {X : Type} (l : list X) : option X :=
   match l with
   | [] => None
   | x::l' => Some x
   end.

Check @hd_opt.

Example test_hd_opt1 : hd_opt [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1];[2]] = Some [1].
Proof. reflexivity. Qed.
