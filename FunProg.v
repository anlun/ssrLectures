(** %\chapter{Functional Programming in Coq} *)

Module FunProg.

(** * Enumeration datatypes *)

Inductive unit : Set := tt.

Check tt.

(**
[[
tt
     : unit
]]
*)

Check unit.

(**
[[
unit
     : Set
]]
*)

Inductive empty : Set := .

Require Import ssreflect ssrbool.

Print bool.
(** 
[[
Inductive bool : Set :=  true : bool | false : bool
]] 
*)

(** 

Let us now try to define some functions that operate with the bool
datatype ignoring for a moment the fact that most of them, if not all,
are already defined in the standard Coq/SSReflect library.  Our first
function will simply negate the boolean value and return its opposite:

*)

Definition negate b := 
  match b with 
  | true  => false
  | false => true
  end.

Check negate.
(**
[negate : bool -> bool
]

* Simple recursive datatypes and programs

*)

Print nat.

(**
[Inductive nat : Set :=  O : nat | S : nat -> nat]

*)

Require Import ssrnat.

Fixpoint my_plus n m := 
 match n with 
 | 0     => m   
 | n'.+1 => (my_plus n' m).+1 (*let: tmp := my_plus n' m in tmp.+1*)
 end.

Eval compute in my_plus 5 7. 
(** 
[  = 12 : nat] 
*)

Fixpoint my_plus' n m := if n is n'.+1 then (my_plus' n' m).+1 else m.

(**
[[
Fixpoint my_plus_buggy n m := 
    if n is n'.+1 then (my_plus_buggy n m).+1 else m.
]]

we immediately get the following error out of the Coq interpreter:

[[
Error: Cannot guess decreasing argument of fix.
]]

*)

Check nat_rec.

(*
Definition my_plus'' (n : nat) (m : nat) : nat :=
  nat_rec (fun _ => nat) m (fun k v => if k is 0 then v else v * k) n.

Eval compute in my_plus'' 5 1.
*)

(** 
[[
nat_rec : forall P : nat -> Set,
          P 0 -> (forall n : nat, P n -> P n.+1) -> forall n : nat, P n
]]

To see how [nat_rec] is implemented, let us explore its generalized
version, [nat_rect]:

*)

Print nat_rect.
(** 
[[
nat_rect = 
 fun (P : nat -> Type) (f : P 0) (f0 : forall n : nat, P n -> P n.+1) =>
 fix F (n : nat) : P n :=
   match n as n0 return (P n0) with
   | 0 => f
   | n0.+1 => f0 n0 (F n0)
   end
      : forall P : nat -> Type,
        P 0 -> (forall n : nat, P n -> P n.+1) -> forall n : nat, P n
]]

*)

Definition my_plus1 n m := nat_rec (fun _ => nat) m (fun n' m' => m'.+1) n.

Eval compute in my_plus1 16 12.

(** 
[    = 28 : (fun _ : nat => nat) 16]

** Dependent function types and pattern matching

*)

Check nat_rec.

Definition sum_no_zero n := 
 let: P := (fun n => if n is 0 then unit else nat) in
 nat_rec P tt (fun n' m => 
match n' return P n' -> _ with
   | 0 => fun _ => 1
   | n1.+1 => fun m => my_plus m (n'.+1) 
end m) n.

(*
Definition three_to_unit n := 
 let: P := (fun n => if n is 3 then unit else nat) in
 nat_rec P 0 (fun n' _ => match n' return P n'.+1 with
               | 2 => tt
               | _ => n'.+1
               end) n.

Eval compute in three_to_unit 0.
*)

Eval compute in sum_no_zero 0.

(** 

[ 
     = tt
     : (fun n : nat => match n with
                       | 0 => unit
                       | _.+1 => nat
                       end) 0
]

*)

Eval compute in sum_no_zero 5.
(** 
[[
     = 15
     : (fun n : nat => match n with
                       | 0 => unit
                       | _.+1 => nat
                       end) 5
]]

Had we omitted the [return] clauses in the pattern matching, we would
get the following type-checking error, indicating that Coq cannot
infer that the type of [my_plus]' argument is always [nat], so it
complains:

[[
Definition sum_no_zero' n := 
 let: P := (fun n => if n is 0 then unit else nat) in
 nat_rec P tt (fun n' m => 
match n' with
   | 0 => fun _ => 1
   | n1.+1 => fun m => my_plus m (n'.+1) 
end m) n.
]]

[[
Error:
In environment
n : ?37
P := fun n : nat => match n with
                    | 0 => unit
                    | _.+1 => nat
                    end : nat -> Set
n' : nat
m : P n'
The term "m" has type "P n'" while it is expected to have type "nat".
]]
*)

(** ** Recursion principle and non-inhabited types *)

Check empty_rect.

Print empty_rect.

(** 
[[
empty_rect
     : forall (P : empty -> Type) (e : empty), P e
]]


Assuming existence of a value, which \emph{cannot be constructed}, we
will be able to construct \emph{anything}.
 
*)

Inductive strange : Set :=  cs : strange -> strange.

Check strange_rect.

(** 
[[
strange_rect
     : forall P : strange -> Type,
       (forall s : strange, P s -> P (cs s)) -> forall s : strange, P s
]]
*)

Definition strange_to_empty (s: strange): empty :=
  strange_rect (fun _ => empty) (fun s e => e) s.

(** * More datatypes *)

(* Pairs *)

Check prod.

(**
[[
prod : Type -> Type -> Type

]]
*)

Print prod.

(** 
[[
Inductive prod (A B : Type) : Type :=  pair : A -> B -> A * B

For pair: Arguments A, B are implicit and maximally inserted
For prod: Argument scopes are [type_scope type_scope]
For pair: Argument scopes are [type_scope type_scope _ _]
]]
*)

Check pair 1 tt.

(** 
[[
(1, tt) : nat * unit

]]

If one wants to explicitly specify the type arguments of a
constructor, the [@]-prefixed notation can be used:

*)

Check @pair nat unit 1 tt.

(**
[[

(1, tt) : nat * unit

]]

*)

Check fst.
(**
[[
fst : forall A B : Type, A * B -> A
]]
*)

Check snd.
(**
[[
fst : forall A B : Type, A * B -> A
]]

The notation "[_ * _]" is not hard-coded into Coq, but rather is
defined as a lightweight syntactic sugar on top of standard Coq
syntax. Very soon we will see how one can easily extend Coq's syntax
by defining their own notations. We will also see how is it possible
to find what a particular notation means.
*)

Print sum.
(**
[[
Inductive sum (A B : Type) : Type :=  inl : A -> A + B | inr : B -> A + B
]]
*)

Require Import seq.
Print seq.

(** 
[[
Notation seq := list
]]

*)

Print list.

(**
[[
Inductive list (A : Type) : Type := nil : list A | cons : A -> list A -> list A
]]
*)

(** * Searching for definitions and notations *)

Search "filt".
(** 
[[
List.filter  forall A : Type, (A -> bool) -> list A -> list A
List.filter_In
   forall (A : Type) (f : A -> bool) (x : A) (l : list A),
   List.In x (List.filter f l) <-> List.In x l /\ f x = true
]]
*)

Search "filt" (_ -> list _).
(** 
[[
List.filter  forall A : Type, (A -> bool) -> list A -> list A
]]
*)

Search _ ((?X -> ?Y) -> _ ?X -> _ ?Y).
(**
[[
option_map  forall A B : Type, (A -> B) -> option A -> option B
List.map  forall A B : Type, (A -> B) -> list A -> list B
...
]]
*)

Search _ (_ * _ : nat).

Search _ (_ * _: Type).

(* Locate machinery *)

Locate "_ + _".

(** 
[[
Notation            Scope     
"x + y" := sum x y   : type_scope
                      
"m + n" := addn m n  : nat_scope
]]
*)

Locate map.

(**
[[
Constant Coq.Lists.List.map
  (shorter name to refer to it in current context is List.map)
Constant Ssreflect.ssrfun.Option.map
  (shorter name to refer to it in current context is ssrfun.Option.map)
...
]]
*)

(** * An alternative syntax to define inductive datatypes *)

Inductive my_prod (A B : Type) : Type :=  my_pair of A & B.

(** 
[[
Check my_pair 1 tt.

Error: The term "1" has type "nat" while it is expected to have type "Type".
]]
*)

(* Declaring implicit arguments *)

Implicit Arguments my_pair [A B].

(* Defining custom notation *)

Notation "X ** Y" := (my_prod X Y) (at level 2).
Notation "( X ,, Y )" := (my_pair X Y).

Check (1 ,, 3).

(** 
[[
(1,, 3)
     : nat ** nat
]]

*)

Check nat ** unit ** nat.

(** 
[[
(nat ** unit) ** nat
     : Set
]]
*)

(** * Sections and modules *)

Section NatUtilSection.

Variable n: nat.

Fixpoint my_mult m := match (n, m) with
 | (0, _) => 0
 | (_, 0) => 0
 | (_, m'.+1) => my_plus (my_mult m') n
 end. 

End NatUtilSection.

Print my_mult.

(** 

[[
my_mult = 
fun n : nat =>
fix my_mult (m : nat) : nat :=
  let (n0, y) := (n, m) in
  match n0 with
  | 0 => 0
  | _.+1 => match y with
            | 0 => 0
            | m'.+1 => my_plus (my_mult m') n
            end
  end
     : nat -> nat -> nat
]]
*)

Module NatUtilModule.

Fixpoint my_fact n :=
  if n is n'.+1 then my_mult n (my_fact n') else 1.

Module Exports.
Definition fact := my_fact.
End Exports.

End NatUtilModule.

Export NatUtilModule.Exports.

(** 
[[
Check my_fact.

Error: The reference my_fact was not found in the current environment.
]]
*)

Check fact.

(**
[[
fact
     : nat -> nat
]]
*)

(*******************************************************************)
(**                     * Exercices *                              *)
(*******************************************************************)

Require Import eqtype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
---------------------------------------------------------------------
Exercise [Power of two]
---------------------------------------------------------------------

Write the function [two_power] of type [nat -> nat], such that
[two_power n = 2^n]. Use the functions that we have defined earlier.
*)

Definition two_power : nat -> nat :=
  nat_rec (fun _ => nat) 1 (fun _ m => 2 * m).
Eval compute in two_power 5.

(**
---------------------------------------------------------------------
Exercise [Even numbers]
---------------------------------------------------------------------

Define the function [evenB] of type [nat -> bool], such that it
returns [true] for even numbers and [false] otherwise. Use the
function we have already defined.
*)

Definition evenB : nat -> bool :=
  nat_rec (fun _ => bool) true (fun _ m => negate m).
Eval compute in evenB 7.
Eval compute in evenB 12.

(**
---------------------------------------------------------------------
Exercise [Division by four]
---------------------------------------------------------------------

Define the function [div4] that maps any natural number [n] to the
integer part of [n/4].
*)

Fixpoint div4 n : nat := if n is n'.+4 then (div4 n').+1 else 0.

Eval compute in div4 1.
Eval compute in div4 10.
Eval compute in div4 12.
Eval compute in div4 13.

(**
---------------------------------------------------------------------
Exercise [Representing rational numbers]
---------------------------------------------------------------------

Every strictly positive rational number can be obtained in a unique
manner by a succession of applications of functions [N] and [D] on the
number one, where [N] and [D] defined as follows:

[[
N(x) = 1 + x

D(x) = 1/(1 + 1/x)
]]

Define an inductive type (with three constructors), such that it
uniquely defines strictly positive rational using the representation
above.

Then, define the function that takes an element of the defined type
and returns a numerator and denominator of the corresponding fraction.
*)

Inductive Rat := One | N of Rat | D of Rat.

Fixpoint rat2pair (r : Rat) : nat * nat :=
  match r with
  | One  => (1 , 1)
  | N n' => let: (a, b) := rat2pair n' in (a + b , b)
  | D n' => let: (a, b) := rat2pair n' in (a , a + b)
  end.

(**
---------------------------------------------------------------------
Exercise [Infinitely-branching trees]
---------------------------------------------------------------------

Define an inductive type of infinitely-branching trees (parametrized
over a type [T]), whose leafs are represented by a constructor that
doesn't take parameters and a non-leaf nodes contain a value _and_ a
function that takes a natural number and returns a child of the node
with a corresponding natural index.

Define a boolean function that takes such a tree (instantiated with a
type [nat]) and an argument of [n] type [nat] and checks whether the
zero value occurs in it at a node reachable only by indices smaller
than a number [n]. Then write some "test-cases" for the defined
function.

Hint: You might need to define a couple of auxiliary functions for
this exercise.

Hint: Sometimes you might need to provide the type arguments to
constructors explicitly.
*)

Inductive tree (T : Set) := Leaf | Node of T & (nat -> tree T).

Fixpoint iterate (n : nat) (f : nat -> bool) : bool :=
  match n with
  | 0 => false
  | n'.+1 => f n' || iterate n' f
  end.

Program Fixpoint has_zero (t : tree nat) (n : nat) : bool :=
  match t with
  | Leaf => false
  | Node v f => (v == 0) || iterate n (fun x => has_zero (f x) n)
  end.

Eval compute in has_zero (@Leaf nat) 1.
Eval compute in has_zero (Node 2 (fun x => if x == 3 then Node 0 (fun x => @Leaf nat) else (@Leaf nat))) 4.

(**
---------------------------------------------------------------------
Exercise [Take n]
---------------------------------------------------------------------

Write a function that takes a type [A], and number [n] and a list [l]
of elements of type [A] as arguments and returns first [n] elements of
the list (as another list) of [l] if they exist.
*)

Fixpoint fTake (A : Set) (n : nat) (l : list A) :=
  match l with
  | nil => nil
  | cons a l'  => match n with  
                  | 0 => nil
                  | n'.+1 => cons a (fTake n' l')
                  end
  end.

(**
---------------------------------------------------------------------
Exercise [Generate a range]
---------------------------------------------------------------------

Implement a function that takes a number [n] and returns the list
containing the natural numbers from [1] to [n], _in this order_.
*)

Fixpoint minus (a : nat) (b : nat) :=
  match a, b with
  | 0, b => 0
  | a, 0 => a
  | a'.+1, b'.+1 => minus a' b'
  end.

Fixpoint generateRange' (m : nat) (n : nat) :=
  match n with
  | 0 => nil
  | n'.+1 => cons (minus m n) (generateRange' m n')
  end.
Definition generateRange (n : nat) := generateRange' (n.+1) n.

Eval compute in generateRange 5.

(**
---------------------------------------------------------------------
Exercise [List-find]
---------------------------------------------------------------------

Write a function that take a type [A], a function [f] of type [A ->
bool] and a list [l], and return the first element [x] in [l], such
that [f x == true]. 

Hint: Use Coq's [option] type to account for the fact that the
 function of interest is partially-defined.
*)

Print option.

Fixpoint listFind (A : Set) (f : A -> bool) (l : list A) : option A :=
  match l with
  | nil => None
  | cons a l => if f a then Some a else listFind f l
  end.

(**
---------------------------------------------------------------------
Exercise [Standard list combinators]
---------------------------------------------------------------------

Implement the following higher-order functions on lists

- map
- filter
- fold_left
- fold_right
- tail-recursive list reversal
*)

Fixpoint map (A B : Set) (f : A -> B) (l : list A) : list B := 
  match l with
  | nil => nil
  | cons a l => cons (f a) (map f l)
  end.

Fixpoint filter (A : Set) (f : A -> bool) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons a l => if f a then cons a (filter f l) else filter f l
  end.

Fixpoint fold_left (A B : Set) (f : A -> B -> A) (i : A) (l : list B) : A :=
  match l with
  | nil => i
  | cons a l => fold_left f (f i a) l
  end.

Fixpoint fold_right (A B : Set) (f : A -> B -> B) (i : B) (l : list A) : B :=
  match l with
  | nil => i
  | cons a l => f a (fold_right f i l)
  end.

Definition reverse (A : Set) (l : list A) : list A :=
  fold_left (fun l a => cons a l) nil l.

Eval compute in reverse [:: 1; 2; 3].

(** 
---------------------------------------------------------------------
Exercises [No-stuttering lists]
---------------------------------------------------------------------

We say that a list of numbers "stutters" if it repeats the same number
consecutively. The predicate "nostutter ls" means that ls does not
stutter. Formulate an inductive definition for nostutter. Write some
"unit tests" for this function.

*)

Fixpoint nostutter (l : list nat) : bool :=
  match l with
  | nil => true
  | [:: a] => true
  | cons a l' => match l' with
                 | nil => true
                 | cons b l'' => if a == b then false else nostutter l' 
                 end
  end.

(**
---------------------------------------------------------------------
Exercise [List alternation]
---------------------------------------------------------------------

Implement the recursive function [alternate] of type [seq nat -> seq
nat -> seq nat], so it would construct the alternation of two
sequences according to the following "test cases".

Eval compute in alternate [:: 1;2;3] [:: 4;5;6].
[[
     = [:: 1; 4; 2; 5; 3; 6]
     : seq nat
]]

Eval compute in alternate [:: 1] [:: 4;5;6].
[[
     = [:: 1; 4; 5; 6]
     : seq nat
]]
Eval compute in alternate [:: 1;2;3] [:: 4].
[[
     = [:: 1; 4; 2; 3]
     : seq nat
]]

Hint: The reason why the "obvious" elegant solution might fail is
 that the argument is not strictly decreasing.
*)

Fixpoint alternate (ls : seq nat) (bs : seq nat) : seq nat :=
  match ls, bs with
  | nil , _   => bs
  | _   , nil => ls
  | cons a ls, cons b bs => a :: b :: (alternate ls bs)
  end.

Eval compute in alternate [:: 1;2;3] [:: 4;5;6].

(**
---------------------------------------------------------------------
Exercise [Functions with dependently-typed result type]
---------------------------------------------------------------------

Write a function that has a dependent result type and whose result is
[true] for natural numbers of the form [4n + 1], [false] for numbers
of the form [4n + 3] and [n] for numbers of the from [2n].

Hint: Again, you might need to define a number of auxiliary
 (possibly, higher-order) functions to complete this exercise.
*)

Fixpoint stype (n : nat) : Set :=
  match n with
  | 0    => nat
  | 1    => bool
  | n.+2 => stype n
  end.
Definition ftype (n : nat) : Set := stype n -> stype n.+2.

Fixpoint smidfunc (n : nat) : stype n * ftype n :=
  match n with
  | 0    => (0, (fun x => x.+1))
  | 1    => (true, negate)
  | n.+2 => let: (a, b) := smidfunc n in (b a, b)
  end.
Definition sfunc (n : nat) : stype n := let: (a, _) := smidfunc n in a.

End FunProg.
