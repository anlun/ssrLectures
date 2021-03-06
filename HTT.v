(** %\chapter{Case Study: Program Verification in Hoare Type Theory}% *)

Module HTT.

(** * Elements of Hoare Type Theory *)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Add LoadPath "./../htt".
Require Import prelude pred pcm unionmap heap heaptac stmod stsep stlog stlogR.  

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Structuring the program verification in HTT *)

(* NOTE: the current implementation of HTT does not support
value/type dependencies in the logical variables (e.g., {T (x: T)}),
so such cases won't be properly handled by the ghR lemma. *)

Program Definition alter_x A (x : ptr) (v : A): 
  {y (Y : nat)}, 
  STsep (fun h => exists B (w : B), h = x :-> w \+ y :-> Y,
        [vfun (_: unit) h => h = x :-> v \+ y :-> Y]) := 
  Do (x ::= v).

(**

The Coq's command [Program Definition] is similar to the standard
definition [Definition] except for the fact that it allows the
expression being defined to have a type, whose some components haven't
yet been type-checked and remain to be filled by the programmer.

After stating the definition, Coq generates a series of obligations to
prove in order to establish the defined program well-typed with
respect to the stated type.

[[
alter_x has type-checked, generating 1 obligation(s)
Solving obligations automatically...
1 obligation remaining
Obligation 1 of alter_x:
forall (A : Type) (x : ptr) (v : A),
conseq (x ::= v)
  (logvar
     (fun y : ptr =>
      logvar
        (fun Y : nat =>
         binarify
           (fun h : heap => exists (B : Type) (w : B), h = x :-> w \+ y :-> Y)
           [vfun _ h => h = x :-> v \+ y :-> Y]))).
]]

The proof mode for each of the remaining obligations is activated by
the Vernacular command [Next Obligation], which automatically moves
some of the assumptions to the context.

*)

Next Obligation.

(**
[[
  A : Type
  x : ptr
  v : A
  ============================
   conseq (x ::= v)
     (logvar
        (fun y : ptr =>
         logvar
           (fun Y : nat =>
            binarify
              (fun h : heap =>
               exists (B : Type) (w : B), h = x :-> w \+ y :-> Y)
              [vfun _ h => h = x :-> v \+ y :-> Y])))
]]
*)

apply: ghR. 

(**
[[
  A : Type
  x : ptr
  v : A
  ============================
   forall (i : heap) (x0 : ptr * nat),
   (exists (B : Type) (w : B), i = x :-> w \+ x0.1 :-> x0.2) ->
   valid i -> verify i (x ::= v) [vfun _ h => h = x :-> v \+ x0.1 :-> x0.2]
]]

We can now move a number of assumptions, arising from the "brushed"
specification, to the context, along with some rewriting by equality
and simplifications.

*)

move=>h1 [y Y][B][w]->{h1} _ /=.

(**

[[
  ...
  B : Type
  w : B
  ============================
   verify (x :-> w \+ y :-> Y) (x ::= v) [vfun _ h => h = x :-> v \+ y :-> Y]
]]

*)

by heval.

(*
Alternatively:
 apply: val_write. 
*)

Qed.

(** ** Verifying the factorial procedure mechanically

Proving an assignment for two non-aliased pointers was a simple
exercise, so now we can proceed to a more interesting program, which
features loops and conditional expressions, namely, imperative
implementation of the factorial function.
*)

Fixpoint fact_pure n := if n is n'.+1 then n * (fact_pure n') else 1.

(** 

Next, we define the loop invariant [fact_inv], which constraints the
heap shape and the values of the involved pointers, [n] and [acc].

*)

Definition fact_inv (n acc : ptr) (N : nat) h : Prop := 
  exists n' a': nat, 
  [/\ h = n :-> n' \+ acc :-> a' & 
      (fact_pure n') * a' = fact_pure N].

Definition fact_tp n acc := 
  unit -> {N}, 
     STsep (fact_inv n acc N, 
           [vfun (res : nat) h => fact_inv n acc N h /\ res = fact_pure N]).

(** 

The definition of the factorial "accumulator" loop is then represented
as a recursive function, taking as arguments the two pointers, [n] and
[acc], and also a unit value. 

*)


Program Definition fact_acc (n acc : ptr): fact_tp n acc := 
  Fix (fun (loop : fact_tp n acc) (_ : unit) => 
    Do (a1 <-- !acc;
        n' <-- !n;
        if n' == 0 then ret a1
        else acc ::= a1 * n';;
             n ::= n' - 1;;
             loop tt)).

(** 

The body of the accumulator loop function reproduces precisely the
factorial implementation in pseudocode. It first reads the values of
the pointers [acc] and [n] into the local variables [a1] and
[n']. Notice that the binding of the local immutable variables is
represented by the [<--] notation, which corresponds to the _bind_
operation of the Hoare monad [STsep]. The function then uses Coq's
standard conditional operator and returns a value of [a1] if [n'] is
zero using the monadic [ret] operator. In the case of [else]-branch,
the new values are written to the pointers [acc] and [n], after which
the function recurs.

Stating the looping function like this leaves us with one obligation
to prove.


*)

Next Obligation. 

(** 

As in the previous example, we start by transforming the goal, so the
logical variable [N], coming from the specification of [fact_tp] would
be exposed as an assumption. We immediately move it to the context
along with the initial heap [i].

*)

apply: ghR=>i N. 

(**
[[
  ...
  i : heap
  N : nat
  ============================
   fact_inv n acc N i ->
   valid i ->
   verify i
     (a1 <-- !acc;
      n' <-- !n;
      (if n' == 0 then ret a1 else acc ::= a1 * n';; n ::= n' - 1;; loop tt))
     [vfun res h => fact_inv n acc N h /\ res = fact_pure N]
]]

We next case-analyse on the top assumption with the invariant
[fact_inv] to acquire the equality describing the shape of the heap
[i]. We then rewrite [i] in place and move a number of hypotheses to
the context.

*)

case=>n' [a'][->{i}] Hi _. 

(**

Now the goal has the shape [verify (n :-> n' \+ acc :-> a') ...],
which is suitable to be hit with the automation by means of the
[heval].

*)

heval. 

(**
[[
  ...
  n' : nat
  a' : nat
  Hi : fact_pure n' * a' = fact_pure N
  ============================
   verify (n :-> n' \+ acc :-> a')
     (if n' == 0 then ret a' else acc ::= a' * n';; n ::= n' - 1;; loop tt)
     [vfun res h => fact_inv n acc N h /\ res = fact_pure N]
]]

The goal, containing a use of the conditional operator, is natural to
be proved on case analysis on the condition [n' == 0].

*)

case X: (n' == 0). 

(** 

[[
  ...
  Hi : fact_pure n' * a' = fact_pure N
  X : (n' == 0) = true
  ============================
   verify (n :-> n' \+ acc :-> a') (ret a')
     [vfun res h => fact_inv n acc N h /\ res = fact_pure N]
]]

To prove it, we will need one of the numerous [val]-lemmas, delivered
as a part of HTT libraries and directly corresponding to the rules of
separation logic. The general recipe on acquiring intuition for the
lemmas applicable for each particular [verify]-goal is to make use of
SSReflect's [Search] machinery. For instance, in this particular case,
given that the command to be verified (i.e., the second argument of
[verify]) is [ret a'], let us try the following query.

*)

Search _ (verify _ _ _) (ret _).

(**

The request results report, in particular, on the following lemma
found:

[[
val_ret
   forall (A : Type) (v : A) (i : heapPCM) (r : cont A),
   (valid i -> r (Val v) i) -> verify i (ret v) r
]]

*)

- apply: val_ret=>/= _. 

(** 

The remaining part of the proof of this goal has absolutely nothing to
do with program verification and separation logic and accounts to
combining a number of arithmetical facts in the goal via the
hypotheses [Hi] and [X]. 
*)

  move/eqP: X=>Z; subst n'.
  split; first by exists 0, a'=>//.
  by rewrite mul1n in Hi.

(** 

The second goal requires to satisfy the specification of a sequence of
assignments, which can be done automatically using the [heval] tactic.

*)

heval. 

(** 
[[
  loop : fact_tp n acc
  ...
  Hi : fact_pure n' * a' = fact_pure N
  X : (n' == 0) = false
  ============================
   verify (n :-> (n' - 1) \+ acc :-> (a' * n')) (loop tt)
     [vfun res h => fact_inv n acc N h /\ res = fact_pure N]
]]

*)

apply: (gh_ex N). 

(**

Now to verify the call to [loop], we can apply the lemma [val_doR],
corresponding to the rule %\Rule{App}%, which will replace the goal by
the precondition from the spec [fact_tp n acc]. In HTT there are
several lemmas tackling this kind of a goal, all different in the way
they treat the postconditions, so in other cases it is recommended to
run [Search "val_do"] to see the full list and chose the most
appropriate one.

%\httl{val\_doR}%

*)

apply: val_doR=>// _.

(**
[[
  ...
  Hi : fact_pure n' * a' = fact_pure N
  X : (n' == 0) = false
  ============================
   fact_inv n acc N (n :-> (n' - 1) \+ acc :-> (a' * n'))
]]

As in the case of the previous goal, the remaining proof is focused on
proving a statement about a heap and natural numbers, so we just
present its proof below without elaborating on the details, as they
are standard and mostly appeal to propositional reasoning and
rewriting by lemmas from SSReflect's [ssrnat] module.

*)

exists (n'-1), (a' * n'); split=>//=. 
rewrite -Hi=>{Hi}; rewrite [a' * _]mulnC mulnA [_ * n']mulnC.
by case: n' X=>//= n' _; rewrite subn1 -pred_Sn. 
Qed.

(** 

We can now implement the main body of the factorial function, which
allocates the necessary pointers, calls the accumulator loop and then
frees the memory.

*)

Program Definition fact (N : nat) : 
  STsep ([Pred h | h = Unit], 
         [vfun res h => res = fact_pure N /\ h = Unit]) := 
  Do (n   <-- alloc N;
      acc <-- alloc 1;
      res <-- fact_acc n acc tt;
      dealloc n;;
      dealloc acc;;
      ret res).

Next Obligation.

(** 

Since the spec of [fact] does not have any logical variables (its
postcondition only mentions its argument [N]), there is no need to
make use of the [ghR] lemma. 

*)

rewrite /conseq =>/=.

(** 
[[
  N : nat
  ============================
   forall i : heap,
   i = Unit ->
   verify i
     (n <-- alloc N;
      acc <-- alloc 1;
      res <-- fact_acc n acc tt; dealloc n;; dealloc acc;; ret res)
     (fun (y : ans nat) (m : heap) =>
      i = Unit -> [vfun res h => res = fact_pure N /\ h = Unit] y m)
]]
*)

move=>_ ->.
heval=>n; heval=>acc; rewrite joinC unitR.

(**

We have now came to the point when the function [fact_acc], which we
have previously verified, is going to be invoked. In this case,
however, the tactic [val_doR] will not work immediately, so we will
first need to reduce the program to be verified from the binding
command to a mere function call be means of HTT's [bnd_seq] lemma,
which tackles the binding _combined_ with a call to a user-defined
function, and this is exactly our case. Next, we instantiate the
[fact_acc] specification's logical variable [N] by applying [gh_ex]
and proceed with the application of [val_doR].

*)

apply: bnd_seq=>/=; apply: (gh_ex N); apply: val_doR=>//.

(** 

The first of the resulting two goals is an obligation arising from the
need to prove [fact_acc]'s precondition.

*)

 - by exists N, 1; rewrite muln1.

(**

The second goal is the remainder of the program's body, which performs
deallocation, so the proof for it is accomplished mostly by applying
[heval] tactic.

*)

by move=>_ _ [[n'][a'][->] _ ->] _; heval.  
Qed.

(** * Specifying and verifying programs with linked lists *)

Definition llist (T : Type) := ptr.

Section LList.
Variable T : Type.
Notation llist := (llist T).

Fixpoint lseg (p q : ptr) (xs : seq T): Pred heap := 
  if xs is x::xt then 
    [Pred h | exists r h', 
       h = p :-> x \+ (p .+ 1 :-> r \+ h') /\ h' \In lseg r q xt]
  else [Pred h | p = q /\ h = Unit].

(** 

The notation [[Pred h | ...]] is just an abbreviation for a function
of type [heap -> Prop], where [h] is assumed to be of type [heap]. The
notation [h \In f] is a synonym for [f h] assuming [f] is a predicate
of type [heap -> Prop].

The following lemma [lseg_null] states a fact, which is almost
obvious: given that the heap [h], corresponding to a linked list, is a
valid one (according to its notion of validity as a PCM) and the head
pointer of a list structure is [null], then its tail pointer is [null]
as well, and the overall list is empty.

*)

Lemma lseg_null xs q h : 
         valid h -> h \In lseg null q xs -> 
         [/\ q = null, xs = [::] & h = Unit].
Proof.
case: xs=>[|x xs] D /= H; first by case: H=><- ->.
case: H D =>r [h'][->] _. 
(**
[[
  ...
  r : ptr
  h' : heap
  ============================
   valid (null :-> x \+ (null.+1 :-> r \+ h')) ->
   [/\ q = null, x :: xs = [::] & null :-> x \+ (null.+1 :-> r \+ h') = Unit]
]]
*)

rewrite hvalidPtUn. 
(**
[[
  ...
  ============================
   [&& null != null, valid (null.+1 :-> r \+ h')
     & null \notin dom (null.+1 :-> r \+ h')] ->
   [/\ q = null, x :: xs = [::] & null :-> x \+ (null.+1 :-> r \+ h') = Unit]
]]
*)

done.
Qed. 

(**  

We can now define a particular case of linked
lists---_null-terminating_ lists and prove the specification of a
simple insertion program, which allocates a new memory cell for an
element [x] and makes it to be a new head of a list pointed by
[p]. 

*)

Definition lseq p := lseg p null.

Program Definition insert p x : 
  {xs}, STsep (lseq p xs, [vfun y => lseq y (x::xs)]) :=
  Do (q <-- allocb p 2; 
      q ::= x;;
      ret q). 
Next Obligation. 
apply: ghR=>i xs H _. 
heval=>x1. 
rewrite unitR -joinA. 
heval. 
Qed.

(** 

Next, we are going to give a specification to the list
"beheading"---removing the head element of a list. For this, we will
need a couple of auxiliary lemmas involving the list heap predicate
[lseg_neq]. The first one, [lseq_null] is just a specialization of the
previously proved [lseg_null.]

*)


Lemma lseq_null xs h : valid h -> h \In lseq null xs -> xs = [::] /\ h = Unit.
Proof. by move=>D; case/(lseg_null D)=>_ ->. Qed.

(** 

The next lemma, [lseq_pos], states that is a head of a linked list,
defined by a heap [h], is not [null], then it can be "beheaded". That
is, there will exist a head value [x], a "next" [r] and a residual
heap [h'], such that the heap [h'] corresponds to the list's tail,
which is expressed by SSReflect's [behead] function.

*)

Lemma lseq_pos xs p h : 
        p != null -> h \In lseq p xs -> 
        exists x, exists r, exists h', 
          [/\ xs = x :: behead xs, 
              p :-> x \+ (p .+ 1 :-> r \+ h') = h & h' \In lseq r (behead xs)].
Proof.
case: xs=>[|x xs] /= H []. 
 - move=>E. 
   by rewrite E eq_refl in H.
by move=>y [h'][->] H1; heval.
Qed.

(** 

We can finally define and specify the HTT procedure [remove], which
returns the current head of the list and returns the pointer to its
next element (or [null]) if the list is empty.

*)


Program Definition 
remove p : {xs}, STsep (lseq p xs, [vfun y => lseq y (behead xs)]) :=
  Do (if p == null then ret p 
      else pnext <-- !(p .+ 1);
           dealloc p;; 
           dealloc p .+ 1;;
           ret pnext). 

(** 

The proof is straightforward and employs both lemmas [lseq_null] to
prove the "[null]" case and [lseq_pos] for the case when the list has
at least one element.

*)

Next Obligation.
apply: ghR=>i xs H V; case: ifP H=>H1.
- by rewrite (eqP H1); case/(lseq_null V)=>->->; heval. 
case/(lseq_pos (negbT H1))=>x [q][h][->] <- /= H2.
by heval; rewrite 2!unitL.
Qed.

End LList.

(*******************************************************************)
(**                     * Exercices *                              *)
(*******************************************************************)

(** 
---------------------------------------------------------------------
Exercise [Swapping two values]
---------------------------------------------------------------------

Implement in HTT a function that takes as arguments two pointers, [x]
and [y], which point to natural numbers, and swaps their
values. Reflect this effect in the function's specification and verify
it.

Hint: Instead of reading the value of a pointer into a variable [t]
using the [t <-- !p] notation, you might need to specify the _type_ of
the expected value explicitly by using the "de-sugared" version of the
command [t <-- read T p], where [T] is the expected type. This way,
the proof will be more straightforward.

*)

Program Definition swap (x y : ptr) :
  {A B : nat},
  STsep ([Pred h | h = x :-> A \+ y :-> B],
         [vfun (_: unit) h => h = x :-> B \+ y :-> A]) :=
  Do (t1 <-- read nat x ;
      t2 <-- read nat y ;
      x ::= t2 ;;
      y ::= t1).

Next Obligation.
apply: ghR. 
move=> i [A B]/= -> vi.
heval.

Restart.

apply: ghR=> i; case=> A B /= =>-> => Hh.
do 2! (apply: bnd_readR=> /=).
apply: bnd_writeR=> /=.
rewrite joinC.
apply: val_write => H /=.
by rewrite joinC.
Qed.

(**
---------------------------------------------------------------------
Exercise [Swapping two values without heval]
---------------------------------------------------------------------

Try to redo the previous exercise _without_ using the automation
provided by the [heval] tactic. The goal of this exercise is to
explore the library of HTT lemmas, mimicking the rules of the
separation logic. You can alway displat the whole list of the
available lemmas by running the command [Search _ (verify _ _ _)] and
then refine the query for specific programs (e.g., [read] or [write]).
*)

(** 
---------------------------------------------------------------------
Exercise [Imperative procedure for Fibonacci numbers]
---------------------------------------------------------------------

The following program is an implementation in pseudocode of an
efficient imperative implementation of the function [fib] that
computes the [N]th Fibonacci number.  

    fun fib (N : nat): nat = {
      if N == 0 then ret 0
       else if N == 1 then ret 1
       else n <-- alloc 2;
            x <-- alloc 1;
            y <-- alloc 1;
            res <-- 
              (fix loop (_ : unit). 
                 n' <-- !n;
                 y' <-- !y;
                 if n' == N then ret y'
                 else tmp <-- !x;
                      x ::= y';;
                      x' <-- !x;
                      y ::= x' + tmp;;
                      n ::= n' + 1;;
                      loop(tt))(tt).
            dealloc n;;
            dealloc x;;
            dealloc y;;
            ret res    
    }

Your task will be to prove its correctness with respect to the "pure"
function [fib_pure] (which you should define in plain Coq) as well as
the fact that it starts and ends in an empty heap.

Hint: What is the loop invariant of the recursive computation defined
by means of the [loop] function?

Hint: Try to decompose the reasoning into verification of several code
pieces as in the factorial example and then composing them together in
the "main" function.

*)

Fixpoint fib_pure (n : nat) :=
  if n is n'.+1
  then if n' is m.+1
       then fib_pure n' + fib_pure m
       else 1
  else 0.


Fixpoint fib_pure_base (n : nat) :=
  match n with
  | 0    => (0, 1)
  | m.+1 => match fib_pure_base m with
            | (a, b) => (b, a + b)
            end
  end.
Definition fib_pure_eff (n : nat) := fst (fib_pure_base n).

(* Imperative description *)

Definition fib_inv (n x y : ptr) h : Prop :=
  exists n',
  h = n :-> n'.+1 \+ x :-> fib_pure n' \+ y :-> fib_pure n'.+1.

Definition fib_loop_tp (n x y : ptr) (N : nat):=
  unit ->
  STsep (fib_inv n x y,
         [vfun res h => fib_inv n x y h /\ res = fib_pure N]).

Program Definition fib_loop (n x y : ptr) (N : nat) : fib_loop_tp n x y N := 
  Fix (fun (loop : fib_loop_tp n x y N) (_ : unit) => 
       Do(
          n' <-- !n;
          y' <-- !y;
          if n' == N then ret y'
          else tmp <-- !x;
               x ::= y';;
               x' <-- !x;
               y ::= x' + tmp;;
               n ::= n' + 1;;
               loop tt)).
Next Obligation.
move=> h /=; case=> n1 =>->.
heval; case X: (n1.+1 == N)=>//.
- by apply: val_ret=>_; move/eqP: X=><-/=.
heval; apply: val_doR=>//.
move=>_.
exists (n1.+1).
rewrite addn1.
rewrite /fib_pure => //=.
Qed.

Definition fib_tp (N : nat) :=
  STsep ([Pred h | h = Unit], [vfun (res : nat) h => h = Unit /\ res = fib_pure N]).

Program Definition fib (N : nat) : fib_tp N :=
  Do(
      if N == 0 then ret 0
       else if N == 1 then ret 1
       else n <-- alloc 2;
            x <-- alloc 1;
            y <-- alloc 1;
            res <-- fib_loop n x y N tt;
            dealloc n;;
            dealloc x;;
            dealloc y;;
            ret res).
Next Obligation.
case N => [| N1] /=; move=> h =>-> /=.
- by apply: val_ret => /=; split.
case N1 => [| N2] /=.
- by apply: val_ret => /=; split.
heval=>n; heval=>x; heval=>y; rewrite unitR joinC [x:->_ \+ _]joinC.
apply: bnd_seq=>/=; clear.
apply: val_doR; last first=>//[res h|].
- case; case=> n1->-> H.
  heval=> _ _; split => //.
  by rewrite !unitR.
by exists 1.
Qed.

(** 
---------------------------------------------------------------------
Exercise [Value-returning list beheading]
---------------------------------------------------------------------

Define and verify function [remove_val] which is similar to [remove],
but also returns the value of the last "head" of the list before
removal, in addition to the "next" pointer. Use Coq's [option] type to
account for the possibility of an empty list in the result.

*)

Program Definition remove_val T p : {l},
  STsep (@lseq T p l,
         [vfun y h =>
          lseq y.1 (behead l) h /\
          y.2 = if l is hl :: tl then Some hl else None]) :=
  Do (if p == null then ret (p, None)
      else val  <-- !p;
           next <-- !(p .+ 1);
           dealloc p;;
           dealloc p .+ 1;;
          ret (next, Some val)).
Next Obligation.
apply: ghR=> h l H1 H2.
case: ifP H1=> H3.
- move: (eqP H3)=>->; case /(lseq_null H2)=>->->; heval.
case/(lseq_pos (negbT H3))=> x [q][h'][->] <- /= H4.
by heval; rewrite 2!unitL.
Qed.

(** 
---------------------------------------------------------------------
Exercise [Imperative in-place map]
---------------------------------------------------------------------

Define, specify and verify the imperative higher-order function
[list_map] that takes arguments two types, [S] and [T], a pure
function [f : T -> S] and a head [p] of a single-linked list,
described by a predicate [lseq], and changes the list in place by
applying [f] to each of its elements, while preserving the list's
structure. The specification should reflect the fact that the new
"logical" contents of the single-linked list are an [f] map-image of
the old content.

Hint: The lemmas [lseq_null] and [lseq_pos], proved previously, might
be useful in the proof of the established specification.

Hint: A tail-recursive call can be verified via HTT's [val_do] lemma,
reminiscent to the rule %\Rule{App}%. However, the heap it operates
with should be "massaged" appropriately via PCM's lemmas [joinC] and
[joinA].

Hint: A boolean lemma [negbT] can be useful to switch between
different representations of inequality.

*)

Definition mapTS T S (f : T -> S) : Type := 
  forall p, {xs}, STsep (@lseq T p xs, 
                         [vfun (_ : unit) h => lseq p (map f xs) h]).

Program Definition map_ex T S (f : T -> S) p : {l},
   STsep (lseq p l,
          [vfun (_: unit) h => lseq p (map f l) h]) :=
   Fix (fun (loop : mapTS f) (p : ptr) =>
     Do (if p == null then ret tt
         else val  <-- !p;
              p ::= f val;;
              next <-- !p .+ 1;
              loop next)) p.
Next Obligation.
apply: ghR=>h xs H V. 
case X: (p0 == null).
- apply: val_ret=>_ /=.
  move/eqP: X H=>-> /=.
  case/(lseq_null V)=>->-> //=.
case/negbT /lseq_pos /(_ H): X=>x[next][h'][Z1] Z2 H1; subst h.
heval.
move/validR: V=> V1; apply: (gh_ex (behead xs)).
rewrite [_ \+ h']joinC joinC -joinA; apply: val_do=>//=.
move=> _ h1 H2 H3.
rewrite Z1 /lseq /lseg /=.
exists next, h1.
split; last apply: H2.
by rewrite joinC joinA [p0 .+ 1 :-> next \+ _] joinC.
Qed.

(**
---------------------------------------------------------------------
Exercise [In-place list reversal]
---------------------------------------------------------------------

Let us define the following auxiliary predicates, where [shape_rev]
splits the heap into two disjoint linked lists (by means of the
separating conjunction [#]).

*)

Definition shape_rev T p s := [Pred h | h \In @lseq T p.1 s.1 # @lseq T p.2 s.2].

(** 

Then the in-place list reversal is implemented by means of the
recursive function [reverse] with a loop invariant expressed using the
type [revT].

*)

Definition revT T : Type := 
  forall p, {ps}, STsep (@shape_rev T p ps, [vfun y => lseq y (rev ps.1 ++ ps.2)]).

Program Definition 
reverse T p : {xs}, STsep (@lseq T p xs, [vfun y => lseq y (rev xs)]) :=
  Do (let: reverse := Fix (fun (reverse : revT T) p => 
                        Do (if p.1 == null then ret p.2 
                            else xnext <-- !p.1 .+ 1;
                                 p.1 .+ 1 ::= p.2;;
                                 reverse (xnext, p.1)))
      in reverse (p, null)).

(** 

You're invited to conduct the verification of [reverse], proving
that it satisfies the given specification.

Hint: It might be a good idea to make use of the previously proved
lemmas [lseq_null] and [lseq_pos].

Hint: Be careful with the logical values of variables passed to the
[gh_ex] lemma before verifying a recursive call of [reverse].

Hint: A verification goal to a function defined via [Fix] can be
reduced via the [val_doR] lemma or similar ones.

Hint: The [shape_rev] predicate is in fact an existential in disguise:
it can be proved by providing appropriate witnesses.

Hint: Lemmas [rev_cons], [cat_rcons] and [cats0] from the [seq]
library will be useful for establishing equalities between lists.

*)

Next Obligation.
apply: ghR=> i [a b] H1 /=.
case X: (p0 == null); move: X H1; case p0 => n; rewrite /null;
  rewrite /eq_op /=; [move/eqP=>-> | move=> H1];
  case=> h1; case=> h2; case=>->.
- case=> H4 H5 H3.
  move: (@lseq_null T a h1 (validL H3) H4).
  case=>->=>-> /=.
  rewrite unitL.
  by apply: val_ret.
case=> H3 H4 H5.
suff X: (ptr_nat n != null);
  last by move: H1; case n.
move: (@lseq_pos T a (ptr_nat n) h1 X H3).
case=> ah; case=> p'; case=> h'; case=> H6 H7 H8.
rewrite -H7.
rewrite H6 rev_cons cat_rcons.
apply: bnd_readR=> /=.
apply: bnd_writeR=> /=.
move: a H6 H3 H8; case=> [|ah' al] //=.
case=>->; clear ah'.
move=> H3 H8.
apply: gh_ex.
apply: val_doR.
- move=> vH.
  rewrite /shape_rev /=.
  Search _ (_ \+ _).

  Search _ (_ \In _).
  Locate "_ \In _".
 
move: b n H1 p1 h1 h2.
elim a => [| ah al H] => b n H1 p1 h1 h2; case=> H4 H5 H3 /=;
  first by move: H4 H1; case; case=>->.
suff X: (ptr_nat n != null);
  last by move: H1; case n.
move: (@lseq_pos T (ah :: al) (ptr_nat n) h1 X H4).
case=> x; case=> p2; case=> h.
case=> /=.
case=> L; rewrite -L; clear L.
move=> H6 H7; rewrite -H6.
rewrite rev_cons cat_rcons.
rewrite [_ h] joinC.
rewrite joinA.
rewrite [_ h] joinC.
do 2! rewrite -joinA.
apply: bnd_readR=> /=.
apply: bnd_writeR=> /=.
move: p2 H6 H7.
case=> n' => H6 H7.
Search "gh_ex".
Locate "Do _".
Print do'.

apply: gh_ex.
Search "val_do".
apply: val_doR.

Search "gh_ex".

(* move: (@H (ah :: b) n H1 p1 h). *)

apply: (@H (ah :: b) n H1 p1 h).
- split.
  move: p2 H6 H7.
  
apply: (@H (ah :: b) n H1 p1 h).
move=>->.


apply: bnd_readR=> /=.
apply: bnd_writeR=> /=.
move: p2 H6 H7.
case=> n' => H6 H7.


move: (fun H' => @H (ah :: b) n H' (ptr_nat n) h 
                    (ptr_nat n :-> ah \+ ((ptr_nat n.+1) :-> ptr_nat n') \+ h2)).


Search _ (?X \+ ?Y = ?Y \+ ?X).
Search "joinA".
 
Search "lseq_pos".

Qed.

Next Obligation.
(* fill in your proof here instead of [admit] *)
admit.
Qed.

End HTT.
