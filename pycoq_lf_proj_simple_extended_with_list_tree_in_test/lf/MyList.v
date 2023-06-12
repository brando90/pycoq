(*
inspired from:
https://rand.cs.uchicago.edu/cufp_2015/
https://rand.cs.uchicago.edu/cufp_2015/basics.v
*)
Module List.

(** Here's a polymorphic definition of a [list] type in Coq: *)

Inductive list (T : Type) :=
| nil : list T
| cons : T -> list T -> list T.

(** In Coq, polymorphism is _explicit_, which means that we need to
    supply type arguments when using polymorphic functions. *)

Definition singleton_list (T : Type) (x : T) :=
  cons T x (nil T).

(** Fortunately, we can avoid providing arguments when Coq has enough
    information to figure them out. In the example below, since [x]
    has type [T], Coq can infer that the type argument for [cons] and
    [nil] must be [T] too. Hence, we can just write a wildcard "_"
    instead of [T], which has the effect of asking Coq to figure out
    what to put there on its own: *)

Definition singleton_list' (T : Type) (x : T) :=
  cons _ x (nil _).

(* We can also instruct Coq once and for all to try to infer arguments
   on its own. This feature is called _implicit arguments_.

   We use "Arguments" to say which arguments of a definition are
   implicit (by surrounding them with curly braces {...}). We can also
   declare them as implicit at definition time: *)

Arguments nil {T}.
Arguments cons {T} _ _.
Definition singleton_list'' {T} (x : T) :=
  cons x nil.

Check (singleton_list'' 3).

(** Finally, we can turn off implicit argument inference for a
    definition locally, by prepending its name with a "@" sign: *)

Check (@singleton_list'' nat).

(** In Coq, polymorphism appears on the type of programs as a
    universal quantifier [forall]: *)

Check @singleton_list''.
Check @nil.

Notation "h :: t" := (cons h t) (at level 60, right associativity).
Notation "[ ]" := (nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* Exercise: Define "snoc", which adds an element to the end of a list. *)

Fixpoint snoc {T} (l : list T) (x : T) : list T :=
    match l with
    | [] => [x]
    | h :: t => h :: (snoc t x)
    end.

Fixpoint app {T} (l1 l2 : list T) : list T :=
  match l1 with
  | [] => l2
  | h :: l1' => h :: (app l1' l2)
  end.

Notation "l1 ++ l2" := (app l1 l2) (at level 60, right associativity).

(** Let us prove some simple facts about lists. To perform an
    inductive proof on a list, we also use the [induction] tactic;
    this has the effect of giving us an inductive hypothesis about the
    tail of the list. Notice that in the proof below we have to give
    names both to the head and to the tail of [l1] *)

Lemma app_assoc :
  forall T (l1 l2 l3 : list T),
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros T l1 l2 l3.
  induction l1 as [|h1 t1 IH].
  - (* [] *)
    simpl.
    reflexivity.
  - (* h1 :: t1 *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(* Exercise *)

Lemma snoc_app :
  forall T (l : list T) (x : T),
    snoc l x = l ++ [x].
Proof.
    intros T l x.
    induction l as [|h t IH].
    - simpl. reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.

End List.