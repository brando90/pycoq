(* ###################################################################### *)
(** * Case study: Red-Black Trees *)

(*
inspiration:
https://rand.cs.uchicago.edu/cufp_2015/
https://rand.cs.uchicago.edu/cufp_2015/redblack.v
*)

Open Scope bool_scope.
Require Import Coq.Arith.Arith_base.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Psatz.

(** We will now see how we can use Coq's language to implement an
    interesting functional program: a red-black tree module. Red-black
    trees are binary search trees that use an intricate invariant to
    guarantee that they are well-balanced.

    We use Coq's [Section] mechanism to state our definitions within
    the scope of common parameters. This makes our notation lighter by
    avoiding having to redeclare these arguments in all
    definitions. The [Variable] and [Hypothesis] keywords introduce
    assumptions in our context that are in scope in the entire
    [Section] declaration.

    Our definitions are parameterized by a type [A] and a comparison
    function [comp] between elements of [A]. The [comparison] type is
    defined in the standard library, and includes the values [Lt],
    [Gt], and [Eq]. Notice that we state a few hypotheses that are
    needed for our results to hold. *)

Section RedBlack.

Variable A : Type.
Variable comp : A -> A -> comparison.

Hypothesis comp_opp :
  forall x y, comp x y = CompOpp (comp y x).
Hypothesis comp_trans :
  forall x y z, comp x y = Lt ->
                comp y z = Lt ->
                comp x z = Lt.

(** [A <-> B] ("A if and only if B") states that [A] and [B] are
    _logically equivalent_, i.e., that [A] implies [B] and [B] implies
    [A]. It can be applied in either direction with the [apply]
    tactic. It can also be rewritten with [rewrite]. *)

Hypothesis comp_refl_iff :
  forall x y, comp x y = Eq <-> x = y.

(* Exercise: *)
Lemma comp_refl : forall x, comp x x = Eq.
Proof.
    intros x.
    apply comp_refl_iff.
    reflexivity.
Qed.

(** Red-black trees are binary search trees that contain elements of
    [A] on their internal nodes, and such that every internal node is
    colored with either [Red] or [Black]. *)

Inductive color := Red | Black.

Inductive tree :=
| Leaf : tree
| Node : color -> tree -> A -> tree -> tree.

(** Before getting into details about the red-black invariants, we can
    already define a search algorithm that looks up an element [x] of
    [A] on a tree. Its definition is standard: *)

Fixpoint member x t : bool :=
  match t with
  | Leaf => false
  | Node _ t1 x' t2 =>
    match comp x x' with
    | Lt => member x t1
    | Eq => true
    | Gt => member x t2
    end
  end.

(** We want to formulate a specification for our algorithm and prove
    that this implementation indeed satisfies it. We begin by
    formalizing what it means for a tree to be a binary search
    tree. This will require the following higher-order function, which
    tests whether all elements of a tree [t] satisfy a property [f]: *)

Fixpoint all (f : A -> bool) (t : tree) : bool :=
  match t with
  | Leaf => true
  | Node _ t1 x t2 => all f t1 && f x && all f t2
  end.

(** We can now state the familiar binary-tree search invariant: Each
    element [x] on an internal node is strictly greater than those to
    its left, and strictly smaller than those to its right. We use an
    auxiliary function [ltb] that tests whether an element [x : A] is
    smaller than some [y : A] with the [comp] function. *)

Definition ltb x y :=
  match comp x y with
  | Lt => true
  | _ => false
  end.

(** The invariant is then expressed with a simple recursive function
    that combines [all] and [ltb] above. *)

Fixpoint search_tree (t : tree) : bool :=
  match t with
  | Leaf => true
  | Node _ t1 x t2 =>
    all (fun y => ltb y x) t1
    && all (ltb x) t2
    && search_tree t1
    && search_tree t2
  end.

(** The specification of [member] is given in terms of a function
    [occurs] that looks for an element [x] on all nodes of a tree
    [t]. The [eqb] function, as its name suggests, tests two elements
    for equality. *)

Definition eqb x y :=
  match comp x y with
  | Eq => true
  | _ => false
  end.

Fixpoint occurs (x : A) (t : tree) : bool :=
  match t with
  | Leaf => false
  | Node _ t1 y t2 => occurs x t1 || eqb x y || occurs x t2
  end.

Lemma all_weaken :
  forall f g,
    (forall x, f x = true -> g x = true) ->
    forall t, all f t = true -> all g t = true.
Proof.
  intros f g Hfg t.

(** New tactic
    ----------

    - [trivial]: solves simple goals through [reflexivity] and by
      looking for assumptions in the context that apply directly. If
      it cannot solve the goal, it does nothing. *)

  induction t as [|c t1 IH1 x t2 IH2].
  - trivial.
  - simpl. intros H.

(** Often, [destruct] generates many easy subgoals that can be readily
    solved. To make this more convenient, we can use the [;] tactic
    operator. An expression such as [foo; bar] first calls [foo], then
    calls [bar] on all generated subgoals. A common idiom is [foo;
    trivial], which solves the trivial subgoals and does nothing on
    the remaining ones.


    New Tactics
    -----------

    - [try]: Calling [try foo] tries to execute [foo], doing nothing
      if [foo] raises any errors. In particular, if [foo] is a
      _terminating tactic_ such as [discriminate], [try foo] attempts
      to solve the goal, and does nothing if it fails.

    - [destruct ... eqn: ...]: Do case analysis on an expression while
      generating an equation. *)

    destruct (all f t1) eqn:H1; try discriminate.
    destruct (f x) eqn:H2; try discriminate.
    destruct (all f t1) eqn:H3; try discriminate.
    rewrite IH1; trivial.
    rewrite Hfg; trivial.
    rewrite IH2; trivial.
Qed.

(* There is more bellow in the original but I think due to the abort it doesn't work so this is all I put in here
file: https://rand.cs.uchicago.edu/cufp_2015/redblack.v
*)

End RedBlack.