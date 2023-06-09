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
Proof. Admitted.

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

(* Exercise: *)
Lemma none_occurs :
  forall (x : A) (f : A -> bool) (t : tree),
    f x = false ->
    all f t = true ->
    occurs x t = false.
Proof. (* fill in here *) Admitted.

(** With these results, we are ready to prove the correctness of the
    membership testing algorithm. *)

Lemma member_correct :
  forall x t,
    search_tree t = true ->
    member x t = occurs x t.
Proof.
  intros x t.
  induction t as [|c t1 IH1 y t2 IH2]; simpl; trivial.
  intros H.
  destruct (all (fun z => ltb z y) t1) eqn:H1; try discriminate.
  destruct (all (ltb y) t2) eqn:H2; try discriminate.
  destruct (search_tree t1) eqn:H3; try discriminate.
  destruct (search_tree t2) eqn:H4; try discriminate.
  unfold eqb.
  rewrite IH1; trivial.
  rewrite IH2; trivial.

(** We often want to introduce new facts in our context. This can be
    done with the [assert] tactic.

    New Tactics
    -----------

    - [assert]: Introduce a new hypothesis in the context, requiring
      us to prove that it holds. *)

  assert (Hx : ltb x x = false).
  { unfold ltb. rewrite comp_refl. reflexivity. }

(** The curly braces [{}] allow us to focus on the current subgoal,
    like [+] and [-]. *)

  destruct (comp x y) eqn:Hxy.
  - rewrite Bool.orb_true_r. reflexivity.
  - assert (H2' : all (ltb x) t2 = true).
    { apply (all_weaken (ltb y) (ltb x)); trivial.
      intros z.
      unfold ltb.
      destruct (comp y z) eqn:Hyz; try congruence.
      rewrite (comp_trans x y z); trivial. }
    rewrite (none_occurs x (ltb x) t2 Hx H2').
    destruct (occurs x t1); reflexivity.
  - assert (Hxy' : comp y x = Lt).
    { rewrite comp_opp, Hxy. reflexivity. }
    assert (H1' : all (fun z => ltb z x) t1 = true).
    { apply (all_weaken (fun z => ltb z y) (fun z => ltb z x)); trivial.
      intros z.
      unfold ltb.
      destruct (comp z y) eqn:Hyz; try congruence.
      rewrite (comp_trans z y x); trivial. }
    rewrite (none_occurs x (fun z => ltb z x) t1); trivial.
Qed.

Definition tree_color (t : tree) : color :=
  match t with
  | Leaf => Black
  | Node c _ _ _ => c
  end.

Fixpoint well_colored (t : tree) : bool :=
  match t with
  | Leaf => true
  | Node c t1 _ t2 =>

    let colors_ok :=
      match c, tree_color t1, tree_color t2 with
      | Red, Black, Black => true
      | Red, _, _ => false
      | Black, _, _ => true
      end in
    colors_ok && well_colored t1 && well_colored t2
  end.

(** The [black_height] function computes the number of black nodes on
    the path to the left-most leaf of the tree. It is used in the
    [height_ok] function, which ensures that _all_ paths have the same
    number of black nodes. *)

Fixpoint black_height (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node Red t _ _ => black_height t
  | Node Black t _ _ => S (black_height t)
  end.

Fixpoint height_ok (t : tree) : bool :=
  match t with
  | Leaf => true
  | Node _ t1 _ t2 =>
    beq_nat (black_height t1) (black_height t2)
    && height_ok t1
    && height_ok t2
  end.

Definition is_red_black (t : tree) : bool :=
  well_colored t && height_ok t.

(** The red-black invariant is important because it implies that the
    height of the tree is logarithmic on the number of nodes. We will
    now see how to formally show that this is the case. We begin by
    defining a function [size] for computing various metrics about our
    trees: *)

Fixpoint size (f : nat -> nat -> nat) (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node _ t1 _ t2 => S (f (size f t1) (size f t2))
  end.

(** Note that [size plus] computes the number of elements stored in
    the tree. [size max] computes the height of the tree, whereas
    [size min] computes the length of the shortest path from the root
    of the tree to a leaf.

    As a warm-up exercise, let's show that the black height of a tree
    is a lower bound on the length of its minimal path: *)

Lemma size_min_black_height :
  forall t,
    if height_ok t then black_height t <= size min t
    else True.
Proof.
  intros t.
  induction t as [|c t1 IH1 x t2 IH2].

  + simpl.

(** To facilitate low-level arithmetic reasoning, we can use the [lia]
    tactic.

    New Tactics
    -----------

    - [lia]: Short for "Linear Integer Arithmetic"; tries to solve
      goals that involve linear systems of inequalites on integers. *)

  lia.

  + simpl.
    destruct (beq_nat (black_height t1) (black_height t2)) eqn:e12; simpl; trivial.
    rewrite beq_nat_true_iff in e12.
    destruct (height_ok t1); simpl; trivial.
    destruct (height_ok t2); simpl; trivial.
    destruct c; lia.
Qed.

(* There is more bellow in the original but I think due to the abort it doesn't work so this is all I put in here
file: https://rand.cs.uchicago.edu/cufp_2015/redblack.v
*)

End RedBlack.