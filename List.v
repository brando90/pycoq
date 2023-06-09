(** * Lists: Working with Structured Data *)
Require Export Induction.

Module NatList.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.
Check (pair 3 5).

(
Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Eval compute in (fst (pair 3 5)).


Notation "( x , y )" := (pair x y).

Eval compute in (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m]. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.


Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | O::t => nonzeros t
  | h::t => h :: nonzeros t
  end
.

Example test_nonzeros:            nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h::t =>
    match (evenb h) with
    | true => oddmembers t
    | false => h :: oddmembers t
    end
  end
.

Example test_oddmembers:            oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  length (oddmembers l)
.

Example test_countoddmembers1:    countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2:    countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3:    countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | h1::t1, h2::t2 => h1 :: h2 :: alternate t1 t2
  end
.


Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4:        alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.
(** [] *)

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h::t =>
    match (beq_nat v h) with
    | true => S (count v t)
    | false => count v t
    end
  end
.

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  app
.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
  v :: s
.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  negb (beq_nat (count v s) 0)
.

Example test_member1:             member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2:             member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h::t =>
    match (beq_nat v h) with
    | true => t
    | false => h :: remove_one v t
    end
  end
.

Example test_remove_one1:         count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:         count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:         count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:         count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h::t =>
    match (beq_nat v h) with
    | true => remove_all v t
    | false => h :: remove_all v t
    end
  end
.

Example test_remove_all1:          count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2:          count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3:          count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4:          count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | h::t =>
    match (member h s2) with
    | true => subset t (remove_one h s2)
    | false => false
    end
  end
.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Theorem plus_count__count_add : forall v s,
    1 + (count v s) = count v (add v s).
Proof.
  intros v s.
  induction s as [| h t].
  Case "s = []".
    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
  Case "s = h::t".
    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    reflexivity.  Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.


Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite <- IHl'.
Abort.

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity.  Qed.


Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> length_snoc.
    rewrite -> IHl'. reflexivity.  Qed.

    _Theorem_: For all numbers [n] and lists [l],
       [length (snoc l n) = S (length l)].

    _Proof_: By induction on [l].

    - First, suppose [l = []].  We must show
        length (snoc [] n) = S (length []),
      which follows directly from the definitions of
      [length] and [snoc].

    - Next, suppose [l = n'::l'], with
        length (snoc l' n) = S (length l').
      We must show
        length (snoc (n' :: l') n) = S (length (n' :: l')).
      By the definitions of [length] and [snoc], this
      follows from
        S (length (snoc l' n)) = S (S (length l')),
]]
      which is immediate from the induction hypothesis. [] *)

Theorem app_nil_end : forall l : natlist,
  l ++ [] = l.
Proof.
  induction l as [| h t].
  Case "l = []".
    reflexivity.
  Case "l = h::t".
    simpl.
    rewrite IHt.
    reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  induction l as [| h t].
  Case "l = []".
    reflexivity.
  Case "l = h::t".
    simpl.
    assert (forall l0, rev (snoc l0 h) = h :: rev l0).
      SCase "Proof of assertion".
      induction l0 as [| h0 t0].
      SSCase "l0 = []".
        reflexivity.
      SSCase "l0 = h0::t0".
        simpl. rewrite IHt0.
        reflexivity.
   rewrite H.
   rewrite IHt.
   reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  replace (((l1 ++ l2) ++ l3) ++ l4) with ((l1 ++ l2) ++ l3 ++ l4).
  rewrite app_assoc. reflexivity.
  rewrite <- app_assoc. reflexivity.
Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros l n.
  induction l as [| h t].
  Case "l = []".
    reflexivity.
  Case "l = h::t".
    simpl.
    rewrite IHt.
    reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  induction l1 as [| h1 t1].
  Case "l1 = []".
    intros l2. simpl.
    rewrite app_nil_end.
    reflexivity.
  Case "l1 = h1::t1".
    intros l2. simpl.
    rewrite IHt1.
    rewrite snoc_append.
    rewrite snoc_append.
    rewrite app_assoc.
    reflexivity.
Qed.

(** An exercise about your implementation of [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1].
  Case "l1 = []".
    simpl.
    reflexivity.
  Case "l1 = h1::t1".
    destruct h1 as [| h1'].
    SCase "h1 = O".
      simpl.
      rewrite IHt1.
      reflexivity.
    SCase "h1 = S h1'".
      simpl.
      rewrite IHt1.
      reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | h1::t1, h2::t2 => andb (beq_nat h1 h2) (beq_natlist t1 t2)
  end
.

Example test_beq_natlist1 :   (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 :   beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 :   beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  induction l as [| h t].
  Case "l = []".
    reflexivity.
  Case "l = h::t".
    simpl.
    rewrite <- beq_nat_refl.
    simpl.
    rewrite <- IHt.
    reflexivity.
Qed.
(** [] *)

Theorem cons_snoc_app : forall v l,
    v::(snoc l v) = [v] ++ l ++ [v].
Proof.
  intros.
  assert (snoc l v = l ++ [v]).
    Case "Proof of assertion".
    rewrite snoc_append. reflexivity.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  intros s.
  reflexivity.
Qed.

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "0".
    simpl.  reflexivity.
  Case "S n'".
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s.
  induction s as [| h t].
  Case "s = []".
    reflexivity.
  Case "s = h::t".
    destruct h as [| h'].
    SCase "h = 0".
      simpl.
      rewrite ble_n_Sn.
      reflexivity.
    SCase "h = S h'".
      simpl.
      rewrite IHt.
      reflexivity.
Qed.

Theorem bag_count_sum : forall b1 b2,
    count 0 b1 + count 0 b2 = count 0 (sum b1 b2).
Proof.
  intros b1 b2.
  induction b1 as [| h1 t1].
  Case "b1 = []".
    reflexivity.
  Case "b1 = h1::t1".
    destruct h1 as [| h1'].
    SCase "h1 = O".
      simpl.
      rewrite IHt1.
      reflexivity.
    SCase "h1 = S h1'".
      simpl.
      rewrite IHt1.
      reflexivity.
Qed.
Theorem rev_injective : forall l1 l2,
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  replace (l1) with (rev (rev l1)).
  replace (l2) with (rev (rev l2)).
  rewrite H.
  reflexivity.
  rewrite rev_involutive.
  reflexivity.
  rewrite rev_involutive.
  reflexivity.
Qed.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.


Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => index (pred n) l'
               end
  end.

Example test_index1 :    index 0 [4;5;6;7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index 3 [4;5;6;7]  = Some 7.
Proof. reflexivity.  Qed.
Example test_index3 :    index 10 [4;5;6;7] = None.
Proof. reflexivity.  Qed.

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a else index' (pred n) l'
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_opt (l : natlist) : natoption :=
  match l with
  | nil => None
  | h::t => Some h
  end
.

Example test_hd_opt1 : hd_opt [] = None.
Proof. reflexivity. Qed.

Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  intros l default.
  destruct l as [| h t].
  Case "l = []".
    reflexivity.
  Case "l = h::t".
    reflexivity.
Qed.

End NatList.
