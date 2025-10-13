Require Import Coq.Lists.List.
Require Import Coq.Structures.Equalities.
Import ListNotations.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
Require Import Classical.


(* this file contains many helper functions and theorems involving lists,
   especially properties of membership, count, filter, index, and append *)

(* return true if l1 and l2 are equal *)
Fixpoint eqblist (l1 l2 : list nat) : bool
  := match l1, l2 with
      | nil, nil => true
      | nil, _ => false
      | _, nil => false
      | h1 :: t1, h2 :: t2 => if (h1 =? h2) then eqblist t1 t2 else false
end.

(* a list l is always equal to itself *)
Theorem eqblist_refl : forall l: list nat,
  true = eqblist l l.
Proof.
  induction l as [| h t IHl].
  - simpl. reflexivity.
  - simpl. rewrite eqb_refl. rewrite IHl. reflexivity.
Qed.

(* a list containing a last element is not empty *)
Theorem eqblist_empty: forall (l: list nat) (x: nat),
  eqblist (l ++ [x]) [] = false.
Proof.
  intros l x.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* return true if v is a member of s *)
Fixpoint member (v : nat) (s : list nat) : bool
  := match s with
      | nil => false
      | h :: t => if (h =? v) then true else member v t
    end.

(* equate our boolean member function with propositional membership predicate *)
Lemma member_In_equiv : 
  forall (l : list nat) (x: nat), member x l = true <-> In x l.
Proof.
  intros l x.
  split.
  - intros H. induction l as [| h t IH].
    + simpl in H. discriminate H.
    + simpl in H. simpl. destruct (h =? x) as [|] eqn:Hhx.
      * left. apply eqb_eq. apply Hhx.
      * right. apply IH. apply H.
  - intros H. induction l as [| h t IH].
    + simpl in H. exfalso. apply H.
    + simpl. simpl in H. destruct H as [H | H].
      * apply eqb_eq in H. rewrite H. reflexivity.
      * destruct (h =? x) as [|] eqn:Hhx.
        -- reflexivity.
        -- apply IH. apply H.
Qed.

(* relate boolean and propositional forms of non-membership *)
Lemma member_In_equiv_F : 
  forall (l : list nat) (x: nat), member x l = false <-> ~(In x l).
Proof.
  intros l x.
  split.
  - intros Hmem F. apply member_In_equiv in F. rewrite F in Hmem. discriminate Hmem.
  - intros Hmem. destruct (member x l) as [|] eqn:F.
    + exfalso. apply Hmem. apply member_In_equiv. apply F.
    + reflexivity.
Qed.

(* l having length >= 1 implies existence of at least one element x *)
Theorem length_member: forall (l: list nat) (n': nat),
  (length l = S n') -> exists x, In x l.
Proof.
  intros l n' H.
  destruct l as [| h t].
  - simpl in H. discriminate H.
  - exists h. simpl. left. reflexivity.
Qed.

(* return number of appearances of v in l *)
Fixpoint count (v : nat) (l : list nat) : nat
  := match l with 
      | nil => 0
      | h :: t => if (h =? v) then S (count v t) else count v t
     end.

(* a non-member of l has count 0 in l *)
Lemma not_member_count_0 : 
  forall (l : list nat) (x : nat), member x l = false -> count x l = 0.
Proof.
  intros l x H.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. simpl in H. destruct (h =? x) as [|] eqn:Hhx.
    * discriminate H.
    * apply IH in H. apply H.
Qed.

(* a member of l has count at least 1 in l *)
Lemma member_count_at_least_1: forall (l: list nat) (x: nat),
  In x l -> count x l >= 1.
Proof.
  intros l x H.
  induction l as [| h t IH].
  - simpl in H. exfalso. apply H.
  - simpl. destruct (h =? x) as [|] eqn:Hhx.
    + lia.
    + simpl in H. destruct H as [contra | Hind].
      * rewrite contra in Hhx. rewrite eqb_refl in Hhx. discriminate Hhx.
      * apply IH. apply Hind.
Qed.

(* the count of an element in the concatenation of two lists is the sum
   of its counts in the two individual lists *)
Lemma count_app: forall (l1 l2: list nat) (x: nat),
  count x (l1 ++ l2) = count x l1 + count x l2.
Proof.
  intros l1 l2 x.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (h =? x) as [|] eqn:Hhx.
    + rewrite IH. simpl. reflexivity.
    + rewrite IH. reflexivity.
Qed.

(* the count of an element in a list is the same as its count in the
   reverse of the list *)
Lemma count_reverse: forall (l: list nat) (x: nat),
  count x l = count x (rev l).
Proof.
  intros l x. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (h =? x) as [|] eqn:Hhx.
    + rewrite count_app. simpl. rewrite Hhx. rewrite <- IH. lia.
    + rewrite count_app. simpl. rewrite Hhx. rewrite <- IH. lia.
Qed.

(* if x satisfies the `test` predicate, then filtering l by test does
   not change the count of x in l *)
Lemma count_filter: forall (l: list nat) (x: nat) (test : nat -> bool),
  test x = true -> count x l = count x (filter test l).
Proof.
  intros l x test H.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (h =? x) as [|] eqn:Hhx.
    + apply eqb_eq in Hhx. rewrite <- Hhx in H. rewrite H. simpl.
      rewrite Hhx. rewrite eqb_refl. rewrite IH. reflexivity.
    + destruct (test h) as [|] eqn:Hh.
      * simpl. rewrite Hhx. apply IH.
      * apply IH.
Qed.

(* if x is not in l, then filtering for elements not equal to x
   does not change l *)
Lemma filter_test_not_satisfied: forall (l: list nat) (x: nat),
  count x l = 0 -> l = (filter (fun v : nat => negb (v =? x)) l).
Proof.
  intros l x H.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl in H. destruct (h =? x) as [|] eqn:Hhx.
    + discriminate H.
    + apply IH in H. simpl. rewrite Hhx. simpl. f_equal. apply H.
Qed.

(* if x appears exactly once in l, then filtering l for elements unequal to x
   will remove exactly 1 from the length of l *)
Lemma count_length: forall (l: list nat) (x: nat),
  count x l = 1 -> length l = S (length (filter (fun v : nat => negb (v =? x)) l)).
Proof.
  intros l x.
  intros Hc.
  induction l as [| h t IH].
  - simpl in Hc. discriminate Hc.
  - simpl in Hc. simpl. destruct (h =? x) as [|] eqn:Hhx.
    + simpl. f_equal. inversion Hc. apply filter_test_not_satisfied in H0.
      rewrite <- H0. reflexivity.
    + f_equal. simpl. apply IH in Hc. apply Hc.
Qed.

(* the length of l filtered by any predicate `test` will always be at most
   the length of l *)
Lemma filter_makes_list_shorter: forall (X : Type) (test : X -> bool) (l: list X),
  length (filter test l) <= length l.
Proof.
  intros X test l.
  induction l as [| h t IH].
  - simpl. lia.
  - simpl. destruct (test h) as [|] eqn:H.
    + simpl. apply succ_le_mono with (m := length t). apply IH.
    + lia.
Qed.

(* if x is a member of l, then l filtered for elements unequal to x will have
   length at least 1 less than the length of l *)
Lemma filter_length_membership: forall (l: list nat) (x: nat),
  In x l -> S (length (filter (fun v : nat => negb (v =? x)) l)) <= length l.
Proof.
  intros l x H.
  induction l as [| h t IH].
  - exfalso. simpl in H. apply H.
  - simpl in H. destruct H as [Hhx | Hmem].
    + simpl. rewrite Hhx. rewrite eqb_refl. simpl. apply succ_le_mono with (m := length t).
      apply filter_makes_list_shorter.
    + apply IH in Hmem. replace (length (h :: t)) with (S (length t)).
      * simpl. destruct (h =? x) as [|] eqn:Hhx.
        -- simpl. apply le_le_succ_r with (m := length t). apply Hmem.
        -- simpl. apply succ_le_mono with (m := length t). apply Hmem.
      * simpl. reflexivity.
Qed.

(* the count of x in a list l filtered for elements unequal to x is 0 *)
Lemma count_remove_element: forall (l: list nat) (x: nat),
  count x (filter (fun v : nat => negb (v =? x)) l) = 0.
Proof.
  intros l x.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (h =? x) as [|] eqn:Hhx.
    + simpl. apply IH.
    + simpl. rewrite Hhx. apply IH.
Qed.

(* return the maximum element of a list of natural numbers *)
Fixpoint max_list (l: list nat) : nat :=
  match l with
  | [] => 0
  | h :: t => if leb (max_list t) h then h else (max_list t)
  end.

(* if x > y, then y <= x. *)
Lemma leb_true_vs_false: forall x y: nat,
 (x <=? y) = false -> (y <=? x) = true. (* x not <= y --> x > y --> y < x --> y <= x*)
Proof.
  intros x y H.
  assert (H1: y < x).
  { apply leb_iff_conv in H. apply H. }
  apply leb_le.
  apply le_trans with (m := S y).
  - apply le_succ_diag_r.
  - apply leb_correct in H1. apply leb_le in H1. apply H1.
Qed.

(* if x is a member of l, then x <= max(l) *)
Theorem max_correct: forall l: list nat, forall x: nat,
  In x l -> leb x (max_list l) = true.
Proof.
  intros l x H.
  induction l as [| h t IH].
  - simpl in H. exfalso. apply H.
  - simpl in H. destruct H as [H | H].
    + simpl. destruct (max_list t <=? h) as [|] eqn:Hmax.
      * rewrite H. unfold leb. apply leb_refl.
      * rewrite H in Hmax. apply leb_true_vs_false in Hmax. apply Hmax.
    + simpl. apply IH in H.
      destruct (max_list t <=? h) as [|] eqn:Hmax.
      * apply leb_le. apply leb_le in Hmax.
        apply le_trans with (m := (max_list t)).
        -- apply leb_le in H. apply H.
        -- apply Hmax.
      * apply H.
Qed.

(* return l after adding `shift` to each element *)
Fixpoint shift_list (l: list nat) (shift: nat) : list nat :=
  match l with
  | [] => []
  | h :: t => (h + shift) :: (shift_list t shift)
  end.

Example shift_1: shift_list [1;2;3] 4 = [5;6;7].
Proof. reflexivity. Qed.

(* in a list of tuples, return the correponding list of only the first
   element of each tuple *)
Fixpoint fsts {X Y: Type} (l: list (X * Y)) : list X :=
  match l with
  | [] => []
  | h :: t => (fst h) :: (fsts t)
  end.

Example firsts_test: fsts [(1,2); (2,3); (4,3)] = [1; 2; 4].
Proof. reflexivity. Qed.

(* return the index of the first appearance of x in l (zero-indexed),
   or None if x is not a member of l *)
Fixpoint index (l: list nat) (x: nat) : option nat :=
  match l with
  | [] => None
  | h :: t => if (h =? x) then Some 0 else
              match (index t x) with
              | None => None
              | Some i => Some (S i)
              end
  end.

(* if x is not in l1, and the index of x in l2 is i, then the index of
   x in the concatenation of l1 and l2 is len(l1) + i *)
Lemma index_append: forall (l1 l2: list nat) (x i: nat),
  ~(In x l1) /\ index l2 x = Some i
  -> index (l1 ++ l2) x = Some (length l1 + i).
Proof.
  intros l1 l2 x i [Hmem Hl2].
  unfold not in Hmem.
  induction l1 as [| h t IH].
  - simpl. apply Hl2.
  - simpl. destruct (h =? x) as [|] eqn:Hhx.
    + exfalso. apply Hmem. simpl. left. apply eqb_eq in Hhx. apply Hhx.
    + simpl in Hmem. replace (index (t ++ l2) x) with (Some (length t + i)).
      * reflexivity.
      * symmetry. apply IH. intros H. apply Hmem. right. apply H.
Qed.

(* if the index of x in the concatenation of l1 and l2 is i, and i is 
   less than the length of l1, then x is in l1 at index i *)
Lemma index_append_2: forall (l1 l2: list nat) (x i: nat),
  index (l1 ++ l2) x = Some i /\ i < length l1 ->
  index l1 x = Some i.
Proof.
  intros l1 l2 x i [H1 H2].
  generalize dependent i. induction l1 as [| h t IH].
  - intros i H1 H2. simpl in H2. lia.
  - intros i H1 H2. simpl in H1. destruct (h =? x) as [|] eqn:Hhx.
    + inversion H1. rewrite eqb_eq in Hhx. rewrite Hhx. simpl.
      rewrite eqb_refl. reflexivity.
    + simpl. rewrite Hhx. destruct (index (t ++ l2) x) as [j|] eqn:H3.
      * destruct i as [| i'] eqn:Hi.
        -- discriminate H1.
        -- specialize IH with (i := i').
           inversion H1. inversion H2.
           ++ replace (index t x) with (Some i').
              ** reflexivity.
              ** symmetry. apply IH. rewrite H0. reflexivity. lia.
           ++ replace (index t x) with (Some i').
              ** reflexivity.
              ** symmetry. apply IH. rewrite H0. reflexivity. lia.
      * discriminate H1.
Qed.

(* if the index of x in l is i, then l[i] = x *)
Theorem index_correct: forall (l: list nat) (x: nat) (i: nat),
  Some i = index l x -> nth_error l i = Some x.
Proof.
  intros l x i H.
  generalize dependent i. induction l as [| h t IH].
  - intros i H. simpl in H. discriminate H.
  - intros i H. simpl in H. destruct (h =? x) as [|] eqn:Hhx.
    + inversion H. apply eqb_eq in Hhx. rewrite Hhx. simpl. reflexivity.
    + destruct i as [| i'] eqn:Hi.
      * destruct (index t x) as [|] eqn:Hr.
        -- inversion H.
        -- discriminate H.
      * simpl. specialize IH with (i := i'). apply IH.
        destruct (index t x) as [|] eqn:Hr.
        -- inversion H. reflexivity.
        -- discriminate H.
Qed.

(* if x appears exactly once in l, and l[i] = x, then `index l x` will return i *)
Theorem index_correct_appears_once: forall (l: list nat) (x: nat) (i: nat),
  count x l = 1 -> nth_error l i = Some x
  -> Some i = index l x.
Proof.
  intros l x i Hc Hn.
  generalize dependent i. induction l as [| h t IH].
  - intros i Hn. simpl in Hc. discriminate Hc.
  - intros i Hn. simpl in Hc. destruct (h =? x) as [|] eqn:Hhx.
    + apply eqb_eq in Hhx. rewrite Hhx in *. destruct i as [| i'].
      * simpl. rewrite eqb_refl. reflexivity.
      * simpl in Hn. apply nth_error_In in Hn. inversion Hc. apply member_count_at_least_1 in Hn. lia.
    + simpl. rewrite Hhx.
      destruct i as [| i'].
      * simpl in Hn. inversion Hn. rewrite H0 in Hhx. rewrite eqb_refl in Hhx. discriminate Hhx.
      * simpl in Hn. specialize IH with (i := i'). apply IH in Hc.
        -- rewrite <- Hc. reflexivity.
        -- apply Hn.
Qed.

(* if the index of x in l is i, then i is less than len(l) *)
Theorem index_in_range: forall (l: list nat) (x: nat) (i: nat),
  Some i = index l x -> i < (length l).
Proof.
  intros l x i H.
  generalize dependent i. induction l as [| h t IH].
  - intros i H. simpl in H. discriminate H.
  - intros i H. simpl in H. destruct (h =? x) as [|] eqn:Hhx.
    + inversion H. simpl. lia.
    + simpl. destruct (index t x) as [|] eqn:Hr.
      * inversion H. specialize IH with (i := n).
        assert (H2: n < length t). { apply IH. reflexivity. }
        apply succ_lt_mono in H2. apply H2.
      * discriminate H.
Qed.

(* x is a member of l iff there is some index for which x is at that index in l *)
Theorem index_exists: forall (l: list nat) (x: nat),
  In x l <-> exists i: nat, Some i = index l x.
Proof.
  intros l x. split.
  - intros H. induction l as [| h t IH].
    + simpl in H. exfalso. apply H.
    + simpl in H. destruct H as [Hhx | Hmem].
      * exists 0. rewrite Hhx. simpl. rewrite eqb_refl. reflexivity.
      * simpl. destruct (h =? x) as [|] eqn:Hhx.
        -- exists 0. reflexivity.
        -- apply IH in Hmem. destruct Hmem as [i Hind]. exists (S i).
           destruct (index t x) as [|] eqn:Hr.
           ++ inversion Hind. reflexivity.
           ++ discriminate Hind.
  - intros [i H]. generalize dependent i. induction l as [| h t IH].
    + intros i H. simpl in H. discriminate H.
    + intros i H. simpl in H. destruct (h =? x) as [|] eqn:Hhx.
      * apply eqb_eq in Hhx. rewrite Hhx. simpl. left. reflexivity.
      * destruct i as [| i'] eqn:Hi.
        -- destruct (index t x) as [|] eqn:Hr.
           ++ inversion H.
           ++ discriminate H.
        -- destruct (index t x) as [|] eqn:Hr.
           ++ inversion H. specialize IH with (i := i').
              simpl. right. apply IH. rewrite H1. reflexivity.
           ++ discriminate H.
Qed.

(* the concatenation of l and an empty list is just l *)
Theorem append_identity: forall X, forall l: list X, l ++ [] = l.
Proof.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* rewrite two lists and a single element x as in two different ways
   using appending and concatenation *)
Theorem append_vs_concat: forall l1 l2: list nat, forall x: nat,
  (l1 ++ [x]) ++ l2 = l1 ++ x :: l2.
Proof.
  intros l1 l2 x.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* version of `append_vs_concat` for generic type X *)
Theorem append_vs_concat_X {X: Type}: forall l1 l2: list X, forall x: X,
  (l1 ++ [x]) ++ l2 = l1 ++ x :: l2.
Proof.
  intros l1 l2 x.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* if u is a member of l1, then it is a member of the concatenation of
   l1 with another list *)
Lemma membership_append: forall (X : Type) (l1 l2: list X) (u: X),
  In u l1 -> In u (l1 ++ l2).
Proof.
  intros X l1 l2 u H.
  induction l1 as [| h t IH].
  - simpl in H. exfalso. apply H.
  - simpl in H. simpl. destruct H as [H | H].
    + left. apply H.
    + right. apply IH. apply H.
Qed.

(* if u is a member of l2, then it is a member of the concatenation of
   another list with l2 *)
Lemma membership_append_r: forall (X : Type) (l1 l2: list X) (u: X),
  In u l2 -> In u (l1 ++ l2).
Proof.
  intros X l1 l2 u H.
  induction l1 as [| h t IH].
  - simpl. apply H.
  - simpl. right. apply IH.
Qed.

(* if u is a member of the concatenation of two lists, then it must be
   a member of at least one of the individual lists *)
Lemma membership_append_or: forall (X : Type) (l1 l2: list X) (u: X),
  In u (l1 ++ l2) -> In u l1 \/ In u l2.
Proof.
  intros X l1 l2 u H.
  induction l1 as [| h t IH].
  - simpl in H. right. apply H.
  - simpl in H. destruct H as [H | H].
    + left. rewrite H. simpl. left. reflexivity.
    + apply IH in H. destruct H as [H | H].
      * left. right. apply H.
      * right. apply H.
Qed.

(* the reverse of the concatenation of two lists is the concatenation
   of the reverse of the second and the reverse of the first *)
Lemma reverse_list_append: forall (l1 l2: list nat),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| h t IH].
  - simpl. symmetry. apply append_identity.
  - simpl. rewrite IH. rewrite <- app_assoc. reflexivity.
Qed.

(* the reverse of the reverse of a list is the list itself *)
Lemma reverse_list_twice: forall (l: list nat),
  l = rev (rev l).
Proof.
  intros l. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite reverse_list_append. rewrite <- IH. simpl. reflexivity.
Qed.

(* an element is in a list iff it is in the reverse of the list *)
Lemma membership_rev: forall (l: list nat) (a: nat),
  In a (rev l) <-> In a l.
Proof.
  assert (H: forall (l: list nat) (a: nat), In a l -> In a (rev l)).
  { intros l a H. induction l as [| h t IH].
    - exfalso. apply H.
    - simpl. simpl in H. destruct H as [H | H].
      + apply membership_append_r. left. apply H.
      + apply membership_append. apply IH. apply H. }
  intros l a.
  split.
  - intros H1. rewrite reverse_list_twice. apply H. apply H1.
  - apply H.
Qed.

(* rewrite two lists and two single elements in two different ways using
   append and concat *)
Lemma rearrange_list_concat_app: forall (l1 l2: list nat) (m v: nat),
  l1 ++ m :: l2 ++ [v] = (l1 ++ m :: l2) ++ [v].
Proof.
  intros l1 l2 m v. induction l1 as [| h1 t1].
  * simpl. reflexivity.
  * simpl. f_equal. apply IHt1.
Qed.

(* if `a` is a member of l, then l can be partitioned into two (possibly empty)
   lists which are connected by `a` *)
Lemma membership_splits_list: forall (l: list nat) (a: nat),
  In a l <-> exists (l1 l2: list nat), l1 ++ [a] ++ l2 = l.
Proof.
  intros l a. split.
  - intros H. induction l as [| h t IH].
    + exfalso. apply H.
    + simpl in H. destruct H as [H | H].
      * exists []. exists t. simpl. rewrite H. reflexivity.
      * apply IH in H. destruct H as [l1 [l2 H]].
        exists (h :: l1). exists l2. simpl. rewrite <- H. simpl. reflexivity.
  - intros [l1 [l2 H]]. rewrite <- H. apply membership_append_r. apply membership_append. left. reflexivity.
Qed.