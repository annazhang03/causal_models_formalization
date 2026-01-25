Require Import Stdlib.Lists.List.
Require Import Stdlib.Structures.Equalities.
Import ListNotations.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
Require Import Classical.
From Utils Require Import List_Basics.
From Utils Require Import Logic.


(* this file introduces and proves properties of several functions that
   relate two lists, such as overlap, subset, union, and intersection *)

Fixpoint overlap (s1 : list nat) (s2 : list nat) : bool
  := match s1 with
      | nil => false
      | h :: t => if (member h s2) then true else overlap t s2
    end.

Example no_overlap : overlap [1;2;3] [4] = false.
Proof. reflexivity. Qed.

Example one_overlap : overlap [1;2;3] [2] = true.
Proof. reflexivity. Qed.

Lemma overlap_with_empty: forall l, overlap l [] = false.
Proof.
  intros l. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. apply IH.
Qed.

Lemma overlap_cat: forall (x: nat) (l1 l2: list nat),
  overlap (x :: l1) l2 = false -> overlap l1 l2 = false.
Proof.
  intros x l1 l2 H. simpl in H. destruct (member x l2) as [|]. discriminate H. apply H.
Qed.

(* if two lists have overlap, there is an element x that belongs to both lists *)
Theorem overlap_has_member_in_common: forall l1 l2: list nat,
  overlap l1 l2 = true <-> exists x: nat, In x l1 /\ In x l2.
Proof.
  intros l1 l2. split.
  - intros H. induction l1 as [| h1 t1 IH].
    + simpl in H. discriminate H.
    + simpl in H. destruct (member h1 l2) as [|] eqn:Hmem.
      * simpl. exists h1. split.
        -- left. reflexivity.
        -- apply member_In_equiv. apply Hmem.
      * apply IH in H. destruct H as [x [H1 H2]].
        exists x. split.
        -- simpl. right. apply H1.
        -- apply H2.
  - intros [x [H1 H2]]. induction l1 as [| h1 t1 IH].
    + simpl in H1. exfalso. apply H1.
    + simpl. destruct (member h1 l2) as [|] eqn:Hmem.
      * reflexivity.
      * simpl in H1. destruct H1 as [H1 | H1].
        -- rewrite <- H1 in H2. apply member_In_equiv in H2. rewrite H2 in Hmem.
           discriminate Hmem.
        -- apply IH. apply H1.
Qed.

Theorem no_overlap_non_member: forall l1 l2: list nat,
  overlap l1 l2 = false <-> forall x: nat, In x l2 -> ~(In x l1).
Proof.
  intros l1 l2. split.
  { intros Hover x HIn.
  induction l1 as [| h t IH].
  - intros contra. simpl in contra. apply contra.
  - intros H. simpl in H. destruct H as [H | H].
    + simpl in Hover. rewrite <- H in HIn. apply member_In_equiv in HIn.
      rewrite HIn in Hover. discriminate Hover.
    + simpl in Hover. destruct (member h l2) as [|] eqn:Hmem.
      * discriminate Hover.
      * apply IH in Hover. unfold not in Hover. apply Hover in H. apply H. }
  { intros H. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (member h l2) as [|] eqn:Hmem.
    + specialize (H h). apply member_In_equiv in Hmem. apply H in Hmem.
      unfold not in Hmem. simpl in Hmem. exfalso. apply Hmem. left. reflexivity.
    + apply IH. simpl in H.
      intros x Hxl2. specialize (H x). intros Hxt. apply H in Hxl2. unfold not in Hxl2.
      apply Hxl2. right. apply Hxt. }
Qed.

Theorem no_overlap_non_member_rev: forall l1 l2: list nat,
  overlap l1 l2 = false <-> forall x: nat, In x l1 -> ~(In x l2).
Proof.
  intros l1 l2. split.
  { intros Hover x HIn.
  induction l1 as [| h t IH].
  - simpl in HIn. exfalso. apply HIn.
  - intros HIn2. simpl in Hover. apply member_In_equiv in HIn2.
    simpl in HIn. destruct HIn as [Hhx | Hind].
    + rewrite Hhx in Hover. rewrite HIn2 in Hover. discriminate Hover.
    + apply IH.
      * destruct (member h l2) as [|] eqn:Hmem.
        -- discriminate Hover.
        -- apply Hover.
      * apply Hind.
      * apply member_In_equiv. apply HIn2. }
  { intros H. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (member h l2) as [|] eqn:Hmem.
    + specialize (H h). apply member_In_equiv in Hmem. apply H in Hmem.
      * exfalso. apply Hmem.
      * simpl. left. reflexivity.
    + apply IH. simpl in H. intros x HIn. specialize (H x).
      apply H. right. apply HIn. }
Qed.

Lemma overlap_rev: forall (l1 l2: list nat),
  overlap l1 l2 = false -> overlap l1 (rev l2) = false.
Proof.
  intros l1 l2 H.
  destruct (overlap l1 (rev l2)) as [|] eqn:F.
  - apply overlap_has_member_in_common in F. destruct F as [x [Hx1 Hx2]].
    apply no_overlap_non_member with (x := x) in H.
    + exfalso. apply H. apply Hx1.
    + apply membership_rev. apply Hx2.
  - reflexivity.
Qed.

Lemma overlap_rev_true: forall (l1 l2: list nat),
  overlap l1 l2 = true -> overlap l1 (rev l2) = true.
Proof.
  intros l1 l2 F.
  destruct (overlap l1 (rev l2)) as [|] eqn:H.
  - reflexivity.
  - apply overlap_has_member_in_common in F. destruct F as [x [Hx1 Hx2]].
    apply no_overlap_non_member with (x := x) in H.
    + exfalso. apply H. apply Hx1.
    + apply membership_rev. apply Hx2.
Qed.

Lemma overlap_flip: forall (l1 l2: list nat),
  overlap l1 l2 = false -> overlap l2 l1 = false.
Proof.
  intros l1 l2 H.
  apply no_overlap_non_member. intros x Hxl1 Hxl2.
  apply no_overlap_non_member with (x := x) in H.
  - apply H. apply Hxl1.
  - apply Hxl2.
Qed.

Lemma overlap_flip_2: forall (l1 l2: list nat),
  overlap l1 l2 = overlap l2 l1.
Proof.
  intros l1 l2. destruct (overlap l1 l2) as [|] eqn:H.
  { symmetry. apply overlap_has_member_in_common in H. destruct H as [x [Hx1 Hx2]].
    apply overlap_has_member_in_common. exists x. easy. }
  { symmetry. apply no_overlap_non_member. intros x Hxl1 Hxl2.
    apply no_overlap_non_member with (x := x) in H.
    - apply H. apply Hxl1.
    - apply Hxl2. }
Qed.



(* return true if l1 is subset of l2 *)
Definition subset (l1 l2 : list nat) : bool :=
  forallb (fun x => member x l2) l1.

Example test_subset_true: subset [1; 2; 3] [3; 4; 2; 5; 1] = true.
Proof. reflexivity. Qed.

Example test_subset_false: subset [1; 2; 3] [3; 4; 2; 5] = false.
Proof. reflexivity. Qed.

Lemma subset_identity: forall (l: list nat),
  subset l l = true.
Proof.
  unfold subset. intros l.
  apply forallb_true_iff_mem. intros x H. apply member_In_equiv. apply H.
Qed.

Theorem subset_larger_set_membership: forall l1 l2: list nat, forall x: nat,
  subset l1 l2 = true /\ In x l1 -> In x l2.
Proof.
  intros l1 l2 x [Hsub Hmem].
  induction l1 as [| h t IH].
  - simpl in Hmem. exfalso. apply Hmem.
  - simpl in Hsub. simpl in Hmem.
    apply split_and_true in Hsub. destruct Hsub as [Hhl2 Hsubt].
    destruct Hmem as [Hhx | Hmem].
    + apply member_In_equiv. rewrite <- Hhx. apply Hhl2.
    + apply IH in Hsubt. apply Hsubt. apply Hmem.
Qed.



(* return elements in l1 that are not in l2 *)
Definition set_subtract (l1 l2 : list nat) : list nat :=
  filter (fun x => negb (member x l2)) l1.

Example test_set_subtract: set_subtract [3; 4; 2; 5; 1] [4; 3] = [2; 5; 1].
Proof. reflexivity. Qed.

Example test_set_subtract_not_in_set: set_subtract [3; 4] [1; 2; 3] = [4].
Proof. reflexivity. Qed.

Example test_set_subtract_duplicates: set_subtract [3; 4] [4; 4] = [3].
Proof. reflexivity. Qed.

Theorem set_subtract_membership: forall l1 l2: list nat, forall x: nat,
  ~(In x l2) /\ (In x l1) -> In x (set_subtract l1 l2).
Proof.
  intros l1 l2 x [H1 H2].
  induction l1 as [| h t IH].
  - simpl in H2. exfalso. apply H2.
  - simpl. simpl in H2. destruct H2 as [H2 | H2].
    + destruct (member h l2) as [|] eqn:Hmem.
      * rewrite <- H2 in H1. unfold not in H1. rewrite <- member_In_equiv in H1. apply H1 in Hmem.
        exfalso. apply Hmem.
      * simpl. left. apply H2.
    + destruct (member h l2) as [|] eqn:Hmem.
      * simpl. apply IH. apply H2.
      * simpl. right. apply IH. apply H2.
Qed.

(* l1 \ l2 is always a subset of l1 *)
Theorem set_subtract_subset: forall l1 sub: list nat,
  subset (set_subtract l1 sub) l1 = true.
Proof.
  intros l1 sub.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - destruct (member h sub) as [|] eqn:Hmem.
    + simpl. rewrite Hmem. simpl. unfold subset in IH. unfold subset. simpl.
      apply forallb_true_iff. apply forallb_true_iff in IH.
      induction (set_subtract t sub) as [| x xs IHxs].
      * simpl. apply I.
      * constructor.
        -- destruct (h =? x) as [|] eqn:Hhx. reflexivity. apply IH.
        -- apply IHxs. apply IH.
    + simpl. rewrite Hmem. simpl. rewrite eqb_refl. simpl.
      unfold subset in IH. unfold subset. simpl.
      apply forallb_true_iff. apply forallb_true_iff in IH.
      induction (set_subtract t sub) as [| x xs IHxs].
      * simpl. apply I.
      * constructor.
        -- destruct (h =? x) as [|] eqn:Hhx. reflexivity. apply IH.
        -- apply IHxs. apply IH.
Qed.



Fixpoint union (l1 l2: list nat) : list nat :=
  match l2 with
  | [] => l1
  | h :: t => if (member h l1) then union l1 t else h :: (union l1 t)
  end.

Theorem union_correct: forall l1 l2: list nat, forall x: nat,
  In x (union l1 l2) <-> (In x l1) \/ (In x l2).
Proof.
  intros l1 l2 x.
  induction l2 as [| h t IH].
  - split.
    + intros H. simpl in H. left. apply H.
    + intros [H | H].
      * simpl. apply H.
      * simpl in H. exfalso. apply H.
  - simpl. destruct (member h l1) as [|] eqn:mem.
    + split.
      * intros H. apply IH in H. destruct H as [H | H].
        -- left. apply H.
        -- right. simpl. right. apply H.
      * intros [H | [H | H]].
        -- apply IH. left. apply H.
        -- apply IH. left. apply member_In_equiv. rewrite <- H. apply mem.
        -- apply IH. right. apply H.
    + split.
      * intros H. simpl in H. destruct H as [H | H].
        -- right. left. apply H.
        -- apply IH in H. destruct H as [H | H].
           ++ left. apply H.
           ++ right. right. apply H.
      * intros [H | [H | H]].
        -- simpl. right. apply IH. left. apply H.
        -- simpl. left. apply H.
        -- simpl. right. apply IH. right. apply H.
Qed.




Fixpoint intersect (l1 l2: list nat) : list nat :=
  match l2 with
  | [] => []
  | h :: t => if (member h l1) then h :: (intersect l1 t) else intersect l1 t
  end.

Theorem intersect_correct: forall l1 l2: list nat,
  subset (intersect l1 l2) l1 = true.
Proof.
  intros l1 l2.
  induction l2 as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (member h l1) as [|] eqn:mem.
    + simpl. rewrite mem. rewrite IH. reflexivity.
    + apply IH.
Qed.

Theorem intersect_correct_element: forall l1 l2: list nat, forall x: nat,
  In x (intersect l1 l2) -> In x l2.
Proof.
  intros l1 l2 x H.
  induction l2 as [| h t IH].
  - simpl in H. exfalso. apply H.
  - simpl. simpl in H. destruct (member h l1) as [|] eqn:mem.
    + simpl in H. destruct H as [H | H].
      * left. apply H.
      * right. apply IH. apply H.
    + right. apply IH. apply H.
Qed.

Theorem intersect_in_both_lists: forall l1 l2: list nat, forall x: nat,
  In x l1 /\ In x l2 -> In x (intersect l1 l2).
Proof.
  intros l1 l2 x [H1 H2].
  induction l2 as [| h t IH].
  - simpl in H2. exfalso. apply H2.
  - simpl. simpl in H2. destruct H2 as [H2 | H2].
    + destruct (member h l1) as [|] eqn:Hmem.
      * simpl. left. apply H2.
      * apply member_In_equiv in H1. rewrite <- H2 in H1. rewrite H1 in Hmem. discriminate Hmem.
    + destruct (member h l1) as [|] eqn:Hmem.
      * simpl. right. apply IH. apply H2.
      * apply IH. apply H2.
Qed.



(* if two lists have overlap, then we can pinpoint the first element of overlap, x, such that
   the two sublists that precede x in each of the lists do not overlap.
   example: [1, 2, 3, 4] and [5, 4, 3] -> x = 4 or 3 both satisfy the requirement *)
Theorem lists_have_first_elt_in_common: forall (l1 l2: list nat),
  overlap l1 l2 = true
  -> exists (l1' l1'' l2' l2'': list nat) (x: nat), l1 = l1' ++ [x] ++ l1'' /\ l2 = l2' ++ [x] ++ l2'' /\ overlap l1' l2' = false.
Proof.
  intros l1 l2 H.
  induction l1 as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. destruct (member h l2) as [|] eqn:Hmem.
    + exists []. exists t. apply member_In_equiv in Hmem. apply membership_splits_list in Hmem. destruct Hmem as [l2' [l2'' Hl2]].
      exists l2'. exists l2''. exists h. repeat split. symmetry. apply Hl2.
    + apply IH in H. destruct H as [l1' [l1'' [l2' [l2'' [x [Ht [Hl2 Hover]]]]]]].
      exists (h :: l1'). exists l1''. exists l2'. exists l2''. exists x. repeat split.
      * simpl. f_equal. apply Ht.
      * apply Hl2.
      * simpl. destruct (member h l2') as [|] eqn:Hmem'.
        -- apply member_In_equiv in Hmem'. apply membership_append with (l2 := [x] ++ l2'') in Hmem'. rewrite <- Hl2 in Hmem'.
           apply member_In_equiv in Hmem'. rewrite Hmem' in Hmem. discriminate Hmem.
        -- apply Hover.
Qed.

(* if two lists have overlap, then we can pinpoint an element x such that all elements preceding x
   in the second list do not appear anywhere in the first list.
   example: [1, 2, 3, 4] and [3, 3, 4, 4] -> 3, the prefix l2' = []
            [1, 1, 2, 2] and [3, 2, 1, 4] -> 2, the prefix l2' = [3] *)
Theorem list_has_first_elt_in_common_with_other_list: forall (l1 l2: list nat),
  overlap l1 l2 = true
  -> exists (l1' l1'' l2' l2'': list nat) (x: nat), l1 = l1' ++ [x] ++ l1'' /\ l2 = l2' ++ [x] ++ l2''
        /\ overlap l1 l2' = false.
Proof.
  intros l1 l2 H.
  induction l2 as [| h t IH].
  - rewrite overlap_flip_2 in H. simpl in H. discriminate H.
  - rewrite overlap_flip_2 in H. simpl in H. destruct (member h l1) as [|] eqn:Hmem.
    + apply member_In_equiv in Hmem. apply membership_splits_list in Hmem. destruct Hmem as [l1' [l1'' Hl1]].
      exists l1'. exists l1''. exists []. exists t. exists h. repeat split.
      symmetry. apply Hl1.
      apply overlap_with_empty.
    + rewrite overlap_flip_2 in H. apply IH in H. destruct H as [l1' [l1'' [l2' [l2'' [x H]]]]].
      exists l1'. exists l1''. exists (h :: l2'). exists l2''. exists x. repeat split.
      * apply H.
      * simpl. f_equal. apply H.
      * rewrite overlap_flip_2. simpl. rewrite Hmem. rewrite overlap_flip_2. apply H.
Qed.


(* below are several lemmas to relate the last elements of two lists *)
Lemma last_elts_of_equal_lists: forall (l1 l2: list nat) (a b: nat),
  l1 ++ [a] = l2 ++ [b] -> a = b.
Proof.
  intros l1 l2 a b H. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H. simpl in H. destruct l2 as [| h2 t2].
    + simpl in H. inversion H. reflexivity.
    + simpl in H. destruct t2 as [| h2' t2']. simpl in H. discriminate H. simpl in H. discriminate H.
  - intros l2 H. simpl in H. destruct l2 as [| h2 t2].
    + simpl in H. destruct t1 as [| h1' t1']. simpl in H. discriminate H. simpl in H. discriminate H.
    + inversion H. specialize IH with (l2 := t2). apply IH. apply H2.
Qed.

Lemma last_elts_of_equal_lists_2: forall (l1 l2 l3: list nat) (a: nat),
  l1 ++ [a] = l2 ++ l3 -> l3 = [] \/ exists (l4: list nat), l3 = l4 ++ [a].
Proof.
  intros l1 l2 l3 a H. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H. simpl in H. destruct l2 as [| h2 t2].
    + simpl in H. right. exists []. simpl. rewrite H. reflexivity.
    + simpl in H. inversion H. left. destruct t2 as [| h2' t2'].
      * simpl in H2. rewrite H2. reflexivity.
      * discriminate H2.
  - intros l2 H. simpl in H. destruct l2 as [| h2 t2].
    + simpl in H. destruct l3 as [| h3 t3].
      * discriminate H.
      * inversion H. right. exists (h3 :: t1). reflexivity.
    + inversion H. specialize IH with (l2 := t2). apply IH. apply H2.
Qed.

Lemma path_breaks_down_midpoint_vs_endpoint: forall (l1 l2 l3: list nat) (a b: nat),
  l1 ++ [a] ++ l2 = l3 ++ [b]
  -> (rev l2 = [] -> a = b /\ l1 = l3) /\ (forall (hl2: nat) (tl2: list nat), rev l2 = hl2 :: tl2 -> b = hl2 /\ l3 = l1 ++ [a] ++ rev tl2).
Proof.
  intros l1' l2' l3 a b H. split.
  { intros Hlp2.
    assert (Hlem: rev (l1' ++ [a]) = rev (l3 ++ [b])).
    { rewrite <- H. rewrite reverse_list_append. rewrite reverse_list_append. rewrite reverse_list_append. rewrite Hlp2.
      simpl. reflexivity. }
    rewrite reverse_list_append in Hlem. rewrite reverse_list_append in Hlem. simpl in Hlem.
    inversion Hlem. split. reflexivity. rewrite reverse_list_twice with (l := l1'). rewrite H2. rewrite <- reverse_list_twice.
    reflexivity. }
  { intros hlp2' tlp2' Hlp2'. assert (Hlem: rev (l1' ++ [a] ++ l2') = rev (l3 ++ [b])).
    { rewrite <- H. reflexivity. }
    rewrite reverse_list_append in Hlem. rewrite reverse_list_append in Hlem. rewrite Hlp2' in Hlem. simpl in Hlem. rewrite reverse_list_append in Hlem.
    simpl in Hlem. inversion Hlem. split. reflexivity. rewrite reverse_list_twice with (l := l3).
    rewrite <- H2. repeat rewrite reverse_list_append. rewrite <- reverse_list_twice. simpl. reflexivity. }
Qed.

Lemma last_suffix {X: Type}: forall (L: list X) (u h a b: X),
  last (u :: h :: L) a = last (h :: L) b.
Proof.
  intros L u h a b.
  simpl. generalize dependent h. induction L as [| h' t' IH].
  - reflexivity.
  - intros h. simpl. apply IH.
Qed.

Lemma last_mem {X: Type}: forall (L: list X) (u h a: X),
  In (last (u :: h :: L) a) (h :: L).
Proof.
  intros L u h a.
  generalize dependent u. generalize dependent h. induction L as [| h' t'].
  - intros h u. simpl. left. reflexivity.
  - intros h u. rewrite last_suffix with (b := a). right. apply IHt'.
Qed.


(* a node (b) with at least one node (c) after in a list must be in the list minus
   the last element (v) *)
Lemma middle_node_not_end: forall (l l' l'': list nat) (b c v: nat),
  l ++ [v] = l'' ++ b :: c :: l'
  -> In b l.
Proof.
  intros l l' l'' b c v H.
  destruct (rev l') as [| h t] eqn:Hl'.
  - assert (Hl: l' = []). { rewrite reverse_list_twice with (l := l'). rewrite Hl'. reflexivity. }
    rewrite Hl in *. clear Hl. assert (Hl: v :: rev l = rev (l'' ++ [b; c])). { rewrite <- H. rewrite reverse_list_append. simpl. reflexivity. }
    rewrite reverse_list_append in Hl. simpl in Hl. inversion Hl. apply membership_rev. rewrite H2. left. reflexivity.
  - assert (Hl: l' = rev t ++ [h]). { rewrite reverse_list_twice with (l := l'). rewrite Hl'. reflexivity. }
    rewrite Hl in *. clear Hl. assert (Hl: v :: rev l = rev (l'' ++ b :: c :: rev t ++ [h])). { rewrite <- H. rewrite reverse_list_append. simpl. reflexivity. }
    rewrite reverse_list_append in Hl. simpl in Hl. rewrite reverse_list_append in Hl. simpl in Hl. inversion Hl. apply membership_rev. rewrite H2. apply membership_append. apply membership_append_r. left. reflexivity.
Qed.



(* return true iff last elt of l1 is the same as first elt of l2 *)
Fixpoint first_and_last_elts_same (l1 l2: list nat) : bool :=
  match l2 with
  | [] => false
  | h2 :: t2 => match l1 with
                | [] => false
                | [h1] => h1 =? h2
                | h1 :: t => (first_and_last_elts_same t l2)
                end
  end.

Example same_fl_elt: first_and_last_elts_same [1;2;3;4] [4;5;6;1] = true.
Proof. reflexivity. Qed.

Example diff_fl_elt: first_and_last_elts_same [1;2;3;4] [1;5;6;1] = false.
Proof. reflexivity. Qed.

Example trivial_l2: first_and_last_elts_same [1;2;3;4] [] = false.
Proof. reflexivity. Qed.

Theorem first_and_last_same: forall (l1 l2: list nat) (x: nat),
  first_and_last_elts_same (l1 ++ [x]) (x :: l2) = true.
Proof.
  intros l1 l2 x.
  induction l1 as [| h t IH].
  - simpl. apply eqb_refl.
  - simpl. destruct (t ++ [x]) as [| h' t'].
    + simpl in IH. discriminate IH.
    + apply IH.
Qed.
