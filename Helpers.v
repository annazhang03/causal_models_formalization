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


(* simple list functions *)
Fixpoint eqblist (l1 l2 : list nat) : bool
  := match l1, l2 with
      | nil, nil => true
      | nil, _ => false
      | _, nil => false
      | h1 :: t1, h2 :: t2 => if (h1 =? h2) then eqblist t1 t2 else false
end.

Theorem eqblist_refl : forall l: list nat,
  true = eqblist l l.
Proof.
  induction l as [| h t IHl].
  - simpl. reflexivity.
  - simpl. rewrite eqb_refl. rewrite IHl. reflexivity.
Qed.

Theorem eqblist_empty: forall (l: list nat) (x: nat),
  eqblist (l ++ [x]) [] = false.
Proof.
  intros l x.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fixpoint member (v : nat) (s : list nat) : bool
  := match s with
      | nil => false
      | h :: t => if (h =? v) then true else member v t
    end.


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


Theorem length_member: forall (l: list nat) (n': nat),
  (length l = S n') -> exists x, In x l.
Proof.
  intros l n' H.
  destruct l as [| h t].
  - simpl in H. discriminate H.
  - exists h. simpl. left. reflexivity.
Qed.

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


Fixpoint count (v : nat) (l : list nat) : nat
  := match l with 
      | nil => 0
      | h :: t => if (h =? v) then S (count v t) else count v t
     end.

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

Lemma count_reverse: forall (l: list nat) (x: nat),
  count x l = count x (rev l).
Proof.
  intros l x. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (h =? x) as [|] eqn:Hhx.
    + rewrite count_app. simpl. rewrite Hhx. rewrite <- IH. lia.
    + rewrite count_app. simpl. rewrite Hhx. rewrite <- IH. lia.
Qed.

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

Theorem append_identity: forall X, forall l: list X, l ++ [] = l.
Proof.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem append_vs_concat: forall l1 l2: list nat, forall x: nat,
  (l1 ++ [x]) ++ l2 = l1 ++ x :: l2.
Proof.
  intros l1 l2 x.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem append_vs_concat_X {X: Type}: forall l1 l2: list X, forall x: X,
  (l1 ++ [x]) ++ l2 = l1 ++ x :: l2.
Proof.
  intros l1 l2 x.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

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

Lemma membership_append_r: forall (X : Type) (l1 l2: list X) (u: X),
  In u l2 -> In u (l1 ++ l2).
Proof.
  intros X l1 l2 u H.
  induction l1 as [| h t IH].
  - simpl. apply H.
  - simpl. right. apply IH.
Qed.

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

Lemma reverse_list_append: forall (l1 l2: list nat),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| h t IH].
  - simpl. symmetry. apply append_identity.
  - simpl. rewrite IH. rewrite <- app_assoc. reflexivity.
Qed.

Lemma reverse_list_twice: forall (l: list nat),
  l = rev (rev l).
Proof.
  intros l. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite reverse_list_append. rewrite <- IH. simpl. reflexivity.
Qed.

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

Lemma overlap_cat: forall (x: nat) (l1 l2: list nat),
  overlap (x :: l1) l2 = false -> overlap l1 l2 = false.
Proof.
  intros x l1 l2 H. simpl in H. destruct (member x l2) as [|]. discriminate H. apply H.
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

Lemma overlap_flip: forall (l1 l2: list nat),
  overlap l1 l2 = false -> overlap l2 l1 = false.
Proof.
  intros l1 l2 H.
  apply no_overlap_non_member. intros x Hxl1 Hxl2.
  apply no_overlap_non_member with (x := x) in H.
  - apply H. apply Hxl1.
  - apply Hxl2.
Qed.

Fixpoint max_list (l: list nat) : nat :=
  match l with
  | [] => 0
  | h :: t => if leb (max_list t) h then h else (max_list t)
  end.


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


Fixpoint shift_list (l: list nat) (shift: nat) : list nat :=
  match l with
  | [] => []
  | h :: t => (h + shift) :: (shift_list t shift)
  end.

Example shift_1: shift_list [1;2;3] 4 = [5;6;7].
Proof. reflexivity. Qed.

Fixpoint fsts {X Y: Type} (l: list (X * Y)) : list X :=
  match l with
  | [] => []
  | h :: t => (fst h) :: (fsts t)
  end.

Example firsts_test: fsts [(1,2); (2,3); (4,3)] = [1; 2; 4].
Proof. reflexivity. Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c. 
  intros H.
  destruct b eqn:Eb.
  - reflexivity.
  - rewrite <- H. destruct c eqn: Ec.
    + reflexivity.
    + reflexivity.
Qed.

Fixpoint index (l: list nat) (x: nat) : option nat :=
  match l with
  | [] => None
  | h :: t => if (h =? x) then Some 0 else
              match (index t x) with
              | None => None
              | Some i => Some (S i)
              end
  end.

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

Lemma split_and_true : forall a b, a && b = true <-> a = true /\ b = true.
Proof.
  intros a b. split.
  { intros H.
    split.
    - apply andb_true_elim2 in H. apply H.
    - rewrite andb_comm in H. apply andb_true_elim2 in H. apply H. }
  { intros H. destruct H as [H1 H2]. rewrite H1. rewrite H2. reflexivity. }
Qed.

Theorem orb_true_elim2 : forall b c : bool,
  orb b c = false -> b = false.
Proof.
  intros b c. 
  intros H.
  destruct b eqn:Eb.
  - simpl in H. discriminate H.
  - reflexivity.
Qed.

Lemma split_orb_false : forall a b, a || b = false <-> a = false /\ b = false.
Proof.
  intros a b. split.
  { intros H.
  split.
  - apply orb_true_elim2 in H. apply H.
  - rewrite orb_comm in H. apply orb_true_elim2 in H. apply H. }
  { intros [Ha Hb]. rewrite Ha. rewrite Hb. simpl. reflexivity. }
Qed.

Lemma split_orb_true : forall a b, a || b = true <-> a = true \/ b = true.
Proof.
  intros a b. split.
  { intros H. destruct a as [|] eqn:A.
    - left. reflexivity.
    - simpl in H. right. apply H. }
  { intros [H | H].
    - rewrite H. simpl. reflexivity.
    - rewrite H. rewrite orb_comm. simpl. reflexivity. }
Qed.

Lemma negb_both_sides: forall b c: bool, negb b = c -> b = negb c.
Proof.
  intros b c H.
  destruct b as [|]. destruct c as [|].
  - simpl in H. discriminate H.
  - simpl. reflexivity.
  - destruct c as [|]. simpl. reflexivity. simpl in H. discriminate H.
Qed.


(* functions for two lists *)

(* output true if l1 is subset of l2 *)
Definition subset (l1 l2 : list nat) : bool :=
  forallb (fun x => member x l2) l1.

Example test_subset_true: subset [1; 2; 3] [3; 4; 2; 5; 1] = true.
Proof. reflexivity. Qed.

Example test_subset_false: subset [1; 2; 3] [3; 4; 2; 5] = false.
Proof. reflexivity. Qed.

(* set subtraction: elements in l1 that are not in l2 *)
Definition set_subtract (l1 l2 : list nat) : list nat :=
  filter (fun x => negb (member x l2)) l1.

Example test_set_subtract: set_subtract [3; 4; 2; 5; 1] [4; 3] = [2; 5; 1].
Proof. reflexivity. Qed.

Example test_set_subtract_not_in_set: set_subtract [3; 4] [1; 2; 3] = [4].
Proof. reflexivity. Qed.

Example test_set_subtract_duplicates: set_subtract [3; 4] [4; 4] = [3].
Proof. reflexivity. Qed.

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





Fixpoint prefix (l1 l2: list nat): bool :=
  match l1 with
  | [] => true
  | h1 :: t1 => match l2 with
                | [] => false
                | h2 :: t2 => (h1 =? h2) && prefix t1 t2
                end
  end.

Fixpoint sublist (l1 l2: list nat) : bool :=
  match l2 with
  | [] => eqblist l1 []
  | h1 :: t1 => prefix l1 l2 || sublist l1 t1
  end.


Example sublist_1: sublist [2;3] [1;2;3;4] = true.
Proof. reflexivity. Qed.

Example sublist_2: sublist [2;3] [1;2;4;3;2;3;2] = true.
Proof. reflexivity. Qed.

Example sublist_3: sublist [2;3] [1;2;4;3] = false.
Proof. reflexivity. Qed.

Lemma sublist_empty: forall l: list nat, sublist [] l = true.
Proof.
  destruct l as [| h t].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Class EqType (X : Type) := {
  eqb : X -> X -> bool;
  eqb_refl' : forall x, eqb x x = true;
  eqb_sym' : forall x y, eqb x y = eqb y x;
  eqb_eq' : forall x y, eqb x y = true <-> x = y
}.

Fixpoint eqblistX {X: Type} `{EqType X} (l1 l2 : list X) : bool
  := match l1, l2 with
      | nil, nil => true
      | nil, _ => false
      | _, nil => false
      | h1 :: t1, h2 :: t2 => if (eqb h1 h2) then eqblistX t1 t2 else false
end.


Fixpoint prefixX {X: Type} `{EqType X} (l1 l2: list X): bool :=
  match l1 with
  | [] => true
  | h1 :: t1 => match l2 with
                | [] => false
                | h2 :: t2 => (eqb h1 h2) && prefixX t1 t2
                end
  end.

Fixpoint sublistX {X: Type} `{EqType X} (l1 l2: list X) : bool :=
  match l2 with
  | [] => eqblistX l1 []
  | h1 :: t1 => prefixX l1 l2 || sublistX l1 t1
  end.

Lemma prefix_member_X {X: Type} `{EqType X}: forall (l1 l2: list X) (x: X),
  In x l1 /\ prefixX l1 l2 = true -> In x l2.
Proof.
  intros l1.
  induction l1 as [| h1 t1 IH].
  - intros l2 x. intros [Hmem Hpre]. exfalso. apply Hmem.
  - intros l2 x. intros [Hmem Hpre]. destruct l2 as [| h2 t2].
    + simpl in Hpre. discriminate Hpre.
    + simpl in Hpre. simpl in Hmem. simpl.
      apply split_and_true in Hpre. destruct Hpre as [H12 Hpre].
      destruct Hmem as [Hhx | Hmem].
      * apply eqb_eq' in H12. rewrite H12 in Hhx. left. apply Hhx.
      * right. apply IH with (l2 := t2). split.
        -- apply Hmem.
        -- apply Hpre.
Qed.

Lemma prefix_member: forall (l1 l2: list nat) (x: nat),
  In x l1 /\ prefix l1 l2 = true -> In x l2.
Proof.
  intros l1.
  induction l1 as [| h1 t1 IH].
  - intros l2 x. intros [Hmem Hpre]. exfalso. apply Hmem.
  - intros l2 x. intros [Hmem Hpre]. destruct l2 as [| h2 t2].
    + simpl in Hpre. discriminate Hpre.
    + simpl in Hpre. simpl in Hmem. simpl.
      apply split_and_true in Hpre. destruct Hpre as [H12 Hpre].
      destruct Hmem as [Hhx | Hmem].
      * apply eqb_eq in H12. rewrite H12 in Hhx. left. apply Hhx.
      * right. apply IH with (l2 := t2). split.
        -- apply Hmem.
        -- apply Hpre.
Qed.


Theorem sublist_member: forall (l1 l2: list nat) (x: nat),
  In x l1 /\ sublist l1 l2 = true -> In x l2.
Proof.
  intros l1 l2 x.
  intros [Hmem Hsub].
  induction l2 as [| h2 t2 IH].
  - destruct l1 as [| h1 t1].
    + apply Hmem.
    + simpl in Hsub. discriminate Hsub.
  - simpl. simpl in Hsub.
    apply split_orb_true in Hsub. destruct Hsub as [Hpre | Hind].
    + destruct l1 as [| h1 t1].
      * exfalso. apply Hmem.
      * simpl in Hmem. simpl in Hpre. apply split_and_true in Hpre.
        destruct Hpre as [H12 Hpre].
        destruct Hmem as [Hhx | Hmem].
        -- left. rewrite <- Hhx. apply eqb_eq in H12. rewrite H12. reflexivity.
        -- right. apply prefix_member with (l1 := t1). split.
           apply Hmem. apply Hpre.
    + right. apply IH. apply Hind.
Qed.

Lemma prefix_identity: forall (l1 l2: list nat),
  prefix l1 (l1 ++ l2) = true.
Proof.
  intros l1 l2. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite eqb_refl. rewrite IH. reflexivity.
Qed.

Lemma prefix_implies_sublist: forall (l1 l2: list nat),
  prefix l1 l2 = true -> sublist l1 l2 = true.
Proof.
  intros l1 l2 H.
  destruct l1 as [| h t].
  - destruct l2 as [| h' t'].
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct l2 as [| h' t'].
    + simpl in H. discriminate H.
    + simpl in H. apply split_and_true in H. destruct H as [Hh Hpre].
      simpl. rewrite Hh. rewrite Hpre. reflexivity.
Qed.

Lemma prefix_breaks_down_list: forall (l1 l: list nat),
  prefix l1 l = true <-> exists (l2: list nat), l1 ++ l2 = l.
Proof.
  intros l1 l. split.
  { generalize dependent l1. induction l as [| h t IH].
  - intros l1 H. simpl in H. destruct l1 as [| h' t'].
    + simpl. exists []. reflexivity.
    + simpl in H. discriminate H.
  - intros l1 H. destruct l1 as [| h' t'].
    + exists (h :: t). simpl. reflexivity.
    + simpl in H. apply split_and_true in H. destruct H as [Hh Hpre].
      specialize IH with (l1 := t'). apply IH in Hpre. destruct Hpre as [l2 Hl2].
      exists l2. simpl. rewrite Hl2. apply eqb_eq in Hh. rewrite Hh. reflexivity. }
  { intros [l2 H]. rewrite <- H. apply prefix_identity. }
Qed.

Theorem sublist_breaks_down_list: forall (l1 l: list nat),
  sublist l1 l = true <-> exists (l2 l3: list nat), l2 ++ l1 ++ l3 = l.
Proof.
  intros l1 l. split.
  { intros H. induction l as [| h t IH].
  - simpl in H. destruct l1 as [| h' t'].
    + simpl. exists []. exists []. reflexivity.
    + simpl in H. discriminate H.
  - simpl in H. apply split_orb_true in H. destruct H as [Hpre | Hsub].
    + exists []. simpl. apply prefix_breaks_down_list. apply Hpre.
    + apply IH in Hsub. destruct Hsub as [l2 [l3 H]].
      exists (h :: l2). exists l3. simpl. rewrite H. reflexivity. }
  { intros [l2 [l3 H]]. generalize dependent l3. generalize dependent l1. generalize dependent l2. induction l as [| h t IH].
  - intros l2 l1 l3 H. destruct l1 as [| h1 t1].
    + reflexivity.
    + simpl in H. destruct l2 as [| h2 t2]. simpl in H. discriminate H. discriminate H.
  - intros l2 l1 l3 H. destruct l1 as [| h1 t1].
    + reflexivity.
    + destruct l2 as [| h2 t2].
      * simpl in H.
        assert (Hpre: prefix (h1 :: t1) (h :: t) = true). { apply prefix_breaks_down_list. exists l3. apply H. }
        simpl. simpl in Hpre. rewrite Hpre. reflexivity.
      * specialize IH with (l2 := t2) (l1 := (h1 :: t1)) (l3 := l3).
        assert (Hsub: sublist (h1 :: t1) t = true). { apply IH. simpl in H. inversion H. reflexivity. }
        simpl. rewrite Hsub. rewrite orb_comm. reflexivity. }
Qed.

Lemma not_first_node_has_sublist: forall (a h v: nat) (t: list nat),
  (a =? h) = false /\ In a (t ++ [v])
  -> exists b : nat, sublist [b; a] (h :: t ++ [v]) = true.
Proof.
  intros a h v t [H1 H2]. generalize dependent h. induction t as [| h' t' IH].
  - intros h H1. exists h. simpl. simpl in H2. destruct H2 as [H2 | F].
    + rewrite H2. repeat rewrite eqb_refl. reflexivity.
    + exfalso. apply F.
  - intros h H1. simpl. destruct (a =? h') as [|] eqn:Ha.
    + exists h. rewrite eqb_refl. simpl. reflexivity.
    + simpl. assert (Hind: exists b : nat, sublist [b; a] (h' :: t' ++ [v]) = true).
      { apply IH. simpl in H2. destruct H2 as [F | H2].
        - rewrite F in Ha. rewrite eqb_refl in Ha. discriminate Ha.
        - apply H2.
        - apply Ha. }
      destruct Hind as [b Hb]. exists b. simpl in Hb. rewrite Hb. rewrite orb_comm. reflexivity.
Qed.


Lemma rearrange_list_concat_app: forall (l1 l2: list nat) (m v: nat),
  l1 ++ m :: l2 ++ [v] = (l1 ++ m :: l2) ++ [v].
Proof.
  intros l1 l2 m v. induction l1 as [| h1 t1].
  * simpl. reflexivity.
  * simpl. f_equal. apply IHt1.
Qed.

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

Lemma sublist_length_less: forall (l1 l2 l3: list nat) (len': nat),
  length l3 < S len' /\ l1 ++ l2 = l3 /\ ~(l1 = []) -> length l2 < len'.
Proof.
  intros l1 l2 l3 len'. intros [Hlen [Hl Hl1]].
  generalize dependent l1. generalize dependent l3. generalize dependent len'. induction l2 as [| h t IH].
  - intros len' l3 Hlen l1 Hl Hl1. simpl. destruct l1 as [| h1 t1].
    + exfalso. apply Hl1. reflexivity.
    + rewrite <- Hl in Hlen. simpl in Hlen. lia.
  - intros len' l3 Hlen l1 Hl Hl1. simpl.
    destruct len' as [| len''].
    + destruct l1 as [| h1 t1].
      * exfalso. apply Hl1. reflexivity.
      * rewrite <- Hl in Hlen. simpl in Hlen. lia.
    + destruct l1 as [| h1 t1].
      * exfalso. apply Hl1. reflexivity.
      * assert (length t < len'').
        { apply IH with (l1 := t1 ++ [h]) (l3 := t1 ++ h :: t).
          - rewrite <- Hl in Hlen. simpl in Hlen. lia.
          - rewrite <- app_assoc. simpl. reflexivity.
          - destruct t1 as [| h1' t1']. simpl. intros F. discriminate F. intros F. discriminate F. }
        lia.
Qed.

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

Lemma list_has_first_appearance_of_elt: forall (l: list nat) (x: nat),
  In x l -> exists (l1 l2: list nat), l = l1 ++ [x] ++ l2 /\ ~In x l1.
Proof.
  intros l x H.
  induction l as [| h t IH].
  - exfalso. apply H.
  - destruct (h =? x) as [|] eqn:Hhx.
    + apply eqb_eq in Hhx. exists []. exists t. split.
      * simpl. rewrite Hhx. reflexivity.
      * intros F. exfalso. apply F.
    + destruct H as [H | H]. rewrite H in Hhx. rewrite eqb_refl in Hhx. discriminate Hhx.
      apply IH in H. destruct H as [l1 [l2 H]]. exists (h :: l1). exists l2. split.
      * simpl. destruct H as [H _]. rewrite H. simpl. reflexivity.
      * intros [Hx | Hx]. rewrite Hx in Hhx. rewrite eqb_refl in Hhx. discriminate Hhx.
        apply H. apply Hx.
Qed.

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

Lemma middle_elt_of_sublist_not_last_elt: forall (l: list nat) (a b c: nat),
  sublist [a; b; c] (l ++ [b]) = true -> In b l.
Proof.
  intros l a b c H.
  induction l as [| h t IH].
  - simpl in H. rewrite orb_comm in H. simpl in H. rewrite andb_comm in H. simpl in H. discriminate H.
  - simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + destruct t as [| h' t'].
      * simpl in H. rewrite eqb_refl in H. simpl in H. rewrite andb_comm in H. discriminate H.
      * simpl in H. apply split_and_true in H. destruct H as [_ H]. apply split_and_true in H. destruct H as [H _].
        simpl. right. left. apply eqb_eq in H. rewrite H. reflexivity.
    + simpl. right. apply IH. apply H.
Qed.

Lemma first_elt_of_sublist_not_last_elt: forall (l: list nat) (a b c v: nat),
  sublist [a; b; c] (l ++ [v]) = true -> In a l.
Proof.
  intros l a b c v H.
  induction l as [| h t IH].
  - simpl in H. rewrite orb_comm in H. simpl in H. rewrite andb_comm in H. simpl in H. discriminate H.
  - simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + destruct t as [| h' t'].
      * simpl in H. rewrite andb_comm in H. rewrite <- andb_assoc in H. rewrite andb_comm in H. discriminate H.
      * simpl in H. apply split_and_true in H. destruct H as [H _]. left. apply eqb_eq in H. rewrite H. reflexivity.
    + simpl. right. apply IH. apply H.
Qed.

Lemma first_elt_of_sublist_not_last_elt_gen: forall (l t: list nat) (a b v: nat),
  sublist (a :: b :: t) (l ++ [v]) = true -> In a l.
Proof.
  intros l t a b v H.
  induction l as [| hl tl IH].
  - simpl in H. rewrite orb_comm in H. simpl in H. rewrite andb_comm in H. simpl in H. discriminate H.
  - simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + destruct t as [| h' t'].
      * simpl in H. rewrite andb_comm in H. apply split_and_true in H. left. destruct H as [_ H]. apply eqb_eq in H. rewrite H. reflexivity.
      * simpl in H. apply split_and_true in H. destruct H as [H _]. left. apply eqb_eq in H. rewrite H. reflexivity.
    + simpl. right. apply IH. apply H.
Qed.

Lemma middle_elt_of_sublist_not_first_elt: forall (l: list nat) (a b c: nat),
  sublist [a; b; c] (b :: l) = true -> In b l.
Proof.
  intros l a b c H.
  simpl in H.
  destruct l as [| h t].
  - simpl in H. rewrite orb_comm in H. simpl in H. rewrite andb_comm in H. simpl in H. discriminate H.
  - apply split_orb_true in H. destruct H as [H | H].
    + apply split_and_true in H. destruct H as [_ H]. apply split_and_true in H. destruct H as [H _].
      simpl. left. apply eqb_eq in H. rewrite H. reflexivity.
    + apply sublist_member with (l1 := [a; b; c]). split.
      * simpl. right. left. reflexivity.
      * apply H.
Qed.

Lemma middle_elt_of_sublist_not_first_elt_gen: forall (A t: list nat) (a b h: nat),
  sublist (a :: A) (h :: t) = true /\ In b A -> In b t.
Proof.
  intros A t a b h [H1 H2].
  generalize dependent h. induction t as [| hl tl IH].
  - intros h H1. simpl in H1. rewrite orb_comm in H1. simpl in H1. apply split_and_true in H1. destruct H1 as [_ H1].
    destruct A as [| ha ta]. apply H2. simpl in H1. discriminate H1.
  - intros h H1. simpl in H1. destruct ((a =? h) && prefix A (hl :: tl)) as [|] eqn:Hpre.
    + apply split_and_true in Hpre. destruct Hpre as [_ Hpre]. apply prefix_breaks_down_list in Hpre.
      apply membership_splits_list in H2. destruct H2 as [A1 [A2 HA]]. rewrite <- HA in Hpre. destruct Hpre as [t2 Ht].
      rewrite <- Ht. apply membership_append. apply membership_append_r. apply membership_append. left. reflexivity.
    + simpl in H1. right. apply IH with (h := hl). apply H1.
Qed.

Lemma index_of_sublist: forall (a b: nat) (i: nat) (l: list nat),
  sublist [b; a] l = true
  -> count a l = 1
  -> count b l = 1
  -> Some (S i) = index l a
  -> Some i = index l b.
Proof.
  intros a b i l. intros H1 Hc Hcb H2.
  generalize dependent i. induction l as [| h t IH].
  - simpl in H1. discriminate H1.
  - intros i H2. simpl in H2. destruct (h =? a) as [|] eqn:Hha. inversion H2.
    simpl in H1. destruct t as [| h' t'].
    + simpl in H1. rewrite andb_comm in H1. simpl in H1. discriminate H1.
    + destruct (a =? h') as [|] eqn:Hah.
      * simpl in H2. rewrite eqb_sym in Hah. rewrite Hah in H2. inversion H2. destruct (h =? b) as [|] eqn:Hhb.
        -- simpl. rewrite Hhb. reflexivity.
        -- rewrite eqb_sym in Hhb. rewrite Hhb in H1. simpl in H1.
           assert (In a t').
           { apply middle_elt_of_sublist_not_first_elt_gen with (A := [a]) (a := b) (h := h'). split. apply H1. left. reflexivity. }
           simpl in Hc. rewrite Hha in Hc. rewrite Hah in Hc. apply member_count_at_least_1 in H. lia.
      * destruct i as [|i'] eqn:Hi.
        -- rewrite eqb_sym in Hah. simpl in H2. rewrite Hah in H2. destruct (index t' a) as [j|]. inversion H2. discriminate H2.
        -- specialize IH with (i := i').
           assert (b =? h = false).
           { destruct (b =? h) as [|] eqn:Hbh.
             - simpl in H1. assert (In b (h' :: t')). { apply sublist_member with (l1 := [b; a]). split.
               + left. reflexivity.
               + apply H1. }
               simpl in Hcb. rewrite eqb_sym in Hbh. rewrite Hbh in Hcb. apply member_count_at_least_1 in H. simpl in H. lia.
             - reflexivity. }
           assert (Hind: Some i' = index (h' :: t') b).
           { apply IH.
             - rewrite andb_comm in H1. simpl in H1. apply H1.
             - simpl in Hc. rewrite Hha in Hc. apply Hc.
             - destruct (index (h' :: t') a) as [j|].
               + simpl in Hcb. rewrite eqb_sym in H. rewrite H in Hcb. apply Hcb.
               + inversion H2.
             - destruct (index (h' :: t') a) as [j|].
               + inversion H2. reflexivity.
               + discriminate H2. }
           simpl. rewrite eqb_sym in H. rewrite H. simpl in Hind. rewrite <- Hind. reflexivity.
Qed.

Lemma merge_two_sublists: forall (l: list nat) (a b x: nat),
  sublist [a; x] l = true
  -> sublist [b; a] l = true
  -> count a l = 1
  -> sublist [b; a; x] l = true.
Proof.
  intros l a b x Hx Hb Hc.
  induction l as [| h t IH].
  - simpl in Hx. discriminate Hx.
  - simpl in Hx.
    destruct (a =? h) as [|] eqn:Hah.
    + assert (Hat: In a t).
      { apply middle_elt_of_sublist_not_first_elt_gen with (A := [a]) (a := b) (h := h). split.
        - apply Hb.
        - left. reflexivity. }
      simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. apply member_count_at_least_1 in Hat. lia.
    + simpl in Hx. simpl in Hb. destruct (b =? h) as [|] eqn:Hbh.
      * destruct t as [| h' t'].
        -- simpl in Hb. discriminate Hb.
        -- simpl in Hb. destruct (a =? h') as [|] eqn:Hah'.
           ++ simpl in Hx. rewrite Hah' in Hx. destruct t' as [| h'' t''].
              ** simpl in Hx. discriminate Hx.
              ** destruct (x =? h'') as [|] eqn:Hxh''.
                 --- simpl. rewrite Hbh. rewrite Hah'. rewrite Hxh''. reflexivity.
                 --- assert (Ha: In a (h'' :: t'')).
                     { apply sublist_member with (l1 := [a; x]). split. left. reflexivity. simpl in Hx. apply Hx. }
                     simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. rewrite eqb_sym in Hah'. rewrite Hah' in Hc.
                     apply member_count_at_least_1 in Ha. simpl in Ha. lia.
           ++ simpl. apply split_orb_true. right. apply IH.
              ** apply Hx.
              ** apply Hb.
              ** simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. apply Hc.
      * simpl in Hb. simpl. apply split_orb_true. right. apply IH.
        -- apply Hx.
        -- apply Hb.
        -- simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. apply Hc.
Qed.

Lemma two_sublists_the_same: forall (l: list nat) (a b b': nat),
  sublist [a; b] l = true
  -> sublist [a; b'] l = true
  -> count a l = 1
  -> b = b'.
Proof.
  intros l a b b' Hb Hb' Hc.
  induction l as [| h t IH].
  - simpl in Hb. discriminate Hb.
  - simpl in Hb.
    destruct (a =? h) as [|] eqn:Hah.
    + destruct t as [| h' t'].
      * simpl in Hb. discriminate Hb.
      * destruct (b =? h') as [|] eqn:Hbh'.
        -- simpl in Hb'. rewrite Hah in Hb'. destruct (b' =? h') as [|] eqn:Hbh''.
           ++ apply eqb_eq in Hbh'. rewrite Hbh'. apply eqb_eq in Hbh''. rewrite Hbh''. reflexivity.
           ++ simpl in Hb'. assert (Ha: In a (h' :: t')). { apply sublist_member with (l1 := [a; b']). split. left. reflexivity. apply Hb'. }
              simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. apply member_count_at_least_1 in Ha. simpl in Ha. lia.
        -- simpl in Hb. assert (Ha: In a (h' :: t')). { apply sublist_member with (l1 := [a; b]). split. left. reflexivity. apply Hb. }
           simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. apply member_count_at_least_1 in Ha. simpl in Ha. lia.
    + simpl in Hb. simpl in Hb'. rewrite Hah in Hb'. simpl in Hb'. apply IH.
      * apply Hb.
      * apply Hb'.
      * simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. apply Hc.
Qed.

Lemma two_sublists_the_same_gen: forall (l l1 l1' l2 l2': list nat) (a: nat),
  l = l1 ++ [a] ++ l2
  -> l = l1' ++ [a] ++ l2'
  -> count a l = 1
  -> l2 = l2'.
Proof.
  intros l l1 l1' l2 l2' a Hl Hl' Hc.
  generalize dependent l1. generalize dependent l1'. induction l as [| h t IH].
  - intros l1' Hl' l1 Hl. simpl in Hc. discriminate Hc.
  - intros l1' Hl' l1 Hl. simpl in Hc.
    destruct l1' as [| hl1' tl1'].
    + simpl in Hl'. destruct l1 as [| hl1 tl1].
      * simpl in Hl. inversion Hl'. inversion Hl. rewrite <- H3. apply H1.
      * inversion Hl. inversion Hl'. rewrite H2 in Hc. rewrite eqb_refl in Hc.
        assert (In a t). { rewrite H1. apply membership_append_r. left. reflexivity. } apply member_count_at_least_1 in H. lia.
    + destruct l1 as [| hl1 tl1].
      * inversion Hl'. inversion Hl. rewrite H2 in Hc. rewrite eqb_refl in Hc.
        assert (In a t). { rewrite H1. apply membership_append_r. left. reflexivity. } apply member_count_at_least_1 in H. lia.
      * apply IH with (l1' := tl1') (l1 := tl1).
        -- destruct (h =? a) as [|] eqn:Hha. 
           ++ assert (In a t). { inversion Hl. apply membership_append_r. left. reflexivity. } apply member_count_at_least_1 in H. lia.
           ++ apply Hc.
        -- inversion Hl'. reflexivity.
        -- inversion Hl. reflexivity.
Qed.

Lemma sublist_rev: forall (l1 l2: list nat),
  sublist l1 l2 = true -> sublist (rev l1) (rev l2) = true.
Proof.
  intros l1 l2 H.
  apply sublist_breaks_down_list in H. destruct H as [A [B H]].
  apply sublist_breaks_down_list. exists (rev B). exists (rev A).
  rewrite <- reverse_list_append. rewrite <- reverse_list_append. f_equal. rewrite <- app_assoc. apply H.
Qed.

Lemma two_sublists_the_same_2: forall (l: list nat) (a b b': nat),
  sublist [b; a] l = true
  -> sublist [b'; a] l = true
  -> count a l = 1
  -> b = b'.
Proof.
  intros l a b b' Hb Hb' Hc.
  apply sublist_rev in Hb. simpl in Hb. apply sublist_rev in Hb'. simpl in Hb'.
  rewrite count_reverse in Hc.
  apply two_sublists_the_same with (l := rev l) (a := a).
  - apply Hb.
  - apply Hb'.
  - apply Hc.
Qed.

Lemma end_of_sublist_still_sublist: forall (a1 a a2 h v: nat) (t: list nat),
  sublist [a1; a; a2] (h :: t ++ [v]) = true
  -> sublist [a; a2] (t ++ [v]) = true.
Proof.
  intros a1 a a2 h v t H.
  simpl in H. destruct (a1 =? h) as [|] eqn:Ha1h.
  - destruct (match t ++ [v] with
    | [] => false
    | h2 :: t2 => (a =? h2) && match t2 with
                               | [] => false
                               | h3 :: _ => (a2 =? h3) && true
                               end
    end) as [|] eqn:H1.
    + destruct t as [| h' t'].
      * simpl in H1. rewrite andb_comm in H1. discriminate H1.
      * simpl. simpl in H1. rewrite H1. reflexivity.
    + simpl in H. apply sublist_breaks_down_list in H. destruct H as [l1 [l2 H]].
      apply sublist_breaks_down_list. exists (l1 ++ [a1]). exists l2. rewrite <- H. simpl. rewrite append_vs_concat. reflexivity.
  - simpl in H. apply sublist_breaks_down_list in H. destruct H as [l1 [l2 H]].
      apply sublist_breaks_down_list. exists (l1 ++ [a1]). exists l2. rewrite <- H. simpl. rewrite append_vs_concat. reflexivity.
Qed.

Lemma end_of_sublist_still_sublist_2: forall (a1 a a2 h v: nat) (t: list nat),
  sublist [a1; a; a2] (h :: t ++ [v]) = true
  -> sublist [a; a2] (h :: t ++ [v]) = true.
Proof.
  intros a1 a a2 h v t H.
  simpl in H. destruct (a1 =? h) as [|] eqn:Ha1h.
  - destruct (match t ++ [v] with
    | [] => false
    | h2 :: t2 => (a =? h2) && match t2 with
                               | [] => false
                               | h3 :: _ => (a2 =? h3) && true
                               end
    end) as [|] eqn:H1.
    + simpl. destruct t as [| h' t'].
      * simpl in H1. rewrite andb_comm in H1. discriminate H1.
      * simpl. simpl in H1. rewrite H1. rewrite orb_comm. simpl. reflexivity.
    + simpl in H. apply sublist_breaks_down_list in H. destruct H as [l1 [l2 H]].
      apply sublist_breaks_down_list. exists (h :: l1 ++ [a1]). exists l2. rewrite <- H. simpl. rewrite append_vs_concat. reflexivity.
  - simpl in H. apply sublist_breaks_down_list in H. destruct H as [l1 [l2 H]].
      apply sublist_breaks_down_list. exists (h :: l1 ++ [a1]). exists l2. rewrite <- H. simpl. rewrite append_vs_concat. reflexivity.
Qed.

Lemma end_of_sublist_still_sublist_gen: forall (a h: nat) (t l: list nat),
  sublist (a :: l) (h :: t) = true
  -> sublist l t = true.
Proof.
  intros a h t l H.
  generalize dependent h. induction t as [| h' t' IH].
  - intros h H. simpl in H. destruct (a =? h) as [|] eqn:Hah.
    + simpl in H. destruct l as [| hl tl]. simpl. reflexivity. simpl in H. discriminate H.
    + simpl in H. discriminate H.
  - intros h H. simpl in H. destruct ((a =? h) && prefix l (h' :: t')) as [|] eqn:H'.
    + apply split_and_true in H'. simpl. destruct H' as [_ H']. rewrite H'. reflexivity.
    + simpl in H. apply IH in H. simpl. rewrite H. rewrite orb_comm. reflexivity.
Qed.

Lemma start_of_sublist_still_sublist: forall (a w b: nat) (l: list nat),
  sublist [a; w; b] l = true
  -> sublist [a; w] l = true.
Proof.
  intros a w b l H.
  apply sublist_breaks_down_list in H. destruct H as [l1 [l2 H]].
  apply sublist_breaks_down_list. exists l1. exists (b :: l2). rewrite <- H. simpl. reflexivity.
Qed.


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

(* logic functions *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x' :: l' => P x' /\ (All P l')
  end.

Theorem demorgan : forall (P Q : Prop),
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  tauto.
Qed.

Theorem demorgan_and: forall (P Q : Prop),
  ~(P /\ Q) -> ~P \/ ~Q.
Proof.
  intros P Q H.
  unfold not in H.
  apply NNPP.
  intro contra.
  apply H.
  split.
  - apply NNPP.
    intros NP.
    apply contra.
    left. apply NP.
  - apply NNPP.
    intros NQ.
    apply contra.
    right. apply NQ.
Qed.

Theorem demorgan_many: forall (T: Type) (P: T -> Prop) (l : list T), ~(All P l) -> exists x: T, (In x l) /\ ~(P x).
Proof.
  intros T P l.
  intros H.
  induction l as [| h t IH].
  - unfold not in H. simpl in H. exfalso. apply H. apply I.
  - simpl in H. apply demorgan_and in H.
    destruct H as [H1 | H2].
    + exists h. simpl. split.
      * left. reflexivity.
      * apply H1.
    + apply IH in H2. destruct H2 as [x [HIn HP]].
      exists x. split.
      * simpl. right. apply HIn.
      * apply HP.
Qed.

Theorem demorgan_bool : forall (A B : bool), A || B = false <-> A = false /\ B = false.
Proof.
  intros A B. split.
  { intros H.
  destruct A as [|] eqn:HA.
  - simpl in H. discriminate H.
  - split. reflexivity. simpl in H. apply H. }
  { intros [H1 H2]. rewrite H1. simpl. apply H2. }
Qed.

Theorem demorgan_and_bool: forall (A B: bool), A && B = false 
  <-> A = false \/ B = false.
Proof.
  intros A B. split. 
  { intros H.
  destruct A as [|] eqn:HA.
  - simpl in H. right. apply H.
  - left. reflexivity. }
  { intros [H | H].
  - rewrite H. simpl. reflexivity.
  - rewrite andb_comm. rewrite H. reflexivity. }
Qed.


Theorem demorgan_many_bool: forall (T: Type) (P: T -> bool) (l : list T), forallb P l = false 
  <-> exists x: T, In x l /\ (P x = false).
Proof.
  intros T P l. split.
  { intros H.
  induction l as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. apply demorgan_and_bool in H. destruct H as [H | H].
    + exists h. simpl. split.
      * left. reflexivity.
      * apply H.
    + apply IH in H. destruct H as [x [HIn HP]].
      exists x. split.
      * simpl. right. apply HIn.
      * apply HP. }
  { intros [x [HIn HP]]. 
  induction l as [| h t IH].
  - simpl in HIn. exfalso. apply HIn.
  - simpl. simpl in HIn.
    destruct HIn as [Hhx | HIn].
    + rewrite Hhx. rewrite HP. simpl. reflexivity.
    + apply IH in HIn. rewrite HIn. rewrite andb_comm. simpl. reflexivity. }
Qed.

Theorem demorgan_many_bool_2: forall (T: Type) (P: T -> bool) (l : list T), (existsb P l = false)
  <-> (forall x: T, In x l -> (P x = false)).
Proof.
  intros T P l. split.
  { intros Hex x HIn.
  induction l as [| h t IH].
  - simpl in HIn. exfalso. apply HIn.
  - simpl in Hex. simpl in HIn. apply split_orb_false in Hex. destruct Hex as [H1 H2].
    destruct HIn as [Hhx | HIn].
    + rewrite <- Hhx. apply H1.
    + apply IH in H2. apply H2. apply HIn. }
  { intros H. induction l as [| h t IH].
    - simpl. reflexivity.
    - simpl in H. simpl. apply split_orb_false. split.
      + specialize (H h). apply H. left. reflexivity.
      + apply IH. intros x Hx. apply H. right. apply Hx. }
Qed.

Theorem example_usage :
  forall (T: Type) (P: T -> bool) (ls : list T), existsb P ls = false -> (forall x : T, In x ls -> P x = false).
Proof.
  intros T P ls H.
  (* Apply the lemma with explicit arguments *)
  destruct (demorgan_many_bool_2 T P ls) as [Hf Hb]. apply Hf. apply H.
Qed.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test.
  intros l.
  split.
  - intros H. induction l as [| h t IH].
    + simpl. apply I.
    + simpl. simpl in H.
      destruct (test h) as [|] eqn:Hh.
      * split. reflexivity. apply IH. apply H.
      * discriminate H.
  - intros H. induction l as [| h t IH].
    + simpl. reflexivity.
    + simpl. simpl in H.
      destruct H as [H1 H2].
      destruct (test h) as [|] eqn:Hh.
      * apply IH. apply H2.
      * apply H1.
Qed.

Theorem forallb_true_iff_mem : forall X test (l : list X),
  forallb test l = true <-> (forall x: X, In x l -> test x = true).
Proof.
  intros X test.
  intros l.
  split.
  - intros H. intros x Hmem. induction l as [| h t IH].
    + simpl in Hmem. exfalso. apply Hmem.
    + simpl in H. simpl in Hmem. destruct Hmem as [Hhx | Hmem].
      * apply split_and_true in H. destruct H as [H _]. rewrite Hhx in H. apply H.
      * apply IH.
        -- apply split_and_true in H. destruct H as [_ H]. apply H.
        -- apply Hmem.
  - intros H. induction l as [| h t IH].
    + simpl. reflexivity.
    + simpl. assert (Hh: test h = true).
      { specialize H with (x := h). apply H. simpl. left. reflexivity. }
      rewrite Hh. simpl. apply IH. intros x Hind.
      apply H. simpl. right. apply Hind.
Qed.

Theorem filter_true : forall (X : Type) (test : X -> bool) (x : X) (l: list X),
  In x (filter test l) <-> In x l /\ test x = true.
Proof.
  intros X test.
  intros x l.
  split.
  { induction l as [| h t IHt].
  - simpl. intros F. exfalso. apply F.
  - simpl. intros H.
    destruct (test h) as [|] eqn:Htesth.
    + simpl in H. destruct H as [H | H].
      * rewrite <- H. split.
        -- left. reflexivity.
        -- apply Htesth.
      * apply IHt in H. destruct H as [H1 H2]. split.
        -- right. apply H1.
        -- apply H2.
    + apply IHt in H. destruct H as [H1 H2]. split.
      * right. apply H1.
      * apply H2. }
  { intros [H1 H2]. induction l as [| h t IHt].
  - simpl in H1. exfalso. apply H1.
  - simpl. destruct (test h) as [|] eqn:Htesth.
    + simpl in H1. destruct H1 as [H1 | H1].
      * simpl. left. apply H1.
      * simpl. right. apply IHt. apply H1.
    + simpl in H1. destruct H1 as [H1 | H1].
      * rewrite H1 in Htesth. rewrite H2 in Htesth. discriminate Htesth.
      * apply IHt. apply H1. }
Qed.

Theorem forallb_true : forall (X : Type) (test : X -> bool) (x : X) (l: list X),
  In x l -> (forallb test l = true -> test x = true).
Proof.
  intros X test.
  intros x l. intros Hmem.
  induction l as [| h t IHt].
  - simpl in Hmem. exfalso. apply Hmem.
  - simpl. intros H.
    destruct (test h) as [|] eqn:Htesth.
    + simpl in H. simpl in Hmem. destruct Hmem as [H1 | H1].
      * rewrite <- H1. apply Htesth.
      * apply IHt. apply H1. apply H.
    + simpl in H. discriminate H.
Qed.


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


Lemma subset_identity: forall (l: list nat),
  subset l l = true.
Proof.
  unfold subset. intros l.
  apply forallb_true_iff_mem. intros x H. apply member_In_equiv. apply H.
Qed.

