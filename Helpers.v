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

Theorem append_identity: forall l: list nat, l ++ [] = l.
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

Fixpoint fsts (l: list (nat * nat)) : list nat :=
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

Lemma split_and_true : forall a b, a && b = true -> a = true /\ b = true.
Proof.
  intros a b H.
  split.
  - apply andb_true_elim2 in H. apply H.
  - rewrite andb_comm in H. apply andb_true_elim2 in H. apply H.
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

