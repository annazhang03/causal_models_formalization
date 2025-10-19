From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.

Definition assignment (X : Type) : Type := node * X.
Definition assignments (X : Type) : Type := list (assignment X).

Fixpoint is_assigned {X: Type} (A: assignments X) (u: node) : bool :=
  match A with
  | [] => false
  | h :: t => (u =? (fst h)) || is_assigned t u
  end.

Lemma is_assigned_app: forall X (A1 A2: assignments X) (u: node),
  is_assigned A1 u = true -> is_assigned (A1 ++ A2) u = true.
Proof.
  intros X A1 A2 u H. induction A1 as [| h t IH].
  - simpl in H. discriminate H.
  - simpl. simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + rewrite H. simpl. reflexivity.
    + apply IH in H. rewrite H. rewrite orb_comm. simpl. reflexivity.
Qed.

Lemma is_assigned_app2: forall X (A1 A2: assignments X) (u: node),
  is_assigned A2 u = true -> is_assigned (A1 ++ A2) u = true.
Proof.
  intros X A1 A2 u H. induction A1 as [| h t IH].
  - simpl. apply H.
  - simpl. rewrite IH. rewrite orb_comm. simpl. reflexivity.
Qed.

Lemma not_assigned_app: forall X (A1 A2: assignments X) (w: node),
  is_assigned A1 w = false /\ is_assigned A2 w = false -> is_assigned (A1 ++ A2) w = false.
Proof.
  intros X A1 A2 w [H1 H2].
  induction A1 as [| h t IH].
  - simpl. apply H2.
  - simpl. simpl in H1. apply split_orb_false in H1. destruct H1 as [Hwh H1].
    rewrite Hwh. simpl. apply IH. apply H1.
Qed.

Lemma is_assigned_membership: forall X (A: assignments X) (w: node),
  is_assigned A w = true <-> exists (x: X), In (w, x) A.
Proof.
  intros X A w. split.
  { intros H.
  induction A as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + simpl. destruct h as [h1 h2]. exists h2. left. simpl in H. apply eqb_eq in H. rewrite H. reflexivity.
    + apply IH in H. destruct H as [x H]. exists x. right. apply H. }
  { intros [x H].
  induction A as [| h t IH].
  - exfalso. apply H.
  - simpl in H. destruct H as [H | H].
    + simpl. rewrite H. simpl. rewrite eqb_refl. reflexivity.
    + apply IH in H. simpl. rewrite orb_comm. rewrite H. reflexivity. }
Qed.

Fixpoint get_assigned_value {X: Type} (A: assignments X) (u: node) : option X :=
  match A with
  | [] => None
  | h :: t => if ((fst h) =? u) then Some (snd h) else (get_assigned_value t u)
  end.

Lemma get_assigned_In: forall X (A: assignments X) (u: node) (x: X),
  get_assigned_value A u = Some x -> In (u, x) A.
Proof.
  intros X A u x H. induction A as [| h t IH].
  - simpl in H. discriminate H.
  - simpl. simpl in H. destruct (fst h =? u) as [|] eqn:Hu.
    + left. destruct h as [h1 h2]. simpl in Hu. apply eqb_eq in Hu. rewrite Hu. simpl in H. inversion H. reflexivity.
    + right. apply IH. apply H.
Qed.

Lemma get_assigned_app_None: forall X (A1 A2: assignments X) (u: node),
  get_assigned_value A1 u = None -> get_assigned_value (A1 ++ A2) u = get_assigned_value A2 u.
Proof.
  intros X A1 A2 u H. induction A1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. simpl in H. destruct (fst h =? u) as [|] eqn:Hhu.
    + discriminate H.
    + apply IH. apply H.
Qed.

Lemma get_assigned_app_Some: forall X (A1 A2: assignments X) (u: node) (x: X),
  get_assigned_value A1 u = Some x -> get_assigned_value (A1 ++ A2) u = Some x.
Proof.
  intros X A1 A2 u x H. induction A1 as [| h t IH].
  - simpl in H. discriminate H.
  - simpl. simpl in H. destruct (fst h =? u) as [|] eqn:Hhu.
    + apply H.
    + apply IH. apply H.
Qed.

Lemma get_assigned_app2: forall X (A1 A1' A2 A2': assignments X) (u: node),
  get_assigned_value A1 u = get_assigned_value A2 u
    /\ get_assigned_value A1' u = get_assigned_value A2' u
  -> get_assigned_value (A1 ++ A1') u = get_assigned_value (A2 ++ A2') u.
Proof.
  intros X A1 A1' A2 A2' u.
  intros [H H'].
  induction A1 as [| h t IH].
  - simpl in H. simpl. symmetry in H. apply get_assigned_app_None with (A1 := A2) (A2 := A2') in H.
    rewrite H. apply H'.
  - simpl in H. simpl. destruct (fst h =? u) as [|] eqn:Hhu.
    + symmetry in H. apply get_assigned_app_Some with (A1 := A2) (A2 := A2') in H.
      rewrite H. reflexivity.
    + apply IH. apply H.
Qed.

Definition is_assignment_for {X: Type} (A: assignments X) (Z: nodes) : bool :=
  (forallb (fun x: node => is_assigned A x) Z).

Lemma is_assignment_for_cat: forall X (A: assignments X) (u: node) (x: X) (V: nodes),
  is_assignment_for A V = true -> is_assignment_for ((u, x) :: A) V = true.
Proof.
  intros X A u x V H. induction V as [| h t IH].
  - simpl. reflexivity.
  - simpl in H. apply split_and_true in H. destruct H as [H1 H2].
    simpl. rewrite H1. rewrite orb_comm. simpl. apply IH. apply H2.
Qed.

Lemma is_assignment_for_app: forall X (A B: assignments X) (V: nodes),
  is_assignment_for A V = true -> is_assignment_for (A ++ B) V = true.
Proof.
  intros X A B V H. unfold is_assignment_for in H. unfold is_assignment_for.
  apply forallb_true_iff_mem. intros x Hmem.
  apply forallb_true with (x := x) in H.
  - apply is_assigned_app. apply H.
  - apply Hmem.
Qed.

Lemma is_assignment_for_app_r: forall X (A B: assignments X) (V: nodes),
  is_assignment_for B V = true -> is_assignment_for (A ++ B) V = true.
Proof.
  intros X A B V H. unfold is_assignment_for in H. unfold is_assignment_for.
  apply forallb_true_iff_mem. intros x Hmem.
  apply forallb_true with (x := x) in H.
  - apply is_assigned_app2. apply H.
  - apply Hmem.
Qed.

Lemma assigned_has_value: forall X (A: assignments X) (u: node) (L: nodes),
  In u L /\ is_assignment_for A L = true -> exists x: X, get_assigned_value A u = Some x.
Proof.
  intros X A u L [Hmem HA].
  unfold is_assignment_for in HA. apply forallb_true_iff_mem with (X := node) (x := u) in HA.
  - induction A as [| h t IH].
    + simpl in HA. discriminate HA.
    + simpl in HA. apply split_orb_true in HA. destruct HA as [Hu | Hind].
      * destruct h as [u1 x1]. exists x1. simpl in Hu. simpl.
        apply eqb_eq in Hu. rewrite Hu. rewrite eqb_refl. reflexivity.
      * apply IH in Hind. destruct Hind as [x Hind].
        simpl. destruct (fst h =? u) as [|] eqn:Hhu.
        -- exists (snd h). reflexivity.
        -- exists x. apply Hind.
  - apply Hmem.
Qed.

Lemma assigned_is_true: forall X (A: assignments X) (u: node),
  (exists x: X, get_assigned_value A u = Some x) <-> is_assigned A u = true.
Proof.
  intros X A u. split.
  { intros [x H].
  induction A as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. destruct (fst h =? u) as [|] eqn:Hhu.
    + simpl. apply eqb_eq in Hhu. rewrite Hhu. rewrite eqb_refl. simpl. reflexivity.
    + simpl. apply IH in H. rewrite H. rewrite orb_comm. simpl. reflexivity. }
  { intros H. induction A as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. destruct (u =? fst h) as [|] eqn:Hhu.
    + simpl. apply eqb_eq in Hhu. rewrite Hhu. rewrite eqb_refl. exists (snd h). reflexivity.
    + simpl in H. apply IH in H. simpl. rewrite eqb_sym. rewrite Hhu. apply H. }
Qed.

Lemma assigned_is_false: forall X (A: assignments X) (u: node),
  is_assigned A u = false <-> get_assigned_value A u = None.
Proof.
  intros X A u. split.
  { intros H. induction A as [| h t IH].
  - simpl. reflexivity.
  - simpl in H. destruct (u =? fst h) as [|] eqn:Huh.
    + simpl in H. discriminate H.
    + simpl. rewrite eqb_sym. rewrite Huh. apply IH.
      simpl in H. apply H. }
  { intros H. induction A as [| h t IH].
  - simpl. reflexivity.
  - simpl. simpl in H. destruct (fst h =? u) as [|] eqn:Hhu.
    + discriminate H.
    + rewrite eqb_sym. rewrite Hhu. simpl. apply IH. apply H. }
Qed.

Definition get_assignment_for {X: Type} (V: nodes) (a: X): assignments X :=
  map (fun u: node => (u, a)) V.

Lemma node_maps_to_assigned: forall X (V: nodes) (u: node) (a: X),
  In u V -> is_assigned (get_assignment_for V a) u = true.
Proof.
  intros X V u a H.
  induction V as [| h t IH].
  - simpl in H. exfalso. apply H.
  - simpl in H. destruct H as [H | H].
    + simpl. rewrite H. rewrite eqb_refl. simpl. reflexivity.
    + simpl. apply IH in H. rewrite H. rewrite orb_comm. simpl. reflexivity.
Qed.

Lemma node_maps_to_assigned_value: forall X (V: nodes) (u: node) (a: X),
  In u V -> get_assigned_value (get_assignment_for V a) u = Some a.
Proof.
  intros X V u a H.
  induction V as [| h t IH].
  - simpl in H. exfalso. apply H.
  - simpl in H. destruct (h =? u) as [|] eqn:Hhu.
    + simpl. rewrite Hhu. reflexivity.
    + simpl. rewrite Hhu. apply IH. destruct H as [H | H]. rewrite H in Hhu. rewrite eqb_refl in Hhu. discriminate Hhu.
      apply H.
Qed.

Lemma node_maps_to_unassigned: forall X (V: nodes) (u: node) (a: X),
  ~(In u V) -> is_assigned (get_assignment_for V a) u = false.
Proof.
  intros X V u a H. unfold not in H.
  induction V as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (u =? h) as [|] eqn:Huh.
    + simpl in H. exfalso. apply H. left. apply eqb_eq in Huh. symmetry. apply Huh.
    + simpl in H. simpl. apply IH. intros Hmem.
      apply H. right. apply Hmem.
Qed.

Lemma nodes_map_to_assignment: forall X (V: nodes) (a: X),
  is_assignment_for (get_assignment_for V a) V = true.
Proof.
  intros X V a.
  induction V as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite eqb_refl. simpl.
    unfold is_assignment_for. unfold is_assignment_for in IH.
    apply forallb_true_iff_mem. intros x Hmem.
    assert (H: is_assigned (get_assignment_for t a) x = true).
    { apply forallb_true with (x := x) in IH.
      - apply IH.
      - apply Hmem. }
    simpl. rewrite H. rewrite orb_comm. simpl. reflexivity.
Qed.

Definition is_exact_assignment_for {X: Type} (A: assignments X) (Z: nodes) : Prop :=
  is_assignment_for A Z = true /\ forall (u: node), member u Z = false -> is_assigned A u = false.

Lemma assigned_true_then_in_list: forall X (A: assignments X) (u: node) (L: nodes),
  is_assigned A u = true /\ is_exact_assignment_for A L -> In u L.
Proof.
  intros X A u L [Hu [HA Hf]].
  destruct (member u L) as [|] eqn:Hmem.
  - apply member_In_equiv. apply Hmem.
  - specialize Hf with (u := u). apply Hf in Hmem. rewrite Hmem in Hu. discriminate Hu.
Qed.

Lemma nodes_map_to_exact_assignment: forall X (V: nodes) (a: X),
  is_exact_assignment_for (get_assignment_for V a) V.
Proof.
  intros X V a.
  unfold is_exact_assignment_for. split.
  - apply nodes_map_to_assignment.
  - induction V as [| h t IH].
    + simpl. reflexivity.
    + simpl. intros u H. destruct (h =? u) as [|] eqn:Hhu.
      * discriminate H.
      * rewrite eqb_sym. rewrite Hhu. simpl. specialize IH with (u := u). apply IH. apply H.
Qed.

Definition remove_assignment_for {X: Type} (A: assignments X) (v: node): assignments X :=
  filter (fun x => negb (fst x =? v)) A.

Lemma exact_assignment_append {X: Type}: forall (A: assignments X) (Z: nodes) (v: node),
  is_exact_assignment_for A (Z ++ [v])
  -> ~(In v Z)
  -> is_exact_assignment_for (remove_assignment_for A v) Z.
Proof.
  intros A Z v H. unfold is_exact_assignment_for in H. destruct H as [HA Hu].
  unfold is_exact_assignment_for. split.
  - unfold is_assignment_for. apply forallb_true_iff_mem. intros x HxZ. unfold remove_assignment_for.
    unfold is_assignment_for in HA. apply forallb_true_iff_mem with (x := x) in HA.
    + apply assigned_is_true in HA. destruct HA as [a HA]. apply get_assigned_In in HA.
      apply is_assigned_membership. exists a. apply filter_true. split.
      * apply HA.
      * simpl. destruct (x =? v) as [|] eqn:Hxv.
        -- exfalso. apply H. apply eqb_eq in Hxv. rewrite Hxv in HxZ. apply HxZ.
        -- reflexivity.
    + apply membership_append. apply HxZ.
  - intros u HuZ.
    unfold remove_assignment_for. destruct (u =? v) as [|] eqn:Huv.
    + destruct (is_assigned (filter (fun x : nat * X => negb (fst x =? v)) A) u) as [|] eqn:Ha.
      * apply is_assigned_membership in Ha. destruct Ha as [a Ha]. apply filter_true in Ha. destruct Ha as [_ Ha]. simpl in Ha. rewrite Huv in Ha. discriminate Ha.
      * reflexivity.
    + assert (is_assigned A u = false). { apply Hu. destruct (member u (Z ++ [v])) as [|] eqn:Hmem.
      - apply member_In_equiv in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
        + apply member_In_equiv in Hmem. rewrite Hmem in HuZ. discriminate HuZ.
        + destruct Hmem as [Hmem | Hmem].
          * rewrite Hmem in Huv. rewrite eqb_refl in Huv. discriminate Huv.
          * exfalso. apply Hmem.
      - reflexivity. }
      destruct (is_assigned (filter (fun x : nat * X => negb (fst x =? v)) A) u) as [|] eqn:Ha.
      * apply is_assigned_membership in Ha. destruct Ha as [a Ha]. apply filter_true in Ha. destruct Ha as [Ha _].
        assert (is_assigned A u = true). { apply is_assigned_membership. exists a. apply Ha. } rewrite H1 in H0. discriminate H0.
      * reflexivity.
Qed.

Lemma remove_assignment_None {X: Type}: forall (A: assignments X) (u: node),
  get_assigned_value (remove_assignment_for A u) u = None.
Proof.
  intros A u.
  induction A as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (fst h =? u) as [|] eqn:Hhu.
    + unfold node in *. rewrite Hhu. simpl. apply IH.
    + unfold node in *. rewrite Hhu. simpl. unfold node in *. rewrite Hhu. apply IH.
Qed.

Lemma remove_assignment_preserves_other_nodes {X: Type}: forall (A: assignments X) (u x: node),
  u =? x = false
  -> get_assigned_value (remove_assignment_for A u) x = get_assigned_value A x.
Proof.
  intros A u x H.
  induction A as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (fst h =? u) as [|] eqn:Hhu.
    + unfold node in *. rewrite Hhu. simpl. destruct (fst h =? x) as [|] eqn:Hhx.
      * apply eqb_eq in Hhu. apply eqb_eq in Hhx. unfold node in *. rewrite Hhx in Hhu. rewrite Hhu in H. rewrite eqb_refl in H. discriminate H.
      * unfold node in *. rewrite Hhx. apply IH.
    + unfold node in *. rewrite Hhu. simpl. destruct (fst h =? x) as [|] eqn:Hhx.
      * unfold node in *. rewrite Hhx. reflexivity.
      * unfold node in *. rewrite Hhx. apply IH.
Qed.

Lemma remove_assignment_is_assignment_cat {X: Type}: forall (A: assignments X) (h u: node) (A': nodes) (c: X),
  is_assignment_for A (u :: A') = true
  -> ~(In u A')
  -> is_assignment_for ((h, c) :: remove_assignment_for A u) (h :: A') = true.
Proof.
  intros A h u A' c HA Hmem.
  simpl. rewrite eqb_refl. simpl. simpl in HA. apply split_and_true in HA. destruct HA as [_ HA].
  induction A' as [| ha ta IH].
  - simpl. reflexivity.
  - simpl. destruct (ha =? h) as [|] eqn:Hhah.
    + simpl. apply IH.
      * simpl in HA. apply split_and_true in HA. apply HA.
      * intros F. apply Hmem. right. apply F.
    + simpl. apply split_and_true. split.
      * apply assigned_is_true. rewrite remove_assignment_preserves_other_nodes.
        -- apply assigned_is_true. simpl in HA. apply split_and_true in HA. apply HA.
        -- destruct (u =? ha) as [|] eqn:Huha. exfalso. apply Hmem. left. apply eqb_eq in Huha. symmetry. apply Huha. reflexivity.
      * apply IH.
        -- simpl in HA. apply split_and_true in HA. apply HA.
        -- intros F. apply Hmem. right. apply F.
Qed.

Lemma remove_assignment_non_member_cat {X: Type}: forall (A: assignments X) (h u: node) (A': nodes) (c: X),
  (forall u0 : node, member u0 (u :: A') = false -> is_assigned A u0 = false)
  -> ~ In u A'
  -> forall u0 : node,
      member u0 (h :: A') = false ->
      is_assigned ((h, c) :: remove_assignment_for A u) u0 = false.
Proof.
  intros A h u A' c HA Hmem.
  intros v Hv. simpl in Hv. destruct (h =? v) as [|] eqn:Hhv.
  - discriminate Hv.
  - simpl. rewrite eqb_sym in Hhv. rewrite Hhv. simpl.
    destruct (v =? u) as [|] eqn:Hvu.
    + apply assigned_is_false. apply eqb_eq in Hvu. rewrite Hvu. apply remove_assignment_None.
    + apply assigned_is_false. rewrite remove_assignment_preserves_other_nodes.
      * apply assigned_is_false. apply HA. simpl. rewrite eqb_sym in Hvu. rewrite Hvu. apply Hv.
      * rewrite eqb_sym. apply Hvu.
Qed.


Lemma remove_assignment_exact_cat {X: Type}: forall (A: assignments X) (h u: node) (A': nodes) (c: X),
  is_exact_assignment_for A (u :: A')
  -> ~(In u A')
  -> is_exact_assignment_for ((h, c) :: remove_assignment_for A u) (h :: A').
Proof.
  intros A h u A' c H Hmem.
  unfold is_exact_assignment_for in *. destruct H as [H1 H2]. split.
  - apply remove_assignment_is_assignment_cat. apply H1. apply Hmem.
  - apply remove_assignment_non_member_cat. apply H2. apply Hmem.
Qed.

Lemma exact_assignment_cat {X: Type}: forall (A: assignments X) (u: node) (t: nodes) (c: X),
  is_exact_assignment_for A t -> is_exact_assignment_for ((u, c) :: A) (u :: t).
Proof.
  intros A u t c H. destruct H as [H1 H2]. split.
  - simpl. rewrite eqb_refl. simpl. apply is_assignment_for_cat. apply H1.
  - intros x Hmem. simpl. simpl in Hmem. destruct (u =? x) as [|] eqn:Hux. discriminate Hmem. rewrite eqb_sym. rewrite Hux. simpl.
    apply H2. apply Hmem.
Qed.

Definition add_assignment {X: Type} (A: assignments X) (u: node) (x: X) : assignments X :=
  A ++ [(u, x)].

Lemma filter_preserves_relative_index {X: Type}: forall (test: (node * X) -> bool) (V: assignments X) (h: node * X) (i: nat),
  nth_error (filter test V) i = Some h -> exists (j: nat), nth_error V j = Some h /\ j >= i.
Proof.
  intros test V h i. intros Hi.
  generalize dependent i. induction V as [| hv tv IH].
  - intros i Hi. simpl in Hi. destruct i as [| i']. simpl in Hi. discriminate Hi. simpl in Hi. discriminate Hi.
  - intros i Hi. simpl in Hi. destruct (test hv) as [|] eqn:Hhv.
    + destruct i as [| i'].
      * simpl in Hi. exists 0. simpl. split. apply Hi. lia.
      * simpl in Hi. apply IH in Hi. destruct Hi as [j [Hj Hji]]. exists (S j).
        split.
        -- simpl. apply Hj.
        -- lia.
    + apply IH in Hi. destruct Hi as [j [Hj Hji]]. exists (S j). split.
      * simpl. apply Hj.
      * lia.
Qed.

Lemma filter_preserves_relative_index_2 {X: Type}: forall (test: (node * X) -> bool) (V t': assignments X) (h h': node * X),
  filter test V = h :: h' :: t' -> exists (i j: nat), nth_error V i = Some h /\ nth_error V j = Some h' /\ i =? j = false.
Proof.
  intros test V t' h h'. intros Hf.
  generalize dependent h. generalize dependent h'. generalize dependent t'. induction V as [| hv tv IH].
  - intros t' h' h Hf. simpl in Hf. discriminate Hf.
  - intros t' h' h Hf. simpl in Hf. destruct (test hv) as [|] eqn:Htest.
    + inversion Hf. exists 0.
      destruct t' as [| ht tt].
      * assert (In h' (filter test tv)). { rewrite H1. left. reflexivity. }
        apply In_nth_error in H. destruct H as [j Hj]. apply filter_preserves_relative_index in Hj. destruct Hj as [j' [Hj' Hjj]].
        exists (S j'). repeat split. simpl. apply Hj'.
      * specialize IH with (t' :=  tt) (h' := ht) (h := h'). apply IH in H1.
        destruct H1 as [j [k [Hj [Hk Hjk]]]].
        exists (S j). repeat split. simpl. apply Hj.
    + apply IH in Hf. destruct Hf as [i [j [Hi [Hj Hij]]]]. exists (S i). exists (S j). repeat split.
      * simpl. apply Hi.
      * simpl. apply Hj.
      * destruct (S i =? S j) as [|] eqn:HSij.
        -- apply eqb_eq in HSij. inversion HSij. rewrite H0 in Hij. rewrite eqb_refl in Hij. discriminate Hij.
        -- reflexivity.
Qed.

Lemma nth_error_get_assigned_value {X: Type}: forall (V: assignments X) (u: node) (x: X) (i: nat),
  nth_error V i = Some (u, x) /\ length (filter (fun x : nat * X => fst x =? u) V) = 1
  -> get_assigned_value V u = Some x.
Proof.
  intros V u x i. intros [Hi Hl].
  generalize dependent i. induction V as [| h t IH].
  - intros i Hi. destruct i as [| i']. simpl in Hi. discriminate Hi. simpl in Hi. discriminate Hi.
  - intros i Hi. destruct i as [| i']. 
    + simpl in Hi. inversion Hi. simpl. rewrite eqb_refl. reflexivity.
    + simpl in Hi. simpl in Hl. destruct (fst h =? u) as [|] eqn:Hhu.
      * unfold node in *. rewrite Hhu in Hl. simpl in Hl. inversion Hl.
        assert (F: In (u, x) (filter (fun x : nat * X => fst x =? u) t)).
        { apply filter_true. split.
          - apply nth_error_In in Hi. apply Hi.
          - simpl. apply eqb_refl. }
        destruct (filter (fun x : nat * X => fst x =? u) t) as [| hf tf]. exfalso. apply F. simpl in H0. lia.
      * unfold node in *. rewrite Hhu in Hl. simpl. unfold node in *. rewrite Hhu. apply IH with (i := i').
        -- apply Hl.
        -- apply Hi.
Qed.


Lemma first_n_preserves_index {X: Type}: forall (V V': assignments X) (i j: nat) (p: node) (x: X),
  first_n V i = Some V'
  -> nth_error V j = Some (p, x)
  -> j < i
  -> nth_error V' j = Some (p, x).
Proof.
  intros V V' i j p x. intros HV' Hj Hji.
  generalize dependent V. generalize dependent j. generalize dependent V'. induction i as [| i' IH].
  - lia.
  - intros V' j Hji V HV' Hj. destruct V as [| h t].
    + simpl in HV'. discriminate HV'.
    + simpl in HV'. destruct (first_n t i') as [r|] eqn:Hr.
      * destruct j as [| j'].
        -- inversion HV'. simpl. simpl in Hj. apply Hj.
        -- specialize IH with (j := j') (V := t) (V' := r). inversion HV'. simpl. apply IH.
           ++ lia.
           ++ apply Hr.
           ++ simpl in Hj. apply Hj.
      * discriminate HV'.
Qed.

Lemma first_n_filter_length {X: Type}: forall (V V': assignments X) (test: node * X -> bool) (i: nat),
  first_n V i = Some V'
  -> length (filter test V) >= length (filter test V').
Proof.
  intros V V' test i. intros Hi.
  generalize dependent V'. generalize dependent i. induction V as [| h t IH].
  - intros i V' Hi. simpl in Hi. destruct i as [|i'].
    + inversion Hi. simpl. lia.
    + discriminate Hi.
  - intros i V' Hi. simpl. destruct (test h) as [|] eqn:Htest.
    + simpl in Hi. destruct i as [| i'].
      * inversion Hi. simpl. lia.
      * destruct (first_n t i') as [r|] eqn:Hr.
        -- specialize IH with (i := i') (V' := r). apply IH in Hr. inversion Hi. simpl. rewrite Htest. simpl. lia.
        -- discriminate Hi.
    + simpl in Hi. destruct i as [| i'].
      * inversion Hi. simpl. lia.
      * destruct (first_n t i') as [r|] eqn:Hr.
        -- inversion Hi. simpl. rewrite Htest. apply IH with (i := i') (V' := r). apply Hr.
        -- discriminate Hi.
Qed.