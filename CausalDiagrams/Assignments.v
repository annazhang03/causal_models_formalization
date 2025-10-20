From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.
From Utils Require Import EqType.


Definition assignment (X : Type) : Type := node * X.
Definition assignments (X : Type) : Type := list (assignment X).

Fixpoint eqb_asmt {X: Type} `{EqType X} (l1 l2: assignments X): bool :=
  match l1 with
  | [] => match l2 with
          | [] => true
          | h :: t => false
          end
  | h1 :: t1 => match l2 with
                | [] => false
                | h2 :: t2 => (fst h1 =? fst h2) && eqb (snd h1) (snd h2) && eqb_asmt t1 t2
                end
  end.

Lemma eqb_asmt_refl {X: Type} `{EqType X}: forall (l: assignments X),
  eqb_asmt l l = true.
Proof.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite eqb_refl. simpl. rewrite eqb_refl'. simpl. apply IH.
Qed.

Lemma eqb_asmt_eq {X: Type} `{EqType X}: forall (U1 U2: assignments X),
  eqb_asmt U1 U2 = true
  <-> U1 = U2.
Proof.
  intros U1 U2. split.
  { intros Heq.
    generalize dependent U2. induction U1 as [| h t IH].
    - intros U2 Heq. destruct U2 as [| h2 t2]. reflexivity. simpl in Heq. discriminate Heq.
    - intros U2 Heq. destruct U2 as [| h2 t2]. simpl in Heq. discriminate Heq.
      simpl in Heq. apply split_and_true in Heq. destruct Heq as [Hh Heq].
      assert (Hhh2: h = h2). { destruct h as [x1 y1]. destruct h2 as [x2 y2]. simpl in Hh. apply split_and_true in Hh. destruct Hh as [Hx Hy].
        apply eqb_eq' in Hy. rewrite Hy. apply eqb_eq in Hx. rewrite Hx. reflexivity. }
      rewrite Hhh2. f_equal. apply IH. apply Heq. }
  { intros Heq.
    generalize dependent U2. induction U1 as [| h t IH].
    - intros U2 Heq. rewrite <- Heq. simpl. reflexivity.
    - intros U2 Heq. destruct U2 as [| h2 t2]. simpl in Heq. discriminate Heq.
      inversion Heq. apply eqb_asmt_refl. }
Qed.

Lemma eqb_asmt_sym {X: Type} `{EqType X}: forall (U1 U2: assignments X),
  eqb_asmt U1 U2 = eqb_asmt U2 U1.
Proof.
  intros U1 U2.
  generalize dependent U2. induction U1 as [| h t IH].
  - intros U2. destruct U2 as [| h2 t2]. reflexivity. simpl. reflexivity.
  - intros U2. destruct U2 as [| h2 t2]. reflexivity. simpl.
    rewrite eqb_sym. rewrite eqb_sym'. rewrite IH. reflexivity.
Qed.

Instance EqType_asmt {X : Type} `{EqType X} : EqType (assignments X) := {
  eqb := eqb_asmt;
  eqb_refl' := eqb_asmt_refl;
  eqb_sym' := eqb_asmt_sym;
  eqb_eq' := eqb_asmt_eq
}.




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

Lemma is_assigned_iff_cat {X: Type}: forall (U: assignments X) (u w: node) (x: X),
  is_assigned U u = true
  -> is_assigned U w = true <-> is_assigned ((u, x) :: U) w = true.
Proof.
  intros U u w x Hu. split.
  - intros H. simpl. rewrite H. rewrite orb_comm. reflexivity.
  - intros H. simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + apply eqb_eq in H. rewrite H. apply Hu.
    + apply H.
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

Definition each_node_assigned_once {X: Type} (A: assignments X): Prop :=
  forall (u: node), is_assigned A u = true -> length (filter (fun (x: node * X) => (fst x) =? u) A) = 1.

Lemma each_node_assigned_once_cat {X: Type}: forall (A: assignments X) (u: node) (i: X),
  each_node_assigned_once ((u, i) :: A)
  -> each_node_assigned_once A.
Proof.
  intros A u i H.
  induction A as [| h t IH].
  - unfold each_node_assigned_once in *. intros w Hw. simpl in Hw. discriminate Hw.
  - unfold each_node_assigned_once in *. intros w Hw. simpl in Hw. destruct (w =? fst h) as [|] eqn:Hwh.
    + specialize H with (u := w). assert (Hl: length (filter (fun x : node * X => fst x =? w) ((u, i) :: h :: t)) = 1).
      { apply H. simpl. rewrite Hwh. rewrite orb_comm. reflexivity. }
      simpl. rewrite eqb_sym. rewrite Hwh. simpl. f_equal. simpl in Hl. destruct (u =? w) as [|] eqn:Huw. rewrite eqb_sym in Hl. rewrite Hwh in Hl.
      simpl in Hl. lia. rewrite eqb_sym in Hl. rewrite Hwh in Hl. simpl in Hl. inversion Hl. reflexivity.
    + simpl in Hw. simpl. rewrite eqb_sym. rewrite Hwh. apply IH.
      2: { apply Hw. }
      intros w' Hw'. simpl. simpl in Hw'. destruct (w' =? u) as [|] eqn:Huw.
      * rewrite eqb_sym in Huw. rewrite Huw.
        specialize H with (u := w'). assert (Hl: length (filter (fun x : node * X => fst x =? w') ((u, i) :: h :: t)) = 1).
        { apply H. simpl. rewrite eqb_sym. rewrite Huw. reflexivity. }
        simpl in Hl. rewrite Huw in Hl. destruct (fst h =? w') as [|] eqn:Hhw'. discriminate Hl. apply Hl.
      * simpl in Hw'. rewrite eqb_sym in Huw. rewrite Huw.
        specialize H with (u := w'). assert (Hl: length (filter (fun x : node * X => fst x =? w') ((u, i) :: h :: t)) = 1).
        { apply H. simpl. rewrite Hw'. rewrite orb_assoc. rewrite orb_comm. reflexivity. }
        simpl in Hl. rewrite Huw in Hl. destruct (fst h =? w') as [|] eqn:Hhw'. 2: { apply Hl. }
        simpl in Hl. inversion Hl. exfalso.
        clear IH. clear H. clear Hl. clear Hhw'. clear Huw. clear Hwh. clear Hw. induction t as [| h' t'].
        -- simpl in Hw'. discriminate Hw'.
        -- simpl in Hw'. destruct (w' =? fst h') as [|] eqn:Hw''.
           ++ simpl in H1. rewrite eqb_sym in Hw''. rewrite Hw'' in H1. simpl in H1. lia.
           ++ apply IHt'. simpl in Hw'. apply Hw'. simpl in H1. rewrite eqb_sym in Hw''. rewrite Hw'' in H1. apply H1.
Qed.

Lemma each_node_assigned_once_remove {X: Type}: forall (A: assignments X) (u: node),
  each_node_assigned_once A
  -> each_node_assigned_once (remove_assignment_for A u).
Proof.
  intros A u H.
  induction A as [| h t IH].
  - unfold each_node_assigned_once in *. intros w Hw. simpl in Hw. discriminate Hw.
  - unfold each_node_assigned_once. intros w Hw. simpl. destruct (fst h =? u) as [|] eqn:Hhu.
    + unfold nodes in *. unfold node in *. rewrite Hhu. simpl. apply IH.
      * destruct h as [h1 h2]. apply each_node_assigned_once_cat in H. apply H.
      * simpl in Hw. rewrite Hhu in Hw. simpl in Hw. apply Hw.
    + unfold nodes in *. unfold node in *. rewrite Hhu. simpl. destruct (fst h =? w) as [|] eqn:Hhw.
      * unfold nodes in *. unfold node in *. rewrite Hhw.
        unfold each_node_assigned_once in H. specialize H with (u := w). simpl in H. unfold nodes in *. unfold node in *. rewrite Hhw in H.
        simpl. f_equal.
        assert (Hl: length (h :: filter (fun x : nat * X => fst x =? w) t) = 1).
        { apply H. rewrite eqb_sym. rewrite Hhw. reflexivity. }
        simpl in Hl.
        destruct (filter (fun x : nat * X => fst x =? w) (remove_assignment_for t u)) as [| h' t'] eqn:Hf.
        -- simpl. reflexivity.
        -- exfalso. inversion Hl.
           assert (Hh': In h' (filter (fun x : nat * X => fst x =? w)
       (remove_assignment_for t u))). { rewrite Hf. left. reflexivity. }
           apply filter_true in Hh'.
           assert (Hh'': In h' (filter (fun x : nat * X => fst x =? w) t)).
           { apply filter_true. split.
             - destruct Hh' as [Hh' _]. apply filter_true in Hh'. apply Hh'.
             - apply Hh'. }
           destruct (filter (fun x : nat * X => fst x =? w) t) as [| h'' t'']. apply Hh''. discriminate Hl.
      * unfold nodes in *. unfold node in *. rewrite Hhw. assert (Hind: each_node_assigned_once (remove_assignment_for t u)).
        { apply IH. destruct h as [h1 h2]. apply each_node_assigned_once_cat with (u := h1) (i := h2). apply H. }
        unfold each_node_assigned_once in Hind. apply Hind. simpl in Hw. rewrite Hhu in Hw. simpl in Hw. rewrite eqb_sym in Hhw.
        unfold nodes in *. unfold node in *. rewrite Hhw in Hw. apply Hw.
Qed.

Lemma each_node_assigned_once_eq {X: Type}: forall (A: assignments X) (u: node) (i j: X),
  In (u, i) A
  -> In (u, j) A
  -> each_node_assigned_once A
  -> i = j.
Proof.
  intros A u i j. intros Hi Hj HA.
  induction A as [| h t IH].
  - exfalso. apply Hi.
  - destruct Hi as [Hi | Hi].
    + destruct Hj as [Hj | Hj].
      * rewrite Hi in Hj. inversion Hj. reflexivity.
      * unfold each_node_assigned_once in HA. specialize HA with (u := u). 
        assert (Hc: length (filter (fun x : node * X => fst x =? u) (h :: t)) = 1).
        { apply HA. simpl. rewrite Hi. simpl. rewrite eqb_refl. reflexivity. }
        simpl in Hc. rewrite Hi in Hc. simpl in Hc. rewrite eqb_refl in Hc. simpl in Hc. inversion Hc.
        assert (Hf: In (u, j) (filter (fun x : node * X => fst x =? u) t)).
        { apply filter_true. split. apply Hj. simpl. apply eqb_refl. }
        destruct (filter (fun x : node * X => fst x =? u) t) as [| h' t']. exfalso. apply Hf. discriminate H0.
    + destruct Hj as [Hj | Hj].
      * unfold each_node_assigned_once in HA. specialize HA with (u := u). 
        assert (Hc: length (filter (fun x : node * X => fst x =? u) (h :: t)) = 1).
        { apply HA. simpl. rewrite Hj. simpl. rewrite eqb_refl. reflexivity. }
        simpl in Hc. rewrite Hj in Hc. simpl in Hc. rewrite eqb_refl in Hc. simpl in Hc. inversion Hc.
        assert (Hf: In (u, i) (filter (fun x : node * X => fst x =? u) t)).
        { apply filter_true. split. apply Hi. simpl. apply eqb_refl. }
        destruct (filter (fun x : node * X => fst x =? u) t) as [| h' t']. exfalso. apply Hf. discriminate H0.
      * apply IH. apply Hi. apply Hj. apply each_node_assigned_once_cat with (u := fst h) (i := snd h). destruct h as [h1 h2]. apply HA.
Qed.

Lemma exact_assignment_assigns_once {X: Type}: forall (Z: nodes) (x: X),
  each_node_appears_once Z -> each_node_assigned_once (get_assignment_for Z x).
Proof.
  intros Z x HZ.
  induction Z as [| h t IH].
  - simpl. unfold each_node_assigned_once. intros u F. simpl in F. discriminate F.
  - unfold each_node_assigned_once. intros u Hu. simpl.
    destruct (h =? u) as [|] eqn:Hhu.
    + unfold each_node_appears_once in HZ. specialize HZ with (u := h). simpl in HZ. rewrite eqb_refl in HZ.
      assert (S (count h t) = 1). { apply HZ. left. reflexivity. } inversion H.
      simpl. f_equal. rewrite H1.
      destruct (member h t) as [|] eqn:Hmem.
      * apply member_In_equiv in Hmem. apply member_count_at_least_1 in Hmem. rewrite H1 in Hmem. lia.
      * rewrite length_0_list_empty.
        assert (Hmem': ~(In h t)). { intros Hmem'. apply member_In_equiv in Hmem'. rewrite Hmem in Hmem'. discriminate Hmem'. }
        apply node_maps_to_unassigned with (X := X) (a := x) in Hmem'.
        destruct (filter (fun x0 : node * X => fst x0 =? u) (get_assignment_for t x)) as [| [h' x'] t'] eqn:Hfil.
        -- reflexivity.
        -- assert (Hh: is_assigned (get_assignment_for t x) h = true).
           { apply is_assigned_membership. exists x'.
             assert (In (h', x') (filter (fun x0 : node * X => fst x0 =? u) (get_assignment_for t x))). { rewrite Hfil. left. reflexivity. }
             apply filter_In in H0. destruct H0 as [H0 H2]. simpl in H2. apply eqb_eq in H2. apply eqb_eq in Hhu. rewrite <- Hhu in H2.
             rewrite H2 in H0. apply H0. }
           rewrite Hh in Hmem'. discriminate Hmem'.
    + pose proof HZ as HZ'. unfold each_node_appears_once in HZ. specialize HZ with (u := u). simpl in HZ. rewrite Hhu in HZ.
      apply IH.
      * unfold each_node_appears_once. intros v Hv. assert (h =? v = false). { apply first_node_appears_once with (Z := t). split. apply HZ'. apply Hv. }
        unfold each_node_appears_once in HZ'. specialize HZ' with (u := v). simpl in HZ'. rewrite H in HZ'. apply HZ'. right. apply Hv.
      * simpl in Hu. rewrite eqb_sym in Hu. rewrite Hhu in Hu. simpl in Hu. apply Hu.
Qed.


(* U and U' assign the same nodes, and only the assignments for nodes in S can change *)
Definition assignments_change_only_for_subset {X: Type} (U U': assignments X) (S: nodes): Prop :=
  forall (x: node), (is_assigned U x = true <-> is_assigned U' x = true)
  /\ (~(In x S) -> get_assigned_value U x = get_assigned_value U' x).

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

Lemma first_n_exists {X: Type}: forall (V: assignments X) (i: nat),
  i < length V
  -> exists V' : assignments X, first_n V i = Some V'.
Proof.
  intros V i H.
  generalize dependent i. induction V as [| h t IH].
  - intros i H. destruct i as [| i'].
    + simpl in H. lia.
    + simpl in H. lia.
  - intros i H. destruct i as [| i'].
    + simpl. exists []. reflexivity.
    + assert (Hind: exists V' : assignments X, first_n t i' = Some V').
      { apply IH. simpl in H. lia. }
      destruct Hind as [V' Hind]. exists (h :: V'). simpl. rewrite Hind. reflexivity.
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

Definition assignments_equiv {X: Type} (U U': assignments X): Prop :=
  forall (u: node), get_assigned_value U u = get_assigned_value U' u.

Fixpoint list_assignments_equiv {X: Type} (L L': list (assignments X)): Prop :=
  match L with
  | [] => match L' with
          | [] => True
          | h :: t => False
          end
  | h :: t => match L' with
              | [] => False
              | h' :: t' => assignments_equiv h h' /\ list_assignments_equiv t t'
              end
  end.

Lemma list_assignments_equiv_identity {X: Type}: forall (L: list (assignments X)),
  list_assignments_equiv L L.
Proof.
  induction L as [| h t IH].
  - simpl. apply I.
  - simpl. split.
    + unfold assignments_equiv. reflexivity.
    + apply IH.
Qed.

Lemma assignments_equiv_symmetry {X: Type}: forall (U U': assignments X),
  assignments_equiv U U'
  -> assignments_equiv U' U.
Proof.
  intros U U' H.
  unfold assignments_equiv in *. intros u. symmetry. apply H.
Qed.

Lemma list_assignments_equiv_symmetry {X: Type}: forall (L L': list (assignments X)),
  list_assignments_equiv L L'
  -> list_assignments_equiv L' L.
Proof.
  intros L L' H.
  generalize dependent L'. induction L as [| h t IH].
  - intros L' H. simpl in H. destruct L' as [| h' t']. simpl. apply I.
    exfalso. apply H.
  - intros L' H. destruct L' as [| h' t']. simpl in H. exfalso. apply H.
    simpl in H. simpl. split.
    + apply assignments_equiv_symmetry. apply H.
    + apply IH. apply H.
Qed.

Lemma equiv_list_assignments_length {X: Type}: forall (L L': list (assignments X)),
  list_assignments_equiv L L'
  ->
  length L = length L'.
Proof.
  intros L L' H.
  generalize dependent L'. induction L as [| h t IH].
  - intros L' H. destruct L' as [| h' t'].
    + simpl. lia.
    + simpl in H. exfalso. apply H.
  - intros L' H. simpl in H. destruct L' as [| h' t'].
    + exfalso. apply H.
    + simpl. f_equal. apply IH. apply H.
Qed.

Lemma equiv_assignment_still_assignment {X: Type}: forall (U U': assignments X) (L: nodes),
  assignments_equiv U' U
  -> is_assignment_for U L = true
  -> is_assignment_for U' L = true.
Proof.
  intros U U' L H1 H2.
  induction L as [| h t IH].
  - simpl. reflexivity.
  - simpl. apply split_and_true. split.
    + simpl in H2. apply split_and_true in H2. unfold assignments_equiv in H1. destruct H2 as [H2 H3].
      apply assigned_is_true in H2. destruct H2 as [x' H2]. specialize H1 with (u := h). rewrite H2 in H1.
      apply assigned_is_true. exists x'. apply H1.
    + apply IH. simpl in H2. apply split_and_true in H2. apply H2.
Qed.

Lemma equiv_assignments_assigned {X: Type}: forall (U U': assignments X) (u: node),
  assignments_equiv U' U
  -> is_assigned U' u = is_assigned U u.
Proof.
  intros U U' u H.
  unfold assignments_equiv in H. specialize H with (u := u).
  destruct (is_assigned U u) as [|] eqn:HU.
  - apply assigned_is_true in HU. destruct HU as [x HU]. rewrite HU in H. apply assigned_is_true. exists x. apply H.
  - apply assigned_is_false. apply assigned_is_false in HU. rewrite HU in H. apply H.
Qed.

Lemma list_equiv_assignment_still_assignment {X: Type}: forall (L L': list (assignments X)) (N: nodes),
  list_assignments_equiv L L'
  -> (forall (U: assignments X), In U L' -> is_assignment_for U N = true)
  -> forall (U: assignments X), In U L
  -> is_assignment_for U N = true.
Proof.
  intros L L' N Heq HL' U HL.
  generalize dependent L'. induction L as [| h t IH].
  - intros L' Heq HL'. exfalso. apply HL.
  - intros L' Heq HL'. simpl in Heq. destruct L' as [| h' t'].
    + exfalso. apply Heq.
    + destruct HL as [HL | HL].
      * apply equiv_assignment_still_assignment with (U := h'). rewrite <- HL. apply Heq. apply HL'. left. reflexivity.
      * apply IH with (L' := t'). apply HL. apply Heq. intros U' HU'. apply HL'. right. apply HU'.
Qed.
