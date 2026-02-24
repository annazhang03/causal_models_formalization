From CausalDiagrams Require Import Assignments.
From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import DSeparation.
From CausalDiagrams Require Import CausalPaths.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.

Import ListNotations.

(* In this file, we explore the descendants of colliders along a path. In d-connectedness, the concept of
   these descendants is very important because every collider along a path must have some descendant (possibly
   the collider itself)
   in the conditioning set. Thus, collider descendants are also very important in our semantics for
   understanding when two nodes are independent of each other. *)


(* This function is used in the context of d-connected paths, where each collider has at least one path
   of descendants, ending at a descendant that is conditioned on.
   Assume D is of the form {col1: ([d1, d2, ..., d_l], d_l), col2: ...}, mapping collider to one of these descendant paths,
   where d_l is the descendant in the conditioning set.
   The descendant path [d1, d2, ...] does not include the collider itself; it is the nodes along the path in
   the order they appear. If the collider itself is conditioned on, then D maps {col1: ([], col1)}
   This function returns all descendants of all colliders in one flattened list *)
Fixpoint get_collider_descendants_from_assignments (D: assignments (nodes * node)) (col: nodes): option nodes :=
  match col with
  | [] => Some []
  | h :: t => match (get_assigned_value D h) with
              | Some x => match (get_collider_descendants_from_assignments D t) with
                          | Some r => if (snd x =? h) then Some r else Some ((fst x) ++ (snd x) :: r)
                          | None => None
                          end
              | None => None
              end
  end.

Lemma get_collider_descendants_from_assignments_contains_path: forall (D: assignments (nodes * node)) (col L p: nodes) (c d: node),
  get_collider_descendants_from_assignments D col = Some L
  -> get_assigned_value D c = Some (p, d) /\ c =? d = false
  -> In c col
  -> (exists (l1 l2: nodes), L = l1 ++ p ++ [d] ++ l2).
Proof.
  intros D col L p c d.
  intros HD HDc Hc.
  generalize dependent L. induction col as [| h t IH].
  - intros L HD. exfalso. apply Hc.
  - intros L HD. destruct Hc as [Hc | Hc].
    + rewrite Hc in HD. simpl in HD. destruct HDc as [HDc Hcd]. rewrite HDc in HD.
      destruct (get_collider_descendants_from_assignments D t) as [r|] eqn:Hr.
      * simpl in HD. rewrite eqb_sym in Hcd. rewrite Hcd in HD. exists []. exists r. inversion HD. simpl. reflexivity.
      * discriminate HD.
    + simpl in HD. destruct (get_assigned_value D h) as [x|] eqn:Hx.
      * destruct (get_collider_descendants_from_assignments D t) as [r|] eqn:Hr.
        -- destruct (snd x =? h) as [|] eqn:Hxh.
           ++ apply IH in HD. destruct HD as [l1 [l2 HL]]. exists l1. exists l2. apply HL. apply Hc.
           ++ inversion HD. apply IH with (L := r) in Hc. destruct Hc as [l1 [l2 HL]]. exists (fst x ++ [snd x] ++ l1). exists l2.
              rewrite <- app_assoc. rewrite <- app_assoc. simpl. rewrite HL. reflexivity. reflexivity.
        -- discriminate HD.
      * discriminate HD.
Qed.

Lemma get_collider_descendants_from_assignments_preserves_order: forall (D: assignments (nodes * node)) (col L p1 p2: nodes) (c1 c2 d1 d2: node),
  get_collider_descendants_from_assignments D col = Some L
  -> get_assigned_value D c1 = Some (p1, d1) /\ c1 =? d1 = false
  -> get_assigned_value D c2 = Some (p2, d2) /\ c2 =? d2 = false
  -> (exists (l1 l2 l3: nodes), col = l1 ++ [c1] ++ l2 ++ [c2] ++ l3)
  -> (exists (l1' l2' l3': nodes), L = l1' ++ p1 ++ [d1] ++ l2' ++ p2 ++ [d2] ++ l3').
Proof.
  intros D col L p1 p2 c1 c2 d1 d2.
  intros HD Hc1 Hc2 [l1 [l2 [l3 Hcol]]].
  generalize dependent l1. generalize dependent L. induction col as [| h t IH].
  - intros L HD l1 Hcol. destruct l1 as [| hl1 tl1]. discriminate Hcol. discriminate Hcol.
  - intros L HD l1 Hcol. destruct l1 as [| hl1 tl1].
    + simpl in Hcol. inversion Hcol. rewrite Hcol in HD. simpl in HD.
      destruct Hc1 as [Hc1 Hc1']. rewrite Hc1 in HD. simpl in HD. rewrite eqb_sym in Hc1'. rewrite Hc1' in HD.
      destruct (get_collider_descendants_from_assignments D (l2 ++ c2 :: l3)) as [r|] eqn:Hr.
      * exists [].
        assert (Hlem: exists (l1 l2: nodes), r = l1 ++ p2 ++ [d2] ++ l2).
        { apply get_collider_descendants_from_assignments_contains_path with (D := D) (col := l2 ++ c2 :: l3) (c := c2). apply Hr. apply Hc2.
          apply membership_append_r. left. reflexivity. }
        destruct Hlem as [l2' [l3' Hlem]]. exists l2'. exists l3'. simpl. simpl in Hlem. rewrite <- Hlem. inversion HD. reflexivity.
      * discriminate HD.
    + simpl in HD. inversion Hcol. destruct (get_assigned_value D h) as [x|] eqn:Hx.
      * destruct (get_collider_descendants_from_assignments D t) as [r|] eqn:Hr.
        -- destruct (snd x =? h) as [|] eqn:Hxh.
           ++ specialize IH with (L := r) (l1 := tl1). apply IH in H1. destruct H1 as [l1' [l2' [l3' Hr']]].
              exists l1'. exists l2'. exists l3'. inversion HD. rewrite <- H1. apply Hr'. reflexivity.
           ++ apply IH with (L := r) in H1. destruct H1 as [l1' [l2' [l3' Hr']]].
              exists (fst x ++ snd x :: l1'). exists l2'. exists l3'. inversion HD. rewrite <- app_assoc. simpl. rewrite Hr'. reflexivity.
              reflexivity.
        -- discriminate HD.
      * discriminate HD.
Qed.


Lemma collider_descendants_from_assignments_existence: forall (D: assignments (nodes * node)) (G: graph) (p: path),
  (forall (c: node), In c (find_colliders_in_path p G)
    -> get_assigned_value D c = Some ([], c)
       \/
       exists (p: nodes) (d: node), get_assigned_value D c = Some (p, d))
  -> exists (L: nodes), get_collider_descendants_from_assignments D (find_colliders_in_path p G) = Some L.
Proof.
  intros D G p H.
  induction (find_colliders_in_path p G) as [| h t IH].
  - simpl. exists []. reflexivity.
  - simpl.
    assert (Hh: In h (h :: t)). { left. reflexivity. } apply H in Hh.
    assert (Hind: exists L : nodes, get_collider_descendants_from_assignments D t = Some L).
    { apply IH. intros c Hc. apply H. right. apply Hc. }
    destruct Hind as [L HL].
    destruct Hh as [Hh | Hh].
    + rewrite Hh. simpl. rewrite eqb_refl.
      exists L. rewrite HL. reflexivity.
    + destruct Hh as [pa [d Hpd]]. rewrite Hpd. rewrite HL. simpl. destruct (d =? h) as [|]. exists L. reflexivity.
      exists (pa ++ d :: L). reflexivity.
Qed.

Lemma collider_descendants_is_assignment_for: forall (D: assignments (nodes * node)) (col L: nodes),
  get_collider_descendants_from_assignments D col = Some L
  -> is_assignment_for D col = true.
Proof.
  intros D col L H.
  generalize dependent L. induction col as [| h t IH].
  - intros L H. simpl. reflexivity.
  - intros L H. simpl. simpl in H. destruct (get_assigned_value D h) as [x|] eqn:Hx.
    + apply split_and_true. split.
      * apply assigned_is_true. exists x. apply Hx.
      * destruct (get_collider_descendants_from_assignments D t) as [r|] eqn:Hr.
        -- destruct (snd x =? h) as [|].
           ++ inversion H. apply IH with (L := r). reflexivity.
           ++ apply IH with (L := r). reflexivity.
        -- discriminate H.
    + discriminate H.
Qed.

Lemma collider_descendants_from_assignments_mem: forall (D: assignments (nodes * node)) (G: graph) (p': path) (L p: nodes) (c d: node),
  In c (find_colliders_in_path p' G)
  -> get_assigned_value D c = Some (p, d) /\ d =? c = false
  -> get_collider_descendants_from_assignments D (find_colliders_in_path p' G) = Some L
  -> forall (u: node), In u (p ++ [d]) -> In u L.
Proof.
  intros D G p' L p c d. intros Hc [Hpd Hdc] HL. intros u Hu.
  generalize dependent L. induction (find_colliders_in_path p' G) as [| h t IH].
  - intros L HL. exfalso. apply Hc.
  - intros L HL. destruct Hc as [Hc | Hc].
    + simpl in HL. rewrite <- Hc in *. rewrite Hpd in HL. simpl in HL. rewrite Hdc in HL.
      destruct (get_collider_descendants_from_assignments D t) as [r|].
      * inversion HL. apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]]. apply membership_append. apply Hu.
        apply membership_append_r. left. apply Hu. exfalso. apply Hu.
      * discriminate HL.
    + simpl in HL. destruct (get_assigned_value D h) as [x|].
      * destruct (get_collider_descendants_from_assignments D t) as [r|] eqn:Hr.
        -- specialize IH with (L := r). apply IH in Hc. destruct (snd x =? h) as [|].
           ++ inversion HL. rewrite <- H0. apply Hc.
           ++ inversion HL. apply membership_append_r. right. apply Hc.
           ++ reflexivity.
        -- discriminate HL.
      * discriminate HL.
Qed.

Lemma collider_descendants_from_assignments_belong_to_collider: forall (D: assignments (nodes * node)) (G: graph) (p': path) (L: nodes) (u: node),
  get_collider_descendants_from_assignments D (find_colliders_in_path p' G) = Some L
  -> In u L
  -> exists (c d: node) (p: nodes), In c (find_colliders_in_path p' G)
      /\ get_assigned_value D c = Some (p, d) /\ d =? c = false
      /\ In u (p ++ [d]).
Proof.
  intros D G p' L u. intros HL Hu.
  generalize dependent L. induction (find_colliders_in_path p' G) as [| h t IH].
  - intros L HL Hu. exfalso. simpl in HL. inversion HL. rewrite <- H0 in Hu. apply Hu.
  - intros L HL Hu. simpl in HL. destruct (get_assigned_value D h) as [x|] eqn:Hx.
    + destruct (get_collider_descendants_from_assignments D t) as [r|] eqn:Hr.
      * destruct (snd x =? h) as [|] eqn:Hhx.
        -- inversion HL. apply IH in Hu.
           ++ destruct Hu as [c [d [p Hu]]]. exists c. exists d. exists p. split. right. apply Hu. apply Hu.
           ++ f_equal. apply H0.
        -- inversion HL. rewrite <- H0 in Hu. apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]].
           ++ exists h. exists (snd x). exists (fst x). split. left. reflexivity. split. destruct x as [x1 x2]. simpl. apply Hx.
              split. apply Hhx. apply membership_append. apply Hu.
           ++ exists h. exists (snd x). exists (fst x). split. left. reflexivity. split. destruct x as [x1 x2]. simpl. apply Hx.
              split. apply Hhx. apply membership_append_r. left. apply Hu.
           ++ apply IH in Hu. destruct Hu as [c [d [p Hu]]]. exists c. exists d. exists p. split. right. apply Hu. apply Hu.
              reflexivity.
      * discriminate HL.
    + discriminate HL.
Qed.

Lemma collider_descendants_from_assignments_belong_to_collider_gen: forall (D: assignments (nodes * node)) (col: nodes) (L: nodes) (u: node),
  get_collider_descendants_from_assignments D col = Some L
  -> In u L
  -> exists (c d: node) (p: nodes), In c col
      /\ get_assigned_value D c = Some (p, d) /\ d =? c = false
      /\ In u (p ++ [d]).
Proof.
  intros D col L u. intros HL Hu.
  generalize dependent L. induction col as [| h t IH].
  - intros L HL Hu. exfalso. simpl in HL. inversion HL. rewrite <- H0 in Hu. apply Hu.
  - intros L HL Hu. simpl in HL. destruct (get_assigned_value D h) as [x|] eqn:Hx.
    + destruct (get_collider_descendants_from_assignments D t) as [r|] eqn:Hr.
      * destruct (snd x =? h) as [|] eqn:Hhx.
        -- inversion HL. apply IH in Hu.
           ++ destruct Hu as [c [d [p Hu]]]. exists c. exists d. exists p. split. right. apply Hu. apply Hu.
           ++ f_equal. apply H0.
        -- inversion HL. rewrite <- H0 in Hu. apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]].
           ++ exists h. exists (snd x). exists (fst x). split. left. reflexivity. split. destruct x as [x1 x2]. simpl. apply Hx.
              split. apply Hhx. apply membership_append. apply Hu.
           ++ exists h. exists (snd x). exists (fst x). split. left. reflexivity. split. destruct x as [x1 x2]. simpl. apply Hx.
              split. apply Hhx. apply membership_append_r. left. apply Hu.
           ++ apply IH in Hu. destruct Hu as [c [d [p Hu]]]. exists c. exists d. exists p. split. right. apply Hu. apply Hu.
              reflexivity.
      * discriminate HL.
    + discriminate HL.
Qed.



(* returns the descendant map D but with keys only being the nodes in col (remove all other key-value pairs)
   Will be crucial when working with subpaths and needing to relate the descendant maps of a subpath with the
   whole path *)
Fixpoint get_collider_descendants_for_subpath (D: assignments (nodes * node)) (col: nodes): option (assignments (nodes * node)) :=
  match col with
  | [] => Some []
  | h :: t => match (get_assigned_value D h) with
              | Some x => match (get_collider_descendants_for_subpath D t) with
                          | Some r => Some ((h, x) :: r)
                          | None => None
                          end
              | None => None
              end
  end.

Lemma collider_subpath_is_exact_assignment: forall (D D': assignments (nodes * node)) (col: nodes),
  get_collider_descendants_for_subpath D col = Some D'
  -> is_exact_assignment_for D' col.
Proof.
  intros D D' col H.
  unfold is_exact_assignment_for. split.
  - generalize dependent D'. induction col as [| h t IH].
    + simpl. reflexivity.
    + intros D' H. simpl. simpl in H. destruct (get_assigned_value D h) as [x|] eqn:Hx.
      * destruct (get_collider_descendants_for_subpath D t) as [r|] eqn:Hr.
        -- apply split_and_true. split.
           ++ inversion H. simpl. rewrite eqb_refl. reflexivity.
           ++ inversion H. apply is_assignment_for_cat. apply IH. reflexivity.
        -- discriminate H.
      * discriminate H.
  - intros u Hu. generalize dependent D'. induction col as [| h t IH].
    + intros D' H. simpl in H. inversion H. simpl. reflexivity.
    + intros D' H. simpl in H. destruct (get_assigned_value D h) as [x|] eqn:Hx.
      * destruct (get_collider_descendants_for_subpath D t) as [r|] eqn:Hr.
        -- inversion H. simpl. simpl in Hu. destruct (h =? u) as [|] eqn:Hhu. discriminate Hu. rewrite eqb_sym in Hhu. rewrite Hhu. simpl.
           apply IH. apply Hu. reflexivity.
        -- discriminate H.
      * discriminate H.
Qed.

Lemma collider_descendants_for_subpath_existence: forall (D: assignments (nodes * node)) (G: graph) (u v m: node) (l1 l2 L: nodes),
  get_collider_descendants_from_assignments D (find_colliders_in_path (concat u m v l1 l2) G) = Some L
  -> exists (D': assignments (nodes * node)), get_collider_descendants_for_subpath D (find_colliders_in_path (u, m, l1) G) = Some D'.
Proof.
  intros D G u v m l1 l2 L H.
  assert (Hc: forall (c: node), In c (find_colliders_in_path (u, m, l1) G) -> In c (find_colliders_in_path (concat u m v l1 l2) G)).
  { intros c Hc. apply subpath_preserves_colliders with (u := m) (l1 := l1) (l2 := l2). split. reflexivity. right. apply Hc. }

  induction (find_colliders_in_path (u, m, l1) G) as [| h t IH].
  - simpl. exists []. reflexivity.
  - simpl.
    assert (Hind: exists D' : assignments (nodes * node), get_collider_descendants_for_subpath D t = Some D').
    { apply IH. intros c Hc'. apply Hc. right. apply Hc'. }
    destruct Hind as [D' HD'].
    assert (Hh: exists x, get_assigned_value D h = Some x).
    { apply assigned_has_value with (L := (find_colliders_in_path (concat u m v l1 l2) G)). split.
      - apply Hc. left. reflexivity.
      - apply collider_descendants_is_assignment_for with (L := L). apply H. }
    destruct Hh as [x Hh]. rewrite Hh. exists ((h, x) :: D'). rewrite HD'. reflexivity.
Qed.

Lemma collider_descendants_for_subpath_existence_2: forall (D: assignments (nodes * node)) (G: graph) (u v m: node) (l1 l2 L: nodes),
  get_collider_descendants_from_assignments D (find_colliders_in_path (concat u m v l1 l2) G) = Some L
  -> exists (D': assignments (nodes * node)), get_collider_descendants_for_subpath D (find_colliders_in_path (m, v, l2) G) = Some D'.
Proof.
  intros D G u v m l1 l2 L H.
  assert (Hc: forall (c: node), In c (find_colliders_in_path (m, v, l2) G) -> In c (find_colliders_in_path (concat u m v l1 l2) G)).
  { intros c Hc. apply subpath_preserves_colliders with (u := m) (l1 := l1) (l2 := l2). split. reflexivity. left. apply Hc. }

  induction (find_colliders_in_path (m, v, l2) G) as [| h t IH].
  - simpl. exists []. reflexivity.
  - simpl.
    assert (Hind: exists D' : assignments (nodes * node), get_collider_descendants_for_subpath D t = Some D').
    { apply IH. intros c Hc'. apply Hc. right. apply Hc'. }
    destruct Hind as [D' HD'].
    assert (Hh: exists x, get_assigned_value D h = Some x).
    { apply assigned_has_value with (L := (find_colliders_in_path (concat u m v l1 l2) G)). split.
      - apply Hc. left. reflexivity.
      - apply collider_descendants_is_assignment_for with (L := L). apply H. }
    destruct Hh as [x Hh]. rewrite Hh. exists ((h, x) :: D'). rewrite HD'. reflexivity.
Qed.

Lemma collider_descendants_preserved_for_subpath: forall (D D': assignments (nodes * node)) (col p: nodes) (c d: node),
  get_collider_descendants_for_subpath D col = Some D'
  -> get_assigned_value D' c = Some (p, d)
  -> get_assigned_value D c = Some (p, d).
Proof.
  intros D D' col p c d H1 H2.
  generalize dependent D'. induction col as [| h t IH].
  - intros D' H1 H2. simpl in H1. inversion H1. rewrite <- H0 in H2. simpl in H2. discriminate H2.
  - intros D' H1 H2. simpl in H1. destruct (get_assigned_value D h) as [x|] eqn:Hx.
    + destruct (get_collider_descendants_for_subpath D t) as [r|] eqn:Hr.
      * inversion H1. rewrite <- H0 in H2. simpl in H2. destruct (h =? c) as [|] eqn:Hhc.
        -- apply eqb_eq in Hhc. rewrite <- Hhc. inversion H2. rewrite <- H3. apply Hx.
        -- apply IH with (D' := r). reflexivity. apply H2.
      * discriminate H1.
    + discriminate H1.
Qed.

Lemma collider_descendants_preserved_for_subpath_2: forall (D D': assignments (nodes * node)) (col p: nodes) (c d: node),
  get_collider_descendants_for_subpath D col = Some D'
  -> get_assigned_value D c = Some (p, d)
  -> In c col
  -> get_assigned_value D' c = Some (p, d).
Proof.
  intros D D' col p c d H1 H2 H3.
  generalize dependent D'. induction col as [| h t IH].
  - intros D' H1. exfalso. apply H3.
  - intros D' H1. simpl in H1. destruct (get_assigned_value D h) as [x|] eqn:Hx.
    + destruct (get_collider_descendants_for_subpath D t) as [r|] eqn:Hr.
      * inversion H1. simpl. destruct (h =? c) as [|] eqn:Hhc.
        -- apply eqb_eq in Hhc. rewrite Hhc in Hx. rewrite H2 in Hx. symmetry. apply Hx.
        -- apply IH with (D' := r). simpl in H3. destruct H3 as [H3 | H3]. rewrite H3 in Hhc. rewrite eqb_refl in Hhc. discriminate Hhc.
           apply H3. reflexivity.
      * discriminate H1.
    + discriminate H1.
Qed.

Lemma collider_descendants_preserved_for_subpath_3: forall (D D': assignments (nodes * node)) (col: nodes) (c: node),
  get_collider_descendants_for_subpath D col = Some D'
  -> In c col
  -> get_assigned_value D c = get_assigned_value D' c.
Proof.
  intros D D' col c H1 H2.
  destruct (get_assigned_value D c) as [[p d] | ] eqn:HDc.
  - symmetry. apply collider_descendants_preserved_for_subpath_2 with (D := D) (col := col). apply H1. apply HDc. apply H2.
  - destruct (get_assigned_value D' c) as [[p d] | ] eqn:HDc'.
    + apply collider_descendants_preserved_for_subpath with (D := D) (col := col) in HDc'.
      * rewrite HDc' in HDc. discriminate HDc.
      * apply H1.
    + reflexivity.
Qed.



(* In later proofs, it will be important to guarantee that the descendant paths specified by D do not overlap
   either the d-connected path that they belong to, or each other. We define the following to provide this
   guarantee *)
Definition descendant_paths_disjoint_col (D: assignments (nodes * node)) (u v: node) (l': nodes) (G: graph) (Z: nodes): Prop :=
  forall (c: node), In c (find_colliders_in_path (u, v, l') G)
      -> get_assigned_value D c = Some ([], c) /\ In c Z (* c is conditioned on, don't need path *)
         \/
         exists (p: nodes) (d: node), get_assigned_value D c = Some (p, d)
           /\ In d Z /\ is_directed_path_in_graph (c, d, p) G = true (* c has path p to conditioned descendant d *)
                     /\ acyclic_path_2 (c, d, p) (* directed path is acyclic, not a huge constraint *)
           /\ overlap (c :: p) Z = false (* d is the first node in the path that is conditioned on *)
           /\ overlap (p ++ [d]) (u :: l' ++ [v]) = false (* the descendant does not intersect the u-v path *)
           /\ forall (c' d': node) (p': nodes), (c =? c' = false) /\ get_assigned_value D c' = Some (p', d')
              -> overlap (c :: p ++ [d]) (c' :: p' ++ [d']) = false. (* the descendant path does not intersect any other descendant path *)

Lemma descendant_paths_disjoint_col_cat: forall (D: assignments (nodes * node)) (u v h: node) (t: nodes) (G: graph) (Z: nodes),
  descendant_paths_disjoint_col D u v (h :: t) G Z
  -> descendant_paths_disjoint_col D h v t G Z.
Proof.
  intros D u v h t G Z Hdesc.

  unfold descendant_paths_disjoint_col in *. intros c Hc.
  assert (Hc': In c (find_colliders_in_path (u, v, h :: t) G)).
  { apply subpath_preserves_colliders with (u := h) (l1 := []) (l2 := t). split. reflexivity. left. apply Hc. }
  apply Hdesc in Hc'. clear Hc.
  destruct Hc' as [Hc | Hc].
  - left. apply Hc.
  - right. destruct Hc as [p [d Hc]]. exists p. exists d. split. apply Hc. split. apply Hc. split. apply Hc. split. apply Hc.
    split. apply Hc. split.
    + destruct Hc as [_ [_ [_ [_ [_ [Hc _]]]]]]. simpl in Hc. apply overlap_flip in Hc. apply overlap_cat in Hc. apply overlap_flip. apply Hc.
    + apply Hc.
Qed.


Definition descendant_paths_disjoint (D: assignments (nodes * node)) (u v: node) (l': nodes) (G: graph) (Z: nodes): Prop :=
  is_exact_assignment_for D (find_colliders_in_path (u, v, l') G) /\
  descendant_paths_disjoint_col D u v l' G Z.

Lemma descendant_paths_disjoint_cat: forall (D: assignments (nodes * node)) (u v h: node) (t: nodes) (G: graph) (Z: nodes),
  descendant_paths_disjoint D u v (h :: t) G Z
  -> ~In h (find_colliders_in_path (u, v, h :: t) G)
  -> descendant_paths_disjoint D h v t G Z.
Proof.
  intros D u v h t G Z Hdesc Hh.
  assert (find_colliders_in_path (u, v, h :: t) G = find_colliders_in_path (h, v, t) G).
  { simpl. destruct t as [| h' t'].
    - simpl. destruct (is_collider_bool u v h G) as [|] eqn:Hcol.
      + exfalso. apply Hh. simpl. rewrite Hcol. left. reflexivity.
      + reflexivity.
    - simpl. destruct (is_collider_bool u h' h G) as [|] eqn:Hcol.
      + exfalso. apply Hh. simpl. rewrite Hcol. left. reflexivity.
      + reflexivity. }

  split. rewrite <- H. apply Hdesc. destruct Hdesc as [_ Hdesc]. apply descendant_paths_disjoint_col_cat in Hdesc.
  apply Hdesc.
Qed.



Lemma get_collider_descendants_from_assignments_preserves_count: forall (D: assignments (nodes * node)) (u v: node) (l': nodes) (G: graph) (Z: nodes) (L: nodes),
  descendant_paths_disjoint D u v l' G Z
  -> get_collider_descendants_from_assignments D (find_colliders_in_path (u, v, l') G) = Some L
  -> acyclic_path_2 (u, v, l')
  -> is_path_in_graph (u, v, l') G = true
  -> forall (x: node), In x L -> count x L = 1.
Proof.
  intros D u v l G Z L HD HL Hcyc Hp x Hx.
  unfold descendant_paths_disjoint in HD. destruct HD as [_ HD]. unfold descendant_paths_disjoint_col in HD.

  assert (Hcount: forall (c: node), In c (find_colliders_in_path (u, v, l) G) -> count c (find_colliders_in_path (u, v, l) G) = 1).
  { intros c Hc. apply collider_count_acyclic. apply Hc. apply Hcyc. apply Hp. }

  generalize dependent L. induction (find_colliders_in_path (u, v, l) G) as [| h t IH].
  - intros L HL Hx. simpl in HL. inversion HL. rewrite <- H0 in Hx. exfalso. apply Hx.
  - intros L HL Hx. simpl in HL. destruct (get_assigned_value D h) as [xh|] eqn:Hxh.
    + destruct (get_collider_descendants_from_assignments D t) as [r|] eqn:Hr.
      * destruct (snd xh =? h) as [|] eqn:Hxhh.
        -- apply IH. intros c Hc. apply HD. right. apply Hc. intros c Hc. assert (Hct: In c (h :: t)). { right. apply Hc. } apply Hcount in Hct.
           simpl in Hct. destruct (h =? c) as [|]. apply member_count_at_least_1 in Hc. lia. apply Hct. apply HL. apply Hx.
        -- specialize IH with (L := r). inversion HL. rewrite <- append_vs_concat. rewrite count_app.
           rewrite <- append_vs_concat in H0. rewrite <- H0 in Hx. apply membership_append_or in Hx.
           assert (HxF: In x r -> In x (fst xh ++ [snd xh]) -> False).
           { intros Hxr Hxxh. apply collider_descendants_from_assignments_belong_to_collider_gen with (D := D) (col := t) in Hxr.
             - destruct Hxr as [c [d [p Hxr]]]. assert (Hcmem: In c (h :: t)). { right. apply Hxr. } pose proof Hcmem as Hcmem'. apply HD in Hcmem.
               destruct Hcmem as [[Hcmem _] | Hcmem].
               + destruct Hxr as [_ [Hpd [Hdc _]]]. rewrite Hpd in Hcmem. inversion Hcmem. rewrite H2 in Hdc. rewrite eqb_refl in Hdc. discriminate Hdc.
               + destruct Hcmem as [p' [d' [Hpd' Hcmem]]]. destruct Hxr as [Hct [Hpd [_ Hxpd]]]. rewrite Hpd in Hpd'. inversion Hpd'.
                 rewrite <- H1 in *. rewrite <- H2 in *. destruct Hcmem as [_ [_ [_ [_ [_ Hcmem]]]]].
                 specialize Hcmem with (c' := h) (d' := snd xh) (p' := fst xh).
                 assert (Hover: overlap (c :: p ++ [d]) (h :: fst xh ++ [snd xh]) = false).
                 { apply Hcmem. split.
                   - destruct (c =? h) as [|] eqn:Hch. apply Hcount in Hcmem'. simpl in Hcmem'. rewrite eqb_sym in Hch. rewrite Hch in Hcmem'. apply member_count_at_least_1 in Hct. lia. reflexivity.
                   - destruct xh as [xh1 xh2]. simpl. apply Hxh. }
                 apply no_overlap_non_member with (x := x) in Hover. apply Hover. right. apply Hxpd. right. apply Hxxh.
             - apply Hr. }

           destruct Hx as [Hx | Hx].
           ++ assert (Hxmem: ~In x r).
              { intros Hxr. apply HxF in Hxr. apply Hxr. apply Hx. }
              apply member_In_equiv_F in Hxmem. apply not_member_count_0 in Hxmem. rewrite Hxmem.
              specialize HD with (c := h). assert (Hh: In h (h :: t)). { left. reflexivity. } apply HD in Hh.
              destruct Hh as [Hh | Hh].
              destruct Hh as [Hh _]. rewrite Hxh in Hh. inversion Hh. rewrite H1 in Hxhh. simpl in Hxhh. rewrite eqb_refl in Hxhh. discriminate Hxhh.
              destruct Hh as [ph [dh [Hh Hh']]]. rewrite Hxh in Hh. inversion Hh. destruct Hh' as [_ [_ [Hh' _]]]. rewrite H1 in Hx. simpl in Hx.
              apply acyclic_path_count with (x := x) in Hh'. simpl. apply member_count_at_least_1 in Hx. simpl in Hh'.
              destruct (h =? x) as [|]. inversion Hh'. unfold nodes in *. unfold node in *. lia. rewrite add_comm. simpl. apply Hh'. right. apply Hx.
           ++ assert (Hxmem: ~In x (fst xh ++ [snd xh])).
              { intros Hxxh. apply HxF. apply Hx. apply Hxxh. }
              apply member_In_equiv_F in Hxmem. apply not_member_count_0 in Hxmem. unfold nodes in *. unfold node in *. rewrite Hxmem. simpl.
              apply IH. intros c Hc. apply HD. right. apply Hc. intros c Hc. assert (Hct: In c (h :: t)). { right. apply Hc. } apply Hcount in Hct.
              simpl in Hct. destruct (h =? c) as [|]. apply member_count_at_least_1 in Hc. lia. apply Hct. reflexivity. apply Hx.
      * discriminate HL.
    + discriminate HL.
Qed.

Lemma descendant_paths_disjoint_subpath: forall (Dh Dx: assignments (nodes * node)) (h v x: node) (l1 l2 lhv: nodes) (G: graph) (Z: nodes),
  descendant_paths_disjoint Dh h v lhv G Z
  -> get_collider_descendants_for_subpath Dh
          (find_colliders_in_path (x, v, l2) G) =
        Some Dx
  -> lhv = l1 ++ [x] ++ l2
  -> descendant_paths_disjoint Dx x v l2 G Z.
Proof.
  intros Dh Dx h v x l1 l2 lhv G Z. intros HDh HDx Hlhv. unfold descendant_paths_disjoint in *.
  split.
  - apply collider_subpath_is_exact_assignment with (D := Dh). apply HDx.
  - intros c Hc. destruct HDh as [_ HDh]. assert (In c (find_colliders_in_path (h, v, lhv) G)).
    { apply subpath_preserves_colliders with (u := x) (l1 := l1) (l2 := l2). split. symmetry. apply Hlhv.
      left. apply Hc. }
    apply HDh in H. destruct H as [H | H].
    + left. rewrite <- collider_descendants_preserved_for_subpath_3 with (D := Dh) (col := (find_colliders_in_path (x, v, l2) G)). apply H. apply HDx. apply Hc.
    + right. destruct H as [p [d H]]. exists p. exists d. split.
      * rewrite <- collider_descendants_preserved_for_subpath_3 with (D := Dh) (col := (find_colliders_in_path (x, v, l2) G)). apply H. apply HDx. apply Hc.
      * rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split. repeat split; apply H. split.
        -- apply no_overlap_non_member. intros y Hy Hy'. destruct H as [_ [_ [_ [_ [_ [H _]]]]]]. apply no_overlap_non_member with (x := y) in H. apply H.
           apply Hy'. right. rewrite Hlhv. rewrite <- app_assoc. apply membership_append_r. apply Hy.
        -- intros c' d' p'. intros Hc'. apply H. split. apply Hc'. apply collider_descendants_preserved_for_subpath with (D' := Dx) (col := (find_colliders_in_path (x, v, l2) G)). apply HDx. apply Hc'.
Qed.
