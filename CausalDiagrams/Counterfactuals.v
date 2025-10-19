From CausalDiagrams Require Import Assignments.
From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import DSeparation.
From CausalDiagrams Require Import CausalPaths.
From CausalDiagrams Require Import Interventions.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.

(* counterfactuals *)
Definition no_repeat_nodes (V: nodes) : bool :=
  forallb (fun x: node => count x V =? 1) V.

Definition find_new_node (V: nodes) : node :=
  (max_list V) + 1.

Example add_new_node_1: find_new_node [1;2;3;4] = 5.
Proof. reflexivity. Qed.

Example add_new_node_2: find_new_node [1;2;4] = 5.
Proof. reflexivity. Qed.

Example add_new_node_3: find_new_node [2;1;4] = 5.
Proof. reflexivity. Qed.

Example add_new_node_4: find_new_node [2;4] = 5.
Proof. reflexivity. Qed.

Lemma new_node_non_member: forall V: nodes,
  member (find_new_node V) V = false.
Proof.
  intros V.
  unfold find_new_node.
  destruct (member (max_list V + 1) V) as [|] eqn:Hmem.
  - apply member_In_equiv in Hmem. apply max_correct in Hmem.
    apply leb_le in Hmem. 
    lia.
  - reflexivity.
Qed.

Theorem add_new_node_no_repeats: forall V: nodes,
  no_repeat_nodes V = true -> no_repeat_nodes ((find_new_node V) :: V) = true.
Proof.
  intros V H.
  apply forallb_true_iff. simpl. split.
  - (* find new node has no repeats *)
    rewrite eqb_refl. simpl.
    apply eqb_eq. apply not_member_count_0.
    apply new_node_non_member.
  - (* V has no repeats (H) *)
    apply forallb_true_iff.
    unfold no_repeat_nodes in H.
    apply forallb_forall. intros x Hmem.
    destruct (find_new_node V =? x) as [|] eqn:contra.
    + apply eqb_eq in contra. rewrite <- contra in Hmem. apply member_In_equiv in Hmem.
      assert (Hnomem: member (find_new_node V) V = false). { apply new_node_non_member. }
      rewrite Hmem in Hnomem. discriminate Hnomem.
    + apply forallb_true with (test := (fun x : node => count x V =? 1)) in Hmem.
      * apply Hmem.
      * apply H.
Qed.

(* shifting is used to translate a set of nodes by an offset
   when duplicating a graph for the twin network, the offset is the max node number *)
Fixpoint shift_nodes_by_offset (Z: nodes) (o: nat) :=
  match Z with
  | [] => []
  | h :: t => (h + o) :: (shift_nodes_by_offset t o)
  end.

Lemma shift_greater_than_offset: forall l: nodes, forall o: nat, forall x: node,
  In x (shift_nodes_by_offset l o) -> o <= x.
Proof.
  intros l o x.
  induction l as [| h t IH].
  - intros H. simpl in H. exfalso. apply H.
  - simpl. intros H. destruct H as [H | H].
    + lia.
    + apply IH. apply H.
Qed.

Lemma shift_member: forall l: nodes, forall x: node, forall o: nat,
  In x (shift_nodes_by_offset l o) <-> In (x - o) l /\ o <= x.
Proof.
  intros l x o. split.
  { intros Hmem.
  induction l as [| h t IH].
  - simpl in Hmem. exfalso. apply Hmem.
  - simpl. simpl in Hmem. destruct Hmem as [Heq | Hind].
    + lia.
    + split.
      * right. apply IH. apply Hind.
      * apply shift_greater_than_offset in Hind. apply Hind. }
  { intros [Hmem Hox].
  induction l as [| h t IH].
  - simpl in Hmem. exfalso. apply Hmem.
  - simpl. simpl in Hmem. destruct Hmem as [Heq | Hind].
    + left. lia.
    + right. apply IH. apply Hind. }
Qed.

Lemma shift_maintains_overlap: forall (l1 l2: nodes) (o: nat),
  overlap l1 l2 = false -> overlap (shift_nodes_by_offset l1 o) (shift_nodes_by_offset l2 o) = false.
Proof.
  intros l1 l2 o H.
  apply no_overlap_non_member. intros x Hmem2 Hmem1.
  apply shift_member in Hmem1. destruct Hmem1 as [Hmem1 _].
  apply shift_member in Hmem2. destruct Hmem2 as [Hmem2 _].
  apply no_overlap_non_member with (x := x - o) in H.
  - unfold not in H. apply H. apply Hmem1.
  - apply Hmem2.
Qed.

Lemma shift_maintains_prefix: forall (l1 l2: nodes) (o: nat),
  prefix l1 l2 = true <-> prefix (shift_nodes_by_offset l1 o) (shift_nodes_by_offset l2 o) = true.
Proof.
  induction l1 as [| h1 t1 IH].
  - intros l2 o. split.
    { simpl. reflexivity. }
    { simpl. reflexivity. }
  - intros l2 o. split.
    { intros Hpref. destruct l2 as [| h2 t2].
    + simpl in Hpref. discriminate Hpref.
    + simpl in Hpref. apply split_and_true in Hpref. destruct Hpref as [H12 Hind].
      simpl. apply eqb_eq in H12. rewrite H12. rewrite eqb_refl. simpl.
      apply IH with (l2 := t2). apply Hind. }
    { intros Hpref. destruct l2 as [| h2 t2].
    + simpl in Hpref. discriminate Hpref.
    + simpl in Hpref. apply split_and_true in Hpref. destruct Hpref as [H12o Hind].
      simpl. apply eqb_eq in H12o.
      assert (H12: h1 = h2). { lia. }
      rewrite H12. rewrite eqb_refl. simpl.
      apply IH with (l2 := t2) (o := o). apply Hind. }
Qed.

Lemma shift_maintains_subset: forall (l1 l2: nodes) (o: nat),
  sublist l1 l2 = true <-> sublist (shift_nodes_by_offset l1 o) (shift_nodes_by_offset l2 o) = true.
Proof.
  intros l1 l2 o. split.
  { intros Hsub. induction l2 as [| h2 t2 IH].
  - destruct l1 as [| h1 t1].
    + simpl. reflexivity.
    + simpl in Hsub. discriminate Hsub.
  - simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [Hpre | Hind].
    + simpl. apply shift_maintains_prefix with (o := o) in Hpre.
      simpl in Hpre. rewrite Hpre. simpl. reflexivity.
    + apply IH in Hind. simpl. rewrite Hind. rewrite orb_comm. simpl. reflexivity. }
  { intros Hsub. induction l2 as [| h2 t2 IH].
  - destruct l1 as [| h1 t1]. 
    + simpl. reflexivity.
    + simpl in Hsub. discriminate Hsub.
  - simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [Hpre | Hind].
    + simpl.
      replace (h2 + o :: shift_nodes_by_offset t2 o) with (shift_nodes_by_offset (h2 :: t2) o) in Hpre.
      * apply shift_maintains_prefix in Hpre. rewrite Hpre. simpl. reflexivity.
      * simpl. reflexivity.
    + apply IH  in Hind. simpl. rewrite Hind. rewrite orb_comm. simpl. reflexivity. }
Qed.

Lemma shift_maintains_append: forall (l1 l2: nodes) (o: nat),
  (shift_nodes_by_offset l1 o) ++ (shift_nodes_by_offset l2 o) = shift_nodes_by_offset (l1 ++ l2) o.
Proof.
  intros l1 l2 o. induction l1 as [| h1 t1 IH].
  - simpl. reflexivity.
  - simpl. apply f_equal. apply IH.
Qed.

(*
Twin Network

BEFORE PREPROCESSING:

for each v in V:
  create new v' in V'
  create new u in U
  add edges (u, v), (u, v')

for each edge (x, y) in E:
  add edge (x', y')

for each v in obs:
  apply do operator for v

for each v in cf:
  apply do operator for v' based on corr

for each u in U:
  if u has <2 edges out, delete edges and node

return (V + V' + U, edges)
*)

Fixpoint get_twin_nodes (V: nodes) (o: nat) : nodes :=
  match V with
  | [] => []
  | h :: t => (h + o) :: (get_twin_nodes t o)
  end.

Lemma twin_nodes_duplicated: forall V, forall o: nat, forall u: node,
  member u V = true <-> member (u + o) (get_twin_nodes V o) = true.
Proof.
  intros V.
  induction V as [| h t IH].
  - intros o u. split.
    { intros Hmem. simpl in Hmem. discriminate Hmem. }
    { intros Hmem. simpl in Hmem. discriminate Hmem. }
  - intros o u. split.
    { intros Hmem. simpl in Hmem. destruct (h + o =? u + o) as [|] eqn:Hhu.
    + simpl. rewrite Hhu. reflexivity.
    + simpl. rewrite Hhu. 
      apply IH. destruct (h =? u) as [|] eqn:Hhu1.
      * rewrite eqb_eq in Hhu1. rewrite Hhu1 in Hhu.
        rewrite eqb_refl in Hhu. discriminate Hhu.
      * apply Hmem. }
    { intros Hmem. simpl in Hmem. simpl. destruct (h =? u) as [|] eqn:Hhu.
    + reflexivity.
    + destruct (h + o =? u + o) as [|] eqn:Hhu1.
      * rewrite eqb_eq in Hhu1. assert (H: h = u). { lia. }
        rewrite H in Hhu.
        rewrite eqb_refl in Hhu. discriminate Hhu.
      * apply IH in Hmem. apply Hmem. }
Qed.

Lemma twin_nodes_greater_than_offset: forall V: nodes, forall o: nat, forall x: node,
  In x (get_twin_nodes V o) -> o <= x.
Proof.
  intros V o x.
  induction V as [| h t IH].
  - intros H. simpl in H. exfalso. apply H.
  - simpl. intros H. destruct H as [H | H].
    + lia.
    + apply IH. apply H.
Qed.

Fixpoint get_twin_edges (E: edges) (o: nat) : edges :=
  match E with
  | [] => []
  | h :: t => match h with
              | (u, v) => (u + o, v + o) :: (get_twin_edges t o)
              end
  end.

Lemma twin_edges_duplicated: forall E: edges, forall o: nat, forall e: edge,
  member_edge e E = true <-> member_edge (fst e + o, snd e + o) (get_twin_edges E o) = true.
Proof.
  intros E o e. split.
  { intros Hmem.
  induction E as [| h t IH].
  - simpl in Hmem. discriminate Hmem.
  - simpl in Hmem. apply split_orb_true in Hmem. destruct Hmem as [Heq | Hmem].
    + destruct h as [u v]. simpl. destruct e as [u' v'].
      unfold eqbedge in Heq. apply split_and_true in Heq. destruct Heq as [Hu Hv].
      simpl. apply eqb_eq in Hu. apply eqb_eq in Hv. rewrite Hu. rewrite eqb_refl. simpl.
      rewrite Hv. rewrite eqb_refl. simpl. reflexivity.
    + apply IH in Hmem. destruct h as [u' v']. simpl. rewrite Hmem.
      rewrite orb_comm. simpl. reflexivity. }
  { intros Hmem.
  induction E as [| h t IH].
  - simpl in Hmem. discriminate Hmem.
  - destruct e as [u v]. destruct h as [u' v']. simpl in Hmem. simpl.
    apply split_orb_true in Hmem. destruct Hmem as [Heq | Hind].
    + apply split_and_true in Heq. destruct Heq as [Hu Hv].
      rewrite eqb_eq in Hu. assert (Hu1: u' = u). { lia. }
      rewrite eqb_eq in Hv. assert (Hv1: v' = v). { lia. }
      rewrite Hu1. rewrite Hv1. rewrite eqb_refl. simpl. rewrite eqb_refl. simpl.
      reflexivity.
    + simpl in IH. apply IH in Hind. rewrite Hind. rewrite orb_comm. simpl.
      reflexivity. }
Qed.

Definition duplicate_graph (G: graph) : graph :=
  match G with
  | (V, E) => (get_twin_nodes V (max_list V), get_twin_edges E (max_list V))
  end.

Lemma duplicate_graph_maintains_edges: forall (u v: node) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  is_edge (u, v) G = true <-> is_edge (u + o, v + o) (duplicate_graph G) = true.
Proof.
  intros y x G o Ho. split.
  - intros Hedge. destruct G as [V E]. simpl. simpl in Ho.
    unfold is_edge in Hedge. apply split_and_true in Hedge. destruct Hedge as [Hmem Hedge].
    apply split_and_true in Hmem. destruct Hmem as [Hy Hx].
    assert (Hmemy: member (y + o) (get_twin_nodes V (max_list V)) = true).
    { apply twin_nodes_duplicated with (o := o) in Hy.
      rewrite <- Ho. apply Hy. }
    rewrite Hmemy. simpl.
    assert (Hmemx: member (x + o) (get_twin_nodes V (max_list V)) = true).
    { apply twin_nodes_duplicated with (o := o) in Hx.
      rewrite <- Ho. apply Hx. }
    rewrite Hmemx. simpl.
    apply twin_edges_duplicated with (o := o) in Hedge. simpl in Hedge.
    rewrite <- Ho. apply Hedge.
  - intros Hedge. destruct G as [V E]. simpl. simpl in Ho.
    unfold is_edge in Hedge. apply split_and_true in Hedge. destruct Hedge as [Hmem Hedge].
    apply split_and_true in Hmem. destruct Hmem as [Hy Hx].
    rewrite <- Ho in Hy. apply twin_nodes_duplicated in Hy.
    rewrite Hy.
    rewrite <- Ho in Hx. apply twin_nodes_duplicated in Hx.
    rewrite Hx.
    rewrite <- Ho in Hedge. apply twin_edges_duplicated with (e := (y,x)) in Hedge.
    rewrite Hedge. simpl. reflexivity.
Qed.

Lemma duplicate_graph_maintains_mediators: forall (u v: node) (l: nodes) (G: graph) (o: nat) (x: node),
  o = max_node_in_graph G -> In x (find_mediators_in_path (u, v, l) G) <->
  In (x + o) (find_mediators_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G)).
Proof.
  intros u v l G o x.
  unfold find_mediators_in_path. intros Ho. split.
  { intros Hmem.
  apply mediators_vs_edges_in_path in Hmem. destruct Hmem as [y [z Hmem]].
  destruct Hmem as [Hsub Hedge].
  apply mediators_vs_edges_in_path. exists (y + o). exists (z + o). split.
  - apply shift_maintains_subset with (o := o) in Hsub.
    replace (shift_nodes_by_offset [y; x; z] o) with ([y + o; x + o; z + o]) in Hsub.
    replace (shift_nodes_by_offset (u :: l ++ [v]) o) with (u + o :: (shift_nodes_by_offset l o) ++ [v + o]) in Hsub.
    + apply Hsub.
    + simpl. replace (shift_nodes_by_offset (l ++ [v]) o) with (shift_nodes_by_offset l o ++ [v + o]).
      * reflexivity.
      * apply shift_maintains_append with (l2 := [v]).
    + simpl. reflexivity.
  - destruct G as [V E]. simpl in Ho.
    destruct Hedge as [Hedge | Hedge].
    { left. split.
    + destruct Hedge as [Hyx _]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hyx.
    + destruct Hedge as [_ Hxz]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hxz. }
    { right. split.
    + destruct Hedge as [Hyx _]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hyx.
    + destruct Hedge as [_ Hxz]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hxz. } }
  { intros Hmem.
    apply mediators_vs_edges_in_path in Hmem. destruct Hmem as [y' [z' Hmem]].
    destruct Hmem as [Hsub Hedge].
    apply mediators_vs_edges_in_path.
    assert (Hshift: (@cons node (add u o)
               (@app node (shift_nodes_by_offset l o)
                  (@cons node (add v o) (@nil node)))) = (shift_nodes_by_offset (u :: l ++ [v]) o)).
      { simpl. rewrite <- shift_maintains_append. simpl. reflexivity. }
    rewrite Hshift in Hsub.
    assert (Hz: exists z, z + o = z').
      { exists (z' - o). assert (Hz': In z' (shift_nodes_by_offset (u :: l ++ [v]) o)).
        { apply sublist_member with (l1 := [y'; x + o; z']). split.
          - simpl. right. right. left. reflexivity.
          - apply Hsub. }
        apply shift_greater_than_offset in Hz'. lia. }
    assert (Hy: exists y, y + o = y').
    { exists (y' - o). assert (Hy': In y' (shift_nodes_by_offset (u :: l ++ [v]) o)).
      { apply sublist_member with (l1 := [y'; x + o; z']). split.
        - simpl. left. reflexivity.
        - apply Hsub. }
      apply shift_greater_than_offset in Hy'. lia. }
    destruct Hz as [z Hz]. destruct Hy as [y Hy].
    exists y. exists z. rewrite <- Hz in Hsub. rewrite <- Hy in Hsub.
    split.
    - replace ((@cons node (add y o)
               (@cons node (add x o) (@cons node (add z o) (@nil node))))) with (shift_nodes_by_offset [y; x; z] o) in Hsub.
      + apply shift_maintains_subset in Hsub. apply Hsub.
      + simpl. reflexivity.
    - destruct Hedge as [Hedge | Hedge].
      { left. split.
      + destruct Hedge as [Hedge _]. apply duplicate_graph_maintains_edges with (o := o).
        * apply Ho.
        * rewrite <- Hy in Hedge. apply Hedge.
      + destruct Hedge as [_ Hedge]. apply duplicate_graph_maintains_edges with (o := o).
        * apply Ho.
        * rewrite <- Hz in Hedge. apply Hedge. }
      { right. split.
      + destruct Hedge as [Hedge _]. apply duplicate_graph_maintains_edges with (o := o).
        * apply Ho.
        * rewrite <- Hy in Hedge. apply Hedge.
      + destruct Hedge as [_ Hedge]. apply duplicate_graph_maintains_edges with (o := o).
        * apply Ho.
        * rewrite <- Hz in Hedge. apply Hedge. } }
Qed.

Lemma duplicate_graph_maintains_confounders: forall (u v: node) (l: nodes) (G: graph) (o: nat) (x: node),
  o = max_node_in_graph G ->
  In x (find_confounders_in_path (u, v, l) G) <->
  In (x + o) (find_confounders_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G)).
Proof.
  intros u v l G o x.
  unfold find_confounders_in_path. intros Ho. split.
  { intros Hmem.
  apply confounders_vs_edges_in_path in Hmem. destruct Hmem as [y [z Hmem]].
  destruct Hmem as [Hsub Hedge].
  apply confounders_vs_edges_in_path. exists (y + o). exists (z + o). split.
  - apply shift_maintains_subset with (o := o) in Hsub.
    replace (shift_nodes_by_offset [y; x; z] o) with ([y + o; x + o; z + o]) in Hsub.
    replace (shift_nodes_by_offset (u :: l ++ [v]) o) with (u + o :: (shift_nodes_by_offset l o) ++ [v + o]) in Hsub.
    + apply Hsub.
    + simpl. replace (shift_nodes_by_offset (l ++ [v]) o) with (shift_nodes_by_offset l o ++ [v + o]).
      * reflexivity.
      * apply shift_maintains_append with (l2 := [v]).
    + simpl. reflexivity.
  - destruct G as [V E]. simpl in Ho. split.
    + destruct Hedge as [Hxy _]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hxy.
    + destruct Hedge as [_ Hxz]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hxz. }
  { intros Hmem.
  apply confounders_vs_edges_in_path in Hmem. destruct Hmem as [y' [z' Hmem]].
  destruct Hmem as [Hsub Hedge].
  apply confounders_vs_edges_in_path.
  assert (Hshift: (@cons node (add u o)
             (@app node (shift_nodes_by_offset l o)
                (@cons node (add v o) (@nil node)))) = (shift_nodes_by_offset (u :: l ++ [v]) o)).
    { simpl. rewrite <- shift_maintains_append. simpl. reflexivity. }
  rewrite Hshift in Hsub.
  assert (Hz: exists z, z + o = z').
    { exists (z' - o). assert (Hz': In z' (shift_nodes_by_offset (u :: l ++ [v]) o)).
      { apply sublist_member with (l1 := [y'; x + o; z']). split.
        - simpl. right. right. left. reflexivity.
        - apply Hsub. }
      apply shift_greater_than_offset in Hz'. lia. }
  assert (Hy: exists y, y + o = y').
  { exists (y' - o). assert (Hy': In y' (shift_nodes_by_offset (u :: l ++ [v]) o)).
    { apply sublist_member with (l1 := [y'; x + o; z']). split.
      - simpl. left. reflexivity.
      - apply Hsub. }
    apply shift_greater_than_offset in Hy'. lia. }
  destruct Hz as [z Hz]. destruct Hy as [y Hy].
  exists y. exists z. rewrite <- Hz in Hsub. rewrite <- Hy in Hsub.
  split.
  - replace ((@cons node (add y o)
             (@cons node (add x o) (@cons node (add z o) (@nil node))))) with (shift_nodes_by_offset [y; x; z] o) in Hsub.
    + apply shift_maintains_subset in Hsub. apply Hsub.
    + simpl. reflexivity.
  - split.
    + destruct Hedge as [Hedge _]. apply duplicate_graph_maintains_edges with (o := o).
      * apply Ho.
      * rewrite <- Hy in Hedge. apply Hedge.
    + destruct Hedge as [_ Hedge]. apply duplicate_graph_maintains_edges with (o := o).
      * apply Ho.
      * rewrite <- Hz in Hedge. apply Hedge. }
Qed.

Lemma duplicate_graph_maintains_single_collider: forall (u v c: node) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  is_collider_bool u v c G = true <-> 
  is_collider_bool (u + o) (v + o) (c + o) (duplicate_graph G) = true.
Proof.
  intros u v c G o Ho. split.
  - unfold is_collider_bool. intros H. apply split_and_true in H.
    destruct H as [Huc Hvc]. destruct G as [V E].
    apply duplicate_graph_maintains_edges with (o := o) in Huc.
    apply duplicate_graph_maintains_edges with (o := o) in Hvc.
    + unfold node. rewrite Huc. rewrite Hvc. reflexivity.
    + apply Ho.
    + apply Ho.
  - unfold is_collider_bool. intros H. apply split_and_true in H.
    destruct H as [Huc Hvc]. destruct G as [V E].
    apply duplicate_graph_maintains_edges with (o := o) in Huc.
    apply duplicate_graph_maintains_edges with (o := o) in Hvc.
    + rewrite Huc. rewrite Hvc. reflexivity.
    + apply Ho.
    + apply Ho.
Qed.

Lemma duplicate_graph_maintains_single_collider_f: forall (u v c: node) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  is_collider_bool u v c G = false <-> 
  is_collider_bool (u + o) (v + o) (c + o) (duplicate_graph G) = false.
Proof.
  intros u v c G o Ho. split.
  - intros H.
    destruct (is_collider_bool (u + o) (v + o) (c + o) (duplicate_graph G)) as [|] eqn:Hcol.
    + apply duplicate_graph_maintains_single_collider in Hcol.
      rewrite Hcol in H. discriminate H. apply Ho.
    + reflexivity.
  - intros H.
    destruct (is_collider_bool u v c G) as [|] eqn:Hcol.
    + apply duplicate_graph_maintains_single_collider with (o := o) in Hcol.
      rewrite Hcol in H. discriminate H. apply Ho.
    + reflexivity.
Qed.

Lemma duplicate_graph_maintains_colliders: forall (u v: node) (l: nodes) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  find_colliders_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G)
  = shift_nodes_by_offset (find_colliders_in_path (u, v, l) G) o.
Proof.
  intros u v l G o. intros Ho.
  generalize dependent v. generalize dependent u.
  unfold find_colliders_in_path.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - intros u v. destruct t as [| h' t'].
    + simpl. destruct (is_collider_bool u v h G) as [|] eqn:Hcol.
      * simpl. apply duplicate_graph_maintains_single_collider with (o := o) in Hcol.
        -- rewrite Hcol. reflexivity.
        -- apply Ho.
      * apply duplicate_graph_maintains_single_collider_f with (o := o) in Hcol.
        rewrite Hcol. simpl. reflexivity. apply Ho.
    + destruct t' as [| h'' t''].
      * simpl. destruct (is_collider_bool u h' h G) as [|] eqn:Hcol.
        -- apply duplicate_graph_maintains_single_collider with (o := o) in Hcol.
           rewrite Hcol. simpl. f_equal.
           destruct (is_collider_bool h v h' G) as [|] eqn:Hcol2.
           ++ apply duplicate_graph_maintains_single_collider with (o := o) in Hcol2.
              rewrite Hcol2. simpl. reflexivity. apply Ho.
           ++ apply duplicate_graph_maintains_single_collider_f with (o := o) in Hcol2.
              rewrite Hcol2. simpl. reflexivity. apply Ho.
           ++ apply Ho.
        -- apply duplicate_graph_maintains_single_collider_f with (o := o) in Hcol.
           rewrite Hcol. destruct (is_collider_bool h v h' G) as [|] eqn:Hcol2.
           ++ apply duplicate_graph_maintains_single_collider with (o := o) in Hcol2.
              rewrite Hcol2. simpl. reflexivity. apply Ho.
           ++ apply duplicate_graph_maintains_single_collider_f with (o := o) in Hcol2.
              rewrite Hcol2. simpl. reflexivity. apply Ho.
           ++ apply Ho.
      * destruct (is_collider_bool u h' h G) as [|] eqn:Hcol.
        -- simpl. rewrite Hcol.
           apply duplicate_graph_maintains_single_collider with (o := o) in Hcol.
           rewrite Hcol. simpl. f_equal. specialize (IH h v). apply IH. apply Ho.
        -- simpl. rewrite Hcol.
           apply duplicate_graph_maintains_single_collider_f with (o := o) in Hcol.
           rewrite Hcol. simpl. specialize (IH h v). apply IH. apply Ho.
Qed.

Lemma duplicate_graph_maintains_dir_paths: forall (u v: node) (l: nodes) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  is_directed_path_in_graph (u, v, l) G = true <->
  is_directed_path_in_graph (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G) = true.
Proof.
  intros u v l G o Ho.
  unfold is_directed_path_in_graph.
  generalize dependent v. generalize dependent u.
  induction l as [| h t IH].
  - intros u v. simpl. split.
    + intros H. rewrite andb_comm in H. simpl in H.
      apply duplicate_graph_maintains_edges with (o := o) in H.
      unfold node in *. rewrite H. reflexivity. apply Ho.
    + intros H. rewrite andb_comm in H. simpl in H.
      apply duplicate_graph_maintains_edges in H. rewrite H. reflexivity. apply Ho.
  - intros u v. split.
    + simpl. intros Hdir. destruct (is_edge (u, h) G) as [|] eqn:Hedge.
      * simpl in Hdir. apply duplicate_graph_maintains_edges with (o := o) in Hedge.
        unfold node in *. rewrite Hedge. simpl. specialize (IH h v). apply IH. apply Hdir. apply Ho.
      * simpl in Hdir. discriminate Hdir.
    + simpl. intros Hdir. destruct (is_edge (u + o, h + o) (duplicate_graph G)) as [|] eqn:Hedge.
      * unfold node in *. rewrite Hedge in Hdir. simpl in Hdir. apply duplicate_graph_maintains_edges in Hedge.
        unfold node in *. rewrite Hedge. simpl. specialize (IH h v). apply IH. apply Hdir. apply Ho.
      * unfold node in *. rewrite Hedge in Hdir. simpl in Hdir. discriminate Hdir.
Qed.

Lemma duplicate_graph_shifts_dir_paths: forall (u' v': node) (l': nodes) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  is_directed_path_in_graph (u', v', l') (duplicate_graph G) = true ->
  exists u v l, u' = u + o /\ v' = v + o /\ l' = shift_nodes_by_offset l o.
Proof.
  intros u' v' l' G o Ho Hdir.
  generalize dependent v'. generalize dependent u'.
  induction l' as [| h t IH].
  - intros u' v' Hdir. simpl in Hdir. rewrite andb_comm in Hdir. simpl in Hdir.
    exists (u' - o). exists (v' - o). exists [].
    unfold is_edge in Hdir. destruct G as [V E]. simpl in Hdir.
    apply split_and_true in Hdir. destruct Hdir as [Hmem Hedge].
    apply split_and_true in Hmem. destruct Hmem as [Hu' Hv']. simpl in Ho.
    repeat split.
    + rewrite <- Ho in Hu'. apply member_In_equiv in Hu'.
      apply twin_nodes_greater_than_offset in Hu'. lia.
    + rewrite <- Ho in Hv'. apply member_In_equiv in Hv'.
      apply twin_nodes_greater_than_offset in Hv'. lia.
  - intros u' v' Hdir. simpl in Hdir.
    destruct (is_edge (u', h) (duplicate_graph G)) as [|] eqn:Hedge.
    + unfold is_edge in Hedge. destruct G as [V E]. simpl in Hedge.
      apply split_and_true in Hedge. destruct Hedge as [Hmem Hedge].
      apply split_and_true in Hmem. destruct Hmem as [Hu' Hh']. simpl in Ho.
      simpl in Hdir. specialize (IH h v'). apply IH in Hdir.
      destruct Hdir as [h1 [v [t' [Hh [Hv Ht]]]]].
      exists (u' - o), v, ((h - o) :: t'). repeat split.
      * rewrite <- Ho in Hu'. apply member_In_equiv in Hu'.
        apply twin_nodes_greater_than_offset in Hu'. lia.
      * apply Hv.
      * simpl. assert (Hho: h = h - o + o).
        { rewrite <- Ho in Hh'. apply member_In_equiv in Hh'.
          apply twin_nodes_greater_than_offset in Hh'. lia. }
        rewrite <- Hho. f_equal. apply Ht.
    + simpl in Hdir. discriminate Hdir.
Qed.

Lemma duplicate_graph_maintains_descendants: forall (u: node) (G: graph) (o: nat) (d: node),
  o = max_node_in_graph G ->
  In d (find_descendants u G) <->
  In (d + o) (find_descendants (u + o) (duplicate_graph G)).
Proof.
  intros u G o d Ho. split.
  - intros Hd. apply find_descendants_correct in Hd. destruct Hd as [Hd | Hd].
    apply find_descendants_correct. left. lia.
    destruct Hd as [p [Hdir Hse]].
    destruct p as [[u' d'] l]. apply path_start_end_equal in Hse. destruct Hse as [Hu Hd].
    apply find_descendants_correct. right.
    exists (u + o, d + o, shift_nodes_by_offset l o). split.
    + rewrite Hu in Hdir. rewrite Hd in Hdir.
      apply duplicate_graph_maintains_dir_paths with (o := o) in Hdir. apply Hdir. apply Ho.
    + apply path_start_end_refl.
  - intros Hd. apply find_descendants_correct in Hd. destruct Hd as [Hd | Hd].
    apply find_descendants_correct. left. lia.
    destruct Hd as [p' [Hdir Hse]].
    destruct p' as [[u' d'] l'].
    apply duplicate_graph_shifts_dir_paths with (o := o) in Hdir as Huvl.
    destruct Huvl as [u1 [d1 [l [Hu1 [Hd1 Hl]]]]].
    apply path_start_end_equal in Hse. destruct Hse as [Hu Hd].
    + apply find_descendants_correct. right. exists (u, d, l). split.
      * rewrite Hu in Hdir. rewrite Hd in Hdir. rewrite Hl in Hdir.
        apply duplicate_graph_maintains_dir_paths in Hdir. apply Hdir. apply Ho.
      * apply path_start_end_refl.
    + apply Ho.
Qed.

Theorem duplicate_graph_maintains_independence: forall G: graph, forall u v o: node, forall Z: nodes,
  o = max_node_in_graph G ->
  (exists p: path, path_start_and_end p u v = true
                  /\ node_in_graph u G = true /\ node_in_graph v G = true 
                  /\ d_connected_2 p G Z)
  <->
  (exists p': path, path_start_and_end p' (u + o) (v + o) = true /\ (exists int: nodes, path_int p' = shift_nodes_by_offset int o)
                  /\ node_in_graph (u + o) (duplicate_graph G) = true /\ node_in_graph (v + o) (duplicate_graph G) = true
                  /\ d_connected_2 p' (duplicate_graph G) (shift_nodes_by_offset Z o)).
Proof.
  intros G u v o Z. intros Ho. split.
  - intros [p [Hp [Hu [Hv Hconn]]]]. destruct p as [[u' v'] l]. apply path_start_end_equal in Hp. destruct Hp as [Hu' Hv'].
    rewrite Hu' in Hconn. rewrite Hv' in Hconn.
    exists (u + o, v + o, shift_nodes_by_offset l o).
    unfold d_connected_2. unfold d_connected_2 in Hconn. destruct Hconn as [Hmed [Hconf Hcol]]. repeat split.
    + apply path_start_end_refl.
    + exists l. simpl. reflexivity.
    + destruct G as [V E]. simpl. simpl in Hu. simpl in Ho. rewrite <- Ho.
      apply twin_nodes_duplicated. apply Hu.
    + destruct G as [V E]. simpl. simpl in Hv. simpl in Ho. rewrite <- Ho.
      apply twin_nodes_duplicated. apply Hv.
    + (* mediators *)
      apply shift_maintains_overlap with (o := o) in Hmed.
      apply no_overlap_non_member.
      intros x Hxmed HxZ.
      assert (Hol: forall x: node,
                   In x (shift_nodes_by_offset (find_mediators_in_path (u, v, l) G) o) -> ~(In x (shift_nodes_by_offset Z o))).
      { apply no_overlap_non_member. apply Hmed. }
      specialize (Hol x). apply Hol.
      { remember (x - o) as y.
        assert (Hox: o <= x). { apply shift_greater_than_offset in HxZ. apply HxZ. }
      replace x with (y + o) in Hxmed.
      * apply duplicate_graph_maintains_mediators with (x := y) in Hxmed.
        -- rewrite Heqy in Hxmed. apply shift_member. split. apply Hxmed. apply Hox.
        -- apply Ho.
      * rewrite Heqy. lia. }
      apply HxZ.
    + (* confounders *)
      apply shift_maintains_overlap with (o := o) in Hconf.
      apply no_overlap_non_member.
      intros x Hxconf HxZ.
      assert (Hol: forall x: node,
                   In x (shift_nodes_by_offset (find_confounders_in_path (u, v, l) G) o) -> ~(In x (shift_nodes_by_offset Z o))).
      { apply no_overlap_non_member. apply Hconf. }
      specialize (Hol x). apply Hol.
      { remember (x - o) as y.
        assert (Hox: o <= x). { apply shift_greater_than_offset in HxZ. apply HxZ. }
      replace x with (y + o) in Hxconf.
      * apply duplicate_graph_maintains_confounders with (x := y) in Hxconf.
        -- rewrite Heqy in Hxconf. apply shift_member. split. apply Hxconf. apply Hox.
        -- apply Ho.
      * rewrite Heqy. lia. }
      apply HxZ.
    + (* colliders *)
      unfold all_colliders_have_descendant_conditioned_on. apply forallb_forall.
      intros c' Hmem. unfold some_descendant_in_Z_bool.
      unfold all_colliders_have_descendant_conditioned_on in Hcol.
      replace (find_colliders_in_path (u + o, v + o, shift_nodes_by_offset l o)
          (duplicate_graph G)) with (shift_nodes_by_offset (find_colliders_in_path (u, v, l) G) o) in Hmem.
      apply shift_member in Hmem.
      destruct Hmem as [Hmem Hoc].
      assert (Hc': exists c, c' = c + o).
      { exists (c' - o). lia. }
      destruct Hc' as [c Hc'].
      assert (Hc: c = c' - o). { lia. } rewrite <- Hc in Hmem.
      assert (Hdesc: some_descendant_in_Z_bool (find_descendants c G) Z = true).
      { apply forallb_true with (l := (find_colliders_in_path (u, v, l) G))
              (test := (fun c: node => some_descendant_in_Z_bool (find_descendants c G) Z)).
        - apply Hmem.
        - apply Hcol. }
      unfold some_descendant_in_Z_bool in Hdesc.
      apply overlap_has_member_in_common in Hdesc. destruct Hdesc as [d [Hdesc HdZ]].
      remember (d + o) as d'.
      assert (Hdesc': In d' (find_descendants c' (duplicate_graph G))).
      { rewrite Hc'. rewrite Heqd'. apply duplicate_graph_maintains_descendants.
        - apply Ho.
        - apply Hdesc. }
      assert (HdZ': In d' (shift_nodes_by_offset Z o)).
      { apply shift_member. split.
        - assert (Hd': d' - o = d). { lia. } rewrite <- Hd' in HdZ. apply HdZ.
        - lia. }
      apply overlap_has_member_in_common. exists d'. split.
      * apply Hdesc'.
      * apply HdZ'.
      * symmetry. apply duplicate_graph_maintains_colliders. apply Ho.
  - intros [p' [Hp [[l Hi] [Hu [Hv Hconn]]]]]. destruct p' as [[u' v'] l']. simpl in Hi.
    apply path_start_end_equal in Hp. destruct Hp as [Hu' Hv'].
    rewrite Hu' in Hconn. rewrite Hv' in Hconn.
    exists (u, v, l).
    unfold d_connected_2. unfold d_connected_2 in Hconn. destruct Hconn as [Hmed [Hconf Hcol]]. repeat split.
    + apply path_start_end_refl.
    + destruct G as [V E]. simpl. simpl in Hu. simpl in Ho. rewrite <- Ho in Hu.
      apply twin_nodes_duplicated in Hu. apply Hu.
    + destruct G as [V E]. simpl. simpl in Hv. simpl in Ho. rewrite <- Ho in Hv.
      apply twin_nodes_duplicated in Hv. apply Hv.
    + (* mediators *)
      apply no_overlap_non_member. intros m Hm HmZ.
      assert (Hm': In (m + o) (find_mediators_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G))).
      { apply duplicate_graph_maintains_mediators. apply Ho. apply Hm. }
      rewrite <- Hi in Hm'.
      assert (HmZ': In (m + o) (shift_nodes_by_offset Z o)).
      { remember (m + o) as m'. apply shift_member. split.
        - replace (m' - o) with m. apply HmZ. lia.
        - lia. }
      assert (contra: overlap (shift_nodes_by_offset Z o)
         (find_mediators_in_path (u + o, v + o, l') (duplicate_graph G)) = true).
      { apply overlap_has_member_in_common. exists (m + o). split.
        - apply HmZ'.
        - apply Hm'. }
      unfold node in Hmed. rewrite Hmed in contra. discriminate contra.
    + (* confounders *)
      apply no_overlap_non_member. intros c Hc HcZ.
      assert (Hc': In (c + o) (find_confounders_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G))).
      { apply duplicate_graph_maintains_confounders. apply Ho. apply Hc. }
      rewrite <- Hi in Hc'.
      assert (HcZ': In (c + o) (shift_nodes_by_offset Z o)).
      { remember (c + o) as c'. apply shift_member. split.
        - replace (c' - o) with c. apply HcZ. lia.
        - lia. }
      assert (contra: overlap (shift_nodes_by_offset Z o)
         (find_confounders_in_path (u + o, v + o, l') (duplicate_graph G)) = true).
      { apply overlap_has_member_in_common. exists (c + o). split.
        - apply HcZ'.
        - apply Hc'. }
      unfold node in Hconf. rewrite Hconf in contra. discriminate contra.
    + (* colliders *)
      unfold all_colliders_have_descendant_conditioned_on. apply forallb_forall.
      intros c Hmem. unfold some_descendant_in_Z_bool.
      unfold all_colliders_have_descendant_conditioned_on in Hcol.
      remember (c + o) as c'.
      assert (Hc': In c' (shift_nodes_by_offset (find_colliders_in_path (u, v, l) G) o)).
      { apply shift_member. split.
        - assert (Hc: c = c' - o). { lia. }
          rewrite <- Hc. apply Hmem.
        - lia. }
      replace (shift_nodes_by_offset (find_colliders_in_path (u, v, l) G) o) with
          (find_colliders_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G)) in Hc'.
      * assert (Hdesc: some_descendant_in_Z_bool (find_descendants c' (duplicate_graph G))
            (shift_nodes_by_offset Z o) = true).
        { apply forallb_true with (l := (find_colliders_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G)))
              (test := (fun c: node => some_descendant_in_Z_bool (find_descendants c (duplicate_graph G))
                (shift_nodes_by_offset Z o))) (x := c').
          - apply Hc'.
          - rewrite <- Hi. apply Hcol. }
        unfold some_descendant_in_Z_bool in Hdesc.
        apply overlap_has_member_in_common in Hdesc. destruct Hdesc as [d' [Hdesc' HdZ']].
        remember (d' - o) as d.
        assert (Hdesc: In d (find_descendants c G)).
        { apply duplicate_graph_maintains_descendants with (o := o).
          - apply Ho.
          - rewrite <- Heqc'.
            assert (Hd': d' = d + o).
            { assert (Hdo': o <= d'). { apply shift_greater_than_offset in HdZ'. apply HdZ'. }
              lia. }
            rewrite <- Hd'. apply Hdesc'. }
        assert (HdZ: In d Z).
        { apply shift_member in HdZ'. destruct HdZ' as [HdZ' Hod'].
          rewrite <- Heqd in HdZ'. apply HdZ'. }
        apply overlap_has_member_in_common. exists d. split.
        -- apply Hdesc.
        -- apply HdZ.
      * apply duplicate_graph_maintains_colliders. apply Ho.
Qed.

(* add unobserved confounders of each pair of corresponding nodes *)
Fixpoint get_unobserved_nodes_and_edges
  (V: nodes) (E: edges) (new_nodes: nodes) (new_edges: edges) (o: nat): graph :=
  match V with
  | [] => (new_nodes, new_edges)
  | h :: t => get_unobserved_nodes_and_edges t E ((h + o + o) :: new_nodes) ((h + o + o, h) :: (h + o + o, h + o) :: new_edges) o
  end.

(* create graph that duplicates original graph and adds unobserved nodes/edges *)
Definition create_duplicate_network (G: graph): graph :=
  match G with
  | (V, E) => let unobs := get_unobserved_nodes_and_edges V E [] [] (max_list V) in
              let dup := duplicate_graph G in
              (V ++ (fst dup) ++ (fst unobs), E ++ (snd dup) ++ (snd unobs))
  end.

Example duplicate_network_1: create_duplicate_network ([1; 2; 3], [(1, 2); (3, 2)])
  = ([1;2;3;4;5;6;9;8;7], [(1,2); (3,2); (4,5); (6,5); (9,3); (9,6); (8,2); (8,5); (7,1); (7,4)]).
Proof. reflexivity. Qed.

Fixpoint do_several (G: graph) (fixed: nodes): graph :=
  match fixed with
  | [] => G
  | h :: t => do_several (do h G) t
  end.

Fixpoint remove_unobserved (original_V: nodes) (new_nodes: nodes) (new_edges: edges) (o: nat) : graph :=
  match original_V with
  | [] => (new_nodes, new_edges)
  | h :: t => if (member_edge (h + o + o, h) new_edges && member_edge (h + o + o, h + o) new_edges) then remove_unobserved t new_nodes new_edges o
              else remove_unobserved t (filter (fun x => negb (x  =? h + o + o)) new_nodes) (filter (fun x => negb (fst x =? h + o + o)) new_edges) o
  end.

Definition create_initial_twin_network {X: Type} (G: graph) (obs: assignments X) (cf: assignments X): graph :=
  match G with
  | (V, E) => let duplicate_G := create_duplicate_network G in
              (do_several (do_several duplicate_G (fsts obs)) (shift_list (fsts cf) (max_list V)))
  end.

Example twin_1: create_initial_twin_network ([1;2;3], [(1, 2); (3, 2)]) [] [(1, 70)]
  = ([1;2;3;4;5;6;9;8;7], [(1,2); (3,2); (4,5); (6,5); (9,3); (9,6); (8,2); (8,5); (7,1)]).
Proof. reflexivity. Qed.

Definition create_twin_network_before_preprocess {X: Type} (G: graph) (obs cf: assignments X): graph :=
  let init := create_initial_twin_network G obs cf in
  match G with
  | (V, E) => remove_unobserved V (fst init) (snd init) (max_list V)
  end.

Definition sequential_V: nodes := [1; 2; 3; 4; 5]. (* [A, H, B, Z, Y] *)
Definition sequential_E: edges := [(1, 4); (2, 4); (2, 3); (4, 3); (4, 5); (3, 5)].
Definition sequential_G: graph := (sequential_V, sequential_E).

Definition sequential_twin: graph := create_twin_network_before_preprocess sequential_G [] [(1, 1); (3, 2)].
Example sequential_twin_network: sequential_twin (* fix counterfactuals a=1, b=2 *)
  = ([1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 14; 12], sequential_E ++ [(6, 9); (7, 9); (9, 10); (8, 10)] ++ [(15, 5); (15, 10); (14, 4); (14, 9); (12, 2); (12, 7)]).
Proof. reflexivity. Qed.

Example sequential_twin_network_error: d_separated_bool 10 3 sequential_twin [4;1] = false.
Proof.
  apply d_separated_vs_connected.
  exists [9; 7; 12; 2].
  split.
  - simpl. split. easy. split.
    + intros H. destruct H as [H | [H | [H | [H | H]]]]. discriminate H. discriminate H. discriminate H. discriminate H. apply H.
    + split. intros H. destruct H as [H | [H | [H | [H | H]]]]. discriminate H. discriminate H. discriminate H. discriminate H. apply H. reflexivity.
  - split.
    + simpl. reflexivity.
    + unfold d_connected_2. split.
      * simpl. reflexivity.
      * split.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
Qed.


(*
PREPROCESSING:

compute topological ordering of original graph

for each node v in topo order:
  if for v and v', 1) parents are the same; 2) not both assigned a different value:
    merge v and v' into single node
    remove u if necessary
*)