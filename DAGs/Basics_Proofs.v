From DAGs Require Import Basics_Constr.
From Utils Require Import Lists.
From Utils Require Import Logic.

Require Import Stdlib.Structures.Equalities.
Import ListNotations.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Classical.
Require Import Stdlib.Logic.FunctionalExtensionality.


(* this file proves theorems about the types and functions defined in DAG_Basic_Constr *)


(* simple theorems about edges *)
Theorem eqbedge_refl : forall e: edge,
  true = eqbedge e e.
Proof.
  intros e.
  destruct e as [u v]. simpl.
  rewrite -> eqb_refl. rewrite -> eqb_refl. simpl.
  reflexivity.
Qed.

Lemma member_edge_In_equiv :
  forall (l : edges) (x: edge), member_edge x l = true <-> In x l.
Proof.
  intros l x.
  split.
  - intros H. induction l as [| h t IH].
    + simpl in H. discriminate H.
    + simpl in H. simpl. destruct (eqbedge h x) as [|] eqn:Hhx.
      * left. destruct h as [h1 h2]. destruct x as [x1 x2].
        simpl in Hhx. apply split_and_true in Hhx. destruct Hhx as [H1 H2].
        apply eqb_eq in H1. rewrite H1. apply eqb_eq in H2. rewrite H2. reflexivity.
      * right. apply IH. apply H.
  - intros H. induction l as [| h t IH].
    + simpl in H. exfalso. apply H.
    + simpl. simpl in H. destruct H as [H | H].
      * rewrite H. rewrite <- eqbedge_refl. reflexivity.
      * destruct (eqbedge h x) as [|] eqn:Hhx.
        -- reflexivity.
        -- apply IH. apply H.
Qed.

Lemma member_edge_In_equiv_false :
  forall (l : edges) (x: edge), member_edge x l = false <-> ~(In x l).
Proof.
  intros l x.
  split.
  - intros Hmem HIn. apply member_edge_In_equiv in HIn. rewrite Hmem in HIn. discriminate HIn.
  - intros HIn. unfold not in HIn. destruct (member_edge x l) as [|] eqn:Hmem.
    + exfalso. apply HIn. apply member_edge_In_equiv. apply Hmem.
    + reflexivity.
Qed.

Theorem eqbpath_refl : forall p: path,
  true = eqbpath p p.
Proof.
  intros p.
  destruct p as [[u v] l]. simpl.
  rewrite -> eqb_refl. rewrite -> eqb_refl. simpl.
  rewrite <- eqblist_refl.
  reflexivity.
Qed.

Lemma count_edge_filter: forall (l: edges) (x: edge) (test : edge -> bool),
  test x = true -> count_edge x l = count_edge x (filter test l).
Proof.
  intros l x test H.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (eqbedge h x) as [|] eqn:Hhx.
    + destruct h as [h1 h2]. destruct x as [x1 x2]. simpl in Hhx. apply split_and_true in Hhx. destruct Hhx as [H1 H2].
      apply eqb_eq in H1. rewrite H1 in *. apply eqb_eq in H2. rewrite H2 in *. rewrite H. simpl. rewrite eqb_refl. rewrite eqb_refl. simpl.
      f_equal. apply IH.
    + destruct (test h) as [|] eqn:Hh.
      * simpl. rewrite Hhx. apply IH.
      * apply IH.
Qed.



(* theorems about the well-formedness of graphs, as well as relating graphs to
   their corresponding nodes and edges *)
Lemma first_node_appears_once: forall (Z: nodes) (u v: node),
  each_node_appears_once (u :: Z) /\ In v Z -> (u =? v) = false.
Proof.
  intros Z u v [Hu Hv].
  unfold each_node_appears_once in Hu.
  destruct (u =? v) as [|] eqn:Huv.
  - specialize Hu with (u := v). simpl in Hu. rewrite Huv in Hu.
    assert (S (count v Z) = 1). { apply Hu. right. apply Hv. } inversion H. clear H.
    apply member_count_at_least_1 in Hv. rewrite H1 in Hv. lia.
  - reflexivity.
Qed.

Lemma remove_node_from_well_formed: forall (V: nodes) (E: edges) (u: node),
  node_in_graph u (V, E) = true /\ G_well_formed (V, E) = true -> length V = S (length (remove_node u V)).
Proof.
  intros V E u [Hu HG].
  unfold G_well_formed in HG. apply count_length. apply split_and_true in HG. destruct HG as [HG _]. apply split_and_true in HG. destruct HG as [_ HG]. apply forallb_true with (x := u) in HG.
  - apply eqb_eq. apply HG.
  - simpl in Hu. apply member_In_equiv. apply Hu.
Qed.

Lemma remove_node_preserves_well_formed: forall (G: graph) (u: node),
  G_well_formed G = true -> G_well_formed (remove_node_from_graph G u) = true.
Proof.
  intros [V E] u H.
  unfold G_well_formed. simpl.
  unfold G_well_formed in H. apply split_and_true in H. destruct H as [He Hec]. apply split_and_true in He. destruct He as [He Hv].
  assert (He': forallb
    (fun e : nat * nat =>
     let (u0, v) := e in
     member u0 (remove_node u V) && member v (remove_node u V))
    (remove_associated_edges u E) = true).
  { apply forallb_true_iff_mem. intros [e1 e2]. intros Hmem.
    unfold remove_associated_edges in Hmem. apply filter_true in Hmem.
    destruct Hmem as [Hmem Heq].
    simpl in Heq. apply split_and_true in Heq. destruct Heq as [He2 He1].
    unfold remove_node.
    assert (HVmem: forall x: nat * nat, In x E -> (let (u, v) := x in member u V && member v V) = true).
    { apply forallb_true_iff_mem. apply He. }
    specialize HVmem with (x := (e1, e2)). apply HVmem in Hmem.
    apply split_and_true in Hmem. destruct Hmem as [He1V He2V].
    assert (He1mem: In e1 (filter (fun v : nat => negb (v =? u)) V)).
    { apply filter_true. split.
      - apply member_In_equiv. apply He1V.
      - apply He1. }
    assert (He2mem: In e2 (filter (fun v : nat => negb (v =? u)) V)).
    { apply filter_true. split.
      - apply member_In_equiv. apply He2V.
      - apply He2. }
    apply member_In_equiv in He1mem. apply member_In_equiv in He2mem.
    rewrite He1mem. rewrite He2mem. reflexivity. }
  rewrite He'. simpl. apply split_and_true. split.
  { apply forallb_true_iff_mem. intros x Hmem.
    unfold remove_node in Hmem. apply filter_true in Hmem. destruct Hmem as [Hmem Hxu].
    unfold remove_node.
    assert (H: count x V = count x (filter (fun v : nat => negb (v =? u)) V)).
    { apply count_filter. apply Hxu. }
    rewrite <- H.
    assert (HVc: forall x: nat, In x V -> (count x V =? 1) = true).
    { apply forallb_true_iff_mem. apply Hv. }
    specialize HVc with (x := x). apply HVc in Hmem. apply Hmem. }
  apply forallb_true_iff_mem. intros x Hmem.
  apply filter_true in Hmem. destruct Hmem as [Hmem Hxu].
  unfold remove_associated_edges.
  assert (H: count_edge x E = count_edge x
   (filter
      (fun edg : nat * nat =>
       negb (snd edg =? u) && negb (fst edg =? u)) E)).
  { apply count_edge_filter. apply Hxu. }
  rewrite <- H.
  assert (HVc: forall x: edge, In x E -> (count_edge x E =? 1) = true).
  { apply forallb_true_iff_mem. apply Hec. }
  specialize HVc with (x := x). apply HVc in Hmem. apply Hmem.
Qed.

Theorem edge_corresponds_to_nodes_in_well_formed: forall (G: graph) (u v: node),
  G_well_formed G = true /\ edge_in_graph (u, v) G = true
  -> node_in_graph u G = true /\ node_in_graph v G = true.
Proof.
  intros [V E] u v [HG Hedge].
  unfold G_well_formed in HG. apply split_and_true in HG. destruct HG as [HG _]. apply split_and_true in HG. destruct HG as [HG _].
  apply forallb_true with (x:=(u,v)) in HG.
  - apply split_and_true in HG. destruct HG as [Hu Hv]. simpl.
    rewrite Hu. rewrite Hv. split. reflexivity. reflexivity.
  - simpl in Hedge. apply member_edge_In_equiv. apply Hedge.
Qed.

Theorem no_self_loops : forall E: edges, forall u v: node,
  member_edge (u, v) E = true -> no_one_cycles E = true -> u <> v.
Proof.
  intros E u v Hmem Hcyc.
  induction E as [| h t IH].
  - simpl in Hmem. discriminate Hmem.
  - simpl in Hmem. destruct (eqbedge h (u, v)) as [|] eqn:Hedge.
    + simpl in Hcyc. destruct (u =? v) as [|] eqn:Huv.
      * destruct h as [a b]. simpl in Hedge. apply split_and_true in Hedge.
        destruct Hedge as [Hau Hbv].
        apply eqb_eq in Huv. rewrite <- Huv in Hbv.
        apply eqb_eq in Hbv. rewrite <-  Hbv in Hau.
        rewrite Hau in Hcyc. discriminate Hcyc.
      * apply eqb_neq in Huv. apply Huv.
    + simpl in Hcyc. destruct (u =? v) as [|] eqn:Huv.
      * destruct h as [a b]. simpl in Hedge. destruct (a =? b) as [|] eqn:Hab.
        -- discriminate Hcyc.
        -- apply IH. apply Hmem. apply Hcyc.
      * apply eqb_neq in Huv. apply Huv.
Qed.

Theorem is_edge_then_node_in_graph: forall (G: graph) (u v: node),
  is_edge (u, v) G = true \/ is_edge (v, u) G = true
  -> node_in_graph u G = true.
Proof.
  intros G u v [Huv | Hvu].
  - destruct G as [V E]. unfold is_edge in Huv. apply split_and_true in Huv. destruct Huv as [Huv _].
    apply split_and_true in Huv. destruct Huv as [Huv _]. simpl. apply Huv.
  - destruct G as [V E]. unfold is_edge in Hvu. apply split_and_true in Hvu. destruct Hvu as [Huv _].
    apply split_and_true in Huv. destruct Huv as [_ Huv]. simpl. apply Huv.
Qed.


(* the following two theorems are for convenience, allowing us to switch between
   the edge_in_graph and is_edge functions easily *)
Theorem edge_in_graph_then_is_edge: forall (G: graph) (u v: node),
  G_well_formed G = true
  -> edge_in_graph (u, v) G = true
  -> is_edge (u, v) G = true.
Proof.
  intros G u v HG Huv.
  unfold is_edge.
  assert (Hnode: node_in_graph u G = true /\ node_in_graph v G = true).
  { apply edge_corresponds_to_nodes_in_well_formed. split. apply HG. apply Huv. }
  destruct G as [V E].
  simpl in Huv. rewrite Huv.
  simpl in Hnode. destruct Hnode as [H1 H2]. rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem edge_in_graph_equiv: forall (G: graph) (u v: node),
  G_well_formed G = true
  -> is_edge (u, v) G = edge_in_graph (u, v) G.
Proof.
  intros G u v HG.
  destruct (edge_in_graph (u, v) G) as [|] eqn:Huv.
  - apply edge_in_graph_then_is_edge in Huv. apply Huv. apply HG.
  - unfold is_edge. destruct G as [V E]. simpl in Huv. rewrite Huv. rewrite andb_comm. simpl. reflexivity.
Qed.




(* simple theorems about paths and the nodes that they include *)

Theorem path_start_end_refl: forall u v: node, forall l: nodes,
  path_start_and_end (u, v, l) u v = true.
Proof.
  intros u v l.
  unfold path_start_and_end. simpl. rewrite eqb_refl. simpl. apply eqb_refl.
Qed.

Theorem path_start_end_equal: forall u v A B: node, forall l: nodes,
  path_start_and_end (u, v, l) A B = true -> u = A /\ v = B.
Proof.
  intros u v A B l.
  intros H. unfold path_start_and_end in H. apply split_and_true in H. destruct H.
  simpl in H. apply eqb_eq in H.
  simpl in H0. apply eqb_eq in H0.
  split. apply H. apply H0.
Qed.

Lemma node_in_path_equiv: forall (u v x: node) (l: nodes),
  node_in_path x (u, v, l) = member x (u :: l ++ [v]).
Proof.
  intros u v x l. unfold node_in_path. simpl.
  destruct (x =? u) as [|] eqn:Hxu.
  - rewrite eqb_sym in Hxu. rewrite Hxu. simpl. reflexivity.
  - rewrite eqb_sym in Hxu. rewrite Hxu. simpl. destruct (x =? v) as [|] eqn:Hxv.
    + simpl. symmetry. apply member_In_equiv. apply membership_append_r. left. apply eqb_eq. rewrite eqb_sym. apply Hxv.
    + simpl. destruct (member x l) as [|] eqn:Hmem.
      * symmetry. apply member_In_equiv. apply membership_append. apply member_In_equiv. apply Hmem.
      * symmetry. apply member_In_equiv_F. intros F. apply membership_append_or in F. destruct F as [F | [F | F]].
        -- apply member_In_equiv_F in Hmem. apply Hmem. apply F.
        -- rewrite F in Hxv. rewrite eqb_refl in Hxv. discriminate Hxv.
        -- apply F.
Qed.

Lemma node_in_path_cat: forall (u v h w: node) (t: nodes),
  (w =? u) = false
  -> node_in_path w (h, v, t) = node_in_path w (u, v, h :: t).
Proof.
  intros u v h w t H.
  unfold node_in_path. simpl. rewrite H. simpl. destruct (w =? h) as [|] eqn:Hwh.
  - simpl. rewrite eqb_sym in Hwh. rewrite Hwh. rewrite orb_comm. reflexivity.
  - simpl. rewrite eqb_sym in Hwh. rewrite Hwh. reflexivity.
Qed.

Lemma first_node_in_path_in_graph: forall (G: graph) (l: nodes) (s e: node),
  is_path_in_graph_helper ((s :: l) ++ [e]) G = true -> node_in_graph s G = true.
Proof.
  intros G l s e Hpath.
  destruct G as [V E].
  simpl in Hpath. destruct (l ++ [e]) as [| h t] eqn:Hl.
  * destruct l as [| h' t'].
    -- simpl in Hl. discriminate Hl.
    -- simpl in Hl. discriminate Hl.
  * apply split_and_true in Hpath. destruct Hpath as [Hpath _].
    apply split_orb_true in Hpath as [Hpath | Hpath].
    -- apply split_and_true in Hpath. destruct Hpath as [Hpath _].
       apply split_and_true in Hpath. destruct Hpath as [Hpath _].
       simpl. apply Hpath.
    -- apply split_and_true in Hpath. destruct Hpath as [Hpath _].
       apply split_and_true in Hpath. destruct Hpath as [_ Hpath].
       simpl. apply Hpath.
Qed.

Lemma last_node_in_path_in_graph: forall (G: graph) (l: nodes) (s e: node),
  (length ((s :: l) ++ [e]) > 1) /\ is_path_in_graph_helper ((s :: l) ++ [e]) G = true -> node_in_graph e G = true.
Proof.
  intros G l s e [Hlen Hpath].
  induction (s :: l) as [| h t IH].
  - simpl in Hlen. lia.
  - destruct t as [| h' t'].
    + simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [H _].
      apply split_orb_true in H. destruct H as [H | H].
      * unfold is_edge in H. apply split_and_true in H. destruct H as [H _].
        apply split_and_true in H. destruct H as [_ H]. simpl. apply H.
      * unfold is_edge in H. apply split_and_true in H. destruct H as [H _].
        apply split_and_true in H. destruct H as [H _]. simpl. apply H.
    + apply IH.
      * simpl. rewrite length_app. simpl. lia.
      * simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ H]. apply H.
Qed.

Lemma middle_node_in_path_in_graph: forall (G: graph) (l: nodes) (s x e: node),
  In x (s :: l) -> (length ((s :: l) ++ [e]) > 1) /\ is_path_in_graph_helper ((s :: l) ++ [e]) G = true -> node_in_graph x G = true.
Proof.
  intros G l s x e Hmem [Hlen Hpath].
  induction (s :: l) as [| h t IH].
  - simpl in Hlen. lia.
  - simpl in Hmem. destruct Hmem as [Hhx | Hmem].
    + rewrite <- Hhx. apply first_node_in_path_in_graph with (s := h) (l := t) (e := e). apply Hpath.
    + destruct t as [| h1 t1].
      * simpl in Hmem. exfalso. apply Hmem.
      * apply IH.
        -- apply Hmem.
        -- simpl. rewrite length_app. simpl. lia.
        -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ H].
           apply H.
Qed.

Lemma nodes_in_graph_in_V: forall (G: graph) (p: path) (u: node),
  node_in_path u p = true /\ is_path_in_graph p G = true -> node_in_graph u G = true.
Proof.
  intros G [[s e] l] u. intros [Hnode Hpath].
  unfold node_in_path in Hnode. apply split_orb_true in Hnode. destruct Hnode as [Hse | Hint].
  - apply split_orb_true in Hse. destruct Hse as [Hs | He].
    + simpl in Hs. unfold is_path_in_graph in Hpath. destruct G as [V E].
      apply eqb_eq in Hs. rewrite Hs.
      apply first_node_in_path_in_graph with (l := l) (e := e). apply Hpath.
    + simpl in He. unfold is_path_in_graph in Hpath. destruct G as [V E].
      apply eqb_eq in He. rewrite He.
      apply last_node_in_path_in_graph with (s := s) (l := l). split.
      * simpl. rewrite length_app. simpl. lia.
      * apply Hpath.
  - simpl in Hint. unfold is_path_in_graph in Hpath. destruct G as [V E].
    apply middle_node_in_path_in_graph with (x := u) (s := s) (l := l) (e := e).
    + simpl. right. apply member_In_equiv. apply Hint.
    + split.
      * simpl. rewrite length_app. simpl. lia.
      * apply Hpath.
Qed.


Lemma two_paths_first_edge_correct : forall G: graph, forall a b c: node,
  is_path_in_graph (a, b, [c]) G = true -> is_edge (a, c) G = true \/ is_edge (c, a) G = true.
Proof.
  intros G a b c.
  intros Hpath.
  destruct (is_edge (a, c) G) as [|] eqn:Hac.
  - left. reflexivity.
  - right. simpl in Hpath. rewrite Hac in Hpath. destruct G as [V E].
    rewrite orb_false_l in Hpath. apply andb_true_elim2 in Hpath. apply Hpath.
Qed.

Lemma two_paths_second_edge_correct : forall G: graph, forall a b c: node,
  is_path_in_graph (a, b, [c]) G = true -> is_edge (c, b) G = true \/ is_edge (b, c) G = true.
Proof.
  intros G a b c.
  intros Hpath.
  destruct (is_edge (c, b) G) as [|] eqn:Hcb.
  - left. reflexivity.
  - right. simpl in Hpath. rewrite Hcb in Hpath. destruct G as [V E].
    rewrite andb_comm in Hpath.
    apply andb_true_elim2 in Hpath.
    apply andb_true_elim2 in Hpath.
    rewrite orb_false_l in Hpath. apply Hpath.
Qed.

Theorem two_paths_correct : forall G: graph, forall a b c: node,
  is_path_in_graph (a, b, [c]) G = true -> (is_edge (a, c) G = true \/ is_edge (c, a) G = true) /\
                                             (is_edge (c, b) G = true \/ is_edge (b, c) G = true).
Proof.
  intros G a b c.
  intros Hpath.
  split.
  - apply two_paths_first_edge_correct in Hpath. apply Hpath.
  - apply two_paths_second_edge_correct in Hpath. apply Hpath.
Qed.



(* the following show that other paths based on the given path are also paths in the graph,
   useful for induction proofs *)
Lemma is_path_in_graph_induction: forall (G: graph) (u h v: node) (t: nodes),
  is_path_in_graph (u, v, h :: t) G = true -> is_path_in_graph (h, v, t) G = true.
Proof.
  intros G u h v t Hp.
  simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. apply Hp.
Qed.

Theorem concat_paths_still_a_path: forall u1 mid v2: node, forall l1 l2: nodes, forall G: graph,
  is_path_in_graph (u1, mid, l1) G = true /\ is_path_in_graph (mid, v2, l2) G = true
  -> is_path_in_graph (concat u1 mid v2 l1 l2) G = true.
Proof.
  intros u m v l1 l2 G.
  intros [H1 H2].
  unfold concat.
  generalize dependent u. induction l1 as [| hl1 tl1 IH].
  - intros u H1. simpl. destruct G as [V E]. apply split_and_true. split.
    + simpl in H1. apply split_and_true in H1. apply H1.
    + apply H2.
  - intros u H1. simpl. destruct G as [V E]. apply split_and_true. split.
    + simpl in H1. apply split_and_true in H1. apply H1.
    + apply IH. simpl in H1. apply split_and_true in H1. apply H1.
Qed.

Lemma reverse_path_in_graph: forall (G: graph) (u v: node) (l: nodes),
  is_path_in_graph (u, v, l) G = true -> is_path_in_graph (v, u, rev l) G = true.
Proof.
  intros G u v l. intros H.
  generalize dependent u. induction l as [| h t IH].
  - intros u H. simpl. simpl in H. rewrite orb_comm. apply H.
  - intros u H. specialize IH with (u := h).
    assert (Hind: is_path_in_graph (v, h, rev t) G = true). { apply IH. simpl in H. destruct G as [V E]. apply split_and_true in H. apply H. }
    assert (Hrew: is_path_in_graph (v, u, rev (h :: t)) G = is_path_in_graph (v, u, rev t ++ [h]) G). { simpl. reflexivity. }
    rewrite Hrew.
    apply concat_paths_still_a_path. split. apply Hind. simpl. simpl in H. destruct G as [V E]. apply split_and_true in H. apply split_and_true.
    split. rewrite orb_comm. apply H. reflexivity.
Qed.

Theorem subpath_still_path: forall (w u v: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ is_path_in_graph (w, v, l3) G = true
  -> is_path_in_graph (u, v, l2) G = true.
Proof.
  intros w u v l1 l2 l3 G. intros [Hl Hdir].
  generalize dependent l3. generalize dependent w. induction l1 as [| h t IH].
  - intros w l3 Hl Hdir. simpl in Hl. rewrite <- Hl in Hdir. simpl in Hdir. destruct G as [V E]. apply split_and_true in Hdir. destruct Hdir as [_ Hdir].
    apply Hdir.
  - intros w l3 Hl Hdir. specialize IH with (w := h) (l3 := (t ++ [u] ++ l2)). apply IH.
    + reflexivity.
    + simpl in Hl. rewrite <- Hl in Hdir. simpl in Hdir. destruct G as [V E]. apply split_and_true in Hdir. destruct Hdir as [_ Hdir]. apply Hdir.
Qed.

Theorem subpath_still_path_2: forall (w u v: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ is_path_in_graph (w, v, l3) G = true
  -> is_path_in_graph (w, u, l1) G = true.
Proof.
  intros w u v l1 l2 l3 G. intros [Hl Hdir].
  generalize dependent l3. generalize dependent w. induction l1 as [| h t IH].
  - intros w l3 Hl Hdir. simpl in Hl. rewrite <- Hl in Hdir. simpl in Hdir. destruct G as [V E]. apply split_and_true in Hdir. destruct Hdir as [Hdir _].
    simpl. simpl in Hdir. rewrite Hdir. reflexivity.
  - intros w l3 Hl Hdir. specialize IH with (w := h) (l3 := (t ++ [u] ++ l2)). simpl.
    rewrite <- Hl in Hdir. simpl in Hdir. destruct G as [V E]. apply split_and_true in Hdir. destruct Hdir as [Hdir1 Hdir2]. rewrite Hdir1. simpl. apply IH.
    + reflexivity.
    + apply Hdir2.
Qed.

(* if a node w is in a path of G, then there is a node x such that x->w or w->x is an edge *)
Theorem node_in_path_has_edge: forall (u v w: node) (l: nodes) (G: graph),
  is_path_in_graph (u, v, l) G = true
  -> node_in_path w (u, v, l) = true
  -> exists (x: node), node_in_path x (u, v, l) = true /\ (is_edge (x, w) G = true \/ is_edge (w, x) G = true).
Proof.
  intros u v w l G H.
  generalize dependent u. induction l as [| h t IH].
  - intros u H Hw. unfold node_in_path in Hw. simpl in Hw. apply split_orb_true in Hw. destruct Hw as [Hw | Hw].
    2: { discriminate Hw. } apply split_orb_true in Hw. destruct Hw as [Hw | Hw].
    + exists v. split. unfold node_in_path. simpl. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
      simpl in H. destruct G as [V E]. apply split_and_true in H. apply eqb_eq in Hw. rewrite Hw in *. apply split_orb_true. rewrite orb_comm. apply H.
    + exists u. split. unfold node_in_path. simpl. rewrite eqb_refl. reflexivity.
      simpl in H. destruct G as [V E]. apply split_and_true in H. apply eqb_eq in Hw. rewrite Hw in *. apply split_orb_true. apply H.
  - intros u H Hw. destruct (u =? w) as [|] eqn:Huw.
    + exists h. split. unfold node_in_path. simpl. rewrite eqb_refl. rewrite orb_comm. reflexivity. apply eqb_eq in Huw. rewrite <- Huw.
      simpl in H. destruct G as [V E]. apply split_and_true in H. apply split_orb_true. rewrite orb_comm. apply H.
    + assert (Hind: exists x : node,
       node_in_path x (h, v, t) = true /\
       (is_edge (x, w) G = true \/ is_edge (w, x) G = true)).
      { apply IH. apply is_path_in_graph_induction with (u := u). apply H. rewrite node_in_path_equiv. rewrite node_in_path_equiv in Hw.
        simpl in Hw. rewrite Huw in Hw. simpl. apply Hw. }
      destruct Hind as [x Hind]. exists x. split.
      * rewrite node_in_path_equiv. destruct Hind as [Hind _]. rewrite node_in_path_equiv in Hind. simpl. destruct (u =? x) as [|]. reflexivity.
        apply Hind.
      * apply Hind.
Qed.

Lemma sublist_of_path_has_edge: forall (a b h v: node) (t: nodes) (G: graph),
  sublist [b; a] (h :: t ++ [v]) = true
  -> is_path_in_graph (h, v, t) G = true
  -> is_edge (b, a) G = true \/ is_edge (a, b) G = true.
Proof.
  intros a b h v t G Hsub Hpath.
  generalize dependent h. induction t as [| h' t' IH].
  - intros h Hsub Hpath. simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [Hsub | F].
    + apply split_and_true in Hsub. destruct Hsub as [Hbh Hav].
      simpl in Hpath. destruct G as [V E]. apply eqb_eq in Hbh. rewrite Hbh. rewrite andb_comm in Hav. simpl in Hav. apply eqb_eq in Hav. rewrite Hav.
      rewrite andb_comm in Hpath. simpl in Hpath. apply split_orb_true in Hpath. apply Hpath.
    + rewrite orb_comm in F. simpl in F. rewrite andb_comm in F. simpl in F. discriminate F.
  - intros h Hsub Hpath. simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [Hsub | Hsub].
    + apply split_and_true in Hsub. destruct Hsub as [Hbh Hav].
      simpl in Hpath. destruct G as [V E]. apply eqb_eq in Hbh. rewrite Hbh. rewrite andb_comm in Hav. simpl in Hav. apply eqb_eq in Hav. rewrite Hav.
      apply split_and_true in Hpath. destruct Hpath as [Hpath _ ]. apply split_orb_true in Hpath. apply Hpath.
    + apply IH with (h := h').
      * apply Hsub.
      * apply is_path_in_graph_induction with (u := h). apply Hpath.
Qed.




(* theorems about acyclic paths *)

(* any node appears in an acyclic path either 0 or 1 times *)
Theorem acyclic_path_intermediate_nodes :
  forall (p : nodes), (acyclic_path p = true) <-> forall (x: node), (count x p = 0) \/ (count x p = 1).
Proof.
  intros p. split.
  { intros Hcyc x.
  induction p as [| h t IH].
  - left. reflexivity.
  - destruct (h =? x) as [|] eqn:Hhx.
    + right. simpl. rewrite Hhx. apply f_equal.
      simpl in Hcyc. destruct (member h t) as [|] eqn:Hmem.
      * discriminate Hcyc.
      * apply eqb_eq in Hhx. rewrite Hhx in Hmem. apply not_member_count_0. apply Hmem.
    + simpl. rewrite Hhx. apply IH.
      simpl in Hcyc. destruct (member h t) as [|] eqn:Hmem.
      * discriminate Hcyc.
      * apply Hcyc. }
  { intros Hx. induction p as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (member h t) as [|] eqn:Hmem.
    + apply member_In_equiv in Hmem. apply member_count_at_least_1 in Hmem.
      assert (Hc: count h (h :: t) >= 2). { simpl. rewrite eqb_refl. lia. }
      specialize Hx with (x := h). destruct Hx as [Hx | Hx]. rewrite Hx in Hc. lia. rewrite Hx in Hc. lia.
    + simpl. apply IH. intros x. specialize Hx with (x := x). destruct Hx as [Hx | Hx].
      * left. simpl in Hx. destruct (h =? x) as [|] eqn:Hhx. lia. apply Hx.
      * simpl in Hx. destruct (h =? x) as [|] eqn:Hhx.
        -- inversion Hx. left. reflexivity.
        -- right. apply Hx. }
Qed.

(* the following two theorems allow us to switch between acyclic_path_2 and acyclic_path *)
Theorem acyclic_path_correct :
  forall (p : path),
    (acyclic_path_2 p) -> acyclic_path ([path_start p; path_end p] ++ (path_int p)) = true.
Proof.
  intros ((u, v), l) H.
  simpl. induction l as [| h t IH].
  - simpl. destruct (v =? u) as [|] eqn:Hvu.
    + simpl in H. destruct H as [H].
      apply eqb_neq in H. apply eqb_eq in Hvu. rewrite Hvu in H.
      rewrite -> eqb_refl in H. discriminate H.
    + reflexivity.
  - simpl. simpl in H. simpl in IH.
    destruct (h =? u) as [|] eqn:Hhu.
    + apply eqb_eq in Hhu. destruct H as [H1 [H2 [H3 H4]]].
      unfold not in H2. exfalso. apply H2.
      left. apply Hhu.
    + destruct H as [H1 [H2 [H3 H4]]]. apply not_eq_sym in H1. apply eqb_neq in H1.
      rewrite H1.
      destruct (member u t) as [|] eqn:Hmemu.
        * unfold not in H2.
          exfalso. apply H2. right. apply member_In_equiv. apply Hmemu.
        * rewrite H1 in IH. destruct (h =? v) as [|] eqn:Hhv.
          -- apply eqb_eq in Hhv. unfold not in H3. exfalso. apply H3.
             left. apply Hhv.
          -- destruct (member v t) as [|] eqn:Hmemv.
             ++ unfold not in H3. exfalso. apply H3. right.
                apply member_In_equiv. apply Hmemv.
             ++ apply H4.
Qed.

Theorem acyclic_path_correct_2 :
  forall (p : path),
    (acyclic_path_2 p) <-> acyclic_path ((path_start p) :: (path_int p) ++ [path_end p]) = true.
Proof.
  intros [[u v] l]. split.
  { generalize dependent v. generalize dependent u. induction l as [| h t IH].
  - intros u v H. simpl. destruct (v =? u) as [|] eqn:Hvu.
    + simpl in H. destruct H as [H].
      apply eqb_neq in H. apply eqb_eq in Hvu. rewrite Hvu in H.
      rewrite -> eqb_refl in H. discriminate H.
    + reflexivity.
  - intros u v H. simpl. destruct (h =? u) as [|] eqn:Hhu.
    + simpl in H. destruct H as [_ [H _]]. exfalso. apply H. left. apply eqb_eq. apply Hhu.
    + destruct (member u (t ++ [v])) as [|] eqn:Hmem.
      * apply member_In_equiv in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
        -- simpl in H. destruct H as [_ [H _]]. exfalso. apply H. right. apply Hmem.
        -- simpl in Hmem. destruct Hmem as [Hmem | F].
           ++ simpl in H. destruct H as [H _]. exfalso. apply H. rewrite Hmem. reflexivity.
           ++ exfalso. apply F.
      * simpl. apply IH. simpl in H. unfold acyclic_path_2. repeat split.
        -- destruct H as [_ [_ [H _]]]. intros Hhv. apply H. left. apply Hhv.
        -- destruct H as [_ [_ [_ H]]]. apply split_and_true in H. destruct H as [H _]. intros F. apply member_In_equiv in F. rewrite F in H. discriminate H.
        -- destruct H as [_ [_ [H _]]]. intros Hhv. apply H. right. apply Hhv.
        -- destruct H as [_ [_ [_ H]]]. apply split_and_true in H. destruct H as [_ H]. destruct t as [| h0 t0]. apply I. apply H. }
  { generalize dependent v. generalize dependent u. induction l as [| h t IH].
  - intros u v H. simpl. destruct (v =? u) as [|] eqn:Hvu.
    + simpl in H. rewrite Hvu in H. discriminate H.
    + simpl in H. repeat split. intros Huv. rewrite Huv in Hvu. rewrite eqb_refl in Hvu. discriminate Hvu. repeat intros F; apply F. intros F; apply F.
  - intros u v H. simpl in H. destruct (h =? u) as [|] eqn:Hhu.
    + simpl in H. discriminate H.
    + destruct (member u (t ++ [v])) as [|] eqn:Hmem.
      * simpl in H. discriminate H.
      * simpl in H. apply IH in H. simpl. repeat split.
        -- intros Huv. apply member_In_equiv_F in Hmem. apply Hmem. apply membership_append_r. left. symmetry. apply Huv.
        -- intros [Hu | Hu]. rewrite Hu in Hhu. rewrite eqb_refl in Hhu. discriminate Hhu.
           apply member_In_equiv_F in Hmem. apply Hmem. apply membership_append. apply Hu.
        -- simpl in H. intros [Hv | Hv]. destruct H as [H]. apply H. apply Hv. destruct H as [_ [_ [H]]]. apply H. apply Hv.
        -- simpl in H. apply split_and_true. split. rewrite negb_true_iff. apply member_In_equiv_F. apply H.
           destruct t as [| h' t']. simpl. reflexivity. simpl. apply H. }
Qed.



(* the following theorems state several functions that preserve acyclicity,
   including reversal, subpaths, and concatenation *)
Lemma acyclic_path_reverse: forall (p: nodes),
  acyclic_path p = true -> acyclic_path (rev p) = true.
Proof.
  intros p H.
  destruct p as [| h t].
  - simpl. reflexivity.
  - simpl. simpl in H. apply acyclic_path_intermediate_nodes. intros x. apply acyclic_path_intermediate_nodes with (p := h :: t) (x := x) in H.
    destruct H as [H | H].
    + simpl in H. destruct (h =? x) as [|] eqn:Hhx.
      * lia.
      * left. rewrite count_app. rewrite <- count_reverse. simpl. rewrite Hhx. rewrite H. reflexivity.
    + simpl in H. destruct (h =? x) as [|] eqn:Hhx.
      * inversion H. right. rewrite H1. rewrite count_app. rewrite <- count_reverse. rewrite H1. simpl. rewrite Hhx. reflexivity.
      * right. rewrite count_app. rewrite <- count_reverse. simpl. rewrite Hhx. rewrite H. reflexivity.
Qed.

Theorem reverse_path_still_acyclic: forall (u v: node) (l: nodes),
  acyclic_path_2 (u, v, l) -> acyclic_path_2 (v, u, rev l).
Proof.
  intros u v l H. generalize dependent u. destruct l as [| h t].
  - intros u H. simpl in H. destruct H as [H _]. simpl. repeat split.
    + intros Hvu. apply H. symmetry. apply Hvu.
    + intros F. apply F.
    + intros F. apply F.
  - intros u H. simpl. repeat split.
    + simpl in H. destruct H as [H _]. intros Hvu. apply H. symmetry. apply Hvu.
    + simpl in H. intros Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
      * apply membership_rev in Hmem. rewrite <- reverse_list_twice in Hmem.
        destruct H as [_ [_ [H _]]]. apply H. right. apply Hmem.
      * destruct H as [_ [_ [H _]]]. apply H. left. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. apply Hmem. exfalso. apply Hmem.
    + simpl in H. intros Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
      * destruct H as [_ [H _]]. rewrite membership_rev in Hmem. apply H. right. apply Hmem.
      * destruct H as [_ [H _]]. apply H. left. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. apply Hmem. exfalso. apply Hmem.
    + simpl in H. destruct H as [_ [_ [_ H]]].
      assert (acyclic_path (h :: t) = true). { simpl. apply H. } apply acyclic_path_reverse in H0. simpl in H0.
      destruct (rev t ++ [h]) as [| h0 t0].
      * apply I.
      * simpl in H0. apply H0.
Qed.

Lemma subpath_still_acyclic: forall (w u v: node) (l1 l2 l3: nodes),
  l1 ++ [u] ++ l2 = l3 /\ acyclic_path_2 (w, v, l3)
  -> acyclic_path_2 (u, v, l2).
Proof.
  intros w u v l1 l2 l3. intros [Hl Hcyc].

  generalize dependent u. generalize dependent l1. induction l2 as [| h t IH].
  - intros l1 u Hl. simpl. repeat split.
    + intros Huv. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [_ Hcyc].
      apply acyclic_path_intermediate_nodes with (x := v) in Hcyc. destruct Hcyc as [Hc | Hc].
      * rewrite <- Hl in Hc. simpl in Hc. rewrite <- Huv in Hc. rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia.
      * rewrite <- Hl in Hc. simpl in Hc. rewrite <- Huv in Hc. repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia.
    + easy.
    + easy.
  - intros l1 u Hl. simpl.
    assert (H: forall (z: node), In z ([u] ++ h :: t) -> (z = u /\ In z (h :: t)) \/ z = v -> False).
    { intros z Hz Hzv. destruct Hzv as [Hzv | Hzv].
      { destruct Hzv as [Hzu Hzl2]. apply membership_splits_list in Hzl2. destruct Hzl2 as [lz1 [lz2 Hzl2]]. rewrite <- Hzl2 in Hl.
      apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [_ Hcyc].
      apply acyclic_path_intermediate_nodes with (x := z) in Hcyc. destruct Hcyc as [Hc | Hc].
      * rewrite <- Hl in Hc. simpl in Hc. rewrite <- Hzu in Hc. repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia.
      * rewrite <- Hl in Hc. simpl in Hc. rewrite <- Hzu in Hc. repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc.
        rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia. }
      { apply membership_splits_list in Hz. destruct Hz as [lz1 [lz2 Hz]]. rewrite <- Hz in Hl.
      apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [_ Hcyc].
      apply acyclic_path_intermediate_nodes with (x := v) in Hcyc. destruct Hcyc as [Hc | Hc].
      * rewrite <- Hl in Hc. simpl in Hc. rewrite <- Hzv in Hc. rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia.
      * rewrite <- Hl in Hc. simpl in Hc. rewrite <- Hzv in Hc. repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia. } }

    repeat split.
    + intros Huv. apply H with (z := u). left. reflexivity. right. apply Huv.
    + intros Hh. destruct Hh as [Hh | Hh].
      * apply H with (z := h).
        -- right. left. reflexivity.
        -- left. split. apply Hh. left. reflexivity.
      * apply H with (z := u).
        -- left. reflexivity.
        -- left. split. reflexivity. right. apply Hh.
    + intros Hh. destruct Hh as [Hh | Hh].
      * apply H with (z := h).
        -- right. left. reflexivity.
        -- right. apply Hh.
      * apply H with (z := v).
        -- right. right. apply Hh.
        -- right. reflexivity.
    + specialize IH with (l1 := l1 ++ [u]) (u := h). unfold acyclic_path_2 in IH. simpl in IH.
      rewrite app_assoc in Hl. apply IH in Hl. destruct t as [| h' t'].
      * simpl. reflexivity.
      * simpl. destruct Hl as [_ [Hh [_ Hl]]]. rewrite Hl.
        destruct (h' =? h) as [|] eqn:Hh'.
        -- exfalso. apply Hh. left. apply eqb_eq. apply Hh'.
        -- destruct (member h t') as [|] eqn:Hmem.
           ++ exfalso. apply Hh. right. apply member_In_equiv. apply Hmem.
           ++ reflexivity.
Qed.

Lemma subpath_still_acyclic_2: forall (w u v: node) (l1 l2 l3: nodes),
  l1 ++ [u] ++ l2 = l3 /\ acyclic_path_2 (w, v, l3)
  -> acyclic_path_2 (w, u, l1).
Proof.
  intros w u v l1 l2 l3. intros [Hl Hcyc].
  destruct l1 as [| h t].
  - simpl in Hl. rewrite <- Hl in Hcyc. simpl. repeat split.
    + intros Hwu. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [Hcyc _]. apply eqb_eq in Hwu.
      rewrite eqb_sym in Hwu. rewrite Hwu in Hcyc. discriminate Hcyc.
    + easy.
    + easy.
  - simpl. repeat split.
    + intros Hwu. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [Hcyc _].
      rewrite <- Hl in Hcyc. simpl in Hcyc. destruct (h =? w) as [|] eqn:Hhw.
      * discriminate Hcyc.
      * assert (Hmem: member w (t ++ u :: l2) = true). { apply member_In_equiv. apply membership_append_r. rewrite Hwu. left. reflexivity. }
        apply member_In_equiv in Hmem. apply membership_append with (l2 := [v]) in Hmem. apply member_In_equiv in Hmem. rewrite Hmem in Hcyc. discriminate Hcyc.
    + intros [Hw | Hw].
      * unfold acyclic_path_2 in Hcyc. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. rewrite <- Hl. rewrite <- Hw. simpl. left. reflexivity.
      * unfold acyclic_path_2 in Hcyc. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. rewrite <- Hl. simpl. right. apply membership_append. apply Hw.
    + intros [Hu | Hu].
      * apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [_ Hcyc].
        apply acyclic_path_intermediate_nodes with (x := h) in Hcyc. destruct Hcyc as [Hc | Hc].
        -- rewrite <- Hl in Hc. simpl in Hc. rewrite <- Hu in Hc. repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia.
        -- rewrite <- Hl in Hc. simpl in Hc. rewrite <- Hu in Hc. repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia.
      * apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [_ Hcyc].
        apply acyclic_path_intermediate_nodes with (x := u) in Hcyc. destruct Hcyc as [Hc | Hc].
        -- rewrite <- Hl in Hc. simpl in Hc. destruct (h =? u) as [|] eqn:Hhu.
           ++ repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. apply member_count_at_least_1 in Hu. lia.
           ++ repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. apply member_count_at_least_1 in Hu. lia.
        -- rewrite <- Hl in Hc. simpl in Hc. destruct (h =? u) as [|] eqn:Hhu.
           ++ repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. apply member_count_at_least_1 in Hu. lia.
           ++ repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. apply member_count_at_least_1 in Hu. lia.
    + rewrite <- Hl in Hcyc. simpl in Hcyc. apply acyclic_path_intermediate_nodes with (p := h :: t).
      intros x. simpl.
      destruct Hcyc as [_ [_ [_ Hcyc]]]. apply split_and_true in Hcyc. destruct Hcyc as [Hcyc1 Hcyc2].
      destruct (h =? x) as [|] eqn:Hhx.
      * right. f_equal. apply not_member_count_0. apply eqb_eq in Hhx. rewrite <- Hhx.
        destruct (member h t) as [|] eqn:Hmem.
        -- apply member_In_equiv in Hmem. apply membership_append with (l2 := u :: l2) in Hmem. apply member_In_equiv in Hmem. rewrite Hmem in Hcyc1. discriminate Hcyc1.
        -- reflexivity.
      * apply acyclic_path_intermediate_nodes with (x := x) in Hcyc2. destruct Hcyc2 as [Hcyc2 | Hcyc2].
        -- left. rewrite count_app in Hcyc2. lia.
        -- rewrite count_app in Hcyc2. lia.
Qed.

Lemma acyclic_path_cat: forall (u v h: node) (t: nodes),
  acyclic_path_2 (u, v, h :: t)
  -> acyclic_path_2 (h, v, t).
Proof.
  intros u v h t H.
  unfold acyclic_path_2 in *.
  repeat split.
  - destruct H as [_ [_ [H _]]]. intros Hhv. apply H. left. apply Hhv.
  - destruct H as [_ [_ [_ H]]]. intros Hht. simpl in H. apply split_and_true in H. destruct H as [H _].
    apply negb_true_iff in H. apply member_In_equiv_F in H. apply H. apply Hht.
  - destruct H as [_ [_ [H _]]]. intros Hvt. apply H. right. apply Hvt.
  - destruct H as [_ [_ [_ H]]]. simpl in H. apply split_and_true in H. destruct H as [_ H]. destruct t as [| h' t'].
    + apply I.
    + apply H.
Qed.

Lemma acyclic_path_cat_2: forall (u v h: node) (t: nodes),
  acyclic_path_2 (h, v, t)
  -> ~In u (h :: t ++ [v])
  -> acyclic_path_2 (u, v, h :: t).
Proof.
  intros u v h t H1 H2.
  apply acyclic_path_correct_2. simpl. apply split_and_true. split.
  - apply member_In_equiv_F in H2. simpl in H2. rewrite H2. reflexivity.
  - apply acyclic_path_correct_2 in H1. simpl in H1. apply H1.
Qed.

Lemma concat_paths_acyclic: forall (w u v: node) (l1 l2: nodes),
  u <> v /\ acyclic_path_2 (u, w, l1) /\ acyclic_path_2 (w, v, l2)
  -> ~(In u l2) /\ ~(In v l1)
  -> overlap l1 l2 = false
  -> acyclic_path_2 (concat u w v l1 l2).
Proof.
  intros w u v l1 l2. intros [Huv [Hcycu Hcycv]]. intros [Hul2 Hvl1]. intros Hover. unfold concat.
  unfold acyclic_path_2. repeat split.
  * apply Huv.
  * intros Hu. apply membership_append_or in Hu. destruct Hu as [Hu | Hu].
    { unfold acyclic_path_2 in Hcycu.
      destruct Hcycu as [_ [Hcycu _]]. apply Hcycu. apply Hu. }
    { destruct Hu as [Hu | Hu].
    -- unfold acyclic_path_2 in Hcycu. destruct Hcycu as [Hcycu _]. apply Hcycu. rewrite Hu. reflexivity.
    -- apply Hul2. apply Hu. }
  * unfold acyclic_path_2 in Hcycv. intros Hv. apply membership_append_or in Hv. destruct Hv as [Hv | Hv].
    { exfalso. apply Hvl1. apply Hv. }
    { destruct Hv as [Hv | Hv].
    -- destruct Hcycv as [Hcycv _]. apply Hcycv. apply Hv.
    -- destruct Hcycv as [_ [_ [Hcycv _]]]. apply Hcycv. apply Hv. }
  * generalize dependent u. induction l1 as [| h1 t1 IH].
    -- intros u Huv Hcycu Hul2. simpl. unfold acyclic_path_2 in Hcycv. destruct Hcycv as [_ [Hwl2 [_ Hcycv]]].
       destruct (member w l2) as [|] eqn:Hwl2'.
       ++ exfalso. apply Hwl2. apply member_In_equiv. apply Hwl2'.
       ++ simpl. destruct l2 as [| h2 t2]. simpl. reflexivity. apply Hcycv.
    -- intros u Huv Hcycu Hul2. simpl. destruct (member h1 (t1 ++ w :: l2)) as [|] eqn:Hmem.
       ++ apply member_In_equiv in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
          ** simpl in Hcycu. destruct Hcycu as [_ [_ [_ Hcycu]]]. apply split_and_true in Hcycu. destruct Hcycu as [Hcycu _].
             apply member_In_equiv in Hmem. rewrite Hmem in Hcycu. discriminate Hcycu.
          ** destruct Hmem as [Hmem | Hmem].
             --- simpl in Hcycu. destruct Hcycu as [_ [_ [Hcycu _]]]. exfalso. apply Hcycu. left. rewrite Hmem. reflexivity.
             --- apply no_overlap_non_member with (x := h1) in Hover.
                 +++ exfalso. apply Hover. left. reflexivity.
                 +++ apply Hmem.
       ++ simpl. destruct (t1 ++ w :: l2) as [| h' t'].
          ** simpl. reflexivity.
          ** apply IH with (u := h1).
             --- intros H. apply Hvl1. right. apply H.
             --- simpl in Hover. destruct (member h1 l2). discriminate Hover. apply Hover.
             --- intros H. apply Hvl1. left. apply H.
             --- apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h1 :: t1). split.
                 simpl. reflexivity. apply Hcycu.
             --- intros H. apply no_overlap_non_member with (x := h1) in Hover.
                 +++ apply Hover. left. reflexivity.
                 +++ apply H.
Qed.

(* for an acyclic path (the node m appears only once), we can equate the nodes before and
   after m in two equal lists of nodes including m *)
Lemma acyclic_path_equate_sublists: forall (l1 l2 l3 l4: nodes) (m: node),
  acyclic_path (l1 ++ [m] ++ l2) = true /\ l1 ++ [m] ++ l2 = l3 ++ [m] ++ l4 -> l1 = l3 /\ l2 = l4.
Proof.
  intros l1 l2 l3 l4 m [Hcyc Hl].
  generalize dependent l3. induction l1 as [| h t IH].
  - intros l3 Hl. simpl in Hl. destruct l3 as [| h3 t3].
    + simpl in Hl. inversion Hl. split. reflexivity. reflexivity.
    + simpl in Hl. inversion Hl. rewrite <- H0 in H1. rewrite H1 in Hcyc. simpl in Hcyc.
      apply split_and_true in Hcyc. destruct Hcyc as [Hcyc _]. destruct (member m (t3 ++ m :: l4)) as [|] eqn:F.
      * simpl in Hcyc. discriminate Hcyc.
      * assert (In m (t3 ++ (m :: l4))). { apply membership_append_r. left. reflexivity. }
        apply member_In_equiv in H. rewrite H in F. discriminate F.
  - intros l3 Hl. simpl in Hl. destruct l3 as [| h3 t3].
    + simpl in Hl. inversion Hl. rewrite H0 in Hcyc. simpl in Hcyc.
      apply split_and_true in Hcyc. destruct Hcyc as [Hcyc _]. destruct (member m (t ++ m :: l2)) as [|] eqn:F.
      * simpl in Hcyc. discriminate Hcyc.
      * assert (In m (t ++ (m :: l2))). { apply membership_append_r. left. reflexivity. }
        apply member_In_equiv in H. rewrite H in F. discriminate F.
    + inversion Hl. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [_ Hcyc].
      specialize IH with (l3 := t3). simpl in IH. apply IH in Hcyc.
      * split.
        -- f_equal. destruct Hcyc as [Hcyc _]. apply Hcyc.
        -- destruct Hcyc as [_ Hcyc]. apply Hcyc.
      * apply H1.
Qed.


(* theorems about nodes within acyclic paths *)

Lemma node_in_subpath_not_acyclic: forall (u h v: node) (t: nodes),
  node_in_path u (h, v, t) = true
  -> acyclic_path_2 (u, v, h :: t)
  -> False.
Proof.
  intros u h v t H1 H2.
  unfold node_in_path in H1. unfold acyclic_path_2 in H2. simpl in H1.
  apply split_orb_true in H1. destruct H1 as [H1 | H1].
  - apply split_orb_true in H1. destruct H1 as [H1 | H1].
    + destruct H2 as [_ [H2 _]]. apply H2. left. apply eqb_eq in H1. rewrite H1. reflexivity.
    + destruct H2 as [H2 _]. apply H2. apply eqb_eq. apply H1.
  - destruct H2 as [_ [H2 _]]. apply H2. right. apply member_In_equiv. apply H1.
Qed.

Theorem intermediate_node_not_endpoint: forall u v x: node, forall l: nodes,
  In x l /\ acyclic_path_2 (u, v, l) -> (x <> u /\ x <> v).
Proof.
  intros u v x l. intros [Hmem Hacyc].
  unfold acyclic_path_2 in Hacyc. destruct Hacyc as [_ [Hxu [Hxv _]]].
  split.
  - destruct (x =? u) as [|] eqn:Hxueq.
    + apply Nat.eqb_eq in Hxueq. rewrite Hxueq in Hmem. unfold not in Hxu. apply Hxu in Hmem. exfalso. apply Hmem.
    + apply Nat.eqb_neq. apply Hxueq.
  - destruct (x =? v) as [|] eqn:Hxveq.
    + apply Nat.eqb_eq in Hxveq. rewrite Hxveq in Hmem. unfold not in Hxv. apply Hxv in Hmem. exfalso. apply Hmem.
    + apply Nat.eqb_neq. apply Hxveq.
Qed.

Lemma acyclic_path_count: forall (u v x: node) (l: nodes),
  In x (u :: l ++ [v])
  -> acyclic_path_2 (u, v, l)
  -> count x (u :: l ++ [v]) = 1.
Proof.
  intros u v x l Hmem Hcyc.
  generalize dependent u. induction l as [| h t IH].
  - intros u Hmem Hcyc. simpl in Hmem. destruct Hmem as [Hux | [Hvx | F]].
    + simpl. rewrite Hux. rewrite eqb_refl. f_equal. unfold acyclic_path_2 in Hcyc. destruct Hcyc as [Hcyc _].
      rewrite Hux in Hcyc. apply eqb_neq in Hcyc. rewrite eqb_sym. rewrite Hcyc. reflexivity.
    + simpl. rewrite Hvx. rewrite eqb_refl. unfold acyclic_path_2 in Hcyc. destruct Hcyc as [Hcyc _].
      rewrite Hvx in Hcyc. apply eqb_neq in Hcyc. rewrite Hcyc. reflexivity.
    + exfalso. apply F.
  - intros u Hmem Hcyc. destruct (u =? x) as [|] eqn:Hux.
    + apply eqb_eq in Hux. rewrite Hux in *. simpl. rewrite eqb_refl. f_equal. unfold acyclic_path_2 in Hcyc.
      destruct Hcyc as [Hxv [Hcyc _]]. simpl in Hcyc.
      destruct (h =? x) as [|] eqn:Hhx.
      * exfalso. apply Hcyc. left. apply eqb_eq. apply Hhx.
      * apply not_member_count_0. apply member_In_equiv_F. intros F. apply membership_append_or in F. destruct F as [F | F].
        -- apply Hcyc. right. apply F.
        -- destruct F as [F | F]. apply Hxv. rewrite F. reflexivity. apply F.
    + simpl in Hmem. destruct Hmem as [Hmem | Hmem].
      * rewrite Hmem in Hux. rewrite eqb_refl in Hux. discriminate Hux.
      * simpl. rewrite Hux. apply IH.
        -- apply Hmem.
        -- apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split.
           ++ simpl. reflexivity.
           ++ apply Hcyc.
Qed.

Lemma path_length_acyclic_graph: forall (G: graph) (u v: node) (l: nodes),
  is_path_in_graph (u, v, l) G = true
  -> acyclic_path_2 (u, v, l)
  -> path_length (u, v, l) <= num_nodes G.
Proof.
  intros G u v l. intros Hp Hc.
  assert (Hl: path_length (u, v, l) = length (u :: l ++ [v])). { unfold path_length. simpl. rewrite length_app. simpl. lia. }
  destruct G as [V E].
  assert (Hw: forall (w: node), In w (u :: l ++ [v]) -> In w V).
  { intros w Hwmem. apply node_in_path_has_edge with (w := w) in Hp. destruct Hp as [x [_ Hp]].
    simpl in Hp. destruct Hp as [Hp | Hp].
    apply split_and_true in Hp. destruct Hp as [Hp]. apply split_and_true in Hp. apply member_In_equiv. apply Hp.
    apply split_and_true in Hp. destruct Hp as [Hp]. apply split_and_true in Hp. apply member_In_equiv. apply Hp.
    rewrite node_in_path_equiv. apply member_In_equiv. apply Hwmem. }

  assert (Hcount: forall (w: node), In w (u :: l ++ [v]) -> count w (u :: l ++ [v]) = 1). { intros w Hwmem. apply acyclic_path_count with (x := w) in Hc. apply Hc. apply Hwmem. }
  rewrite Hl. unfold num_nodes.
  clear Hp. clear Hc. clear Hl.
  generalize dependent u. generalize dependent V. induction l as [| h t IH].
  - intros V u Hw Hcount. simpl. destruct V as [| x V'].
    + exfalso. apply Hw with (w := u). left. reflexivity.
    + destruct V' as [| x' V'].
      * assert (Hu: u = x). { assert (Hu: In u [x]). { apply Hw. left. reflexivity. } destruct Hu as [Hu | Hu]. symmetry. apply Hu. exfalso. apply Hu. }
        assert (Hv: v = x). { assert (Hv: In v [x]). { apply Hw. right. simpl. left. reflexivity. } destruct Hv as [Hv | Hv]. symmetry. apply Hv. exfalso. apply Hv. }
        assert (Hc': count x (u :: [] ++ [v]) = 1). { apply Hcount. left. apply Hu. } simpl in Hc'. rewrite Hu in Hc'. rewrite Hv in Hc'. rewrite eqb_refl in Hc'. lia.
      * simpl. lia.
  - intros V u Hw Hcount.
    assert (Hl: length (u :: (h :: t) ++ [v]) = S (length (h :: t ++ [v]))). { simpl. reflexivity. }
    rewrite Hl.
    assert (Hind: length (h :: t ++ [v]) <= length (filter (fun v : nat => negb (v =? u)) V)).
    { assert (Hwu: forall (w: node), In w (h :: t ++ [v]) -> w =? u = false).
      { intros w Hwmem. destruct (w =? u) as [|] eqn:Hwu.
        * exfalso. assert (Hc': count w (u :: (h :: t) ++ [v]) = 1). { apply Hcount. right. apply Hwmem. }
          simpl in Hc'. rewrite eqb_sym in Hwu. rewrite Hwu in Hc'. apply member_count_at_least_1 in Hwmem. simpl in Hwmem. lia.
        * reflexivity. }
      apply IH.
      - intros w Hwmem. apply filter_true. split.
        + apply Hw. right. apply Hwmem.
        + rewrite Hwu. reflexivity. apply Hwmem.
      - intros w Hwmem. assert (Hc': count w (u :: (h :: t) ++ [v]) = 1). { apply Hcount. right. apply Hwmem. }
        simpl in Hc'. rewrite eqb_sym in Hc'. rewrite Hwu in Hc'. apply Hc'. apply Hwmem. }
    assert (Hl': S (length (filter (fun v : nat => negb (v =? u)) V)) <= length V). { apply filter_length_membership. apply Hw. left. reflexivity. }
    lia.
Qed.



(* theorems about directed paths *)

Theorem directed_path_is_path: forall (p: path) (G: graph),
  is_directed_path_in_graph p G = true -> is_path_in_graph p G = true.
Proof.
  intros [[u v] l] [V E] Hdir.
  unfold is_directed_path_in_graph in Hdir.
  unfold is_path_in_graph.
  induction ((u :: l) ++ [v]) as [| h t IH].
  - simpl. reflexivity.
  - destruct t as [| h1 t1].
    + simpl. reflexivity.
    + simpl. simpl in Hdir. apply split_and_true in Hdir. destruct Hdir as [Hedge Hind].
      rewrite Hedge. simpl.
      apply IH. apply Hind.
Qed.

(* the following theorems provide specific nodes that form edges with the
   start or end nodes of a path *)
Theorem directed_path_has_directed_edge: forall (u v: node) (l: nodes) (G: graph),
  is_directed_path_in_graph (u, v, l) G = true
  -> exists (x: node), node_in_path x (u, v, l) = true /\ is_edge (x, v) G = true.
Proof.
  intros u v l G H.
  generalize dependent v. generalize dependent u. induction l as [| h t IH].
  - intros u v H. simpl in H. exists u. split.
    + unfold node_in_path. simpl. rewrite eqb_refl. simpl. reflexivity.
    + rewrite andb_comm in H. simpl in H. apply H.
  - intros u v H. specialize IH with (u := h) (v := v). simpl in H. apply split_and_true in H. destruct H as [_ H].
    apply IH in H. destruct H as [x [H1 H2]]. exists x. split.
    + unfold node_in_path. simpl. unfold node_in_path in H1. simpl in H1. destruct (h =? x) as [|] eqn:Hhx.
      * rewrite orb_comm. reflexivity.
      * rewrite eqb_sym in Hhx. rewrite Hhx in H1. simpl in H1. rewrite split_orb_true in H1. destruct H1 as [H1 | H1].
        -- rewrite H1. rewrite orb_comm. rewrite orb_assoc. rewrite orb_comm. reflexivity.
        -- rewrite H1. rewrite orb_comm. reflexivity.
    + apply H2.
Qed.

Theorem directed_path_has_directed_edge_end: forall (u v: node) (l: nodes) (G: graph),
  is_directed_path_in_graph (u, v, l) G = true
  -> l = [] \/ exists (l': nodes) (x: node), l = l' ++ [x] /\ is_edge (x, v) G = true.
Proof.
  intros u v l G H.
  generalize dependent v. generalize dependent u. induction l as [| h t IH].
  - intros u v H. left. reflexivity.
  - intros u v H. right. specialize IH with (u := h) (v := v). simpl in H. apply split_and_true in H. destruct H as [Hedge H].
    apply IH in H as H'. destruct H' as [H' | H'].
    + rewrite H'. exists []. exists h. split.
      * simpl. reflexivity.
      * rewrite H' in H. simpl in H. rewrite andb_comm in H. simpl in H. apply H.
    + destruct H' as [l' [x [Ht Hx]]].
      * exists (h :: l'). exists x. split.
        -- simpl. rewrite <- Ht. reflexivity.
        -- apply Hx.
Qed.

Theorem directed_path_has_directed_edge_start: forall (u v: node) (l: nodes) (G: graph),
  is_directed_path_in_graph (u, v, l) G = true
  -> exists (x: node), node_in_path x (u, v, l) = true /\ is_edge (u, x) G = true.
Proof.
  intros u v l G H.
  destruct l as [| h t].
  - exists v. split.
    + unfold node_in_path. simpl. rewrite orb_comm. rewrite orb_assoc. rewrite orb_comm. rewrite eqb_refl. reflexivity.
    + simpl in H. rewrite andb_comm in H. simpl in H. apply H.
  - exists h. split.
    + unfold node_in_path. simpl. rewrite eqb_refl. rewrite orb_comm. reflexivity.
    + simpl in H. apply split_and_true in H. destruct H as [H _]. apply H.
Qed.


(* theorems about functions that preserve directness of paths, such as concatenation of two
   directed paths or a subpath of a directed path *)
Lemma concat_directed_paths_helper: forall l1 l2: nodes, forall G: graph,
  (is_dir_path_in_graph_helper l1 G = true) /\ (is_dir_path_in_graph_helper l2 G = true)
  /\ first_and_last_elts_same l1 l2 = true
  -> is_dir_path_in_graph_helper (l1 ++ (tl l2)) G = true.
Proof.
  intros l1 l2 G [H1 [H2 H12]].
  induction l1 as [| h t IH].
  - simpl in H12. destruct l2 as [| h2 t2]. discriminate H12. discriminate H12.
  - destruct t as [| h' t'].
    + simpl. destruct l2 as [| h2 t2] eqn:Hl2.
      * simpl. reflexivity.
      * simpl. simpl in H12. apply eqb_eq in H12.
        simpl in H2. rewrite <- H12 in H2. apply H2.
    + simpl in H12. destruct l2 as [| al2 bl2].
      * discriminate H12.
      * simpl. simpl in H1. apply split_and_true in H1.
        destruct H1 as [Hedge Hrec]. rewrite Hedge. simpl.
        destruct t' as [| at' bt'].
        -- simpl in IH. apply IH. reflexivity. apply H12.
        -- apply IH.
           ++ apply Hrec.
           ++ apply H12.
Qed.

Theorem concat_directed_paths: forall u1 mid v2: node, forall l1 l2: nodes, forall G: graph,
  is_directed_path_in_graph (u1, mid, l1) G = true /\ is_directed_path_in_graph (mid, v2, l2) G = true
  -> is_directed_path_in_graph (concat u1 mid v2 l1 l2) G = true.
Proof.
  intros u1 mid v2 l1 l2 G.
  intros [U1 U2].
  unfold concat. unfold is_directed_path_in_graph.
  unfold is_directed_path_in_graph in U1.
  unfold is_directed_path_in_graph in U2.
  assert (Hfl: first_and_last_elts_same ((u1 :: l1) ++ [mid]) ((mid :: l2) ++ [v2]) = true).
  { apply first_and_last_same. }
  remember ((u1 :: l1) ++ [mid]) as ls1.
  remember ((mid :: l2) ++ [v2]) as ls2.
  assert (H: is_dir_path_in_graph_helper (ls1 ++ (tl ls2)) G = true).
  { apply concat_directed_paths_helper. split. apply U1. split. apply U2.
    destruct ls1 as [| h t].
    - discriminate Heqls1.
    - induction l1 as [| h1 t1 IH].
      + simpl. destruct ls2 as [| h2 t2].
        * discriminate Heqls2.
        * inversion Heqls1. simpl. inversion Heqls2. apply eqb_refl.
      + apply Hfl. }
  rewrite Heqls2 in H. simpl in H. rewrite Heqls1 in H.
  assert (Hformat: ((u1 :: l1) ++ [mid]) ++ l2 = u1 :: l1 ++ mid :: l2).
  { simpl. apply f_equal. apply append_vs_concat. }
  assert (Hformat2: ((u1 :: l1) ++ [mid]) ++ l2 ++ [v2] = ((u1 :: l1 ++ mid :: l2) ++ [v2])).
  { rewrite <- Hformat. simpl. rewrite app_assoc. reflexivity. }
  rewrite <- Hformat2. apply H.
Qed.

Theorem subpath_still_directed: forall (w u v: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ is_directed_path_in_graph (w, v, l3) G = true
  -> is_directed_path_in_graph (u, v, l2) G = true.
Proof.
  intros w u v l1 l2 l3 G. intros [Hl Hdir].
  generalize dependent l3. generalize dependent w. induction l1 as [| h t IH].
  - intros w l3 Hl Hdir. simpl in Hl. rewrite <- Hl in Hdir. simpl in Hdir. apply split_and_true in Hdir. destruct Hdir as [_ Hdir].
    apply Hdir.
  - intros w l3 Hl Hdir. specialize IH with (w := h) (l3 := (t ++ [u] ++ l2)). apply IH.
    + reflexivity.
    + simpl in Hl. rewrite <- Hl in Hdir. simpl in Hdir. apply split_and_true in Hdir. destruct Hdir as [_ Hdir]. apply Hdir.
Qed.

Theorem subpath_still_directed_2: forall (w u v: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ is_directed_path_in_graph (w, v, l3) G = true
  -> is_directed_path_in_graph (w, u, l1) G = true.
Proof.
  intros w u v l1 l2 l3 G. intros [Hl Hdir].
  generalize dependent l3. generalize dependent w. induction l1 as [| h t IH].
  - intros w l3 Hl Hdir. simpl in Hl. rewrite <- Hl in Hdir. simpl in Hdir. apply split_and_true in Hdir. destruct Hdir as [Hdir _].
    simpl. rewrite Hdir. reflexivity.
  - intros w l3 Hl Hdir. specialize IH with (w := h) (l3 := (t ++ [u] ++ l2)). simpl.
    rewrite <- Hl in Hdir. simpl in Hdir. apply split_and_true in Hdir. destruct Hdir as [Hdir1 Hdir2]. rewrite Hdir1. simpl. apply IH.
    + reflexivity.
    + apply Hdir2.
Qed.

Lemma remove_node_preserves_directed_path: forall (G: graph) (p: path) (u: node),
  is_directed_path_in_graph p (remove_node_from_graph G u) = true
  -> is_directed_path_in_graph p G = true.
Proof.
  intros G p u H.
  destruct p as [[s e] l]. generalize dependent s. induction l as [| h t IH].
  - intros s H. simpl in H. simpl. destruct G as [V E]. simpl in H. simpl.
    assert (member s V = true).
    { destruct (member s (remove_node u V)) as [|] eqn:Hmem.
      - apply member_In_equiv in Hmem. unfold remove_node in Hmem. apply filter_true in Hmem. apply member_In_equiv. apply Hmem.
      - discriminate H. }
    rewrite H0.
    assert (member e V = true).
    { destruct (member e (remove_node u V)) as [|] eqn:Hmem.
      - apply member_In_equiv in Hmem. unfold remove_node in Hmem. apply filter_true in Hmem. apply member_In_equiv. apply Hmem.
      - rewrite <- andb_assoc in H. rewrite <- andb_assoc in H. rewrite andb_comm in H. discriminate H. }
    rewrite H1. simpl.
    assert (member_edge (s, e) E = true).
    { destruct (member_edge (s, e) (remove_associated_edges u E)) as [|] eqn:Hmem.
      - apply member_edge_In_equiv in Hmem. apply filter_true in Hmem. apply member_edge_In_equiv. apply Hmem.
      - rewrite <- andb_assoc in H. rewrite andb_comm in H. discriminate H. }
    rewrite H2. reflexivity.
  - intros s H. simpl. apply split_and_true. split.
    + destruct G as [V E]. simpl in H. simpl.
      assert (member s V = true).
      { destruct (member s (remove_node u V)) as [|] eqn:Hmem.
        - apply member_In_equiv in Hmem. unfold remove_node in Hmem. apply filter_true in Hmem. apply member_In_equiv. apply Hmem.
        - discriminate H. }
      rewrite H0.
      assert (member h V = true).
      { destruct (member h (remove_node u V)) as [|] eqn:Hmem.
        - apply member_In_equiv in Hmem. unfold remove_node in Hmem. apply filter_true in Hmem. apply member_In_equiv. apply Hmem.
        - rewrite <- andb_assoc in H. rewrite <- andb_assoc in H. rewrite andb_comm in H. discriminate H. }
      rewrite H1. simpl.
      assert (member_edge (s, h) E = true).
      { destruct (member_edge (s, h) (remove_associated_edges u E)) as [|] eqn:Hmem.
        - apply member_edge_In_equiv in Hmem. apply filter_true in Hmem. apply member_edge_In_equiv. apply Hmem.
        - rewrite <- andb_assoc in H. rewrite andb_comm in H. discriminate H. }
      rewrite H2. reflexivity.
    + apply IH. simpl in H. apply split_and_true in H. apply H.
Qed.

(* given a directed path going between to distinct nodes, we can always extract an acyclic
   directed path between the same two nodes such that the intermediate nodes of the acyclic path
   are a subset of the intermediate nodes of the original path
   example: 1 -> 2 -> 3 -> 4 -> 5 -> 3 -> 7 -> 6 is directed and cyclic
            1 -> 2 -> 3 ->                7 -> 6 is directed and acyclic *)
Lemma directed_path_can_be_acyclic: forall (G: graph) (u v: node) (l: nodes),
  u <> v
  -> is_directed_path_in_graph (u, v, l) G = true
  -> exists (l': nodes), is_directed_path_in_graph (u, v, l') G = true /\ acyclic_path_2 (u, v, l')
      /\ subset l' l = true.
Proof.
  intros G u v l Huv Hdir.
  assert (Hi: exists (i: nat), length l <= i). { exists (length l). lia. }
  destruct Hi as [i Hi].
  generalize dependent u. generalize dependent l. induction i as [| i' IH].
  - intros l Hi u Huv Hdir.
    assert (Hl: l = []). { destruct l as [| h t]. reflexivity. simpl in Hi. lia. } rewrite Hl in *. clear Hl.
    exists []. split. apply Hdir. split. simpl. split. apply Huv. easy. simpl. reflexivity.
  - intros l Hi u Huv Hdir.
    destruct l as [| h t].
    { exists []. split. apply Hdir. split. simpl. split. apply Huv. easy. simpl. reflexivity. }
    destruct (member u (h :: t)) as [|] eqn:Hut.
    * apply member_In_equiv in Hut. apply membership_splits_list in Hut. destruct Hut as [l1 [l2 Hut]].
      specialize IH with (l := l2) (u := u). apply IH in Huv.
      -- destruct Huv as [l' Huv]. exists l'. split. apply Huv. split. apply Huv.
         apply forallb_true_iff_mem. intros x Hx. apply member_In_equiv. destruct Huv as [_ [_ Huv]]. apply forallb_true_iff_mem with (x := x) in Huv.
         rewrite <- Hut. apply membership_append_r. simpl. right. apply member_In_equiv. apply Huv. apply Hx.
      -- rewrite <- Hut in Hi. rewrite length_app in Hi. rewrite length_app in Hi. simpl in Hi.
         assert (Hlen: length l2 < S (length l2)). { lia. }
         assert (Hlen2: S (length l2) <= length l1 + S (length l2)). { lia. }
         assert (Hlen3: S (length l2) <= S i'). { lia. }
         apply le_S_n in Hlen3. apply Hlen3.
      -- apply subpath_still_directed with (w := u) (l1 := l1) (l3 := h :: t). split. apply Hut. apply Hdir.
    * specialize IH with (u := h).
      assert (Hdir': is_directed_path_in_graph (h, v, t) G = true).
      { simpl in Hdir. apply split_and_true in Hdir. apply Hdir. }
      destruct (h =? v) as [|] eqn:Hvh.
      + exists []. split. simpl. rewrite andb_comm. simpl. simpl in Hdir. apply split_and_true in Hdir. apply eqb_eq in Hvh. rewrite <- Hvh. apply Hdir.
        split. simpl. split. apply Huv. easy. simpl. reflexivity.
      + apply IH in Hdir'.
        -- destruct Hdir' as [l' Hdir'].
           destruct (member u l') as [|] eqn:Hul.
           { apply member_In_equiv in Hul. apply membership_splits_list in Hul. destruct Hul as [l1 [l2 Hul]].
             exists l2. split.
             - apply subpath_still_directed with (w := h) (l1 := l1) (l3 := l'). split. apply Hul. apply Hdir'.
             - split. apply subpath_still_acyclic with (w := h) (l1 := l1) (l3 := l'). split. apply Hul. apply Hdir'.
               apply forallb_true_iff_mem. intros x Hx. apply member_In_equiv. right. destruct Hdir' as [_ [_ Hdir']]. apply forallb_true_iff_mem with (x := x) in Hdir'.
               apply member_In_equiv. apply Hdir'. rewrite <- Hul. apply membership_append_r. simpl. right. apply Hx. }
           exists (h :: l'). split.
           ++ simpl. apply split_and_true. split. simpl in Hdir. apply split_and_true in Hdir. apply Hdir. apply Hdir'.
           ++ split.
              ** apply acyclic_path_cat_2. apply Hdir'. intros Hu. destruct Hu as [Hu | Hu]. simpl in Hut. rewrite Hu in Hut. rewrite eqb_refl in Hut. discriminate Hut.
                 apply membership_append_or in Hu. destruct Hu as [Hu | Hu].
                 { apply member_In_equiv_F in Hul. apply Hul. apply Hu. }
                 { destruct Hu as [Hu | Hu]. apply Huv. symmetry. apply Hu. apply Hu. }
              ** simpl. rewrite eqb_refl. simpl. apply forallb_true_iff_mem. intros x Hx. apply member_In_equiv. right. destruct Hdir' as [_ [_ Hdir']]. apply forallb_true_iff_mem with (x := x) in Hdir'.
                 apply member_In_equiv. apply Hdir'. apply Hx.
        -- simpl in Hi. apply le_S_n in Hi. apply Hi.
        -- apply eqb_neq. apply Hvh.
Qed.
