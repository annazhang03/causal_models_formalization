From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.

Import ListNotations.


Definition get_indegree (u: node) (G: graph): nat :=
  length (find_parents u G).

Definition get_indegree_zero (G: graph): nodes :=
  match G with
  | (V, E) => filter (fun v => (get_indegree v G) =? 0) V
  end.

Fixpoint construct_path (G: graph) (p: path) (iters: nat) : path :=
  match iters with
  | 0 => p
  | S iters' => match p with
                | (u, v, l) => match (find_parents u G) with
                               | [] => p
                               | h :: t => (construct_path G (h, v, u :: l) iters')
                               end
                end
  end.

Definition contains_any_node (G: graph): bool :=
  match G with
  | (V, E) => negb (eqblist V [])
  end.

Theorem constructed_path_in_graph: forall (G: graph) (p: path) (iters: nat),
  G_well_formed G = true -> is_directed_path_in_graph p G = true -> is_directed_path_in_graph (construct_path G p iters) G = true.
Proof.
  intros G p iters Hwf H.
  generalize dependent p. induction iters as [| iters' IH].
  - intros p H. simpl. apply H.
  - intros p H. destruct p as [[u v] l]. simpl. destruct (find_parents u G) as [| h t] eqn:HP.
    + apply H.
    + specialize IH with (p := (h, v, u :: l)). apply IH.
      simpl. apply split_and_true. split.
      * assert (Hedge: edge_in_graph (h, u) G = true).
        { apply edge_from_parent_to_child. rewrite HP. simpl. left. reflexivity. }
        apply edge_in_graph_then_is_edge in Hedge. apply Hedge. apply Hwf.
      * apply H.
Qed.

Theorem constructed_path_adds_length_iters: forall (G: graph) (p: path) (iters: nat),
  G_well_formed G = true /\ is_path_in_graph p G = true /\ get_indegree_zero G = []
  -> measure_path (construct_path G p iters) = (measure_path p) + iters.
Proof.
  intros G p iters [Hwf [Hpath Hindeg]].
  generalize dependent p. induction iters as [| iters' IH].
  - intros p Hpath. simpl. rewrite add_0_r. reflexivity.
  - intros p Hpath. destruct p as [[u v] l]. simpl. destruct (find_parents u G) as [| h t] eqn:HP.
    + (* contradiction: u should be in get_indegree_zero G = [] *)
      assert (contra: In u (get_indegree_zero G)).
      { destruct G as [V E]. unfold get_indegree_zero.
        apply filter_true. split.
        - assert (Hu: node_in_graph u (V, E) = true).
          { apply first_node_in_path_in_graph with (e := v) (l := l). unfold is_path_in_graph in Hpath. apply Hpath. }
          simpl in Hu. apply member_In_equiv. apply Hu.
        - unfold get_indegree. rewrite HP. simpl. reflexivity. }
      rewrite Hindeg in contra. exfalso. simpl in contra. apply contra.
    + specialize IH with (p := (h, v, u :: l)). rewrite IH.
      * simpl. lia.
      * destruct G as [V E]. simpl. unfold is_path_in_graph in Hpath. simpl in Hpath.
        rewrite Hpath.
        assert (Hhu: edge_in_graph (h, u) (V, E) = true).
        { apply edge_from_parent_to_child. rewrite HP. simpl. left. reflexivity. }
        simpl in Hhu. rewrite Hhu.
        assert (Hnode: node_in_graph h (V, E) = true /\ node_in_graph u (V, E) = true).
        { apply edge_corresponds_to_nodes_in_well_formed. split.
          - apply Hwf.
          - simpl. apply Hhu. }
        simpl in Hnode. destruct Hnode as [Hh Hu]. rewrite Hh. rewrite Hu. simpl. reflexivity.
Qed.

Theorem pigeonhole: forall (V: nodes) (V': nodes),
  (forall (u: node), In u V' -> In u V) /\ (length V < length V') -> exists (v: node), (count v V' > 1).
Proof.
  intros V V'. intros [Hu Hlen].
  generalize dependent V. induction V' as [| h' t' IH].
  - intros V Hu Hlen. simpl in Hlen. lia.
  - intros V Hu Hlen. destruct (member h' t') as [|] eqn:Hmem.
    + exists h'. simpl. rewrite eqb_refl.
      assert (Hc: count h' t' >= 1).
      { apply member_count_at_least_1. apply member_In_equiv. apply Hmem. }
      lia.
    + specialize IH with (V := (filter (fun v : nat => negb (v =? h')) V)).
      assert (H: exists v : node, count v t' > 1).
      { apply IH.
        - intros u Hmem2. apply filter_true. split.
          + apply Hu with (u := u). simpl. right. apply Hmem2.
          + destruct (u =? h') as [|] eqn:H.
            * apply eqb_eq in H. rewrite H in Hmem2. apply member_In_equiv in Hmem2. rewrite Hmem2 in Hmem. discriminate Hmem.
            * simpl. reflexivity.
        - assert (Hlen': S (length (filter (fun v : nat => negb (v =? h')) V)) <= length V).
          { apply filter_length_membership. apply Hu with (u := h'). simpl. left. reflexivity. }
          simpl in Hlen. apply succ_lt_mono. apply le_lt_trans with (m := (length V)).
          + apply Hlen'.
          + apply Hlen. }
      destruct H as [v H]. exists v. simpl. destruct (h' =? v) as [|] eqn:Hhv.
      -- lia.
      -- apply H.
Qed.

Theorem acyclic_has_indegree_zero: forall (G: graph),
  G_well_formed G = true /\ contains_any_node G = true /\ contains_cycle G = false
  -> exists u, ((node_in_graph u G) && (get_indegree u G =? 0)) = true.
Proof.
  intros G [HGwf [Hnode Hcyc]].
  destruct G as [V E] eqn: HG.
  destruct (get_indegree_zero (V, E)) as [| h t] eqn:Hindeg.
  - (* assume there are 0 nodes with indegree 0. Show a contradiction by showing that G is cyclic. *)
    destruct V as [| v V'] eqn:HV.
    + simpl in Hnode. discriminate Hnode.
    + destruct (get_indegree v G) as [| n'] eqn:Hvindeg.
      * exists v. simpl. rewrite eqb_refl. rewrite <- HG. rewrite Hvindeg. rewrite eqb_refl. reflexivity.
      * unfold get_indegree in Hvindeg. apply length_member in Hvindeg. destruct Hvindeg as [p Hp].
        apply edge_from_parent_to_child in Hp.
        assert (HpV: node_in_graph p G = true /\ node_in_graph v G = true).
        { apply edge_corresponds_to_nodes_in_well_formed. split. rewrite HG. apply HGwf. apply Hp. }
        destruct HpV as [HpV _].
        remember (construct_path G (p, v, []) (length V)) as cycle. (* extend (p, v) backwards |V| times *)
        assert (Hpath: is_directed_path_in_graph cycle G = true).
        { rewrite Heqcycle. apply constructed_path_in_graph. rewrite HG. apply HGwf. rewrite HG. simpl.
          rewrite HG in HpV. simpl in HpV. rewrite HpV. rewrite eqb_refl.
          rewrite HG in Hp. simpl in Hp. rewrite Hp. simpl. reflexivity. }
        assert (Hrepeat: exists (r: node), (count r ([path_start cycle; path_end cycle] ++ (path_int cycle)) > 1)).
        { apply pigeonhole with (V := V). split.
          - intros x Hx.
            assert (Heq: node_in_graph x G = true).
            { apply nodes_in_graph_in_V with (p := cycle). split.
              - unfold node_in_path. simpl in Hx.
                destruct Hx as [Hs | [He | Hint]].
                + rewrite Hs. rewrite eqb_refl. simpl. reflexivity.
                + rewrite He. rewrite eqb_refl. simpl.
                  apply split_orb_true. left. apply split_orb_true. right. reflexivity.
                + apply member_In_equiv in Hint. rewrite Hint. apply split_orb_true. right. reflexivity.
              - apply directed_path_is_path. apply Hpath. }
            rewrite HG in Heq. rewrite <- HV in Heq. simpl in Heq. apply member_In_equiv. apply Heq.
          - assert (Hlen: measure_path cycle = 2 + (length V)).
            { rewrite Heqcycle. apply constructed_path_adds_length_iters. repeat split.
              - rewrite HG. apply HGwf.
              - rewrite HG. simpl. rewrite eqb_refl.
                assert (Hmemp: node_in_graph p G = true /\ node_in_graph v G = true).
                { apply edge_corresponds_to_nodes_in_well_formed. split.
                  - rewrite HG. apply HGwf.
                  - apply Hp. } destruct Hmemp as [Hmemp _].
                rewrite HG in Hmemp. simpl in Hmemp. rewrite Hmemp. rewrite HG in Hp. simpl in Hp. rewrite Hp.
                simpl. reflexivity.
              - rewrite HG. apply Hindeg. }
            destruct cycle as [[s e] l]. unfold measure_path in Hlen. simpl.
            apply add_cancel_l in Hlen. rewrite Hlen. lia. }
        assert (Hcycle: ~(acyclic_path_2 cycle)).
        { unfold not. intros H. apply acyclic_path_correct in H. destruct Hrepeat as [r Hrepeat].
          apply acyclic_path_intermediate_nodes with (x := r) in H. destruct H as [H0 | H1].
          - rewrite H0 in Hrepeat. lia.
          - rewrite H1 in Hrepeat. lia. }
        assert (contra: contains_cycle G = true).
        { apply contains_cycle_true_correct. rewrite HG; auto.
        exists cycle. split.
          - apply Hpath.
          - apply Hcycle. }
        rewrite HG in contra. rewrite Hcyc in contra. discriminate contra.
  - exists h.
    unfold get_indegree_zero in Hindeg.
    assert (Hh: In h (filter
           (fun v : node =>
            get_indegree v (V, E) =? 0) V)). { rewrite Hindeg. simpl. left. reflexivity. }
    apply filter_true in Hh. unfold node_in_graph. rewrite <- member_In_equiv in Hh.
    destruct Hh as [HhV Hhdeg]. rewrite HhV. rewrite Hhdeg. reflexivity.
Qed.

Fixpoint topological_sort_helper (G: graph) (iters: nat) : option nodes :=
  match iters with
  | 0 => Some []
  | S iters' => let ind := get_indegree_zero G in
                match ind with
                | [] => None (* G contains cycle *)
                | h :: t => let rec := topological_sort_helper (remove_node_from_graph G h) iters' in
                            match rec with
                            | None => None
                            | Some r => Some (h :: r)
                            end
                end
  end.

Definition topological_sort (G: graph) : option nodes :=
  match G with
  | (V, E) => topological_sort_helper G (length V)
  end.

Definition V_topo: nodes := [3; 1; 2; 0; 4; 5].
Definition E_topo: edges := [(5, 0); (5, 2); (2, 3); (3, 1); (4, 0); (4, 1)].

Example toposort_1: topological_sort (V_topo, E_topo) = Some [4; 5; 2; 3; 1; 0].
Proof. reflexivity. Qed.

Lemma topo_sort_subgraph: forall (G: graph) (u: node) (ts: nodes),
  G_well_formed G = true /\ node_in_graph u G = true
  -> topological_sort G = Some (u :: ts) -> topological_sort (remove_node_from_graph G u) = Some ts.
Proof.
  intros [V E] u ts [Hwf Hu] H.
  unfold topological_sort in H.
  destruct (length V) as [| l'] eqn:Hlen.
  - simpl in H. inversion H.
  - simpl in H. destruct (get_indegree_zero (V, E)) as [| h t] eqn:Hind.
    + unfold get_indegree_zero in Hind. rewrite Hind in H. discriminate H.
    + unfold get_indegree_zero in Hind. rewrite Hind in H.
      destruct (topological_sort_helper (remove_node h V, remove_associated_edges h E) l') as [r|] eqn:Hr.
      * inversion H. unfold topological_sort. simpl. rewrite <- H1.
        assert (Hlen': length V = S (length (remove_node h V))).
        { apply remove_node_from_well_formed with (E := E). split.
          - rewrite H1. apply Hu.
          - apply Hwf. }
        rewrite Hlen in Hlen'. inversion Hlen'. rewrite <- H3. rewrite <- H2. apply Hr.
      * discriminate H.
Qed.

Lemma topo_sort_exists_for_acyclic_helper: forall (G: graph) (iters: nat),
  G_well_formed G = true /\ contains_any_node G = true /\ iters <= num_nodes G ->
  contains_cycle G = false
  -> exists sorted: nodes, topological_sort_helper G iters = Some sorted.
Proof.
  intros G iters. intros [Hwf [Hnode Hiters]].
  intros Hcyc.
  generalize dependent G. induction iters as [| iters' IH].
  + intros G Hwf Hnode Hiters Hcyc. simpl. exists []. reflexivity.
  + intros [V E] Hwf Hnode Hiters Hcyc. simpl. destruct (filter (fun v : node => get_indegree v (V, E) =? 0) V) as [| h t] eqn:Hind.
    * assert (contra: exists u, ((node_in_graph u (V, E)) && (get_indegree u (V, E) =? 0)) = true).
      { apply acyclic_has_indegree_zero. repeat split.
        - apply Hwf.
        - apply Hnode.
        - apply Hcyc. }
      destruct contra as [u contra].
      assert (contra': In u (filter (fun v : node => get_indegree v (V, E) =? 0) V)).
      { apply filter_true. apply split_and_true in contra. simpl in contra. rewrite <- member_In_equiv. apply contra. }
      rewrite Hind in contra'. exfalso. simpl in contra'. apply contra'.
    * destruct iters' as [| iters''] eqn:Hiters'.
      -- simpl. exists [h]. reflexivity.
      -- specialize IH with (G := (remove_node h V, remove_associated_edges h E)).
         assert (Hlen: length V = S (length (remove_node h V))).
          { apply remove_node_from_well_formed with (E := E). split.
            - simpl. assert (H: In h (filter (fun v : node => get_indegree v (V, E) =? 0) V)).
              { rewrite Hind. simpl. left. reflexivity. }
              apply filter_true in H. destruct H as [H _]. apply member_In_equiv. apply H.
            - apply Hwf. }
      assert (H: exists sorted : nodes,
          topological_sort_helper (remove_node_from_graph (V, E) h) iters' = Some sorted).
      { rewrite Hiters'. apply IH.
        - apply remove_node_preserves_well_formed with (u := h) in Hwf. simpl in Hwf. apply Hwf.
        - simpl. simpl in Hiters.
          rewrite Hlen in Hiters. destruct (remove_node h V) as [| h' t'].
          + simpl in Hiters. lia.
          + simpl. reflexivity.
        - simpl. simpl in Hiters. lia.
        - apply remove_node_preserves_acyclic with (u := h) in Hcyc. apply Hcyc. auto. }
      destruct H as [r H]. simpl in H. rewrite Hiters' in H. rewrite H. exists (h :: r). reflexivity.
Qed.

Lemma topo_sort_exists_for_acyclic: forall (G: graph),
  G_well_formed G = true /\ contains_cycle G = false -> exists sorted: nodes, topological_sort G = Some sorted.
Proof.
  intros [V E].
  intros [Hwf Hcyc].
  unfold topological_sort. destruct (length V) as [| l'] eqn:Hlen.
  + simpl. exists []. reflexivity.
  + apply topo_sort_exists_for_acyclic_helper.
    * repeat split.
      -- apply Hwf.
      -- simpl. destruct V as [| h t].
         ++ simpl in Hlen. discriminate Hlen.
         ++ simpl. reflexivity.
      -- simpl. rewrite Hlen. lia.
    * apply Hcyc.
Qed.

Lemma topo_sort_length_correct_helper: forall (G: graph) (iters: nat) (sorted: nodes),
  topological_sort_helper G iters = Some sorted -> length sorted = iters.
Proof.
  intros G iters sorted H.
  generalize dependent G. generalize dependent sorted. induction iters as [| iters' IH].
  - intros sorted G H. simpl in H. inversion H. simpl. reflexivity.
  - intros sorted G H. simpl in H. destruct (get_indegree_zero G) as [| h t].
    + discriminate H.
    + destruct (topological_sort_helper (remove_node_from_graph G h) iters') as [r|] eqn:Hr.
      * specialize IH with (sorted := r) (G := (remove_node_from_graph G h)).
        apply IH in Hr. inversion H. simpl. rewrite Hr. reflexivity.
      * discriminate H.
Qed.

Lemma topo_sort_length_correct: forall (G: graph) (sorted: nodes),
  topological_sort G = Some sorted -> length sorted = num_nodes G.
Proof.
  intros G sorted H.
  unfold topological_sort in H. destruct G as [V E].
  apply topo_sort_length_correct_helper in H. simpl. apply H.
Qed.

Lemma topo_sort_contains_nodes_helper: forall (G: graph) (iters: nat) (sorted: nodes),
  iters >= num_nodes G /\ topological_sort_helper G iters = Some sorted ->
  forall (u: node), (In u sorted <-> node_in_graph u G = true).
Proof.
  intros G iters sorted [Hiters Hts].
  intros u. split.
  - intros Hmem. generalize dependent G. generalize dependent sorted.
    induction iters as [| iters' IH].
    + intros sorted Hmem G Hiters Hts. simpl in Hts. inversion Hts. rewrite <- H0 in Hmem. simpl in Hmem.
      exfalso. apply Hmem.
    + intros sorted Hmem G Hiters Hts. simpl in Hts. destruct (get_indegree_zero G) as [| h t] eqn:Hd.
      * discriminate Hts.
      * destruct (topological_sort_helper (remove_node_from_graph G h) iters') as [r|] eqn:Hr.
        -- inversion Hts. rewrite <- H0 in Hmem. simpl in Hmem.
           assert (Hmemh: node_in_graph h G = true).
           { unfold get_indegree_zero in Hd. destruct G as [V E].
              assert (H: In h (filter (fun v : node => get_indegree v (V, E) =? 0) V)).
              { rewrite Hd. simpl. left. reflexivity. }
              apply filter_true in H. destruct H as [H _]. simpl.
              apply member_In_equiv. apply H. }
           destruct Hmem as [Hhu | Hind].
           ++ unfold get_indegree_zero in Hd. rewrite Hhu in Hmemh. apply Hmemh.
           ++ specialize IH with (sorted := r) (G := (remove_node_from_graph G h)).
              apply IH in Hind. destruct G as [V E].
              ** simpl in Hind. unfold remove_node in Hind.
                 apply member_In_equiv in Hind. apply filter_true in Hind. destruct Hind as [Hind _].
                 simpl. apply member_In_equiv. apply Hind.
              ** destruct G as [V E]. simpl in Hiters. simpl.
                 assert (H: S (length (remove_node h V)) <= length V).
                 { unfold remove_node. apply filter_length_membership. simpl in Hmemh. apply member_In_equiv. apply Hmemh. }
                 lia.
              ** apply Hr.
        -- discriminate Hts.
  - intros Hnode. generalize dependent G. generalize dependent sorted.
    induction iters as [| iters' IH].
    + intros sorted G Hiters Hts Hnode.
      destruct G as [V E]. simpl in Hiters. simpl in Hnode.
      destruct (length V) as [| l] eqn:Hl.
      * destruct V as [| h t] eqn:HV.
        -- simpl in Hnode. discriminate Hnode.
        -- simpl in Hl. discriminate Hl.
      * lia.
    + intros sorted G Hiters Hts Hnode. simpl in Hts.
      destruct (get_indegree_zero G) as [| h t] eqn:Hd.
      * discriminate Hts.
      * destruct (topological_sort_helper (remove_node_from_graph G h) iters') as [r|] eqn:Hr.
        -- inversion Hts. destruct G as [V E]. simpl in Hnode.
           destruct (u =? h) as [|] eqn:Huh.
           ++ apply eqb_eq in Huh. rewrite Huh. simpl. left. reflexivity.
           ++ assert (Hmem: node_in_graph u (remove_node_from_graph (V, E) h) = true).
              { simpl. unfold remove_node. apply member_In_equiv.
                apply filter_true. split.
                - apply member_In_equiv. apply Hnode.
                - rewrite Huh. simpl. reflexivity. }
              specialize IH with (sorted := r) (G := (remove_node_from_graph (V, E) h)).
              simpl. right. apply IH.
              ** simpl in Hiters. simpl.
                 assert (Hmemh: node_in_graph h (V, E) = true).
                 { unfold get_indegree_zero in Hd.
                    assert (H: In h (filter (fun v : node => get_indegree v (V, E) =? 0) V)).
                    { rewrite Hd. simpl. left. reflexivity. }
                    apply filter_true in H. destruct H as [H _]. simpl.
                    apply member_In_equiv. apply H. }
                 assert (H: S (length (remove_node h V)) <= length V).
                 { unfold remove_node. apply filter_length_membership. simpl in Hmemh. apply member_In_equiv. apply Hmemh. }
                 lia.
              ** apply Hr.
              ** apply Hmem.
        -- discriminate Hts.
Qed.

Lemma topo_sort_contains_nodes: forall (G: graph) (sorted: nodes),
  topological_sort G = Some sorted ->
  forall (u: node), (In u sorted <-> node_in_graph u G = true).
Proof.
  intros G sorted Hts.
  intros u.
  apply topo_sort_contains_nodes_helper with (iters := (num_nodes G)).
  split.
  - apply le_n.
  - destruct G as [V E]. unfold topological_sort in Hts. simpl. apply Hts.
Qed.

Lemma topo_sort_contains_nodes_exactly_once: forall (G: graph) (sorted: nodes),
  G_well_formed G = true /\ topological_sort G = Some sorted ->
  forall (u: node), node_in_graph u G = true -> count u sorted = 1.
Proof.
  intros G ts [Hwf Hts].
  assert (HV: forall (u: node), In u (nodes_in_graph G) -> count u (nodes_in_graph G) = 1).
  { intros u Hmem. destruct G as [V E].
    unfold G_well_formed in Hwf. apply split_and_true in Hwf. destruct Hwf as [Hwf _]. apply split_and_true in Hwf. destruct Hwf as [_ Hwf].
    apply forallb_true_iff_mem with (x := u) in Hwf.
    - simpl. apply eqb_eq in Hwf. apply Hwf.
    - simpl in Hmem. apply Hmem. }
  assert (HVts: forall (u: node), count u (nodes_in_graph G) = count u ts).
  { intros u.
    apply topo_sort_length_correct in Hts as Hlen.
    generalize dependent G. induction ts as [| h t IH].
    - intros G Hwf Hts Hu Hlen. simpl. simpl in Hlen. destruct G as [V E]. destruct V as [| h1 t1].
      + simpl. reflexivity.
      + discriminate Hlen.
    - intros G Hwf Hts Hnode Hlen. simpl.
      specialize IH with (G := remove_node_from_graph G h).
      assert (H: count u (nodes_in_graph (remove_node_from_graph G h)) = count u t).
      { apply IH.
        - apply remove_node_preserves_well_formed. apply Hwf.
        - apply topo_sort_subgraph.
          + split. apply Hwf.
            apply topo_sort_contains_nodes with (u := h) in Hts. apply Hts. simpl. left. reflexivity.
          + apply Hts.
        - intros u1 Hmem. destruct G as [V E]. simpl in Hmem. simpl.
          unfold remove_node in Hmem. apply filter_true in Hmem. destruct Hmem as [Hmem Huu1].
          simpl in Hnode. specialize Hnode with (u := u1). apply Hnode in Hmem.
          unfold remove_node.
          assert (H1: count u1 V = count u1 (filter (fun v : nat => negb (v =? h)) V)).
          { apply count_filter. apply Huu1. }
          rewrite <- H1. apply Hmem.
        - destruct G as [V E]. simpl. simpl in Hnode.
          specialize Hnode with (u := h). simpl in Hlen.
          assert (H1: length V = S (length (filter (fun v : nat => negb (v =? h)) V))).
          { apply count_length. apply Hnode.
            apply topo_sort_contains_nodes with (u := h) in Hts. simpl in Hts.
            apply member_In_equiv. apply Hts. left. reflexivity. }
          rewrite H1 in Hlen. inversion Hlen. unfold remove_node. apply H0. }
      destruct (h =? u) as [|] eqn:Hhu.
      + destruct G as [V E]. simpl. simpl in H. simpl in Hnode.
        assert (HcV: count u V = 1).
        { apply topo_sort_contains_nodes with (u := h) in Hts. simpl in Hts.
          specialize Hnode with (u := u). apply Hnode.
          apply member_In_equiv. apply eqb_eq in Hhu. rewrite <- Hhu. apply Hts. left. reflexivity. }
        assert (Hct: count u t = 0).
        { rewrite <- H. unfold remove_node. apply eqb_eq in Hhu. rewrite Hhu. apply count_remove_element. }
        rewrite HcV. rewrite Hct. reflexivity.
      + destruct G as [V E]. simpl. simpl in H. unfold remove_node in H.
        rewrite <- H. apply count_filter. rewrite eqb_sym. rewrite Hhu. simpl. reflexivity. }
  intros u H.
  specialize HVts with (u := u). rewrite <- HVts.
  specialize HV with (u := u). apply HV. destruct G as [V E].
  simpl in H. simpl. apply member_In_equiv. apply H.
Qed.

Theorem topo_sort_correct: forall (G: graph) (u v: node) (sorted: nodes),
  G_well_formed G = true /\ topological_sort G = Some sorted /\ edge_in_graph (u, v) G = true
  -> exists (i j: nat), Some i = index sorted u /\ Some j = index sorted v /\ i < j.
Proof.
Admitted.

Corollary topo_sort_parents: forall (G: graph) (c p: node) (sorted: nodes),
  G_well_formed G = true /\ topological_sort G = Some sorted
  -> In p (find_parents c G)
  -> exists (i j: nat), Some i = index sorted p /\ Some j = index sorted c /\ i < j.
Proof.
  intros G c p sorted. intros [Hwf Hts].
  intros Hmem. apply edge_from_parent_to_child in Hmem.
  apply topo_sort_correct with (G := G) (u := p) (v := c) (sorted := sorted).
  repeat split.
  - apply Hwf.
  - apply Hts.
  - apply Hmem.
Qed.

Lemma topo_sort_first_node_no_parents: forall (G: graph) (u: node) (ts: nodes),
  G_well_formed G = true /\ topological_sort G = Some (u :: ts) -> find_parents u G = [].
Proof.
  intros G u ts [Hwf Hts].
  destruct (find_parents u G) as [| h t] eqn:HP.
  - reflexivity.
  - (* contradiction: u is first in topological sort *)
    assert (Hcontra: exists (i j: nat), Some i = index (u :: ts) h /\ Some j = index (u :: ts) u /\ i < j).
    { apply topo_sort_parents with (G := G).
      - split. apply Hwf. apply Hts.
      - rewrite HP. simpl. left. reflexivity. }
    destruct Hcontra as [i [j [Hi [Hj Hij]]]].
    simpl in Hj. rewrite eqb_refl in Hj. inversion Hj. rewrite H0 in Hij. lia.
Qed.

Lemma topo_sort_parents_before: forall (G: graph) (h: node) (tsp t: nodes),
  G_well_formed G = true /\ topological_sort G = Some (tsp ++ h :: t)
  -> forall (v: node), In v (find_parents h G) -> In v tsp.
Proof.
  intros G h tsp t [Hwf Hts] p Hp.
  apply topo_sort_parents with (sorted := (tsp ++ h :: t)) in Hp.
  - (* i < j, so p must appear in tsp *)
    destruct Hp as [i [j [Hi [Hj Hij]]]].
    assert (Hmem: ~(In h tsp)).
    { intros Hhtsp.
      (* contradict that h appears only once in the topological sort of G *)
      assert (Hc: count h (tsp ++ h :: t) >= 2).
      { apply member_count_at_least_1 in Hhtsp.
        rewrite count_app. simpl. rewrite eqb_refl. lia. }
      assert (Hc2: count h (tsp ++ h :: t) = 1).
      { apply topo_sort_contains_nodes_exactly_once with (G := G).
        - split. apply Hwf. apply Hts.
        - apply topo_sort_contains_nodes with (u := h) in Hts. apply Hts.
          apply membership_append_r. simpl. left. reflexivity. }
      lia. }
    assert (Hj2: index (tsp ++ h :: t) h = Some (length tsp + 0)).
    { apply index_append with (l1 := tsp) (l2 := h :: t) (i := 0). split.
      - apply Hmem.
      - simpl. rewrite eqb_refl. reflexivity. }
    rewrite Hj2 in Hj. inversion Hj. rewrite add_0_r in H0. rewrite H0 in Hij.
    assert (Hptsp: index tsp p = Some i).
    { apply index_append_2 with (l2 := h :: t). split.
      - symmetry. apply Hi.
      - apply Hij. }
    apply index_exists. exists i. symmetry. apply Hptsp.
  - split.
    + apply Hwf.
    + apply Hts.
Qed.
