From DAGs Require Import Basics.
From DAGs Require Import CycleDetection PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Stdlib Require Import Arith.EqNat. Import Nat.

Import ListNotations.
Import Lia.

(* this file defines the functions necessary to find directed paths in a graph that start
   and end at specific nodes, find all descendants of a node in a graph, and thereby find
   all ancestors of a node in a graph. *)


(* return list of directed 1-paths (each edge becomes one 1-path) starting from s *)
Fixpoint directed_edges_as_paths_from_start (s: node) (E: edges) : paths :=
  match E with
  | [] => []
  | h :: t => match h with
              | (u, v) => if (u =? s) then (u, v, []) :: directed_edges_as_paths_from_start s t
                          else directed_edges_as_paths_from_start s t
              end
  end.

(* determine all directed paths starting from u in G, assuming that G is acyclic,
   so we do not need to check the boolean output of `dfs_extend_by_edges_iter` *)
Definition find_directed_paths_from_start (u: node) (G: graph) : paths :=
  match G with
  | (V, E) => snd (dfs_extend_by_edges_iter E (directed_edges_as_paths_from_start u E) (length V))
  (* each path can have at most |V| vertices *)
  end.

Definition find_directed_paths_to_end (t: node) (G: graph): paths :=
  filter (fun (p: path) => path_end p =? t)
         (snd (dfs_extend_by_edges_iter (edges_in_graph G) (directed_edges_as_paths (edges_in_graph G)) (num_nodes G))).

Lemma directed_paths_to_end_sound : forall p: path, forall v: node, forall G: graph,
  G_well_formed G = true -> contains_cycle G = false ->
    In p (find_directed_paths_to_end v G) -> (is_directed_path_in_graph p G = true) /\ (path_end p =? v = true) /\ acyclic_path_2 p.
Proof. intros p v G Hwf Hno_cycle Hin.
  unfold find_directed_paths_to_end in Hin.
  apply filter_In in Hin.
  destruct Hin as [Hin_iter Hend].
  destruct G as [V E].
  unfold edges_in_graph, num_nodes in Hin_iter; simpl in Hin_iter.
  assert (Hdir_edges : directed_paths_in_graph (directed_edges_as_paths E) (V, E)).
  { apply directed_edges_as_paths_in_graph. exact Hwf. }
  assert (Hall_acyclic : forall p', is_directed_path_in_graph p' (V, E) = true -> acyclic_path_2 p').
  { intros p' Hpath'. eapply contains_cycle_false_correct; eauto. }
  assert (Hiter := dfs_iter_no_cycle (V, E) (length V) (directed_edges_as_paths E) Hwf Hdir_edges Hall_acyclic).
  destruct Hiter as [_ Hdir_result].

  assert (Hpath : is_directed_path_in_graph p (V, E) = true).
  { unfold directed_paths_in_graph in Hdir_result.
    rewrite Forall_forall in Hdir_result. apply Hdir_result. exact Hin_iter. }
  split; [| split].
  - exact Hpath.
  - exact Hend.
  - eapply contains_cycle_false_correct; eauto.
Qed.

Lemma dfs_extend_by_edge_complete :
  forall u v w l (e:edge) (ps:paths),
    In (u, v, l) ps ->
    e = (v, w) ->
    acyclic_path_2 (u, v, l) ->
    ~In w (u :: v :: l) ->
    fst (dfs_extend_by_edge e ps) = false ->
    In (u, w, l ++ [v]) (snd (dfs_extend_by_edge e ps)).
Proof.
  intros u v w l e ps Hin Hedge Hacyc Hnotin Hno_cycle. subst e.
  induction ps as [|h ps' IH].
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + subst h. simpl.
      destruct (v =? w) eqn:Hvw.
      * apply Nat.eqb_eq in Hvw. subst w. exfalso. apply Hnotin. simpl. right. left. reflexivity.
      * simpl in Hno_cycle. rewrite Hvw in Hno_cycle. rewrite Nat.eqb_refl in *. simpl in Hno_cycle.
        destruct (u =? w) eqn:Huw.
        { apply Nat.eqb_eq in Huw. subst w. exfalso. apply Hnotin. simpl. left. reflexivity. }
        simpl in Hno_cycle. simpl.
        destruct (member w l) eqn:Hmem.
        { exfalso. apply Hnotin. simpl. right. right. apply member_In_equiv. exact Hmem. }
        simpl in Hno_cycle. remember (dfs_extend_by_edge (v, w) ps') as res eqn:Hres.
        destruct res as [cycle_rec paths_rec].
        destruct cycle_rec eqn:Hcycle_rec.
        { simpl in Hno_cycle. discriminate. }
        simpl. right. unfold add_path_no_repeats.
        destruct (member_path (u, w, l ++ [v]) paths_rec) eqn:Hmem_path.
        { rewrite <- member_path_true_iff. exact Hmem_path. }
        { apply in_or_app. right. simpl. left. reflexivity. }

    + destruct h as [[h_u h_v] h_l]. simpl.
      destruct (v =? w) eqn:Hvw.
      * simpl in Hno_cycle. rewrite Hvw in Hno_cycle. discriminate.
      * simpl in Hno_cycle. rewrite Hvw in Hno_cycle.
        destruct ((v =? h_v) && (h_u =? w)) eqn:Hcycle_h.
        { simpl in Hno_cycle. discriminate. }
        destruct ((v =? h_v) && (member w h_l)) eqn:Hcycle_h2.
        { simpl in Hno_cycle. discriminate. }
        destruct (v =? h_v) eqn:Hextend_h.
        { remember (dfs_extend_by_edge (v, w) ps') as res eqn:Hres. destruct res as [cycle_rec paths_rec].
          destruct cycle_rec eqn:Hcycle_rec.
          - simpl in Hno_cycle. discriminate.
          - simpl. right.
            assert (Hno_cycle_rec : fst (dfs_extend_by_edge (v, w) ps') = false).
            { rewrite <- Hres. simpl. reflexivity. } simpl in IH.
            assert (meaningless: false = false ); auto.
            specialize (IH Hin' meaningless).
            assert (snd ((dfs_extend_by_edge (v, w) ps')) = paths_rec).
            { rewrite <- Hres. simpl. reflexivity. } eapply add_path_no_repeats_superset; eauto. }

        { remember (dfs_extend_by_edge (v, w) ps') as res eqn:Hres. destruct res as [cycle_rec paths_rec].
          destruct cycle_rec eqn:Hcycle_rec.
          - simpl in Hno_cycle. discriminate.
          - simpl. right.
            assert (Hno_cycle_rec : fst (dfs_extend_by_edge (v, w) ps') = false).
            { rewrite <- Hres. simpl. reflexivity. }
            assert (meaningless: false = false ); auto. }
Qed.

Lemma dfs_extend_by_edges_complete :
  forall G u v w l (ps:paths),
    G_well_formed G = true ->
    In (u, v, l) ps ->
    In (v, w) (snd G) ->
    acyclic_path_2 (u, v, l) ->
    ~In w (u :: v :: l) ->
    fst (dfs_extend_by_edges (snd G) ps) = false ->
    In (u, w, l ++ [v]) (snd (dfs_extend_by_edges (snd G) ps)).
Proof.
  intros [V E] u v w l ps Hwf Hin_p Hedge Hacyc Hfresh Hcyc. simpl. simpl in Hcyc.
  revert ps Hin_p Hedge Hcyc.
  induction E as [|e E' IH]; intros ps Hin_p Hedge Hcyc.
  - destruct Hedge.
  - simpl. pose proof (dfs_extend_by_edge_preserves_paths e ps (u, v, l) Hin_p) as Hin_p'.
    simpl in Hedge. destruct Hedge as [Heq_head | Htail].
    + subst e. destruct (fst (dfs_extend_by_edge (v, w) ps)) eqn:Hcyc_edge.
      { exfalso. simpl in Hcyc. rewrite Hcyc_edge in Hcyc; simpl in Hcyc. discriminate. }
      { assert (Hin_after_edge : In (u, w, l ++ [v]) (snd (dfs_extend_by_edge (v, w) ps))).
        eapply dfs_extend_by_edge_complete; eauto.
        assert (Hno_cycle_E' : fst (dfs_extend_by_edges E' (snd (dfs_extend_by_edge (v, w) ps))) = false).
        { simpl in Hcyc. rewrite Hcyc_edge in Hcyc. auto. }
        eapply dfs_extend_by_edges_preserves_paths; eauto. }
    + destruct (fst (dfs_extend_by_edge e ps)) eqn:Hcyc_e.
      { exfalso. simpl in Hcyc. rewrite Hcyc_e in Hcyc; simpl in Hcyc. discriminate. }
      { simpl. eapply IH; eauto.
        - eapply G_well_formed_induction. exact Hwf.
        - simpl in Hcyc. rewrite Hcyc_e in Hcyc. auto. }
Qed.

Lemma cycle_propagates :
  forall E (l:paths) k,
    fst (dfs_extend_by_edges_iter E l k) = true ->
    fst (dfs_extend_by_edges_iter E l (S k)) = true.
Proof.
  intros E l k Hcyc. revert E l Hcyc. induction k as [|k' IH]; intros E l Hfst.
  - simpl in Hfst. discriminate.
  - simpl in Hfst. simpl in *. destruct (fst (dfs_extend_by_edges E l)) eqn: Heq.
    simpl in *. auto. apply IH in Hfst. eapply Hfst.
Qed.

Lemma dfs_paths_appear_after_k_iterations :
  forall G u v l k,
    G_well_formed G = true ->
    is_directed_path_in_graph (u, v, l) G = true ->
    acyclic_path_2 (u, v, l) ->
    length l = k ->
    fst (dfs_extend_by_edges_iter (snd G) (directed_edges_as_paths (snd G)) k) = false ->
    In (u, v, l) (snd (dfs_extend_by_edges_iter (snd G) (directed_edges_as_paths (snd G)) k)).
Proof. intros [V E] u v l k Hwf Hpath Hacyc Hlen Hcyc. simpl.
  revert u v l Hpath Hacyc Hlen Hcyc.
  induction k as [|k' IH]; intros u v l Hpath Hacyc Hlen Hcyc.
  - assert (l = []) as Hl by (destruct l; simpl in Hlen; auto; lia).
    subst l. simpl. pose proof directed_edges_as_paths_complete as Hcap.
    apply Hcap. unfold is_directed_path_in_graph in Hpath.
    simpl in Hpath. apply andb_true_iff in Hpath as [Hedge _].
    assert (In (u,v) E) as HinE by (eapply is_edge_true_implies_In_edge; eauto). auto.
  - erewrite dfs_extend_by_edges_iter_spec; eauto; cycle 1.
    { simpl in Hcyc. destruct (fst (dfs_extend_by_edges E (directed_edges_as_paths E))) eqn:Hedges.
      - simpl in Hcyc. discriminate.
      - assert (Hno_cycle_Sk' : fst (dfs_extend_by_edges_iter E (directed_edges_as_paths E) (S k')) = false).
        { simpl. rewrite Hedges. simpl. exact Hcyc. }
        destruct (fst (dfs_extend_by_edges_iter E (directed_edges_as_paths E) k')) eqn:Hcyc_k'.
        exfalso. apply cycle_propagates in Hcyc_k'. rewrite Hcyc_k' in Hno_cycle_Sk'. discriminate. auto. }
    { pose proof dfs_extend_by_edges_complete. destruct l as [|w l'] using rev_ind.
      { simpl in Hlen. discriminate Hlen. }
      clear IHl'. rewrite length_app in Hlen. simpl in Hlen. assert (length l' = k') by lia; clear Hlen.
      specialize (H (V,E)). eapply H; eauto.
      - eapply IH; auto.
        * pose proof subpath_still_directed_2. specialize (H1 u w v l' [] (l' ++ [w]) (V,E)).
          assert (l' ++ [w] ++ [] = l' ++ [w] /\ is_directed_path_in_graph (u, v, l' ++ [w]) (V, E) = true).
          { constructor. simpl. auto. auto. } specialize (H1 H2); clear H2. auto.
        * pose proof subpath_still_acyclic_2. specialize (H1 u w v l' [] (l' ++ [w])).
          assert (l' ++ [w] ++ [] = l' ++ [w] /\ acyclic_path_2 (u, v, l' ++ [w])).
          { constructor; simpl; auto. } specialize (H1 H2); clear H2. auto.
        * pose proof cycle_propagates.
          destruct (fst (dfs_extend_by_edges_iter (snd (V, E)) (directed_edges_as_paths (snd (V, E))) k')) eqn:Hcyc_k'.
          exfalso. apply (H1 (snd (V, E)) (directed_edges_as_paths (snd (V, E))) k') in Hcyc_k'.
          rewrite Hcyc_k' in Hcyc. discriminate. reflexivity.
      - simpl. pose proof directed_path_has_directed_edge_end.
        specialize (H1 u v (l' ++ [w]) _ Hpath). destruct H1. destruct l' as [|h l''].
        * simpl in H1. discriminate.
        * discriminate.
        * destruct H1. destruct H1. destruct H1 as [Heq Hedge]. apply is_edge_true_implies_In_edge in Hedge.
          apply app_inj_tail in Heq as [_ Heq]. rewrite Heq. exact Hedge.
      - pose proof subpath_still_acyclic_2. specialize (H1 u w v l' [] (l' ++ [w])).
          assert (l' ++ [w] ++ [] = l' ++ [w] /\ acyclic_path_2 (u, v, l' ++ [w])).
          { constructor; simpl; auto. } specialize (H1 H2); clear H2. auto.
      - intro Hin. simpl in Hin. destruct Hin as [Heq | [Heq | Hin]].
        { subst v. unfold acyclic_path_2 in Hacyc. destruct Hacyc as [Hneq _]. contradiction. }
        { subst v. unfold acyclic_path_2 in Hacyc. destruct Hacyc as [_ [_ [Hnotin _]]].
          assert (In w (l' ++ [w])) by (apply in_or_app; right; simpl; auto). contradiction. }
        { unfold acyclic_path_2 in Hacyc. destruct Hacyc as [_ [_ [Hnotin _]]].
            apply Hnotin. apply in_or_app. left. exact Hin. }
      - rewrite <- dfs_extend_by_edges_iter_spec. eapply Hcyc; eauto.
        pose proof cycle_propagates.
        destruct (fst (dfs_extend_by_edges_iter E (directed_edges_as_paths E) k')) eqn:Hfst; [|reflexivity].
        exfalso. apply H1 in Hfst. replace (snd (V,E)) with E in Hcyc by auto. rewrite Hcyc in Hfst. discriminate. }
Qed.


Lemma dfs_extend_by_edges_preserves_paths_incl :
  forall E ps,
    fst (dfs_extend_by_edges E ps) = false ->
    incl ps (snd (dfs_extend_by_edges E ps)).
Proof.
  intros E ps Hno_cycle.
  unfold incl.
  intros p Hin.
  apply dfs_extend_by_edges_preserves_paths.
  - exact Hin.
  - exact Hno_cycle.
Qed.
Lemma dfs_iter_monotone :
  forall E ps k1 k2,
    k1 <= k2 ->
    fst (dfs_extend_by_edges_iter E ps k2) = false ->
    incl (snd (dfs_extend_by_edges_iter E ps k1))
         (snd (dfs_extend_by_edges_iter E ps k2)).
Proof.   intros E ps k1 k2 Hle Hno_cycle. induction k2 as [|k2' IH].
  - assert (k1 = 0) by lia. subst k1. apply incl_refl.
  - destruct (Nat.eq_dec k1 (S k2')) as [Heq | Hlt].
    + subst k1. apply incl_refl.
    + assert (Hle' : k1 <= k2') by lia.
      assert (Hno_cycle_k2' : fst (dfs_extend_by_edges_iter E ps k2') = false).
      { destruct (fst (dfs_extend_by_edges_iter E ps k2')) eqn:Hcyc.
        - exfalso. apply cycle_propagates in Hcyc. rewrite Hcyc in Hno_cycle. discriminate.
        - reflexivity. }
      specialize (IH Hle' Hno_cycle_k2').
      assert (Hstep : incl (snd (dfs_extend_by_edges_iter E ps k2')) (snd (dfs_extend_by_edges_iter E ps (S k2')))).
      { rewrite (dfs_extend_by_edges_iter_spec E ps k2' Hno_cycle_k2').
        apply dfs_extend_by_edges_preserves_paths_incl. rewrite dfs_extend_by_edges_iter_spec in Hno_cycle; cycle 1; eauto. }
      eapply incl_tran; eauto.
Qed.

Lemma directed_paths_are_paths :
  forall G (l:path),
  G_well_formed G = true ->
  is_directed_path_in_graph l G = true ->
  is_path_in_graph l G = true.
Proof. intros [V E] [[u v] l] Hwf. revert u v. induction l; intros u v hdir.
  - simpl. simpl in hdir. rewrite andb_true_r in hdir. rewrite andb_true_r.
    apply orb_true_intro. left. exact hdir.
  - simpl. simpl in hdir. rewrite andb_true_iff in *. split. destruct hdir as [hb hmatch].
    + apply orb_true_intro. left. auto.
    + destruct hdir as [hb hmatch]. destruct (l ++ [v]) eqn:hl.
      * reflexivity.
      * unfold is_directed_path_in_graph, is_path_in_graph in IHl.
        apply andb_prop in hmatch as [Hedge Hrest]. apply andb_true_intro.
        split.
        { apply orb_true_intro. left. exact Hedge. }
        { assert (Hconv : is_path_in_graph_helper ((a :: l) ++ [v]) (V, E) = true).
          { apply IHl with (u := a) (v := v). simpl. rewrite hl. simpl. apply andb_true_intro.
            split; eauto. }
          simpl in Hconv. rewrite hl in Hconv. simpl in Hconv.
          apply andb_prop in Hconv as [_ Hpath].
          exact Hpath. }
Qed.

Lemma all_acyclic_directed_paths_appear :
  forall G u v l,
    G_well_formed G = true ->
    is_directed_path_in_graph (u, v, l) G = true ->
    acyclic_path_2 (u, v, l) ->
    fst (dfs_extend_by_edges_iter (snd G) (directed_edges_as_paths (snd G)) (length (fst G))) = false ->
    In (u, v, l) (snd (dfs_extend_by_edges_iter (snd G) (directed_edges_as_paths (snd G)) (length (fst G)))).
Proof.
  intros [V E] u v l Hwf Hpath Hacyc Hcycle. simpl.
  set (k := length l).
  assert (Hk_bound : k <= length V).
  { unfold k. unfold acyclic_path_2 in Hacyc.
  destruct Hacyc as [Hneq [Hnotinu [Hnotinl Hacycl]]].
  assert (Hacyc2 : acyclic_path_2 (u, v, l)).
  { unfold acyclic_path_2. split; [exact Hneq | split; [exact Hnotinu | split; [exact Hnotinl | exact Hacycl]]]. }
    apply path_length_acyclic_graph with (G := (V, E)) in Hacyc2; auto.
    unfold path_length in Hacyc2. unfold num_nodes in Hacyc2. simpl in Hacyc2. lia. eapply directed_paths_are_paths; eauto. }
  eapply dfs_iter_monotone with (k1 := k); eauto.
  pose proof dfs_paths_appear_after_k_iterations.
  specialize (H (V,E) u v l k Hwf Hpath Hacyc). eapply H; eauto. simpl. simpl in Hcycle.
  pose proof cycle_propagates. destruct (fst (dfs_extend_by_edges_iter E (directed_edges_as_paths E) k)) eqn:Hcyc_k.
  - exfalso. assert (Hcyc_V : fst (dfs_extend_by_edges_iter E (directed_edges_as_paths E) (length V)) = true).
    { remember (length V - k) as d eqn:Hd. assert (length V = k + d) by lia.
      rewrite H1. clear H1 Hk_bound Hcycle Hd. induction d as [|d' IH].
      - simpl. replace (k+0) with k. auto. lia.
      - replace (k + S d') with (S (k + d')) by lia. apply H0. exact IH. }
    rewrite Hcyc_V in Hcycle. discriminate.
  - reflexivity.
Qed.

Theorem directed_paths_to_end_complete : forall p: path, forall v: node, forall G: graph,
  G_well_formed G = true -> contains_cycle G = false ->
      (is_directed_path_in_graph p G = true) -> (path_end p =? v = true) -> acyclic_path_2 p
  -> In p (find_directed_paths_to_end v G).
Proof.
  intros p v G Hwf Hno_cycle Hpath Hend Hacyc. unfold find_directed_paths_to_end.
  apply filter_In. split.
  - unfold edges_in_graph, num_nodes. destruct G as [V E]; destruct p as [[u w] l].
    pose proof all_acyclic_directed_paths_appear.
    specialize (H _ _ _ _ Hwf Hpath Hacyc). simpl in H.
    assert (Hdir_edges : directed_paths_in_graph (directed_edges_as_paths E) (V, E)).
    { apply directed_edges_as_paths_in_graph. exact Hwf. }
    assert (Hall_acyclic : forall p', is_directed_path_in_graph p' (V, E) = true -> acyclic_path_2 p').
    { intros p' Hpath'. eapply contains_cycle_false_correct; eauto. }
    assert (Hiter := dfs_iter_no_cycle (V, E) (length V) (directed_edges_as_paths E) Hwf Hdir_edges Hall_acyclic).
    destruct Hiter as [Hno_cycle_iter _]. apply (H Hno_cycle_iter).
  - exact Hend.
Qed.
Theorem directed_paths_to_end_correct : forall p: path, forall v: node, forall G: graph,
  G_well_formed G = true -> contains_cycle G = false ->
      (is_directed_path_in_graph p G = true) /\ (path_end p =? v = true) /\ acyclic_path_2 p
  <-> In p (find_directed_paths_to_end v G).
Proof. constructor; cycle 1.
  - intros. eapply directed_paths_to_end_sound; eauto.
  - intros. eapply directed_paths_to_end_complete; auto; apply H1.
Qed.


Example directed_paths_from_1: find_directed_paths_from_start 1 G = [(1, 2, [])].
Proof. reflexivity. Qed.

Example directed_paths_from_3: find_directed_paths_from_start 3 G = [(3, 2, []); (3, 1, []); (3, 2, [1])].
Proof. reflexivity. Qed.

Example directed_paths_to_1: find_directed_paths_to_end 4 G = [].
Proof. reflexivity. Qed.

Example directed_paths_to_2: find_directed_paths_to_end 2 G = [(1, 2, []); (3, 2, []); (4, 2, [1]); (3, 2, [1])].
Proof. reflexivity. Qed.


(* return set of ending points of all paths in p, with no repeats
   example: if p = [[1 -> 2 -> 3], [1 -> 3], [1 -> 2]], then get_endpoints p returns [2, 3] *)
Fixpoint get_endpoints (p: paths) : nodes :=
  match p with
  | [] => []
  | h :: t => match h with
              | (u, v, l) => let int := get_endpoints t in
                             if (member v int) then int else v :: int
              end
  end.

(* every node is always a descendant of itself.
   other descendants are all possible ending points of directed paths in G that
   start from s *)
Definition find_descendants (s: node) (G: graph) : nodes :=
  s :: get_endpoints (find_directed_paths_from_start s G).

Example descendants_of_1: find_descendants 1 G = [1; 2].
Proof. reflexivity. Qed.

Example descendants_of_3: find_descendants 3 G = [3; 1; 2].
Proof. reflexivity. Qed.

Example descendants_of_4: find_descendants 4 G = [4; 1; 2].
Proof. reflexivity. Qed.

Lemma node_is_descendant_of_itself: forall s: node, forall G: graph,
  In s (find_descendants s G).
Proof.
  intros s G. unfold find_descendants. simpl. left. reflexivity.
Qed.

(* v is a descendant of u iff u = v or there is a directed path from u to v *)
Theorem find_descendants_correct: forall G: graph, forall u v: node,
  (* contains_cycle G = false -> *)
  In v (find_descendants u G) <->
  u = v \/ exists U: path, is_directed_path_in_graph U G = true /\ path_start_and_end U u v = true.
Proof.
  intros G u v. split.
  - intros Hv. unfold find_descendants in Hv. destruct Hv as [Hv | Hv].
    + left. apply Hv.
    + right. induction (find_directed_paths_from_start u G) as [| h t IH].
      * simpl in Hv. exfalso. apply Hv.
      * simpl in Hv. destruct h as [[uh vh] lh]. destruct (member vh (get_endpoints t)) as [|] eqn:Hmem.
        -- apply IH. apply Hv.
        -- destruct Hv as [Hv | Hv].
Admitted.


(* find ancestors of a node by finding all nodes in G of which the given
   node is a descendant *)
Definition find_ancestors (e: node) (G: graph) : nodes :=
  match G with
  | (V, E) => filter (fun s => member e (find_descendants s G)) V
  end.

Example ancestors_of_1: find_ancestors 1 G = [1; 3; 4].
Proof. reflexivity. Qed.

Example ancestors_of_3: find_ancestors 3 G = [3].
Proof. reflexivity. Qed.

Example ancestors_of_4: find_ancestors 4 G = [4].
Proof. reflexivity. Qed.

Theorem descendants_ancestors_correct: forall G: graph, forall u v: node,
  node_in_graph u G = true /\ node_in_graph v G = true
  -> (In u (find_descendants v G) <-> In v (find_ancestors u G)).
Proof.
  intros [V E] u v Huv.
  split.
  - intros H. destruct Huv as [Hu Hv].
    destruct V as [| h t].
    + simpl in Hu. discriminate Hu.
    + apply filter_true. split.
      * simpl in Hv. destruct (h =? v) as [|] eqn:Hhv.
        -- left. apply eqb_eq. apply Hhv.
        -- right. apply member_In_equiv. apply Hv.
      * apply member_In_equiv. apply H.
  - intros H. destruct V as [| h t].
    + simpl in H. exfalso. apply H.
    + apply filter_true in H. destruct H as [_ H].
      apply member_In_equiv. apply H.
Qed.


(* if x is descendant of y, and y is descendant of z, then x is descendant of z *)
Theorem descendants_transitive: forall G: graph, forall x y z: node,
  In y (find_descendants z G) /\ In x (find_descendants y G) -> In x (find_descendants z G).
Proof.
  intros G x y z [Hy Hx].
  apply find_descendants_correct in Hy. destruct Hy as [Hy | Hy].
  { apply find_descendants_correct in Hx. destruct Hx as [Hx | Hx].
    - unfold find_descendants. left. rewrite <- Hx. apply Hy.
    - destruct Hx as [Uyx [dirUyx seUyx]]. destruct Uyx as [[vy vx] lyx].
      apply find_descendants_correct. right. exists (vy, vx, lyx). split. apply dirUyx. rewrite Hy. apply seUyx. }
  { destruct Hy as [Uzy [dirUzy seUzy]].
    apply find_descendants_correct in Hx. destruct Hx as [Hx | Hx].
    - apply find_descendants_correct. right. exists Uzy. split. apply dirUzy. rewrite <- Hx. apply seUzy.
    - destruct Hx as [Uyx [dirUyx seUyx]].
      destruct Uzy as [[uz uy] lzy]. destruct Uyx as [[vy vx] lyx].
      apply path_start_end_equal in seUyx. destruct seUyx as [Hy Hx]. rewrite Hy in dirUyx. rewrite Hx in dirUyx.
      apply path_start_end_equal in seUzy. destruct seUzy as [Hz Hy2]. rewrite Hy2 in dirUzy. rewrite Hz in dirUzy.
      apply find_descendants_correct. right. exists (concat z y x lzy lyx). split.
      * apply concat_directed_paths. split.
        + apply dirUzy.
        + apply dirUyx.
      * unfold concat. unfold path_start_and_end. simpl. rewrite eqb_refl. simpl. apply eqb_refl. }
Qed.



(* here we focus specifically on parent nodes. The parents of a node X are
   all nodes with an edge directly to X *)
Fixpoint find_parents_from_edges (X: node) (E: edges) : nodes :=
  match E with
  | [] => []
  | h :: t => match h with
              | (u, v) => if (v =? X) then u :: (find_parents_from_edges X t)
                          else find_parents_from_edges X t
              end
  end.

Definition find_parents (X: node) (G: graph) : nodes :=
  match G with
  | (V, E) => find_parents_from_edges X E
  end.

Theorem edge_from_parent_to_child: forall (X P: node) (G: graph),
  In P (find_parents X G) <-> edge_in_graph (P, X) G = true.
Proof.
  intros X P [V E]. split.
  { intros Hmem. simpl. simpl in Hmem.
  induction E as [| h t IH].
  - simpl in Hmem. exfalso. apply Hmem.
  - destruct h as [u v]. destruct (v =? X) as [|] eqn:HvX.
    + simpl in Hmem. rewrite HvX in Hmem. simpl in Hmem.
      destruct Hmem as [HuIsP | HInd].
      * simpl. rewrite HvX. apply eqb_eq in HuIsP. rewrite HuIsP. simpl. reflexivity.
      * simpl. destruct ((u =? P) && (v =? X)) as [|] eqn:H.
        -- reflexivity.
        -- apply IH. apply HInd.
    + simpl in Hmem. rewrite HvX in Hmem. simpl. rewrite HvX.
      destruct (u =? P) as [|] eqn:HuP.
      * simpl. apply IH. apply Hmem.
      * simpl. apply IH. apply Hmem. }
  { intros H. simpl. induction E as [| h t IH].
  - simpl in H. discriminate H.
  - destruct h as [a b]. simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + apply split_and_true in H. destruct H as [H1 H2]. simpl.
      destruct (b =? X) as [|] eqn:Hbv.
      * simpl. left. apply eqb_eq. apply H1.
      * discriminate H2.
    + simpl. destruct (b =? X) as [|] eqn:Hbv.
      * simpl. right. apply IH. simpl. apply H.
      * apply IH. simpl. apply H. }
Qed.

(* in well-formed graphs, parents must also be nodes in the graph *)
Lemma parents_in_graph: forall (G: graph) (u p: node),
  G_well_formed G = true
  -> In p (find_parents u G)
  -> node_in_graph p G = true.
Proof.
  intros G u p. intros HG Hp.
  apply edge_from_parent_to_child in Hp.
  assert (Hnode: node_in_graph p G = true /\ node_in_graph u G = true).
  { apply edge_corresponds_to_nodes_in_well_formed. split. apply HG. apply Hp. }
  apply Hnode.
Qed.

Lemma each_parent_appears_once: forall (u p: node) (G: graph),
  G_well_formed G = true -> In p (find_parents u G) -> count p (find_parents u G) = 1.
Proof.
  intros u p G HG Hp.
  unfold G_well_formed in HG. destruct G as [V E]. apply split_and_true in HG. destruct HG as [_ HG].
  apply forallb_true with (x := (p, u)) in HG.
  - apply eqb_eq in HG. simpl. clear Hp.
    assert (count_edge (p, u) E = count p (find_parents_from_edges u E)).
    { clear HG. induction E as [| h t IH].
      + simpl. reflexivity.
      + simpl. destruct h as [h1 h2]. destruct (h2 =? u) as [|] eqn:Hu.
        * simpl. destruct (h1 =? p) as [|] eqn:Hp.
          -- simpl. rewrite Hu. f_equal. apply IH.
          -- simpl. apply IH.
        * simpl. rewrite Hu. rewrite andb_comm. simpl. apply IH. }
    rewrite <- H. apply HG.
  - apply edge_from_parent_to_child in Hp. simpl in Hp. apply member_edge_In_equiv. apply Hp.
Qed.
