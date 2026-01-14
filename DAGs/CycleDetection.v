From DAGs Require Import Basics.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.

From Coq Require Import Classical.
From Coq Require Import Classical_Prop.
Import ListNotations.

(* this file provides functions and correctness theorems for cycle detection
   within a directed graph by performing DFS in a manner similar to in DAG_PathFinding *)


(* return list of directed 1-paths from a list of edges
   e.g. each edge (a,b) becomes 1-path a->b, or (a, b, []) *)
Fixpoint directed_edges_as_paths (E: edges) : paths :=
  match E with
  | [] => []
  | h :: t => match h with
              | (u, v) => (u, v, []) :: directed_edges_as_paths t
              end
  end.

Compute directed_edges_as_paths [(1, 2); (4, 3); (3, 2); (3, 4)].


(* return a tuple (bool, paths). the first element represents whether a cycle was encountered.
   if false, then the second element contains the extended (acyclic) list of paths after attempting
   to extend paths in l by e *)
Fixpoint dfs_extend_by_edge (e : edge) (l: paths) : bool * paths :=
  match l with
  | [] => (false, l) (* no cycle and nothing more to extend *)
  | h :: t => match h, e with
                | (u1, v1, l1), (u2, v2) =>
                      if (u2 =? v2) then (true, []) (* self loop: the edge (u2, u2) exists *)
                      else if ((u2 =? v1) && (u1 =? v2)) then (true, []) (* cycle! u1 --l1--> v1=u2 -> v2=u1 *)
                      else if ((u2 =? v1) && (member v2 l1)) then (true, [])
                           (* cycle inside path: u1 --l1--> v1=u2 -> v2, which already appeared in l1 *)
                      else if (u2 =? v1) then let res := dfs_extend_by_edge e t in (* can extend h by e *)
                                              (fst res, h :: (add_path_no_repeats (u1, v2, l1 ++ [v1]) (snd res)))
                      else let res := dfs_extend_by_edge e t in (* cannot extend h by e *)
                           (fst res, h :: (snd res))
               end
end.

Compute dfs_extend_by_edge (4, 3) (directed_edges_as_paths [(1, 2); (4, 3); (3, 2); (3, 4)]).

(* for each edge, see if extending by this edge would create a cycle.
   return (bool, paths) representing whether a cycle was encountered for any edge
   and the extended (acyclic) list of all directed paths if not *)
Fixpoint dfs_extend_by_edges (E : edges) (l: paths) : bool * paths :=
  match E with
  | [] => (false, l)
  | h :: t => let dfs := dfs_extend_by_edge h l in
              if (fst dfs) then (true, [])
              else dfs_extend_by_edges t (snd dfs)
  end.

(* iteratively extend paths k times, like a for loop,
   ultimately returning whether the graph contains a cycle *)
Fixpoint dfs_extend_by_edges_iter (E: edges) (l: paths) (k: nat) : bool * paths :=
  match k with
  | 0 => (false, l)
  | S k' => let dfs := dfs_extend_by_edges E l in
            if (fst dfs) then (true, snd dfs)
            else dfs_extend_by_edges_iter E (snd dfs) k'
  end.

(* determine if directed graph G contains a cycle *)
Definition contains_cycle (G: graph) : bool :=
  match G with
  | (V, E) => fst (dfs_extend_by_edges_iter E (directed_edges_as_paths E) (length V))
  (* each path can have at most |V| vertices *)
  end.

Example k_cycle: contains_cycle ([1; 2; 3; 4; 5], [(5, 1); (4, 5); (3, 4); (2, 3); (1, 2)]) = true.
Proof. reflexivity. Qed.

Example acyclic_when_edges_directed: contains_cycle G = false.
Proof. reflexivity. Qed.

Example contains_self_loop: contains_cycle ([1; 2; 3], [(2, 3); (2, 2)]) = true.
Proof. reflexivity. Qed.

Example contains_2_cycle: contains_cycle ([1; 2; 3; 4], [(1, 2); (4, 3); (3, 2); (3, 4)]) = true.
Proof. reflexivity. Qed.

Example acyclic_larger_graph: contains_cycle G_cf = false.
Proof. reflexivity. Qed.

Example cyclic_when_edge_added: contains_cycle (V_cf, (8, 4) :: E_cf) = true.
Proof. reflexivity. Qed.

Example cyclic_when_edge_added2: contains_cycle (V_cf, (8, 1) :: E_cf) = true.
Proof. reflexivity. Qed.

Example cyclic_when_edges_added: contains_cycle (V_cf, (8, 6) :: E_cf ++ [(6, 1)]) = true.
Proof. reflexivity. Qed.

Example but_not_when_only_one_added: contains_cycle (V_cf, E_cf ++ [(6, 1)]) = false.
Proof. reflexivity. Qed.

(* helpers for contains_cycle_complete *)
Definition directed_paths_in_graph (l: paths) (G: graph) : Prop :=
  Forall (fun p => is_directed_path_in_graph p G = true) l.


Lemma dir_path_in_graph_monotone_edges :
  forall V E a l,
    is_directed_path_in_graph l (V, E) = true ->
    is_directed_path_in_graph l (V, a :: E) = true.
Proof.
  intros V E a [[u v] int] H. unfold is_directed_path_in_graph in *.
  induction ((u :: int) ++ [v]) as [|h l' IH]. simpl. reflexivity. destruct l' as [|h' l''].
    - simpl. reflexivity.
    - apply andb_true_iff in H as [Hedge Hrest].
      apply andb_true_iff.
      split.
      + eapply edge_in_extended_graph; eauto.
      + exact (IH Hrest).
Qed.
Lemma directed_edges_as_paths_in_graph :
  forall V E,
    G_well_formed (V,E) = true ->
    directed_paths_in_graph (directed_edges_as_paths E) (V,E).
Proof. intros V E Hwf.
  unfold directed_paths_in_graph.
  induction E as [| [u v] E' IHE]; simpl; constructor.
  - unfold is_directed_path_in_graph. simpl.
    pose proof G_well_formed_corollary. specialize (H _ _ Hwf u v).
    assert (In (u, v) ((u, v) :: E')). { left. reflexivity. }
    specialize (H H0); clear H0. destruct H as [Hin_u Hin_v].
    rewrite <- member_In_equiv in Hin_u, Hin_v. rewrite Hin_u, Hin_v.
    rewrite Nat.eqb_refl, Nat.eqb_refl. simpl. reflexivity.
  - pose proof G_well_formed_induction as Hwf'. specialize (Hwf' _ _ _ Hwf).
    specialize (IHE Hwf'); clear Hwf'. rewrite Forall_forall in *.
    intros x Hin. specialize (IHE x Hin). eapply dir_path_in_graph_monotone_edges; eauto.
Qed.


Lemma directed_path_extend_last :
  forall V E u1 v1 l1 u2 v2,
    is_directed_path_in_graph (u1, v1, l1) (V,E) = true ->
    is_edge (u2,v2) (V,E) = true ->
    u2 = v1 ->
    is_directed_path_in_graph (u1, v2, l1 ++ [v1]) (V,E) = true.
Admitted.
Lemma dfs_extend_by_edge_no_cycle :
  forall V E e l,
    In e E ->
    directed_paths_in_graph l (V,E) ->
    (forall p, is_directed_path_in_graph p (V,E) = true -> acyclic_path_2 p) ->
    fst (dfs_extend_by_edge e l) = false /\
    directed_paths_in_graph (snd (dfs_extend_by_edge e l)) (V,E).
Admitted.


Lemma dfs_extend_by_edges_no_cycle :
  forall V E l,
    directed_paths_in_graph l (V,E) ->
    (forall p, is_directed_path_in_graph p (V,E) = true -> acyclic_path_2 p) ->
    fst (dfs_extend_by_edges E l) = false
    /\ directed_paths_in_graph (snd (dfs_extend_by_edges E l)) (V,E).
Admitted.


Lemma dfs_iter_no_cycle :
  forall V E k l,
    directed_paths_in_graph l (V,E) ->
    (forall p, is_directed_path_in_graph p (V,E) = true -> acyclic_path_2 p) ->
    fst (dfs_extend_by_edges_iter E l k) = false /\
    directed_paths_in_graph (snd (dfs_extend_by_edges_iter E l k)) (V,E).
Admitted.
(*helpers end*)

(* Main lemmas for contains_cycle_true_correct *)
Lemma contains_cycle_complete :
  forall G,
    G_well_formed G = true ->
    (forall p, is_directed_path_in_graph p G = true -> acyclic_path_2 p) ->
    contains_cycle G = false.
Proof. intros [V E] Hwf Hall.
    unfold contains_cycle.
    pose proof (directed_edges_as_paths_in_graph V E Hwf) as Hinit.
    pose proof (dfs_iter_no_cycle V E (length V) (directed_edges_as_paths E) Hinit Hall) as [Hfst _].
    exact Hfst.
Qed.

Lemma contains_cycle_sound :
  forall G,
    G_well_formed G = true ->
    contains_cycle G = false ->
    forall p, is_directed_path_in_graph p G = true ->
      acyclic_path_2 p.
Proof.
Admitted.

(* correctness proof for contains_cycle function and the contrapositive *)
Theorem contains_cycle_true_correct : forall G: graph,
  G_well_formed G = true ->
  (exists p: path, is_directed_path_in_graph p G = true /\ ~(acyclic_path_2 p))
  <-> contains_cycle G = true.
  (*logically the same as
  (∀ p, is_directed_path_in_graph p G = true → acyclic_path_2 p) ↔ contains_cycle G = false *)
Proof. intros [V E] Hwf. unfold contains_cycle. split.
  - intros [p [Hpath Hcyclic]].
    unfold contains_cycle.
    destruct (fst (dfs_extend_by_edges_iter E (directed_edges_as_paths E) (length V))) eqn:Hiter; eauto.
    exfalso. assert (Hacyc : acyclic_path_2 p).
      { eapply contains_cycle_sound; eauto. }
      contradiction.

  - intro Hcycle. pose proof contains_cycle_complete.
  assert (Hcontra: ~ (forall p : path, is_directed_path_in_graph p (V, E) = true -> acyclic_path_2 p)).
  { intro Hall. specialize (H (V, E) Hwf Hall). unfold contains_cycle in H. rewrite Hcycle in H. discriminate. }
  clear H. apply not_all_ex_not in Hcontra. destruct Hcontra as [p Hp].
  exists p. destruct (is_directed_path_in_graph p (V, E)) eqn:Hpath.
    + split; auto.
    + exfalso. apply Hp. intro. exfalso. discriminate H.
Qed.

Theorem contains_cycle_false_correct : forall G: graph, forall p: path,
  G_well_formed G = true ->
  contains_cycle G = false -> ((is_directed_path_in_graph p G = true) -> acyclic_path_2 p).
Proof.
  intros G p.
  pose proof contains_cycle_true_correct as cycle_true.
  specialize (cycle_true G).
  intros Hwf Hcyc Hpath.
  destruct (classic (acyclic_path_2 p)) as [HnC | HC].
  - apply HnC.
  - assert (H: (exists p' : path, is_directed_path_in_graph p' G = true /\ ~ acyclic_path_2 p')).
    { exists p. split. apply Hpath. apply HC. }
    apply cycle_true in H. rewrite H in Hcyc. discriminate Hcyc. assumption.
Qed.

Lemma remove_node_preserves_well_formed: forall (G: graph) (u: node),
  G_well_formed G = true ->
  G_well_formed (remove_node_from_graph G u) = true.
Proof.
  intros [V E] u Hwf.
  unfold remove_node_from_graph; simpl.
  unfold G_well_formed in *; simpl in *.
  apply andb_true_iff in Hwf as [Hwf1 Hwf2].
  apply andb_true_iff in Hwf1 as [Hwf_edges Hwf_nodup_V].
  apply andb_true_iff. split.
  - apply andb_true_iff. split.
    + rewrite forallb_forall in *.
      intros [a b] Hin.
      unfold remove_associated_edges in Hin.
      apply filter_In in Hin as [Hin Hnot_u].
      apply andb_true_iff in Hnot_u as [Hb Ha].
      apply negb_true_iff in Ha; apply negb_true_iff in Hb.
      specialize (Hwf_edges (a, b) Hin); simpl in Hwf_edges.
      apply andb_true_iff in Hwf_edges as [Hain Hbin].
      simpl. apply andb_true_iff. split;
      rewrite member_In_equiv in *;
      unfold remove_node; apply filter_In; split; auto;
      apply negb_true_iff; assumption.
    + unfold remove_node.
      rewrite forallb_forall in *.
      intros v Hin.
      apply filter_In in Hin as [Hin_V Htest].
      specialize (Hwf_nodup_V v Hin_V).
      apply Nat.eqb_eq in Hwf_nodup_V.
      rewrite <- count_filter with (test := fun v0 => negb (v0 =? u)).
      * apply Nat.eqb_eq. exact Hwf_nodup_V.
      * exact Htest.

  - rewrite forallb_forall in *.
    intros e Hin.
    unfold remove_associated_edges in Hin. (* This creates filter (filter E) *)
    apply filter_In in Hin as [Hin_E Htest].
    specialize (Hwf2 e Hin_E).
    apply Nat.eqb_eq in Hwf2.
    unfold remove_associated_edges.
    rewrite <- count_edge_filter with (l := E) (test := fun edg => negb (snd edg =? u) && negb (fst edg =? u)).
    + apply Nat.eqb_eq. exact Hwf2.
    + exact Htest.
Qed.

(* simple properties of acyclic graphs *)
Lemma remove_node_preserves_acyclic: forall (G: graph) (u: node),
  G_well_formed G = true ->
  contains_cycle G = false -> contains_cycle (remove_node_from_graph G u) = false.
Proof.
  intros G u Hwf H.
  destruct (contains_cycle (remove_node_from_graph G u)) as [|] eqn:Hcyc.
  - apply contains_cycle_true_correct in Hcyc. destruct Hcyc as [p Hp].
    apply contains_cycle_false_correct with (p := p) in H.
    + destruct Hp as [_ Hp]. exfalso. apply Hp. apply H.
    + auto.
    + apply remove_node_preserves_directed_path with (u := u). apply Hp.
    + eapply remove_node_preserves_well_formed; eauto.
  - reflexivity.
Qed.

Lemma acyclic_no_self_loop: forall (G: graph) (u: node),
  G_well_formed G = true ->
  contains_cycle G = false -> is_edge (u, u) G = false.
Proof.
  intros G u Hwf Hcyc.
  destruct (is_edge (u, u) G) as [|] eqn:Hedge.
  - apply contains_cycle_false_correct with (p := (u, u, [])) in Hcyc; eauto.
    + simpl in Hcyc. destruct Hcyc as [Hcyc _]. unfold not in Hcyc.
        exfalso. apply Hcyc. reflexivity.
    + simpl. rewrite Hedge. reflexivity.
  - reflexivity.
Qed.

Lemma acyclic_no_two_cycle: forall (G: graph) (u v: node),
  G_well_formed G = true ->
  contains_cycle G = false -> is_edge (u, v) G = true -> is_edge (v, u) G = false.
Proof.
  intros G u v Hwf Hcyc He.
  destruct (is_edge (v, u) G) as [|] eqn:Hvu.
  - apply contains_cycle_false_correct with (p := (u, u, [v])) in Hcyc; eauto.
    + simpl in Hcyc. destruct Hcyc as [F _]. exfalso. apply F. reflexivity.
    + simpl. rewrite He. rewrite Hvu. reflexivity.
  - reflexivity.
Qed.
