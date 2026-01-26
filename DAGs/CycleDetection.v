From DAGs Require Import Basics.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.

From Stdlib Require Import Classical.
From Stdlib Require Import Classical_Prop.
Import ListNotations.
Import Lia.

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

(* helpers for contains_cycle_false_complete *)
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


Lemma add_path_no_repeats_preserves_directed :
  forall (G : graph) (p : path) (ps : paths),
    directed_paths_in_graph ps G ->
    is_directed_path_in_graph p G = true ->
    directed_paths_in_graph (add_path_no_repeats p ps) G.
Proof. intros G p ps Hps Hp. unfold add_path_no_repeats.
  destruct (member_path p ps); [exact Hps|].
  unfold directed_paths_in_graph in *.
  apply Forall_app; split; [exact Hps|].
  constructor; [exact Hp|constructor].
Qed.
Lemma is_dir_path_in_graph_helper_app_one :
  forall (G: graph) (x: list node) (y z: node),
    is_dir_path_in_graph_helper (x ++ [y]) G = true ->
    is_edge (y, z) G = true ->
    is_dir_path_in_graph_helper (x ++ [y; z]) G = true.
Proof.
  intros G x; induction x as [|a x IH]; intros y z Hxy Hyz; simpl in *.
  - simpl. now rewrite Hyz.
  - destruct x as [|a2 x']; simpl in *.
    + apply Bool.andb_true_iff in Hxy as [Ha _].
      apply Bool.andb_true_iff; split; [exact Ha|].
      simpl. now rewrite Hyz.
    + apply Bool.andb_true_iff in Hxy as [Ha Hrest].
      apply Bool.andb_true_iff; split; [exact Ha|]. now apply IH.
Qed.
Lemma directed_path_extend_last :
  forall G u1 v1 l1 v2,
    is_directed_path_in_graph (u1, v1, l1) G = true ->
    is_edge (v1,v2) G = true ->
    is_directed_path_in_graph (u1, v2, l1 ++ [v1]) G = true.
Proof. intros G u1 v1 l1 v2 Hdir Hedge.
  unfold is_directed_path_in_graph in *.
  simpl in *. set (x := u1 :: l1).
  change (is_dir_path_in_graph_helper (x ++ [v1]) G = true) in Hdir.
  rewrite <- app_assoc. simpl.
  change (is_dir_path_in_graph_helper (x ++ [v1; v2]) G = true).
  eapply is_dir_path_in_graph_helper_app_one; eauto.
Qed.
Lemma dfs_extend_by_edge_no_cycle :
  forall G e l,
    G_well_formed G = true ->
    In e (snd G) ->
    directed_paths_in_graph l G ->
    (forall p, is_directed_path_in_graph p G = true -> acyclic_path_2 p) ->
    fst (dfs_extend_by_edge e l) = false /\
    directed_paths_in_graph (snd (dfs_extend_by_edge e l)) G.
Proof. intros G e l Hwf HinE Hdir Hall.
  destruct G as [V E]; simpl in *.
  pose proof (G_well_formed_corollary V E Hwf) as Hwf_cor.
  assert (Hedge_true : forall u v, In (u,v) E -> is_edge (u,v) (V,E) = true).
  { intros u v Hin. unfold is_edge. simpl.
    specialize (Hwf_cor u v Hin) as [Hu Hv].
    apply (proj2 (member_In_equiv V u)) in Hu.
    apply (proj2 (member_In_equiv V v)) in Hv.
    assert (Huv : member_edge (u,v) E = true).
    { apply (proj2 (member_edge_In_equiv E (u, v))). exact Hin. }
    rewrite Hu, Hv, Huv. reflexivity.
  }
  induction l as [|h t IH]; simpl.
  - split; simpl; auto.
  - unfold directed_paths_in_graph in Hdir. rewrite Forall_cons_iff in Hdir.
    destruct Hdir as [Hhdir Htdir]. destruct h as [[u1 v1] l1].
    destruct e as [u2 v2]. simpl in *.

    (* Case 1: self-loop u2=?v2 *)
    destruct (u2 =? v2) eqn:Hself.
    { apply Nat.eqb_eq in Hself; subst v2.
      assert (Hed : is_edge (u2,u2) (V,E) = true).
      { apply Hedge_true. exact HinE. }
      assert (Hdp : is_directed_path_in_graph (u2,u2,[]) (V,E) = true).
      { simpl. simpl. unfold is_edge in Hed. rewrite Hed. simpl. reflexivity. }
      pose proof (Hall (u2,u2,[]) Hdp) as Hacyc.
      destruct Hacyc as [Hneq _].
      exfalso; exact (Hneq eq_refl). }

    (* Case 2: 2-cycle test (u2=?v1)&&(u1=?v2) *)
    destruct ((u2 =? v1) && (u1 =? v2)) eqn:Htwo.
    { apply andb_true_iff in Htwo as [Hu2v1 Hu1v2].
      apply Nat.eqb_eq in Hu2v1.
      apply Nat.eqb_eq in Hu1v2.
      subst u2 v2.
      assert (Hed : is_edge (v1,u1) (V,E) = true).
      { apply Hedge_true. exact HinE. }
      assert (Hnewdir : is_directed_path_in_graph (u1,u1,l1 ++ [v1]) (V,E) = true).
      { eapply directed_path_extend_last; eauto. }
      pose proof (Hall (u1,u1,l1 ++ [v1]) Hnewdir) as Hacyc.
      destruct Hacyc as [Hneq _].
      exfalso; exact (Hneq eq_refl). }

    (* Case 3: (u2=?v1) && member v2 l1 *)
    destruct ((u2 =? v1) && (member v2 l1)) eqn:Hinside.
    { apply andb_true_iff in Hinside as [Hu2v1 Hmem].
      apply Nat.eqb_eq in Hu2v1. subst u2.
      assert (Hed : is_edge (v1,v2) (V,E) = true).
      { apply Hedge_true. exact HinE. }
      assert (Hnewdir : is_directed_path_in_graph (u1,v2,l1 ++ [v1]) (V,E) = true).
      { eapply directed_path_extend_last; eauto. }
      pose proof (Hall (u1,v2,l1 ++ [v1]) Hnewdir) as Hacyc.
      destruct Hacyc as [_ [_ [HnotInV _]]].
      assert (HinL1 : In v2 l1).
      { apply (proj1 (member_In_equiv l1 v2)); exact Hmem. }
      assert (HinInt : In v2 (l1 ++ [v1])).
      { apply in_or_app; left; exact HinL1. }
      exfalso; exact (HnotInV HinInt).
    }

    (* Case 4: u2=?v1 *)
    destruct (u2 =? v1) eqn:Hu2v1.
    { apply Nat.eqb_eq in Hu2v1. subst u2.
      assert (Hed : is_edge (v1,v2) (V,E) = true).
      { apply Hedge_true. exact HinE. }
      fold (G_well_formed (V, E)) in Hwf.
      fold (directed_paths_in_graph t (V, E)) in Htdir.
      specialize (IH Htdir).
      destruct IH as [Hfst_t Hdir_t].
      split.
      - simpl. exact Hfst_t.
      - unfold directed_paths_in_graph.
        constructor.
        + exact Hhdir.
        + assert (Hnewdir : is_directed_path_in_graph (u1,v2,l1 ++ [v1]) (V,E) = true).
          { eapply directed_path_extend_last; eauto. }
          eapply add_path_no_repeats_preserves_directed; eauto.
      }

    { fold (directed_paths_in_graph t (V, E)) in Htdir.
      specialize (IH Htdir).
      destruct IH as [Hfst_t Hdir_t].
      split.
      - simpl. exact Hfst_t.
      - unfold directed_paths_in_graph.
        constructor; [exact Hhdir| exact Hdir_t].
    }
Qed.

Lemma dfs_extend_by_edges_no_cycle_gen :
  forall G E_iter l,
    G_well_formed G = true ->
    (forall e, In e E_iter -> In e (snd G)) ->
    directed_paths_in_graph l G ->
    (forall p, is_directed_path_in_graph p G = true -> acyclic_path_2 p) ->
    fst (dfs_extend_by_edges E_iter l) = false /\
    directed_paths_in_graph (snd (dfs_extend_by_edges E_iter l)) G.
Proof. intros G E_iter.
  induction E_iter as [|e t IH]; intros l Hwf Hsub Hdir Hall; simpl.
  - split; simpl; auto.
  - assert (HinG : In e (snd G)) by (apply Hsub; left; reflexivity).
    pose proof (dfs_extend_by_edge_no_cycle G e l Hwf HinG Hdir Hall) as [Hfst_edge Hdir_edge].
    rewrite Hfst_edge. apply IH with (l := snd (dfs_extend_by_edge e l)).
    + exact Hwf.
    + intros e' Hin_t. apply Hsub. right. exact Hin_t.
    + exact Hdir_edge.
    + exact Hall.
Qed.
Lemma dfs_extend_by_edges_no_cycle :
  forall G l, G_well_formed G = true ->
    directed_paths_in_graph l G ->
    (forall p, is_directed_path_in_graph p G = true -> acyclic_path_2 p) ->
    fst (dfs_extend_by_edges (snd G) l) = false
    /\ directed_paths_in_graph (snd (dfs_extend_by_edges (snd G) l)) G.
Proof. intros G l Hwf Hdir Hall.
  pose proof (dfs_extend_by_edges_no_cycle_gen G (snd G) l Hwf) as H.
  specialize (H (fun e Hin => Hin) Hdir Hall). exact H.
Qed.


Lemma dfs_iter_no_cycle :
  forall G k l, G_well_formed G = true ->
    directed_paths_in_graph l G ->
    (forall p, is_directed_path_in_graph p G = true -> acyclic_path_2 p) ->
    fst (dfs_extend_by_edges_iter (snd G) l k) = false /\
    directed_paths_in_graph (snd (dfs_extend_by_edges_iter (snd G) l k)) G.
Proof. intros G k.
  induction k as [|k' IH]; intros l Hwf Hdir Hall; simpl.
  - split; simpl; auto.
  - pose proof (dfs_extend_by_edges_no_cycle G l Hwf Hdir Hall) as [Hfst Hedgedir].
    rewrite Hfst.
    exact (IH (snd (dfs_extend_by_edges (snd G) l)) Hwf Hedgedir Hall).
Qed.
(*helpers end*)

(* "helpers for contains_cycle_true_complete" *)
Lemma directed_edges_as_paths_In :
  forall (E : edges) (u v : node),
    In (u,v) E <-> In (u,v,[]) (directed_edges_as_paths E).
Proof.
  induction E as [| [a b] t IH]; intros u v; simpl.
  - split; intros H; contradiction.
  - simpl. split.
    + intros [H | H].
      * inversion H; subst. left. reflexivity.
      * right. apply IH. exact H.
    + intros [H | H].
      * inversion H; subst. left. reflexivity.
      * right. apply IH. exact H.
Qed.

Lemma paths_appear_after_k_iterations :
  forall G u v l k, G_well_formed G = true ->
    is_directed_path_in_graph (u, v, l) G = true ->
    acyclic_path_2 (u, v, l) ->
    length l = k ->
    In (u, v, l) (extend_paths_from_start_iter (snd G)
                    (edges_as_paths_from_start u (snd G)) k).
Admitted.
Lemma all_acyclic_paths_appear :
  forall G u v l, G_well_formed G = true ->
    is_directed_path_in_graph (u, v, l) G = true ->
    acyclic_path_2 (u, v, l) ->
    In (u, v, l) (extend_paths_from_start_iter (snd G)
                    (edges_as_paths_from_start u (snd G)) (length (fst G))).
Admitted.
(*helpers end*)

(* Main completeness lemmas for contains_cycle_true_correct *)
Lemma contains_cycle_false_complete :
  forall G,
    G_well_formed G = true ->
    (forall p, is_directed_path_in_graph p G = true -> acyclic_path_2 p) ->
    contains_cycle G = false.
Proof. intros [V E] Hwf Hall.
    unfold contains_cycle.
    pose proof (directed_edges_as_paths_in_graph V E Hwf) as Hinit.
    pose proof (dfs_iter_no_cycle (V, E) (length V) (directed_edges_as_paths E) Hwf Hinit Hall) as [Hfst _].
    exact Hfst.
Qed.

Lemma contains_cycle_true_complete1 :
  forall G,
    G_well_formed G = true ->
    contains_cycle G = false ->
    forall p, is_directed_path_in_graph p G = true -> acyclic_path_2 p.
Proof. intros [V E] Hwf Hcycle. unfold contains_cycle in Hcycle.
Admitted.

Lemma contains_cycle_true_complete2 :
  forall G,
    G_well_formed G = true ->
    (exists p, is_directed_path_in_graph p G = true /\ ~acyclic_path_2 p) ->
    contains_cycle G = true.
Proof. intros [V E] Hwf Hex. destruct Hex as [p [Hdir Hacyc]]. unfold contains_cycle.
Admitted.

(* correctness proof for contains_cycle function and the contrapositive *)
Theorem contains_cycle_true_correct : forall G: graph,
  G_well_formed G = true ->
  (exists p: path, is_directed_path_in_graph p G = true /\ ~(acyclic_path_2 p))
  <-> contains_cycle G = true.
Proof. intros [V E] Hwf. unfold contains_cycle. split.
  - intros [p [Hpath Hcyclic]].
    unfold contains_cycle.
    destruct (fst (dfs_extend_by_edges_iter E (directed_edges_as_paths E) (length V))) eqn:Hiter; eauto.
    exfalso. assert (Hacyc : acyclic_path_2 p).
      { eapply contains_cycle_true_complete1; eauto. }
      contradiction.

  - intro Hcycle. pose proof contains_cycle_false_complete.
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

Lemma contains_cycle_E_ind: forall V E e,
  G_well_formed (V,e::E) = true ->
  contains_cycle (V,e::E) = false -> contains_cycle (V,E) = false.
Proof. intros V E e Hwf Hcyc. unfold contains_cycle in *.
Admitted.

Lemma contains_cycle_no_self_loop: forall (G: graph),
  G_well_formed G = true ->
  contains_cycle G = false -> no_one_cycles (snd G) = true.
Proof. intros [V E]. induction E as [| [u v] E' IH].
  - intros. simpl in *. auto.
  - intros. simpl. case (u =? v) eqn:Heq.
      + apply Nat.eqb_eq in Heq; subst. pose proof (acyclic_no_self_loop _ v H H0).
        rewrite <- H1 in *. simpl. pose proof (G_well_formed_corollary _ _ H).
        assert (In (v,v) ((v, v) :: E')). { simpl. left. reflexivity. }
        specialize (H2 _ _ H3); clear H3. destruct H2 as [_ H2].
        rewrite <- member_In_equiv in H2. rewrite H2. simpl.
        rewrite Nat.eqb_refl. simpl. reflexivity.
      + eapply IH; eauto. eapply G_well_formed_induction; eauto.
        eapply contains_cycle_E_ind; eauto.
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
