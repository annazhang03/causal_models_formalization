From CausalDiagrams Require Import CausalPaths.
From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import Assignments.
From CausalDiagrams Require Import DSeparation.
From CausalDiagrams Require Import UnblockedAncestors.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.


(* This file provides the framework for the group of nodes we call "sources". Sources
   are the nodes along a path whose neighbors on the path are not parents.
   Example: a -> b <- c <- d -> e. a and d are sources, since their neighboring nodes
     on the path are not their parents *)


(* confounders, u if u is a parent, and v if v is a parent *)
Definition get_sources_in_g_path (G: graph) (p: path): nodes :=
  match p with
  | (u, v, l) =>
    match path_out_of_end p G with
    | Some b => if b then (if path_into_start p G then (find_confounders_in_path p G) ++ [v] else u :: (find_confounders_in_path p G) ++ [v])
                     else (if path_into_start p G then (find_confounders_in_path p G) else u :: (find_confounders_in_path p G))
    | None => [] (* since p has at least two nodes, will not reach this *)
    end
  end.

Definition source_fixed {X: Type} (U: assignments X) (A1: assignments X) (x: X): Prop :=
  forall (u1: node), is_assigned A1 u1 = true -> get_assigned_value U u1 = Some x.

Lemma sources_nonempty: forall (G: graph) (u v: node) (l: nodes),
  is_path_in_graph (u, v, l) G = true
  -> get_sources_in_g_path G (u, v, l) = [] -> False.
Proof.
  intros G u v l Hp H.
  unfold get_sources_in_g_path in H. destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + destruct (find_confounders_in_path (u, v, l) G) as [| h t]. discriminate H. discriminate H.
    + discriminate H.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + generalize dependent u. induction l as [| h t IH].
      * intros u Hp Hout Hin H. simpl in Hin. simpl in Hout. inversion Hout. rewrite Hin in H1. discriminate H1.
      * intros u Hp Hout Hin H. simpl in H. destruct t as [| h' t'].
        -- simpl in H. destruct (is_confounder_bool u v h G) as [|] eqn:Hcon. discriminate H.
           unfold is_confounder_bool in Hcon. simpl in Hin. rewrite Hin in Hcon. simpl in Hout. simpl in Hp.
           assert (is_edge (h, v) G = true).
           { inversion Hout. rewrite H1 in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp].
             apply split_and_true in Hp. rewrite orb_comm in Hp. simpl in Hp. simpl. apply Hp. }
           rewrite H0 in Hcon. discriminate Hcon.
        -- simpl in H. destruct (is_confounder_bool u h' h G) as [|] eqn:Hcon. discriminate H.
           apply IH with (u := h).
           ++ apply is_path_in_graph_induction with (u := u). apply Hp.
           ++ rewrite path_out_of_end_same in Hout. apply Hout.
           ++ simpl. unfold is_confounder_bool in Hcon. simpl in Hin. rewrite Hin in Hcon. simpl in Hcon.
              simpl in Hp. rewrite Hcon in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp].
              apply split_and_true in Hp. simpl in Hp. simpl. apply Hp.
           ++ apply H.
    + discriminate H.
  - apply path_out_of_end_Some in Hout. apply Hout.
Qed.


Lemma sources_in_graph: forall (G: graph) (u v x: node) (l: nodes),
  G_well_formed G = true
  -> is_path_in_graph (u, v, l) G = true
  -> In x (get_sources_in_g_path G (u, v, l))
  -> node_in_graph x G = true.
Proof.
  intros G u v x l. intros HG Hp Hx.
  unfold get_sources_in_g_path in Hx.
  destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
      * apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [Hx _]]]].
        apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
      * destruct Hx as [Hx | F].
           ++ apply nodes_in_graph_in_V with (p := (u, v, l)). split.
              ** unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
              ** apply Hp.
           ++ exfalso. apply F.
    + destruct Hx as [Hx | Hx].
      * apply nodes_in_graph_in_V with (p := (u, v, l)). split.
              ** unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. reflexivity.
              ** apply Hp.
      * apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [Hx _]]]].
           apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
        -- destruct Hx as [Hx | F].
           ++ apply nodes_in_graph_in_V with (p := (u, v, l)). split.
              ** unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
              ** apply Hp.
           ++ exfalso. apply F.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [Hx _]]]].
        apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
    + destruct Hx as [Hx | Hx].
      * apply nodes_in_graph_in_V with (p := (u, v, l)). split.
              ** unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. reflexivity.
              ** apply Hp.
      * apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [Hx _]]]].
        apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
  - exfalso. apply Hx.
Qed.

Lemma sources_in_path: forall (G: graph) (u v x: node) (l: nodes),
  In x (get_sources_in_g_path G (u, v, l))
  -> node_in_path x (u, v, l) = true.
Proof.
  intros G u v x l. intros Hx.
  unfold get_sources_in_g_path in Hx.
  destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
        -- unfold node_in_path. destruct Hx as [Hx | F]. rewrite Hx. rewrite eqb_refl. simpl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
    + destruct Hx as [Hx | Hx].
      * unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. reflexivity.
      * apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
        -- unfold node_in_path. destruct Hx as [Hx | F]. rewrite Hx. rewrite eqb_refl. simpl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
    + destruct Hx as [Hx | Hx].
      * unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. reflexivity.
      * apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
  - exfalso. apply Hx.
Qed.


Lemma sources_induction_into_start: forall (G: graph) (u h v: node) (t: nodes),
  is_path_in_graph (u, v, h :: t) G = true /\ contains_cycle G = false
  -> path_into_start (u, v, h :: t) G = true -> get_sources_in_g_path G (u, v, h :: t) = get_sources_in_g_path G (h, v, t).
Proof.
  intros G u h v t [Hp Hcyc] Hin.
  unfold get_sources_in_g_path.
  destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    destruct (path_into_start (h, v, t) G) as [|] eqn:Houth.
    + destruct t as [| h' t'].
      * simpl. simpl in Houth. unfold is_confounder_bool. apply acyclic_no_two_cycle in Houth.
        -- rewrite Houth. rewrite andb_comm. simpl. reflexivity.
        -- apply Hcyc.
      * simpl in Houth. simpl. unfold is_confounder_bool. apply acyclic_no_two_cycle in Houth.
        -- rewrite Houth. rewrite andb_comm. simpl. reflexivity.
        -- apply Hcyc.
    + destruct t as [| h' t'].
      * simpl in Houth. simpl in Hout. inversion Hout. rewrite H0 in Houth. discriminate Houth.
      * simpl in Hin. simpl in Houth. simpl. unfold is_confounder_bool. rewrite Hin.
        simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. apply split_and_true in Hp. destruct Hp as [Hp _].
        rewrite Houth in Hp. rewrite orb_comm in Hp. simpl in Hp. simpl. rewrite Hp. reflexivity.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    destruct (path_into_start (h, v, t) G) as [|] eqn:Houth.
    + destruct t as [| h' t'].
      * simpl. simpl in Houth. unfold is_confounder_bool. apply acyclic_no_two_cycle in Houth.
        -- rewrite Houth. rewrite andb_comm. simpl. reflexivity.
        -- apply Hcyc.
      * simpl in Houth. simpl. unfold is_confounder_bool. apply acyclic_no_two_cycle in Houth.
        -- rewrite Houth. rewrite andb_comm. simpl. reflexivity.
        -- apply Hcyc.
    + destruct t as [| h' t'].
      * simpl in Houth. simpl. unfold is_confounder_bool. simpl in Hin. rewrite Hin. simpl in Hp. destruct G as [V E].
        apply split_and_true in Hp. destruct Hp as [_ Hp]. rewrite Houth in Hp. rewrite andb_comm in Hp. rewrite orb_comm in Hp. simpl in Hp.
        simpl. rewrite Hp. reflexivity.
      * simpl in Hin. simpl in Houth. simpl. unfold is_confounder_bool. rewrite Hin.
        simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. apply split_and_true in Hp. destruct Hp as [Hp _].
        rewrite Houth in Hp. rewrite orb_comm in Hp. simpl in Hp. simpl. rewrite Hp. reflexivity.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma sources_induction_out_of_start_out_of_h: forall (G: graph) (u h v: node) (t: nodes),
  is_path_in_graph (u, v, h :: t) G = true /\ contains_cycle G = false
  -> path_into_start (u, v, h :: t) G = false /\ path_out_of_h G u v h t = true
  -> exists (A: nodes),
     get_sources_in_g_path G (u, v, h :: t) = u :: A
     /\ get_sources_in_g_path G (h, v, t) = h :: A.
Proof.
  intros G u h v t [Hp Hcyc] [Hin Houth].
  unfold get_sources_in_g_path.
  destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction in Houth.
    + rewrite Houth. exists (find_confounders_in_path (u, v, h :: t) G ++ [v]). split. reflexivity. f_equal.
      unfold find_confounders_in_path. simpl. destruct t as [| h' t'].
      * simpl. unfold is_confounder_bool. simpl in Houth. simpl in Hout. inversion Hout. rewrite H0 in Houth. discriminate Houth.
      * simpl. assert (Hcon: is_confounder_bool u h' h G = false).
        { unfold is_confounder_bool. simpl in Houth. simpl in Hin. rewrite Hin. reflexivity. }
        rewrite Hcon. reflexivity.
    + split. apply is_path_in_graph_induction with (u := u). apply Hp. apply Hcyc.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction in Houth.
    + rewrite Houth. exists (find_confounders_in_path (u, v, h :: t) G). split. reflexivity. f_equal.
      unfold find_confounders_in_path. simpl. destruct t as [| h' t'].
      * simpl. unfold is_confounder_bool. simpl in Houth. simpl in Hin. rewrite Hin. simpl. reflexivity.
      * simpl. assert (Hcon: is_confounder_bool u h' h G = false).
        { unfold is_confounder_bool. simpl in Houth. simpl in Hin. rewrite Hin. reflexivity. }
        rewrite Hcon. reflexivity.
    + split. apply is_path_in_graph_induction with (u := u). apply Hp. apply Hcyc.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma sources_induction_out_of_start_into_h: forall (G: graph) (u h v: node) (t: nodes),
  is_path_in_graph (u, v, h :: t) G = true /\ contains_cycle G = false
  -> path_into_start (u, v, h :: t) G = false /\ path_out_of_h G u v h t = false
  -> get_sources_in_g_path G (u, v, h :: t) = u :: get_sources_in_g_path G (h, v, t).
Proof.
  intros G u h v t [Hp Hcyc] [Hin Hinh].
  unfold get_sources_in_g_path.
  destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Hinh. apply acyclic_path_one_direction_2 in Hinh.
    + rewrite Hinh. f_equal.
      unfold find_confounders_in_path. simpl. destruct t as [| h' t'].
      * simpl. unfold is_confounder_bool. simpl in Hinh. simpl in Hin. rewrite Hin. simpl. reflexivity.
      * simpl. assert (Hcon: is_confounder_bool u h' h G = false).
        { unfold is_confounder_bool. simpl in Hin. rewrite Hin. reflexivity. }
        rewrite Hcon. reflexivity.
    + split. apply is_path_in_graph_induction with (u := u). apply Hp. apply Hcyc.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Hinh. apply acyclic_path_one_direction_2 in Hinh.
    + rewrite Hinh. f_equal.
      unfold find_confounders_in_path. simpl. destruct t as [| h' t'].
      * simpl. unfold is_confounder_bool. simpl in Hin. rewrite Hin. simpl. reflexivity.
      * simpl. assert (Hcon: is_confounder_bool u h' h G = false).
        { unfold is_confounder_bool. simpl in Hin. rewrite Hin. reflexivity. }
        rewrite Hcon. reflexivity.
    + split. apply is_path_in_graph_induction with (u := u). apply Hp. apply Hcyc.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma sources_induction_into_end_rev: forall (G: graph) (u v h: node) (t: nodes),
  path_out_of_end (u, v, rev (h :: t)) G = Some false
  -> contains_cycle G = false
  -> is_path_in_graph (u, v, rev (h :: t)) G = true
  -> get_sources_in_g_path G (u, h, rev t) = get_sources_in_g_path G (u, v, rev (h :: t)).
Proof.
  intros G u v h t H Hcyc Hpath.
  unfold get_sources_in_g_path. rewrite H.
  destruct (path_out_of_end (u, h, rev t) G) as [[|]|] eqn:Houth.
  + assert (Hcon: find_confounders_in_path (u, h, rev t) G ++ [h] = find_confounders_in_path (u, v, rev (h :: t)) G).
    { simpl in H. simpl. simpl in Hpath. generalize dependent u. induction (rev t) as [| h' t' IH].
      - intros u H Hpath Houth. simpl. unfold is_confounder_bool. simpl in Houth. inversion Houth. rewrite H1. simpl in H. inversion H.
        simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hhv]. rewrite H2 in Hhv.
        rewrite andb_comm in Hhv. rewrite orb_comm in Hhv. simpl in Hhv. simpl. rewrite Hhv. reflexivity.
      - intros u H Hpath Houth. simpl. destruct t' as [| h'' t''].
        + simpl. destruct (is_confounder_bool u h h' G) as [|] eqn:Huhh'.
          * unfold is_confounder_bool. simpl in Houth. inversion Houth. rewrite H1. simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [_ Hhv].
            simpl in H. inversion H. simpl in Hhv. rewrite H2 in Hhv. rewrite andb_comm in Hhv. rewrite orb_comm in Hhv. simpl in Hhv. simpl. rewrite Hhv. simpl. reflexivity.
          * simpl. unfold is_confounder_bool. simpl in Houth. inversion Houth. rewrite H1. simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [_ Hhv].
             simpl in H. inversion H. simpl in Hhv. rewrite H2 in Hhv. rewrite andb_comm in Hhv. rewrite orb_comm in Hhv. simpl in Hhv. simpl. rewrite Hhv. simpl. reflexivity.
        + simpl. destruct (is_confounder_bool u h'' h' G) as [|] eqn:Huhh'.
          * simpl. f_equal. apply IH.
            -- simpl. simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. simpl. apply Houth.
          * simpl. apply IH.
            -- simpl. simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. simpl. apply Houth. }
    rewrite Hcon. destruct (path_into_start (u, v, rev (h :: t)) G) as [|] eqn:Hin.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
  + assert (Hcon: find_confounders_in_path (u, h, rev t) G = find_confounders_in_path (u, v, rev (h :: t)) G).
    { simpl in H. simpl. simpl in Hpath. generalize dependent u. induction (rev t) as [| h' t' IH].
      - intros u H Hpath Houth. simpl. unfold is_confounder_bool. simpl in Houth. inversion Houth. rewrite H1. simpl. reflexivity.
      - intros u H Hpath Houth. simpl. destruct t' as [| h'' t''].
        + simpl. destruct (is_confounder_bool u h h' G) as [|] eqn:Huhh'.
          * unfold is_confounder_bool. simpl in Houth. inversion Houth. rewrite H1. simpl. reflexivity.
          * simpl in H. unfold is_confounder_bool. simpl in Houth. inversion Houth. rewrite H1. simpl. reflexivity.
        + simpl. destruct (is_confounder_bool u h'' h' G) as [|] eqn:Huhh'.
          * f_equal. simpl in IH. apply IH.
            -- simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. apply Houth.
          * apply IH.
            -- simpl in H. simpl. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. simpl. apply Houth. }
    rewrite Hcon. destruct (path_into_start (u, v, rev (h :: t)) G) as [|] eqn:Hin.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
  + apply path_out_of_end_Some in Houth. exfalso. apply Houth.
Qed.

Lemma sources_induction_out_of_end_rev: forall (G: graph) (u v h: node) (t: nodes),
  path_out_of_end (u, v, rev (h :: t)) G = Some true
  -> contains_cycle G = false
  -> is_path_in_graph (u, v, rev (h :: t)) G = true
  -> exists (l: nodes), l ++ [v] = get_sources_in_g_path G (u, v, rev (h :: t)).
Proof.
  intros G u v h t H Hcyc Hpath.
  unfold get_sources_in_g_path. rewrite H. destruct (path_into_start (u, v, rev (h :: t)) G) as [|].
  - exists (find_confounders_in_path (u, v, rev (h :: t)) G). reflexivity.
  - exists (u :: find_confounders_in_path (u, v, rev (h :: t)) G). reflexivity.
Qed.


Lemma middle_sources_in_path: forall (G: graph) (u v: node) (l: nodes) (a b c: node) (l4: nodes),
  get_sources_in_g_path G (u, v, l) = a :: b :: c :: l4
  -> is_path_in_graph (u, v, l) G = true
  -> In b l.
Proof.
  intros G u v l a b c l4 H Hp.
  induction l as [| h t IH].
  - simpl in H. destruct (is_edge (v, u) G) as [|]. discriminate H. discriminate H.
  - unfold get_sources_in_g_path in H.
    destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
    + unfold nodes in *. rewrite Hout in H. destruct (path_into_start (u, v, h :: t) G) as [|] eqn:Hin.
      * apply intermediate_node_in_path with (x := b) in Hp. apply Hp. right. left.
        apply middle_node_not_end with (l' := l4) (v := v) (l'' := [a]) (c := c). apply H.
      * apply intermediate_node_in_path with (x := b) in Hp. apply Hp. right. left.
        apply middle_node_not_end with (l' := l4) (v := v) (l'' := []) (c := c). inversion H. apply H2.
    + unfold nodes in *. rewrite Hout in H. destruct (path_into_start (u, v, h :: t) G) as [|] eqn:Hin.
      * apply intermediate_node_in_path with (x := b) in Hp. apply Hp. right. left. unfold nodes in *. rewrite H.
        right. left. reflexivity.
      * apply intermediate_node_in_path with (x := b) in Hp. apply Hp. right. left. inversion H. simpl. rewrite H2.
        left. reflexivity.
    + apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma sources_not_in_Z: forall (G: graph) (p: path) (w: node) (Z: nodes),
  In w (get_sources_in_g_path G p)
  -> ~In (path_start p) Z /\ ~In (path_end p) Z
  -> d_connected_2 p G Z
  -> ~In w Z.
Proof.
  intros G p w Z Hw HZ Hconn HwZ. destruct p as [[u v] l].
  unfold get_sources_in_g_path in Hw. destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
      * destruct Hconn as [_ [Hconn _]]. apply no_overlap_non_member with (x := w) in Hconn. apply Hconn. apply HwZ. apply Hw.
      * destruct Hw as [Hw | Hw]. destruct HZ as [_ HZ]. apply HZ. simpl. rewrite Hw. apply HwZ. apply Hw.
    + destruct Hw as [Hw | Hw]. destruct HZ as [HZ]. apply HZ. simpl. rewrite Hw. apply HwZ.
      apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
      * destruct Hconn as [_ [Hconn _]]. apply no_overlap_non_member with (x := w) in Hconn. apply Hconn. apply HwZ. apply Hw.
      * destruct Hw as [Hw | Hw]. destruct HZ as [_ HZ]. apply HZ. simpl. rewrite Hw. apply HwZ. apply Hw.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + destruct Hconn as [_ [Hconn _]]. apply no_overlap_non_member with (x := w) in Hconn. apply Hconn. apply HwZ. apply Hw.
    + destruct Hw as [Hw | Hw]. destruct HZ as [HZ]. apply HZ. simpl. rewrite Hw. apply HwZ.
      destruct Hconn as [_ [Hconn _]]. apply no_overlap_non_member with (x := w) in Hconn. apply Hconn. apply HwZ. apply Hw.
  - apply Hw.
Qed.

Lemma confounders_in_sources: forall (G: graph) (a: node) (u v: node) (l: nodes),
  In a (find_confounders_in_path (u, v, l) G)
  -> In a (get_sources_in_g_path G (u, v, l)).
Proof.
  intros G a u v l H.
  unfold get_sources_in_g_path. destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply membership_append. apply H.
    + right. apply membership_append. apply H.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply H.
    + right. apply H.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma sources_confounders_or_endpoints: forall (G: graph) (a: node) (u v: node) (l: nodes),
  In a (get_sources_in_g_path G (u, v, l))
  -> a = u \/ In a (find_confounders_in_path (u, v, l) G) \/ a = v.
Proof.
  intros G a u v l H.
  unfold get_sources_in_g_path in H. destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply membership_append_or in H.
      destruct H as [H | H]. right. left. apply H. destruct H as [H | H]. right. right. symmetry. apply H.
      exfalso. apply H.
    + destruct H as [H | H]. left. symmetry. apply H. apply membership_append_or in H.
      destruct H as [H | H]. right. left. apply H. destruct H as [H | H]. right. right. symmetry. apply H.
      exfalso. apply H.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + right. left. apply H.
    + destruct H as [H | H]. left. symmetry. apply H. right. left. apply H.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma subpath_preserves_sources: forall (G: graph) (u v: node) (l1 l2 l: nodes) (b: node) (A A': nodes),
  contains_cycle G = false
  -> is_path_in_graph (u, v, l) G = true
  -> get_sources_in_g_path G (u, v, l) = A' ++ b :: A
  -> l1 ++ [b] ++ l2 = l
  -> acyclic_path_2 (u, v, l)
  -> get_sources_in_g_path G (b, v, l2) = b :: A.
Proof.
  intros G u v l1 l2 l b A A' HG Hp HA Hl Hcyc.

  assert (Hb: In b (find_confounders_in_path (u, v, l) G)).
  { assert (Hb: In b (get_sources_in_g_path G (u, v, l))). { rewrite HA. apply membership_append_r. left. reflexivity. }
    apply sources_confounders_or_endpoints in Hb. destruct Hb as [Hb | [Hb | Hb]].
    - destruct Hcyc as [_ [Hcyc _]]. exfalso. apply Hcyc. rewrite <- Hb. rewrite <- Hl. apply membership_append_r. left. reflexivity.
    - apply Hb.
    - destruct Hcyc as [_ [_ [Hcyc _]]]. exfalso. apply Hcyc. rewrite <- Hb. rewrite <- Hl. apply membership_append_r. left. reflexivity. }

  apply confounders_vs_edges_in_path in Hb. destruct Hb as [y [z [Hsub Hedge]]]. rewrite <- Hl in Hsub. destruct l2 as [| h2 t2].
  - rewrite append_identity in Hsub. assert (Hzv: z = v).
    { apply two_sublists_the_same with (l := u :: l1 ++ [b] ++ [v]) (a := b).
      - apply end_of_sublist_still_sublist_2 in Hsub. rewrite <- app_assoc in Hsub. apply Hsub.
      - apply sublist_breaks_down_list. exists (u :: l1). exists []. simpl. reflexivity.
      - apply acyclic_path_count with (x := b) in Hcyc. rewrite <- Hl in Hcyc. rewrite append_identity in Hcyc. rewrite <- app_assoc in Hcyc. apply Hcyc.
        right. rewrite <- Hl. apply membership_append. apply membership_append_r. left. reflexivity. }
    simpl. destruct Hedge as [_ Hedge]. rewrite Hzv in Hedge. apply acyclic_no_two_cycle in Hedge. rewrite Hedge. 2: { apply HG. }
    unfold get_sources_in_g_path in HA.
    assert (Hout: path_out_of_end (u, v, l) G = Some false).
    { rewrite <- Hl. rewrite append_identity. apply sublist_path_out_of_end_false with (x := b). apply Hedge. rewrite Hzv in Hsub. apply end_of_sublist_still_sublist_2 in Hsub. apply Hsub.
      intros Hv. destruct Hv as [Hv | Hv]. destruct Hcyc as [Hcyc _]. apply Hcyc. apply Hv. destruct Hcyc as [_ [_ [Hcyc _]]]. apply Hcyc. rewrite <- Hl. rewrite append_identity. apply Hv. }
    rewrite Hout in HA.
    destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + pose proof Hl as Hl'. apply subpath_preserves_confounders_2 with (w := u) (v := v) (G := G) in Hl. destruct Hl as [Hl | Hl].
      * rewrite Hl in HA.
        assert (Hlem: find_confounders_in_path (u, b, l1) G = A' /\ find_confounders_in_path (b, v, []) G = A).
        { apply acyclic_path_equate_sublists with (m := b). split. 2: { apply HA. }
          apply acyclic_path_intermediate_nodes. intros x.
          destruct (member x (find_confounders_in_path (u, b, l1) G)) as [|] eqn:Hmem1.
          - right. rewrite count_app.
            assert (Hcyc': acyclic_path_2 (u, b, l1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := []) (l3 := l). split. apply Hl'. apply Hcyc. }
            assert (Hp': is_path_in_graph (u, b, l1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := []) (l3 := l). split. apply Hl'. apply Hp. }

            rewrite confounder_count_acyclic.
            2: { apply member_In_equiv. apply Hmem1. } 2: { apply Hcyc'. } 2: { apply Hp'. }
            simpl. destruct (b =? x) as [|] eqn:Hbx.
            + apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left. apply member_In_equiv.
              apply eqb_eq in Hbx. rewrite Hbx in *. apply Hmem1.
            + reflexivity.
          - rewrite count_app. apply not_member_count_0 in Hmem1. rewrite Hmem1. simpl. destruct (b =? x) as [|] eqn:Hbx. right. reflexivity. left. reflexivity. }
        destruct Hlem as [Hlem1 Hlem2]. simpl in Hlem2. rewrite <- Hlem2. reflexivity.
      * exfalso. assert (Hb: In b (A' ++ b :: A)). { apply membership_append_r. left. reflexivity. } rewrite <- HA in Hb. rewrite Hl in Hb. apply membership_append_or in Hb.
        destruct Hb as [Hb | Hb].
        -- assert (Hcyc': acyclic_path_2 (u, b, l1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := []) (l3 := l). split. apply Hl'. apply Hcyc. }
           assert (Hp': is_path_in_graph (u, b, l1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := []) (l3 := l). split. apply Hl'. apply Hp. }
           apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left. apply Hb.
        -- simpl in Hb. apply Hb.
    + destruct A' as [| ha ta]. inversion HA. exfalso. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. rewrite H0. rewrite <- Hl. apply membership_append_r. left. reflexivity.
      assert (HA': find_confounders_in_path (u, v, l) G = ta ++ b :: A). { inversion HA. simpl. reflexivity. }
      clear HA. pose proof HA' as HA. clear HA'.
      pose proof Hl as Hl'. apply subpath_preserves_confounders_2 with (w := u) (v := v) (G := G) in Hl. destruct Hl as [Hl | Hl].
      * rewrite Hl in HA.
        assert (Hlem: find_confounders_in_path (u, b, l1) G = ta /\ find_confounders_in_path (b, v, []) G = A).
        { apply acyclic_path_equate_sublists with (m := b). split. 2: { apply HA. }
          apply acyclic_path_intermediate_nodes. intros x.
          destruct (member x (find_confounders_in_path (u, b, l1) G)) as [|] eqn:Hmem1.
          - right. rewrite count_app.
            assert (Hcyc': acyclic_path_2 (u, b, l1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := []) (l3 := l). split. apply Hl'. apply Hcyc. }
            assert (Hp': is_path_in_graph (u, b, l1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := []) (l3 := l). split. apply Hl'. apply Hp. }

            rewrite confounder_count_acyclic.
            2: { apply member_In_equiv. apply Hmem1. } 2: { apply Hcyc'. } 2: { apply Hp'. }
            simpl. destruct (b =? x) as [|] eqn:Hbx.
            + apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left. apply member_In_equiv.
              apply eqb_eq in Hbx. rewrite Hbx in *. apply Hmem1.
            + reflexivity.
          - rewrite count_app. apply not_member_count_0 in Hmem1. rewrite Hmem1. simpl. destruct (b =? x) as [|] eqn:Hbx. right. reflexivity. left. reflexivity. }
        destruct Hlem as [Hlem1 Hlem2]. simpl in Hlem2. rewrite <- Hlem2. reflexivity.
      * exfalso. assert (Hb: In b (ta ++ b :: A)). { apply membership_append_r. left. reflexivity. } rewrite <- HA in Hb. rewrite Hl in Hb. apply membership_append_or in Hb.
        destruct Hb as [Hb | Hb].
        -- assert (Hcyc': acyclic_path_2 (u, b, l1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := []) (l3 := l). split. apply Hl'. apply Hcyc. }
           assert (Hp': is_path_in_graph (u, b, l1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := []) (l3 := l). split. apply Hl'. apply Hp. }
           apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left. apply Hb.
        -- simpl in Hb. apply Hb.
  - assert (Hzv: z = h2).
    { apply two_sublists_the_same with (l := u :: l1 ++ [b] ++ h2 :: t2 ++ [v]) (a := b).
      - apply end_of_sublist_still_sublist_2 in Hsub. rewrite <- app_assoc in Hsub. rewrite <- app_assoc in Hsub. apply Hsub.
      - apply sublist_breaks_down_list. exists (u :: l1). exists (t2 ++ [v]). simpl. reflexivity.
      - apply acyclic_path_count with (x := b) in Hcyc. rewrite <- Hl in Hcyc. rewrite <- app_assoc in Hcyc. rewrite <- app_assoc in Hcyc. apply Hcyc.
        right. rewrite <- Hl. apply membership_append. apply membership_append_r. left. reflexivity. }
    unfold get_sources_in_g_path. destruct Hedge as [_ Hedge]. rewrite Hzv in Hedge. apply acyclic_no_two_cycle in Hedge. 2: { apply HG. }
    unfold get_sources_in_g_path in HA.

    destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
    { assert (Hout': path_out_of_end (b, v, h2 :: t2) G = Some true). { rewrite <- subpath_preserves_path_out_of_end with (u := u) (l1 := l1) (l := l). apply Hout. symmetry. apply Hl. }
      unfold nodes in *. unfold node in *. rewrite Hout'. simpl. unfold nodes in *. unfold node in *. rewrite Hedge.
      destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
      + pose proof Hl as Hl'. apply subpath_preserves_confounders_2 with (w := u) (v := v) (G := G) in Hl. destruct Hl as [Hl | Hl].
        * unfold nodes in *. unfold node in *. rewrite Hl in HA.
          assert (Hlem: find_confounders_in_path (u, b, l1) G = A' /\ find_confounders_in_path (b, v, h2 :: t2) G ++ [v] = A).
          { apply acyclic_path_equate_sublists with (m := b). split. 2: { rewrite <- app_assoc in HA. apply HA. }
            apply acyclic_path_intermediate_nodes. intros x.
            destruct (member x (find_confounders_in_path (u, b, l1) G)) as [|] eqn:Hmem1.
            - right. rewrite count_app.
              assert (Hcyc': acyclic_path_2 (u, b, l1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split. apply Hl'. apply Hcyc. }
              assert (Hp': is_path_in_graph (u, b, l1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split. apply Hl'. apply Hp. }

              rewrite confounder_count_acyclic.
              2: { apply member_In_equiv. apply Hmem1. } 2: { apply Hcyc'. } 2: { apply Hp'. }
              destruct (b =? x) as [|] eqn:Hbx.
              + apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left. apply member_In_equiv.
                apply eqb_eq in Hbx. rewrite Hbx in *. apply Hmem1.
              + rewrite count_app. rewrite count_app.
                destruct (member x (find_confounders_in_path (b, v, h2 :: t2) G)) as [|] eqn:Hmem2.
                * (* contra: x appears in l1 and in h2 :: t2 *)
                  assert (Hx1: In x l1). { apply intermediate_node_in_path with (x := x) in Hp'. apply Hp'. right. left. apply member_In_equiv. apply Hmem1. }
                  assert (Hx2: In x (h2 :: t2)).
                  { assert (Hp'': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hp. }
                    apply intermediate_node_in_path with (x := x) in Hp''. apply Hp''. right. left. apply member_In_equiv. apply Hmem2. }
                  apply acyclic_path_count with (x := x) in Hcyc.
                  assert (Hc: count x l >= 2).
                  { rewrite <- Hl'. rewrite count_app. rewrite count_app. apply member_count_at_least_1 in Hx1. apply member_count_at_least_1 in Hx2. lia. }
                  simpl in Hcyc. rewrite count_app in Hcyc. destruct (u =? x) as [|]. lia. lia. right. apply membership_append. rewrite <- Hl'. apply membership_append. apply Hx1.
                * apply not_member_count_0 in Hmem2. rewrite Hmem2. simpl. rewrite Hbx. destruct (v =? x) as [|] eqn:Hvx.
                  -- apply intermediate_node_in_path with (x := v) in Hp. exfalso. destruct Hcyc as [_ [_ [Hcyc _]]]. apply Hcyc. apply Hp. right. left. unfold nodes in *. unfold node in *. rewrite Hl. apply membership_append. apply member_In_equiv.
                     apply eqb_eq in Hvx. rewrite Hvx in *. apply Hmem1.
                  -- simpl. reflexivity.
            - rewrite count_app. apply not_member_count_0 in Hmem1. rewrite Hmem1. destruct (b =? x) as [|] eqn:Hbx.
              + right. rewrite count_app. rewrite count_app.
                destruct (member x (find_confounders_in_path (b, v, h2 :: t2) G)) as [|] eqn:Hmem2.
                * assert (Hx2: In b (h2 :: t2)).
                  { assert (Hp'': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hp. }
                    apply intermediate_node_in_path with (x := b) in Hp''. apply Hp''. right. left. apply member_In_equiv. apply eqb_eq in Hbx. rewrite Hbx in *. apply Hmem2. }
                  apply acyclic_path_count with (x := b) in Hcyc.
                  assert (Hc: count b l >= 2).
                  { rewrite <- Hl'. rewrite count_app. rewrite count_app. apply member_count_at_least_1 in Hx2. simpl. rewrite eqb_refl. simpl in Hx2. lia. }
                  simpl in Hcyc. rewrite count_app in Hcyc. destruct (u =? b) as [|]. lia. lia. right. apply membership_append. rewrite <- Hl'. apply membership_append_r. left. reflexivity.
                * apply not_member_count_0 in Hmem2. rewrite Hmem2. simpl. rewrite Hbx. destruct (v =? x) as [|] eqn:Hvx.
                  -- destruct Hcyc as [_ [_ [Hcyc _]]]. exfalso. apply Hcyc. rewrite <- Hl'. apply membership_append_r. left. apply eqb_eq in Hbx. rewrite Hbx. symmetry. apply eqb_eq. apply Hvx.
                  -- simpl. reflexivity.
              + rewrite count_app. rewrite count_app.
                destruct (member x (find_confounders_in_path (b, v, h2 :: t2) G)) as [|] eqn:Hmem2.
                * right. assert (Hcyc': acyclic_path_2 (b, v, h2 :: t2)). { apply subpath_still_acyclic with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hcyc. }
                  assert (Hp': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hp. }

                  rewrite confounder_count_acyclic.
                  2: { apply member_In_equiv. apply Hmem2. } 2: { apply Hcyc'. } 2: { apply Hp'. }
                  destruct (v =? x) as [|] eqn:Hvx.
                  -- apply intermediate_node_in_path with (x := v) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left.
                     apply eqb_eq in Hvx. rewrite Hvx in *. apply member_In_equiv. apply Hmem2.
                  -- simpl. rewrite Hbx. rewrite Hvx. reflexivity.
                * apply not_member_count_0 in Hmem2. rewrite Hmem2. simpl. rewrite Hbx. destruct (v =? x) as [|] eqn:Hvx. right. reflexivity. left. reflexivity. }
          destruct Hlem as [Hlem1 Hlem2]. simpl in Hlem2. rewrite <- Hlem2. reflexivity.
        * exfalso. assert (Hb: In b (A' ++ b :: A)). { apply membership_append_r. left. reflexivity. } rewrite <- HA in Hb. unfold nodes in *. unfold node in *. rewrite Hl in Hb. apply membership_append_or in Hb.
          destruct Hb as [Hb | Hb].
          -- apply membership_append_or in Hb. destruct Hb as [Hb | Hb].
             ++ assert (Hcyc': acyclic_path_2 (u, b, l1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split.  apply Hl'. apply Hcyc. }
                assert (Hp': is_path_in_graph (u, b, l1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split. unfold nodes in *. unfold node in *. apply Hl'. apply Hp. }
                apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left. apply Hb.
             ++ assert (Hcyc': acyclic_path_2 (b, v, h2 :: t2)). { apply subpath_still_acyclic with (w := u) (l1 := l1) (l3 := l). split.  apply Hl'. apply Hcyc. }
                assert (Hp': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. unfold nodes in *. unfold node in *. apply Hl'. apply Hp. }
                apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [Hcyc' _]]. apply Hcyc'. apply Hp'. right. left. apply Hb.
          -- destruct Hcyc as [_ [_ [Hcyc _]]]. apply Hcyc. destruct Hb as [Hb | Hb]. rewrite Hb. rewrite <- Hl'. apply membership_append_r. left. reflexivity. exfalso. apply Hb.
      + destruct A' as [| ha ta]. inversion HA. exfalso. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. rewrite H0. rewrite <- Hl. apply membership_append_r. left. reflexivity.
        assert (HA': find_confounders_in_path (u, v, l) G ++ [v] = ta ++ b :: A). { inversion HA. simpl. reflexivity. }
        clear HA. pose proof HA' as HA. clear HA'.
        pose proof Hl as Hl'. apply subpath_preserves_confounders_2 with (w := u) (v := v) (G := G) in Hl. destruct Hl as [Hl | Hl].
        * unfold nodes in *. unfold node in *. rewrite Hl in HA.
          assert (Hlem: find_confounders_in_path (u, b, l1) G = ta /\ find_confounders_in_path (b, v, h2 :: t2) G ++ [v] = A).
          { apply acyclic_path_equate_sublists with (m := b). split. 2: { rewrite <- app_assoc in HA. apply HA. }
            apply acyclic_path_intermediate_nodes. intros x.
            destruct (member x (find_confounders_in_path (u, b, l1) G)) as [|] eqn:Hmem1.
            - right. rewrite count_app.
              assert (Hcyc': acyclic_path_2 (u, b, l1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split. apply Hl'. apply Hcyc. }
              assert (Hp': is_path_in_graph (u, b, l1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split. apply Hl'. apply Hp. }

              rewrite confounder_count_acyclic.
              2: { apply member_In_equiv. apply Hmem1. } 2: { apply Hcyc'. } 2: { apply Hp'. }
              destruct (b =? x) as [|] eqn:Hbx.
              + apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left. apply member_In_equiv.
                apply eqb_eq in Hbx. rewrite Hbx in *. apply Hmem1.
              + rewrite count_app. rewrite count_app.
                destruct (member x (find_confounders_in_path (b, v, h2 :: t2) G)) as [|] eqn:Hmem2.
                * (* contra: x appears in l1 and in h2 :: t2 *)
                  assert (Hx1: In x l1). { apply intermediate_node_in_path with (x := x) in Hp'. apply Hp'. right. left. apply member_In_equiv. apply Hmem1. }
                  assert (Hx2: In x (h2 :: t2)).
                  { assert (Hp'': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hp. }
                    apply intermediate_node_in_path with (x := x) in Hp''. apply Hp''. right. left. apply member_In_equiv. apply Hmem2. }
                  apply acyclic_path_count with (x := x) in Hcyc.
                  assert (Hc: count x l >= 2).
                  { rewrite <- Hl'. rewrite count_app. rewrite count_app. apply member_count_at_least_1 in Hx1. apply member_count_at_least_1 in Hx2. lia. }
                  simpl in Hcyc. rewrite count_app in Hcyc. destruct (u =? x) as [|]. lia. lia. right. apply membership_append. rewrite <- Hl'. apply membership_append. apply Hx1.
                * apply not_member_count_0 in Hmem2. rewrite Hmem2. simpl. rewrite Hbx. destruct (v =? x) as [|] eqn:Hvx.
                  -- apply intermediate_node_in_path with (x := v) in Hp. exfalso. destruct Hcyc as [_ [_ [Hcyc _]]]. apply Hcyc. apply Hp. right. left. unfold nodes in *. unfold node in *. rewrite Hl. apply membership_append. apply member_In_equiv.
                     apply eqb_eq in Hvx. rewrite Hvx in *. apply Hmem1.
                  -- simpl. reflexivity.
            - rewrite count_app. apply not_member_count_0 in Hmem1. rewrite Hmem1. destruct (b =? x) as [|] eqn:Hbx.
              + right. rewrite count_app. rewrite count_app.
                destruct (member x (find_confounders_in_path (b, v, h2 :: t2) G)) as [|] eqn:Hmem2.
                * (* contra: b appears in h2 :: t2 *)
                  assert (Hx2: In b (h2 :: t2)).
                  { assert (Hp'': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hp. }
                    apply intermediate_node_in_path with (x := b) in Hp''. apply Hp''. right. left. apply member_In_equiv. apply eqb_eq in Hbx. rewrite Hbx in *. apply Hmem2. }
                  apply acyclic_path_count with (x := b) in Hcyc.
                  assert (Hc: count b l >= 2).
                  { rewrite <- Hl'. rewrite count_app. rewrite count_app. apply member_count_at_least_1 in Hx2. simpl. rewrite eqb_refl. simpl in Hx2. lia. }
                  simpl in Hcyc. rewrite count_app in Hcyc. destruct (u =? b) as [|]. lia. lia. right. apply membership_append. rewrite <- Hl'. apply membership_append_r. left. reflexivity.
                * apply not_member_count_0 in Hmem2. rewrite Hmem2. simpl. rewrite Hbx. destruct (v =? x) as [|] eqn:Hvx.
                  -- destruct Hcyc as [_ [_ [Hcyc _]]]. exfalso. apply Hcyc. rewrite <- Hl'. apply membership_append_r. left. apply eqb_eq in Hbx. rewrite Hbx. symmetry. apply eqb_eq. apply Hvx.
                  -- simpl. reflexivity.
              + rewrite count_app. rewrite count_app.
                destruct (member x (find_confounders_in_path (b, v, h2 :: t2) G)) as [|] eqn:Hmem2.
                * right. assert (Hcyc': acyclic_path_2 (b, v, h2 :: t2)). { apply subpath_still_acyclic with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hcyc. }
                  assert (Hp': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hp. }

                  rewrite confounder_count_acyclic.
                  2: { apply member_In_equiv. apply Hmem2. } 2: { apply Hcyc'. } 2: { apply Hp'. }
                  destruct (v =? x) as [|] eqn:Hvx.
                  -- apply intermediate_node_in_path with (x := v) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left.
                     apply eqb_eq in Hvx. rewrite Hvx in *. apply member_In_equiv. apply Hmem2.
                  -- simpl. rewrite Hbx. rewrite Hvx. reflexivity.
                * apply not_member_count_0 in Hmem2. rewrite Hmem2. simpl. rewrite Hbx. destruct (v =? x) as [|] eqn:Hvx. right. reflexivity. left. reflexivity. }
          destruct Hlem as [Hlem1 Hlem2]. simpl in Hlem2. rewrite <- Hlem2. reflexivity.
        * exfalso. assert (Hb: In b (ta ++ b :: A)). { apply membership_append_r. left. reflexivity. } rewrite <- HA in Hb. unfold nodes in *. unfold node in *. rewrite Hl in Hb. apply membership_append_or in Hb.
          destruct Hb as [Hb | Hb].
          -- apply membership_append_or in Hb. destruct Hb as [Hb | Hb].
             ++ assert (Hcyc': acyclic_path_2 (u, b, l1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split.  apply Hl'. apply Hcyc. }
                assert (Hp': is_path_in_graph (u, b, l1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split. unfold nodes in *. unfold node in *. apply Hl'. apply Hp. }
                apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left. apply Hb.
             ++ assert (Hcyc': acyclic_path_2 (b, v, h2 :: t2)). { apply subpath_still_acyclic with (w := u) (l1 := l1) (l3 := l). split.  apply Hl'. apply Hcyc. }
                assert (Hp': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. unfold nodes in *. unfold node in *. apply Hl'. apply Hp. }
                apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [Hcyc' _]]. apply Hcyc'. apply Hp'. right. left. apply Hb.
          -- destruct Hcyc as [_ [_ [Hcyc _]]]. apply Hcyc. destruct Hb as [Hb | Hb]. rewrite Hb. rewrite <- Hl'. apply membership_append_r. left. reflexivity. exfalso. apply Hb. }

    { assert (Hout': path_out_of_end (b, v, h2 :: t2) G = Some false). { rewrite <- subpath_preserves_path_out_of_end with (u := u) (l1 := l1) (l := l). apply Hout. symmetry. apply Hl. }
      unfold nodes in *. unfold node in *. rewrite Hout'. simpl. unfold nodes in *. unfold node in *. rewrite Hedge.
      destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
      + pose proof Hl as Hl'. apply subpath_preserves_confounders_2 with (w := u) (v := v) (G := G) in Hl. destruct Hl as [Hl | Hl].
        * unfold nodes in *. unfold node in *. rewrite Hl in HA.
          assert (Hlem: find_confounders_in_path (u, b, l1) G = A' /\ find_confounders_in_path (b, v, h2 :: t2) G = A).
          { apply acyclic_path_equate_sublists with (m := b). split. 2: { apply HA. }
            apply acyclic_path_intermediate_nodes. intros x.
            destruct (member x (find_confounders_in_path (u, b, l1) G)) as [|] eqn:Hmem1.
            - right. rewrite count_app.
              assert (Hcyc': acyclic_path_2 (u, b, l1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split. apply Hl'. apply Hcyc. }
              assert (Hp': is_path_in_graph (u, b, l1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split. apply Hl'. apply Hp. }

              rewrite confounder_count_acyclic.
              2: { apply member_In_equiv. apply Hmem1. } 2: { apply Hcyc'. } 2: { apply Hp'. }
              destruct (b =? x) as [|] eqn:Hbx.
              + apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left. apply member_In_equiv.
                apply eqb_eq in Hbx. rewrite Hbx in *. apply Hmem1.
              + rewrite count_app.
                destruct (member x (find_confounders_in_path (b, v, h2 :: t2) G)) as [|] eqn:Hmem2.
                * (* contra: x appears in l1 and in h2 :: t2 *)
                  assert (Hx1: In x l1). { apply intermediate_node_in_path with (x := x) in Hp'. apply Hp'. right. left. apply member_In_equiv. apply Hmem1. }
                  assert (Hx2: In x (h2 :: t2)).
                  { assert (Hp'': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hp. }
                    apply intermediate_node_in_path with (x := x) in Hp''. apply Hp''. right. left. apply member_In_equiv. apply Hmem2. }
                  apply acyclic_path_count with (x := x) in Hcyc.
                  assert (Hc: count x l >= 2).
                  { rewrite <- Hl'. rewrite count_app. rewrite count_app. apply member_count_at_least_1 in Hx1. apply member_count_at_least_1 in Hx2. lia. }
                  simpl in Hcyc. rewrite count_app in Hcyc. destruct (u =? x) as [|]. lia. lia. right. apply membership_append. rewrite <- Hl'. apply membership_append. apply Hx1.
                * apply not_member_count_0 in Hmem2. rewrite Hmem2. simpl. rewrite Hbx. reflexivity.
            - rewrite count_app. apply not_member_count_0 in Hmem1. rewrite Hmem1. destruct (b =? x) as [|] eqn:Hbx.
              + right. rewrite count_app.
                destruct (member x (find_confounders_in_path (b, v, h2 :: t2) G)) as [|] eqn:Hmem2.
                * (* contra: b appears in h2 :: t2 *)
                  assert (Hx2: In b (h2 :: t2)).
                  { assert (Hp'': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hp. }
                    apply intermediate_node_in_path with (x := b) in Hp''. apply Hp''. right. left. apply member_In_equiv. apply eqb_eq in Hbx. rewrite Hbx in *. apply Hmem2. }
                  apply acyclic_path_count with (x := b) in Hcyc.
                  assert (Hc: count b l >= 2).
                  { rewrite <- Hl'. rewrite count_app. rewrite count_app. apply member_count_at_least_1 in Hx2. simpl. rewrite eqb_refl. simpl in Hx2. lia. }
                  simpl in Hcyc. rewrite count_app in Hcyc. destruct (u =? b) as [|]. lia. lia. right. apply membership_append. rewrite <- Hl'. apply membership_append_r. left. reflexivity.
                * apply not_member_count_0 in Hmem2. rewrite Hmem2. simpl. rewrite Hbx. reflexivity.
              + rewrite count_app.
                destruct (member x (find_confounders_in_path (b, v, h2 :: t2) G)) as [|] eqn:Hmem2.
                * right. assert (Hcyc': acyclic_path_2 (b, v, h2 :: t2)). { apply subpath_still_acyclic with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hcyc. }
                  assert (Hp': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hp. }

                  rewrite confounder_count_acyclic.
                  2: { apply member_In_equiv. apply Hmem2. } 2: { apply Hcyc'. } 2: { apply Hp'. }
                  simpl. rewrite Hbx. reflexivity.
                * apply not_member_count_0 in Hmem2. rewrite Hmem2. simpl. rewrite Hbx. left. reflexivity. }
          destruct Hlem as [Hlem1 Hlem2]. simpl in Hlem2. rewrite <- Hlem2. reflexivity.
        * exfalso. assert (Hb: In b (A' ++ b :: A)). { apply membership_append_r. left. reflexivity. } rewrite <- HA in Hb. unfold nodes in *. unfold node in *. rewrite Hl in Hb. apply membership_append_or in Hb.
          destruct Hb as [Hb | Hb].
          -- assert (Hcyc': acyclic_path_2 (u, b, l1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split.  apply Hl'. apply Hcyc. }
             assert (Hp': is_path_in_graph (u, b, l1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split. unfold nodes in *. unfold node in *. apply Hl'. apply Hp. }
             apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left. apply Hb.
          -- assert (Hcyc': acyclic_path_2 (b, v, h2 :: t2)). { apply subpath_still_acyclic with (w := u) (l1 := l1) (l3 := l). split.  apply Hl'. apply Hcyc. }
             assert (Hp': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. unfold nodes in *. unfold node in *. apply Hl'. apply Hp. }
             apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [Hcyc' _]]. apply Hcyc'. apply Hp'. right. left. apply Hb.
      + destruct A' as [| ha ta]. inversion HA. exfalso. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. rewrite H0. rewrite <- Hl. apply membership_append_r. left. reflexivity.
        assert (HA': find_confounders_in_path (u, v, l) G = ta ++ b :: A). { inversion HA. simpl. reflexivity. }
        clear HA. pose proof HA' as HA. clear HA'.
        pose proof Hl as Hl'. apply subpath_preserves_confounders_2 with (w := u) (v := v) (G := G) in Hl. destruct Hl as [Hl | Hl].
        * unfold nodes in *. unfold node in *. rewrite Hl in HA.
          assert (Hlem: find_confounders_in_path (u, b, l1) G = ta /\ find_confounders_in_path (b, v, h2 :: t2) G = A).
          { apply acyclic_path_equate_sublists with (m := b). split. 2: { apply HA. }
            apply acyclic_path_intermediate_nodes. intros x.
            destruct (member x (find_confounders_in_path (u, b, l1) G)) as [|] eqn:Hmem1.
            - right. rewrite count_app.
              assert (Hcyc': acyclic_path_2 (u, b, l1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split. apply Hl'. apply Hcyc. }
              assert (Hp': is_path_in_graph (u, b, l1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split. apply Hl'. apply Hp. }

              rewrite confounder_count_acyclic.
              2: { apply member_In_equiv. apply Hmem1. } 2: { apply Hcyc'. } 2: { apply Hp'. }
              destruct (b =? x) as [|] eqn:Hbx.
              + apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left. apply member_In_equiv.
                apply eqb_eq in Hbx. rewrite Hbx in *. apply Hmem1.
              + rewrite count_app.
                destruct (member x (find_confounders_in_path (b, v, h2 :: t2) G)) as [|] eqn:Hmem2.
                * (* contra: x appears in l1 and in h2 :: t2 *)
                  assert (Hx1: In x l1). { apply intermediate_node_in_path with (x := x) in Hp'. apply Hp'. right. left. apply member_In_equiv. apply Hmem1. }
                  assert (Hx2: In x (h2 :: t2)).
                  { assert (Hp'': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hp. }
                    apply intermediate_node_in_path with (x := x) in Hp''. apply Hp''. right. left. apply member_In_equiv. apply Hmem2. }
                  apply acyclic_path_count with (x := x) in Hcyc.
                  assert (Hc: count x l >= 2).
                  { rewrite <- Hl'. rewrite count_app. rewrite count_app. apply member_count_at_least_1 in Hx1. apply member_count_at_least_1 in Hx2. lia. }
                  simpl in Hcyc. rewrite count_app in Hcyc. destruct (u =? x) as [|]. lia. lia. right. apply membership_append. rewrite <- Hl'. apply membership_append. apply Hx1.
                * apply not_member_count_0 in Hmem2. rewrite Hmem2. simpl. rewrite Hbx. reflexivity.
            - rewrite count_app. apply not_member_count_0 in Hmem1. rewrite Hmem1. destruct (b =? x) as [|] eqn:Hbx.
              + right. rewrite count_app.
                destruct (member x (find_confounders_in_path (b, v, h2 :: t2) G)) as [|] eqn:Hmem2.
                * (* contra: b appears in h2 :: t2 *)
                  assert (Hx2: In b (h2 :: t2)).
                  { assert (Hp'': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hp. }
                    apply intermediate_node_in_path with (x := b) in Hp''. apply Hp''. right. left. apply member_In_equiv. apply eqb_eq in Hbx. rewrite Hbx in *. apply Hmem2. }
                  apply acyclic_path_count with (x := b) in Hcyc.
                  assert (Hc: count b l >= 2).
                  { rewrite <- Hl'. rewrite count_app. rewrite count_app. apply member_count_at_least_1 in Hx2. simpl. rewrite eqb_refl. simpl in Hx2. lia. }
                  simpl in Hcyc. rewrite count_app in Hcyc. destruct (u =? b) as [|]. lia. lia. right. apply membership_append. rewrite <- Hl'. apply membership_append_r. left. reflexivity.
                * apply not_member_count_0 in Hmem2. rewrite Hmem2. simpl. rewrite Hbx. reflexivity.
              + rewrite count_app.
                destruct (member x (find_confounders_in_path (b, v, h2 :: t2) G)) as [|] eqn:Hmem2.
                * right. assert (Hcyc': acyclic_path_2 (b, v, h2 :: t2)). { apply subpath_still_acyclic with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hcyc. }
                  assert (Hp': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hl'. apply Hp. }

                  rewrite confounder_count_acyclic.
                  2: { apply member_In_equiv. apply Hmem2. } 2: { apply Hcyc'. } 2: { apply Hp'. }
                  simpl. rewrite Hbx. reflexivity.
                * apply not_member_count_0 in Hmem2. rewrite Hmem2. simpl. rewrite Hbx. left. reflexivity. }
          destruct Hlem as [Hlem1 Hlem2]. simpl in Hlem2. rewrite <- Hlem2. reflexivity.
        * exfalso. assert (Hb: In b (ta ++ b :: A)). { apply membership_append_r. left. reflexivity. } rewrite <- HA in Hb. unfold nodes in *. unfold node in *. rewrite Hl in Hb. apply membership_append_or in Hb.
          destruct Hb as [Hb | Hb].
          -- assert (Hcyc': acyclic_path_2 (u, b, l1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split.  apply Hl'. apply Hcyc. }
             assert (Hp': is_path_in_graph (u, b, l1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := h2 :: t2) (l3 := l). split. unfold nodes in *. unfold node in *. apply Hl'. apply Hp. }
             apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [_ [Hcyc' _]]]. apply Hcyc'. apply Hp'. right. left. apply Hb.
          -- assert (Hcyc': acyclic_path_2 (b, v, h2 :: t2)). { apply subpath_still_acyclic with (w := u) (l1 := l1) (l3 := l). split.  apply Hl'. apply Hcyc. }
             assert (Hp': is_path_in_graph (b, v, h2 :: t2) G = true). { apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. unfold nodes in *. unfold node in *. apply Hl'. apply Hp. }
             apply intermediate_node_in_path with (x := b) in Hp'. exfalso. destruct Hcyc' as [_ [Hcyc' _]]. apply Hcyc'. apply Hp'. right. left. apply Hb. }
    { exfalso. apply path_out_of_end_Some in Hout. apply Hout. }
Qed.

Lemma sources_len: forall (G: graph) (u v: node) (l L: nodes),
  is_path_in_graph (u, v, l) G = true
  -> contains_cycle G = false
  -> get_sources_in_g_path G (u, v, l) = L
  -> length L <= path_length (u, v, l).
Proof.
  intros G u v l L Hp Hc HL.
  generalize dependent u. generalize dependent L. induction l as [| h t IH].
  - intros L u Hp HL. simpl in HL. destruct (is_edge (v, u) G) as [|]. rewrite <- HL. simpl. unfold path_length. lia.
    rewrite <- HL. unfold path_length. simpl. lia.
  - intros L u Hp HL. destruct (path_into_start (u, v, h :: t) G) as [|] eqn:Hin.
    + apply sources_induction_into_start in Hin.
      * assert (Hind: length L <= path_length (h, v, t)).
        { apply IH. apply is_path_in_graph_induction with (u := u). apply Hp. rewrite <- HL. symmetry. apply Hin. }
        unfold path_length. unfold path_length in Hind. simpl. simpl in Hind. lia.
      * split. apply Hp. apply Hc.
    + destruct (path_out_of_h G u v h t) as [|] eqn:Hout.
      * assert (HA1: exists (A: nodes), get_sources_in_g_path G (u, v, h :: t) = u :: A /\
                                        get_sources_in_g_path G (h, v, t) = h :: A).
        { apply sources_induction_out_of_start_out_of_h. split. apply Hp. apply Hc. split. apply Hin. apply Hout. }
        destruct HA1 as [A HA1].

        assert (Hind: length (h :: A) <= path_length (h, v, t)).
        { apply IH. apply is_path_in_graph_induction with (u := u). apply Hp. apply HA1. }
        unfold path_length. unfold path_length in Hind. destruct HA1 as [HA1 _]. rewrite <- HL. unfold nodes in *.
        rewrite HA1. simpl. simpl in Hind. lia.
      * assert (HA1: get_sources_in_g_path G (u, v, h :: t) = u :: get_sources_in_g_path G (h, v, t)).
        { apply sources_induction_out_of_start_into_h. split. apply Hp. apply Hc. split. apply Hin. apply Hout. }
        assert (Hind: length (get_sources_in_g_path G (h, v, t)) <= path_length (h, v, t)).
        { apply IH. apply is_path_in_graph_induction with (u := u). apply Hp. reflexivity. }
        unfold path_length. unfold path_length in Hind. rewrite <- HL. unfold nodes in *.
        rewrite HA1. simpl. simpl in Hind. lia.
Qed.

Lemma next_source_is_unblocked_ancestor: forall (x: node) (l4: nodes) (u v: node) (l: nodes) (G: graph) (Z: nodes),
  contains_cycle G = false
  -> ~In v Z
  -> is_path_in_graph (u, v, l) G = true
  -> acyclic_path_2 (u, v, l)
  -> get_sources_in_g_path G (u, v, l) = x :: l4
  -> path_into_start (u, v, l) G = true
  -> d_connected_2 (u, v, l) G Z
  -> In x (find_unblocked_ancestors G u Z).
Proof.
  intros x l4 u v l G Z HG Huv Hp Hcyc H4 Hin Hconn.
  generalize dependent u. induction l as [| h t IH].
  - intros u Hp Hcyc H4 Hin Hconn. simpl in H4. simpl in Hin. rewrite Hin in H4. inversion H4. rewrite <- H0.
    apply unblocked_ancestors_have_unblocked_directed_path. right. exists []. split.
    + simpl. rewrite Hin. reflexivity.
    + split. apply reverse_path_still_acyclic with (l := []). apply Hcyc.
      intros w [Hw | Hw]. rewrite Hw. apply Huv. exfalso. apply Hw.
  - intros u Hp Hcyc H4 Hin Hconn.
    destruct (path_into_start (h, v, t) G) as [|] eqn:Hinh.
    + pose proof Hin as Hin_const. apply sources_induction_into_start in Hin. specialize IH with (u := h).
      assert (Hind: In x (find_unblocked_ancestors G h Z)).
      { apply IH.
        - apply is_path_in_graph_induction with (u := u). apply Hp.
        - apply acyclic_path_cat with (u := u). apply Hcyc.
        - rewrite <- Hin. apply H4.
        - apply Hinh.
        - apply subpath_still_d_connected with (u := u). apply Hconn. }
      apply unblocked_ancestors_transitive with (ancu' := h).
      apply single_edge_unblocked_ancestor. apply Hin_const. apply edge_out_not_in_Z with (u := u) (v := v) (t := t) (G := G). apply Hconn. left. apply Hin_const. apply Hp.
      destruct Hcyc as [_ [Hcyc _]]. intros F. apply Hcyc. left. apply F.
      apply Hind. split. apply Hp. apply HG.
    + (* u <- h -> ..., so h = x *)
      assert (Hhx: h = x).
      { unfold get_sources_in_g_path in H4. rewrite Hin in H4. simpl in H4.
        destruct t as [| h' t'].
        * simpl in H4. unfold is_confounder_bool in H4. simpl in Hin. rewrite Hin in H4. simpl in Hinh.
          assert (Hhv: is_edge (h, v) G = true).
          { simpl in Hp. rewrite Hinh in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp].
            rewrite andb_comm in Hp. rewrite orb_comm in Hp. simpl in Hp. apply Hp. }
          rewrite Hhv in H4. simpl in H4. rewrite Hinh in H4. inversion H4. reflexivity.
        * simpl in H4. unfold is_confounder_bool in H4. simpl in Hin. rewrite Hin in H4. simpl in Hinh.
          assert (Hhv: is_edge (h, h') G = true).
          { simpl in Hp. rewrite Hinh in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp].
            rewrite orb_comm in Hp. simpl in Hp. apply split_and_true in Hp. apply Hp. }
          rewrite Hhv in H4. simpl in H4.
          destruct (path_out_of_end (u, v, h :: h' :: t') G) as [[|]|] eqn:Hout.
          -- simpl in Hout. rewrite Hout in H4. inversion H4. reflexivity.
          -- simpl in Hout. rewrite Hout in H4. inversion H4. reflexivity.
          -- apply path_out_of_end_Some in Hout. exfalso. apply Hout. }
      rewrite <- Hhx. apply single_edge_unblocked_ancestor. apply Hin.
      apply edge_out_not_in_Z with (u := u) (v := v) (t := t) (G := G). apply Hconn. left. apply Hin. apply Hp.
      destruct Hcyc as [_ [Hcyc _]]. intros F. apply Hcyc. left. apply F.
Qed.

Lemma next_source_is_unblocked_ancestor_2: forall (G: graph) (u v r: node) (l: nodes) (Z: nodes),
  is_path_in_graph (u, v, l) G = true
  -> contains_cycle G = false
  -> acyclic_path_2 (u, v, l)
  -> d_connected_2 (u, v, l) G Z
  -> ~In v Z
  -> In (hd r (get_sources_in_g_path G (u, v, l))) (find_unblocked_ancestors G u Z).
Proof.
  intros G u v r l Z Hp HG Hcyc Hconn HvZ.
  generalize dependent u. induction l as [| h t IH].
  - intros u Hp Hcyc Hconn. apply unblocked_ancestors_have_unblocked_directed_path. destruct (is_edge (v, u) G) as [|] eqn:Hvu.
    + right. exists [].
      assert (H4: hd r (get_sources_in_g_path G (u, v, [])) = v). { simpl. rewrite Hvu. simpl. reflexivity. }
      unfold nodes in *. rewrite H4. split. simpl. rewrite Hvu. reflexivity.
      split. split. symmetry. apply Hcyc. easy. intros w [Hw | Hw]. rewrite Hw. apply HvZ. exfalso. apply Hw.
    + left. simpl. rewrite Hvu. simpl. reflexivity.
  - intros u Hp Hcyc Hconn. destruct (path_into_start (u, v, h :: t) G) as [|] eqn:Hin.
    + destruct (get_sources_in_g_path G (u, v, h :: t)) as [| h4 t4] eqn:H4.
      * apply sources_nonempty in H4. exfalso. apply H4. apply Hp.
      * unfold nodes in *. rewrite H4. simpl. apply next_source_is_unblocked_ancestor with (l4 := t4) (v := v) (l := h :: t). apply HG. apply HvZ. apply Hp.
        apply Hcyc. apply H4. apply Hin. apply Hconn.
    + unfold get_sources_in_g_path. left. destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
      * unfold nodes in *. rewrite Hout. rewrite Hin. simpl. reflexivity.
      * unfold nodes in *. rewrite Hout. rewrite Hin. simpl. reflexivity.
      * exfalso. apply path_out_of_end_Some in Hout. apply Hout.
Qed.


Lemma conditioned_node_between_sources: forall (x y: node) (l4: nodes) (p: path) (G: graph) (Z: nodes),
  contains_cycle G = false
  -> ~In (path_start p) Z /\ ~In (path_end p) Z
  -> is_path_in_graph p G = true
  -> acyclic_path_2 p
  -> get_sources_in_g_path G p = x :: y :: l4
  -> d_connected_2 p G Z
  -> exists (z: node), In z Z /\ In x (find_unblocked_ancestors G z Z) /\ In y (find_unblocked_ancestors G z Z).
Proof.
  intros x y l4 p G Z HG HZ HpG Hcyc HA1 Hp.
  destruct p as [[u v] l]. simpl in HZ.
  generalize dependent u. generalize dependent x. induction l as [| h t IH].
  - intros x u HZ HpG Hcyc HA1 Hp. simpl in HA1. destruct (is_edge (v, u) G) as [|] eqn:Hvu.
    + discriminate HA1.
    + discriminate HA1.
  - intros x u HZ HpG Hcyc HA1 Hp. destruct t as [| h' t'].
    + simpl in HA1. destruct (is_edge (v, h) G) as [|] eqn:Hvh.
      * destruct (is_edge (h, u) G) as [|] eqn:Hhu.
        -- destruct (is_confounder_bool u v h G) as [|] eqn:Hcon.
           ++ (* u <- h <- v, but confounder => u <- h -> v, so cycle *)
              apply acyclic_no_two_cycle in Hvh. unfold is_confounder_bool in Hcon. rewrite Hvh in Hcon. rewrite andb_comm in Hcon. discriminate Hcon.
              apply HG.
           ++ discriminate HA1.
        -- destruct (is_confounder_bool u v h G) as [|] eqn:Hcon.
           ++ unfold is_confounder_bool in Hcon. rewrite Hhu in Hcon. discriminate Hcon.
           ++ (* u -> h <- v *) inversion HA1. rewrite <- H0 in *. rewrite <- H1 in *.
              assert (Huh: is_edge (u, h) G = true).
              { simpl in HpG. rewrite Hhu in HpG. rewrite orb_comm in HpG. simpl in HpG. destruct G as [V E]. apply split_and_true in HpG. apply HpG. }
              apply colliders_have_unblocked_path_to_descendant with (c := h) in Hp.
              ** destruct Hp as [Hp | Hp].
                 --- exists h. split. apply Hp. split.
                     +++ apply single_edge_unblocked_ancestor_path with (v := v) (t := []). apply Huh. apply HZ. apply Hcyc.
                     +++ apply single_edge_unblocked_ancestor_path with (v := u) (t := []). apply Hvh. apply HZ. apply reverse_path_still_acyclic with (l := [h]). apply Hcyc.
                 --- destruct Hp as [HhZ [z [dp Hp]]]. exists z. split. apply Hp. split.
                     +++ apply unblocked_ancestors_transitive with (ancu' := h).
                         { apply unblocked_ancestors_have_unblocked_directed_path. right. exists dp. split. apply Hp. split. apply Hp.
                           intros w [Hw | Hw]. rewrite Hw. apply HhZ. intros HwZ. destruct Hp as [_ [_ [Hp _]]]. apply no_overlap_non_member with (x := w) in Hp.
                           apply Hp. apply Hw. apply HwZ. }
                         { apply single_edge_unblocked_ancestor_path with (v := v) (t := []). apply Huh. apply HZ. apply Hcyc. }
                     +++ apply unblocked_ancestors_transitive with (ancu' := h).
                         { apply unblocked_ancestors_have_unblocked_directed_path. right. exists dp. split. apply Hp. split. apply Hp.
                           intros w [Hw | Hw]. rewrite Hw. apply HhZ. intros HwZ. destruct Hp as [_ [_ [Hp _]]]. apply no_overlap_non_member with (x := w) in Hp.
                           apply Hp. apply Hw. apply HwZ. }
                         { apply single_edge_unblocked_ancestor_path with (v := u) (t := []). apply Hvh. apply HZ. apply reverse_path_still_acyclic with (l := [h]). apply Hcyc. }
              ** simpl. unfold is_collider_bool. rewrite Hvh. rewrite Huh. simpl. left. reflexivity.
      * destruct (is_edge (h, u) G) as [|] eqn:Hhu. destruct (is_confounder_bool u v h G) as [|] eqn:Hcon. discriminate HA1. discriminate HA1.
        destruct (is_confounder_bool u v h G) as [|] eqn:Hcon.
        -- (* u <- h -> v, u -> h *)
           unfold is_confounder_bool in Hcon. apply split_and_true in Hcon. destruct Hcon as [Hcon]. rewrite Hcon in Hhu. discriminate Hhu.
        -- discriminate HA1.
    + pose proof HA1 as HA1_const. unfold get_sources_in_g_path in HA1.
      destruct (path_into_start (u, v, h :: h' :: t') G) as [|] eqn:Hin.
      * unfold nodes in *. unfold node in *. rewrite Hin in HA1. rewrite path_out_of_end_same in HA1. simpl in HA1.
        destruct (is_confounder_bool u h' h G) as [|] eqn:Hcon.
        -- (* Hin: u<-h, Hcon: u<-h *) simpl in HA1. (* h = x *)
           specialize IH with (u := h). apply IH.
           ++ (* h not in Z *) split. apply edge_out_not_in_Z with (u := u) (v := v) (t := h' :: t') (G := G). apply Hp. left. apply Hin. apply HpG.
              apply HZ.
           ++ apply is_path_in_graph_induction with (u := u). apply HpG.
           ++ apply acyclic_path_cat with (u := u). apply Hcyc.
           ++ simpl. unfold is_confounder_bool in Hcon. apply split_and_true in Hcon. destruct Hcon as [_ Hcon]. apply acyclic_no_two_cycle in Hcon.
              rewrite Hcon. rewrite Hcon in HA1. apply HA1. apply HG.
           ++ apply subpath_still_d_connected with (u := u). apply Hp.
        -- unfold is_confounder_bool in Hcon. simpl in Hin. rewrite Hin in Hcon. simpl in Hcon.
           assert (Hhh': is_edge (h', h) G = true). { simpl in HpG. rewrite Hcon in HpG. simpl in HpG. destruct G as [V E]. rewrite andb_comm in HpG.
            apply split_and_true in HpG. destruct HpG as [HpG _]. apply split_and_true in HpG. apply HpG. }
           specialize IH with (u := h). apply IH.
           ++ split.
              apply edge_out_not_in_Z with (u := u) (v := v) (t := h' :: t') (G := G). apply Hp. left. apply Hin. apply HpG.
              apply HZ.
           ++ apply is_path_in_graph_induction with (u := u). apply HpG.
           ++ apply acyclic_path_cat with (u := u). apply Hcyc.
           ++ simpl. unfold nodes in *. unfold node in *. rewrite Hhh'. rewrite Hhh' in HA1. apply HA1.
           ++ apply subpath_still_d_connected with (u := u). apply Hp.
      * unfold nodes in *. unfold node in *. rewrite Hin in HA1. rewrite path_out_of_end_same in HA1. simpl in HA1.
        destruct (is_confounder_bool u h' h G) as [|] eqn:Hcon.
        -- simpl in Hin. (* Hin: u->h. Hcon: u<-h *)
           unfold is_confounder_bool in Hcon. apply split_and_true in Hcon. destruct Hcon as [Hcon _]. rewrite Hin in Hcon. discriminate Hcon.
        -- (* u = x *)
           assert (Hux: u = x).
           { destruct (path_out_of_end (h, v, h' :: t') G) as [[|]|] eqn:Hout.
             - simpl in Hout. rewrite Hout in HA1. inversion HA1. reflexivity.
             - simpl in Hout. rewrite Hout in HA1. inversion HA1. reflexivity.
             - apply path_out_of_end_Some in Hout. exfalso. apply Hout. }
           assert (Huh: is_edge (u, h) G = true).
           { simpl in HpG. simpl in Hin. rewrite Hin in HpG. rewrite orb_comm in HpG. simpl in HpG. destruct G as [V E]. apply split_and_true in HpG. apply HpG. }
           destruct (is_edge (h, h') G) as [|] eqn:Hhh'.
           ++ (* u -> h -> h' *)
              assert (HA1': get_sources_in_g_path G (h, v, h' :: t') = h :: y :: l4).
              { pose proof sources_induction_out_of_start_out_of_h.
                assert (Hdir: path_into_start (u, v, h :: h' :: t') G = false /\ path_out_of_h G u v h (h' :: t') = true).
                { split. apply Hin. simpl. apply Hhh'. }
                apply H in Hdir.
                - destruct Hdir as [A [HuA HhA]]. unfold nodes in *. unfold node in *. rewrite HA1_const in HuA. inversion HuA.
                  rewrite <- H2 in HhA. apply HhA.
                - split. apply HpG. apply HG. }

              specialize IH with (u := h) (x := h). apply IH in HA1'.
              ** destruct HA1' as [z [HzZ [HhZ HyZ]]]. exists z. split. apply HzZ. rewrite and_comm. split. apply HyZ.
                 apply unblocked_ancestors_transitive with (ancu' := h). apply HhZ.
                 rewrite <- Hux.
                 apply single_edge_unblocked_ancestor_path with (v := v) (t := h' :: t'). simpl in Hin. apply Huh. apply HZ. apply Hcyc.
              ** split.
                 apply edge_out_not_in_Z with (u := u) (v := v) (t := h' :: t') (G := G). apply Hp. right. simpl. apply Hhh'. apply HpG.
                 apply HZ.
              ** apply is_path_in_graph_induction with (u := u). apply HpG.
              ** apply acyclic_path_cat with (u := u). apply Hcyc.
              ** apply subpath_still_d_connected with (u := u). apply Hp.
           ++ (* u -> h <- h' *)
              assert (Hhh'': is_edge (h', h) G = true).
              { simpl in HpG. unfold nodes in *. unfold node in *. rewrite Hhh' in HpG. simpl in HpG. destruct G as [V E]. rewrite andb_comm in HpG.
                apply split_and_true in HpG. destruct HpG as [HpG _]. apply split_and_true in HpG. apply HpG. }
              pose proof Hp as Hconn. apply colliders_have_unblocked_path_to_descendant with (c := h) in Hp.
              ** assert (Hhy: In y (find_unblocked_ancestors G h Z)).
                 { apply next_source_is_unblocked_ancestor with (l4 := l4) (v := v) (l := h' :: t'). apply HG. apply HZ.
                   *** apply is_path_in_graph_induction with (u := u). apply HpG.
                   *** apply acyclic_path_cat with (u := u). apply Hcyc.
                   *** assert (HA1': get_sources_in_g_path G (u, v, h :: h' :: t') = u :: get_sources_in_g_path G (h, v, h' :: t')).
                       { apply sources_induction_out_of_start_into_h. split. apply HpG. apply HG. split. apply Hin. simpl. apply Hhh'. }
                       rewrite HA1_const in HA1'. symmetry in HA1'. unfold nodes in *. unfold node in *. inversion HA1'. simpl. reflexivity.
                   *** simpl. apply Hhh''.
                   *** apply subpath_still_d_connected with (u := u). apply Hconn. }

                 destruct Hp as [Hp | Hp].
                 --- exists h. split. apply Hp. split.
                     +++ rewrite <- Hux. apply single_edge_unblocked_ancestor_path with (v := v) (t := h' :: t'). simpl in Hin. apply Huh. apply HZ.
                         apply Hcyc.
                     +++ apply Hhy.
                 --- destruct Hp as [HhZ [z [dp Hp]]]. exists z. split. apply Hp. split.
                     +++ apply unblocked_ancestors_transitive with (ancu' := h).
                         { apply unblocked_ancestors_have_unblocked_directed_path. right. exists dp. split. apply Hp. split. apply Hp.
                           intros w [Hw | Hw]. rewrite Hw. apply HhZ. intros HwZ. destruct Hp as [_ [_ [Hp _]]]. apply no_overlap_non_member with (x := w) in Hp.
                           apply Hp. apply Hw. apply HwZ. }
                         { rewrite <- Hux. apply single_edge_unblocked_ancestor_path with (v := v) (t := h' :: t'). simpl in Hin. apply Huh. apply HZ.
                           apply Hcyc. }
                     +++ apply unblocked_ancestors_transitive with (ancu' := h).
                         { apply unblocked_ancestors_have_unblocked_directed_path. right. exists dp. split. apply Hp. split. apply Hp.
                           intros w [Hw | Hw]. rewrite Hw. apply HhZ. intros HwZ. destruct Hp as [_ [_ [Hp _]]]. apply no_overlap_non_member with (x := w) in Hp.
                           apply Hp. apply Hw. apply HwZ. }
                         { apply Hhy. }
              ** simpl. unfold is_collider_bool. unfold nodes in *. unfold node in *. rewrite Huh.
                 rewrite Hhh''. simpl. left. reflexivity.
Qed.

Lemma sources_count_acyclic: forall (u v c: node) (l: nodes) (G: graph),
  In c (get_sources_in_g_path G (u, v, l))
  -> acyclic_path_2 (u, v, l)
  -> is_path_in_graph (u, v, l) G = true
  -> count c (get_sources_in_g_path G (u, v, l)) = 1.
Proof.
  intros u v c l G Hc' Hcyc Hp.
  unfold get_sources_in_g_path in *.
  assert (H: In c (find_confounders_in_path (u, v, l) G ++ [v]) -> count c (find_confounders_in_path (u, v, l) G ++ [v]) = 1).
  { intros Hc. apply membership_append_or in Hc. destruct Hc as [Hc | Hc].
    * apply confounder_count_acyclic in Hc as Hcount. 2: { apply Hcyc. } 2: { apply Hp. }
      rewrite count_app. rewrite Hcount. simpl. f_equal. destruct (v =? c) as [|] eqn:Hvc.
      -- apply intermediate_node_in_path with (x := c) in Hp. assert (Hcmem: In c l). { apply Hp. right. left. apply Hc. }
         apply eqb_eq in Hvc. rewrite <- Hvc in Hcmem. destruct Hcyc as [_ [_ [Hcyc _]]]. exfalso. apply Hcyc. apply Hcmem.
      -- reflexivity.
    * destruct (member c (find_confounders_in_path (u, v, l) G)) as [|] eqn:Hcmem.
      -- exfalso. destruct Hcyc as [_ [_ [Hcyc _]]]. apply Hcyc. apply intermediate_node_in_path with (x := c) in Hp. destruct Hc as [Hc | Hc].
         rewrite Hc. apply Hp. right. left. apply member_In_equiv. apply Hcmem. exfalso. apply Hc.
      -- rewrite count_app. apply not_member_count_0 in Hcmem. rewrite Hcmem. destruct Hc as [Hc | Hc]. rewrite Hc. simpl. rewrite eqb_refl. reflexivity. exfalso. apply Hc. }

  destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply H. apply Hc'.
    + destruct (u =? c) as [|] eqn:Huc.
      * simpl. rewrite Huc. f_equal. rewrite count_app. simpl.
        destruct (member c (find_confounders_in_path (u, v, l) G)) as [|] eqn:Hcmem.
        -- exfalso. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. apply intermediate_node_in_path with (x := c) in Hp. apply eqb_eq in Huc.
           rewrite Huc. apply Hp. right. left. apply member_In_equiv. apply Hcmem.
        -- apply not_member_count_0 in Hcmem. simpl in Hcmem. apply eqb_eq in Huc. rewrite Huc in *. rewrite Hcmem. destruct (v =? c) as [|] eqn:Hvc.
           ++ exfalso. destruct Hcyc as [Hcyc _]. apply Hcyc. apply eqb_eq. rewrite eqb_sym. apply Hvc.
           ++ reflexivity.
      * destruct Hc' as [Hc' | Hc']. apply eqb_eq in Hc'. rewrite Hc' in Huc. discriminate Huc. simpl. rewrite Huc.
        apply H. apply Hc'.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply confounder_count_acyclic in Hc'. apply Hc'. apply Hcyc. apply Hp.
    + destruct (u =? c) as [|] eqn:Huc.
      * simpl. rewrite Huc. f_equal.
        destruct (member c (find_confounders_in_path (u, v, l) G)) as [|] eqn:Hcmem.
        -- exfalso. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. apply intermediate_node_in_path with (x := c) in Hp. apply eqb_eq in Huc.
           rewrite Huc. apply Hp. right. left. apply member_In_equiv. apply Hcmem.
        -- apply not_member_count_0 in Hcmem. simpl in Hcmem. apply eqb_eq in Huc. rewrite Huc in *. rewrite Hcmem. reflexivity.
      * destruct Hc' as [Hc' | Hc']. apply eqb_eq in Hc'. rewrite Hc' in Huc. discriminate Huc. simpl. rewrite Huc.
        apply confounder_count_acyclic in Hc'. apply Hc'. apply Hcyc. apply Hp.
  - exfalso. apply Hc'.
Qed.
