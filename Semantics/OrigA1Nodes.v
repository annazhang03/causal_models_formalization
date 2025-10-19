From CausalDiagrams Require Import CausalPaths.
From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import Assignments.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.

(* mediators, u if u is a child, and v if v is a child *)
Definition get_A1_binded_nodes_in_g_path (G: graph) (p: path): nodes :=
  match p with
  | (u, v, l) =>
    match path_out_of_end p G with
    | Some b => if b then (if path_into_start p G then u :: (find_mediators_in_path p G) else find_mediators_in_path p G)
                     else (if path_into_start p G then u :: (find_mediators_in_path p G) ++ [v] else (find_mediators_in_path p G) ++ [v])
    | None => [] (* since p has at least two nodes, will not reach this *)
    end
  end.

Lemma A1_nodes_in_graph: forall (G: graph) (u v x: node) (l: nodes),
  G_well_formed G = true
  -> is_path_in_graph (u, v, l) G = true
  -> In x (get_A1_binded_nodes_in_g_path G (u, v, l))
  -> node_in_graph x G = true.
Proof.
  intros G u v x l. intros HG Hp Hx.
  unfold get_A1_binded_nodes_in_g_path in Hx.
  destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + destruct Hx as [Hx | Hx].
      * unfold path_into_start in Hin. destruct l as [| h t].
        -- apply is_edge_then_node_in_graph with (v := v). right. rewrite <- Hx. apply Hin.
        -- apply is_edge_then_node_in_graph with (v := h). right. rewrite <- Hx. apply Hin.
      * apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [[Hx _] | [Hx _]]]]].
        apply is_edge_then_node_in_graph with (v := y). right. apply Hx. apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
    + apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [[Hx _] | [Hx _ ]]]]].
      apply is_edge_then_node_in_graph with (v := y). right. apply Hx. apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + destruct Hx as [Hx | Hx].
      * unfold path_into_start in Hin. destruct l as [| h t].
        -- apply is_edge_then_node_in_graph with (v := v). right. rewrite <- Hx. apply Hin.
        -- apply is_edge_then_node_in_graph with (v := h). right. rewrite <- Hx. apply Hin.
      * apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [[Hx _] | [Hx _]]]]].
           apply is_edge_then_node_in_graph with (v := y). right. apply Hx. apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
        -- destruct Hx as [Hx | F].
           ++ apply nodes_in_graph_in_V with (p := (u, v, l)). split.
              ** unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
              ** apply Hp.
           ++ exfalso. apply F.
    + apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [[Hx _] | [Hx _]]]]].
           apply is_edge_then_node_in_graph with (v := y). right. apply Hx. apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
        -- destruct Hx as [Hx | F].
           ++ apply nodes_in_graph_in_V with (p := (u, v, l)). split.
              ** unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
              ** apply Hp.
           ++ exfalso. apply F.
  - exfalso. apply Hx.
Qed.

Lemma A1_nodes_in_path: forall (G: graph) (u v x: node) (l: nodes),
  In x (get_A1_binded_nodes_in_g_path G (u, v, l))
  -> node_in_path x (u, v, l) = true.
Proof.
  intros G u v x l. intros Hx.
  unfold get_A1_binded_nodes_in_g_path in Hx.
  destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + destruct Hx as [Hx | Hx].
      * unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. reflexivity.
      * apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
    + apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + destruct Hx as [Hx | Hx].
      * unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. reflexivity.
      * apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
        -- unfold node_in_path. destruct Hx as [Hx | F]. rewrite Hx. rewrite eqb_refl. simpl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
    + apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
        -- unfold node_in_path. destruct Hx as [Hx | F]. rewrite Hx. rewrite eqb_refl. simpl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
  - exfalso. apply Hx.
Qed.

Lemma A1_induction_into_start: forall (G: graph) (u h v: node) (t: nodes),
  is_path_in_graph (u, v, h :: t) G = true /\ contains_cycle G = false
  -> path_into_start (u, v, h :: t) G = true -> get_A1_binded_nodes_in_g_path G (u, v, h :: t) = u :: (get_A1_binded_nodes_in_g_path G (h, v, t)).
Proof.
  intros G u h v t [Hp Hcyc] Hin.
  unfold get_A1_binded_nodes_in_g_path.
  destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    destruct (path_into_start (h, v, t) G) as [|] eqn:Hinh.
    + simpl. destruct t as [| h' t']. simpl.
      * unfold is_mediator_bool. simpl in Hin. rewrite Hin. simpl in Hinh. rewrite Hinh. rewrite orb_comm. simpl. reflexivity.
      * simpl. unfold is_mediator_bool. simpl in Hinh. simpl in Hin. rewrite Hin. rewrite Hinh. rewrite orb_comm. simpl. reflexivity.
    + simpl. destruct t as [| h' t']. simpl.
      * unfold is_mediator_bool. simpl in Hinh. simpl in Hin. apply acyclic_no_two_cycle in Hin. rewrite Hin. simpl. rewrite Hinh. simpl. reflexivity. apply Hcyc.
      * simpl. unfold is_mediator_bool. simpl in Hinh. simpl in Hin. apply acyclic_no_two_cycle in Hin. rewrite Hin. simpl. rewrite Hinh. simpl. reflexivity. apply Hcyc.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    destruct (path_into_start (h, v, t) G) as [|] eqn:Hinh.
    + simpl. destruct t as [| h' t']. simpl.
      * unfold is_mediator_bool. simpl in Hin. simpl in Hinh. rewrite Hinh. rewrite Hin. rewrite orb_comm. simpl. reflexivity.
      * simpl. unfold is_mediator_bool. simpl in Hinh. simpl in Hin. rewrite Hinh. rewrite Hin. rewrite orb_comm. simpl. reflexivity.
    + simpl. destruct t as [| h' t']. simpl.
      * unfold is_mediator_bool. simpl in Hinh. simpl in Hin. apply acyclic_no_two_cycle in Hin. rewrite Hin. simpl. rewrite Hinh. simpl. reflexivity. apply Hcyc.
      * simpl. unfold is_mediator_bool. simpl in Hinh. simpl in Hin. apply acyclic_no_two_cycle in Hin. rewrite Hin. simpl. rewrite Hinh. simpl. reflexivity. apply Hcyc.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma A1_induction_add_collider: forall (G: graph) (u h h' v: node) (t': nodes),
  is_path_in_graph (u, v, h :: h' :: t') G = true /\ contains_cycle G = false
  -> path_into_start (u, v, h :: h' :: t') G = false /\ path_out_of_h G u v h (h' :: t') = false
  -> get_A1_binded_nodes_in_g_path G (u, v, h :: h' :: t') = get_A1_binded_nodes_in_g_path G (h', v, t').
Proof.
  (* u -> h <- h' ... *)
  intros G u h h' v t' [Hp Hcyc] [Hin Houth].
  unfold get_A1_binded_nodes_in_g_path.

  destruct (path_out_of_end (u, v, h :: h' :: t') G) as [[|]|] eqn:Hout.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := h). rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Houth.
    simpl. unfold is_mediator_bool. simpl in Hin. rewrite Hin. simpl in Houth. rewrite Houth. rewrite andb_comm. simpl. rewrite andb_comm. simpl.
    assert (Houth': is_edge (h', h) G = true).
    { simpl in Hp.
      destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. rewrite Houth in Hp. apply split_and_true in Hp. simpl. simpl in Hp. destruct Hp as [Hp _]. rewrite Hp. reflexivity. }

    destruct (path_into_start (h', v, t') G) as [|] eqn:Hinh.
    + destruct t' as [| h'' t''].
      * simpl. simpl in Hout. inversion Hout. rewrite H0. rewrite Houth'. simpl. reflexivity.
      * simpl. simpl in Hinh. rewrite Hinh. rewrite Houth'. simpl. reflexivity.

    + destruct t' as [| h'' t''].
      * simpl. simpl in Hout. inversion Hout. rewrite H0. rewrite Houth'. simpl. reflexivity.
      * simpl. simpl in Hinh. rewrite Hinh. rewrite Houth'. simpl. reflexivity.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := h). rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Houth.
    simpl. unfold is_mediator_bool. simpl in Hin. rewrite Hin. simpl in Houth. rewrite Houth. rewrite andb_comm. simpl. rewrite andb_comm. simpl.
    assert (Houth': is_edge (h', h) G = true).
    { simpl in Hp.
      destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. rewrite Houth in Hp. apply split_and_true in Hp. simpl. simpl in Hp. destruct Hp as [Hp _]. rewrite Hp. reflexivity. }

    destruct (path_into_start (h', v, t') G) as [|] eqn:Hinh.
    + destruct t' as [| h'' t''].
      * simpl. simpl in Hout. inversion Hout. rewrite H0. rewrite Houth'. simpl. reflexivity.
      * simpl. simpl in Hinh. rewrite Hinh. rewrite Houth'. simpl. reflexivity.

    + destruct t' as [| h'' t''].
      * simpl. simpl in Hout. inversion Hout. rewrite H0. rewrite Houth'. simpl. reflexivity.
      * simpl. simpl in Hinh. rewrite Hinh. rewrite Houth'. simpl. reflexivity.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma A1_induction_out_of_start_out_of_h: forall (G: graph) (u h v: node) (t: nodes),
  is_path_in_graph (u, v, h :: t) G = true /\ contains_cycle G = false
  -> path_into_start (u, v, h :: t) G = false /\ path_out_of_h G u v h t = true -> get_A1_binded_nodes_in_g_path G (u, v, h :: t) = h :: (get_A1_binded_nodes_in_g_path G (h, v, t)).
Proof.
  intros G u h v t [Hp Hcyc] [Hin Houth].
  unfold get_A1_binded_nodes_in_g_path.
  destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction in Houth.
    + rewrite Houth. simpl. destruct t as [| h' t'].
      * unfold is_mediator_bool. simpl in Hout. simpl in Houth. inversion Hout. rewrite H0 in Houth. discriminate Houth.
      * assert (Hmed: is_mediator_bool u h' h G = true).
        { unfold is_mediator_bool. simpl in Hin. simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [Hp Hp'].
          rewrite Hin in Hp. rewrite orb_comm in Hp. simpl in Hp. simpl. rewrite Hp. simpl.
          apply split_and_true in Hp'. destruct Hp' as [Hp' _]. simpl in Houth. simpl in Hp'. rewrite Houth in Hp'. rewrite orb_comm in Hp'. simpl in Hp'. rewrite Hp'. reflexivity. }
        simpl. rewrite Hmed. reflexivity.
    + split.
      * simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. apply Hp.
      * apply Hcyc.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction in Houth.
    + rewrite Houth. destruct t as [| h' t'].
      * simpl. assert (Hmed: is_mediator_bool u v h G = true).
        { unfold is_mediator_bool. simpl in Hin. simpl in Houth. simpl in Hp. rewrite Hin in Hp. rewrite Houth in Hp. rewrite orb_comm in Hp. simpl in Hp. rewrite orb_comm in Hp. simpl in Hp.
          destruct G as [V E]. rewrite andb_assoc in Hp. apply split_and_true in Hp. apply Hp. }
        rewrite Hmed. reflexivity.
      * assert (Hmed: is_mediator_bool u h' h G = true).
        { unfold is_mediator_bool. simpl in Hin. simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [Hp Hp'].
          rewrite Hin in Hp. rewrite orb_comm in Hp. simpl in Hp. simpl. rewrite Hp. simpl.
          apply split_and_true in Hp'. destruct Hp' as [Hp' _]. simpl in Houth. simpl in Hp'. rewrite Houth in Hp'. rewrite orb_comm in Hp'. simpl in Hp'. rewrite Hp'. reflexivity. }
        simpl. rewrite Hmed. reflexivity.
    + split.
      * apply is_path_in_graph_induction with (u := u). apply Hp.
      * apply Hcyc.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma A1_induction_case_rev: forall (G: graph) (u v h: node) (t: nodes),
  path_out_of_end (u, v, rev (h :: t)) G = Some false
  -> contains_cycle G = false
  -> is_path_in_graph (u, v, rev (h :: t)) G = true
  -> get_A1_binded_nodes_in_g_path G (u, h, rev t) ++ [v] = get_A1_binded_nodes_in_g_path G (u, v, rev (h :: t)).
Proof.
  intros G u v h t H Hcyc Hpath.
  unfold get_A1_binded_nodes_in_g_path. rewrite H. 
  destruct (path_out_of_end (u, h, rev t) G) as [[|]|] eqn:Houth.
  + assert (Hmed: find_mediators_in_path (u, h, rev t) G = find_mediators_in_path (u, v, rev (h :: t)) G).
    { simpl in H. simpl. simpl in Hpath. generalize dependent u. induction (rev t) as [| h' t' IH].
      - intros u H Hpath Houth. simpl. unfold is_mediator_bool. simpl in Houth. inversion Houth.
        assert (Huh: is_edge (u, h) G = false). { apply acyclic_no_two_cycle. apply Hcyc. apply H1. } rewrite Huh. simpl. simpl in H. inversion H. rewrite H2. reflexivity.
      - intros u H Hpath Houth. simpl. destruct t' as [| h'' t''].
        + simpl. destruct (is_mediator_bool u h h' G) as [|] eqn:Huhh'.
          * unfold is_mediator_bool. simpl in Houth. inversion Houth.
            assert (Huh: is_edge (h', h) G = false). { apply acyclic_no_two_cycle. apply Hcyc. apply H1. } rewrite Huh. simpl. rewrite H1. simpl.
            simpl in H. inversion H. rewrite H2. reflexivity.
          * simpl in H. unfold is_mediator_bool. unfold is_mediator_bool in Huhh'. simpl in Houth. inversion Houth.
            assert (Huh: is_edge (h', h) G = false). { apply acyclic_no_two_cycle. apply Hcyc. apply H1. } rewrite Huh. simpl. rewrite H1. simpl.
            inversion H. rewrite H2. simpl. reflexivity.
        + simpl. destruct (is_mediator_bool u h'' h' G) as [|] eqn:Huhh'.
          * f_equal. simpl in IH. simpl. f_equal. apply IH.
            -- simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. apply Houth.
          * simpl. f_equal. destruct (is_mediator_bool h'' u h' G) as [|].
            { simpl. f_equal. apply IH.
            -- simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. apply Houth. }
            { apply IH.
            -- simpl in H. simpl. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. simpl. apply Houth. } }
    rewrite Hmed. destruct (path_into_start (u, v, rev (h :: t)) G) as [|] eqn:Hin.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
  + assert (Hmed: find_mediators_in_path (u, h, rev t) G ++ [h] = find_mediators_in_path (u, v, rev (h :: t)) G).
    { simpl in H. simpl. simpl in Hpath. generalize dependent u. induction (rev t) as [| h' t' IH].
      - intros u H Hpath Houth. simpl. unfold is_mediator_bool. simpl in Hpath. destruct G as [V E]. simpl in Houth. inversion Houth.
        simpl in Hpath. rewrite H1 in Hpath. simpl in H. inversion H. rewrite H2 in Hpath. simpl. apply split_and_true in Hpath. destruct Hpath as [Huh Hhv].
        rewrite orb_comm in Huh. simpl in Huh. rewrite Huh. rewrite andb_comm in Hhv. rewrite orb_comm in Hhv. simpl in Hhv. rewrite Hhv. simpl. reflexivity.
      - intros u H Hpath Houth. simpl. destruct t' as [| h'' t''].
        + simpl. destruct (is_mediator_bool u h h' G) as [|] eqn:Huhh'.
          * unfold is_mediator_bool. simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [Hhh Hhv].
             simpl in Houth. inversion Houth. simpl in Hhh. rewrite H1 in Hhh. rewrite orb_comm in Hhh. simpl in Hhh. simpl. rewrite Hhh.
             simpl in H. inversion H. simpl in Hhv. rewrite H2 in Hhv. rewrite andb_comm in Hhv. rewrite orb_comm in Hhv. simpl in Hhv. rewrite Hhv. simpl. reflexivity.
          * simpl. unfold is_mediator_bool. simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [Hhh Hhv].
             simpl in Houth. inversion Houth. simpl in Hhh. rewrite H1 in Hhh. rewrite orb_comm in Hhh. simpl in Hhh. simpl. rewrite Hhh.
             simpl in H. inversion H. simpl in Hhv. rewrite H2 in Hhv. rewrite andb_comm in Hhv. rewrite orb_comm in Hhv. simpl in Hhv. rewrite Hhv. simpl. rewrite H1. simpl. reflexivity.
        + simpl. destruct (is_mediator_bool u h'' h' G || is_mediator_bool h'' u h' G) as [|] eqn:Huhh'.
          * simpl. f_equal. apply IH.
            -- simpl. simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. simpl. apply Houth.
          * simpl. apply IH.
            -- simpl. simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. simpl. apply Houth. }
    rewrite Hmed. destruct (path_into_start (u, v, rev (h :: t)) G) as [|] eqn:Hin.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
  + apply path_out_of_end_Some in Houth. exfalso. apply Houth.
Qed.

Definition A1_nodes_binded_to_parent_in_path (G: graph) (p: path) (A1: assignments nat): Prop :=
  forall (m: node) (i: nat), In (m, i) A1
  -> exists (a: node), nth_error (find_parents m G) i = Some a
     /\ (sublist [a; m] ((path_start p) :: (path_int p) ++ [path_end p]) = true \/ sublist [m; a] ((path_start p) :: (path_int p) ++ [path_end p]) = true).

Lemma mediators_in_A1: forall (G: graph) (a: node) (u v: node) (l: nodes),
  In a (find_mediators_in_path (u, v, l) G)
  -> In a (get_A1_binded_nodes_in_g_path G (u, v, l)).
Proof.
  intros G a u v l H.
  unfold get_A1_binded_nodes_in_g_path. destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + right. apply H.
    + apply H.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + right. apply membership_append. apply H.
    + apply membership_append. apply H.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma A1_mediators_or_endpoints: forall (G: graph) (a: node) (u v: node) (l: nodes),
  In a (get_A1_binded_nodes_in_g_path G (u, v, l))
  -> a = u \/ In a (find_mediators_in_path (u, v, l) G) \/ a = v.
Proof.
  intros G a u v l H.
  unfold get_A1_binded_nodes_in_g_path in H. destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + destruct H as [H | H]. left. symmetry. apply H. right. left. apply H.
    + right. left. apply H.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + destruct H as [H | H]. left. symmetry. apply H. apply membership_append_or in H.
      destruct H as [H | H]. right. left. apply H. destruct H as [H | H]. right. right. symmetry. apply H.
      exfalso. apply H.
    + apply membership_append_or in H.
      destruct H as [H | H]. right. left. apply H. destruct H as [H | H]. right. right. symmetry. apply H.
      exfalso. apply H.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.