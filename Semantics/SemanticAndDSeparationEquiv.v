From Semantics Require Import FunctionRepresentation.
From Semantics Require Import FindValue.
From Semantics Require Import NodeCategorization.
From Semantics Require Import ColliderDescendants.
From Semantics Require Import DescendantPathsDisjoint.
From Semantics Require Import SemanticSeparationDef.
From Semantics Require Import EquateValues.
From Semantics Require Import ChangeOriginatesFromUnbAnc.
From CausalDiagrams Require Import Assignments.
From CausalDiagrams Require Import DSeparation.
From CausalDiagrams Require Import UnblockedAncestors.
From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import CausalPaths.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From DAGs Require Import Basics.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.


Import ListNotations.
From Utils Require Import EqType.


(* show that using the g from generic_graph_and_type_properties_hold to equate values along the path, the
   semantically_separated proposition cannot hold *)
Lemma path_d_connected_then_not_semantically_separated {X : Type} `{EqType X}: forall (G: graph) (u v: node) (p: path),
  generic_graph_and_type_properties_hold X G /\ In p (find_all_paths_from_start_to_end u v G) ->
  forall (Z: nodes), subset Z (nodes_in_graph G) = true /\ each_node_appears_once Z /\ member u Z = false /\ member v Z = false
  -> d_connected_2 p G Z -> ~(semantically_separated X G u v Z).
Proof.
  intros G u v p [HG Hp]. intros Z [HZ [HZnode [HuZ HvZ]]] Hconn.
  intros H_cond_ind. unfold semantically_separated in H_cond_ind.
  pose proof HG as Hxy. unfold generic_graph_and_type_properties_hold in Hxy. destruct Hxy as [Hxy _]. destruct Hxy as [x [y Hxy]].
  apply paths_start_to_end_correct in Hp.

  assert (Hpath: exists (l: nodes), p = (u, v, l)).
  { destruct p as [[u' v'] l]. destruct Hp as [_ [Hp _]].
    apply path_start_end_equal in Hp. destruct Hp as [Huu' Hvv']. exists l. rewrite Huu'. rewrite Hvv'. reflexivity. }
  destruct Hpath as [l' Hpath].

  pose proof exists_d_connected_path_with_collider_descendants_disjoint as Hdisj. specialize Hdisj with (G := G) (Z := Z) (l := l') (u := u) (v := v).
  rewrite Hpath in *. pose proof Hconn as HD. apply Hdisj in HD.
  2: { apply HG. } 2: { apply Hp. } 2: { apply Hp. }
  clear Hdisj. destruct HD as [l Huvl]. pose proof Huvl as HD. destruct HD as [_ [_ [_ [_ HD]]]]. destruct HD as [D HD].

  pose proof path_d_connected_then_can_equate_values'' as Heq'. specialize Heq' with (G := G) (u := u) (v := v) (p := (u, v, l)) (Z := Z) (D := D).

  assert (Heq: generic_graph_and_type_properties_hold X G /\ In (u, v, l) (find_all_paths_from_start_to_end u v G)).
  { split. apply HG. apply paths_start_to_end_correct. split. apply Huvl. split. apply path_start_end_refl. apply Huvl. }

  remember (get_assignment_for Z x) as AZ.

  apply Heq' with (AZ := AZ) in Heq. clear Heq'.
  2: { split. apply member_In_equiv_F. apply HuZ. apply member_In_equiv_F. apply HvZ. }
  2: { rewrite HeqAZ. apply nodes_map_to_exact_assignment. }
  2: { simpl. apply HD. }
  2: { apply Huvl. }

  destruct Heq as [A1 [A2 [A3 Heq]]].
  rewrite <- and_assoc in Heq. rewrite <- and_assoc in Heq. destruct Heq as [HA1 Heq]. rewrite <- and_assoc in Heq. rewrite <- and_assoc in Heq. destruct Heq as [HA2 Heq]. destruct Heq as [HA3 Heq].
  (* Hcond: for all AZ, changing f(u) from a to b via valid sequence does NOT change the value of f(v) *)
  (* Heq: there is some sequence that changes the value of f(v) to x *)

  remember ([]) as empty. rewrite Heqempty in *.
  remember (get_constant_nodefun_assignments empty) as A5. (* unused, could be empty *)
  remember (get_assignment_for (get_A4_binded_nodes_in_g_path G (u, v, l)) x) as A4. (* value doesn't matter *)
  remember (f_constant X x) as default.

  assert (HA4: is_exact_assignment_for A4 (get_A4_binded_nodes_in_g_path G (u, v, l))). { rewrite HeqA4. apply nodes_map_to_exact_assignment. }

  apply Heq with (A5 := A5) (default := default) (x := x) in HA4. clear Heq.
  destruct HA4 as [U [x' [HU [Hcond [Hx [Hx' HA4]]]]]].

  remember (g_path'' X A1 A2 A3 A4 AZ A5 default) as g.

  remember ((hd 0 (get_A4_binded_nodes_in_g_path G (u, v, l)), x) :: U) as Ux.
  remember (tl (get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G (u, v, l)) U x)) as LUx.
  assert (HUseq: assignments_equiv Ux ((hd 0 (get_A4_binded_nodes_in_g_path G (u, v, l)), x) :: U) /\
      list_assignments_equiv LUx
        (tl
           (get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G (u, v, l)) U
              x))).
  { split. rewrite HeqUx. unfold assignments_equiv. reflexivity.
    rewrite HeqLUx. apply list_assignments_equiv_identity. }
  rewrite HeqUx in HA4. rewrite HeqLUx in HA4.
  apply HA4 in HUseq. clear HA4.

  assert (HA: exists (A: assignments X), get_values G g U [] = Some A). { apply get_values_existence. apply HG. apply HU. }
  destruct HA as [A HA].

  assert (HUx: is_assignment_for Ux (nodes_in_graph G) = true).
  { destruct HUseq as [_ [_ [HUseq _]]]. simpl in HUseq. unfold sequence_of_ancestors_change_for_Z in HUseq. apply HUseq. right. left. reflexivity. }

  assert (HAx: exists (A: assignments X), get_values G g Ux [] = Some A). { apply get_values_existence. apply HG. apply HUx. }
  destruct HAx as [Ax HAx].

  remember (last (Ux :: LUx) Ux) as Ub'.
  assert (HUb': is_assignment_for Ub' (nodes_in_graph G) = true).
  { destruct HUseq as [_ [_ [HUseq _]]]. simpl in HUseq. unfold sequence_of_ancestors_change_for_Z in HUseq. apply HUseq. rewrite HeqUb'. rewrite <- last_suffix with (u := U) (a := Ux). right. apply last_mem. }

  assert (HAb': exists (Ab': assignments X), get_values G g Ub' [] = Some Ab'). { apply get_values_existence. apply HG. apply HUb'. }
  destruct HAb' as [Ab' HAb'].

  specialize H_cond_ind with (AZ := AZ) (g := g) (a := x') (Ua := U) (Aa := A) (b := x) (Ub := Ux) (Ab := Ax) (L := LUx)
        (Ub' := Ub') (Ab' := Ab').

  assert (Hv: node_in_path v (u, v, l) = true /\ ~ In v (find_colliders_in_path (u, v, l) G)).
  { split. unfold node_in_path. simpl. rewrite <- orb_assoc. rewrite orb_comm. rewrite eqb_refl. reflexivity.
    intros Hv. destruct Huvl as [Hcyc [_ [HpG _]]]. apply intermediate_node_in_path with (x := v) in HpG. destruct Hcyc as [_ [_ [Hcyc _]]]. apply Hcyc.
    apply HpG. right. right. apply Hv. }

  assert (Hva': get_assigned_value A v = Some x').
  { assert (Hf: find_value G g v U [] = Some x'). { apply Hx. apply Hv. }
    unfold find_value in Hf. rewrite HA in Hf. apply Hf. }

  assert (Hvb': get_assigned_value Ab' v = Some x).
  { assert (Hf: find_value G g v Ub' [] = Some x).
    { rewrite HeqUb'. destruct HUseq as [_ [_ [_ [_ HUseq]]]]. apply HUseq. apply Hv. }
    unfold find_value in Hf. rewrite HAb' in Hf. apply Hf. }

  assert (H_contra: get_assigned_value A v = get_assigned_value Ab' v).
  { assert (Hu: node_in_path u (u, v, l) = true /\ ~ In u (find_colliders_in_path (u, v, l) G)).
    { split. unfold node_in_path. simpl. rewrite eqb_refl. reflexivity.
      intros Hu. destruct Huvl as [Hcyc [_ [HpG _]]]. apply intermediate_node_in_path with (x := u) in HpG. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc.
      apply HpG. right. right. apply Hu. }

    apply H_cond_ind.
    - rewrite HeqAZ. split. apply nodes_map_to_exact_assignment. apply exact_assignment_assigns_once. apply HZnode.
    - split. apply HA. repeat split.
      + apply HU.
      + assert (Hf: find_value G g u U [] = Some x'). { apply Hx. apply Hu. }
        unfold find_value in Hf. rewrite HA in Hf. apply Hf.
      + apply Hcond.
    - split.
      + unfold sequence_of_ancestors_change_for_Z in HUseq. destruct HUseq as [_ [_ [HUseq _]]]. destruct HUseq as [HUseq _].
        unfold assignments_change_only_for_subset. intros w. split.
        * apply HUseq.
        * intros Hw. apply HUseq. intros Hw'. apply Hw. apply intersect_correct_element with (l1 := u :: path_int (u, v, l) ++ [v]). apply Hw'.
      + split. apply HAx. split.
        * apply HUx.
        * destruct HUseq as [HUseq _]. unfold find_value in HUseq. rewrite HAx in HUseq. apply HUseq.
    - assert (Hlen: path_length (u, v, l) <= num_nodes G). { apply path_length_acyclic_graph. apply Huvl. apply Huvl. }
      lia.
    - split. symmetry. apply HeqUb'. apply HAb'.
    - repeat split.
      + rewrite HeqUb'. apply HUseq.
      + apply HUb'.
      + assert (Hf: find_value G g u Ub' [] = Some x). { rewrite HeqUb'. destruct HUseq as [_ [_ [_ [_ HUseq]]]]. apply HUseq. apply Hu. }
        unfold find_value in Hf. rewrite HAb' in Hf. apply Hf.
    - unfold sequence_of_ancestors_change_for_Z in HUseq. apply HUseq. }

  apply Hx'. rewrite Hva' in H_contra. rewrite Hvb' in H_contra. inversion H_contra. reflexivity.
Qed.


Theorem path_d_separated_then_semantically_separated {X : Type} `{EqType X}: forall (G: graph) (u v: node),
  u <> v /\ generic_graph_and_type_properties_hold X G /\ node_in_graph v G = true
  -> forall (Z: nodes), subset Z (nodes_in_graph G) = true /\ each_node_appears_once Z /\ member u Z = false /\ member v Z = false
  -> d_separated_bool u v G Z = true -> semantically_separated X G u v Z.
Proof.
  intros G u' v'. intros [Huveq [HG Hnodev]] Z HZ.
  intros Hdsep. unfold semantically_separated.

  assert (Hdconn1: forall (anc u: node) (l: nodes), is_directed_path_in_graph (anc, u, l) G = true /\
          (forall w : node, w = anc \/ In w l -> ~ In w Z) -> acyclic_path_2 (anc, u, l) -> d_connected_2 (anc, u, l) G Z).
  { intros anc u l [Hdir HlZ]. intros Hcyc. apply directed_path_is_path in Hdir as Hpath.
    unfold d_connected_2. repeat split.
    - destruct (overlap Z (find_mediators_in_path (anc, u, l) G)) as [|] eqn:Hmed.
      + apply overlap_has_member_in_common in Hmed. destruct Hmed as [m [HmZ Hmmed]].
        assert (Hml: In m l).
        { apply intermediate_node_in_path with (x := m) in Hpath. apply Hpath. left. apply Hmmed. }
        specialize HlZ with (w := m). assert (F: ~(In m Z)). { apply HlZ. right. apply Hml. } exfalso. apply F. apply HmZ.
      + reflexivity.
    - destruct (overlap Z (find_confounders_in_path (anc, u, l) G)) as [|] eqn:Hcon.
      + apply overlap_has_member_in_common in Hcon. destruct Hcon as [c [HcZ Hccon]].
        assert (Hcl: In c l).
        { apply intermediate_node_in_path with (x := c) in Hpath. apply Hpath. right. left. apply Hccon. }
        specialize HlZ with (w := c). assert (F: ~(In c Z)). { apply HlZ. right. apply Hcl. } exfalso. apply F. apply HcZ.
      + reflexivity.
    - destruct (collider_descendants_not_conditioned (find_colliders_in_path (anc, u, l) G) G Z) as [|] eqn:Hcol.
      + destruct (find_colliders_in_path (anc, u, l) G) as [| h t] eqn:Hcol'.
        ** simpl in Hcol. discriminate Hcol.
        ** (* h is a collider, so h in l. But the path v...l...u is directed, contradiction *)
           assert (Hmemh: In h l).
           { apply intermediate_node_in_path with (x := h) in Hpath. apply Hpath. right. right. rewrite Hcol'. left. reflexivity. }
           assert (Hmedh: In h (find_mediators_in_path (anc, u, l) G)).
           { apply directed_path_all_mediators with (m := h). split. apply Hdir. apply Hmemh. }
           apply if_mediator_then_not_confounder_path in Hmedh. destruct Hmedh as [_ Hhcol]. exfalso. apply Hhcol. rewrite Hcol'. left. reflexivity.
           destruct HG as [_ [_ HG]]. apply HG. apply Hcyc.
      + unfold all_colliders_have_descendant_conditioned_on. unfold collider_descendants_not_conditioned in Hcol. apply forallb_true_iff_mem.
        intros col Hcol'. apply descendants_in_or_not_in. apply existsb_false with (x := col) in Hcol.
        ** apply Hcol.
        ** apply Hcol'. }

  assert (Hdconn2: forall (anc u v: node) (lu lv: nodes), is_directed_path_in_graph (anc, u, lu) G = true /\ (forall w : node, w = anc \/ In w lu -> ~ In w Z)
                                                       /\ is_directed_path_in_graph (anc, v, lv) G = true /\ (forall w : node, w = anc \/ In w lv -> ~ In w Z)
                   -> is_path_in_graph (u, v, (rev lu) ++ (anc :: lv)) G = true /\ acyclic_path_2 (u, v, (rev lu) ++ (anc :: lv)) -> d_connected_2 (u, v, (rev lu) ++ anc :: lv) G Z).
  { intros anc u v lu lv [Hdiru [HluZ [Hdirv HlvZ]]] [Hpath Hcyc].
    assert (Hconnu: d_connected_2 (anc, u, lu) G Z). { apply Hdconn1. split. apply Hdiru. apply HluZ. rewrite reverse_list_twice with (l := lu). apply reverse_path_still_acyclic. apply subpath_still_acyclic_2 with (v := v) (l2 := lv) (l3 := rev lu ++ anc :: lv). split. reflexivity. apply Hcyc. }
    assert (Hconnv: d_connected_2 (anc, v, lv) G Z). { apply Hdconn1. split. apply Hdirv. apply HlvZ. apply subpath_still_acyclic with (w := u) (l1 := rev lu) (l3 := rev lu ++ anc :: lv). split. reflexivity. apply Hcyc. }
    apply concat_d_connected_paths.
    - destruct HG as [_ [_ HG]]. apply HG.
    - apply Hpath.
    - split. apply reverse_d_connected_paths. apply Hconnu. split. apply Hconnv. apply Hcyc.
    - right. left. split.
      + apply confounders_vs_edges_in_path. destruct lu as [| hlu tlu].
        * destruct lv as [| hlv tlv].
          -- exists u. exists v. split.
             ++ simpl. repeat rewrite eqb_refl. reflexivity.
             ++ simpl in Hdiru. rewrite andb_comm in Hdiru. simpl in Hdiru. split. apply Hdiru.
                simpl in Hdirv. rewrite andb_comm in Hdirv. simpl in Hdirv. apply Hdirv.
          -- exists u. exists hlv. split.
             ++ apply sublist_breaks_down_list. exists []. exists (tlv ++ [v]). simpl. reflexivity.
             ++ simpl in Hdiru. rewrite andb_comm in Hdiru. simpl in Hdiru. split. apply Hdiru.
                simpl in Hdirv. apply split_and_true in Hdirv. destruct Hdirv as [Hdirv _]. apply Hdirv.
        * destruct lv as [| hlv tlv].
          -- exists hlu. exists v. split.
             ++ apply sublist_breaks_down_list. exists (u :: rev tlu). exists []. simpl. repeat rewrite <- app_assoc; simpl. reflexivity.
             ++ simpl in Hdiru. apply split_and_true in Hdiru. destruct Hdiru as [Hdiru _]. split. apply Hdiru.
                simpl in Hdirv. apply split_and_true in Hdirv. destruct Hdirv as [Hdirv _]. apply Hdirv.
          -- exists hlu. exists hlv. split.
             ++ apply sublist_breaks_down_list. exists (u :: rev tlu). exists (tlv ++ [v]). simpl. repeat rewrite <- app_assoc; simpl. reflexivity.
             ++ simpl in Hdiru. apply split_and_true in Hdiru. destruct Hdiru as [Hdiru _]. split. apply Hdiru.
                simpl in Hdirv. apply split_and_true in Hdirv. destruct Hdirv as [Hdirv _]. apply Hdirv.
      + specialize HluZ with (w := anc). apply HluZ. left. reflexivity. }

  assert (Hdconn_con: forall (anc: node) (u v: node), u <> v -> In anc (find_unblocked_ancestors G v Z) /\ In anc (find_unblocked_ancestors G u Z)
                  -> (exists (l: nodes), d_connected_2 (v, u, l) G Z /\ is_directed_path_in_graph (v, u, l) G = true /\ acyclic_path_2 (v, u, l) /\ (forall w : node, w = v \/ In w l -> ~ In w Z))
                     \/ (exists (l: nodes), d_connected_2 (u, v, l) G Z /\ is_directed_path_in_graph (u, v, l) G = true /\ acyclic_path_2 (u, v, l) /\ (forall w : node, w = u \/ In w l -> ~ In w Z))
                     \/ (exists (lu lv: nodes) (anc: node), d_connected_2 (u, v, (rev lu) ++ anc :: lv) G Z /\ is_path_in_graph (u, v, (rev lu) ++ anc :: lv) G = true
                          /\ is_directed_path_in_graph (anc, u, lu) G = true /\ is_directed_path_in_graph (anc, v, lv) G = true
                          /\ acyclic_path_2 (u, v, (rev lu) ++ anc :: lv) /\ (forall w : node, w = anc \/ In w lu \/ In w lv -> ~ In w Z))).
  { intros anc u v Huv [Hancv Hancu].
    destruct (member v (find_unblocked_ancestors G u Z)) as [|] eqn:Heqancv.
    - apply member_In_equiv in Heqancv. destruct (member u (find_unblocked_ancestors G v Z)) as [|] eqn:Heqancu.
      + (* cycle, contradiction *) exfalso. apply member_In_equiv in Heqancu. apply unblocked_ancestors_have_unblocked_directed_path in Heqancv.
        apply unblocked_ancestors_have_unblocked_directed_path in Heqancu.
        destruct Heqancu as [Heqancu | Heqancu]. apply Huv. apply Heqancu.
        destruct Heqancv as [Heqancv | Heqancv]. apply Huv. rewrite Heqancv. reflexivity.
        destruct Heqancu as [lu [Hlu _]]. destruct Heqancv as [lv [Hlv _]].
        assert (Hcycle: is_directed_path_in_graph (concat u v u lu lv) G = true).
        { apply concat_directed_paths. split. apply Hlu. apply Hlv. }
        destruct HG as [_ [_ HG]]. apply contains_cycle_false_correct with (p := (concat u v u lu lv)) in HG.
        * unfold concat in HG. unfold acyclic_path_2 in HG. destruct HG as [HG _]. apply HG. reflexivity.
        * apply Hcycle.
      + (* v -> ...l... -> u is d-connected path *) left. clear Hancu. clear Hancv.
        apply unblocked_ancestors_have_unblocked_directed_path in Heqancv. destruct Heqancv as [Hancu | Hancu]. exfalso. apply Huv. rewrite Hancu. reflexivity.
        destruct Hancu as [l [Hdir [Hcycu HlZ]]]. exists l.
        assert (Hconn: d_connected_2 (v, u, l) G Z). { apply Hdconn1. split. apply Hdir. apply HlZ. apply Hcycu. }
        split. apply Hconn. split. apply Hdir. split. apply Hcycu. apply HlZ.
    - pose proof Hancv as Hancv'. apply unblocked_ancestors_have_unblocked_directed_path in Hancv. destruct Hancv as [Hancv | Hancv].
      (* v is not an unblocked ancestor of u *) rewrite Hancv in Hancu. apply member_In_equiv in Hancu. rewrite Hancu in Heqancv. discriminate Heqancv.
      destruct (member u (find_unblocked_ancestors G v Z)) as [|] eqn:Heqancu.
      + (* u -> ...lv... -> v is a d-connected path *) right. left. clear Hancu. clear Hancv. apply member_In_equiv in Heqancu.
        apply unblocked_ancestors_have_unblocked_directed_path in Heqancu. destruct Heqancu as [Hancv | Hancv]. exfalso. apply Huv. apply Hancv.
        destruct Hancv as [l [Hdir [Hcycv HlZ]]]. exists l.
        assert (Hconn: d_connected_2 (u, v, l) G Z). { apply Hdconn1. split. apply Hdir. apply HlZ. apply Hcycv. }
        split. apply Hconn. split. apply Hdir. split. apply Hcycv. apply HlZ.
      + (* u <- ...lu... <- anc -> ...lv... -> v  is a d-connected path *) right. right.
        apply unblocked_ancestors_have_unblocked_directed_path in Hancu. destruct Hancu as [Hancu | Hancu]. rewrite Hancu in Hancv'. apply member_In_equiv in Hancv'. rewrite Hancv' in Heqancu. discriminate Heqancu.
        assert (Hanc': exists (anc': node) (lu lv: nodes), is_directed_path_in_graph (anc', u, lu) G = true /\ is_directed_path_in_graph (anc', v, lv) G = true
                       /\ (forall w : node, w = anc' \/ In w lu \/ In w lv -> ~ In w Z) /\ acyclic_path_2 (u, v, (rev lu) ++ (anc' :: lv))).
        { destruct Hancv as [lv' Hv']. destruct Hancu as [lu' Hu']. apply acyclic_path_if_common_ancestor with (anc := anc) (lu := lu') (lv := lv') (len := S (length lu')).
          - split. apply Huv. split. intros Hmem. apply member_In_equiv in Hmem. rewrite Hmem in Heqancu. discriminate Heqancu.
            intros Hmem. apply member_In_equiv in Hmem. rewrite Hmem in Heqancv. discriminate Heqancv.
          - lia.
          - apply Hv'.
          - apply Hu'. }
        destruct Hanc' as [anc' [lu [lv [Hdiru [Hdirv [HlulvZ Hcycuv]]]]]]. exists lu. exists lv. exists anc'.
        assert (Hpath: is_path_in_graph (u, v, (rev lu) ++ (anc' :: lv)) G = true).
        { apply concat_paths_still_a_path. split. apply reverse_path_in_graph. apply directed_path_is_path. apply Hdiru.
          apply directed_path_is_path. apply Hdirv. }
        assert (Hconn: d_connected_2 (u, v, (rev lu) ++ anc' :: lv) G Z).
        { apply Hdconn2. repeat split.
          - apply Hdiru.
          - intros w Hw. apply HlulvZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. left. apply Hw.
          - apply Hdirv.
          - intros w Hw. apply HlulvZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. right. apply Hw.
          - split. apply Hpath. apply Hcycuv. }
        split. apply Hconn. split. apply Hpath. split. apply Hdiru. split. apply Hdirv. split. apply Hcycuv. apply HlulvZ. }

  assert (Hdconn_con': forall (anc: node) (u v: node), u <> v -> In anc (find_unblocked_ancestors G v Z) /\ In anc (find_unblocked_ancestors G u Z)
                  -> d_separated_bool u v G Z = true -> False).
  { intros anc u v Huv [Hancv Hancu] Hsep.
    specialize Hdconn_con with (anc := anc) (u := u) (v := v). apply Hdconn_con in Huv.
    destruct Huv as [Hvlu | [Hulv | Hcon]].
    - destruct Hvlu as [l [Hconn [Hdir [Hcyc HlZ]]]].
      apply d_connected_path_not_d_separated with (l := rev l) in Hsep.
      * apply Hsep.
      * apply reverse_d_connected_paths. apply Hconn.
      * split. apply reverse_path_in_graph. apply directed_path_is_path. apply Hdir. apply reverse_path_still_acyclic. apply Hcyc.
    - destruct Hulv as [l [Hconn [Hdir [Hcyc HlZ]]]].
      apply d_connected_path_not_d_separated with (l := l) in Hsep.
      * apply Hsep.
      * apply Hconn.
      * split. apply directed_path_is_path. apply Hdir. apply Hcyc.
    - destruct Hcon as [lu [lv [anc' [Hconn [Hpath [_ [_ [Hcyc HlZ]]]]]]]].
      apply d_connected_path_not_d_separated with (u := u) (v := v) (l := (rev lu) ++ (anc' :: lv)) (G := G) (Z := Z).
      -- apply Hconn.
      -- split. apply Hpath. apply Hcyc.
      -- apply Hsep.
    - split. apply Hancv. apply Hancu. }

  intros AZ HAZ g a Ua Aa [HAa [HUa HZUa]]. intros b Ub Ab [HUab [HAb HUb]]. intros L HL Ub' Ab' [HUb' HAb'] [HZUb' HuUb'] Hseq.

  assert (HvUa: exists (va: X), find_value G g v' Ua [] = Some va).
  { apply find_value_existence.
    - destruct HG as [_ HG]. apply HG.
    - split. destruct HUa as [HUa _]. apply HUa. apply Hnodev. }
  assert (HvUb: exists (vb: X), find_value G g v' Ub [] = Some vb).
  { apply find_value_existence.
    - destruct HG as [_ HG]. apply HG.
    - split. destruct HUb as [HUb _]. apply HUb. apply Hnodev. }
  assert (HvUb': exists (vb': X), find_value G g v' Ub' [] = Some vb').
  { apply find_value_existence.
    - destruct HG as [_ HG]. apply HG.
    - split. destruct HuUb' as [HuUb' _]. apply HuUb'. apply Hnodev. }
  destruct HvUa as [va HvUa]. destruct HvUb as [vb HvUb]. destruct HvUb' as [vb' HvUb'].

  destruct (eqb va vb') as [|] eqn:Hvavb'.
  { apply eqb_eq' in Hvavb'. rewrite Hvavb' in HvUa. unfold find_value in HvUa. unfold find_value in HvUb'. rewrite HAa in HvUa. rewrite HAb' in HvUb'.
    rewrite HvUa. rewrite HvUb'. reflexivity. }

  exfalso.

  assert (Hfvavb': find_value G g v' Ua [] <> find_value G g v' Ub' []).
  { rewrite HvUa. rewrite HvUb'. intros F. inversion F. rewrite H1 in Hvavb'. rewrite eqb_refl' in Hvavb'. discriminate Hvavb'. }

  assert (Hancv: exists (a: node), In a (find_unblocked_ancestors G v' Z)
      /\ (In a (find_unblocked_ancestors G u' Z) \/
         exists (z: node),
           In a (find_unblocked_ancestors G z Z)
           /\ In z (get_conditioned_nodes_that_change_in_seq (Ua :: Ub :: L) Z AZ G))).
  { apply nodefun_value_only_affected_by_unblocked_ancestors_seq with (Ub' := Ub') (g := g). apply HG. symmetry. apply HUb'. apply Hfvavb'.
    split. apply HUa. apply HuUb'. apply Hnodev. split. apply HZUa. apply HZUb'. apply HUab. apply Hseq. }

  destruct Hancv as [ancv [Hancv Hancv']]. destruct Hancv' as [Hancv' | Hancv'].
  - specialize Hdconn_con' with (anc := ancv) (u := u') (v := v'). exfalso. apply Hdconn_con'. repeat split.
    + apply Huveq.
    + split. apply Hancv. apply Hancv'.
    + apply Hdsep.
  - destruct Hancv' as [z [Hancvz Hzseq]].

    assert (HzZ: In z Z). { apply conditioned_nodes_that_change_in_Z in Hzseq. destruct (member z Z) as [|] eqn:HzZ. apply member_In_equiv. apply HzZ.
      apply HAZ in HzZ. rewrite HzZ in Hzseq. discriminate Hzseq. }

    assert (HzAZ: is_assigned AZ z = true). { apply assigned_is_true. apply assigned_has_value with (L := Z). split. apply HzZ. apply HAZ. }

    assert (HU123: exists (U1 U2 U3: assignments X), sublist_X [U1; U2; U3] (Ua :: Ub :: L) = true
                    /\ In z (find_unblocked_ancestors_in_Z_contributors G Z AZ (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) U1 U2))).
    { apply conditioned_nodes_that_change_in_seq_attached_to_U_sublist. apply Hzseq. }
    destruct HU123 as [Ui' [Ui'' [Ui''' [HsubU Hz]]]].

    assert (Hzv: z <> v').
    { intros Hzv. rewrite Hzv in HzZ. destruct HZ as [_ [_ [_ Hzv']]]. apply member_In_equiv_F in Hzv'. apply Hzv'. apply HzZ. }
    apply Hdconn_con with (anc := ancv) in Hzv. 2: { split. apply Hancv. apply Hancvz. }

    assert (Hzv': (exists l : nodes,
         d_connected_2 (v', z, l) G Z /\
         is_directed_path_in_graph (v', z, l) G = true /\
         acyclic_path_2 (v', z, l) /\
         (forall w : node, w = v' \/ In w l -> ~ In w Z)) \/
      (exists (lu lv : nodes) (anc : node),
         d_connected_2 (z, v', rev lu ++ anc :: lv) G Z /\
         is_path_in_graph (z, v', rev lu ++ anc :: lv) G = true /\
         is_directed_path_in_graph (anc, z, lu) G = true /\
         is_directed_path_in_graph (anc, v', lv) G = true /\
         acyclic_path_2 (z, v', rev lu ++ anc :: lv) /\
         (forall w : node, w = anc \/ In w lu \/ In w lv -> ~ In w Z))).
    { destruct Hzv as [Hzv | [Hzv | Hzv]].
      2: { (* contradiction, z is in Z *) destruct Hzv as [l [_ [_ [_ Hzv]]]]. exfalso. apply Hzv with (w := z). left. reflexivity. apply HzZ. }
      left. apply Hzv. right. apply Hzv. }
    clear Hzv. pose proof Hzv' as Hzv. clear Hzv'.

    destruct L as [| U1 L'].
    { rewrite sublist_X_false in HsubU. discriminate HsubU. }

    assert (Hp: exists (luz: nodes), is_path_in_graph (u', z, luz) G = true /\ d_connected_2 (u', z, luz) G Z /\ acyclic_path_2 (u', z, luz) /\ path_out_of_end (u', z, luz) G = Some false).
    { assert (Hi: exists (i: nat), index_sublist [Ui'; Ui''; Ui'''] (Ua :: Ub :: U1 :: L') = Some i). { apply index_sublist_exists. apply HsubU. }
      destruct Hi as [i Hi]. apply index_sublist_loosen in Hi. clear Hzv. clear Hancvz. generalize dependent Ui'''. generalize dependent Ui''. generalize dependent Ui'. generalize dependent z.
      induction i as [| i' IH].
      - intros z Hzseq HzZ HzAZ Ui' Ui'' Hz Ui''' Hsub Hi.
        assert (HUieq: eqb_asmt Ui' Ua && eqb_asmt Ui'' Ub && eqb_asmt Ui''' U1 = true).
        { simpl in Hi. rewrite andb_assoc in Hi. rewrite andb_assoc in Hi. rewrite andb_comm in Hi. simpl in Hi. apply Hi. }
        assert (HUi': Ui' = Ua). { apply split_and_true in HUieq. destruct HUieq as [HUieq _]. apply split_and_true in HUieq. destruct HUieq as [HUieq _]. apply eqb_asmt_eq. apply HUieq. } rewrite HUi' in *. clear HUi'.
        assert (HUi'': Ui'' = Ub). { apply split_and_true in HUieq. destruct HUieq as [HUieq _]. apply split_and_true in HUieq. destruct HUieq as [_ HUieq]. apply eqb_asmt_eq in HUieq. apply HUieq. } rewrite HUi'' in *. clear HUi''.
        assert (HUi''': Ui''' = U1). { apply split_and_true in HUieq. destruct HUieq as [_ HUieq]. apply eqb_asmt_eq in HUieq. apply HUieq. } rewrite HUi''' in *. clear HUi'''. clear HUieq.
        apply ancestors_overlap_with_seq_then_contributor in Hz. 2: { apply HzAZ. }
        apply overlap_has_member_in_common in Hz. destruct Hz as [ancu [Hancuz Hancu]].

        assert (Huz: u' <> z).
        { intros Huz. rewrite <- Huz in HzZ. destruct HZ as [_ [_ [Huz' _]]]. apply member_In_equiv_F in Huz'. apply Huz'. apply HzZ. }
        apply Hdconn_con with (anc := ancu) in Huz.
        2: { split. apply Hancuz. destruct (member ancu (find_unblocked_ancestors G u' Z)) as [|] eqn:HmemZ.
             + apply member_In_equiv in HmemZ. apply HmemZ.
             + apply in_unblocked_that_changed in Hancu. assert (F: get_assigned_value Ua ancu = get_assigned_value Ub ancu).
              { apply HUab. apply member_In_equiv_F in HmemZ. apply HmemZ. }
              exfalso. apply Hancu. apply F. }
        destruct Huz as [Huz | [Huz | Huz]].
        + exfalso. destruct Huz as [luz Hluz]. apply Hluz with (w := z). left. reflexivity. apply HzZ.
        + destruct Huz as [luz Hluz]. exists luz. split. apply directed_path_is_path. apply Hluz. split. apply Hluz. split. apply Hluz.
          apply directed_path_into_end. apply HG. apply Hluz.
        + destruct Huz as [lu [lz [ancu' Hlulz]]]. exists (rev lu ++ ancu' :: lz). split. apply Hlulz. split. apply Hlulz. split. apply Hlulz.
          rewrite subpath_preserves_path_out_of_end with (w := ancu') (l1 := rev lu) (l2 := lz). 2: { reflexivity. }
          apply directed_path_into_end. apply HG. apply Hlulz.

      - intros z Hzseq HzZ HzAZ Ui' Ui'' Hz Ui''' Hsub Hi.

        assert (Hi': exists (Ui: assignments X), index_sublist_2 [Ui; Ui'; Ui''; Ui'''] (Ua :: Ub :: U1 :: L') i' = true). { apply sublist_with_index_one_less_2. apply Hi. }
        destruct Hi' as [Ui Hi'].
        assert (HUi: sublist_X [Ui; Ui'; Ui''; Ui'''] (Ua :: Ub :: U1 :: L') = true). { apply index_sublist_exists. apply index_sublist_tighten with (i := i'). apply Hi'. }
        apply path_between_two_conditioned_nodes with (Ua := Ua) (Ub := Ub) (Ui := Ui) (L := U1 :: L') in Hz.
        2: { apply HG. }
        2: { apply assigned_is_true. apply assigned_has_value with (L := Z). split. apply HzZ. apply HAZ. }
        2: { apply Hseq. }
        2: { apply sublist_X_start with (U := Ui'''). apply HUi. }

        destruct Hz as [z' [az Haz]].
        assert (Hz': In z' (get_conditioned_nodes_that_change_in_seq (Ua :: Ub :: U1 :: L') Z AZ G)).
        { apply conditioned_nodes_that_change_in_seq_attached_to_U_sublist. exists Ui. exists Ui'. exists Ui''. split.
          - apply sublist_X_start with (U := Ui'''). apply HUi.
          - apply Haz. }

        assert (HzZ': In z' Z).
        { apply conditioned_nodes_that_change_in_Z in Hz'. destruct (member z' Z) as [|] eqn:HzZ'. apply member_In_equiv. apply HzZ'.
          apply HAZ in HzZ'. rewrite HzZ' in Hz'. discriminate Hz'. }

        assert (Huz: u' <> z).
        { intros Huz. rewrite <- Huz in HzZ. destruct HZ as [_ [_ [Huz' _]]]. apply member_In_equiv_F in Huz'. apply Huz'. apply HzZ. }

        specialize IH with (z := z') (Ui' := Ui) (Ui'' := Ui') (Ui''' := Ui'').

        assert (Hind: exists luz : nodes,
                       is_path_in_graph (u', z', luz) G = true /\
                       d_connected_2 (u', z', luz) G Z /\
                       acyclic_path_2 (u', z', luz) /\
                       path_out_of_end (u', z', luz) G = Some false).
        { apply IH.
          - apply Hz'.
          - apply HzZ'.
          - apply conditioned_nodes_that_change_in_Z in Hz'. apply Hz'.
          - apply Haz.
          - apply sublist_X_start with (U := Ui'''). apply HUi.
          - apply index_for_start_of_sublist with (U := Ui'''). apply Hi'. }
        destruct Hind as [luz' Hluz'].

        (* create path from z' <- ... az ... -> z, then concatenate *)
        destruct (z' =? z) as [|] eqn:Hzz'.
        + apply eqb_eq in Hzz'. rewrite Hzz' in *. exists luz'. apply Hluz'.
        + apply eqb_neq in Hzz'. apply Hdconn_con with (anc := az) in Hzz'. 2: { split. apply Haz. apply Haz. }
          destruct Hzz' as [Hzz' | [Hzz' | Hzz']].
          * exfalso. destruct Hzz' as [lz Hlz]. apply Hlz with (w := z). left. reflexivity. apply HzZ.
          * exfalso. destruct Hzz' as [lz Hlz]. apply Hlz with (w := z'). left. reflexivity. apply HzZ'.
          * destruct Hzz' as [lz' [lz [az' Hlzlz']]].
            (* u ...luz'... -> z' <- ... rev lz' ... <- az' -> ... lz ... -> z *)
            destruct (overlap (u' :: luz') (z :: rev lz ++ [az'] ++ lz')) as [|] eqn:Hover.
            { apply lists_have_first_elt_in_common in Hover. destruct Hover as [luz1 [luz2 [lz1 [lz2 [x [Hx [Hx' Hover]]]]]]].
              destruct luz1 as [| hluz1 tluz1].
              - (* u is in the z'<-...->z path *)
                simpl in Hx. inversion Hx. rewrite <- H1 in *. destruct lz1 as [| hlz1 tlz1]. inversion Hx'. exfalso. apply Huz. symmetry. apply H3.
                inversion Hx'. rewrite <- H3 in *. clear H3. clear H1. exists (rev tlz1).
                assert (H4': rev lz2 ++ [u'] ++ rev tlz1 = rev lz' ++ az' :: lz).
                { assert (H4': rev (rev lz ++ az' :: lz') = rev (tlz1 ++ u' :: lz2)). { rewrite H4. reflexivity. }
                  repeat rewrite reverse_list_append in H4'. simpl in H4'. rewrite <- reverse_list_twice in H4'. repeat rewrite <- app_assoc in H4'.
                  symmetry. apply H4'. }

                split.
                { apply subpath_still_path with (w := z') (l1 := rev lz2) (l3 := rev lz' ++ az' :: lz). split. apply H4'. apply Hlzlz'. }
                split.
                { apply subpath_still_d_connected_gen with (w := z') (l1 := rev lz2) (l3 := rev lz' ++ az' :: lz). split. apply H4'. apply Hlzlz'. }
                split.
                { apply subpath_still_acyclic with (w := z') (l1 := rev lz2) (l3 := rev lz' ++ az' :: lz). split. apply H4'. apply Hlzlz'. }
                { rewrite <- subpath_preserves_path_out_of_end with (u := z') (l := rev lz' ++ az' :: lz) (l1 := rev lz2) (l2 := rev tlz1).
                  - rewrite subpath_preserves_path_out_of_end with (w := az') (l1 := rev lz') (l2 := lz).
                    apply directed_path_into_end. apply HG. apply Hlzlz'. reflexivity.
                  - symmetry. apply H4'. }
              - inversion Hx. rewrite <- H1 in *. clear H1. destruct lz1 as [| hlz1 tlz1].
                + (* z is in the u ... -> z' path *)
                  inversion Hx'. rewrite <- H1 in *. clear H1. exists (tluz1). split.
                  { apply subpath_still_path_2 with (v := z') (l2 := luz2) (l3 := luz'). split. symmetry. apply H2. apply Hluz'. }
                  split.
                  { apply subpath_still_d_connected_gen_2 with (v := z') (l2 := luz2) (l3 := luz'). split. symmetry. apply H2. apply Hluz'. }
                  split.
                  { apply subpath_still_acyclic_2 with (v := z') (l2 := luz2) (l3 := luz'). split. symmetry. apply H2. apply Hluz'. }
                  { (* z must be a collider since z in Z, so must have -> z *)
                    assert (Hmem: In z luz'). { rewrite H2. apply membership_append_r. left. reflexivity. }
                    destruct Hluz' as [Hpluz' [Hconnluz' [Hcycluz' _]]]. apply intermediate_node_in_path with (x := z) in Hpluz'. apply Hpluz' in Hmem.
                    destruct Hmem as [Hmem | [Hmem | Hmem]].
                    - exfalso. destruct Hconnluz' as [Hconn _]. apply no_overlap_non_member with (x := z) in Hconn. apply Hconn. apply HzZ. apply Hmem.
                    - exfalso. destruct Hconnluz' as [_ [Hconn _]]. apply no_overlap_non_member with (x := z) in Hconn. apply Hconn. apply HzZ. apply Hmem.
                    - apply colliders_vs_edges_in_path in Hmem. destruct Hmem as [z1 [z2 Hz]].
                      destruct (rev tluz1) as [| ht tt] eqn:Htluz1.
                      + assert (Htluz1': tluz1 = []). { rewrite reverse_list_twice with (l := tluz1). rewrite Htluz1. simpl. reflexivity. }
                        rewrite Htluz1' in *. rewrite H2 in Hz.
                        assert (Huz1: u' = z1).
                        { apply two_sublists_the_same_2 with (l := u' :: z :: luz2 ++ [z']) (a := z).
                          - simpl. repeat rewrite eqb_refl. reflexivity.
                          - destruct Hz as [Hz _]. apply start_of_sublist_still_sublist in Hz. apply Hz.
                          - apply acyclic_path_count with (x := z) in Hcycluz'. rewrite H2 in Hcycluz'. apply Hcycluz'. right. rewrite H2. simpl. left. reflexivity. }
                        simpl. rewrite <- Huz1 in Hz. destruct Hz as [_ [Hz _]]. apply acyclic_no_two_cycle in Hz. 2: { apply HG. } rewrite Hz. reflexivity.
                      + assert (Htluz1': tluz1 = rev tt ++ [ht]). { rewrite reverse_list_twice with (l := tluz1). rewrite Htluz1. simpl. reflexivity. }
                        rewrite Htluz1' in *. rewrite H2 in Hz.
                        assert (Huz1: ht = z1).
                        { apply two_sublists_the_same_2 with (l := (u' :: ((rev tt ++ [ht]) ++ z :: luz2) ++ [z'])) (a := z).
                          - apply sublist_breaks_down_list. exists (u' :: rev tt). exists (luz2 ++ [z']). rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                          - destruct Hz as [Hz _]. apply start_of_sublist_still_sublist in Hz. apply Hz.
                          - apply acyclic_path_count with (x := z) in Hcycluz'. rewrite H2 in Hcycluz'. apply Hcycluz'. right. rewrite H2. apply membership_append. apply membership_append_r. simpl. left. reflexivity. }
                        rewrite subpath_preserves_path_out_of_end with (w := ht) (l1 := rev tt) (l2 := []). simpl.
                        rewrite <- Huz1 in Hz. destruct Hz as [_ [Hz _]]. apply acyclic_no_two_cycle in Hz. 2: { apply HG. } rewrite Hz. reflexivity. reflexivity. }

                + inversion Hx'. rewrite <- H1 in *. clear H1. exists (tluz1 ++ [x] ++ rev tlz1).
                  assert (H3': rev lz2 ++ [x] ++ rev tlz1 = rev lz' ++ az' :: lz).
                  { assert (H3': rev (rev lz ++ az' :: lz') = rev (tlz1 ++ x :: lz2)). { rewrite H3. reflexivity. }
                    repeat rewrite reverse_list_append in H3'. simpl in H3'. rewrite <- reverse_list_twice in H3'. repeat rewrite <- app_assoc in H3'.
                    symmetry. apply H3'. }
                  assert (Hpath: is_path_in_graph (u', z, tluz1 ++ [x] ++ rev tlz1) G = true).
                  { apply concat_paths_still_a_path. split.
                    - apply subpath_still_path_2 with (v := z') (l2 := luz2) (l3 := luz'). split. symmetry. apply H2. apply Hluz'.
                    - apply subpath_still_path with (w := z') (l1 := rev lz2) (l3 := rev lz' ++ az' :: lz). split. apply H3'. apply Hlzlz'. }
                  assert (Hcyc: acyclic_path_2 (u', z, tluz1 ++ [x] ++ rev tlz1)).
                  { apply concat_paths_acyclic. split.
                    - apply Huz.
                    - split.
                      + apply subpath_still_acyclic_2 with (v := z') (l2 := luz2) (l3 := luz'). split. symmetry. apply H2. apply Hluz'.
                      + apply subpath_still_acyclic with (w := z') (l1 := rev lz2) (l3 := rev lz' ++ az' :: lz). split. apply H3'. apply Hlzlz'.
                    - split.
                      + intros F. apply no_overlap_non_member with (x := u') in Hover. apply Hover. left. reflexivity. right. apply membership_rev. apply F.
                      + intros F. apply no_overlap_non_member with (x := z) in Hover. apply Hover. right. apply F. left. reflexivity.
                    - apply no_overlap_non_member. intros y Hy Hy'. apply no_overlap_non_member with (x := y) in Hover. apply Hover. right. apply Hy'. right. apply membership_rev. apply Hy. }
                  split. apply Hpath.
                  assert (Hmem: In x (rev lz' ++ az' :: lz)). { rewrite <- H3'. apply membership_append_r. left. reflexivity. }
                  split.
                  { apply concat_d_connected_paths. apply HG. apply Hpath.
                    - split.
                      + apply subpath_still_d_connected_gen_2 with (v := z') (l2 := luz2) (l3 := luz'). split. symmetry. apply H2. apply Hluz'.
                      + split. apply subpath_still_d_connected_gen with (w := z') (l1 := rev lz2) (l3 := rev lz' ++ az' :: lz). split. apply H3'. apply Hlzlz'. apply Hcyc.
                    - (* since x is an intermediate node in z' <- ... <- az' -> ... -> z, it is either a mediator or az' (confounder), thus not in Z *)
                      (* if collider in new path, then desc path to z' or z. if mediator or confounder in new path, then fine since not in Z *)
                      assert (HxZ: ~In x Z).
                      { intros HxZ.
                        apply membership_append_or in Hmem. destruct Hmem as [Hmem | [Hmem | Hmem]].
                        - assert (Hmed: In x (find_mediators_in_path (z', z, rev lz' ++ az' :: lz) G)).
                          { apply subpath_preserves_mediators with (u := az') (l1 := rev lz') (l2 := lz). split. reflexivity. right.
                            apply mediators_same_in_reverse_path. apply directed_path_all_mediators. split. apply Hlzlz'. apply membership_rev. apply Hmem. }
                          destruct Hlzlz' as [[Hlzlz' _] _]. apply no_overlap_non_member with (x := x) in Hlzlz'. apply Hlzlz'. apply HxZ. apply Hmed.
                        - rewrite <- Hmem in *.
                          assert (Hmed: In az' (find_confounders_in_path (z', z, rev lz' ++ az' :: lz) G)).
                          { apply confounders_vs_edges_in_path. destruct lz' as [| hlz' tlz'].
                            * exists z'. destruct lz as [| hlz tlz].
                              - exists z. split.
                                + simpl. repeat rewrite eqb_refl. reflexivity.
                                + split.
                                  -- destruct Hlzlz' as [_ [_ [Hlzlz' _]]]. simpl in Hlzlz'. apply split_and_true in Hlzlz'. apply Hlzlz'.
                                  -- destruct Hlzlz' as [_ [_ [_ [Hlzlz' _]]]]. simpl in Hlzlz'. apply split_and_true in Hlzlz'. apply Hlzlz'.
                              - exists hlz. split.
                                + apply sublist_breaks_down_list. exists []. exists (tlz ++ [z]). simpl. reflexivity.
                                + split.
                                  -- destruct Hlzlz' as [_ [_ [Hlzlz' _]]]. simpl in Hlzlz'. apply split_and_true in Hlzlz'. apply Hlzlz'.
                                  -- destruct Hlzlz' as [_ [_ [_ [Hlzlz' _]]]]. simpl in Hlzlz'. apply split_and_true in Hlzlz'. apply Hlzlz'.
                            * exists hlz'. destruct lz as [| hlz tlz].
                              - exists z. split.
                                + apply sublist_breaks_down_list. exists (z' :: rev tlz'). exists []. simpl. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                                + split.
                                  -- destruct Hlzlz' as [_ [_ [Hlzlz' _]]]. simpl in Hlzlz'. apply split_and_true in Hlzlz'. apply Hlzlz'.
                                  -- destruct Hlzlz' as [_ [_ [_ [Hlzlz' _]]]]. simpl in Hlzlz'. apply split_and_true in Hlzlz'. apply Hlzlz'.
                              - exists hlz. split.
                                + apply sublist_breaks_down_list. exists (z' :: rev tlz'). exists (tlz ++ [z]). simpl. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                                + split.
                                  -- destruct Hlzlz' as [_ [_ [Hlzlz' _]]]. simpl in Hlzlz'. apply split_and_true in Hlzlz'. apply Hlzlz'.
                                  -- destruct Hlzlz' as [_ [_ [_ [Hlzlz' _]]]]. simpl in Hlzlz'. apply split_and_true in Hlzlz'. apply Hlzlz'. }
                          destruct Hlzlz' as [[_ [Hlzlz' _]] _]. apply no_overlap_non_member with (x := az') in Hlzlz'. apply Hlzlz'. apply HxZ. apply Hmed.
                        - assert (Hmed: In x (find_mediators_in_path (z', z, rev lz' ++ az' :: lz) G)).
                          { apply subpath_preserves_mediators with (u := az') (l1 := rev lz') (l2 := lz). split. reflexivity. left.
                            apply directed_path_all_mediators. split. apply Hlzlz'. apply Hmem. }
                          destruct Hlzlz' as [[Hlzlz' _] _]. apply no_overlap_non_member with (x := x) in Hlzlz'. apply Hlzlz'. apply HxZ. apply Hmed. }

                      apply intermediate_node_in_path with (x := x) in Hpath.
                      assert (Hmem': In x (tluz1 ++ [x] ++ rev tlz1)). { apply membership_append_r. left. reflexivity. }
                      apply Hpath in Hmem'. destruct Hmem' as [Hmem' | [Hmem' | Hmem']].
                      + left. split. apply Hmem'. apply HxZ.
                      + right. left. split. apply Hmem'. apply HxZ.
                      + right. right. split. apply Hmem'. unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common.
                        apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                        * exists z'. split. 2: { apply HzZ'. }
                          apply find_descendants_correct. right. apply membership_splits_list in Hmem. destruct Hmem as [lz1' [lz2' Hlz']].
                          exists (x, z', rev lz1'). split. 2: { apply path_start_end_refl. } apply subpath_still_directed with (w := az') (l1 := rev lz2') (l3 := lz').
                          split. rewrite reverse_list_twice with (l := lz'). unfold nodes in *. unfold node in *. rewrite <- Hlz'. rewrite reverse_list_append. simpl. rewrite <- app_assoc. reflexivity.
                          apply Hlzlz'.
                        * exists z. split. 2: { apply HzZ. }
                          apply find_descendants_correct. right. destruct Hmem as [Hmem | Hmem]. rewrite <- Hmem in *. exists (az', z, lz). split. apply Hlzlz'. apply path_start_end_refl.
                          apply membership_splits_list in Hmem. destruct Hmem as [lz1' [lz2' Hlz']].
                          exists (x, z, lz2'). split. 2: { apply path_start_end_refl. } apply subpath_still_directed with (w := az') (l1 := lz1') (l3 := lz).
                          split. apply Hlz'. apply Hlzlz'. }

                  split. apply Hcyc.
                  rewrite subpath_preserves_path_out_of_end with (w := x) (l1 := tluz1) (l2 := rev tlz1). 2: { reflexivity. }
                  rewrite <- subpath_preserves_path_out_of_end with (u := z') (l1 := rev lz2) (l2 := rev tlz1) (l := rev lz' ++ az' :: lz). 2: { symmetry. apply H3'. }
                  rewrite subpath_preserves_path_out_of_end with (w := az') (l1 := rev lz') (l2 := lz). 2: { reflexivity. }
                  apply directed_path_into_end. apply HG. apply Hlzlz'. }

            { (* no overlap, simply concatenate paths *)
              exists (luz' ++ [z'] ++ rev lz' ++ [az'] ++ lz).
              assert (Hpath: is_path_in_graph (u', z, luz' ++ [z'] ++ rev lz' ++ [az'] ++ lz) G = true).
              { apply concat_paths_still_a_path. split. apply Hluz'. apply Hlzlz'. }
              assert (Hcyc: acyclic_path_2 (u', z, luz' ++ [z'] ++ rev lz' ++ [az'] ++ lz)).
              { apply concat_paths_acyclic.
                - split.
                  + apply Huz.
                  + split. apply Hluz'. apply Hlzlz'.
                - split.
                  + intros F. apply no_overlap_non_member with (x := u') in Hover. apply Hover. left. reflexivity. right.
                    apply membership_rev. rewrite reverse_list_append. simpl. rewrite <- reverse_list_twice. rewrite <- app_assoc. apply F.
                  + intros F. apply no_overlap_non_member with (x := z) in Hover. apply Hover. right. apply F. left. reflexivity.
                - apply no_overlap_non_member. intros x Hx Hx'. apply no_overlap_non_member with (x := x) in Hover. apply Hover. right. apply Hx'. right.
                  apply membership_rev. rewrite reverse_list_append. simpl. rewrite <- reverse_list_twice. rewrite <- app_assoc. apply Hx. }
              split. apply Hpath. split.
              { apply concat_d_connected_paths. apply HG. apply Hpath.
                - split. apply Hluz'. split. apply Hlzlz'. apply Hcyc.
                - right. right. split.
                  + apply colliders_vs_edges_in_path. destruct Hluz' as [Hpluz' [_ [_ Houtluz']]]. apply path_out_of_end_edge in Houtluz'. 2: { apply HG. } 2: { apply Hpluz'. }
                    destruct Houtluz' as [x1 [luz'' Hluz'']]. exists x1. destruct Hlzlz' as [_ [_ [Hdirz' _]]].
                    apply directed_path_has_directed_edge_end in Hdirz' as Hdirz''. destruct Hdirz'' as [Hdirz'' | Hdirz''].
                    * exists az'. split.
                      -- rewrite Hdirz''. apply sublist_breaks_down_list. exists luz''. exists (lz ++ [z]). simpl. rewrite <- append_vs_concat. destruct Hluz'' as [Hluz'' _]. unfold nodes in *. unfold node in *. rewrite Hluz''.
                         rewrite <- app_assoc. reflexivity.
                      -- split. apply Hluz''. rewrite Hdirz'' in Hdirz'. simpl in Hdirz'. apply split_and_true in Hdirz'. apply Hdirz'.
                    * destruct Hdirz'' as [lz'' [x2 Hlz'']]. exists x2. split.
                      -- apply sublist_breaks_down_list. exists luz''. exists (rev lz'' ++ [az'] ++ lz ++ [z]). simpl. rewrite <- append_vs_concat. destruct Hluz'' as [Hluz'' _]. unfold nodes in *. unfold node in *. rewrite Hluz''.
                         destruct Hlz'' as [Hlz'' _]. rewrite Hlz''. rewrite reverse_list_append. simpl. f_equal. rewrite app_comm_cons. rewrite app_comm_cons. rewrite app_comm_cons. rewrite app_assoc. rewrite app_assoc. rewrite app_comm_cons. rewrite app_comm_cons. rewrite app_assoc with (l := luz'). reflexivity.
                      -- split. apply Hluz''. apply Hlz''.
                  + unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists z'. split. left. reflexivity. apply HzZ'. }
              split. apply Hcyc.
              rewrite subpath_preserves_path_out_of_end with (w := az') (l1 := luz' ++ [z'] ++ rev lz') (l2 := lz).
              apply directed_path_into_end. apply HG. apply Hlzlz'. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. } }

    (* using p, concat with Hzv path and get d-connected path from u' to v', contradicting Hsep. *)
    destruct Hp as [lu Hlu].
    assert (Hp: exists (l: nodes), is_path_in_graph (u', v', l) G = true /\ d_connected_2 (u', v', l) G Z /\ acyclic_path_2 (u', v', l)).
    { destruct Hzv as [Hzv | Hzv].
      - destruct Hzv as [lv Hlv]. (* z <- ...lv... <- v *)
        destruct (overlap (u' :: lu) (v' :: lv)) as [|] eqn:Hover.
        + apply lists_have_first_elt_in_common in Hover. destruct Hover as [lu1 [lu2 [lv1 [lv2 [x [Hx [Hx' Hover]]]]]]].
          destruct lu1 as [| hlu1 tlu1].
          * (* u is in the z <-...<- v path *)
            simpl in Hx. inversion Hx. rewrite <- H1 in *. destruct lv1 as [| hlv1 tlv1]. inversion Hx'. exfalso. apply Huveq. symmetry. apply H3.
            inversion Hx'. rewrite <- H3 in *. clear H3. clear H1. exists (rev tlv1).

            split.
            { apply reverse_path_in_graph. apply subpath_still_path_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply H4. apply directed_path_is_path. apply Hlv. }
            split.
            { apply reverse_d_connected_paths. apply subpath_still_d_connected_gen_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply H4. apply Hlv. }
            { apply reverse_path_still_acyclic. apply subpath_still_acyclic_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply H4. apply Hlv. }
          * inversion Hx. rewrite <- H1 in *. clear H1. destruct lv1 as [| hlv1 tlv1].
            --- (* z is in the u ... -> z' path *)
                inversion Hx'. rewrite <- H1 in *. clear H1. exists (tlu1). split.
                { apply subpath_still_path_2 with (v := z) (l2 := lu2) (l3 := lu). split. symmetry. apply H2. apply Hlu. }
                split.
                { apply subpath_still_d_connected_gen_2 with (v := z) (l2 := lu2) (l3 := lu). split. symmetry. apply H2. apply Hlu. }
                apply subpath_still_acyclic_2 with (v := z) (l2 := lu2) (l3 := lu). split. symmetry. apply H2. apply Hlu.
            --- inversion Hx'. rewrite <- H1 in *. clear H1. exists (tlu1 ++ [x] ++ rev tlv1).

                assert (Hpath: is_path_in_graph (u', v', tlu1 ++ [x] ++ rev tlv1) G = true).
                { apply concat_paths_still_a_path. split.
                  - apply subpath_still_path_2 with (v := z) (l2 := lu2) (l3 := lu). split. symmetry. apply H2. apply Hlu.
                  - apply reverse_path_in_graph. apply subpath_still_path_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply H3. apply directed_path_is_path. apply Hlv. }
                assert (Hcyc: acyclic_path_2 (u', v', tlu1 ++ [x] ++ rev tlv1)).
                { apply concat_paths_acyclic. split.
                  - apply Huveq.
                  - split.
                    + apply subpath_still_acyclic_2 with (v := z) (l2 := lu2) (l3 := lu). split. symmetry. apply H2. apply Hlu.
                    + apply reverse_path_still_acyclic. apply subpath_still_acyclic_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply H3. apply Hlv.
                  - split.
                    + intros F. apply no_overlap_non_member with (x := u') in Hover. apply Hover. left. reflexivity. right. apply membership_rev. apply F.
                    + intros F. apply no_overlap_non_member with (x := v') in Hover. apply Hover. right. apply F. left. reflexivity.
                  - apply no_overlap_non_member. intros y Hy Hy'. apply no_overlap_non_member with (x := y) in Hover. apply Hover. right. apply Hy'. right. apply membership_rev. apply Hy. }
                split. apply Hpath. split. 2: { apply Hcyc. }
                { apply concat_d_connected_paths. apply HG. apply Hpath.
                  - split.
                    + apply subpath_still_d_connected_gen_2 with (v := z) (l2 := lu2) (l3 := lu). split. symmetry. apply H2. apply Hlu.
                    + split. 2: { apply Hcyc. }
                      apply reverse_d_connected_paths. apply subpath_still_d_connected_gen_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply H3. apply Hlv.
                  - (* since x is an intermediate node in v' -> ... -> z, it is either a mediator, thus not in Z *)
                    (* if collider in new path, then desc path to z. if mediator or confounder in new path, then fine since not in Z *)
                    assert (HxZ: ~In x Z).
                    { apply Hlv with (w := x). right. rewrite H3. apply membership_append_r. left. reflexivity. }
                    apply intermediate_node_in_path with (x := x) in Hpath.
                    assert (Hmem': In x (tlu1 ++ [x] ++ rev tlv1)). { apply membership_append_r. left. reflexivity. }
                    apply Hpath in Hmem'. destruct Hmem' as [Hmem' | [Hmem' | Hmem']].
                    + left. split. apply Hmem'. apply HxZ.
                    + right. left. split. apply Hmem'. apply HxZ.
                    + right. right. split. apply Hmem'. unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists z. split. 2: { apply HzZ. }
                      apply find_descendants_correct. right. exists (x, z, lv2). split. 2: { apply path_start_end_refl. }
                      apply subpath_still_directed with (w := v') (l1 := tlv1) (l3 := lv). split. symmetry. apply H3. apply Hlv. }

        + exists (lu ++ [z] ++ rev lv).
          assert (Hpath: is_path_in_graph (u', v', lu ++ [z] ++ rev lv) G = true).
          { apply concat_paths_still_a_path. split. apply Hlu. apply reverse_path_in_graph. apply directed_path_is_path. apply Hlv. }
          split. apply Hpath.
          assert (Hcyc: acyclic_path_2 (u', v', lu ++ [z] ++ rev lv)).
          { apply concat_paths_acyclic. split. apply Huveq. split. apply Hlu. apply reverse_path_still_acyclic. apply Hlv.
            split.
            - intros F. apply no_overlap_non_member with (x := u') in Hover. apply Hover. left. reflexivity. right. apply membership_rev. apply F.
            - intros F. apply no_overlap_non_member with (x := v') in Hover. apply Hover. right. apply F. left. reflexivity.
            - apply no_overlap_non_member. intros x Hx Hx'. apply no_overlap_non_member with (x := x) in Hover. apply Hover. right. apply Hx'. right. apply membership_rev. apply Hx. }
          split. 2: { apply Hcyc. }
          apply concat_d_connected_paths. apply HG. apply Hpath. split. apply Hlu. split. apply reverse_d_connected_paths. apply Hlv. apply Hcyc.
          right. right. split.
          * unfold concat. apply colliders_vs_edges_in_path. destruct Hlu as [Hplu [_ [_ Hlu]]]. apply path_out_of_end_edge in Hlu. 2: { apply HG. } 2: { apply Hplu. }
            destruct Hlu as [x [lu' Hlu]]. exists x. destruct Hlv as [_ [Hlv _]]. pose proof Hlv as Hlv'. apply directed_path_has_directed_edge_end in Hlv.
            destruct Hlv as [Hlv | Hlv].
            -- rewrite Hlv in *. exists v'. split.
               ++ apply sublist_breaks_down_list. exists lu'. exists []. rewrite <- app_assoc. destruct Hlu as [Hlu _]. rewrite app_comm_cons. unfold nodes in *. unfold node in *. rewrite <- Hlu.
                  rewrite <- app_assoc. reflexivity.
               ++ split. apply Hlu. simpl in Hlv'. apply split_and_true in Hlv'. apply Hlv'.
            -- destruct Hlv as [lv' [x' Hlv]]. exists x'. split.
               ++ apply sublist_breaks_down_list. exists lu'. exists (rev lv' ++ [v']). rewrite <- app_assoc. destruct Hlu as [Hlu _]. rewrite app_comm_cons. unfold nodes in *. unfold node in *. rewrite <- Hlu.
                  rewrite <- app_assoc. destruct Hlv as [Hlv _]. rewrite Hlv. rewrite reverse_list_append. reflexivity.
               ++ split. apply Hlu. apply Hlv.
          * unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists z. split. left. reflexivity. apply HzZ.
      - destruct Hzv as [lz [lv [az Haz]]]. (* z <- ...rev lz... <- az -> ...lv... -> v *)
        destruct (overlap (u' :: lu) (v' :: rev lv ++ [az] ++ lz)) as [|] eqn:Hover.
        + apply lists_have_first_elt_in_common in Hover. destruct Hover as [lu1 [lu2 [lv1 [lv2 [x [Hx [Hx' Hover]]]]]]].
          destruct lu1 as [| hlu1 tlu1].
          * (* u is in the z<-...->v path *)
            simpl in Hx. inversion Hx. rewrite <- H1 in *. destruct lv1 as [| hlv1 tlv1]. inversion Hx'. exfalso. apply Huveq. symmetry. apply H3.
            inversion Hx'. rewrite <- H3 in *. clear H3. clear H1. exists (rev tlv1).
            assert (H4': rev lv2 ++ [u'] ++ rev tlv1 = rev lz ++ az :: lv).
            { assert (H4': rev (rev lv ++ az :: lz) = rev (tlv1 ++ u' :: lv2)). { rewrite H4. reflexivity. }
              repeat rewrite reverse_list_append in H4'. simpl in H4'. rewrite <- reverse_list_twice in H4'. repeat rewrite <- app_assoc in H4'.
              symmetry. apply H4'. }

            split.
            { apply subpath_still_path with (w := z) (l1 := rev lv2) (l3 := rev lz ++ az :: lv). split. apply H4'. apply Haz. }
            split.
            { apply subpath_still_d_connected_gen with (w := z) (l1 := rev lv2) (l3 := rev lz ++ az :: lv). split. apply H4'. apply Haz. }
            { apply subpath_still_acyclic with (w := z) (l1 := rev lv2) (l3 := rev lz ++ az :: lv). split. apply H4'. apply Haz. }

          * inversion Hx. rewrite <- H1 in *. clear H1. destruct lv1 as [| hlv1 tlv1].
            --- (* v' is in the u ... -> z path *)
                inversion Hx'. rewrite <- H1 in *. clear H1. exists (tlu1). split.
                { apply subpath_still_path_2 with (v := z) (l2 := lu2) (l3 := lu). split. symmetry. apply H2. apply Hlu. }
                split.
                { apply subpath_still_d_connected_gen_2 with (v := z) (l2 := lu2) (l3 := lu). split. symmetry. apply H2. apply Hlu. }
                { apply subpath_still_acyclic_2 with (v := z) (l2 := lu2) (l3 := lu). split. symmetry. apply H2. apply Hlu. }

            --- inversion Hx'. rewrite <- H1 in *. clear H1. exists (tlu1 ++ [x] ++ rev tlv1).
                assert (H3': rev lv2 ++ [x] ++ rev tlv1 = rev lz ++ az :: lv).
                { assert (H3': rev (rev lv ++ az :: lz) = rev (tlv1 ++ x :: lv2)). { rewrite H3. reflexivity. }
                  repeat rewrite reverse_list_append in H3'. simpl in H3'. rewrite <- reverse_list_twice in H3'. repeat rewrite <- app_assoc in H3'.
                  symmetry. apply H3'. }
                assert (Hpath: is_path_in_graph (u', v', tlu1 ++ [x] ++ rev tlv1) G = true).
                { apply concat_paths_still_a_path. split.
                  - apply subpath_still_path_2 with (v := z) (l2 := lu2) (l3 := lu). split. symmetry. apply H2. apply Hlu.
                  - apply subpath_still_path with (w := z) (l1 := rev lv2) (l3 := rev lz ++ az :: lv). split. apply H3'. apply Haz. }
                assert (Hcyc: acyclic_path_2 (u', v', tlu1 ++ [x] ++ rev tlv1)).
                { apply concat_paths_acyclic. split.
                  - apply Huveq.
                  - split.
                    + apply subpath_still_acyclic_2 with (v := z) (l2 := lu2) (l3 := lu). split. symmetry. apply H2. apply Hlu.
                    + apply subpath_still_acyclic with (w := z) (l1 := rev lv2) (l3 := rev lz ++ az :: lv). split. apply H3'. apply Haz.
                  - split.
                    + intros F. apply no_overlap_non_member with (x := u') in Hover. apply Hover. left. reflexivity. right. apply membership_rev. apply F.
                    + intros F. apply no_overlap_non_member with (x := v') in Hover. apply Hover. right. apply F. left. reflexivity.
                  - apply no_overlap_non_member. intros y Hy Hy'. apply no_overlap_non_member with (x := y) in Hover. apply Hover. right. apply Hy'. right. apply membership_rev. apply Hy. }
                split. apply Hpath. split. 2: { apply Hcyc. }
                assert (Hmem: In x (rev lz ++ az :: lv)). { rewrite <- H3'. apply membership_append_r. left. reflexivity. }
                { apply concat_d_connected_paths. apply HG. apply Hpath.
                  - split.
                    + apply subpath_still_d_connected_gen_2 with (v := z) (l2 := lu2) (l3 := lu). split. symmetry. apply H2. apply Hlu.
                    + split. 2: { apply Hcyc. }
                      apply subpath_still_d_connected_gen with (w := z) (l1 := rev lv2) (l3 := rev lz ++ az :: lv). split. apply H3'. apply Haz.
                  - (* since x is an intermediate node in z <- ... <- az -> ... -> v, it is either a mediator or az (confounder), thus not in Z *)
                    (* if collider in new path, then cannot be in az->...->v, since all edge out. Thus in z<-...<-az, so desc path to z.
                       if mediator or confounder in new path, then fine since not in Z *)
                    assert (HxZ: ~In x Z).
                    { intros HxZ.
                      apply membership_append_or in Hmem. destruct Hmem as [Hmem | [Hmem | Hmem]].
                      - assert (Hmed: In x (find_mediators_in_path (z, v', rev lz ++ az :: lv) G)).
                        { apply subpath_preserves_mediators with (u := az) (l1 := rev lz) (l2 := lv). split. reflexivity. right.
                          apply mediators_same_in_reverse_path. apply directed_path_all_mediators. split. apply Haz. apply membership_rev. apply Hmem. }
                        destruct Haz as [[Haz _] _]. apply no_overlap_non_member with (x := x) in Haz. apply Haz. apply HxZ. apply Hmed.
                      - rewrite <- Hmem in *.
                        assert (Hmed: In az (find_confounders_in_path (z, v', rev lz ++ az :: lv) G)).
                        { apply confounders_vs_edges_in_path. destruct lz as [| hlz' tlz'].
                          * exists z. destruct lv as [| hlz tlz].
                            - exists v'. split.
                              + simpl. repeat rewrite eqb_refl. reflexivity.
                              + split.
                                -- destruct Haz as [_ [_ [Haz _]]]. simpl in Haz. apply split_and_true in Haz. apply Haz.
                                -- destruct Haz as [_ [_ [_ [Haz _]]]]. simpl in Haz. apply split_and_true in Haz. apply Haz.
                            - exists hlz. split.
                              + apply sublist_breaks_down_list. exists []. exists (tlz ++ [v']). simpl. reflexivity.
                              + split.
                                -- destruct Haz as [_ [_ [Haz _]]]. simpl in Haz. apply split_and_true in Haz. apply Haz.
                                -- destruct Haz as [_ [_ [_ [Haz _]]]]. simpl in Haz. apply split_and_true in Haz. apply Haz.
                          * exists hlz'. destruct lv as [| hlz tlz].
                            - exists v'. split.
                              + apply sublist_breaks_down_list. exists (z :: rev tlz'). exists []. simpl. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                              + split.
                                -- destruct Haz as [_ [_ [Haz _]]]. simpl in Haz. apply split_and_true in Haz. apply Haz.
                                -- destruct Haz as [_ [_ [_ [Haz _]]]]. simpl in Haz. apply split_and_true in Haz. apply Haz.
                            - exists hlz. split.
                              + apply sublist_breaks_down_list. exists (z :: rev tlz'). exists (tlz ++ [v']). simpl. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                              + split.
                                -- destruct Haz as [_ [_ [Haz _]]]. simpl in Haz. apply split_and_true in Haz. apply Haz.
                                -- destruct Haz as [_ [_ [_ [Haz _]]]]. simpl in Haz. apply split_and_true in Haz. apply Haz. }
                        destruct Haz as [[_ [Haz _]] _]. apply no_overlap_non_member with (x := az) in Haz. apply Haz. apply HxZ. apply Hmed.
                      - assert (Hmed: In x (find_mediators_in_path (z, v', rev lz ++ az :: lv) G)).
                        { apply subpath_preserves_mediators with (u := az) (l1 := rev lz) (l2 := lv). split. reflexivity. left.
                          apply directed_path_all_mediators. split. apply Haz. apply Hmem. }
                        destruct Haz as [[Haz _] _]. apply no_overlap_non_member with (x := x) in Haz. apply Haz. apply HxZ. apply Hmed. }

                    apply intermediate_node_in_path with (x := x) in Hpath.
                    assert (Hmem': In x (tlu1 ++ [x] ++ rev tlv1)). { apply membership_append_r. left. reflexivity. }
                    apply Hpath in Hmem'. destruct Hmem' as [Hmem' | [Hmem' | Hmem']].
                    + left. split. apply Hmem'. apply HxZ.
                    + right. left. split. apply Hmem'. apply HxZ.
                    + right. right. split. apply Hmem'.
                      apply membership_append_or in Hmem.
                      assert (Hcount: acyclic_path (rev lz ++ [az] ++ lv) = true).
                      { apply acyclic_path_intermediate_nodes. intros w. destruct (member w (rev lz ++ [az] ++ lv)) as [|] eqn:Hw.
                        - destruct Haz as [_ [_ [_ [_ [Haz _]]]]]. apply acyclic_path_count with (x := w) in Haz. 2: { right. apply membership_append. apply member_In_equiv. apply Hw. }
                          apply member_In_equiv in Hw. apply member_count_at_least_1 in Hw. right.
                          simpl in Haz. destruct (z =? w) as [|] eqn:Hzw. rewrite count_app in Haz. inversion Haz. destruct (v' =? w) as [|]. lia. rewrite add_comm in H1. simpl in H1.
                          unfold nodes in *. unfold node in *. rewrite <- append_vs_concat in H1. rewrite <- app_assoc in H1. rewrite H1 in Hw. lia.
                          rewrite count_app in Haz. simpl in Haz. destruct (v' =? w) as [|]. rewrite add_comm in Haz. simpl in Haz. inversion Haz. unfold nodes in *. unfold node in *. rewrite <- append_vs_concat in H1. rewrite <- app_assoc in H1. lia.
                          rewrite add_comm in Haz. apply Haz.
                        - left. apply not_member_count_0. apply Hw. }

                      destruct Hmem as [Hmem | [Hmem | Hmem]].
                      * unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common.
                        exists z. split. 2: { apply HzZ. }
                        apply find_descendants_correct. right. apply membership_rev in Hmem. rewrite <- reverse_list_twice in Hmem. apply membership_splits_list in Hmem. destruct Hmem as [lz1' [lz2' Hlz']].
                        exists (x, z, lz2'). split. 2: { apply path_start_end_refl. } apply subpath_still_directed with (w := az) (l1 := lz1') (l3 := lz).
                        split. apply Hlz'. apply Haz.
                      * exfalso. rewrite <- Hmem in *.
                        assert (rev lz = rev lv2 /\ lv = rev tlv1).
                        { apply acyclic_path_equate_sublists with (m := az). split. 2: { symmetry. apply H3'. } apply Hcount. }
                        destruct H0 as [Hlz Hlv]. rewrite <- Hlz in *. rewrite <- Hlv in *. clear Hlz. clear Hlv.
                        apply colliders_vs_edges_in_path in Hmem'. destruct Hmem' as [y' [y'' Hy]].
                        destruct lv as [| hlv tlv].
                        -- assert (Hy'': y'' = v').
                           { apply two_sublists_the_same with (l := (u' :: (tlu1 ++ [az] ++ []) ++ [v'])) (a := az). apply end_of_sublist_still_sublist_2 with (a1 := y'). apply Hy.
                             apply sublist_breaks_down_list. exists (u' :: tlu1). exists []. simpl. rewrite <- app_assoc. reflexivity.
                             apply acyclic_path_count with (x := az) in Hcyc. apply Hcyc. right. apply membership_append. apply membership_append_r. left. reflexivity. }
                           rewrite Hy'' in *. clear Hy''. destruct Hy as [_ [_ Hy]]. apply acyclic_no_two_cycle in Hy. 2: { apply HG. }
                           destruct Haz as [_ [_ [_ [Haz _]]]]. simpl in Haz. rewrite Hy in Haz. discriminate Haz.
                        -- assert (Hy'': y'' = hlv).
                           { apply two_sublists_the_same with (l := (u' :: (tlu1 ++ [az] ++ hlv :: tlv) ++ [v'])) (a := az). apply end_of_sublist_still_sublist_2 with (a1 := y'). apply Hy.
                             apply sublist_breaks_down_list. exists (u' :: tlu1). exists (tlv ++ [v']). simpl. rewrite <- app_assoc. reflexivity.
                             apply acyclic_path_count with (x := az) in Hcyc. apply Hcyc. right. apply membership_append. apply membership_append_r. left. reflexivity. }
                           rewrite <- Hy'' in *. clear Hy''. destruct Hy as [_ [_ Hy]]. apply acyclic_no_two_cycle in Hy. 2: { apply HG. }
                           destruct Haz as [_ [_ [_ [Haz _]]]]. simpl in Haz. rewrite Hy in Haz. discriminate Haz.
                      * exfalso. apply membership_splits_list in Hmem. destruct Hmem as [lx1 [lx2 Hlx]].
                        assert (rev lz ++ [az] ++ lx1 = rev lv2 /\ lx2 = rev tlv1).
                        { apply acyclic_path_equate_sublists with (m := x).
                          assert (Heq: (rev lz ++ [az] ++ lx1) ++ [x] ++ lx2 = rev lz ++ [az] ++ lv).
                          { rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hlx. reflexivity. }
                          split.
                          - unfold nodes in *. unfold node in *. rewrite Heq. apply Hcount.
                          - unfold nodes in *. unfold node in *. rewrite Heq. symmetry. apply H3'. }
                        destruct H0 as [Hlz Hlv]. rewrite <- Hlz in *. rewrite <- Hlv in *. clear Hlz. clear Hlv.
                        apply colliders_vs_edges_in_path in Hmem'. destruct Hmem' as [y' [y'' Hy]].
                        destruct lx2 as [| hlv tlv].
                        -- assert (Hy'': y'' = v').
                           { apply two_sublists_the_same with (l := (u' :: (tlu1 ++ [x] ++ []) ++ [v'])) (a := x). apply end_of_sublist_still_sublist_2 with (a1 := y'). apply Hy.
                             apply sublist_breaks_down_list. exists (u' :: tlu1). exists []. simpl. rewrite <- app_assoc. reflexivity.
                             apply acyclic_path_count with (x := x) in Hcyc. apply Hcyc. right. apply membership_append. apply membership_append_r. left. reflexivity. }
                           rewrite Hy'' in *. clear Hy''. destruct Hy as [_ [_ Hy]]. apply acyclic_no_two_cycle in Hy. 2: { apply HG. }
                           assert (Hdir: is_directed_path_in_graph (x, v', []) G = true). { apply subpath_still_directed with (w := az) (l1 := lx1) (l3 := lv). split. apply Hlx. apply Haz. }
                           simpl in Hdir. rewrite Hy in Hdir. discriminate Hdir.
                        -- assert (Hy'': y'' = hlv).
                           { apply two_sublists_the_same with (l := (u' :: (tlu1 ++ [x] ++ hlv :: tlv) ++ [v'])) (a := x). apply end_of_sublist_still_sublist_2 with (a1 := y'). apply Hy.
                             apply sublist_breaks_down_list. exists (u' :: tlu1). exists (tlv ++ [v']). simpl. rewrite <- app_assoc. reflexivity.
                             apply acyclic_path_count with (x := x) in Hcyc. apply Hcyc. right. apply membership_append. apply membership_append_r. left. reflexivity. }
                           rewrite <- Hy'' in *. clear Hy''. destruct Hy as [_ [_ Hy]]. apply acyclic_no_two_cycle in Hy. 2: { apply HG. }
                           assert (Hdir: is_directed_path_in_graph (x, v', y'' :: tlv) G = true). { apply subpath_still_directed with (w := az) (l1 := lx1) (l3 := lv). split. apply Hlx. apply Haz. }
                           simpl in Hdir. rewrite Hy in Hdir. discriminate Hdir. }

        + exists (lu ++ [z] ++ rev lz ++ [az] ++ lv).
          assert (Hpath: is_path_in_graph (u', v', lu ++ [z] ++ rev lz ++ [az] ++ lv) G = true).
          { apply concat_paths_still_a_path. split. apply Hlu. apply Haz. }
          split. apply Hpath.
          assert (Hcyc: acyclic_path_2 (u', v', lu ++ [z] ++ rev lz ++ [az] ++ lv)).
          { apply concat_paths_acyclic. split. apply Huveq. split. apply Hlu. apply Haz.
            split.
            - intros F. apply no_overlap_non_member with (x := u') in Hover. apply Hover. left. reflexivity. right. apply membership_rev. rewrite reverse_list_append. rewrite <- reverse_list_twice. simpl. rewrite <- app_assoc. apply F.
            - intros F. apply no_overlap_non_member with (x := v') in Hover. apply Hover. right. apply F. left. reflexivity.
            - apply no_overlap_non_member. intros x Hx Hx'. apply no_overlap_non_member with (x := x) in Hover. apply Hover. right. apply Hx'. right.
              apply membership_rev. rewrite reverse_list_append. rewrite <- reverse_list_twice. simpl. rewrite <- app_assoc. apply Hx. }
          split. 2: { apply Hcyc. }
          apply concat_d_connected_paths. apply HG. apply Hpath. split. apply Hlu. split. apply Haz. apply Hcyc.
          right. right. split.
          * unfold concat. apply subpath_preserves_colliders with (u := az) (l1 := lu ++ z :: rev lz) (l2 := lv). split. rewrite <- app_assoc. reflexivity. right.
            apply colliders_vs_edges_in_path. destruct Hlu as [Hplu [_ [_ Hlu]]]. apply path_out_of_end_edge in Hlu. 2: { apply HG. } 2: { apply Hplu. }
            destruct Hlu as [x [lu' Hlu]]. exists x. destruct Haz as [_ [_ [Hlv _]]]. pose proof Hlv as Hlv'. apply directed_path_has_directed_edge_end in Hlv.
            destruct Hlv as [Hlv | Hlv].
            -- rewrite Hlv in *. exists az. split.
               ++ apply sublist_breaks_down_list. exists lu'. exists []. rewrite <- app_assoc. destruct Hlu as [Hlu _]. rewrite app_comm_cons. unfold nodes in *. unfold node in *. rewrite <- Hlu.
                  rewrite <- app_assoc. reflexivity.
               ++ split. apply Hlu. simpl in Hlv'. apply split_and_true in Hlv'. apply Hlv'.
            -- destruct Hlv as [lv' [x' Hlv]]. exists x'. split.
               ++ apply sublist_breaks_down_list. exists lu'. exists (rev lv' ++ [az]). rewrite <- app_assoc. destruct Hlu as [Hlu _]. rewrite app_comm_cons. unfold nodes in *. unfold node in *. rewrite <- Hlu.
                  rewrite <- app_assoc. destruct Hlv as [Hlv _]. rewrite Hlv. rewrite reverse_list_append. reflexivity.
               ++ split. apply Hlu. apply Hlv.
          * unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists z. split. left. reflexivity. apply HzZ. }

    destruct Hp as [l Hp]. apply d_connected_path_not_d_separated with (l := l) in Hdsep.
    + apply Hdsep.
    + apply Hp.
    + split. apply Hp. apply Hp.
Qed.

Theorem semantic_and_d_separation_equivalent {X : Type} `{EqType X}: forall (G: graph) (u v: node),
  u <> v /\ generic_graph_and_type_properties_hold X G /\ node_in_graph v G = true
  -> forall (Z: nodes), subset Z (nodes_in_graph G) = true /\ each_node_appears_once Z /\ member u Z = false /\ member v Z = false
  -> semantically_separated X G u v Z <-> d_separated_bool u v G Z = true.
Proof.
  intros G u' v'. intros [Huveq [HG Hnodev]] Z HZ. split.
  { intros Hcond. remember u' as u. remember v' as v. (* show that if NOT d-separated, then there is a contradiction. *)
    destruct (d_separated_bool u v G Z) as [|] eqn:Hsep.
    - reflexivity.
    - apply d_separated_vs_connected in Hsep. destruct Hsep as [l Hp].
      assert (contra: ~(semantically_separated X G u v Z)).
      { apply path_d_connected_then_not_semantically_separated with (p := (u, v, l)).
        - split. apply HG.
          apply paths_start_to_end_correct. split.
          + apply Hp.
          + split.
            * apply path_start_end_refl.
            * apply Hp.
        - apply HZ.
        - apply Hp. }
      exfalso. apply contra. apply Hcond. }
  { intros Hsep. apply path_d_separated_then_semantically_separated. easy. easy. easy. }
Qed.