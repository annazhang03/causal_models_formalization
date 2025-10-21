From Semantics Require Import FunctionRepresentation.
From Semantics Require Import FindValue.
From Semantics Require Import NodeCategorization.
From Semantics Require Import ColliderDescendants.
From Semantics Require Import SemanticSeparationDef.
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

(* return value of i-th parent, where val is (unobs, pa) *)
Definition f_parent_i (X: Type) (i: nat) (val: X * (list X)): X :=
  nth_default (fst val) (snd val) i.

Lemma find_value_child_equals_parent {X: Type}: forall (G: graph) (g: graphfun) (u v: node) (U: assignments X) (i: nat),
  (G_well_formed G = true /\ contains_cycle G = false) /\ is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph v G = true /\ node_in_graph u G = true
  -> index (find_parents v G) u = Some i /\ g v = f_parent_i X i
  -> find_value G g v U [] = find_value G g u U [].
Proof.
  intros G g u v U i [HG [HU [Hv Hu]]] [Hi Hg].
  assert (Hgv: exists (P: assignments X), find_values G g (find_parents v G) U [] = Some P
                  /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents v G)
                  /\ exists (unobs: X), get_assigned_value U v = Some unobs
                  /\ find_value G g v U [] = Some (g v (unobs, pa))).
  { apply find_value_evaluates_to_g. split.
    - apply HG.
    - split.
      + apply HU.
      + apply Hv. }
  destruct Hgv as [Pv [HPv [PAv [HPAv [unobsv [HUv Hgv]]]]]].
  assert (Hgu: exists x: X, find_value G g u U [] = Some x /\ nth_error Pv i = Some (u, x)).
  { apply find_values_preserves_index with (P := find_parents v G).
    - apply HG.
    - split.
      + apply HU.
      + apply Hu.
    - intros u' Hfp. apply edge_from_parent_to_child in Hfp.
      assert (Huv': node_in_graph u' G = true /\ node_in_graph v G = true).
      { apply edge_corresponds_to_nodes_in_well_formed. split. apply HG. apply Hfp. }
      destruct Huv' as [Huv' _]. apply Huv'.
    - split. apply HPv. apply Hi. }
  destruct Hgu as [x [Hgu Hi']].
  assert (Hvx: g v (unobsv, PAv) = x).
  { rewrite Hg. unfold f_parent_i. simpl.
    assert (Hn: nth_error PAv i = Some x).
    { apply parent_assignments_preserves_index with (P := Pv) (V := find_parents v G) (m := u).
      repeat split.
      - symmetry. apply HPAv.
      - apply Hi.
      - apply find_values_get_assigned with (G := G) (g := g) (P := find_parents v G) (U := U) (A := []). repeat split.
        + apply HPv.
        + apply index_exists. exists i. symmetry. apply Hi.
        + apply Hgu. }
    unfold nth_default. rewrite Hn. reflexivity. }
  rewrite Hgu. rewrite <- Hvx. apply Hgv.
Qed.

(* return x if values of i-th and j-th parents are equal, else y, where val is (unobs, pa) *)
Definition f_equate_ij (X: Type) `{EqType X} (i j: nat) (x y: X) (val: X * (list X)): X :=
  if (eqb (nth_default (fst val) (snd val) i) (nth_default (fst val) (snd val) j)) then x else y.

Definition f_constant (X: Type) (res: X) (val: X * (list X)): X := res.

Definition get_constant_nodefun_assignments {X: Type} (AZ: assignments X): assignments (nodefun X) :=
  map (fun (x: (node * X)) => (fst x, f_constant X (snd x))) AZ.

Lemma assigned_node_has_constant_nodefun {X: Type}: forall (AZ: assignments X) (z: node) (x: X),
  get_assigned_value AZ z = Some x -> get_assigned_value (get_constant_nodefun_assignments AZ) z = Some (f_constant X x).
Proof.
  intros AZ z x H.
  induction AZ as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. destruct (fst h =? z) as [|] eqn:Hhz.
    + simpl. rewrite Hhz. inversion H. reflexivity.
    + simpl. rewrite Hhz. apply IH. apply H.
Qed.


Definition f_changes_with_unobs {X: Type} (f: nodefun X): Prop := forall (x: X) (pa: list X), exists (unobs: X), f (unobs, pa) = x.

Definition f_unobs (X: Type) (val: X * (list X)): X := fst val.

Definition get_unobs_nodefun_assignments (X: Type) (A4: nodes): assignments (nodefun X) :=
  map (fun (x: node) => (x, f_unobs X)) A4.

Lemma assigned_node_has_unobs_nodefun {X: Type}: forall (A4: nodes) (z: node) (fw: nodefun X),
  get_assigned_value (get_unobs_nodefun_assignments X A4) z = Some fw -> fw = f_unobs X.
Proof.
  intros A4 z fw H.
  induction A4 as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. destruct (h =? z) as [|] eqn:Hhz.
    + inversion H. reflexivity.
    + apply IH. apply H.
Qed.


Lemma A4_nodes_not_in_A1: forall (G: graph) (u: node) (p: path),
  contains_cycle G = false
  -> acyclic_path_2 p
  -> is_path_in_graph p G = true
  -> In u (get_A4_binded_nodes_in_g_path G p) -> ~(In u (get_A1_binded_nodes_in_g_path G p)).
Proof.
  intros G w p HG Hc Hp Hu Hu'. destruct p as [[u v] l].
  apply A4_confounders_or_endpoints in Hu as H4. apply A1_mediators_or_endpoints in Hu' as H1.
  destruct H4 as [H4 | [H4 | H4]].
  - destruct H1 as [H1 | [H1 | H1]].
    + unfold get_A4_binded_nodes_in_g_path in Hu. unfold get_A1_binded_nodes_in_g_path in Hu'. destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
      * destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
        -- apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]].
           ++ apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [Hc _]]. apply Hc. rewrite <- H4. apply Hp. right. left. apply Hu.
           ++ destruct Hc as [Hc _]. apply Hc. rewrite Hu. rewrite <- H4. reflexivity.
           ++ apply Hu.
        -- apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [Hc _]]. apply Hc. rewrite <- H4. apply Hp. right. left. apply Hu.
        -- apply Hu.
      * destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
        -- apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [Hc _]]. apply Hc. rewrite <- H4. apply Hp. left. apply Hu'.
        -- apply membership_append_or in Hu'. destruct Hu' as [Hu' | [Hu' | Hu']].
           ++ apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [Hc _]]. apply Hc. rewrite <- H4. apply Hp. left. apply Hu'.
           ++ destruct Hc as [Hc _]. apply Hc. rewrite Hu'. rewrite <- H4. reflexivity.
           ++ apply Hu'.
        -- apply Hu.
    + apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [Hc _]]. apply Hc. rewrite <- H4. apply Hp. left. apply H1.
    + destruct Hc as [Hc _]. apply Hc. rewrite <- H4. apply H1.
  - destruct H1 as [H1 | [H1 | H1]].
    + apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [Hc _]]. apply Hc. rewrite <- H1. apply Hp. right. left. apply H4.
    + apply if_confounder_then_not_mediator_path in H4. destruct H4 as [H4 _]. apply H4. apply H1. apply HG. apply Hc.
    + apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [_ [Hc _]]]. apply Hc. rewrite <- H1. apply Hp. right. left. apply H4.
  - destruct H1 as [H1 | [H1 | H1]].
    + destruct Hc as [Hc _]. apply Hc. rewrite <- H1. apply H4.
    + apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [_ [Hc _]]]. apply Hc. rewrite <- H4. apply Hp. left. apply H1.
    + unfold get_A4_binded_nodes_in_g_path in Hu. unfold get_A1_binded_nodes_in_g_path in Hu'. destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
      * destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
        -- destruct Hu' as [Hu' | Hu'].
           ++ destruct Hc as [Hc _]. apply Hc. rewrite Hu'. apply H4.
           ++ apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [_ [Hc _]]]. apply Hc. rewrite <- H4. apply Hp. left. apply Hu'.
        -- apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [_ [Hc _]]]. apply Hc. rewrite <- H4. apply Hp. left. apply Hu'.
      * destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
        -- apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [_ [Hc _]]]. apply Hc. rewrite <- H4. apply Hp. right. left. apply Hu.
        -- clear Hu'. pose proof Hu as Hu'. destruct Hu' as [Hu' | Hu'].
           ++ destruct Hc as [Hc _]. apply Hc. rewrite Hu'. apply H4.
           ++ apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [_ [Hc _]]]. apply Hc. rewrite <- H4. apply Hp. right. left. apply Hu'.
      * apply Hu.
Qed.

Lemma A4_nodes_not_in_A2: forall (G: graph) (u: node) (p: path),
  contains_cycle G = false
  -> acyclic_path_2 p
  -> is_path_in_graph p G = true
  -> In u (get_A4_binded_nodes_in_g_path G p) -> ~(In u (get_A2_binded_nodes_in_g_path G p)).
Proof.
  intros G w p HG Hc Hp Hu Hu'. destruct p as [[u v] l].
  apply A4_confounders_or_endpoints in Hu. unfold get_A2_binded_nodes_in_g_path in Hu'.
  destruct Hu as [Hu | [Hu | Hu]].
  - apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [Hc _]]. apply Hc. rewrite <- Hu. apply Hp.
    right. right. apply Hu'.
  - apply if_confounder_then_not_mediator_path in Hu. destruct Hu as [_ Hu]. apply Hu. apply Hu'. apply HG. apply Hc.
  - apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [_ [Hc _]]]. apply Hc. rewrite <- Hu. apply Hp.
    right. right. apply Hu'.
Qed.


Lemma A2_nodes_not_in_A1: forall (G: graph) (u: node) (p: path),
  contains_cycle G = false
  -> acyclic_path_2 p
  -> is_path_in_graph p G = true
  -> In u (get_A2_binded_nodes_in_g_path G p) -> ~(In u (get_A1_binded_nodes_in_g_path G p)).
Proof.
  intros G w p HG Hc Hp Hu' Hu. destruct p as [[u v] l].
  apply A1_mediators_or_endpoints in Hu. unfold get_A2_binded_nodes_in_g_path in Hu'.
  destruct Hu as [Hu | [Hu | Hu]].
  - apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [Hc _]]. apply Hc. rewrite <- Hu. apply Hp.
    right. right. apply Hu'.
  - apply if_mediator_then_not_confounder_path in Hu. destruct Hu as [_ Hu]. apply Hu. apply Hu'. apply HG. apply Hc.
  - apply intermediate_node_in_path with (x := w) in Hp. destruct Hc as [_ [_ [Hc _]]]. apply Hc. rewrite <- Hu. apply Hp.
    right. right. apply Hu'.
Qed.

Definition A3_nodes_not_assigned_elsewhere {X: Type} (A3: assignments nat) (G: graph) (p: path): Prop :=
  forall (u: node),
    (In u (get_A1_binded_nodes_in_g_path G p) -> is_assigned A3 u = false)
    /\ (In u (get_A2_binded_nodes_in_g_path G p) -> is_assigned A3 u = false)
    /\ (In u (get_A4_binded_nodes_in_g_path G p) -> is_assigned A3 u = false).

Lemma descendant_paths_disjoint_with_A4: forall (D: assignments (nodes * node)) (u v: node) (l: nodes) (A3: assignments nat) (G: graph) (Z: nodes),
  descendant_paths_disjoint D u v l G Z
  -> get_A3_assignments_for_desc_paths D G (find_colliders_in_path (u, v, l) G) = Some A3
  -> forall (x: node), In x (get_A4_binded_nodes_in_g_path G (u, v, l))
  -> get_assigned_value A3 x = None.
Proof.
  intros D u v l A3 G Z Hdesc HA3 x Hx.
  destruct (get_assigned_value A3 x) as [r|] eqn:Hr.
  - assert (Hrx: is_assigned A3 x = true). { apply assigned_is_true. exists r. apply Hr. }
    apply A3_nodes_belong_to_collider with (D := D) (G := G) (u := u) (v := v) (l := l) in Hrx.
    + destruct Hrx as [c [d [p [Hc [HDc [Hdc Hxpd]]]]]].
      unfold descendant_paths_disjoint in Hdesc.
      destruct Hdesc as [_ Hdesc]. apply Hdesc in Hc. destruct Hc as [[Hc _] | Hc].
      * rewrite HDc in Hc. inversion Hc. rewrite H1 in Hdc. rewrite eqb_refl in Hdc. discriminate Hdc.
      * destruct Hc as [p' [d' [HDc' [_ [_ [_ [_ [Hover _]]]]]]]]. rewrite HDc in HDc'. inversion HDc'. rewrite <- H0 in *. rewrite <- H1 in *.
        clear HDc'. clear H0. clear H1.
        exfalso. apply no_overlap_non_member with (x := x) in Hover. apply Hover. apply Hxpd.
        apply A4_nodes_in_path in Hx. rewrite node_in_path_equiv in Hx. apply member_In_equiv. apply Hx.
    + apply HA3.
  - reflexivity.
Qed.

Lemma descendant_paths_disjoint_with_A2: forall (D: assignments (nodes * node)) (u v: node) (l: nodes) (A3: assignments nat) (G: graph) (Z: nodes),
  descendant_paths_disjoint D u v l G Z
  -> get_A3_assignments_for_desc_paths D G (find_colliders_in_path (u, v, l) G) = Some A3
  -> forall (x: node), In x (get_A2_binded_nodes_in_g_path G (u, v, l))
  -> get_assigned_value A3 x = None.
Proof.
  intros D u v l A3 G Z Hdesc HA3 x Hx.
  destruct (get_assigned_value A3 x) as [r|] eqn:Hr.
  - assert (Hrx: is_assigned A3 x = true). { apply assigned_is_true. exists r. apply Hr. }
    apply A3_nodes_belong_to_collider with (D := D) (G := G) (u := u) (v := v) (l := l) in Hrx.
    + destruct Hrx as [c [d [p [Hc [HDc [Hdc Hxpd]]]]]].
      unfold descendant_paths_disjoint in Hdesc.
      destruct Hdesc as [_ Hdesc]. apply Hdesc in Hc. destruct Hc as [[Hc _] | Hc].
      * rewrite HDc in Hc. inversion Hc. rewrite H1 in Hdc. rewrite eqb_refl in Hdc. discriminate Hdc.
      * destruct Hc as [p' [d' [HDc' [_ [_ [_ [_ [Hover _]]]]]]]]. rewrite HDc in HDc'. inversion HDc'. rewrite <- H0 in *. rewrite <- H1 in *.
        clear HDc'. clear H0. clear H1.
        exfalso. apply no_overlap_non_member with (x := x) in Hover. apply Hover. apply Hxpd.
        unfold get_A2_binded_nodes_in_g_path in Hx. apply colliders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        apply sublist_member with (l1 := [y;x;z]). split. right. left. reflexivity. apply Hx.
    + apply HA3.
  - reflexivity.
Qed.

Lemma descendant_paths_disjoint_with_A1: forall (D: assignments (nodes * node)) (u v: node) (l: nodes) (A3: assignments nat) (G: graph) (Z: nodes),
  descendant_paths_disjoint D u v l G Z
  -> get_A3_assignments_for_desc_paths D G (find_colliders_in_path (u, v, l) G) = Some A3
  -> forall (x: node), In x (get_A1_binded_nodes_in_g_path G (u, v, l))
  -> get_assigned_value A3 x = None.
Proof.
  intros D u v l A3 G Z Hdesc HA3 x Hx.
  destruct (get_assigned_value A3 x) as [r|] eqn:Hr.
  - assert (Hrx: is_assigned A3 x = true). { apply assigned_is_true. exists r. apply Hr. }
    apply A3_nodes_belong_to_collider with (D := D) (G := G) (u := u) (v := v) (l := l) in Hrx.
    + destruct Hrx as [c [d [p [Hc [HDc [Hdc Hxpd]]]]]].
      unfold descendant_paths_disjoint in Hdesc.
      destruct Hdesc as [_ Hdesc]. apply Hdesc in Hc. destruct Hc as [[Hc _] | Hc].
      * rewrite HDc in Hc. inversion Hc. rewrite H1 in Hdc. rewrite eqb_refl in Hdc. discriminate Hdc.
      * destruct Hc as [p' [d' [HDc' [_ [_ [_ [_ [Hover _]]]]]]]]. rewrite HDc in HDc'. inversion HDc'. rewrite <- H0 in *. rewrite <- H1 in *.
        clear HDc'. clear H0. clear H1.
        exfalso. apply no_overlap_non_member with (x := x) in Hover. apply Hover. apply Hxpd.
        apply A1_nodes_in_path in Hx. rewrite node_in_path_equiv in Hx. apply member_In_equiv. apply Hx.
    + apply HA3.
  - reflexivity.
Qed.

Definition g_path'' (X: Type) `{EqType X} (A1: assignments nat) (A2: assignments (nat * nat * X * X)) (A3: assignments nat) (A4: assignments X) (AZ: assignments X) (A5: assignments (nodefun X)) (def: nodefun X) (u: node): nodefun X :=
  match (get_assigned_value A1 u) with
  | Some i => f_parent_i X i (* mediators in the path, sometimes u and v depending on arrow directions *)
  | None => match (get_assigned_value A2 u) with
            | Some (i, j, x, y) => f_equate_ij X i j x y (* colliders, need to equate two parents in path *)
            | None => match (get_assigned_value A3 u) with
                      | Some i => f_parent_i X i (* descendants of colliders *)
                      | None => match (get_assigned_value A4 u) with
                                | Some _ => f_unobs X (* confounders, sometimes u and v *)
                                | None => match (get_assigned_value AZ u) with
                                          | Some z => f_constant X z
                                          | None => match (get_assigned_value A5 u) with
                                                    | Some f => f
                                                    | None => def
                                                    end
                                          end
                                end
                      end
            end
  end.




Lemma define_sets_for_equating_values_on_d_connected_path {X : Type} `{EqType X}: forall (G: graph) (u v: node) (p: path)
  (D: assignments (nodes * node)),
  generic_graph_and_type_properties_hold X G /\ In p (find_all_paths_from_start_to_end u v G) ->
  forall (Z: nodes) (AZ: assignments X), ~(In u Z) /\ ~(In v Z) -> is_exact_assignment_for AZ Z -> d_connected_2 p G Z -> descendant_paths_disjoint_col D u v (path_int p) G Z
  -> exists (A1: assignments nat) (A2: assignments (nat * nat * X * X)) (A3: assignments nat),
     is_exact_assignment_for A1 (get_A1_binded_nodes_in_g_path G p) /\ A1_nodes_binded_to_parent_in_path G p A1 /\ each_node_assigned_once A1
     /\ is_exact_assignment_for A2 (get_A2_binded_nodes_in_g_path G p) /\ A2_nodes_colliders_in_graph G p A2 /\ A2_consistent_with_D D A2 AZ
     /\ get_A3_assignments_for_desc_paths D G (find_colliders_in_path (u, v, path_int p) G) = Some A3.
Proof.
  intros G u v p D [HG Hp]. intros Z AZ [HuZ HvZ] HAZ Hconn Hdesc.
  assert (Hpath: exists (l: nodes), p = (u, v, l)).
  { destruct p as [[u' v'] l]. apply paths_start_to_end_correct in Hp. destruct Hp as [_ [Hp _]].
    apply path_start_end_equal in Hp. destruct Hp as [Huu' Hvv']. exists l. rewrite Huu'. rewrite Hvv'. reflexivity. }
  destruct Hpath as [l Hpath]. rewrite Hpath in *. clear Hpath.

  remember (u :: l ++ [v]) as n.
  assert (Hl: exists (l': nodes), l' = u :: l ++ [v] /\ sublist l' n = true).
  { exists n. split.
    - apply Heqn.
    - apply sublist_breaks_down_list. exists []. exists []. simpl. rewrite append_identity. reflexivity. }
  clear Heqn.
  generalize dependent u. generalize dependent l. generalize dependent D. induction n as [| hn tn IH].
  - intros D l u Hp HuZ Hconn Hdesc Hl. destruct Hl as [l' [Hl' Hsub]]. destruct l' as [| hl tl]. discriminate Hl'. simpl in Hsub. discriminate Hsub.
  - intros D l u Hp HuZ Hconn Hdesc Hl. destruct l as [| h t].
    (* base case: path consists of only u and v *)
    { destruct (path_out_of_start (u, v, []) G) as [|] eqn:Hout.
      + (* u -> v: A1 = {v: i}, where i is the index of u in pa(v). A2 = {} *)
        assert (Hin: path_into_start (u, v, []) G = false).
        { apply acyclic_path_one_direction in Hout.
          -- apply Hout.
          -- split. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
             unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [_ HG]]. apply HG. }
        assert (Hi: exists i: nat, index (find_parents v G) u = Some i).
        { assert (Hu: In u (find_parents v G)).
          { apply edge_from_parent_to_child. simpl in Hout. destruct G as [V E]. simpl. simpl in Hout. apply split_and_true in Hout.
            destruct Hout as [_ Hout]. apply Hout. }
          apply index_exists in Hu. destruct Hu as [i Hi]. exists i. rewrite Hi. reflexivity. }
        destruct Hi as [i Hi].
        exists [(v, i)]. exists []. exists []. repeat split.
        * simpl. simpl in Hin. rewrite Hin. simpl. rewrite eqb_refl. simpl. reflexivity.
        * intros w Hmem. simpl in Hmem. simpl in Hin. rewrite Hin in Hmem. simpl in Hmem.
          simpl. destruct (v =? w) as [|] eqn:Hvw.
          -- discriminate Hmem.
          -- rewrite eqb_sym. rewrite Hvw. reflexivity.
        * unfold A1_nodes_binded_to_parent_in_path. intros m i' Hmem. simpl in Hmem. destruct Hmem as [Hmem | F]. inversion Hmem. rewrite H1 in *. rewrite H2 in *. exists u. repeat split.
          -- apply index_correct. symmetry. apply Hi.
          -- left. simpl. repeat rewrite eqb_refl. reflexivity.
          -- exfalso. apply F.
        * unfold each_node_assigned_once. intros w Hw. simpl in Hw. rewrite orb_comm in Hw. simpl in Hw. simpl. rewrite eqb_sym. rewrite Hw.
          simpl. reflexivity.
        * unfold A2_nodes_colliders_in_graph. intros c i' j' x y F. exfalso. apply F.
        * unfold A2_consistent_with_D. intros w iw jw xw yw Hw. simpl in Hw. discriminate Hw.

      + (* u <- v: A1 = {u: i}, where i is the index of v in pa(u). A2 = {} *)
        assert (Hin: path_into_start (u, v, []) G = true).
        { apply acyclic_path_one_direction_2 in Hout.
          -- apply Hout.
          -- split. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
             unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [_ HG]]. apply HG. }
        assert (Hi: exists i: nat, index (find_parents u G) v = Some i).
        { assert (Hu: In v (find_parents u G)).
          { apply edge_from_parent_to_child. simpl in Hout. destruct G as [V E]. simpl. simpl in Hin. apply split_and_true in Hin.
            destruct Hin as [_ Hin]. apply Hin. }
        apply index_exists in Hu. destruct Hu as [i Hi]. exists i. rewrite Hi. reflexivity. }
        destruct Hi as [i Hi].
        exists [(u, i)]. exists []. exists []. repeat split.
        * simpl. simpl in Hin. rewrite Hin. simpl. rewrite eqb_refl. simpl. reflexivity.
        * intros w Hmem. simpl in Hmem. simpl in Hin. rewrite Hin in Hmem. simpl in Hmem.
          simpl. destruct (u =? w) as [|] eqn:Huw.
          -- discriminate Hmem.
          -- rewrite eqb_sym. rewrite Huw. reflexivity.
        * unfold A1_nodes_binded_to_parent_in_path. intros m i' Hmem. simpl in Hmem. destruct Hmem as [Hmem | F]. inversion Hmem. rewrite H1 in *. rewrite H2 in *. exists v. repeat split.
          -- apply index_correct. symmetry. apply Hi.
          -- right. simpl. repeat rewrite eqb_refl. reflexivity.
          -- exfalso. apply F.
        * unfold each_node_assigned_once. intros w Hw. simpl in Hw. rewrite orb_comm in Hw. simpl in Hw. simpl. rewrite eqb_sym. rewrite Hw.
          simpl. reflexivity.
        * unfold A2_nodes_colliders_in_graph. intros c i' j' x y F. exfalso. apply F.
        * unfold A2_consistent_with_D. intros w iw jw xw yw Hw. simpl in Hw. discriminate Hw. }

    (* induction step: assume true for path (h, v, t). Show true for (u, v, h :: t) *)
    destruct (path_out_of_h G u v h t) as [|] eqn:Houth.
    { (* out of h: u <-> h -> ... v *)
      specialize IH with (u := h) (l := t) (D := D).
      assert (Hp': In (h, v, t) (find_all_paths_from_start_to_end h v G)).
      { apply paths_start_to_end_correct in Hp. apply paths_start_to_end_correct. split.
        - apply is_path_in_graph_induction with (u := u). apply Hp.
        - split. apply path_start_end_refl. apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity. apply Hp. }
      pose proof Hp' as Hpind. apply IH in Hp'. clear IH.
      + destruct Hp' as [A1' [A2' [A3' HA12]]]. destruct HA12 as [HA1' [HA1'' [HA1''' [HA2' [HA2'' [HA2D HA3']]]]]].
        (* u <-> h -> ... <-> v *)
        assert (HA2ind: get_A2_binded_nodes_in_g_path G (u, v, h :: t) = get_A2_binded_nodes_in_g_path G (h, v, t)).
        { apply A2_induction_case.
          - destruct HG as [_ [_ HG]]. apply HG.
          - right. apply Houth. }
        assert (HindA2: is_exact_assignment_for A2' (get_A2_binded_nodes_in_g_path G (u, v, h :: t)) /\ A2_nodes_colliders_in_graph G (u, v, h :: t) A2').
        { repeat split.
          -- unfold nodes. rewrite HA2ind. unfold is_exact_assignment_for in HA2'. destruct HA2' as [HA2' _]. apply HA2'.
          -- (* since h is not a collider, nothing changes from induction case *)
             unfold nodes. rewrite HA2ind. unfold is_exact_assignment_for in HA2'. destruct HA2' as [_ HA2']. apply HA2'.
          -- unfold A2_nodes_colliders_in_graph. intros c i' j' x y Hc. unfold A2_nodes_colliders_in_graph in HA2''.
             specialize HA2'' with (c := c) (i := i') (j := j') (x := x) (y := y). apply HA2'' in Hc. destruct Hc as [a [b Hc]].
             exists a. exists b. repeat split.
             ++ apply Hc.
             ++ apply Hc.
             ++ destruct Hc as [_ [_ [Hc _]]]. apply sublist_breaks_down_list in Hc. simpl in Hc. destruct Hc as [l2 [l3 Hc]].
                apply sublist_breaks_down_list. exists (u :: l2). exists l3. simpl. rewrite Hc. reflexivity.
             ++ apply Hc. }

        destruct (path_into_start (u, v, h :: t) G) as [|] eqn:Hin.
        * (* u <- h -> ... *)
          assert (Hi: exists i: nat, index (find_parents u G) h = Some i).
          { assert (Hh: In h (find_parents u G)).
            { apply edge_from_parent_to_child. simpl in Hin. destruct G as [V E]. simpl. simpl in Hin. apply split_and_true in Hin.
              destruct Hin as [_ Hin]. apply Hin. }
            apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
          destruct Hi as [i Hi].
          assert (Hnodeu: node_in_graph u G = true).
          { apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. simpl in Hp. apply is_edge_then_node_in_graph with (v := h). destruct G as [V E].
            apply split_and_true in Hp. destruct Hp as [Hp _]. apply split_orb_true. apply Hp. }
          assert (HA1ind: get_A1_binded_nodes_in_g_path G (u, v, h :: t) = u :: get_A1_binded_nodes_in_g_path G (h, v, t)).
          { apply A1_induction_into_start.
            - split.
              ** apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
              ** destruct HG as [_ [_ HG]]. apply HG.
            - apply Hin. }

          exists ((u, i) :: A1'). exists A2'. exists A3'.
          repeat split.
          -- (* since arrow into u, u is in A1 *)
             unfold nodes. rewrite HA1ind. simpl. rewrite eqb_refl. simpl. apply is_assignment_for_cat.
             unfold is_exact_assignment_for in HA1'. destruct HA1' as [HA1' _]. apply HA1'.
          -- intros u' Hmemu'. unfold is_exact_assignment_for in HA1'. destruct HA1' as [_ HA1']. simpl.
             assert (Hmemu: In u (get_A1_binded_nodes_in_g_path G (u, v, h :: t))).
             { rewrite HA1ind. left. reflexivity. }
             destruct (u' =? u) as [|] eqn:Huu'.
             ++ apply eqb_eq in Huu'. apply member_In_equiv in Hmemu. rewrite Huu' in Hmemu'. unfold nodes in Hmemu'. rewrite Hmemu in Hmemu'. discriminate Hmemu'.
             ++ simpl. apply HA1'. unfold nodes in Hmemu'. rewrite HA1ind in Hmemu'. unfold member in Hmemu'. rewrite eqb_sym in Hmemu'. rewrite Huu' in Hmemu'. apply Hmemu'.
          -- unfold A1_nodes_binded_to_parent_in_path. intros c i' Hmi'. simpl in Hmi'. destruct Hmi' as [Hmi' | Hmi'].
             ++ inversion Hmi'. rewrite <- H1 in *. rewrite <- H2 in *. exists h. repeat split.
                ** apply index_correct. symmetry. apply Hi.
                ** right. simpl. repeat rewrite eqb_refl. reflexivity.
             ++ unfold A1_nodes_binded_to_parent_in_path in HA1''. specialize HA1'' with (m := c) (i := i'). apply HA1'' in Hmi'.
                destruct Hmi' as [a [Ha Hsub]]. exists a. split.
                ** apply Ha.
                ** destruct Hsub as [Hsub | Hsub].
                   --- left. simpl. simpl in Hsub. rewrite Hsub. rewrite orb_comm. reflexivity.
                   --- right. simpl. simpl in Hsub. rewrite Hsub. rewrite orb_comm. reflexivity.
          -- unfold each_node_assigned_once. intros w Hw. simpl in Hw. apply split_orb_true in Hw. destruct (w =? u) as [|] eqn:Hwu.
             ++ simpl. rewrite eqb_sym in Hwu. rewrite Hwu. simpl. f_equal. destruct (filter (fun x : node * nat => fst x =? w) A1') as [| h1 t1] eqn:H1.
                ** simpl. reflexivity.
                ** exfalso. assert (Hu: In u (get_A1_binded_nodes_in_g_path G (h, v, t))).
                   { assert (Hh1: In h1 (filter (fun x : node * nat => fst x =? w) A1')). { rewrite H1. left. reflexivity. }
                     apply filter_true in Hh1. assert (Hu: is_assigned A1' u = true). { apply is_assigned_membership. destruct h1 as [h11 h12]. exists h12.
                     simpl in Hh1. apply eqb_eq in Hwu. rewrite Hwu. destruct Hh1 as [Hh1 Hh1']. apply eqb_eq in Hh1'. rewrite <- Hh1'. apply Hh1. }
                     destruct (member u (get_A1_binded_nodes_in_g_path G (h, v, t))) as [|] eqn:Humem.
                     - apply member_In_equiv. apply Humem.
                     - apply HA1' in Humem. rewrite Humem in Hu. discriminate Hu. }
                   apply A1_nodes_in_path in Hu. rewrite node_in_path_equiv in Hu. rewrite app_comm_cons in Hu. apply member_In_equiv in Hu.
                   apply membership_append_or in Hu. apply paths_start_to_end_correct in Hp. destruct Hp as [_ [_ Hp]]. destruct Hu as [Hu | [Hu | Hu]].
                   --- destruct Hp as [_ [Hp _]]. apply Hp. apply Hu.
                   --- destruct Hp as [Hp _]. apply Hp. symmetry. apply Hu.
                   --- apply Hu.
             ++ simpl. rewrite eqb_sym in Hwu. rewrite Hwu. apply HA1'''. destruct Hw as [Hw | Hw]. discriminate Hw. apply Hw.
          -- apply HindA2.
          -- apply HindA2.
          -- apply HindA2.
          -- apply HA2D.
          -- unfold get_A2_binded_nodes_in_g_path in HA2ind. simpl. simpl in HA2ind. rewrite HA2ind. apply HA3'.

        * (* u -> h -> ... *)
          assert (Hi: exists i: nat, index (find_parents h G) u = Some i).
          { assert (Hh: In u (find_parents h G)).
            { apply edge_from_parent_to_child. simpl in Hin. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _].
              simpl in Hp. rewrite Hin in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [Hp _]. rewrite orb_comm in Hp.
              simpl in Hp. simpl. apply split_and_true in Hp. apply Hp. }
            apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
          destruct Hi as [i Hi].
          assert (HA1ind: get_A1_binded_nodes_in_g_path G (u, v, h :: t) = h :: get_A1_binded_nodes_in_g_path G (h, v, t)).
          { apply A1_induction_out_of_start_out_of_h.
            - split.
              ** apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
              ** destruct HG as [_ [_ HG]]. apply HG.
            - split.
              ** apply Hin.
              ** apply Houth. }
          assert (HA4ind: exists (A4'': nodes), get_A4_binded_nodes_in_g_path G (u, v, h :: t) = u :: A4'' /\ get_A4_binded_nodes_in_g_path G (h, v, t) = h :: A4'').
          { apply A4_induction_out_of_start_out_of_h.
            - split.
              ** apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
              ** destruct HG as [_ [_ HG]]. apply HG.
            - split. apply Hin. apply Houth. }
          destruct HA4ind as [A4'' HA4ind].

          exists ((h, i) :: A1'). exists A2'. exists A3'.
          repeat split.

          -- (* since arrow into u, u is in A1 *)
             unfold nodes. rewrite HA1ind. simpl. rewrite eqb_refl. simpl. apply is_assignment_for_cat.
             unfold is_exact_assignment_for in HA1'. destruct HA1' as [HA1' _]. apply HA1'.
          -- intros u' Hmemu'. unfold is_exact_assignment_for in HA1'. destruct HA1' as [_ HA1']. simpl.
             assert (Hmemu: In h (get_A1_binded_nodes_in_g_path G (u, v, h :: t))).
             { rewrite HA1ind. left. reflexivity. }
             destruct (u' =? h) as [|] eqn:Huu'.
             ++ apply eqb_eq in Huu'. apply member_In_equiv in Hmemu. rewrite Huu' in Hmemu'. unfold nodes in Hmemu'. rewrite Hmemu in Hmemu'. discriminate Hmemu'.
             ++ simpl. apply HA1'. unfold nodes in Hmemu'. rewrite HA1ind in Hmemu'. unfold member in Hmemu'. rewrite eqb_sym in Hmemu'. rewrite Huu' in Hmemu'. apply Hmemu'.
          -- unfold A1_nodes_binded_to_parent_in_path. intros c i' Hmi'. simpl in Hmi'. destruct Hmi' as [Hmi' | Hmi'].
             ++ inversion Hmi'. rewrite <- H1 in *. rewrite <- H2 in *. exists u. repeat split.
                ** apply index_correct. symmetry. apply Hi.
                ** left. simpl. repeat rewrite eqb_refl. reflexivity.
             ++ unfold A1_nodes_binded_to_parent_in_path in HA1''. specialize HA1'' with (m := c) (i := i'). apply HA1'' in Hmi'.
                destruct Hmi' as [a [Ha Hsub]]. exists a. split.
                ** apply Ha.
                ** destruct Hsub as [Hsub | Hsub].
                   --- left. simpl. simpl in Hsub. rewrite Hsub. rewrite orb_comm. reflexivity.
                   --- right. simpl. simpl in Hsub. rewrite Hsub. rewrite orb_comm. reflexivity.
          -- unfold each_node_assigned_once. intros w Hw. simpl in Hw. apply split_orb_true in Hw. destruct (w =? h) as [|] eqn:Hwu.
             ++ simpl. rewrite eqb_sym in Hwu. rewrite Hwu. simpl. f_equal. destruct (filter (fun x : node * nat => fst x =? w) A1') as [| h1 t1] eqn:H1.
                ** simpl. reflexivity.
                ** exfalso. assert (Hu: In h (get_A1_binded_nodes_in_g_path G (h, v, t))).
                   { assert (Hh1: In h1 (filter (fun x : node * nat => fst x =? w) A1')). { rewrite H1. left. reflexivity. }
                     apply filter_true in Hh1. assert (Hu: is_assigned A1' h = true). { apply is_assigned_membership. destruct h1 as [h11 h12]. exists h12.
                     simpl in Hh1. apply eqb_eq in Hwu. rewrite Hwu. destruct Hh1 as [Hh1 Hh1']. apply eqb_eq in Hh1'. rewrite <- Hh1'. apply Hh1. }
                     destruct (member h (get_A1_binded_nodes_in_g_path G (h, v, t))) as [|] eqn:Humem.
                     - apply member_In_equiv. apply Humem.
                     - apply HA1' in Humem. rewrite Humem in Hu. discriminate Hu. }
                   assert (Hp': is_path_in_graph (h, v, t) G = true). { apply paths_start_to_end_correct in Hp. apply is_path_in_graph_induction with (u := u). apply Hp. }
                   assert (Hcyc: acyclic_path_2 (h, v, t)). { apply paths_start_to_end_correct in Hp. apply acyclic_path_cat with (u := u). apply Hp. }
                   unfold get_A1_binded_nodes_in_g_path in Hu. rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction in Houth.
                   2: { split. apply Hp'. apply HG. }
                   unfold nodes in *. rewrite Houth in Hu. destruct (path_out_of_end (h, v, t) G) as [[|]|].
                   --- apply intermediate_node_in_path with (x := h) in Hp'. assert (Hh: In h t). { apply Hp'. left. apply Hu. }
                       destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. apply Hh.
                   --- apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]].
                       apply intermediate_node_in_path with (x := h) in Hp'. assert (Hh: In h t). { apply Hp'. left. apply Hu. }
                       destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. apply Hh.
                       destruct Hcyc as [Hcyc _]. apply Hcyc. symmetry. apply Hu. apply Hu.
                   --- apply Hu.
             ++ simpl. rewrite eqb_sym in Hwu. rewrite Hwu. apply HA1'''. destruct Hw as [Hw | Hw]. discriminate Hw. apply Hw.

          -- apply HindA2.
          -- apply HindA2.
          -- apply HindA2.
          -- apply HA2D.
          -- unfold get_A2_binded_nodes_in_g_path in HA2ind. simpl. simpl in HA2ind. rewrite HA2ind. apply HA3'.

      + (* since arrow out of h is ->, h cannot be a collider, so h not in Z *)
        apply edge_out_not_in_Z with (u := u) (v := v) (t := t) (G := G). apply Hconn. right. apply Houth. apply paths_start_to_end_correct in Hp. apply Hp.
      + apply subpath_still_d_connected with (u := u). apply Hconn.
      + simpl. apply descendant_paths_disjoint_col_cat with (u := u). apply Hdesc.
      + destruct Hl as [l' [Hl' Hsub]]. exists (h :: t ++ [v]). split. reflexivity.
        apply end_of_sublist_still_sublist_gen with (a := u) (h := hn). rewrite Hl' in Hsub. apply Hsub. }

    destruct (path_into_start (u, v, h :: t) G) as [|] eqn:Hin.
    * (* u <- h <- ... *)
      specialize IH with (u := h) (l := t) (D := D).
      assert (Hp': In (h, v, t) (find_all_paths_from_start_to_end h v G)).
      { apply paths_start_to_end_correct in Hp. apply paths_start_to_end_correct. split.
        - apply is_path_in_graph_induction with (u := u). apply Hp.
        - split. apply path_start_end_refl. apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity. apply Hp. }
      pose proof Hp' as Hpind. apply IH in Hp'. clear IH.

      + destruct Hp' as [A1' [A2' [A3' HA12]]]. destruct HA12 as [HA1' [HA1'' [HA1''' [HA2' [HA2'' [HA2D HA3']]]]]].
        assert (Hi: exists i: nat, index (find_parents u G) h = Some i).
        { assert (Hh: In h (find_parents u G)).
          { simpl in Hin. apply edge_from_parent_to_child. unfold is_edge in Hin. destruct G as [V E]. simpl. apply split_and_true in Hin. apply Hin. }
          apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
        destruct Hi as [i Hi].

        assert (HA1ind: get_A1_binded_nodes_in_g_path G (u, v, h :: t) = u :: get_A1_binded_nodes_in_g_path G (h, v, t)).
        { apply A1_induction_into_start.
          - split.
            ** apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
            ** destruct HG as [_ [_ HG]]. apply HG.
          - apply Hin. }
        assert (HA2ind: get_A2_binded_nodes_in_g_path G (u, v, h :: t) = get_A2_binded_nodes_in_g_path G (h, v, t)).
        { apply A2_induction_case.
          - destruct HG as [_ [_ HG]]. apply HG.
          - left. apply Hin. }
        assert (HindA2: is_exact_assignment_for A2' (get_A2_binded_nodes_in_g_path G (u, v, h :: t)) /\ A2_nodes_colliders_in_graph G (u, v, h :: t) A2').
        { repeat split.
          -- unfold nodes. rewrite HA2ind. unfold is_exact_assignment_for in HA2'. destruct HA2' as [HA2' _]. apply HA2'.
          -- (* since h is not a collider, nothing changes from induction case *)
             unfold nodes. rewrite HA2ind. unfold is_exact_assignment_for in HA2'. destruct HA2' as [_ HA2']. apply HA2'.
          -- unfold A2_nodes_colliders_in_graph. intros c i' j' x y Hc. unfold A2_nodes_colliders_in_graph in HA2''.
             specialize HA2'' with (c := c) (i := i') (j := j') (x := x) (y := y). apply HA2'' in Hc. destruct Hc as [a [b Hc]].
             exists a. exists b. repeat split.
             ++ apply Hc.
             ++ apply Hc.
             ++ destruct Hc as [_ [_ [Hc _]]]. apply sublist_breaks_down_list in Hc. simpl in Hc. destruct Hc as [l2 [l3 Hc]].
                apply sublist_breaks_down_list. exists (u :: l2). exists l3. simpl. rewrite Hc. reflexivity.
             ++ apply Hc. }

        exists ((u, i) :: A1'). exists A2'. exists A3'. repeat split.

        -- (* since arrow into u, u is in A1 *)
           unfold nodes. rewrite HA1ind. simpl. rewrite eqb_refl. simpl. apply is_assignment_for_cat.
           unfold is_exact_assignment_for in HA1'. destruct HA1' as [HA1' _]. apply HA1'.
        -- intros u' Hmemu'. unfold is_exact_assignment_for in HA1'. destruct HA1' as [_ HA1']. simpl.
           assert (Hmemu: In u (get_A1_binded_nodes_in_g_path G (u, v, h :: t))).
           { rewrite HA1ind. left. reflexivity. }
           destruct (u' =? u) as [|] eqn:Huu'.
           ++ apply eqb_eq in Huu'. apply member_In_equiv in Hmemu. rewrite Huu' in Hmemu'. unfold nodes in Hmemu'. rewrite Hmemu in Hmemu'. discriminate Hmemu'.
           ++ simpl. apply HA1'. unfold nodes in Hmemu'. rewrite HA1ind in Hmemu'. unfold member in Hmemu'. rewrite eqb_sym in Hmemu'. rewrite Huu' in Hmemu'. apply Hmemu'.
        -- unfold A1_nodes_binded_to_parent_in_path. intros c i' Hmi'. simpl in Hmi'. destruct Hmi' as [Hmi' | Hmi'].
           ++ inversion Hmi'. rewrite <- H1 in *. rewrite <- H2 in *. exists h. repeat split.
              ** apply index_correct. symmetry. apply Hi.
              ** right. simpl. repeat rewrite eqb_refl. reflexivity.
           ++ unfold A1_nodes_binded_to_parent_in_path in HA1''. specialize HA1'' with (m := c) (i := i'). apply HA1'' in Hmi'.
              destruct Hmi' as [a [Ha Hsub]]. exists a. split.
              ** apply Ha.
              ** destruct Hsub as [Hsub | Hsub].
                 --- left. simpl. simpl in Hsub. rewrite Hsub. rewrite orb_comm. reflexivity.
                 --- right. simpl. simpl in Hsub. rewrite Hsub. rewrite orb_comm. reflexivity.
        -- unfold each_node_assigned_once. intros w Hw. simpl in Hw. apply split_orb_true in Hw. destruct (w =? u) as [|] eqn:Hwu.
           ++ simpl. rewrite eqb_sym in Hwu. rewrite Hwu. simpl. f_equal. destruct (filter (fun x : node * nat => fst x =? w) A1') as [| h1 t1] eqn:H1.
              ** simpl. reflexivity.
              ** exfalso. assert (Hu: In u (get_A1_binded_nodes_in_g_path G (h, v, t))).
                 { assert (Hh1: In h1 (filter (fun x : node * nat => fst x =? w) A1')). { rewrite H1. left. reflexivity. }
                   apply filter_true in Hh1. assert (Hu: is_assigned A1' u = true). { apply is_assigned_membership. destruct h1 as [h11 h12]. exists h12.
                   simpl in Hh1. apply eqb_eq in Hwu. rewrite Hwu. destruct Hh1 as [Hh1 Hh1']. apply eqb_eq in Hh1'. rewrite <- Hh1'. apply Hh1. }
                   destruct (member u (get_A1_binded_nodes_in_g_path G (h, v, t))) as [|] eqn:Humem.
                   - apply member_In_equiv. apply Humem.
                   - apply HA1' in Humem. rewrite Humem in Hu. discriminate Hu. }
                 apply A1_nodes_in_path in Hu. rewrite node_in_path_equiv in Hu. rewrite app_comm_cons in Hu. apply member_In_equiv in Hu.
                 apply membership_append_or in Hu. apply paths_start_to_end_correct in Hp. destruct Hp as [_ [_ Hp]]. destruct Hu as [Hu | [Hu | Hu]].
                 --- destruct Hp as [_ [Hp _]]. apply Hp. apply Hu.
                 --- destruct Hp as [Hp _]. apply Hp. symmetry. apply Hu.
                 --- apply Hu.
           ++ simpl. rewrite eqb_sym in Hwu. rewrite Hwu. apply HA1'''. destruct Hw as [Hw | Hw]. discriminate Hw. apply Hw.
        -- apply HindA2.
        -- apply HindA2.
        -- apply HindA2.
        -- apply HA2D.
        -- unfold get_A2_binded_nodes_in_g_path in HA2ind. simpl. simpl in HA2ind. rewrite HA2ind. apply HA3'.

      + (* path is u <- h, so h cannot be a collider. Thus, h not in Z *) apply edge_out_not_in_Z with (u := u) (v := v) (t := t) (G := G). apply Hconn.
        left. apply Hin. apply paths_start_to_end_correct in Hp. apply Hp.
      + apply subpath_still_d_connected with (u := u). apply Hconn.
      + simpl. apply descendant_paths_disjoint_col_cat with (u := u). apply Hdesc.
      + exists (h :: t ++ [v]). split. reflexivity. apply end_of_sublist_still_sublist_gen with (a := u) (h := hn).
        destruct Hl as [l' [Hl' Hsub]]. rewrite Hl' in Hsub. apply Hsub.

    * (* u -> h <- ... *)
      unfold generic_graph_and_type_properties_hold in HG. destruct HG as [[X1 [X2 HX]] HG].
      destruct t as [| h' t'].
      + (* u -> h <- v *)
        assert (Huh: is_edge (u, h) G = true).
        { simpl in Hin. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. simpl in Hp. rewrite Hin in Hp. rewrite orb_comm in Hp. simpl in Hp.
          destruct G as [V E]. apply split_and_true in Hp. apply Hp. }
        assert (Hhv: is_edge (v, h) G = true).
        { simpl in Houth. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. simpl in Hp. rewrite Houth in Hp. simpl in Hp.
          destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. rewrite andb_comm in Hp. simpl in Hp. apply Hp. }

        assert (Hi: exists i: nat, index (find_parents h G) u = Some i).
        { assert (Hh: In u (find_parents h G)).
          { apply edge_from_parent_to_child. unfold is_edge in Huh. destruct G as [V E]. simpl. apply split_and_true in Huh. apply Huh. }
          apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
        destruct Hi as [iu Hiu].
        assert (Hi: exists i: nat, index (find_parents h G) v = Some i).
        { assert (Hh: In v (find_parents h G)).
          { apply edge_from_parent_to_child. unfold is_edge in Hhv. destruct G as [V E]. simpl. apply split_and_true in Hhv. apply Hhv. }
          apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
        destruct Hi as [iv Hiv].

        assert (Hhcol: exists (p: nodes) (d: node) (xd: X), get_assigned_value D h = Some (p, d) /\ get_assigned_value AZ d = Some xd).
        { assert (Hhcol: In h (find_colliders_in_path (u, v, path_int (u, v, [h])) G)). { simpl. unfold is_collider_bool. rewrite Huh. rewrite Hhv. simpl. left. reflexivity. }
          apply Hdesc in Hhcol. destruct Hhcol as [Hhcol | Hhcol].
          - exists []. exists h.
            assert (HhZ: exists (xh: X), get_assigned_value AZ h = Some xh). { apply assigned_has_value with (L := Z). split. apply Hhcol. apply HAZ. }
            destruct HhZ as [xh HhZ]. exists xh. split. apply Hhcol. apply HhZ.
          - destruct Hhcol as [ph [dh Hhcol]]. exists ph. exists dh.
            assert (HhZ: exists (xh: X), get_assigned_value AZ dh = Some xh). { apply assigned_has_value with (L := Z). split. apply Hhcol. apply HAZ. }
            destruct HhZ as [xh HhZ]. exists xh. split. apply Hhcol. apply HhZ. }
        destruct Hhcol as [ph [dh [xh Hhcol]]].
        assert (Hxh: exists (yh: X), xh <> yh). { destruct (eqb xh X1) as [|] eqn:Hxh. exists X2. intros Hxh'. rewrite Hxh' in Hxh. apply HX. apply eqb_eq'. rewrite eqb_sym'. apply Hxh.
          exists X1. intros Hxh'. rewrite Hxh' in Hxh. rewrite eqb_refl' in Hxh. discriminate Hxh. }
        destruct Hxh as [yh Hxh].

        exists []. exists [(h, (iu, iv, xh, yh))].

        assert (HA3: exists (A3: assignments nat), get_A3_assignments_for_desc_paths D G
                      (find_colliders_in_path (u, v, path_int (u, v, [h])) G) = Some A3). { apply A3_nodes_existence with (Z := Z). apply Hdesc. }
        destruct HA3 as [A3 HA3]. exists A3.

        repeat split.
        -- simpl. rewrite Hhv. simpl in Hin. rewrite Hin. unfold is_mediator_bool. simpl in Houth. rewrite Houth. rewrite Hin. rewrite andb_comm. simpl.
           rewrite andb_comm. simpl. reflexivity.
        -- unfold A1_nodes_binded_to_parent_in_path. intros m i F. exfalso. apply F.
        -- unfold each_node_assigned_once. intros w Hw. simpl in Hw. discriminate Hw.
        -- simpl. unfold is_collider_bool. rewrite Huh. rewrite Hhv. simpl. rewrite eqb_refl. simpl. reflexivity.
        -- intros w Hw. simpl. rewrite orb_comm. simpl. simpl in Hw. unfold is_collider_bool in Hw. rewrite Huh in Hw. rewrite Hhv in Hw. simpl in Hw.
           destruct (h =? w) as [|] eqn:Hhw. discriminate Hw. rewrite eqb_sym. apply Hhw.
        -- unfold A2_nodes_colliders_in_graph. intros c i j x' y' Hc. exists u. exists v. simpl in Hc. inversion Hc. inversion H0. repeat split.
           ++ rewrite <- H2. rewrite <- H3. apply index_correct. symmetry. apply Hiu.
           ++ rewrite <- H2. rewrite <- H4. apply index_correct. symmetry. apply Hiv.
           ++ simpl. repeat rewrite eqb_refl. reflexivity.
           ++ unfold is_collider_bool. rewrite <- H2. rewrite Huh. rewrite Hhv. reflexivity.
           ++ exfalso. apply H0.
        -- unfold A2_consistent_with_D. intros c i j x' y' Hc. simpl in Hc. destruct (h =? c) as [|] eqn:Hhc. inversion Hc. exists ph. exists dh. split. apply eqb_eq in Hhc. rewrite <- Hhc. apply Hhcol.
           split. rewrite <- H3. apply Hhcol. rewrite <- H3. rewrite <- H4. apply Hxh. discriminate Hc.
        -- apply HA3.

      + (* u -> h <- h' ... t'... v *)
        assert (Huh: is_edge (u, h) G = true).
        { simpl in Hin. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. simpl in Hp. rewrite Hin in Hp. rewrite orb_comm in Hp. simpl in Hp.
          destruct G as [V E]. apply split_and_true in Hp. apply Hp. }
        assert (Hhv: is_edge (h', h) G = true).
        { simpl in Houth. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. simpl in Hp. rewrite Houth in Hp. simpl in Hp.
          destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. apply split_and_true in Hp. apply Hp. }

        assert (Hcoluv: find_colliders_in_path (u, v, h :: h' :: t') G = h :: find_colliders_in_path (h', v, t') G).
        { simpl. unfold is_collider_bool. rewrite Huh. rewrite Hhv. simpl. f_equal. destruct t' as [| h'' t''].
          - simpl. simpl in Houth. rewrite Houth. simpl. reflexivity.
          - simpl. simpl in Houth. rewrite Houth. simpl. reflexivity. }

        specialize IH with (u := h') (l := t') (D := D).
        assert (Hp': In (h', v, t') (find_all_paths_from_start_to_end h' v G)).
        { apply paths_start_to_end_correct in Hp. apply paths_start_to_end_correct. split.
          - apply is_path_in_graph_induction with (u := h). apply is_path_in_graph_induction with (u := u). apply Hp.
          - split. apply path_start_end_refl. apply subpath_still_acyclic with (w := u) (l1 := [h]) (l3 := h :: h' :: t'). split. reflexivity. apply Hp. }
        pose proof Hp' as Hpind. apply IH in Hp'. clear IH.

        { destruct Hp' as [A1' [A2' [A3' Hind]]]. exists A1'.
          assert (Hi: exists i: nat, index (find_parents h G) u = Some i).
          { assert (Hh: In u (find_parents h G)).
            { apply edge_from_parent_to_child. unfold is_edge in Huh. destruct G as [V E]. simpl. apply split_and_true in Huh. apply Huh. }
            apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
          destruct Hi as [iu Hiu].
          assert (Hi: exists i: nat, index (find_parents h G) h' = Some i).
          { assert (Hh: In h' (find_parents h G)).
            { apply edge_from_parent_to_child. unfold is_edge in Hhv. destruct G as [V E]. simpl. apply split_and_true in Hhv. apply Hhv. }
            apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
          destruct Hi as [iv Hiv].
          assert (HA1ind: is_exact_assignment_for A1'
                             (get_A1_binded_nodes_in_g_path G (u, v, h :: h' :: t')) /\
                           A1_nodes_binded_to_parent_in_path G (u, v, h :: h' :: t') A1' /\ each_node_assigned_once A1').
          { repeat split.
            - rewrite A1_induction_add_collider. apply Hind. split. apply paths_start_to_end_correct in Hp. apply Hp. apply HG.
              split. apply Hin. apply Houth.
            - rewrite A1_induction_add_collider. apply Hind. split. apply paths_start_to_end_correct in Hp. apply Hp. apply HG.
              split. apply Hin. apply Houth.
            - unfold A1_nodes_binded_to_parent_in_path. intros m i Hmi. destruct Hind as [_ [Hind _]]. apply Hind in Hmi.
              destruct Hmi as [a Hmi]. exists a. split. apply Hmi. destruct Hmi as [_ [Hmi | Hmi]].
              -- left. apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hmi. destruct Hmi as [l2 [l3 Hmi]]. exists (u :: h :: l2). exists l3.
                 simpl. simpl in Hmi. rewrite <- Hmi. reflexivity.
              -- right. apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hmi. destruct Hmi as [l2 [l3 Hmi]]. exists (u :: h :: l2). exists l3.
                 simpl. simpl in Hmi. rewrite <- Hmi. reflexivity. 
            - apply Hind. }

          assert (HA2ind: forall (xh y: X), is_exact_assignment_for ((h, (iu, iv, xh, y)) :: A2')
                                (get_A2_binded_nodes_in_g_path G (u, v, h :: h' :: t')) /\
                              A2_nodes_colliders_in_graph G (u, v, h :: h' :: t')
                                ((h, (iu, iv, xh, y)) :: A2')).
          { intros xh' y. repeat split.
            - unfold get_A2_binded_nodes_in_g_path. unfold nodes in *. rewrite Hcoluv. simpl. rewrite eqb_refl. simpl. apply is_assignment_for_cat.
              destruct Hind as [_ [_ [_ [Hind _]]]]. unfold get_A2_binded_nodes_in_g_path in Hind. simpl in Hind. apply Hind.
            - intros w Hw. simpl. unfold get_A2_binded_nodes_in_g_path in Hw. unfold nodes in *. rewrite Hcoluv in Hw. destruct (w =? h) as [|] eqn:Hwh.
              simpl in Hw. rewrite eqb_sym in Hwh. rewrite Hwh in Hw. discriminate Hw. simpl. apply Hind. simpl in Hw. rewrite eqb_sym in Hwh. rewrite Hwh in Hw. apply Hw.
            - unfold A2_nodes_colliders_in_graph. intros c i j x' y' Hc. destruct Hc as [Hc | Hc].
              { exists u. exists h'. inversion Hc. repeat split.
                -- rewrite <- H1. rewrite <- H2. apply index_correct. symmetry. apply Hiu.
                -- rewrite <- H1. rewrite <- H3. apply index_correct. symmetry. apply Hiv.
                -- simpl. repeat rewrite eqb_refl. simpl. reflexivity.
                -- unfold is_collider_bool. rewrite <- H1. rewrite Huh. rewrite Hhv. reflexivity. }
              { destruct Hind as [_ [_ [_ [_ [Hind _]]]]]. apply Hind in Hc. destruct Hc as [a [b Hc]]. exists a. exists b. repeat split.
                -- apply Hc.
                -- apply Hc.
                -- destruct Hc as [_ [_ [Hc _]]]. apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hc. destruct Hc as [l2 [l3 Hc]].
                   exists (u :: h :: l2). exists l3. simpl. simpl in Hc. rewrite <- Hc. reflexivity.
                -- apply Hc. } }

          assert (Hhcol: exists (p: nodes) (d: node) (xd: X), get_assigned_value D h = Some (p, d) /\ get_assigned_value AZ d = Some xd).
          { assert (Hhcol: In h (find_colliders_in_path (u, v, path_int (u, v, h :: h' :: t')) G)). { simpl. unfold is_collider_bool. rewrite Huh. rewrite Hhv. simpl. left. reflexivity. }
            apply Hdesc in Hhcol. destruct Hhcol as [Hhcol | Hhcol].
            - exists []. exists h.
              assert (HhZ: exists (xh: X), get_assigned_value AZ h = Some xh). { apply assigned_has_value with (L := Z). split. apply Hhcol. apply HAZ. }
              destruct HhZ as [xh HhZ]. exists xh. split. apply Hhcol. apply HhZ.
            - destruct Hhcol as [ph [dh Hhcol]]. exists ph. exists dh.
              assert (HhZ: exists (xh: X), get_assigned_value AZ dh = Some xh). { apply assigned_has_value with (L := Z). split. apply Hhcol. apply HAZ. }
              destruct HhZ as [xh HhZ]. exists xh. split. apply Hhcol. apply HhZ. }
          destruct Hhcol as [ph [dh [xh Hhcol]]].
          assert (Hxh: exists (yh: X), xh <> yh). { destruct (eqb xh X1) as [|] eqn:Hxh. exists X2. intros Hxh'. rewrite Hxh' in Hxh. apply HX. apply eqb_eq'. rewrite eqb_sym'. apply Hxh.
            exists X1. intros Hxh'. rewrite Hxh' in Hxh. rewrite eqb_refl' in Hxh. discriminate Hxh. }
          destruct Hxh as [yh Hxh].

          exists ((h, (iu, iv, xh, yh)) :: A2').
          assert (HA3: exists (A3: assignments nat), get_A3_assignments_for_desc_paths D G (find_colliders_in_path (u, v, h :: h' :: t') G) = Some A3).
          { apply A3_nodes_existence with (Z := Z). apply Hdesc. }
          destruct HA3 as [A3 HA3]. exists A3.

          rewrite <- and_assoc. rewrite <- and_assoc. split. repeat split; apply HA1ind. rewrite <- and_assoc. split. apply HA2ind. split. 2: { apply HA3. }
          unfold A2_consistent_with_D. intros c i j x' y' Hc. simpl in Hc. destruct (h =? c) as [|] eqn:Hhc.
          - inversion Hc. exists ph. exists dh. split. apply eqb_eq in Hhc. rewrite <- Hhc. apply Hhcol. rewrite <- H3. split. apply Hhcol. rewrite <- H4. apply Hxh.
          - destruct Hind as [_ [_ [_ [_ [_ [Hind _]]]]]]. unfold A2_consistent_with_D in Hind. apply Hind with (iw := i) (jw := j). apply Hc. }


        { (* u -> h <- h', so h' not a collider *)
          apply edge_out_not_in_Z with (u := h) (v := v) (t := t') (G := G). apply subpath_still_d_connected with (u := u). apply Hconn. left. simpl. apply Hhv.
          apply is_path_in_graph_induction with (u := u). apply paths_start_to_end_correct in Hp. apply Hp. }
        { apply subpath_still_d_connected_gen with (w := u) (l1 := [h]) (l3 := h :: h' :: t'). split. reflexivity. apply Hconn. }
        { apply descendant_paths_disjoint_col_cat with (u := h). apply descendant_paths_disjoint_col_cat with (u := u). apply Hdesc. }
        { exists (h' :: t' ++ [v]). split. reflexivity. destruct Hl as [l' [Hl' Hsub]]. rewrite Hl' in Hsub. apply end_of_sublist_still_sublist_gen in Hsub.
          apply sublist_breaks_down_list in Hsub. destruct Hsub as [l2 [l3 Hsub]]. apply sublist_breaks_down_list. exists (l2 ++ [h]). exists l3.
          rewrite <- app_assoc. apply Hsub. }
Qed.


(* using g_path and specific values for A1, A2, A3, A4, A5, for a d-connected path betw u and v, provide a graphfun
   that requires all non-collider node values along the path (and importantly, f(v) and f(u)), to be equal *)
Lemma path_d_connected_then_can_equate_values'' {X : Type} `{EqType X}: forall (G: graph) (u v: node) (p: path)
  (D: assignments (nodes * node)),
  generic_graph_and_type_properties_hold X G /\ In p (find_all_paths_from_start_to_end u v G) ->
  forall (Z: nodes) (AZ: assignments X), ~(In u Z) /\ ~(In v Z) -> is_exact_assignment_for AZ Z -> descendant_paths_disjoint D u v (path_int p) G Z -> d_connected_2 p G Z
  -> exists (A1: assignments nat) (A2: assignments (nat * nat * X * X)) (A3: assignments nat),
     is_exact_assignment_for A1 (get_A1_binded_nodes_in_g_path G p) /\ A1_nodes_binded_to_parent_in_path G p A1 /\ each_node_assigned_once A1
     /\ is_exact_assignment_for A2 (get_A2_binded_nodes_in_g_path G p) /\ A2_nodes_colliders_in_graph G p A2 /\ A2_consistent_with_D D A2 AZ
     /\ get_A3_assignments_for_desc_paths D G (find_colliders_in_path (u, v, path_int p) G) = Some A3
     /\ forall (A4: assignments X), is_exact_assignment_for A4 (get_A4_binded_nodes_in_g_path G p)
        -> forall (A5: assignments (nodefun X)) (default: nodefun X) (x: X),
           exists (U: assignments X) (xX: X),
              is_assignment_for U (nodes_in_graph G) = true (*  /\ get_values G (g_path'' X A1 A2 A3 A4 AZ A5 default) U [] = Some A *)
              /\ (unobs_conditions_on_Z G (g_path'' X A1 A2 A3 A4 AZ A5 default) U AZ Z
                  /\ (forall (w: node), node_in_path w p = true /\ ~(In w (find_colliders_in_path p G))
                             -> find_value G (g_path'' X A1 A2 A3 A4 AZ A5 default) w U [] = Some xX) /\ xX <> x
                  /\ forall (Ux: assignments X) (LUx: list (assignments X)),
                     (assignments_equiv Ux ((hd 0 (get_A4_binded_nodes_in_g_path G p), x) :: U))
                     /\ (list_assignments_equiv LUx (tl (get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G p) U x)))
                     (* Ux = (hd 0 (get_A4_binded_nodes_in_g_path G p), x) :: U /\ tl (get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G p) U x) = LUx *)
                    -> find_value G (g_path'' X A1 A2 A3 A4 AZ A5 default) u Ux [] = Some x /\ length LUx <= path_length p
                         /\ sequence_of_ancestors_change_for_Z U Ux LUx G Z AZ u v (path_int p)
                         /\ unobs_conditions_on_Z G (g_path'' X A1 A2 A3 A4 AZ A5 default) (last (Ux :: LUx) Ux) AZ Z
                         /\ (forall (w: node), node_in_path w p = true /\ ~(In w (find_colliders_in_path p G))
                             -> find_value G (g_path'' X A1 A2 A3 A4 AZ A5 default) w (last (Ux :: LUx) Ux) [] = Some x)).
Proof.
  intros G u v p D [HG Hp]. intros Z AZ [HuZ HvZ] HAZ Hdesc Hconn.

  assert (Hpath: exists (l: nodes), p = (u, v, l)).
  { destruct p as [[u' v'] l]. apply paths_start_to_end_correct in Hp. destruct Hp as [_ [Hp _]].
    apply path_start_end_equal in Hp. destruct Hp as [Huu' Hvv']. exists l. rewrite Huu'. rewrite Hvv'. reflexivity. }
  destruct Hpath as [l Hpath]. rewrite Hpath in *. clear Hpath.

  assert (Hlem: exists
                (A1 : assignments nat) (A2 : assignments (nat * nat * X * X)) 
              (A3 : assignments nat),
                is_exact_assignment_for A1 (get_A1_binded_nodes_in_g_path G (u, v, l)) /\
                A1_nodes_binded_to_parent_in_path G (u, v, l) A1 /\
                each_node_assigned_once A1 /\
                is_exact_assignment_for A2 (get_A2_binded_nodes_in_g_path G (u, v, l)) /\
                A2_nodes_colliders_in_graph G (u, v, l) A2 /\
                A2_consistent_with_D D A2 AZ /\
                get_A3_assignments_for_desc_paths D G
                  (find_colliders_in_path (u, v, path_int (u, v, l)) G) = Some A3).
  { apply define_sets_for_equating_values_on_d_connected_path with (Z := Z). split. apply HG. apply Hp. split. apply HuZ. apply HvZ. apply HAZ.
    apply Hconn. destruct Hdesc as [_ Hdesc]. simpl. unfold descendant_paths_disjoint_col. apply Hdesc. }

  destruct Hlem as [A1 [A2 [A3 Hlem]]]. exists A1. exists A2. exists A3.
  rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split.
  repeat split; apply Hlem.
  pose proof Hlem as Hexist. clear Hlem.

  intros A4 HA4 A5 default.

  apply paths_start_to_end_correct in Hp.

  assert (Hi'': forall (g: graphfun) (iw: nat) (a w: node) (unobs' xa: X) (pa: list X) (P U: assignments X),
                      node_in_graph a G = true
                      -> is_assignment_for U (nodes_in_graph G) = true
                      -> nth_error (find_parents w G) iw = Some a
                      -> Some pa = get_parent_assignments P (find_parents w G) /\ find_values G g (find_parents w G) U [] = Some P
                      -> find_value G g a U [] = Some xa
                      -> nth_default unobs' pa iw = xa).
  { intros g i' a w' un xa Pa P1 U Hnodea HU Hi' Hpa Ha.
    assert (Hxa': get_assigned_value P1 a = Some xa).
     { apply find_values_get_assigned with (G := G) (g := g) (P := find_parents w' G) (U := U) (A := []). repeat split.
       - apply Hpa.
       - apply nth_error_In with (n := i'). apply Hi'.
       - apply Ha. }
     assert (Hiw: nth_error Pa i' = get_assigned_value P1 a).
     { rewrite Hxa'. apply parent_assignments_preserves_index with (P := P1) (V := find_parents w' G) (m := a). repeat split.
       - symmetry. apply Hpa.
       - symmetry. apply index_correct_appears_once.
         + apply each_parent_appears_once. apply HG. apply nth_error_In with (n := i'). apply Hi'.
         + apply Hi'.
       - apply Hxa'. }
     unfold nth_default. rewrite Hiw. rewrite Hxa'. reflexivity. }
  remember (g_path'' X A1 A2 A3 A4 AZ A5 default) as g.

  assert (HA4_const: forall (U: assignments X) (w: node) (x: X), is_assigned A4 w = true
                      -> is_assignment_for U (nodes_in_graph G) = true
                      -> get_assigned_value U w = Some x
                      -> find_value G g w U [] = Some x).
  { intros U w x' HA4w HU HeqU.
    assert (HA4w': In w (get_A4_binded_nodes_in_g_path G (u, v, l))).
    { apply assigned_true_then_in_list with (A := A4). split. apply HA4w. apply HA4. }
    assert (Hw': exists (P: assignments X), find_values G g (find_parents w G) U [] = Some P
         /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
         /\ exists (unobs: X), get_assigned_value U w = Some unobs
         /\ find_value G g w U [] = Some (g w (unobs, pa))).
    { apply find_value_evaluates_to_g. split.
      - apply HG.
      - split. apply HU. apply A4_nodes_in_graph with (u := u) (v := v) (l := l). apply HG. apply Hp.
         apply HA4w'. }
    destruct Hw' as [Px [HPx [pax [Hparx [unobsx [HxU Hx]]]]]]. rewrite Hx.
    rewrite Heqg. unfold g_path''.

    assert (HA1w: get_assigned_value A1 w = None).
    { apply A4_nodes_not_in_A1 in HA4w'. apply assigned_is_false. apply Hexist. apply member_In_equiv_F. apply HA4w'. apply HG. apply Hp. apply Hp. }
    rewrite HA1w.
    assert (HA2w: get_assigned_value A2 w = None).
    { apply A4_nodes_not_in_A2 in HA4w'. apply assigned_is_false. apply Hexist. apply member_In_equiv_F. apply HA4w'. apply HG. apply Hp. apply Hp. }
    rewrite HA2w.
    assert (HA3w: get_assigned_value A3 w = None).
    { apply descendant_paths_disjoint_with_A4 with (D := D) (u := u) (v := v) (l := l) (G := G) (Z := Z). apply Hdesc. apply Hexist. apply HA4w'. }
    rewrite HA3w.
    assert (HA4w'': exists (xA4: X), get_assigned_value A4 w = Some xA4).
    { apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (u, v, l)). split. apply HA4w'. apply HA4. }
    destruct HA4w'' as [xA4 HA4w'']. rewrite HA4w''. unfold f_unobs. simpl.
    rewrite <- HxU. apply HeqU. }

  assert (Hw: (forall (w : node) (U: assignments X) (x: X),
                    is_assignment_for U (nodes_in_graph G) = true
                    -> (forall (u4: node), is_assigned A4 u4 = true -> get_assigned_value U u4 = Some x)
                    -> node_in_path w (u, v, l) = true /\ ~ In w (find_colliders_in_path (u, v, l) G)
                    -> find_value G g w U [] = Some x)).
  { (* show that all nodes in A1 evaluate to x (since they are tied to their parents, which becomes a chain that
       must eventually end at a node in A4) *)
    intros w' U x HU Hu4.

    assert (HaU: forall (a: node), is_assigned A4 a = true -> get_assigned_value U a = Some x).
    { intros a Ha. apply Hu4. apply Ha. }

    assert (HuA4: is_assigned A4 u = true \/ is_assigned A1 u = true).
    { destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
      + right. apply assigned_is_true. apply assigned_has_value with (L := get_A1_binded_nodes_in_g_path G (u, v, l)). split. 2: { apply Hexist. }
        unfold get_A1_binded_nodes_in_g_path. rewrite Hin. destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
        left. reflexivity. left. reflexivity. apply path_out_of_end_Some in Hout. exfalso. apply Hout.
      + left. apply assigned_is_true. apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (u, v, l)). split. 2: { apply HA4. }
        unfold get_A4_binded_nodes_in_g_path. rewrite Hin. destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
        left. reflexivity. left. reflexivity. apply path_out_of_end_Some in Hout. exfalso. apply Hout. }

    assert (HvA4: is_assigned A4 v = true \/ is_assigned A1 v = true).
    { destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
      + left. apply assigned_is_true. apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (u, v, l)). split. 2: { apply HA4. }
        unfold get_A4_binded_nodes_in_g_path. rewrite Hout. destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
        apply membership_append_r. left. reflexivity. right. apply membership_append_r. left. reflexivity.
      + right. apply assigned_is_true. apply assigned_has_value with (L := get_A1_binded_nodes_in_g_path G (u, v, l)). split. 2: { apply Hexist. }
        unfold get_A1_binded_nodes_in_g_path. rewrite Hout. destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
        right. apply membership_append_r. left. reflexivity. apply membership_append_r. left. reflexivity.
      + apply path_out_of_end_Some in Hout. exfalso. apply Hout. }

    assert (HA1_const: forall (w: node), is_assigned A1 w = true -> find_value G g w U [] = Some x).
    { intros w HA1w. destruct Hexist as [HA1 [HA1' [HA2 [HA2' HA3]]]].

       assert (Hwmem: In w (u :: l ++ [v])). { apply member_In_equiv. rewrite <- node_in_path_equiv. apply A1_nodes_in_path with (G := G).
       apply member_In_equiv. destruct (member w (get_A1_binded_nodes_in_g_path G (u, v, l))) as [|] eqn:Hwmem.
       - reflexivity.
       - apply HA1 in Hwmem. rewrite HA1w in Hwmem. discriminate Hwmem. }

       pose proof HA1w as HA1w'.
       apply assigned_is_true in HA1w'. destruct HA1w' as [iw HA1w']. pose proof HA1w' as Hiw. apply get_assigned_In in HA1w'.
       unfold A1_nodes_binded_to_parent_in_path in HA1'. pose proof HA1' as HA1bind. specialize HA1' with (m := w) (i := iw).
       apply HA1' in HA1w'. destruct HA1w' as [a [Haxix Haxsub]]. destruct Haxsub as [Haxsub | Haxsub].
       - apply index_exists in Hwmem. destruct Hwmem as [iwp Hiwp].
         clear Hconn. clear HA2'. clear HA1'.
         generalize dependent a. generalize dependent w. generalize dependent iw. induction iwp as [| iwp' IH].
         + intros iw w HA1w Hiwp Hiw a Haxix Haxsub.
           assert (Huw: u = w). { apply index_correct in Hiwp. simpl in Hiwp. inversion Hiwp. reflexivity. } rewrite <- Huw in *.

           assert (Hu: In u (l ++ [v])). { apply middle_elt_of_sublist_not_first_elt_gen with (A := [u]) (a := a) (h := u). split. apply Haxsub. left. reflexivity. }
           exfalso. apply membership_append_or in Hu. destruct Hp as [_ [_ Hcyc]].
           destruct Hu as [Hu | Hu]. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. apply Hu.
           destruct Hu as [Hu | Hu]. destruct Hcyc as [Hcyc _]. apply Hcyc. symmetry. apply Hu. apply Hu.
         + intros iw w HA1w Hiwp Hiw a Haxix Haxsub.

           assert (HA1w': In w (get_A1_binded_nodes_in_g_path G (u, v, l))).
           { apply assigned_true_then_in_list with (A := A1). split. apply HA1w. apply HA1. }

           assert (Hw': exists (P: assignments X), find_values G g (find_parents w G) U [] = Some P
                /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                /\ exists (unobs: X), get_assigned_value U w = Some unobs
                /\ find_value G g w U [] = Some (g w (unobs, pa))).
           { apply find_value_evaluates_to_g. split.
             - apply HG.
             - split. apply HU. apply A1_nodes_in_graph with (u := u) (v := v) (l := l). apply HG. apply Hp.
               apply HA1w'. }
           destruct Hw' as [Px [HPx [pax [Hparx [unobsx [HxU Hx]]]]]]. rewrite Hx.
           rewrite Heqg. unfold g_path''. rewrite Hiw. unfold f_parent_i. simpl.

           f_equal. apply Hi'' with (g := g) (U := U) (a := a) (w := w) (P := Px).
           * apply parents_in_graph with (u := w). apply HG. apply nth_error_In in Haxix. apply Haxix.
           * apply HU.
           * apply Haxix.
           * split. apply Hparx. apply HPx.
           * assert (Ha: is_assigned A4 a = true \/ is_assigned A1 a = true).
             { assert (Ha: In a (u :: l)). { apply first_elt_of_sublist_not_last_elt_gen with (t := []) (b := w) (v := v). apply Haxsub. }
               destruct Ha as [Ha | Ha].
               - rewrite <- Ha. apply HuA4.
               - destruct Hp as [Hp [_ Hcyc]]. apply intermediate_node_in_path with (x := a) in Hp. apply Hp in Ha.
                 destruct Ha as [Ha | [Ha | Ha]].
                 + right. apply assigned_is_true. apply assigned_has_value with (L := get_A1_binded_nodes_in_g_path G (u, v, l)). split. 2: { apply HA1. }
                   apply mediators_in_A1. apply Ha.
                 + left. apply assigned_is_true. apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (u, v, l)). split. 2: { apply HA4. }
                   apply confounders_in_A4. apply Ha.
                 + exfalso. apply colliders_vs_edges_in_path in Ha. destruct Ha as [y [z Ha]].
                   assert (Hwb: z = w).
                   { apply two_sublists_the_same with (l := u :: l ++ [v]) (a := a).
                     - apply end_of_sublist_still_sublist_2 with (a1 := y). apply Ha.
                     - apply Haxsub.
                     - apply acyclic_path_count with (x := a) in Hcyc.
                       apply Hcyc. apply sublist_member with (l1 := [a;w]). split. left. reflexivity. apply Haxsub. }
                   unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [HG' HG]]. apply contains_cycle_false_correct with (p := (a, a, [w])) in HG.
                   +++ unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
                   +++ simpl. apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. apply edge_in_graph_then_is_edge in Haxix.
                       rewrite Haxix. rewrite <- Hwb. destruct Ha as [_ [_ Ha]]. rewrite Ha. reflexivity. apply HG'. }

             destruct Ha as [Ha | Ha].
             -- apply HA4_const. apply Ha. apply HU. apply HaU. apply Ha.
             -- (* induction: find node b s.t. b -> a -> w is in path *)
                apply assigned_is_true in Ha. destruct Ha as [ia Ha]. pose proof Ha as HA1a. apply get_assigned_In in Ha.
                apply HA1bind in Ha. destruct Ha as [b [Hbaia Hbasub]]. destruct Hbasub as [Hbasub | Hbasub].
                ++ apply IH with (a := b) (iw := ia). apply assigned_is_true. exists ia. apply HA1a.
                   ** assert (Hsub: sublist [a; w] (u :: l ++ [v]) = true).
                      { simpl. simpl in Haxsub. apply Haxsub. }
                      apply index_of_sublist with (a := w).
                      { apply Hsub. }
                      { apply acyclic_path_count with (l := l).
                        * apply sublist_member with (l1 := [a; w]). split. right. left. reflexivity. apply Hsub.
                        * apply Hp. }
                      { apply acyclic_path_count with (l := l).
                        * apply sublist_member with (l1 := [a; w]). split. left. reflexivity. apply Hsub.
                        * apply Hp. }
                      apply Hiwp.
                   ** apply HA1a.
                   ** apply Hbaia.
                   ** apply Hbasub.
                ++ assert (Hwb: w = b).
                   { apply two_sublists_the_same with (l := u :: l ++ [v]) (a := a).
                     - simpl in Haxsub. apply Haxsub.
                     - simpl in Hbasub. apply Hbasub.
                     - destruct Hp as [_ [_ Hp]]. apply acyclic_path_count with (x := a) in Hp.
                       apply Hp. apply sublist_member with (l1 := [a;b]). split. left. reflexivity. apply Hbasub. }
                   unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [HG' HG]]. apply contains_cycle_false_correct with (p := (a, a, [w])) in HG.
                   +++ unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
                   +++ simpl. rewrite <- Hwb in Hbaia. apply nth_error_In in Hbaia. apply edge_from_parent_to_child in Hbaia. apply edge_in_graph_then_is_edge in Hbaia.
                       rewrite Hbaia. apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. apply edge_in_graph_then_is_edge in Haxix. rewrite Haxix. reflexivity.
                       apply HG'. apply HG'.
       - apply membership_rev in Hwmem. apply index_exists in Hwmem. destruct Hwmem as [iwp Hiwp].
         clear Hconn. clear HA2'. clear HA1'.
         generalize dependent a. generalize dependent w. generalize dependent iw. induction iwp as [| iwp' IH].
         + intros iw w HA1w Hiwp Hiw a Haxix Haxsub. (* w = v, but [w;a] is sublist, contradicts acyclic *)
           apply index_correct in Hiwp. simpl in Hiwp. rewrite reverse_list_append in Hiwp. simpl in Hiwp. inversion Hiwp.
           assert (Hwmem': In w (u :: l)). { apply first_elt_of_sublist_not_last_elt_gen with (t := []) (b := a) (v := v). simpl in Haxsub. apply Haxsub. }
           destruct Hp as [_ [_ Hp]]. exfalso. destruct Hwmem' as [Hwmem' | Hwmem']. destruct Hp as [Hp _]. apply Hp. rewrite H1. apply Hwmem'.
           destruct Hp as [_ [_ [Hp _]]]. apply Hp. rewrite H1. apply Hwmem'.
         + intros iw w HA1w Hiwp Hiw a Haxix Haxsub.

           assert (HA1w': In w (get_A1_binded_nodes_in_g_path G (u, v, l))).
           { apply assigned_true_then_in_list with (A := A1). split. apply HA1w. apply HA1. }

           assert (Hw': exists (P: assignments X), find_values G g (find_parents w G) U [] = Some P
                /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                /\ exists (unobs: X), get_assigned_value U w = Some unobs
                /\ find_value G g w U [] = Some (g w (unobs, pa))).
           { apply find_value_evaluates_to_g. split.
             - apply HG.
             - split. apply HU. apply A1_nodes_in_graph with (u := u) (v := v) (l := l). apply HG. apply Hp.
               apply HA1w'. }
           destruct Hw' as [Px [HPx [pax [Hparx [unobsx [HxU Hx]]]]]]. rewrite Hx.
           rewrite Heqg. unfold g_path''. rewrite Hiw. unfold f_parent_i. simpl.

           f_equal. apply Hi'' with (g := g) (U := U) (a := a) (w := w) (P := Px).
           * apply parents_in_graph with (u := w). apply HG. apply nth_error_In in Haxix. apply Haxix.
           * apply HU.
           * apply Haxix.
           * split. apply Hparx. apply HPx.
           * assert (Ha: is_assigned A4 a = true \/ is_assigned A1 a = true).
             { assert (Ha: In a (l ++ [v])). { apply middle_elt_of_sublist_not_first_elt_gen with (A := [a]) (a := w) (h := u). split. apply Haxsub. left. reflexivity. }
               apply membership_append_or in Ha. destruct Ha as [Ha | Ha].
               - destruct Hp as [Hp [_ Hcyc]]. apply intermediate_node_in_path with (x := a) in Hp. apply Hp in Ha.
                 destruct Ha as [Ha | [Ha | Ha]].
                 + right. apply assigned_is_true. apply assigned_has_value with (L := get_A1_binded_nodes_in_g_path G (u, v, l)). split. 2: { apply HA1. }
                   apply mediators_in_A1. apply Ha.
                 + left. apply assigned_is_true. apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (u, v, l)). split. 2: { apply HA4. }
                   apply confounders_in_A4. apply Ha.
                 + exfalso. apply colliders_vs_edges_in_path in Ha. destruct Ha as [y [z Ha]].
                   assert (Hwb: y = w).
                   { apply two_sublists_the_same_2 with (l := u :: l ++ [v]) (a := a).
                     - apply start_of_sublist_still_sublist with (b := z). apply Ha.
                     - apply Haxsub.
                     - apply acyclic_path_count with (x := a) in Hcyc.
                       apply Hcyc. apply sublist_member with (l1 := [w;a]). split. right. left. reflexivity. apply Haxsub. }
                   unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [HG' HG]]. apply contains_cycle_false_correct with (p := (a, a, [w])) in HG.
                   +++ unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
                   +++ simpl. apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. apply edge_in_graph_then_is_edge in Haxix.
                       rewrite Haxix. rewrite <- Hwb. destruct Ha as [_ [Ha _]]. rewrite Ha. reflexivity. apply HG'.
               - destruct Ha as [Ha | Ha]. rewrite <- Ha. apply HvA4. exfalso. apply Ha. }

             destruct Ha as [Ha | Ha].
             -- apply HA4_const. apply Ha. apply HU. apply HaU. apply Ha.
             -- (* induction: find node b s.t. b -> a -> w is in path *)
                apply assigned_is_true in Ha. destruct Ha as [ia Ha]. pose proof Ha as HA1a. apply get_assigned_In in Ha.
                apply HA1bind in Ha. destruct Ha as [b [Hbaia Hbasub]]. destruct Hbasub as [Hbasub | Hbasub].
                ++ assert (Hwb: w = b).
                   { apply two_sublists_the_same_2 with (l := u :: l ++ [v]) (a := a).
                     - simpl in Haxsub. apply Haxsub.
                     - simpl in Hbasub. apply Hbasub.
                     - destruct Hp as [_ [_ Hp]]. apply acyclic_path_count with (x := a) in Hp.
                       apply Hp. apply sublist_member with (l1 := [b;a]). split. right. left. reflexivity. apply Hbasub. }
                   unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [HG' HG]]. apply contains_cycle_false_correct with (p := (a, a, [w])) in HG.
                   +++ unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
                   +++ simpl. rewrite <- Hwb in Hbaia. apply nth_error_In in Hbaia. apply edge_from_parent_to_child in Hbaia. apply edge_in_graph_then_is_edge in Hbaia.
                       rewrite Hbaia. apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. apply edge_in_graph_then_is_edge in Haxix. rewrite Haxix. reflexivity.
                       apply HG'. apply HG'.
                ++ apply IH with (a := b) (iw := ia). apply assigned_is_true. exists ia. apply HA1a.
                   ** assert (Hsub: sublist [w; a] (u :: l ++ [v]) = true).
                      { apply Haxsub. }
                      apply index_of_sublist with (a := w).
                      { unfold nodes in *. unfold node in *. rewrite reverse_list_twice with (l := [a; w]). apply sublist_rev. apply Hsub. }
                      { rewrite count_reverse. rewrite <- reverse_list_twice. apply acyclic_path_count with (l := l).
                        * apply sublist_member with (l1 := [w; a]). split. left. reflexivity. apply Hsub.
                        * apply Hp. }
                      { rewrite count_reverse. rewrite <- reverse_list_twice. apply acyclic_path_count with (l := l).
                        * apply sublist_member with (l1 := [w; a]). split. right. left. reflexivity. apply Hsub.
                        * apply Hp. }
                      apply Hiwp.
                   ** apply HA1a.
                   ** apply Hbaia.
                   ** apply Hbasub. }

    intros [Hwp Hwcol]. rewrite node_in_path_equiv in Hwp. apply member_In_equiv in Hwp. destruct Hwp as [Hwu | Hwhtv].
    - assert (Hu: is_assigned A4 u = true \/ is_assigned A1 u = true). { apply HuA4. }
      destruct Hu as [Hu | Hu]. apply HA4_const. rewrite <- Hwu. apply Hu. apply HU. apply HaU. rewrite <- Hwu. apply Hu.
      apply HA1_const. rewrite <- Hwu. apply Hu.
    - apply membership_append_or in Hwhtv. destruct Hwhtv as [Hwt | Hwv].
      + assert (Hp': is_path_in_graph (u, v, l) G = true). { apply Hp. }
        apply intermediate_node_in_path with (x := w') in Hp'. apply Hp' in Hwt. destruct Hwt as [Hwt | [Hwt | Hwt]].
        * apply HA1_const. apply assigned_is_true. apply assigned_has_value with (L := get_A1_binded_nodes_in_g_path G (u, v, l)).
          split. apply mediators_in_A1. apply Hwt. apply Hexist.
        * assert (Hw: is_assigned A4 w' = true). { apply assigned_is_true. apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (u, v, l)). split.
            apply confounders_in_A4. apply Hwt. apply HA4. }
          apply HA4_const. apply Hw. apply HU. apply HaU. apply Hw.
        * exfalso. apply Hwcol. apply Hwt.
      + assert (Hv: is_assigned A1 v = true \/ is_assigned A4 v = true). { rewrite or_comm. apply HvA4. }
        destruct Hwv as [Hwv | F]. destruct Hv as [Hv | Hv].
        * apply HA1_const. rewrite <- Hwv. apply Hv.
        * apply HA4_const. rewrite <- Hwv. apply Hv. apply HU. apply HaU. rewrite <- Hwv. apply Hv.
        * exfalso. apply F. }

  assert (HA2_equate: forall (U: assignments X) (w: node) (Px: assignments X) (pax: list X) (unobsx: X) (iw jw: nat) (xw yw: X) (x: X),
                          is_assignment_for U (nodes_in_graph G) = true
                          -> (forall u4 : node, is_assigned A4 u4 = true -> get_assigned_value U u4 = Some x)
                          -> find_values G g (find_parents w G) U [] = Some Px
                          -> Some pax = get_parent_assignments Px (find_parents w G)
                          -> get_assigned_value U w = Some unobsx
                          -> find_value G g w U [] = Some (g w (unobsx, pax))
                          -> get_assigned_value A2 w = Some (iw, jw, xw, yw)
                          -> f_equate_ij X iw jw xw yw (unobsx, pax) = xw).
  { destruct Hexist as [HA1 [HA1' [HA1'' [HA2 [HA2' [HA2D HA3]]]]]].
    intros U w Px pax unobsx iw jw xw yw x HU Hu4 HPx Hparx HxU Hx HA2w. unfold A2_nodes_colliders_in_graph in HA2'.
    specialize HA2' with (c := w) (i := iw) (j := jw) (x := xw) (y := yw). pose proof HA2w as HA2w'.
    apply get_assigned_In in HA2w'. apply HA2' in HA2w'. destruct HA2w' as [a [b Hvalw]].

    (* since a and b are in the path and not colliders, they must be in A1 or A4 -> use HA4_const or HA1_const *)
    assert (Ha: find_value G g a U [] = Some x).
    { apply Hw. apply HU. apply Hu4. split.
      - rewrite node_in_path_equiv. apply member_In_equiv. apply sublist_member with (l1 := [a; w; b]). split. left. reflexivity. simpl in Hvalw. apply Hvalw.
      - intros Hacol.
        (* contradiction: since a -> w is an edge, a is not a collider *)
        apply colliders_vs_edges_in_path in Hacol. destruct Hacol as [a1 [a2 [Hasub Haedge]]]. destruct Hvalw as [_ [_ [Hawbsub Hawbcol]]].
        assert (Ha2w: (w =? a2) = false).
        { unfold is_collider_bool in Hawbcol. destruct (w =? a2) as [|] eqn:Hwa2.
          - unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [_ HG]]. apply contains_cycle_false_correct with (p := (a, a, [w])) in HG.
            + unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
            + simpl. destruct Haedge as [_ Ha2a]. apply eqb_eq in Hwa2. rewrite <- Hwa2 in Ha2a. rewrite Ha2a.
              apply split_and_true in Hawbcol. destruct Hawbcol as [Haw _]. rewrite Haw. reflexivity.
          - reflexivity. }
        assert (Ha2w': w = a2).
        { apply two_sublists_the_same with (l := u :: l ++ [v]) (a := a).
          - apply start_of_sublist_still_sublist in Hawbsub. apply Hawbsub.
          - apply end_of_sublist_still_sublist_2 in Hasub. apply Hasub.
          - apply acyclic_path_count with (l := l).
            * apply sublist_member with (l1 := [a; w; b]). split. left. reflexivity. apply Hawbsub.
            * apply Hp. }
        rewrite Ha2w' in Ha2w. rewrite eqb_refl in Ha2w. discriminate Ha2w. }

    assert (Hb: find_value G g b U [] = Some x).
    { apply Hw. apply HU. apply Hu4. split.
      - rewrite node_in_path_equiv. apply member_In_equiv. apply sublist_member with (l1 := [a; w; b]). split. right. right. left. reflexivity. simpl in Hvalw. apply Hvalw.
      - intros Hbcol.
        (* contradiction: since w <- b is an edge, b is not a collider *)
        apply colliders_vs_edges_in_path in Hbcol. destruct Hbcol as [b1 [b2 [Hbsub Hbedge]]]. destruct Hvalw as [_ [_ [Hawbsub Hawbcol]]]. 
        assert (Hb1w: (w =? b1) = false).
        { unfold is_collider_bool in Hawbcol. destruct (w =? b1) as [|] eqn:Hwb1.
          - unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [_ HG]]. apply contains_cycle_false_correct with (p := (b, b, [w])) in HG.
            + unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
            + simpl. destruct Hbedge as [Hb1w _]. apply eqb_eq in Hwb1. rewrite <- Hwb1 in Hb1w. rewrite Hb1w.
              apply split_and_true in Hawbcol. destruct Hawbcol as [_ Hwb]. rewrite Hwb. reflexivity.
          - reflexivity. }
        assert (Hb1w': w = b1).
        { apply two_sublists_the_same_2 with (l := u :: l ++ [v]) (a := b).
          - apply end_of_sublist_still_sublist_2 in Hawbsub. apply Hawbsub.
          - apply start_of_sublist_still_sublist in Hbsub. apply Hbsub.
          - apply acyclic_path_count with (u := u) (v := v) (l := l).
            * apply sublist_member with (l1 := [b1; b; b2]). split. right. left. reflexivity. apply Hbsub.
            * apply Hp. }
        rewrite Hb1w' in Hb1w. rewrite eqb_refl in Hb1w. discriminate Hb1w. }

    unfold f_equate_ij. simpl.
    assert (Hiw: nth_default unobsx pax iw = x).
    { apply Hi'' with (g := g) (U := U) (a := a) (w := w) (P := Px). apply parents_in_graph with (u := w). apply HG. destruct Hvalw as [Hvalw _]. apply nth_error_In in Hvalw. apply Hvalw. apply HU.
      apply Hvalw. split. apply Hparx. apply HPx. apply Ha. }
    assert (Hjw: nth_default unobsx pax jw = x).
    { apply Hi'' with (g := g) (U := U) (a := b) (w := w) (P := Px). apply parents_in_graph with (u := w). apply HG. destruct Hvalw as [_ [Hvalw _]]. apply nth_error_In in Hvalw. apply Hvalw. apply HU.
      apply Hvalw. split. apply Hparx. apply HPx. apply Hb. }
    rewrite Hiw. rewrite Hjw. rewrite eqb_refl'. reflexivity. }

  assert (HcondU: forall (U: assignments X) (x: X),
                    is_assignment_for U (nodes_in_graph G) = true
                    -> (forall (u4: node), is_assigned A4 u4 = true -> get_assigned_value U u4 = Some x)
                    -> unobs_conditions_on_Z G g U AZ Z).
  { destruct Hexist as [HA1 [HA1' [HA1'' [HA2 [HA2' [HA2D HA3]]]]]].
    intros U x HU Hu4. unfold unobs_conditions_on_Z. intros w [HwZ HwG].
    (* either w is in A2, A3, or not in the path *)
    assert (Hw': exists (P: assignments X), find_values G g (find_parents w G) U [] = Some P
                /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                /\ exists (unobs: X), get_assigned_value U w = Some unobs
                /\ find_value G g w U [] = Some (g w (unobs, pa))).
    { apply find_value_evaluates_to_g. split.
      - apply HG.
      - split. apply HU. apply HwG. }
    destruct Hw' as [Px [HPx [pax [Hparx [unobsx [HxU Hx]]]]]]. rewrite Hx.
    rewrite Heqg. unfold g_path''.
    assert (HA1w: is_assigned A1 w = false).
    { destruct (is_assigned A1 w) as [|] eqn:HA1w.
      - assert (HA1w': In w (get_A1_binded_nodes_in_g_path G (u, v, l))).
        { destruct (member w (get_A1_binded_nodes_in_g_path G (u, v, l))) as [|] eqn:Hmem.
          - apply member_In_equiv. apply Hmem.
          - apply HA1 in Hmem. rewrite HA1w in Hmem. discriminate Hmem. }
        exfalso. apply A1_mediators_or_endpoints in HA1w'. destruct HA1w' as [HA1w' | [HA1w' | HA1w']].
        + apply HuZ. rewrite <- HA1w'. apply HwZ.
        + destruct Hconn as [Hconn _]. apply no_overlap_non_member with (x := w) in Hconn. apply Hconn. apply HwZ. apply HA1w'.
        + apply HvZ. rewrite <- HA1w'. apply HwZ.
      - reflexivity. }
    apply assigned_is_false in HA1w. rewrite HA1w.

    destruct (get_assigned_value A2 w) as [vA2 |] eqn:HA2w.
    - destruct vA2 as [[[iw jw] xw] yw].
      assert (Hvalw: f_equate_ij X iw jw xw yw (unobsx, pax) = xw).
      { apply HA2_equate with (w := w) (Px := Px) (U := U) (x := x). apply HU. apply Hu4. apply HPx. apply Hparx. apply HxU. apply Hx. apply HA2w. }
      rewrite Hvalw.
      unfold A2_consistent_with_D in HA2D. pose proof HA2w as HA2w'. apply HA2D in HA2w. unfold descendant_paths_disjoint in Hdesc. destruct Hdesc as [_ Hdesc].
      assert (Hwcol: In w (find_colliders_in_path (u, v, path_int (u, v, l)) G)).
      { apply assigned_true_then_in_list with (A := A2). split. apply assigned_is_true. exists (iw, jw, xw, yw). apply HA2w'. apply HA2. }
      apply Hdesc in Hwcol. destruct Hwcol as [[Hwcol _] | Hwcol].
      + destruct HA2w as [pw [dw Hpdw]]. destruct Hpdw as [Hpdw Hpdw']. rewrite Hpdw in Hwcol. inversion Hwcol. rewrite H2 in Hpdw'. symmetry. apply Hpdw'.
      + (* contradiction: w is in Z *) destruct Hwcol as [pw [dw [_ [_ [_ [_ [Hover _]]]]]]]. apply member_In_equiv in HwZ. simpl in Hover. rewrite HwZ in Hover. discriminate Hover.
    - destruct (get_assigned_value A3 w) as [iw |] eqn:HA3w.
      + assert (HA3w': is_assigned A3 w = true). { apply assigned_is_true. exists iw. apply HA3w. }
        apply A3_nodes_belong_to_collider with (D := D) (G := G) (u := u) (v := v) (l := l) in HA3w'. 2: { apply HA3. }
        destruct HA3w' as [cw [dw [pw [Hcw [HDw [Hdcw Hwpd]]]]]].
        unfold descendant_paths_disjoint in Hdesc. destruct Hdesc as [Hdesc' Hdesc].
        pose proof Hcw as Hccol. apply Hdesc in Hcw.
        destruct Hcw as [Hcw | Hcw].
        * (* contradiction, w is not in A2 *) destruct Hcw as [Hcw _]. rewrite HDw in Hcw. inversion Hcw.
          assert (HA2cw: is_assigned A2 cw = true). { apply assigned_is_true. apply assigned_has_value with (L := get_A2_binded_nodes_in_g_path G (u, v, l)). split. 2: { apply HA2. }
            apply Hccol. }
          rewrite <- H2 in HA2cw. assert (Hdww: w = dw). { rewrite H1 in Hwpd. simpl in Hwpd. destruct Hwpd as [Hwpd | Hwpd]. symmetry. apply Hwpd. exfalso. apply Hwpd. }
          rewrite <- Hdww in HA2cw. apply assigned_is_false in HA2w. rewrite HA2w in HA2cw. discriminate HA2cw.
        * destruct Hcw as [pw' [dw' [Hpdw' Hcw]]]. rewrite Hpdw' in HDw. inversion HDw. rewrite H1 in *. rewrite H2 in *. clear H1. clear H2.
          assert (Hdww: w = dw).
          { apply membership_append_or in Hwpd. destruct Hwpd as [Hwpd | Hwpd].
            - destruct Hcw as [_ [_ [_ [Hcw _]]]]. apply no_overlap_non_member with (x := w) in Hcw. exfalso. apply Hcw. right. apply Hwpd. apply HwZ.
            - destruct Hwpd as [Hwpd | Hwpd]. symmetry. apply Hwpd. exfalso. apply Hwpd. }

          assert (Hnodecw: node_in_graph cw G = true).
          { apply colliders_vs_edges_in_path in Hccol.  destruct Hccol as [y [_ [_ [Hccol _]]]]. apply is_edge_then_node_in_graph with (v := y). right. apply Hccol. }

          assert (Hdw: Some (f_parent_i X iw (unobsx, pax)) = find_value G g cw U []).
          { assert (Hmap: get_A3_assignments_for_desc_paths D G (find_colliders_in_path (u, v, l) G) = Some A3).
            { apply HA3. }
            pose proof Hmap as HA3_const. apply A3_nodes_map_to_parent with (w := w) (Z := Z) in Hmap.
            2: { split. apply Hdesc'. apply Hdesc. } 2: { apply assigned_is_true. exists iw. apply HA3w. }
            destruct Hmap as [cw' [dw'' [pw'' [ipd [Hcw' [Hpdw'' Hmap]]]]]].
            assert (Hcweq: cw = cw').
            { destruct (cw =? cw') as [|] eqn:Hcweq.
              - apply eqb_eq. apply Hcweq.
              - exfalso. assert (Hover: overlap (cw :: pw ++ [dw]) (cw' :: pw'' ++ [dw'']) = false).
                { apply Hcw. split. apply Hcweq. apply Hpdw''. }
                apply no_overlap_non_member with (x := w) in Hover. apply Hover. right. apply Hwpd.
                apply index_exists. exists (S ipd). symmetry. apply Hmap. }
            rewrite <- Hcweq in *. clear Hcweq. unfold nodes in *. rewrite Hpdw' in Hpdw''. inversion Hpdw''. rewrite <- H1 in *. rewrite <- H2 in *. clear H1. clear H2.
            clear Hpdw''. destruct Hmap as [_ [Hipd Hmap]]. clear HwZ. clear HwG. clear Hdww. clear HDw. clear HA1w. clear HA2w.

            destruct Hmap as [w' [iw' [Hiw' [Hw' Hparw]]]]. rewrite HA3w in Hiw'. inversion Hiw'. rewrite <- H1 in *. clear H1. clear Hiw'.

            assert (Hcwf: exists (xcw: X), find_value G g cw U [] = Some xcw). { apply find_value_existence. apply HG. split. apply HU. apply Hnodecw. }
            destruct Hcwf as [xcw Hcwf].

            generalize dependent w. generalize dependent pax. generalize dependent unobsx. generalize dependent iw. generalize dependent w'. generalize dependent Px.
            induction ipd as [| ipd' IH].
            - intros Px w' Hw' iw unobsx pax w HPx Hparx HxU Hx HA3w Hwpd Hipd Hparw.
              assert (Hcweq: cw =? w' = true). { simpl in Hw'. destruct (cw =? w') as [|] eqn:Hcweq. reflexivity. destruct (index (pw ++ [dw]) w') as [ind|]. discriminate Hw'. discriminate Hw'. }
              clear Hw'. apply eqb_eq in Hcweq. rewrite <- Hcweq in *. clear Hcweq. unfold f_parent_i. simpl.
              assert (Hxcw: nth_default unobsx pax iw = xcw).
              { apply Hi'' with (g := g) (U := U) (a := cw) (w := w) (P := Px). apply parents_in_graph with (u := w). apply HG. apply index_exists. exists iw. symmetry. apply Hparw.
                apply HU. apply index_correct. symmetry. apply Hparw. split. apply Hparx. apply HPx. apply Hcwf. }
              rewrite Hxcw. rewrite Hcwf. reflexivity.
            - intros Px w' Hw' iw unobsx pax w HPx Hparx HxU Hx HA3w Hwpd Hipd Hparw.
               unfold f_parent_i. simpl.
               assert (Hwf': exists (xw': X), find_value G g w' U [] = Some xw'). { apply find_value_existence. apply HG. split. apply HU.
                 destruct Hcw as [_ [Hcw _]]. apply directed_path_is_path in Hcw. apply node_in_path_has_edge with (w := w') in Hcw. destruct Hcw as [w'' Hcw].
                 apply is_edge_then_node_in_graph with (v := w''). rewrite or_comm. apply Hcw. rewrite node_in_path_equiv. apply member_In_equiv. apply index_exists. exists (S ipd'). symmetry. apply Hw'. }
               destruct Hwf' as [xw' Hwf'].
               assert (Hxw': nth_default unobsx pax iw = xw').
               { apply Hi'' with (g := g) (U := U) (a := w') (w := w) (P := Px). apply parents_in_graph with (u := w). apply HG. apply index_exists. exists iw. symmetry. apply Hparw.
                 apply HU. apply index_correct. symmetry. apply Hparw. split. apply Hparx. apply HPx. apply Hwf'. }
               rewrite Hxw'. rewrite <- Hwf'. (* induction on w' *) rewrite Hcwf.

               assert (Hmemw': In w' (pw ++ [dw])).
               { apply index_exists. exists ipd'. simpl in Hw'. destruct (cw =? w') as [|]. discriminate Hw'.
                 destruct (index (pw ++ [dw]) w') as [ipd'' |]. inversion Hw'. reflexivity. discriminate Hw'. }

               assert (HA3w': is_assigned A3 w' = true).
               { apply desc_path_nodes_in_A3 with (d := dw) (c := cw) (p := pw) (x := w') in HA3_const.
                 - apply HA3_const.
                 - split. apply Hpdw'. apply Hdcw.
                 - apply Hcw'.
                 - apply Hmemw'. }

               assert (Hfw': exists (P: assignments X), find_values G g (find_parents w' G) U [] = Some P
                    /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w' G)
                    /\ exists (unobs: X), get_assigned_value U w' = Some unobs
                    /\ find_value G g w' U [] = Some (g w' (unobs, pa))).
               { apply find_value_evaluates_to_g. split.
                 - apply HG.
                 - split. apply HU. apply parents_in_graph with (u := w). apply HG. apply index_exists. exists iw. symmetry. apply Hparw. }
               destruct Hfw' as [Pw' [HPw' [paw' [Hparw' [unobsw' [HwU' Hfw']]]]]]. rewrite Hfw'.
               rewrite Heqg. unfold g_path''.

               assert (HA1w': is_assigned A1 w' = false).
               { apply HA1. apply member_In_equiv_F. intros HA1w'.
                 apply descendant_paths_disjoint_with_A1 with (Z := Z) (x := w') in HA3_const.
                 - apply assigned_is_false in HA3_const. rewrite HA3_const in HA3w'. discriminate HA3w'.
                 - split. apply Hdesc'. apply Hdesc.
                 - apply HA1w'. } apply assigned_is_false in HA1w'. rewrite HA1w'.
               assert (HA2w': is_assigned A2 w' = false).
               { apply HA2. apply member_In_equiv_F. intros HA2w'.
                 apply descendant_paths_disjoint_with_A2 with (Z := Z) (x := w') in HA3_const.
                 - apply assigned_is_false in HA3_const. rewrite HA3_const in HA3w'. discriminate HA3w'.
                 - split. apply Hdesc'. apply Hdesc.
                 - apply HA2w'. } apply assigned_is_false in HA2w'. rewrite HA2w'.
               apply assigned_is_true in HA3w'. destruct HA3w' as [_iw' HA3w']. rewrite HA3w'.
               rewrite <- Hcwf.

               apply A3_nodes_map_to_parent with (w := w') (Z := Z) in HA3_const as Hmapw'.
               2: { split. apply Hdesc'. apply Hdesc. } 2: { apply assigned_is_true. exists _iw'. apply HA3w'. }
               destruct Hmapw' as [cw'' [dw''' [pw''' [ipd'' [Hcw'' [Hpdw''' Hmapw']]]]]].
               assert (Hcweq: cw = cw'').
               { destruct (cw =? cw'') as [|] eqn:Hcweq. apply eqb_eq. apply Hcweq.
                 assert (Hover: overlap (cw :: pw ++ [dw]) (cw'' :: pw''' ++ [dw''']) = false).
                 { apply Hcw. split. apply Hcweq. apply Hpdw'''. }
                 exfalso. apply no_overlap_non_member with (x := w') in Hover. apply Hover. apply index_exists. exists (S ipd'). symmetry. apply Hw'.
                 apply index_exists. exists (S ipd''). symmetry. apply Hmapw'. }
               rewrite <- Hcweq in *. clear Hcweq. clear Hcw''. unfold nodes in *. rewrite Hpdw' in Hpdw'''. inversion Hpdw'''. rewrite <- H1 in *. rewrite <- H2 in *. clear H1. clear H2.
               clear Hpdw'''. destruct Hmapw' as [_ [Hipd'' Hmapw']]. rewrite Hw' in Hipd''. inversion Hipd''. rewrite <- H1 in *. clear H1. clear Hipd''.
               destruct Hmapw' as [w'' [_iw'' [Hiw'' Hmapw']]]. rewrite HA3w' in Hiw''. inversion Hiw''. rewrite <- H1 in *. clear H1. clear Hiw''.
               apply IH with (w := w') (w' := w'') (Px := Pw'). apply Hmapw'. apply HPw'. apply Hparw'. apply HwU'. apply Hfw'. apply HA3w'.
               apply Hmemw'. apply Hw'. apply Hmapw'. }

          rewrite Hdw.
          assert (Hcwf: exists (P: assignments X), find_values G g (find_parents cw G) U [] = Some P
               /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents cw G)
               /\ exists (unobs: X), get_assigned_value U cw = Some unobs
               /\ find_value G g cw U [] = Some (g cw (unobs, pa))).
          { apply find_value_evaluates_to_g. split.
            - apply HG.
            - split. apply HU. apply Hnodecw. }
          destruct Hcwf as [Pcw [HPcw [pacw [Hparcw [unobscw [HcwU Hcwf]]]]]]. rewrite Hcwf.
          rewrite Heqg. unfold g_path''.

          assert (HA1cw: is_assigned A1 cw = false).
          { apply HA1. apply member_In_equiv_F. intros HA1cw.
            apply A2_nodes_not_in_A1 in HA1cw. apply HA1cw. apply HG. apply Hp. apply Hp. unfold get_A2_binded_nodes_in_g_path. apply Hccol. }
          apply assigned_is_false in HA1cw. rewrite HA1cw.

          assert (HA2cw: exists (valcw: nat * nat * X * X), get_assigned_value A2 cw = Some valcw).
          { apply assigned_has_value with (L := find_colliders_in_path (u, v, l) G). split. apply Hccol. apply HA2. }
          destruct HA2cw as [[[[icw jcw] xcw] ycw] HA2cw]. rewrite HA2cw.
          assert (Hfcw: f_equate_ij X icw jcw xcw ycw (unobscw, pacw) = xcw).
          { apply HA2_equate with (w := cw) (Px := Pcw) (U := U) (x := x). apply HU. apply Hu4. apply HPcw. apply Hparcw. apply HcwU. apply Hcwf. apply HA2cw. }
          rewrite Hfcw.

          unfold A2_consistent_with_D in HA2D. pose proof HA2cw as HA2cw'. apply HA2D in HA2cw. destruct HA2cw as [pw'' [dw'' [Hpd' [Hxcw Hycw]]]].
          unfold nodes in *. rewrite Hpdw' in Hpd'. inversion Hpd'. rewrite <- H1 in *. rewrite <- H2 in *. clear H1. clear H2. clear Hpd'.
          rewrite Hdww. rewrite Hxcw. reflexivity.

      + assert (HA4w: is_assigned A4 w = false).
        { destruct (is_assigned A4 w) as [|] eqn:HA4w.
          - assert (HA4w': In w (get_A4_binded_nodes_in_g_path G (u, v, l))).
            { destruct (member w (get_A4_binded_nodes_in_g_path G (u, v, l))) as [|] eqn:Hmem.
              - apply member_In_equiv. apply Hmem.
              - apply HA4 in Hmem. rewrite HA4w in Hmem. discriminate Hmem. }
            exfalso. apply A4_confounders_or_endpoints in HA4w'. destruct HA4w' as [HA4w' | [HA4w' | HA4w']].
            + apply HuZ. rewrite <- HA4w'. apply HwZ.
            + destruct Hconn as [_ [Hconn _]]. apply no_overlap_non_member with (x := w) in Hconn. apply Hconn. apply HwZ. apply HA4w'.
            + apply HvZ. rewrite <- HA4w'. apply HwZ.
          - reflexivity. }
        apply assigned_is_false in HA4w. rewrite HA4w.
        assert (HAZw: exists (wz: X), get_assigned_value AZ w = Some wz).
        { apply assigned_has_value with (L := Z). split. apply HwZ. apply HAZ. }
        destruct HAZw as [wz HAZw]. rewrite HAZw. unfold f_constant. reflexivity. }

  pose proof HG as HX. destruct HX as [HX _]. destruct HX as [X1 [X2 HX]]. intros x.
  assert (Hx: exists (y: X), x <> y). { destruct (eqb X1 x) as [|] eqn:Hx. exists X2. intros Hx'. rewrite Hx' in Hx. apply HX. apply eqb_eq'. apply Hx.
    exists X1. intros Hx'. rewrite Hx' in Hx. rewrite eqb_refl' in Hx. discriminate Hx. }
  destruct Hx as [xX Hx]. clear HX.

  remember (get_assignment_for (nodes_in_graph G) xX) as U'. exists U'. exists xX.
  assert (HUA: is_assignment_for U' (nodes_in_graph G) = true). { rewrite HeqU'. apply nodes_map_to_assignment. }
  split. apply HUA.

  assert (HUA1': forall u4 : node, is_assigned A4 u4 = true -> get_assigned_value U' u4 = Some xX).
  { intros u4 Hu4. rewrite HeqU'. apply node_maps_to_assigned_value.
    assert (HA4w': In u4 (get_A4_binded_nodes_in_g_path G (u, v, l))).
    { destruct (member u4 (get_A4_binded_nodes_in_g_path G (u, v, l))) as [|] eqn:Hmem.
      - apply member_In_equiv. apply Hmem.
      - apply HA4 in Hmem. rewrite Hu4 in Hmem. discriminate Hmem. }
    apply A4_nodes_in_graph in HA4w'. destruct G as [V E]. simpl in HA4w'. apply member_In_equiv. simpl. apply HA4w'. apply HG. apply Hp. }

  assert (Hcond: unobs_conditions_on_Z G g U' AZ Z).
  { apply HcondU with (x := xX). apply HUA. apply HUA1'. }

  split. apply Hcond.

  split. intros w Hw'. apply Hw. apply HUA. apply HUA1'. apply Hw'.

  split. symmetry. apply Hx.

  intros Ux LUx HeqUx. destruct HeqUx as [HeqUx HeqLUx].

  assert (Hrx: forall w : node,
                 In w (get_A4_binded_nodes_in_g_path G (u, v, path_int (u, v, l))) ->
                 exists r : X, get_assigned_value U' w = Some r /\ eqb r x = false).
  { intros w Hw4. exists xX. split. rewrite HeqU'. apply node_maps_to_assigned_value. apply A4_nodes_in_graph in Hw4. destruct G as [V E]. apply member_In_equiv. simpl. simpl in Hw4. apply Hw4.
    apply HG. apply Hp. destruct (eqb xX x) as [|] eqn:Hyx. exfalso. apply Hx. apply eqb_eq'. rewrite eqb_sym'. apply Hyx. reflexivity. }

  assert (HUxA: is_assignment_for Ux (nodes_in_graph G) = true).
  { apply equiv_assignment_still_assignment with (U := (hd 0 (get_A4_binded_nodes_in_g_path G (u, v, l)), x) :: U'). apply HeqUx. apply is_assignment_for_cat. apply HUA. }

  split.
  { destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + (* u <- ...l... <-> v, u is in A1 *)
      assert (H1: exists (t1: nodes), get_A1_binded_nodes_in_g_path G (u, v, l) = u :: t1).
      { unfold get_A1_binded_nodes_in_g_path. rewrite Hin. destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
        exists (find_mediators_in_path (u, v, l) G). reflexivity.
        exists (find_mediators_in_path (u, v, l) G ++ [v]). reflexivity.
        apply path_out_of_end_Some in Hout. exfalso. apply Hout. }
      destruct H1 as [t1 H1].

      assert (HA1u: is_assigned A1 u = true). { apply assigned_is_true. apply assigned_has_value with (L := u :: t1). split. left. reflexivity. rewrite <- H1. apply Hexist. }

      clear Hrx. clear HeqLUx. clear H1. destruct Hexist as [HA1 [HA1' [HA1'' [HA2 [_ [_ HA3]]]]]]. destruct HA1 as [HA1 _].
      destruct Hp as [Hp [_ Hcyc]]. clear Hw.

      generalize dependent u. generalize dependent A1. generalize dependent A5. induction l as [| h t IH].
      * intros A5 A1 HA1'' Heqg u Hp Hcyc HuZ Hdesc Hconn HA1 HA1' HA2 HA3 HA4 HeqUx Hin HA1u.
        assert (Hw': exists (P: assignments X), find_values G g (find_parents u G) Ux [] = Some P
          /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents u G)
          /\ exists (unobs: X), get_assigned_value Ux u = Some unobs
          /\ find_value G g u Ux [] = Some (g u (unobs, pa))).
        { apply find_value_evaluates_to_g. split.
          - apply HG.
          - split. apply HUxA. apply is_edge_then_node_in_graph with (v := v). simpl in Hin. right. apply Hin. }
        destruct Hw' as [Px [HPx [pax [Hparx [unobsx [HxU Hu]]]]]]. rewrite Hu.
        rewrite Heqg. unfold g_path''.
        pose proof HA1u as HA1u'.
        apply assigned_is_true in HA1u'. destruct HA1u' as [iu HA1u']. pose proof HA1u' as Hiu. apply get_assigned_In in HA1u'.
        unfold A1_nodes_binded_to_parent_in_path in HA1'. pose proof HA1' as HA1bind. specialize HA1' with (m := u) (i := iu).
        apply HA1' in HA1u'. destruct HA1u' as [a [Haxix Haxsub]]. destruct Haxsub as [Haxsub | Haxsub].
        - exfalso. simpl in Haxsub. rewrite orb_comm in Haxsub. rewrite andb_comm in Haxsub. simpl in Haxsub. apply split_and_true in Haxsub. destruct Haxsub as [_ Haxsub].
          destruct Hcyc as [Hcyc _]. apply Hcyc. apply eqb_eq. apply split_and_true in Haxsub. apply Haxsub.
        - rewrite Hiu. unfold f_parent_i. simpl.

          f_equal. apply Hi'' with (g := g) (U := Ux) (a := a) (w := u) (P := Px).
          -- apply parents_in_graph with (u := u). apply HG. apply nth_error_In in Haxix. apply Haxix.
          -- apply HUxA.
          -- apply Haxix.
          -- split. apply Hparx. apply HPx.
          -- assert (Hav: a = v). { simpl in Haxsub. rewrite orb_comm in Haxsub. rewrite andb_comm in Haxsub. simpl in Haxsub.
                rewrite eqb_refl in Haxsub. simpl in Haxsub. rewrite andb_comm in Haxsub. apply eqb_eq. apply Haxsub. }
             rewrite Hav. apply HA4_const.
             ++ apply assigned_is_true. apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (u, v, [])). split.
                2: { apply HA4. }
                simpl. simpl in Hin. rewrite Hin. left. reflexivity.
             ++ apply HUxA.
             ++ rewrite HeqUx. simpl. simpl in Hin. rewrite Hin. simpl. rewrite eqb_refl. reflexivity.

      * intros A5 A1 HA1'' Heqg u Hp Hcyc HuZ Hdesc Hconn HA1 HA1' HA2 HA3 HA4 HeqUx Hin HA1u.

        pose proof HA1u as HA1u'.
        apply assigned_is_true in HA1u'. destruct HA1u' as [iu HA1u']. pose proof HA1u' as Hiu. apply get_assigned_In in HA1u'.
        unfold A1_nodes_binded_to_parent_in_path in HA1'. pose proof HA1' as HA1bind. specialize HA1' with (m := u) (i := iu).
        apply HA1' in HA1u'. destruct HA1u' as [a [Haxix Haxsub]]. destruct Haxsub as [Haxsub | Haxsub].
        - assert (Hu: In u ((h :: t) ++ [v])). { apply middle_elt_of_sublist_not_first_elt_gen with (A := [u]) (a := a) (h := u). split. apply Haxsub. left. reflexivity. }
          exfalso. apply membership_append_or in Hu. destruct Hu as [Hu | Hu]. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. apply Hu.
          destruct Hu as [Hu | Hu]. destruct Hcyc as [Hcyc _]. apply Hcyc. symmetry. apply Hu. apply Hu.
        - (* a = h, f(u) = f(h). if h in A4, then same as above. if h in A1, then induction *)
          assert (Hw': exists (P: assignments X), find_values G g (find_parents u G) Ux [] = Some P
            /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents u G)
            /\ exists (unobs: X), get_assigned_value Ux u = Some unobs
            /\ find_value G g u Ux [] = Some (g u (unobs, pa))).
          { apply find_value_evaluates_to_g. split.
            - apply HG.
            - split. apply HUxA. apply is_edge_then_node_in_graph with (v := h). simpl in Hin. right. apply Hin. }
          destruct Hw' as [Px [HPx [pax [Hparx [unobsx [HxU Hu]]]]]]. rewrite Hu.
          rewrite Heqg. unfold g_path''.
          rewrite Hiu. unfold f_parent_i. simpl.

          f_equal. apply Hi'' with (g := g) (U := Ux) (a := a) (w := u) (P := Px).
          -- apply parents_in_graph with (u := u). apply HG. apply nth_error_In in Haxix. apply Haxix.
          -- apply HUxA.
          -- apply Haxix.
          -- split. apply Hparx. apply HPx.
          -- assert (Hav: a = h). { apply two_sublists_the_same with (l := u :: h :: t ++ [v]) (a := u). apply Haxsub. simpl. repeat rewrite eqb_refl. reflexivity.
             apply acyclic_path_count with (x := u) in Hcyc. apply Hcyc. left. reflexivity. }
             rewrite Hav.

             destruct (path_out_of_h G u v h t) as [|] eqn:Houth.
             ++ (* u <- h -> ... h is in A4 *)
                assert (Hhcol: exists (l4: nodes), get_A4_binded_nodes_in_g_path G (u, v, h :: t) = h :: l4).
                { unfold get_A4_binded_nodes_in_g_path. unfold nodes in *. rewrite Hin. destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
                  3: { apply path_out_of_end_Some in Hout. exfalso. apply Hout. }
                  { destruct t as [| h' t'].
                    - simpl. unfold is_confounder_bool. simpl in Hin. rewrite Hin. simpl in Houth. rewrite Houth. simpl. exists [v]. reflexivity.
                    - exists (find_confounders_in_path (h, v, h' :: t') G ++ [v]). simpl. unfold is_confounder_bool. simpl in Hin. rewrite Hin. simpl in Houth. rewrite Houth. simpl. reflexivity. }
                  { destruct t as [| h' t'].
                    - simpl. unfold is_confounder_bool. simpl in Hin. rewrite Hin. simpl in Houth. rewrite Houth. simpl. exists []. reflexivity.
                    - exists (find_confounders_in_path (h, v, h' :: t') G). simpl. unfold is_confounder_bool. simpl in Hin. rewrite Hin. simpl in Houth. rewrite Houth. simpl. reflexivity. } }

                apply HA4_const. 2: { apply HUxA. }
                2: { rewrite HeqUx. unfold nodes in *. destruct Hhcol as [l4 Hhcol]. rewrite Hhcol. simpl. rewrite eqb_refl. reflexivity. }
                apply assigned_is_true. apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (u, v, h :: t)). split.
                2: { apply HA4. }
                destruct Hhcol as [l4 Hhcol]. rewrite Hhcol. left. reflexivity.
             ++ (* u <- h <- ... h is in A1 *)
                assert (HA1h: In h (get_A1_binded_nodes_in_g_path G (u, v, h :: t))).
                { unfold get_A1_binded_nodes_in_g_path. unfold nodes in *. rewrite Hin.
                  assert (Hhmed: In h (find_mediators_in_path (u, v, h :: t) G)).
                  { apply mediators_vs_edges_in_path. exists u. destruct t as [| h' t'].
                    + exists v. split. simpl. repeat rewrite eqb_refl. reflexivity. right. split. apply Hin. simpl in Houth.
                      simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp].
                      apply split_and_true in Hp. destruct Hp as [Hp _]. rewrite Houth in Hp. apply Hp.
                    + exists h'. split. simpl. repeat rewrite eqb_refl. reflexivity. right. split. apply Hin. simpl in Houth.
                      simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp].
                      apply split_and_true in Hp. destruct Hp as [Hp _]. rewrite Houth in Hp. apply Hp. }
                  destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
                  - right. apply Hhmed.
                  - right. apply membership_append. apply Hhmed.
                  - exfalso. apply path_out_of_end_Some in Hout. apply Hout. }

                assert (HA1h': is_assigned A1 h = true). { apply assigned_is_true. apply assigned_has_value with (L := get_A1_binded_nodes_in_g_path G (u, v, h :: t)). split. apply HA1h. apply HA1. }

                assert (Hnodeu: node_in_graph u G = true).
                { simpl in Hp. apply is_edge_then_node_in_graph with (v := h). destruct G as [V E].
                  apply split_and_true in Hp. destruct Hp as [Hp _]. apply split_orb_true. apply Hp. }

                assert (HA1ind: get_A1_binded_nodes_in_g_path G (u, v, h :: t) = u :: get_A1_binded_nodes_in_g_path G (h, v, t)).
                { apply A1_induction_into_start.
                  - split.
                    ** apply Hp.
                    ** destruct HG as [_ [_ HG]]. apply HG.
                  - apply Hin. }
                assert (HA2ind: get_A2_binded_nodes_in_g_path G (u, v, h :: t) = get_A2_binded_nodes_in_g_path G (h, v, t)).
                { apply A2_induction_case.
                  - destruct HG as [_ [_ HG]]. apply HG.
                  - left. apply Hin. }

                assert (HA4ind: get_A4_binded_nodes_in_g_path G (u, v, h :: t) = get_A4_binded_nodes_in_g_path G (h, v, t)).
                { apply A4_induction_case.
                  - split.
                    ** apply Hp.
                    ** destruct HG as [_ [_ HG]]. apply HG.
                  - apply Hin. }

                assert (Huh: u =? h = false).
                { destruct (u =? h) as [|] eqn:Huh. exfalso. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. left. apply eqb_eq. rewrite eqb_sym. apply Huh.
                  reflexivity. }

                apply IH with (A1 := remove_assignment_for A1 u) (A5 := (u, f_parent_i X iu) :: A5).
                ** apply each_node_assigned_once_remove. apply HA1''.
                ** apply functional_extensionality. intros w. rewrite Heqg. unfold g_path''.
                   destruct (u =? w) as [|] eqn:Hux.
                   { apply eqb_eq in Hux. rewrite <- Hux in *. assert (Humem: node_in_path u (h, v, t) = false).
                     { unfold node_in_path. simpl. rewrite Huh. destruct (u =? v) as [|] eqn:Huv.
                       + exfalso. destruct Hcyc as [Hcyc _]. apply Hcyc. apply eqb_eq in Huv. apply Huv.
                       + simpl. destruct Hcyc as [_ [Hcyc _]]. apply member_In_equiv_F. intros F. apply Hcyc. right. apply F. }
                       assert (HxA1': get_assigned_value (remove_assignment_for A1 u) u = None).
                       { apply remove_assignment_None. }
                       rewrite HxA1'. rewrite Hiu.
                       assert (HxA2': get_assigned_value A2 u = None).
                       { destruct (is_assigned A2 u) as [|] eqn:HxA2'.
                         - assert (Hcol: In u (get_A2_binded_nodes_in_g_path G (h, v, t))).
                           { apply assigned_true_then_in_list with (A := A2). split. apply HxA2'. rewrite <- HA2ind. apply HA2. }
                           unfold get_A2_binded_nodes_in_g_path in Hcol. apply colliders_vs_edges_in_path in Hcol. destruct Hcol as [y [z [Hsub _]]].
                           assert (Hmem: In u (h :: t ++ [v])). { apply sublist_member with (l1 := [y; u; z]). split. right. left. reflexivity. apply Hsub. }
                           rewrite node_in_path_equiv in Humem. apply member_In_equiv in Hmem. rewrite Hmem in Humem. discriminate Humem.
                         - apply assigned_is_false. apply HxA2'. }
                       rewrite HxA2'.
                       assert (HxA3': get_assigned_value A3 u = None).
                       { apply descendant_paths_disjoint_with_A1 with (D := D) (u := u) (v := v) (l := h :: t) (G := G) (Z := Z). apply Hdesc. apply HA3.
                         unfold nodes in *. rewrite HA1ind. left. reflexivity. }
                       rewrite HxA3'.
                       assert (HxA4: get_assigned_value A4 u = None).
                       { destruct (is_assigned A4 u) as [|] eqn:HxA4.
                         - assert (Hmem: node_in_path u (h, v, t) = true).
                           { apply A4_nodes_in_path with (G := G). apply assigned_true_then_in_list with (A := A4). split. apply HxA4. unfold nodes. rewrite <- HA4ind.
                             apply HA4. }
                           rewrite Hmem in Humem. discriminate Humem.
                         - apply assigned_is_false. apply HxA4. }
                       rewrite HxA4.
                       assert (HxAZ: get_assigned_value AZ u = None).
                       { destruct (is_assigned AZ u) as [|] eqn:HxAZ.
                         - assert (Hmem: In u Z).
                           { apply assigned_true_then_in_list with (A := AZ). split. apply HxAZ. apply HAZ. }
                           exfalso. apply HuZ. apply Hmem.
                         - apply assigned_is_false. apply HxAZ. }
                       rewrite HxAZ. simpl. rewrite eqb_refl. reflexivity. }
                   { rewrite remove_assignment_preserves_other_nodes. simpl. rewrite Hux. reflexivity. apply Hux. }
                ** apply is_path_in_graph_induction with (u := u). apply Hp.
                ** apply acyclic_path_cat with (u := u). apply Hcyc.
                ** apply edge_out_not_in_Z with (u := u) (v := v) (t := t) (G := G). apply Hconn.
                   left. apply Hin. apply Hp.
                ** apply descendant_paths_disjoint_cat with (u := u). apply Hdesc. intros Hhcol.
                   assert (HA2h: In h (get_A2_binded_nodes_in_g_path G (u, v, h :: t))). { unfold get_A2_binded_nodes_in_g_path. apply Hhcol. }
                   apply A2_nodes_not_in_A1 in HA2h. apply HA2h. apply HA1h. apply HG. apply Hcyc. apply Hp.
                ** apply subpath_still_d_connected with (u := u). apply Hconn.
                ** apply forallb_true_iff_mem. intros w Hw.
                   apply assigned_is_true. rewrite remove_assignment_preserves_other_nodes. apply assigned_is_true.
                   apply forallb_true_iff_mem with (x := w) in HA1. apply HA1. unfold nodes in *. rewrite HA1ind. right. apply Hw.
                   destruct (u =? w) as [|] eqn:Huw. apply eqb_eq in Huw. rewrite <- Huw in *. apply A1_nodes_in_path in Hw.
                   rewrite node_in_path_equiv in Hw. exfalso. apply member_In_equiv in Hw. rewrite app_comm_cons in Hw. apply membership_append_or in Hw.
                   destruct Hw as [Hw | Hw]. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. apply Hw. destruct Hw as [Hw | Hw]. destruct Hcyc as [Hcyc _]. apply Hcyc. symmetry. apply Hw.
                   apply Hw. reflexivity.
                ** unfold A1_nodes_binded_to_parent_in_path. intros m i Hmi.
                   assert (Hum: u =? m = false).
                   { apply filter_true in Hmi. simpl in Hmi. destruct (u =? m) as [|] eqn:Hum. rewrite eqb_sym in Hum. rewrite Hum in Hmi. simpl in Hmi. destruct Hmi as [_ Hmi]. discriminate Hmi.
                     reflexivity. }
                   assert (Hmi': In (m, i) A1). { apply filter_true in Hmi. apply Hmi. }
                   destruct (m =? h) as [|] eqn:Hmh.
                   --- apply assigned_is_true in HA1h'. destruct HA1h' as [ih HA1h']. apply get_assigned_In in HA1h'.
                       assert (Hih': ih = i). { apply each_node_assigned_once_eq with (A := A1) (u := h). apply HA1h'. apply eqb_eq in Hmh. rewrite <- Hmh. apply Hmi'. apply HA1''. }
                       rewrite <- Hih' in *.
                       apply HA1bind in Hmi'. destruct Hmi' as [a' [Hai Hmi']]. apply HA1bind in HA1h'.
                       destruct HA1h' as [b [Hih HA1h']]. destruct HA1h' as [HA1h' | HA1h'].
                       *** (* contradiction, b = u, cycle *)
                           assert (Hwb: u = b).
                           { apply two_sublists_the_same_2 with (l := u :: h :: t ++ [v]) (a := h).
                             - rewrite Hav in Haxsub. simpl in Haxsub. apply Haxsub.
                             - apply HA1h'.
                             - apply acyclic_path_count with (x := h) in Hcyc. apply Hcyc. right. left. reflexivity. }

                           unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [HG' HG]]. apply contains_cycle_false_correct with (p := (h, h, [u])) in HG.
                           +++ unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
                           +++ simpl.

                               rewrite <- Hwb in Hih. apply nth_error_In in Hih. apply edge_from_parent_to_child in Hih. apply edge_in_graph_then_is_edge in Hih. rewrite Hih.
                               apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. apply edge_in_graph_then_is_edge in Haxix. rewrite <- Hav. rewrite Haxix.
                               reflexivity. apply HG'. apply HG'.
                       *** exists b. apply eqb_eq in Hmh. rewrite Hmh. split. apply Hih. right. simpl in HA1h'. rewrite eqb_sym in Huh. rewrite Huh in HA1h'. simpl in HA1h'. apply HA1h'.
                   --- apply HA1bind in Hmi'. destruct Hmi' as [a' [Hai Hmi']]. exists a'. split. apply Hai. simpl in Hmi'. rewrite Hmh in Hmi'. rewrite eqb_sym in Hum. rewrite Hum in Hmi'. simpl in Hmi'. rewrite andb_comm in Hmi'. simpl in Hmi'. simpl.
                       destruct Hmi' as [Hmi' | Hmi']. left. apply Hmi'. right. apply split_orb_true. right. apply Hmi'.
                ** unfold nodes in *. rewrite <- HA2ind. apply HA2.
                ** simpl. simpl in HA2ind. rewrite <- HA2ind. apply HA3.
                ** unfold nodes in *. rewrite <- HA4ind. apply HA4.
                ** unfold nodes in *. rewrite <- HA4ind. apply HeqUx.
                ** rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction_2. split. apply is_path_in_graph_induction with (u := u). apply Hp.
                   apply HG. apply Houth.
                ** apply assigned_is_true. rewrite remove_assignment_preserves_other_nodes. apply assigned_is_true. apply HA1h'. apply Huh.

      + assert (H4: exists (t4: nodes), get_A4_binded_nodes_in_g_path G (u, v, l) = u :: t4).
        { unfold get_A4_binded_nodes_in_g_path. rewrite Hin. destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
          exists (find_confounders_in_path (u, v, l) G ++ [v]). reflexivity.
          exists (find_confounders_in_path (u, v, l) G). reflexivity.
          apply path_out_of_end_Some in Hout. exfalso. apply Hout. }
        destruct H4 as [t4 H4]. rewrite H4 in *.
        apply HA4_const. 2: { apply HUxA. } 2: { rewrite HeqUx. simpl. rewrite eqb_refl. reflexivity. }

        apply assigned_is_true. apply assigned_has_value with (L := u :: t4). split. left. reflexivity. apply HA4. }

      split.
      { rewrite equiv_list_assignments_length with (L' := (tl
                  (get_assignment_sequence_from_A4
                     (get_A4_binded_nodes_in_g_path G (u, v, l)) U' x))). 2: { apply HeqLUx. }
        assert (Hlen: length (get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G (u, v, l)) U' x) <= path_length (u, v, l)).
        { apply assignment_sequence_len_shorter_than_path with (G := G) (x := x) (U := U'). apply Hp. apply HG.
          reflexivity. }
        assert (Hlen': length (tl (get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G (u, v, l)) U' x)) <= length (get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G (u, v, l)) U' x)).
        { destruct (get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G (u, v, l)) U' x) as [| h' t']. simpl. lia. simpl. lia. } unfold nodes in *.
        lia. }

      split.
      { unfold sequence_of_ancestors_change_for_Z. split.
        - unfold assignments_change_only_for_subset. intros w. split.
          + assert (Hass: is_assigned Ux w = is_assigned ((hd 0 (get_A4_binded_nodes_in_g_path G (u, v, l)),
            x) :: U') w). { apply equiv_assignments_assigned. apply HeqUx. }
            rewrite Hass. apply is_assigned_iff_cat. apply assigned_is_true. apply assigned_has_value with (L := nodes_in_graph G).
            split.
            destruct (get_A4_binded_nodes_in_g_path G (u, v, l)) as [| h4 t4] eqn:H4. apply A4_has_nodes in H4. exfalso. apply H4.
            apply Hp. simpl.
            assert (Hh4: node_in_graph h4 G = true). { apply A4_nodes_in_graph with (u := u) (v := v) (l := l). apply HG. apply Hp.
              unfold nodes in *. rewrite H4. left. reflexivity. }
            destruct G as [V E]. simpl. apply member_In_equiv. simpl in Hh4. apply Hh4. apply HUA.
          + intros Hwmem. destruct (hd 0 (get_A4_binded_nodes_in_g_path G (u, v, l)) =? w) as [|] eqn:Huw.
            * apply eqb_eq in Huw. exfalso. apply Hwmem. apply intersect_in_both_lists. split.
              -- destruct (get_A4_binded_nodes_in_g_path G (u, v, l)) as [| h4 t4] eqn:H4. apply A4_has_nodes in H4. exfalso. apply H4.
                 apply Hp. simpl in Huw. apply member_In_equiv. rewrite <- node_in_path_equiv with (l := l).
                 apply A4_nodes_in_path with (G := G). unfold nodes in *. rewrite H4. left. apply Huw.
              -- rewrite <- Huw. apply next_A4_node_is_unblocked_ancestor_2. apply Hp. apply HG.
                 apply Hp. apply Hconn. apply HvZ.
            * unfold assignments_equiv in HeqUx. specialize HeqUx with (u := w).
              remember (hd 0 (get_A4_binded_nodes_in_g_path G (u, v, l))) as x4. simpl in HeqUx. rewrite Huw in HeqUx.
              symmetry. apply HeqUx.
       - remember (tl (get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G (u, v, l)) U' x)) as Lt.
         assert (HA4bind: get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G (u, v, l)) U' x = ((hd 0 (get_A4_binded_nodes_in_g_path G (u, v, l)),
            x) :: U') :: Lt).
         { destruct (get_A4_binded_nodes_in_g_path G (u, v, l)) as [| h4 t4] eqn:H4. apply A4_has_nodes in H4. exfalso. apply H4.
           apply Hp. simpl. rewrite HeqLt. simpl. reflexivity. }
         split.
         + apply equiv_assignments_preserve_anc with (L := U' :: ((hd 0 (get_A4_binded_nodes_in_g_path G (u, v, l)),
            x) :: U') :: Lt).
           * simpl. split. unfold assignments_equiv. intros u'. reflexivity. split. apply assignments_equiv_symmetry. apply HeqUx.
             apply list_assignments_equiv_symmetry. apply HeqLUx.
           * apply assignments_change_A4 with (x := x) (p := (u, v, l)). apply HG. apply HG. simpl. split. apply HuZ. apply HvZ.
             apply Hp. apply Hp. apply Hconn. apply HAZ.
             apply Hrx. apply HA4bind. apply HUA.
         + intros U HUmem.
           destruct HUmem as [HUmem | [HUmem | HUmem]].
           * rewrite <- HUmem. apply HUA.
           * rewrite <- HUmem. apply HUxA.
           * apply list_equiv_assignment_still_assignment with (L := LUx) (L' := Lt). apply HeqLUx.
             intros Ut HUt. apply assignment_sequence_U with (A4 := get_A4_binded_nodes_in_g_path G (u, v, l)) (U := U') (L := ((hd 0 (get_A4_binded_nodes_in_g_path G (u, v, l)),
            x) :: U') :: Lt) (x := x).
             apply HA4bind. apply HUA. right. apply HUt. apply HUmem. }

      remember (last (Ux :: LUx) Ux) as U.
      assert (HU: is_assignment_for U (nodes_in_graph G) = true).
      { destruct LUx as [| U1 LUx']. simpl in HeqU. rewrite HeqU. apply HUxA.

        remember (tl (get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G (u, v, l)) U' x)) as Lt.
         assert (HA4bind: get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G (u, v, l)) U' x = ((hd 0 (get_A4_binded_nodes_in_g_path G (u, v, l)),
            x) :: U') :: Lt).
         { destruct (get_A4_binded_nodes_in_g_path G (u, v, l)) as [| h4 t4] eqn:H4. apply A4_has_nodes in H4. exfalso. apply H4.
           apply Hp. simpl. rewrite HeqLt. simpl. reflexivity. }
         apply list_equiv_assignment_still_assignment with (L := U1 :: LUx') (L' := Lt). apply HeqLUx.
             intros Ut HUt. apply assignment_sequence_U with (A4 := get_A4_binded_nodes_in_g_path G (u, v, l)) (U := U') (L := ((hd 0 (get_A4_binded_nodes_in_g_path G (u, v, l)),
            x) :: U') :: Lt) (x := x).
             apply HA4bind. apply HUA. right. apply HUt. rewrite HeqU. apply last_mem. }

      assert (HUA4: forall u4 : node, is_assigned A4 u4 = true -> get_assigned_value U u4 = Some x).
      { intros a Ha. rewrite HeqU. apply assignments_seq_nodes_map_to_x with (U := U') (A := get_A4_binded_nodes_in_g_path G (u, v, l)).
        + destruct (get_A4_binded_nodes_in_g_path G (u, v, l)) as [| h4 t4] eqn:H4.
          ** apply A4_has_nodes in H4. exfalso. apply H4. apply Hp.
          ** simpl. split. simpl in HeqUx. apply HeqUx. simpl in HeqLUx. apply HeqLUx.
        + destruct (member a (get_A4_binded_nodes_in_g_path G (u, v, l))) as [|] eqn:Hmem.
          ** apply member_In_equiv. apply Hmem.
          ** apply HA4 in Hmem. rewrite Ha in Hmem. discriminate Hmem. }

      assert (Hw_last_U: (forall w : node, node_in_path w (u, v, l) = true /\ ~ In w (find_colliders_in_path (u, v, l) G)
                    -> find_value G g w (last (Ux :: LUx) Ux) [] = Some x)).
      { (* show that all nodes in A1 evaluate to x (since they are tied to their parents, which becomes a chain that
           must eventually end at a node in A4) *)
        rewrite <- HeqU. intros w Hw'. apply Hw. apply HU.
        apply HUA4. apply Hw'. }

      split. 2: { rewrite HeqU. apply Hw_last_U. }

      apply HcondU with (x := x). apply HU. apply HUA4.
Qed.
