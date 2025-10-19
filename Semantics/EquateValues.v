From Semantics Require Import FunctionRepresentation.
From Semantics Require Import FindValue.
From Semantics Require Import NodeCategorization.
From Semantics Require Import ColliderDescendants.
From CausalDiagrams Require Import Assignments.
From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import CausalPaths.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import Basics.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

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
