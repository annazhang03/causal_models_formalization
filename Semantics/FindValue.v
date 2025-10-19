From Semantics Require Import FunctionRepresentation.
From CausalDiagrams Require Import Assignments.
(* From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import DSeparation. *)
From DAGs Require Import Basics.
From DAGs Require Import TopologicalSort.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
(* From DAGs Require Import PathFinding. *)
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.
From Utils Require Import EqType.

(* returns None if some parent hasn't been assigned a value, else returns list of assignments *)
Fixpoint get_parent_assignments {X: Type} (A: assignments X) (P: nodes) : option (list X) :=
  match P with
  | [] => Some []
  | h :: t => match (get_assigned_value A h) with
              | Some x => match (get_parent_assignments A t) with
                          | Some l => Some (x :: l)
                          | None => None
                          end
              | None => None
              end
  end.

Lemma parent_assignments_exist: forall X (A: assignments X) (P: nodes),
  is_assignment_for A P = true -> exists L: list X, Some L = get_parent_assignments A P.
Proof.
  intros X A P H.
  induction P as [| h t IH].
  - simpl. exists []. reflexivity.
  - simpl in H. apply split_and_true in H. destruct H as [Hh Hind].
    assert (Hhx: exists x: X, get_assigned_value A h = Some x).
    { apply assigned_has_value with (L := h :: t). split.
      - simpl. left. reflexivity.
      - simpl. rewrite Hh. rewrite Hind. reflexivity. }
    destruct Hhx as [x Hhx].
    simpl. rewrite Hhx.
    apply IH in Hind. destruct Hind as [L Hind].
    exists (x :: L). rewrite <- Hind. reflexivity.
Qed.

Lemma parent_assignments_preserves_index: forall X (P: assignments X) (V: nodes) (p: list X) 
                                              (i: nat) (x: X) (m: node),
  (get_parent_assignments P V = Some p /\ index V m = Some i /\ get_assigned_value P m = Some x)
  -> nth_error p i = Some x.
Proof.
  intros X P V p i x m [Hp [Hi Hm]].
  generalize dependent p. generalize dependent i. induction V as [| h t IH].
  - intros i Hi p Hp. simpl in Hi. discriminate Hi.
  - intros i Hi p Hp. simpl in Hi. destruct (h =? m) as [|] eqn:Hhm.
    + inversion Hi. simpl in Hp. apply eqb_eq in Hhm. rewrite Hhm in Hp. rewrite Hm in Hp.
      destruct (get_parent_assignments P t) as [l|].
      * inversion Hp. simpl. reflexivity.
      * discriminate Hp.
    + destruct (index t m) as [i'|].
      * inversion Hi. simpl in Hp. destruct (get_assigned_value P h) as [vh|].
        -- destruct (get_parent_assignments P t) as [l|].
           ++ inversion Hp. simpl. specialize IH with (i := i') (p := l).
              apply IH. reflexivity. reflexivity.
           ++ discriminate Hp.
        -- discriminate Hp.
      * discriminate Hi.
Qed.

(* A = assigned assignments, A_eval = evaluated assignments *)
Definition get_value_of_node {X: Type} (u: node) (G: graph) (g: graphfun) (U A A_eval: assignments X) : option X :=
  match (get_assigned_value A u) with
  | Some x => (* value already assigned *) Some x
  | None => (* find value of parents and use node function *)
            match (get_assigned_value U u) with
            | Some unobs => match (get_parent_assignments A_eval (find_parents u G)) with
                            | Some p => Some ((g u) (unobs, p))
                            | None => None (* won't reach this, contradicts topo correctness *)
                            end
            | None => None (* error, U needs to have unobserved value of all nodes *)
            end
  end.

Lemma value_exists_if_parents_are_assigned: forall X (u: node) (G: graph) (g: graphfun) (U A A_eval: assignments X),
  is_assignment_for A_eval (find_parents u G) = true /\ is_assignment_for U (nodes_in_graph G) = true
  /\ node_in_graph u G = true
  -> exists x: X, get_value_of_node u G g U A A_eval = Some x.
Proof.
  intros X u [V E] g U A A_eval [Hsf [HU Hu]].
  unfold get_value_of_node. destruct (get_assigned_value A u) as [x|] eqn:HA.
  - exists x. reflexivity.
  - assert (HUu: exists hu: X, get_assigned_value U u = Some hu).
    { apply assigned_has_value with (L := V). split.
      - simpl in Hu. apply member_In_equiv. apply Hu.
      - simpl in HU. apply HU. }
    destruct HUu as [hu HUu]. rewrite HUu.
    assert (HP: exists p, Some p = get_parent_assignments A_eval (find_parents u (V, E))).
    { apply parent_assignments_exist. apply Hsf. }
    destruct HP as [p HP].
    rewrite <- HP. exists (g u (hu, p)). reflexivity.
Qed.

Lemma value_same_if_parents_are_same:
  forall X (u: node) (G: graph) (g: graphfun) (U1 U2 A1 A2 V1 V2: assignments X),
  is_assignment_for V1 (find_parents u G) = true /\ is_assignment_for V2 (find_parents u G) = true
  /\ is_assignment_for U1 (nodes_in_graph G) = true /\ is_assignment_for U2 (nodes_in_graph G) = true
  /\ get_assigned_value U1 u = get_assigned_value U2 u
  /\ get_assigned_value A1 u = get_assigned_value A2 u
  /\ (forall (v: node), In v (find_parents u G) -> get_assigned_value V1 v = get_assigned_value V2 v)
  /\ node_in_graph u G = true
  -> get_value_of_node u G g U1 A1 V1 = get_value_of_node u G g U2 A2 V2.
Proof.
  intros X u [V E] g U1 U2 A1 A2 V1 V2.
  intros [HV1 [HV2 [HU1 [HU2 [HU [HA [Hv Hu]]]]]]].
  unfold get_value_of_node. rewrite <- HA.
  destruct (get_assigned_value A1 u) as [x|] eqn:HA1.
  - reflexivity.
  - rewrite <- HU. assert (HUu: exists hu: X, get_assigned_value U1 u = Some hu).
    { apply assigned_has_value with (L := V). split.
      - simpl in Hu. apply member_In_equiv. apply Hu.
      - simpl in HU1. apply HU1. }
    destruct HUu as [hu HUu]. rewrite HUu.
    assert (HP: exists p, Some p = get_parent_assignments V1 (find_parents u (V, E))).
    { apply parent_assignments_exist. apply HV1. }
    destruct HP as [p HP].
    assert (HP2: get_parent_assignments V2 (find_parents u (V, E)) = Some p).
    { generalize dependent p. induction (find_parents u (V, E)) as [| h t IH].
      - intros p HP. simpl. simpl in HP. inversion HP. reflexivity.
      - intros p HP. simpl in HP. destruct (get_assigned_value V1 h) as [a|] eqn:Hh.
        + simpl. assert (Hh2: get_assigned_value V2 h = Some a).
          { rewrite <- Hh. symmetry. specialize Hv with (v := h). apply Hv. simpl. left. reflexivity. }
          rewrite Hh2. destruct (get_parent_assignments V1 t) as [l|] eqn:Hl.
          * specialize IH with (p := l).
            assert (Hl2: get_parent_assignments V2 t = Some l).
            { apply IH.
              - simpl in HV1. apply split_and_true in HV1. destruct HV1 as [_ HV1]. apply HV1.
              - simpl in HV2. apply split_and_true in HV2. destruct HV2 as [_ HV2]. apply HV2.
              - intros v Hmem. apply Hv. simpl. right. apply Hmem.
              - reflexivity. }
            rewrite Hl2. symmetry. apply HP.
          * discriminate HP.
        + discriminate HP. }
    rewrite <- HP. rewrite HP2. reflexivity.
Qed.

Fixpoint get_values_from_topo_sort {X: Type} (ts: nodes) (G: graph) (g: graphfun) (U: assignments X)
                                   (A: assignments X) (A_eval: assignments X) : option (assignments X) :=
  match ts with
  | [] => Some A_eval
  | u :: ts' => match (get_value_of_node u G g U A A_eval) with
                | Some x => get_values_from_topo_sort ts' G g U A (add_assignment A_eval u x)
                | None => None
                end
  end.

Fixpoint get_values_from_topo_sort_2 {X: Type} (ts: nodes) (G: graph) (g: graphfun) (U: assignments X)
                                     (A_eval: assignments X) : option (assignments X) :=
  match ts with
  | [] => Some []
  | u :: ts' => match (get_value_of_node u G g U [] A_eval) with
                | Some x => match (get_values_from_topo_sort_2 ts' G g U (add_assignment A_eval u x)) with
                            | Some r => Some ((u, x) :: r)
                            | None => None
                            end
                | None => None
                end
  end.

Lemma get_values_ts_2_preserves_length {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U Ae V: assignments X),
  get_values_from_topo_sort_2 ts G g U Ae = Some V
  -> length V = length ts.
Proof.
  intros ts G g U Ae V HV.
  generalize dependent Ae. generalize dependent ts. induction V as [| h t IH].
  - intros ts Ae HV. destruct ts as [| hts tts].
    + reflexivity.
    + simpl in HV. destruct (get_value_of_node hts G g U [] Ae) as [x|] eqn:Hx.
      * destruct (get_values_from_topo_sort_2 tts G g U (add_assignment Ae hts x)) as [r|] eqn:Hr.
        -- inversion HV.
        -- discriminate HV.
      * discriminate HV.
  - intros ts Ae HV. destruct ts as [| hts tts].
    + simpl in HV. inversion HV.
    + simpl in HV. destruct (get_value_of_node hts G g U [] Ae) as [x|].
      * destruct (get_values_from_topo_sort_2 tts G g U (add_assignment Ae hts x)) as [r|] eqn:Hr.
        -- inversion HV. simpl. f_equal.
           specialize IH with (ts := tts) (Ae := (add_assignment Ae hts x)). apply IH. rewrite <- H1. apply Hr.
        -- discriminate HV.
      * discriminate HV.
Qed.

Lemma get_values_ts_2_preserves_index {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U Ae: assignments X) (u: node),
  forall (i: nat) (V: assignments X), nth_error ts i = Some u
  -> get_values_from_topo_sort_2 ts G g U Ae = Some V
  -> exists (x: X), nth_error V i = Some (u, x).
Proof.
  intros ts G g U Ae u i V Hi HV.
  generalize dependent ts. generalize dependent V. generalize dependent Ae. induction i as [| i' IH].
  - intros Ae V ts Hi HV. destruct ts as [| h t].
    + simpl in Hi. discriminate Hi.
    + simpl in Hi. inversion Hi. rewrite H0 in *. simpl in HV.
      destruct (get_value_of_node u G g U [] Ae) as [x|].
      * destruct (get_values_from_topo_sort_2 t G g U (add_assignment Ae u x)) as [r|].
        -- inversion HV. exists x. simpl. reflexivity.
        -- discriminate HV.
      * discriminate HV.
  - intros Ae V ts Hi HV. destruct ts as [| h t].
    + simpl in Hi. discriminate Hi.
    + simpl in Hi. simpl in HV. destruct (get_value_of_node h G g U [] Ae) as [xh|].
      * destruct (get_values_from_topo_sort_2 t G g U (add_assignment Ae h xh)) as [r|] eqn:Hr.
        -- specialize IH with (V := r) (ts := t) (Ae := add_assignment Ae h xh).
           assert (Hind: exists x : X, nth_error r i' = Some (u, x)).
           { apply IH. apply Hi. apply Hr. }
           destruct Hind as [x Hux]. exists x.
           inversion HV. simpl. apply Hux.
        -- discriminate HV.
      * discriminate HV.
Qed.

Lemma get_values_ts_2_preserves_index_rev {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U Ae: assignments X) (u: node),
  forall (i: nat) (V: assignments X) (x: X),
  get_values_from_topo_sort_2 ts G g U Ae = Some V /\ nth_error V i = Some (u, x)
  -> nth_error ts i = Some u.
Proof.
  intros ts G g U Ae u i V x [HV Hi].
  generalize dependent ts. generalize dependent V. generalize dependent Ae. induction i as [| i' IH].
  - intros Ae V Hi ts HV. destruct V as [| h t].
    + simpl in Hi. discriminate Hi.
    + simpl in Hi. inversion Hi. rewrite H0 in *. destruct ts as [| hts tts].
      * simpl in HV. inversion HV.
      * simpl in HV. destruct (get_value_of_node hts G g U [] Ae) as [htsx|].
        -- destruct (get_values_from_topo_sort_2 tts G g U (add_assignment Ae hts htsx)) as [r|].
           ++ inversion HV. simpl. reflexivity.
           ++ discriminate HV.
        -- discriminate HV.
  - intros Ae V Hi ts HV. destruct V as [| h t].
    + simpl in Hi. discriminate Hi.
    + simpl in Hi. destruct ts as [| hts tts].
      * simpl in HV. inversion HV.
      * simpl in HV. destruct (get_value_of_node hts G g U [] Ae) as [htsx|].
        -- destruct (get_values_from_topo_sort_2 tts G g U (add_assignment Ae hts htsx)) as [r|] eqn:Hr.
           ++ inversion HV. simpl. specialize IH with (ts := tts) (Ae := add_assignment Ae hts htsx) (V := r).
              apply IH. rewrite H1. apply Hi. easy.
           ++ discriminate HV.
        -- discriminate HV.
Qed.

Lemma get_values_ts_2_get_value_node {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U Ae: assignments X) (u: node),
  forall (i: nat) (V: assignments X), nth_error ts i = Some u
  -> get_values_from_topo_sort_2 ts G g U Ae = Some V
  -> exists (x: X) (V': assignments X),
       get_value_of_node u G g U [] (Ae ++ V') = Some x
       /\ first_n V i = Some V'
       /\ nth_error V i = Some (u, x).
Proof.
  intros ts G g U Ae u i V Hi HV.
  generalize dependent ts. generalize dependent V. generalize dependent Ae. induction i as [| i' IH].
  - intros Ae V ts Hi HV. destruct ts as [| h t].
    + simpl in Hi. discriminate Hi.
    + simpl in Hi. inversion Hi. rewrite H0 in *. simpl in HV.
      destruct (get_value_of_node u G g U [] Ae) as [x|] eqn:Hx.
      * destruct (get_values_from_topo_sort_2 t G g U (add_assignment Ae u x)) as [r|].
        -- inversion HV. exists x. exists []. repeat split. rewrite append_identity. apply Hx.
        -- discriminate HV.
      * discriminate HV.
  - intros Ae V ts Hi HV. destruct ts as [| h t].
    + simpl in Hi. discriminate Hi.
    + simpl in Hi. simpl in HV. destruct (get_value_of_node h G g U [] Ae) as [xh|] eqn:Hxh.
      * destruct (get_values_from_topo_sort_2 t G g U (add_assignment Ae h xh)) as [r|] eqn:Hr.
        -- specialize IH with (V := r) (ts := t) (Ae := add_assignment Ae h xh).
           assert (Hind: exists (x : X) (V' : assignments X),
                         get_value_of_node u G g U [] (add_assignment Ae h xh ++ V') = Some x /\
                         first_n r i' = Some V' /\ nth_error r i' = Some (u, x)).
           { apply IH. apply Hi. apply Hr. }
           destruct Hind as [x [V' [Hx [Hi' Hux]]]].
           exists x. exists ((h, xh) :: V'). repeat split.
           ++ unfold add_assignment in Hx. rewrite append_vs_concat_X in Hx. apply Hx.
           ++ inversion HV. simpl. rewrite Hi'. reflexivity.
           ++ inversion HV. simpl. apply Hux.
        -- discriminate HV.
      * discriminate HV.
Qed.

Lemma get_values_from_topo_sort_equiv_helper {X: Type}: forall (G: graph) (g: graphfun) (tsp tss: nodes) (U A_eval V1: assignments X),
  topological_sort G = Some (tsp ++ tss)
  -> get_values_from_topo_sort (tss) G g U [] A_eval = Some V1
  -> exists (V2: assignments X), get_values_from_topo_sort_2 (tss) G g U A_eval = Some V2
  /\ V1 = A_eval ++ V2.
Proof.
  intros G g tsp tss U Ae V1 Hts HV1.
  generalize dependent tsp. generalize dependent Ae. induction tss as [| h t IH].
  - intros Ae HV1 tsp Hts. simpl in HV1. exists []. simpl. split. reflexivity. inversion HV1. symmetry. apply append_identity.
  - intros Ae HV1 tsp Hts. simpl in HV1. simpl.
    destruct (get_value_of_node h G g U [] Ae) as [x|] eqn:Hh.
    + specialize IH with (Ae := add_assignment Ae h x) (tsp := tsp ++ [h]).
      assert (Hind: exists V2 : assignments X,
         get_values_from_topo_sort_2 t G g U (add_assignment Ae h x) = Some V2 /\
         V1 = add_assignment Ae h x ++ V2).
      { apply IH.
        - apply HV1.
        - rewrite append_vs_concat_X. apply Hts. }
      destruct Hind as [r [Hr Hind]].
      exists ((h, x) :: r). rewrite Hr. split. reflexivity.
      unfold add_assignment in Hind. rewrite append_vs_concat_X in Hind. apply Hind.
    + discriminate HV1.
Qed.


Definition get_values {X: Type} (G: graph) (g: graphfun) (U A: assignments X) : option (assignments X) :=
  match (topological_sort G) with
  | Some ts => get_values_from_topo_sort ts G g U A []
  | None => None (* graph is cyclic *)
  end.

Lemma assigned_if_in_A_eval: forall X (ts: nodes) (G: graph) (g: graphfun) (U A A_eval values: assignments X) (u: node),
  get_values_from_topo_sort ts G g U A A_eval = Some values /\ is_assigned A_eval u = true ->
  is_assigned values u = true.
Proof.
  intros X ts G g U A A_eval values u.
  intros [H1 H2].
  generalize dependent A_eval. induction ts as [| h t IH].
  - intros A_eval H1 H2. simpl in H1. inversion H1. rewrite <- H0. apply H2.
  - intros A_eval H1 H2. simpl in H1. unfold get_value_of_node in H1.
    destruct (get_assigned_value A h) as [x|] eqn:HA.
    + specialize IH with (A_eval := (add_assignment A_eval h x)).
      apply IH.
      * apply H1.
      * unfold add_assignment. apply is_assigned_app. apply H2.
    + destruct (get_assigned_value U h) as [unobs|] eqn:HU.
      * destruct (get_parent_assignments A_eval (find_parents h G)) as [p|] eqn:HP.
        -- specialize IH with (A_eval := (add_assignment A_eval h (g h (unobs, p)))).
           apply IH.
           ++ apply H1.
           ++ unfold add_assignment. apply is_assigned_app. apply H2.
        -- discriminate H1.
      * discriminate H1.
Qed.

Lemma get_assigned_if_in_A_eval:
  forall X (ts: nodes) (G: graph) (g: graphfun) (U A A_eval values: assignments X) (u: node) (x: X),
  get_values_from_topo_sort ts G g U A A_eval = Some values /\ get_assigned_value A_eval u = Some x ->
  get_assigned_value values u = Some x.
Proof.
  intros X ts G g U A A' values u x.
  intros [Hts HA'].
  generalize dependent A'. induction ts as [| h t IH].
  - intros A' Hts HA'. simpl in Hts. inversion Hts. rewrite <- H0. apply HA'.
  - intros A' Hts HA'. simpl in Hts. destruct (get_value_of_node h G g U A A') as [hv|] eqn:Hhv.
    + specialize IH with (A' := (add_assignment A' h hv)). apply IH.
      * apply Hts.
      * unfold add_assignment. apply get_assigned_app_Some with (A2 := [(h, hv)]) in HA'.
        apply HA'.
    + discriminate Hts.
Qed.

Lemma get_values_exists_then_all_nodes_assigned_helper: forall X (ts: nodes) (G: graph) (g: graphfun)
  (U A A_eval values: assignments X),
  topological_sort G = Some ts /\ get_values_from_topo_sort ts G g U A A_eval = Some values
  -> is_assignment_for values (nodes_in_graph G) = true.
Proof.
  intros X ts G g U A A_eval values [Hts H].
  unfold is_assignment_for. apply forallb_true_iff_mem. intros u Hmem.
  assert (Huts: In u ts).
  { apply topo_sort_contains_nodes with (u := u) in Hts as Hu.
    apply Hu. destruct G as [V E]. simpl. simpl in Hmem. apply member_In_equiv. apply Hmem. }
  clear Hts.
  generalize dependent values. generalize dependent A_eval. induction ts as [| h t IH].
  + exfalso. apply Huts.
  + intros A_eval values H. simpl in Huts. destruct Huts as [Huh | Hut].
    * simpl in H. unfold get_value_of_node in H. destruct (get_assigned_value A u) as [x|] eqn:Hassigned.
      -- rewrite <- Huh in Hassigned. rewrite Hassigned in H. unfold add_assignment in H.
         apply assigned_if_in_A_eval with (ts := t) (G := G) (g := g) (U := U) (A := A) (A_eval := A_eval ++ [(h, x)]).
         split.
         ++ apply H.
         ++ rewrite <- Huh. apply is_assigned_app2. simpl. rewrite eqb_refl. simpl. reflexivity.
      -- rewrite <- Huh in Hassigned. rewrite Hassigned in H.
         destruct (get_assigned_value U h) as [unobs|] eqn:HU.
         ++ destruct (get_parent_assignments A_eval (find_parents h G)) as [p|] eqn:HP.
            ** unfold add_assignment in H.
               apply assigned_if_in_A_eval with (ts := t) (G := G) (g := g) (U := U) (A := A) (A_eval := A_eval ++ [(h, g h (unobs, p))]).
               split.
              { apply H. } { rewrite <- Huh. apply is_assigned_app2. simpl. rewrite eqb_refl. simpl. reflexivity. }
            ** discriminate H.
         ++ discriminate H.
    * simpl in H. unfold get_value_of_node in H. destruct (get_assigned_value A h) as [x|] eqn:HA.
      -- unfold add_assignment in H. specialize IH with (A_eval := (A_eval ++ [(h, x)])) (values := values).
         apply IH. apply Hut. apply H.
      -- destruct (get_assigned_value U h) as [Uh|] eqn:HU.
         ++ destruct (get_parent_assignments A_eval (find_parents h G)) as [p|] eqn:HP.
            ** specialize IH with (A_eval := (add_assignment A_eval h (g h (Uh, p)))) (values := values).
               apply IH. apply Hut. apply H.
            ** discriminate H.
         ++ discriminate H.
Qed.

Theorem get_values_exists_then_all_nodes_assigned: forall X (G: graph) (g: graphfun) (U A values: assignments X),
  get_values G g U A = Some values -> is_assignment_for values (nodes_in_graph G) = true.
Proof.
  intros X G g U A values H. destruct (topological_sort G) as [ts|] eqn:Hts.
  - apply get_values_exists_then_all_nodes_assigned_helper with (ts := ts) (g := g) (U := U) (A := A) (A_eval := []).
    split. apply Hts. unfold get_values in H. rewrite Hts in H. apply H. 
  - unfold get_values in H. rewrite Hts in H. discriminate H.
Qed.

Lemma get_values_only_dependent_on_parents_helper:
  forall X (G: graph) (ts_pre ts_suff: nodes) (u: node) (g: graphfun)
           (U1 U2 A1 A2 A1' A2' V1 V2: assignments X),
  G_well_formed G = true /\ topological_sort G = Some (ts_pre ++ ts_suff) /\ node_in_graph u G = true ->
  get_values_from_topo_sort ts_suff G g U1 A1 A1' = Some V1
  /\ get_values_from_topo_sort ts_suff G g U2 A2 A2' = Some V2
  /\ is_assignment_for A1' ts_pre = true /\ is_assignment_for A2' ts_pre = true
  /\ get_assigned_value A1' u = get_assigned_value A2' u /\ True
  /\ get_assigned_value U1 u = get_assigned_value U2 u
  /\ is_assignment_for U1 (nodes_in_graph G) = true /\ is_assignment_for U2 (nodes_in_graph G) = true
  /\ get_assigned_value A1 u = get_assigned_value A2 u
  /\ (forall (v: node), In v (find_parents u G)
          -> get_assigned_value V1 v = get_assigned_value V2 v) ->
  get_assigned_value V1 u = get_assigned_value V2 u.
Proof.
  intros X G tsp tss u g U1 U2 A1 A2 A1' A2' V1 V2.
  intros [Hwf [Hts Hu]] [HV1 [HV2 [HA1' [HA2' [HA1u [HA2u [HU [HU1 [HU2 [HA HP]]]]]]]]]].
  generalize dependent V1. generalize dependent V2. generalize dependent tsp.
  generalize dependent A1'. generalize dependent A2'.
  induction tss as [| h t IH].
  - intros A2' A1' HA1u. intros tsp Hts HA1' HA2' V2 HV2 V1 HV1 Hv.
    simpl in HV1. inversion HV1. rewrite <- H0.
    simpl in HV2. inversion HV2. rewrite <- H1.
    apply HA1u.
  - intros A2' A1' HA1u. intros tsp Hts HA1' HA2' V2 HV2 V1 HV1 Hv.
    simpl in HV1. simpl in HV2.
    destruct (get_value_of_node h G g U1 A1 A1') as [hv1|] eqn:Hhv1.
    + destruct (get_value_of_node h G g U2 A2 A2') as [hv2|] eqn:Hhv2.
      * unfold add_assignment in HV1. unfold add_assignment in HV2.
        specialize IH with (A2' := (A2' ++ [(h, hv2)])) (A1' := (A1' ++ [(h, hv1)])).
        specialize IH with (tsp := tsp ++ [h]) (V2 := V2) (V1 := V1).
        apply IH.
        -- destruct (get_assigned_value A1' u) as [x|] eqn:Hx.
           ++ apply get_assigned_app_Some with (A2 := [(h, hv1)]) in Hx. rewrite Hx.
              symmetry in HA1u. apply get_assigned_app_Some with (A2 := [(h, hv2)]) in HA1u. rewrite HA1u.
              reflexivity.
           ++ apply get_assigned_app_None with (A2 := [(h, hv1)]) in Hx. rewrite Hx.
              symmetry in HA1u. apply get_assigned_app_None with (A2 := [(h, hv2)]) in HA1u. rewrite HA1u.
              (* if h=u, then hv1=hv2. *)
              destruct (h =? u) as [|] eqn:Hhu.
              ** assert (Hp: forall v: node, In v (find_parents u G) -> In v tsp).
                 { apply topo_sort_parents_before with (t := t). split. apply Hwf.
                   apply eqb_eq in Hhu. rewrite Hhu in Hts. apply Hts. }
                 unfold get_assigned_value. simpl. rewrite Hhu. apply eqb_eq in Hhu. 
                 assert (H: get_value_of_node u G g U1 A1 A1' = get_value_of_node u G g U2 A2 A2').
                 { apply value_same_if_parents_are_same. repeat split.
                 - unfold is_assignment_for. apply forallb_true_iff_mem. intros p Hmem.
                   specialize Hp with (v := p). apply Hp in Hmem.
                   apply assigned_is_true. apply assigned_has_value with (L := tsp). split.
                   + apply Hmem.
                   + apply HA1'.
                 - unfold is_assignment_for. apply forallb_true_iff_mem. intros p Hmem.
                   specialize Hp with (v := p). apply Hp in Hmem.
                   apply assigned_is_true. apply assigned_has_value with (L := tsp). split.
                   + apply Hmem.
                   + apply HA2'.
                 - apply HU1.
                 - apply HU2.
                 - apply HU.
                 - apply HA.
                 - intros p Hpmem. specialize Hv with (v := p).
                   assert (HA1p: exists x: X, get_assigned_value A1' p = Some x).
                   { apply assigned_has_value with (L := tsp). split.
                     - specialize Hp with (v := p). apply Hp. apply Hpmem.
                     - apply HA1'. }
                   destruct HA1p as [x1 HA1p]. rewrite HA1p.
                   assert (HV1p: get_assigned_value V1 p = Some x1).
                   { apply get_assigned_if_in_A_eval with (ts := t) (G := G) (g := g) (U := U1)
                                                          (A := A1) (A_eval := (A1' ++ [(h, hv1)])).
                     split. apply HV1. apply get_assigned_app_Some with (A2 := [(h, hv1)]) in HA1p.
                     apply HA1p. }
                   assert (HA2p: exists x: X, get_assigned_value A2' p = Some x).
                   { apply assigned_has_value with (L := tsp). split.
                     - specialize Hp with (v := p). apply Hp. apply Hpmem.
                     - apply HA2'. }
                   destruct HA2p as [x2 HA2p]. rewrite HA2p.
                   assert (HV2p: get_assigned_value V2 p = Some x2).
                   { apply get_assigned_if_in_A_eval with (ts := t) (G := G) (g := g) (U := U2)
                                                          (A := A2) (A_eval := (A2' ++ [(h, hv2)])).
                     split. apply HV2. apply get_assigned_app_Some with (A2 := [(h, hv2)]) in HA2p.
                     apply HA2p. }
                   apply Hv in Hpmem. rewrite HV1p in Hpmem. rewrite HV2p in Hpmem. apply Hpmem.
                 - apply Hu. }
                 rewrite <- Hhu in H. rewrite Hhv1 in H. rewrite Hhv2 in H.
                 apply H.
              ** simpl. rewrite Hhu. reflexivity.
        -- rewrite append_vs_concat. apply Hts.
        -- unfold is_assignment_for. apply forallb_true_iff_mem. intros x Hmem.
           apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
           ++ apply is_assigned_app. apply assigned_is_true. apply assigned_has_value with (L := tsp).
              split. apply Hmem. apply HA1'.
           ++ apply is_assigned_app2. apply assigned_is_true. apply assigned_has_value with (L := [h]).
              split. apply Hmem. simpl. rewrite eqb_refl. simpl. reflexivity.
        -- unfold is_assignment_for. apply forallb_true_iff_mem. intros x Hmem.
           apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
           ++ apply is_assigned_app. apply assigned_is_true. apply assigned_has_value with (L := tsp).
              split. apply Hmem. apply HA2'.
           ++ apply is_assigned_app2. apply assigned_is_true. apply assigned_has_value with (L := [h]).
              split. apply Hmem. simpl. rewrite eqb_refl. simpl. reflexivity.
        -- apply HV2.
        -- apply HV1.
        -- apply Hv.
      * discriminate HV2.
    + discriminate HV1.
Qed.

(* as long as u has the same error term,
   its parents have the same values,
   and it has either not been assigned or been assigned the same value,
   then it will have the same find_value *)
Theorem get_values_only_dependent_on_parents:
  forall X (G: graph) (u: node) (g: graphfun) (U1 U2 A1 A2 V1 V2: assignments X),
  G_well_formed G = true /\ node_in_graph u G = true ->
  get_values G g U1 A1 = Some V1 /\ get_values G g U2 A2 = Some V2 ->
  (forall (v: node), In v (find_parents u G) 
          -> get_assigned_value V1 v = get_assigned_value V2 v)
  /\ get_assigned_value U1 u = get_assigned_value U2 u
  /\ is_assignment_for U1 (nodes_in_graph G) = true /\ is_assignment_for U2 (nodes_in_graph G) = true
  /\ get_assigned_value A1 u = get_assigned_value A2 u ->
  get_assigned_value V1 u = get_assigned_value V2 u.
Proof.
  intros X G u g U1 U2 A1 A2 V1 V2.
  intros [Hwf Hu] [HV1 HV2] [Hp [HU [HU1 [HU2 HA]]]].
  unfold get_values in HV1. destruct (topological_sort G) as [ts|] eqn:Hts.
  - unfold get_values in HV2. rewrite Hts in HV2.
    apply get_values_only_dependent_on_parents_helper with (G := G) (ts_pre := []) (ts_suff := ts)
                    (g := g) (U1 := U1) (U2 := U2) (A1 := A1) (A2 := A2) (A1' := []) (A2' := []).
    + repeat split.
      * apply Hwf.
      * simpl. apply Hts.
      * apply Hu.
    + repeat split.
      * apply HV1.
      * apply HV2.
      * apply HU.
      * apply HU1.
      * apply HU2.
      * apply HA.
      * apply Hp.
  - discriminate HV1.
Qed.

Lemma get_values_existence_helper: forall X (ts_pre ts_suff: nodes) (G: graph) (g: graphfun) (U A A_eval: assignments X),
  G_well_formed G = true ->
  topological_sort G = Some (ts_pre ++ ts_suff) /\ is_assignment_for A_eval ts_pre = true /\
  is_assignment_for U (nodes_in_graph G) = true
  -> exists (values: assignments X), get_values_from_topo_sort ts_suff G g U A A_eval = Some values.
Proof.
  intros X tsp tss G g U A A_eval.
  intros Hwf [Hts [Hsf HU]].
  generalize dependent tsp. generalize dependent A_eval. induction tss as [| h t IH].
  - intros A_eval tsp Hts Hsf. simpl. exists A_eval. reflexivity.
  - intros A_eval tsp Hts Hsf. simpl.
    assert (Hh: exists x: X, get_value_of_node h G g U A A_eval = Some x).
    { apply value_exists_if_parents_are_assigned. repeat split.
      - assert (Hp: forall (p: node), In p (find_parents h G) -> In p tsp).
        { apply topo_sort_parents_before with (t := t). split. apply Hwf. apply Hts. }
        unfold is_assignment_for. apply forallb_true_iff_mem. intros p Hmem.
        specialize Hp with (p := p). apply Hp in Hmem.
        apply assigned_is_true. apply assigned_has_value with (L := tsp). split.
        + apply Hmem.
        + apply Hsf.
      - apply HU.
      - apply topo_sort_contains_nodes with (u := h) in Hts. apply Hts.
        apply membership_append_r. simpl. left. reflexivity. }
    destruct Hh as [x Hh]. rewrite Hh.
    specialize IH with (A_eval := (add_assignment A_eval h x)) (tsp := tsp ++ [h]).
    apply IH.
    + rewrite Hts. f_equal. rewrite append_vs_concat. reflexivity.
    + unfold add_assignment. unfold is_assignment_for.
      apply forallb_true_iff_mem. intros v Hmem.
      apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
      * apply is_assigned_app. apply assigned_is_true. apply assigned_has_value with (L := tsp). split.
        -- apply Hmem.
        -- apply Hsf.
      * apply is_assigned_app2. apply assigned_is_true. apply assigned_has_value with (L := [h]). split.
        -- apply Hmem.
        -- simpl. rewrite eqb_refl. simpl. reflexivity.
Qed.

Theorem get_values_existence: forall X (G: graph) (g: graphfun) (U A: assignments X),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true ->
  exists (values: assignments X), get_values G g U A = Some values.
Proof.
  intros X G g U A. destruct G as [V E] eqn:HG.
  intros [Hwf Hcyc]. intros HU. simpl in HU. simpl.
  assert (Hts: exists ts: nodes, topological_sort G = Some ts).
  { apply topo_sort_exists_for_acyclic. split.
    - rewrite HG. apply Hwf.
    - rewrite HG. apply Hcyc. }
  destruct Hts as [ts Hts].
  unfold get_values. rewrite HG in Hts. rewrite Hts.
  apply get_values_existence_helper with (ts_pre := []).
  - apply Hwf.
  - repeat split.
    + rewrite Hts. simpl. reflexivity.
    + simpl. apply HU.
Qed.

Theorem get_values_from_topo_sort_equiv {X: Type}: forall (G: graph) (g: graphfun) (ts: nodes) (U: assignments X),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true ->
  topological_sort G = Some ts
  -> get_values G g U [] = get_values_from_topo_sort_2 ts G g U [].
Proof.
  intros G g ts U HG HU Hts.
  assert (HV: exists (V: assignments X), get_values G g U [] = Some V).
  { apply get_values_existence. easy. easy. }
  destruct HV as [V HV].
  assert (Hlem: exists (V2: assignments X), get_values_from_topo_sort_2 ts G g U [] = Some V2 /\ V = [] ++ V2).
  { apply get_values_from_topo_sort_equiv_helper with (tsp := []).
    - simpl. apply Hts.
    - unfold get_values in HV. rewrite Hts in HV. apply HV. }
  destruct Hlem as [V2 [HV2 HV']]. rewrite HV. simpl in HV'. rewrite HV2. f_equal. apply HV'.
Qed.

Definition find_value {X: Type} (G: graph) (g: graphfun) (u: node) (U A: assignments X): option X :=
  match (get_values G g U A) with
  | Some values => get_assigned_value values u
  | None => None
  end.

Lemma find_value_get_values {X: Type}: forall (G: graph) (g: graphfun) (u: node) (U A: assignments X) (x: X),
  get_values G g U [] = Some A
  -> find_value G g u U [] = Some x
  -> get_assigned_value A u = Some x.
Proof.
  intros G g u U A x. intros HA Hx.
  unfold find_value in Hx. rewrite HA in Hx. apply Hx.
Qed.

Lemma get_values_preserves_index {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U V: assignments X) (u: node) (i: nat),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true
  -> topological_sort G = Some ts /\ nth_error ts i = Some u
  -> get_values G g U [] = Some V
  -> exists (x: X), nth_error V i = Some (u, x).
Proof.
  intros ts G g U V u i. intros HG HU [Hts Hi] HV.
  assert (Hgvts: get_values G g U [] = get_values_from_topo_sort_2 ts G g U []).
  { apply get_values_from_topo_sort_equiv. easy. easy. easy. }
  rewrite Hgvts in HV.
  assert (HVi: exists (x: X) (V': assignments X),
               get_value_of_node u G g U [] ([] ++ V') = Some x
               /\ first_n V i = Some V'
               /\ nth_error V i = Some (u, x)).
  { apply get_values_ts_2_get_value_node with (ts := ts).
    - apply Hi.
    - apply HV. }
  destruct HVi as [x [V' [HV' [Hi' Hux]]]].
  exists x. apply Hux.
Qed.

Lemma length_filter_1 {X: Type}: forall (u: node) (U V: assignments X) (i: nat) (x: X) (ts: nodes) (G: graph) (g: graphfun),
  G_well_formed G = true /\ topological_sort G = Some ts
  -> nth_error V i = Some (u, x)
  -> get_values_from_topo_sort_2 ts G g U [] = Some V
  -> length (filter (fun x => fst x =? u) V) = 1.
Proof.
  intros u U V i x ts G g [HG Hts] Hx Hgvts.
  destruct (length (filter (fun x0 : nat * X => fst x0 =? u) V)) as [|l] eqn:Hl.
  - apply nth_error_In in Hx.
    assert (Hfilt: In (u, x) (filter (fun x0 : nat * X => fst x0 =? u) V)).
    { apply filter_true. split. apply Hx. simpl. apply eqb_refl. }
    destruct (filter (fun x0 : nat * X => fst x0 =? u) V) as [| h t].
    + exfalso. apply Hfilt.
    + simpl in Hl. lia.
  - destruct l as [|l'] eqn:Hl'.
    + reflexivity.
    + destruct (filter (fun x0 : nat * X => fst x0 =? u) V) as [| h t] eqn:Hfilt.
      * simpl in Hl. lia.
      * simpl in Hl. inversion Hl. destruct t as [|h' t'] eqn:Ht.
        -- simpl in H0. lia.
        -- apply filter_preserves_relative_index_2 in Hfilt as Hfilt'. destruct Hfilt' as [j [k [Hj [Hk Hjk]]]].
           simpl in H0. inversion H0.
           assert (Hh: In h V /\ fst h =? u = true).
           { assert (In h (filter (fun x0 : nat * X => fst x0 =? u) V)). { rewrite Hfilt. left. reflexivity. }
             apply filter_true in H. apply H. }
           assert (Hh': In h' V /\ fst h' =? u = true).
           { assert (In h' (filter (fun x0 : nat * X => fst x0 =? u) V)). { rewrite Hfilt. right. left. reflexivity. }
             apply filter_true in H. apply H. }
           destruct Hh as [HhV Hh]. destruct h as [h1 h2]. destruct h' as [h1' h2'].
           simpl in Hh. apply eqb_eq in Hh. rewrite Hh in *. clear Hh. destruct Hh' as [HhV' Hh].
           simpl in Hh. apply eqb_eq in Hh. rewrite Hh in *. clear Hh.
           assert (Hhts: nth_error ts j = Some u).
           { apply get_values_ts_2_preserves_index_rev with (G := G) (g := g) (Ae := []) (U := U) (V := V) (x := h2).
             split. apply Hgvts. apply Hj. }
           assert (Hhts': nth_error ts k = Some u).
           { apply get_values_ts_2_preserves_index_rev with (G := G) (g := g) (Ae := []) (U := U) (V := V) (x := h2').
             split. apply Hgvts. apply Hk. }
           assert (Hc: count u ts = 1).
           { apply topo_sort_contains_nodes_exactly_once with (G := G). easy.
             apply topo_sort_contains_nodes with (u := u) in Hts. apply Hts. apply nth_error_In with (n := j). apply Hhts. }
           assert (Hc': count u ts > 1). { apply nth_error_count with (j := j) (k := k). easy. easy. }
           lia.
Qed.

Lemma find_value_preserves_index {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U V: assignments X) (u: node) (i: nat),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true
  -> topological_sort G = Some ts /\ nth_error ts i = Some u
  -> get_values G g U [] = Some V
  -> exists (x: X), nth_error V i = Some (u, x) /\ find_value G g u U [] = Some x.
Proof.
  intros ts G g U V u i. intros HG HU [Hts Hi] HV.
  assert (Hx: exists (x: X), nth_error V i = Some (u, x)).
  { apply get_values_preserves_index with (ts := ts) (G := G) (g := g) (U := U) (u := u). easy. easy. easy. easy. }
  destruct Hx as [x Hx]. exists x. split. easy.
  unfold find_value. rewrite HV.

  assert (Hgvts: get_values_from_topo_sort_2 ts G g U [] = Some V).
  { symmetry. rewrite <- HV. apply get_values_from_topo_sort_equiv. easy. easy. easy. }

  assert (Hc: length (filter (fun x => fst x =? u) V) = 1).
  { apply length_filter_1 with (U := U) (ts := ts) (i := i) (x := x) (G := G) (g := g). easy. apply Hx. apply Hgvts. }
  apply nth_error_get_assigned_value with (i := i). easy.
Qed.

Lemma find_value_parent_first_n {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U V V': assignments X) (u: node) (i: nat),
  G_well_formed G = true /\ contains_cycle G = false
  -> is_assignment_for U (nodes_in_graph G) = true
  -> topological_sort G = Some ts /\ nth_error ts i = Some u
  -> get_values_from_topo_sort_2 ts G g U [] = Some V
  -> first_n V i = Some V'
  -> forall (p: node), In p (find_parents u G)
     -> find_value G g p U [] = get_assigned_value V' p.
Proof.
  intros ts G g U V V' u i.
  intros HG HU [Hts Hi] HV HV' p Hp.
  assert (Hj: exists (j: nat), nth_error ts j = Some p /\ j < i).
  { assert (Hpar: exists (j i: nat), Some j = index ts p /\ Some i = index ts u /\ j < i).
    { apply topo_sort_parents with (G := G). easy. easy. }
    destruct Hpar as [j [i' [Hj [Hi' Hji]]]].
    exists j. split.
    - apply index_correct. apply Hj.
    - apply index_correct_appears_once in Hi.
      + rewrite <- Hi in Hi'. inversion Hi'. rewrite <- H0. apply Hji.
      + apply topo_sort_contains_nodes_exactly_once with (G := G). easy. apply topo_sort_contains_nodes with (u := u) in Hts.
        apply Hts. apply index_exists. exists i'. apply Hi'. }
  destruct Hj as [j Hj].
  assert (Hlem: exists (x: X), nth_error V j = Some (p, x) /\ find_value G g p U [] = Some x).
  { apply find_value_preserves_index with (ts := ts). easy. easy. easy. 
    rewrite <- HV. apply get_values_from_topo_sort_equiv. easy. easy. easy. }
  destruct Hlem as [x [Hpx Hx]].
  rewrite Hx. symmetry.
  assert (Hc: length (filter (fun x => fst x =? p) V) = 1).
  { apply length_filter_1 with (U := U) (i := j) (x := x) (G := G) (g := g) (ts := ts). easy. apply Hpx. apply HV. }
  assert (Hj': nth_error V' j = Some (p, x)).
  { apply first_n_preserves_index with (V := V) (i := i). apply HV'. apply Hpx. apply Hj. }
  apply nth_error_get_assigned_value with (i := j). split.
  - apply Hj'.
  - assert (Hgeq1: length (filter (fun x0 : nat * X => fst x0 =? p) V') >= 1).
    { assert (Hmem: In (p, x) V'). { apply nth_error_In with (n := j). apply Hj'. }
      assert (Hmem': In (p, x) (filter (fun x0 : nat * X => fst x0 =? p) V')).
      { apply filter_true. split. apply Hmem. simpl. apply eqb_refl. }
      destruct (filter (fun x0 : nat * X => fst x0 =? p) V') as [| h t] eqn: Hl.
      - exfalso. apply Hmem'.
      - simpl. lia. }
    assert (Hleq1: 1 >= length (filter (fun x0 : nat * X => fst x0 =? p) V')).
    { rewrite <- Hc. apply first_n_filter_length with (i := i). apply HV'. }
    lia.
Qed.

Lemma find_value_get_value_node {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U: assignments X) (u: node),
  forall (i: nat) (V V': assignments X), 
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true
  -> topological_sort G = Some ts /\ nth_error ts i = Some u
  -> get_values G g U [] = Some V
  -> first_n V i = Some V'
  -> find_value G g u U [] = get_value_of_node u G g U [] V'.
Proof.
  intros ts G g U u i V V'. intros HG HU [Hts Hi] HV HV'.
  assert (Hgvts: get_values_from_topo_sort_2 ts G g U [] = Some V).
  { symmetry. rewrite <- HV. apply get_values_from_topo_sort_equiv. easy. easy. easy. }

  assert (Hx: exists (x: X), nth_error V i = Some (u, x) /\ find_value G g u U [] = Some x).
  { apply find_value_preserves_index with (ts := ts). easy. easy. easy. easy. }
  destruct Hx as [x [Hux Hx]].
  assert (Hx': exists (x: X) (V': assignments X),
       get_value_of_node u G g U [] ([] ++ V') = Some x
       /\ first_n V i = Some V'
       /\ nth_error V i = Some (u, x)).
  { apply get_values_ts_2_get_value_node with (ts := ts). easy. apply Hgvts. }
  destruct Hx' as [x' [V'' [Hx' [HV'' Hux']]]].
  rewrite Hx. simpl in Hx'. rewrite HV' in HV''. inversion HV''. rewrite Hx'. rewrite Hux in Hux'. inversion Hux'. reflexivity.
Qed.

Fixpoint find_values {X: Type} (G: graph) (g: graphfun) (P: nodes) (U A: assignments X): option (assignments X) :=
  match P with
  | [] => Some []
  | h :: t => match (find_value G g h U A) with
              | Some x => match (find_values G g t U A) with
                          | Some r => Some ((h, x) :: r)
                          | None => None
                          end
              | None => None
              end
  end.

Lemma find_values_not_assigned {X: Type}: forall (G: graph) (g: graphfun) (P: nodes) (U A values: assignments X) (u: node),
  find_values G g P U A = Some values /\ ~(In u P) -> is_assigned values u = false.
Proof.
  intros G g P U A values u. intros [Hv Hu].
  generalize dependent values. induction P as [| h t IH].
  - intros values Hv. simpl in Hv. inversion Hv. simpl. reflexivity.
  - intros values Hv. simpl in Hu. simpl in Hv. destruct (find_value G g h U A) as [x|].
    + destruct (find_values G g t U A) as [r|].
      * inversion Hv. specialize IH with (values := r). simpl.
        assert (u =? h = false). { destruct (u =? h) as [|] eqn:Hhu. exfalso. apply Hu. left. apply eqb_eq. rewrite eqb_sym. apply Hhu. reflexivity. }
        rewrite H. simpl. apply IH.
        -- intros F. apply Hu. right. apply F. 
        -- reflexivity.
      * discriminate Hv.
    + discriminate Hv.
Qed.

Lemma find_values_assignment: forall X (G: graph) (g: graphfun) (P: nodes) (U A values: assignments X),
  find_values G g P U A = Some values -> is_assignment_for values P = true.
Proof.
  intros X G g P U A.
  induction P as [| h t IH].
  - intros values H. simpl. reflexivity.
  - intros values H. simpl. simpl in H. destruct (find_value G g h U A) as [x|].
    + destruct (find_values G g t U A) as [r|].
      * inversion H. simpl. rewrite eqb_refl. simpl. specialize IH with (values := r).
        apply is_assignment_for_cat. apply IH. reflexivity.
      * discriminate H.
    + discriminate H.
Qed.

Lemma find_values_get_assigned: forall X (G: graph) (g: graphfun) (P: nodes) (U A values: assignments X)
                                       (x: X) (m: node),
  find_values G g P U A = Some values /\ In m P /\ find_value G g m U A = Some x
  -> get_assigned_value values m = Some x.
Proof.
  intros X G g P U A values x m.
  intros [Hv [Hm Hx]].
  generalize dependent values. induction P as [| h t IH].
  - intros values Hv. simpl in Hm. exfalso. apply Hm.
  - intros values Hv. simpl in Hm. destruct Hm as [Hhm | Hmem].
    + simpl in Hv. rewrite Hhm in Hv. rewrite Hx in Hv.
      destruct (find_values G g t U A) as [r|].
      * inversion Hv. simpl. rewrite eqb_refl. reflexivity.
      * discriminate Hv.
    + simpl in Hv. destruct (find_value G g h U A) as [x'|] eqn:Hh.
      * destruct (find_values G g t U A) as [r|].
        -- inversion Hv. simpl. destruct (h =? m) as [|] eqn:Hhm.
           ++ apply eqb_eq in Hhm. rewrite Hhm in Hh. rewrite <- Hh. apply Hx.
           ++ apply IH with (values := r).
              ** apply Hmem.
              ** reflexivity.
        -- discriminate Hv.
      * discriminate Hv.
Qed.

Lemma find_values_same_if_parents_same {X: Type}: forall (G: graph) (g g': graphfun) (w: node) (U: assignments X),
  (forall (p: node), In p (find_parents w G) -> find_value G g p U [] = find_value G g' p U [])
  -> find_values G g' (find_parents w G) U [] = find_values G g (find_parents w G) U [].
Proof.
  intros G g g' w U H.
  induction (find_parents w G) as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    assert (Hh: find_value G g h U [] = find_value G g' h U []).
    { apply H. left. reflexivity. }
    rewrite Hh.
    destruct (find_value G g' h U []) as [x|] eqn:Hx.
    + assert (Ht: find_values G g' t U [] = find_values G g t U []).
      { apply IH. intros p Hp. apply H. right. apply Hp. }
      rewrite Ht. reflexivity.
    + reflexivity.
Qed.

Lemma find_values_same_if_parents_same_U {X: Type}: forall (G: graph) (g: graphfun) (w: node) (U U': assignments X),
  (forall (p: node), In p (find_parents w G) -> find_value G g p U [] = find_value G g p U' [])
  -> find_values G g (find_parents w G) U [] = find_values G g (find_parents w G) U' [].
Proof.
  intros G g w U U' H.
  induction (find_parents w G) as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    assert (Hh: find_value G g h U [] = find_value G g h U' []).
    { apply H. left. reflexivity. }
    rewrite Hh.
    destruct (find_value G g h U' []) as [x|] eqn:Hx.
    + assert (Ht: find_values G g t U [] = find_values G g t U' []).
      { apply IH. intros p Hp. apply H. right. apply Hp. }
      rewrite Ht. reflexivity.
    + reflexivity.
Qed.

Lemma get_value_of_node_equal {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U: assignments X) (u: node) (i: nat) (V V' P: assignments X),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true
  -> topological_sort G = Some ts /\ nth_error ts i = Some u
  -> get_values G g U [] = Some V
  -> first_n V i = Some V'
  -> find_values G g (find_parents u G) U [] = Some P
  -> get_value_of_node u G g U [] V' = get_value_of_node u G g U [] P.
Proof.
  intros ts G g U u i V V' P. intros HG HU [Hts Hi] HV HV' HP.
  unfold get_value_of_node. simpl. destruct (get_assigned_value U u) as [unobs|].
  - assert (Hpar: get_parent_assignments V' (find_parents u G) = get_parent_assignments P (find_parents u G)).
    { assert (Hedge: forall (p: node), In p (find_parents u G) -> edge_in_graph (p, u) G = true).
      { intros p Hp. apply edge_from_parent_to_child. apply Hp. }
      assert (Hcount: forall (p: node), In p (find_parents u G) -> count p (find_parents u G) = 1).
      { intros p Hp. apply each_parent_appears_once. easy. apply Hp. }
      generalize dependent P. induction (find_parents u G) as [| h t IH].
      - intros P HP. simpl. reflexivity.
      - intros P HP. simpl. simpl in HP.
        destruct (find_value G g h U []) as [x|] eqn:Hx.
        + assert (HPh: get_assigned_value P h = Some x).
          { apply find_values_get_assigned with (G := G) (g := g) (U := U) (A := []) (P := h :: t).
            repeat split.
            - simpl. rewrite Hx. apply HP.
            - left. reflexivity.
            - apply Hx. }
          assert (HVh': get_assigned_value V' h = Some x).
          { symmetry. rewrite <- Hx. apply find_value_parent_first_n with (ts := ts) (V := V) (U := U) (i := i) (u := u).
            - easy.
            - easy.
            - easy.
            - rewrite <- HV. symmetry. apply get_values_from_topo_sort_equiv. easy. easy. easy.
            - apply HV'.
            - apply edge_from_parent_to_child. apply Hedge. left. reflexivity. }
          rewrite HPh. rewrite HVh'. destruct (find_values G g t U []) as [r|] eqn:Hr.
          * specialize IH with (P := r).
            assert (Hpar: get_parent_assignments P t = get_parent_assignments r t).
            { inversion HP. clear IH. clear Hr. clear Hedge. induction t as [| ht tt IH].
              - simpl. reflexivity.
              - simpl.
                destruct (h =? ht) as [|] eqn:Hhht.
                + apply eqb_eq in Hhht. rewrite Hhht in Hcount. specialize Hcount with (p := ht).
                  assert (F: count ht (ht :: ht :: tt) = 1). { apply Hcount. left. reflexivity. }
                  simpl in F. rewrite eqb_refl in F. lia.
                + assert (Hind: get_parent_assignments ((h, x) :: r) tt = get_parent_assignments r tt).
                  { apply IH. intros p Hmem. destruct Hmem as [Hmem | Hmem].
                    - rewrite Hmem in *. simpl. rewrite eqb_refl. f_equal.
                      assert (Hc: count p (p :: ht :: tt) = 1). { apply Hcount. left. reflexivity. }
                      simpl in Hc. rewrite eqb_refl in Hc. inversion Hc. destruct (ht =? p) as [|] eqn:F.
                      + lia.
                      + reflexivity.
                    - simpl. destruct (h =? p) as [|] eqn:F.
                      + apply eqb_eq in F. rewrite F in *. assert (Hc: count p (p :: ht :: tt) = 1). { apply Hcount. left. reflexivity. }
                        simpl in Hc. rewrite eqb_refl in Hc. rewrite eqb_sym in Hhht. rewrite Hhht in Hc. inversion Hc.
                        apply member_count_at_least_1 in Hmem. lia.
                      + assert (Hc: count p (h :: ht :: tt) = 1). { apply Hcount. right. right. apply Hmem. }
                        simpl in Hc. rewrite F in Hc. destruct (ht =? p) as [|] eqn:F'.
                        * inversion Hc. apply member_count_at_least_1 in Hmem. lia.
                        * apply Hc. }
                  rewrite Hind. reflexivity. }
            rewrite Hpar.
            assert (Hind: get_parent_assignments V' t = get_parent_assignments r t).
            { apply IH.
              - intros p Hmem. apply Hedge. right. apply Hmem.
              - intros p Hmem. destruct (h =? p) as [|] eqn:Hhp.
                + apply eqb_eq in Hhp. rewrite Hhp in Hcount. specialize Hcount with (p := p).
                  assert (F: count p (p :: t) = 1). { apply Hcount. left. reflexivity. }
                  simpl in F. rewrite eqb_refl in F. inversion F. apply member_count_at_least_1 in Hmem. lia.
                + assert (Hc: count p (h :: t) = 1). { apply Hcount. right. apply Hmem. }
                  simpl in Hc. rewrite Hhp in Hc. apply Hc.
              - reflexivity. }
            rewrite Hind. reflexivity.
          * discriminate HP.
        + discriminate HP. }
    rewrite Hpar. reflexivity.
  - reflexivity.
Qed.

Theorem find_value_existence: forall X (G: graph) (g: graphfun) (U A: assignments X) (u: node),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph u G = true ->
  exists (x: X), find_value G g u U A = Some x.
Proof.
  intros X G g U A u. intros [Hwf Hcyc]. intros [HU Hu].
  assert (Hval: exists (values: assignments X), get_values G g U A = Some values).
  { apply get_values_existence.
    - split.
      + apply Hwf.
      + apply Hcyc.
    - apply HU. }
  unfold find_value. destruct Hval as [values Hval].
  rewrite Hval. apply get_values_exists_then_all_nodes_assigned in Hval.
  apply assigned_has_value with (L := (nodes_in_graph G)). split.
  - destruct G as [V E]. simpl. simpl in Hu. apply member_In_equiv. apply Hu.
  - apply Hval.
Qed.

Corollary find_values_existence: forall X (G: graph) (g: graphfun) (U A: assignments X) (u: node),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph u G = true ->
  exists (P: assignments X), find_values G g (find_parents u G) U A = Some P.
Proof.
  intros X G g U A u. intros [Hwf Hcyc]. intros [HU hu].
  remember (find_parents u G).
  assert (H: forall h: node, In h n -> In h (find_parents u G)).
  { intros h Hmem. rewrite <- Heqn. apply Hmem. }
  clear Heqn.
  induction n as [| h t IH].
  - exists []. reflexivity.
  - simpl. assert (Hv: exists v, find_value G g h U A = Some v).
    { apply find_value_existence.
      - split. apply Hwf. apply Hcyc.
      - split. apply HU.
        assert (He: edge_in_graph (h, u) G = true).
        { apply edge_from_parent_to_child. specialize H with (h := h).
          apply H. simpl. left. reflexivity. }
        assert (Hh: node_in_graph h G = true /\ node_in_graph u G = true).
        { apply edge_corresponds_to_nodes_in_well_formed. split.
          apply Hwf. apply He. }
        destruct Hh as [Hh _]. apply Hh. }
    destruct Hv as [v Hv]. rewrite Hv.
    assert (H': forall h: node, In h t -> In h (find_parents u G)).
    { intros h' Hmem. apply H. simpl. right. apply Hmem. }
    apply IH in H'. destruct H' as [P' H']. rewrite H'. exists ((h, v) :: P'). reflexivity.
Qed.

Corollary find_values_existence_gen: forall X (G: graph) (g: graphfun) (U A: assignments X) (l: nodes),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true ->
  (forall (u: node), In u l -> node_in_graph u G = true) ->
  exists (P: assignments X), find_values G g l U A = Some P.
Proof.
  intros X G g U A l. intros [Hwf Hcyc]. intros HU Hu.
  induction l as [| h t IH].
  - exists []. reflexivity.
  - simpl. assert (Hv: exists v, find_value G g h U A = Some v).
    { apply find_value_existence.
      - split. apply Hwf. apply Hcyc.
      - split. apply HU. apply Hu. left. reflexivity. }
    destruct Hv as [v Hv]. rewrite Hv.
    assert (H': forall u: node, In u t -> node_in_graph u G = true).
    { intros h' Hmem. apply Hu. simpl. right. apply Hmem. }
    apply IH in H'. destruct H' as [P' H']. rewrite H'. exists ((h, v) :: P'). reflexivity.
Qed.


Theorem find_value_gives_value_of_node {X: Type}: forall (G: graph) (g: graphfun) (U: assignments X) (u: node),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph u G = true ->
  exists (P: assignments X), find_values G g (find_parents u G) U [] = Some P
                              /\ find_value G g u U [] = get_value_of_node u G g U [] P.
Proof.
  intros G g U u. intros HG [HU Hu].
  assert (HP: exists (P: assignments X), find_values G g (find_parents u G) U [] = Some P).
  { apply find_values_existence. easy. easy. }
  destruct HP as [P HP]. exists P. split. apply HP.
  assert (HV: exists (V: assignments X), get_values G g U [] = Some V).
  { apply get_values_existence. easy. easy. }
  destruct HV as [V HV].
  assert (Hts: exists (ts: nodes), topological_sort G = Some ts).
  { apply topo_sort_exists_for_acyclic. easy. }
  destruct Hts as [ts Hts].
  assert (Hi: exists (i: nat), nth_error ts i = Some u).
  { apply In_nth_error. apply topo_sort_contains_nodes with (u := u) in Hts. apply Hts. apply Hu. }
  destruct Hi as [i Hi].
  assert (HV': exists (V': assignments X), first_n V i = Some V').
  { apply first_n_exists. apply index_correct_appears_once in Hi.
    - apply index_in_range in Hi.
      assert (Hlen: length V = length ts).
      { apply get_values_ts_2_preserves_length with (G := G) (g := g) (U := U) (Ae := []). symmetry. rewrite <- HV.
        apply get_values_from_topo_sort_equiv. easy. easy. easy. }
      rewrite Hlen. apply Hi.
    - apply topo_sort_contains_nodes_exactly_once with (G := G). easy. easy. }
  destruct HV' as [V' HV'].
  assert (H1: find_value G g u U [] = get_value_of_node u G g U [] V').
  { apply find_value_get_value_node with (ts := ts) (i := i) (V := V).
    - apply HG.
    - apply HU.
    - split. apply Hts. apply Hi.
    - apply HV.
    - apply HV'. }
  rewrite H1.
  apply get_value_of_node_equal with (ts := ts) (i := i) (V := V).
  - apply HG.
  - apply HU.
  - split. apply Hts. apply Hi.
  - apply HV.
  - apply HV'.
  - apply HP.
Qed.

Lemma find_values_append {X: Type}: forall (G: graph) (g: graphfun) (l: nodes) (U A: assignments X) (u: node),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true ->
  (forall (u: node), In u l -> node_in_graph u G = true) ->
  node_in_graph u G = true ->
  exists (x: X) (V: assignments X), find_value G g u U A = Some x
      /\ find_values G g l U A = Some V /\ find_values G g (l ++ [u]) U A = Some (V ++ [(u, x)]).
Proof.
  intros G g l U A u HG HU Hl Hu.
  assert (Hx: exists (x: X), find_value G g u U A = Some x).
  { apply find_value_existence.
    - apply HG.
    - split. apply HU. apply Hu. }
  destruct Hx as [x Hx].
  induction l as [| h t IH].
  - simpl. exists x. exists []. repeat split.
    + apply Hx.
    + rewrite Hx. simpl. reflexivity.
  - assert (Hxh: exists (xh: X), find_value G g h U A = Some xh).
    { apply find_value_existence.
      - apply HG.
      - split. apply HU. apply Hl. left. reflexivity. }
    destruct Hxh as [xh Hxh].
    assert (Hind: forall u : node, In u t -> node_in_graph u G = true).
    { intros v Hmem. apply Hl. right. apply Hmem. }
    apply IH in Hind. destruct Hind as [x' [V [Hx' [HV HVx]]]].
    exists x'. exists ((h, xh) :: V). repeat split.
    + apply Hx'.
    + simpl. rewrite Hxh. rewrite HV. reflexivity.
    + simpl. rewrite Hxh. rewrite HVx. reflexivity.
Qed.

Lemma get_parent_assignments_append {X: Type}: forall (G: graph) (g: graphfun) (l: nodes) (U Ae Ae': assignments X) (u: node),
  G_well_formed G = true /\ contains_cycle G = false /\ is_assignment_for U (nodes_in_graph G) = true
  -> (forall (v: node), In v l -> node_in_graph v G = true) /\ node_in_graph u G = true
  -> subset (find_parents u G) l = true /\ find_values G g l U [] = Some Ae
  -> get_parent_assignments Ae (find_parents u G) = get_parent_assignments (Ae ++ Ae') (find_parents u G).
Proof.
  intros G g l U Ae Ae' u. intros [HG [Hcyc HU]] [Hul Hu] [Hl HAe].
  induction (find_parents u G) as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    assert (Hlmem: In h l).
    { apply member_In_equiv. apply split_and_true in Hl. apply Hl. }

    assert (Hh: exists (x: X), find_value G g h U [] = Some x).
    { apply find_value_existence. easy. split. apply HU. apply Hul. simpl in Hl. apply Hlmem. }
    destruct Hh as [x Hh].

    assert (HAeh: get_assigned_value Ae h = Some x).
    { apply find_values_get_assigned with (G := G) (g := g) (P := l) (U := U) (A := []). easy. }

    rewrite HAeh. assert (HAeh': get_assigned_value (Ae ++ Ae') h = Some x).
    { apply get_assigned_app_Some. apply HAeh. }
    rewrite HAeh'.

    simpl in Hl. apply split_and_true in Hl. destruct Hl as [_ Hl]. apply IH in Hl.
    rewrite Hl. reflexivity.
Qed.


Lemma find_values_get_assigned_2: forall X (G: graph) (g: graphfun) (P: nodes) (U A values: assignments X)
                                       (x: X) (m: node),
  G_well_formed G = true /\ contains_cycle G = false /\ is_assignment_for U (nodes_in_graph G) = true
  -> find_values G g P U A = Some values /\ In m P /\ (forall (u: node), In u P -> node_in_graph u G = true)
  -> get_assigned_value values m = Some x -> find_value G g m U A = Some x.
Proof.
  intros X G g P U A values x m.
  intros HG [Hv [Hm Hu]] Hx. generalize dependent values. induction P as [| h t IH].
  - exfalso. apply Hm.
  - intros values Hv Hx.
    assert (Hh: exists (xh: X), find_value G g h U A = Some xh).
    { apply find_value_existence. easy. split. easy. apply Hu. left. reflexivity. }
    destruct Hh as [xh Hxh].
    destruct (h =? m) as [|] eqn:Hhm.
    + simpl in Hv. apply eqb_eq in Hhm.
      rewrite Hxh in Hv.
      destruct (find_values G g t U A) as [r|].
      * inversion Hv. rewrite <- H0 in Hx. simpl in Hx. rewrite Hhm in Hx. rewrite eqb_refl in Hx. inversion Hx.
        rewrite <- H1. rewrite <- Hhm. apply Hxh.
      * discriminate Hv.
    + destruct Hm as [Hm | Hm]. rewrite Hm in Hhm. rewrite eqb_refl in Hhm. discriminate Hhm.
      simpl in Hv. rewrite Hxh in Hv. destruct (find_values G g t U A) as [r|].
      * inversion Hv. apply IH with (values := r).
        -- apply Hm.
        -- intros u Hu'. apply Hu. right. apply Hu'.
        -- reflexivity.
        -- rewrite <- H0 in Hx. simpl in Hx. rewrite Hhm in Hx. apply Hx.
      * discriminate Hv.
Qed.

Theorem find_values_preserves_index: forall X (G: graph) (g: graphfun) (U A values: assignments X)
                                            (P: nodes) (u: node) (i: nat),
  G_well_formed G = true /\ contains_cycle G = false
  -> is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph u G = true
  -> (forall (v: node), In v P -> node_in_graph v G = true)
  -> find_values G g P U A = Some values /\ index P u = Some i
  -> exists x: X, find_value G g u U A = Some x /\ nth_error values i = Some (u, x).
Proof.
  intros X G g U A values P u i [Hwf Hcyc] [HU Hu] HP [Hfv Hi].
  assert (Hx: exists x: X, find_value G g u U A = Some x).
  { apply find_value_existence. split.
    - apply Hwf.
    - apply Hcyc.
    - split. apply HU. apply Hu. }
  destruct Hx as [x Hx]. exists x. split.
  - apply Hx.
  - generalize dependent values. generalize dependent i. induction P as [| h t IH].
    + intros i Hi values H. simpl in Hi. discriminate Hi.
    + intros i Hi values H. assert (Hx': exists x': X, find_value G g h U A = Some x').
      { apply find_value_existence. split.
        - apply Hwf.
        - apply Hcyc.
        - split. apply HU. specialize HP with (v := h). apply HP. simpl. left. reflexivity. }
      destruct Hx' as [x' Hx'].
      simpl in H. rewrite Hx' in H. simpl in Hi.
      destruct (h =? u) as [|] eqn:Hhu.
      * inversion Hi. destruct (find_values G g t U A) as [r|].
        -- inversion H. simpl. apply eqb_eq in Hhu. rewrite Hhu.
           assert (Hxx': x = x').
           { rewrite Hhu in Hx'. rewrite Hx in Hx'. inversion Hx'. reflexivity. }
           rewrite Hxx'. reflexivity.
        -- discriminate H.
      * destruct (index t u) as [i'|].
        -- inversion Hi. destruct (find_values G g t U A) as [r|].
           ++ inversion H. specialize IH with (i := i') (values := r).
              simpl. apply IH.
              ** intros v Hmem. apply HP. simpl. right. apply Hmem.
              ** reflexivity.
              ** reflexivity.
           ++ discriminate H.
        -- discriminate Hi.
Qed.

Lemma find_value_evaluates_to_g {X: Type}: forall (G: graph) (g: graphfun) (U: assignments X) (u: node),
  (G_well_formed G = true /\ contains_cycle G = false) /\ is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph u G = true
  -> exists (P: assignments X), find_values G g (find_parents u G) U [] = Some P
  /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents u G)
  /\ exists (unobs: X), get_assigned_value U u = Some unobs
  /\ find_value G g u U [] = Some (g u (unobs, pa)).
Proof.
  intros G g U u. intros [HG [HU HuG]].
  assert (HP: exists (P: assignments X), find_values G g (find_parents u G) U [] = Some P
                              /\ find_value G g u U [] = get_value_of_node u G g U [] P).
  { apply find_value_gives_value_of_node.
    - apply HG.
    - split. apply HU. apply HuG. }
  destruct HP as [P [HP Hu]]. exists P. split.
  - apply HP.
  - unfold get_value_of_node in Hu. simpl in Hu.
    apply find_values_assignment in HP as HP'.
    assert (Hpar: exists p, Some p = get_parent_assignments P (find_parents u G)).
    { apply parent_assignments_exist. apply HP'. }
    destruct Hpar as [pa Hpar]. exists pa. split.
    + apply Hpar.
    + rewrite <- Hpar in Hu.
      assert (HuU: exists (unobs: X), get_assigned_value U u = Some unobs).
      { apply assigned_has_value with (L := nodes_in_graph G). split.
        - destruct G as [V E]. simpl. simpl in HuG. apply member_In_equiv. apply HuG.
        - apply HU. }
      destruct HuU as [unobs HuU]. exists unobs. split.
      * apply HuU.
      * rewrite HuU in Hu. apply Hu.
Qed.

Lemma find_values_unequal {X: Type} `{EqType X}: forall (G: graph) (g: graphfun) (u: node) (U1 U2 P1 P2: assignments X),
  find_values G g (find_parents u G) U1 [] = Some P1
  -> find_values G g (find_parents u G) U2 [] = Some P2
  -> P1 <> P2
  -> exists (p: node), In p (find_parents u G) /\ find_value G g p U1 [] <> find_value G g p U2 [].
Proof.
  intros G g u U1 U2 P1 P2. intros HP1 HP2 HP.
  generalize dependent P2. generalize dependent P1. induction (find_parents u G) as [| h t IH].
  - intros P1 HP1 P2 HP2 HP. simpl in HP1. simpl in HP2. exfalso. apply HP. inversion HP1. inversion HP2. reflexivity.
  - intros P1 HP1 P2 HP2 HP. simpl in HP1. destruct (find_value G g h U1 []) as [x1|] eqn:Hx1.
    + simpl in HP2. destruct (find_value G g h U2 []) as [x2|] eqn:Hx2.
      * destruct (eqb x1 x2) as [|] eqn:Hx.
        -- destruct (find_values G g t U1 []) as [P1'|] eqn:HP1'.
           ++ destruct (find_values G g t U2 []) as [P2'|] eqn:HP2'.
              ** specialize IH with (P1 := P1') (P2 := P2').
                 assert (Hind: exists p : node,
                               In p t /\ find_value G g p U1 [] <> find_value G g p U2 []).
                 { apply IH. reflexivity. reflexivity. intros F. apply HP. inversion HP1. inversion HP2. rewrite F.
                   apply eqb_eq' in Hx. rewrite Hx. reflexivity. }
                 destruct Hind as [p [Hmem Hp]]. exists p. split. right. apply Hmem. apply Hp.
              ** discriminate HP2.
           ++ discriminate HP1.
        -- exists h. split.
           ++ left. reflexivity.
           ++ rewrite Hx1. rewrite Hx2. intros F. inversion F. rewrite H1 in Hx. rewrite eqb_refl' in Hx. discriminate Hx.
      * discriminate HP2.
    + discriminate HP1.
Qed.