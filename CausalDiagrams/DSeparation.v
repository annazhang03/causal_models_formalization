From CausalDiagrams Require Import IntermediateNodes.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.

Import ListNotations.

Fixpoint descendants_not_in_Z (d: nodes) (Z: nodes) : Prop :=
  match d with
  | [] => True
  | h :: t => ~(In h Z) /\ descendants_not_in_Z t Z
  end.

Definition descendants_not_in_Z_bool (d: nodes) (Z: nodes) : bool :=
  forallb (fun x: node => negb (member x Z)) d.

Definition some_descendant_in_Z_bool (d: nodes) (Z: nodes) : bool :=
  overlap d Z.

Theorem descendants_in_or_not_in: forall d: nodes, forall Z: nodes,
  descendants_not_in_Z_bool d Z = false <-> some_descendant_in_Z_bool d Z = true.
Proof.
  intros d Z. split.
  - intros H. induction d as [| h t IH].
    + simpl in H. discriminate H.
    + simpl. simpl in H. destruct (member h Z) as [|] eqn:HhZ.
      * reflexivity.
      * simpl in H. apply IH in H. apply H.
  - intros H. induction d as [| h t IH].
    + simpl in H. discriminate H.
    + simpl. simpl in H. destruct (member h Z) as [|] eqn:HhZ.
      * simpl. reflexivity.
      * simpl. apply IH in H. apply H.
Qed.

(* there is some collider such that none of its descendants are in Z *)
Definition collider_descendants_not_conditioned (cols: nodes) (G: graph) (Z: nodes) : bool :=
  existsb (fun c => descendants_not_in_Z_bool (find_descendants c G) Z) cols.

(* p contains collision A -> B <- C, where B and descendants are not in Z (the conditioning set) *)
Definition is_blocked_by_collider_2 (p: path) (G: graph) (Z: nodes) : bool :=
  collider_descendants_not_conditioned (find_colliders_in_path p G) G Z.

Example collider_in_conditioning_set_2:
  is_blocked_by_collider_2 (1, 3, [2]) ([1; 2; 3], [(1, 2); (3, 2)]) [2] = false.
Proof. reflexivity. Qed.

Example collider_not_in_conditioning_set_2:
  is_blocked_by_collider_2 (1, 3, [2]) ([1; 2; 3], [(1, 2); (3, 2)]) [] = true.
Proof. reflexivity. Qed.

Example descendant_in_conditioning_set_2:
  is_blocked_by_collider_2 (1, 3, [2]) ([1; 2; 3; 4], [(1, 2); (3, 2); (2, 4)]) [4] = false.
Proof. reflexivity. Qed.

Example collider_in_longer_path_2:
  is_blocked_by_collider_2 (1, 4, [2; 3]) ([1; 2; 3; 4], [(1, 2); (3, 2); (3, 4)]) [] = true.
Proof. reflexivity. Qed.

Definition path_is_blocked_bool (G: graph) (Z: nodes) (p: path) : bool :=
  is_blocked_by_mediator_2 p G Z || is_blocked_by_confounder_2 p G Z || is_blocked_by_collider_2 p G Z.

Example collider_no_conditioning_needed_2: path_is_blocked_bool G_d [] (5, 8, [6; 7]) = true.
Proof. reflexivity. Qed.

(* conditioning on W unblocks the path from Z to Y *)
Example condition_on_collider_2:
  path_is_blocked_bool G_d [6] (5, 8, [6; 7]) = false.
Proof. reflexivity. Qed.

(* conditioning on U (a descendant of W) unblocks the path from Z to Y *)
Example condition_on_descendant_collider_2:
  path_is_blocked_bool G_d [10] (5, 8, [6; 7]) = false.
Proof. reflexivity. Qed.

(* conditioning on X blocks the path from Z to Y, even if W unblocks it *)
Example condition_on_collider_and_mediator_2:
  path_is_blocked_bool G_d [6; 7] (5, 8, [6; 7]) = true.
Proof. reflexivity. Qed.

(* determine whether u and v are independent in G conditional on the nodes in Z *)
Definition d_separated_bool (u v: node) (G: graph) (Z: nodes) : bool :=
  forallb (path_is_blocked_bool G Z) (find_all_paths_from_start_to_end u v G).


(* Z to Y are unconditionally independent due to collider at W *)
Example unconditionally_independent_2: d_separated_bool 5 8 G_d [] = true.
Proof. reflexivity. Qed.

(* conditioning on W unblocks the path from Z to Y *)
Example conditionally_dependent_2: d_separated_bool 5 8 G_d [6] = false.
Proof. reflexivity. Qed.

(* based on figure 2.8 of primer *)
(* conditioning on nothing leaves the path Z <- T -> Y open *)
Example unconditionally_dependent_2:
  d_separated_bool 5 8 G_d_modified [] = false.
Proof. reflexivity. Qed.

(* conditioning on T blocks the second path from Z to Y *)
Example conditionally_independent_2:
  d_separated_bool 5 8 (V_d ++ [11; 12], E_d ++ [(11, 5); (11, 8); (12, 11)]) [11] = true.
Proof. reflexivity. Qed.

(* conditioning on T and W unblocks the path Z -> W <- X -> Y *)
Example condition_on_T_W_2 :
  d_separated_bool 5 8 (V_d ++ [11; 12], E_d ++ [(11, 5); (11, 8); (12, 11)]) [11; 6] = false.
Proof. reflexivity. Qed.

(* conditioning on X closes the path Z -> W <- X -> Y *)
Example condition_on_T_W_X_2 :
  d_separated_bool 5 8 (V_d ++ [11; 12], E_d ++ [(11, 5); (11, 8); (12, 11)]) [11; 6; 7] = true.
Proof. reflexivity. Qed.

Definition all_colliders_have_descendant_conditioned_on (col: nodes) (G: graph) (Z: nodes) : bool :=
  forallb (fun c => (some_descendant_in_Z_bool (find_descendants c G) Z)) col.

Definition d_connected_2 (p: path) (G: graph) (Z: nodes) : Prop :=
  overlap Z (find_mediators_in_path p G) = false /\
  overlap Z (find_confounders_in_path p G) = false /\
  all_colliders_have_descendant_conditioned_on (find_colliders_in_path p G) G Z = true.


(* u and v are d-separated given Z in G iff no path d-connects u and v given Z *)
Theorem d_separated_vs_connected: forall u v: node, forall G: graph, forall Z: nodes,
  d_separated_bool u v G Z = false <->
  exists l: nodes, (acyclic_path_2 (u, v, l)) /\ (is_path_in_graph (u, v, l) G = true)
                                              /\ d_connected_2 (u, v, l) G Z.
Proof.
  intros u v G Z.
  split.
  - intros d_sep.
    unfold d_separated_bool in d_sep.
    apply demorgan_many_bool in d_sep.
    destruct d_sep as [p [HIn Hblock]].
    apply paths_start_to_end_correct in HIn. destruct HIn as [Hpath [Hse Hcyc]].
    destruct p as [[s e] l].
    apply path_start_end_equal in Hse. destruct Hse as [Hsu Hev].
    rewrite <- Hsu. rewrite <- Hev.
    exists l.
    split. apply Hcyc. split. apply Hpath.
    unfold path_is_blocked_bool in Hblock.
    apply demorgan_bool in Hblock. destruct Hblock as [Hblock Hcol].
    apply demorgan_bool in Hblock. destruct Hblock as [Hmed Hcon].
    unfold d_connected_2. split.
    (* no mediators are in Z *)
    + unfold is_blocked_by_mediator_2 in Hmed. apply Hmed.
    + split.
      (* no confounders are in Z *)
      * unfold is_blocked_by_confounder_2 in Hcon. apply Hcon.
      (* every collider has a descendant in Z *)
      * unfold is_blocked_by_collider_2 in Hcol.
        induction (find_colliders_in_path (s, e, l) G) as [| h t IH].
        -- simpl. reflexivity.
        -- simpl. simpl in Hcol.
           destruct (member h Z) as [|] eqn:HhZ.
           ++ simpl in Hcol. simpl. apply IH in Hcol. apply Hcol.
           ++ simpl in Hcol. simpl.
              destruct (descendants_not_in_Z_bool (get_endpoints (find_directed_paths_from_start h G)) Z) as [|] eqn:Hdesc.
              ** discriminate Hcol.
              ** apply IH in Hcol. rewrite Hcol.
                 apply descendants_in_or_not_in in Hdesc. rewrite Hdesc. reflexivity.
    + admit.
    + admit.
  - intros [l [cyc [path conn]]].
    unfold d_separated_bool. apply demorgan_many_bool.
    exists (u, v, l). split.
    + apply paths_start_to_end_correct.
      * admit.
      * admit.
      * split. apply path.
        { split.
          - unfold path_start_and_end. simpl. rewrite eqb_refl. simpl. apply eqb_refl.
          - apply cyc. }
    + unfold path_is_blocked_bool. unfold d_connected_2 in conn. destruct conn as [med [con col]].
      apply demorgan_bool. split.
      * apply demorgan_bool. split.
        (* path is not blocked by any mediator *)
        -- unfold is_blocked_by_mediator_2. apply med.
        (* path is not blocked by any confounder *)
        -- unfold is_blocked_by_confounder_2. apply con.
      (* path is not blocked by any collider *)
      * unfold is_blocked_by_collider_2.
        induction (find_colliders_in_path (u, v, l) G) as [| h t IH].
        -- simpl. reflexivity.
        -- simpl. simpl in col. destruct (member h Z) as [|] eqn:HhZ.
           ++ simpl. simpl in col. apply IH in col. apply col.
           ++ simpl. simpl in col.
              destruct (descendants_not_in_Z_bool (get_endpoints (find_directed_paths_from_start h G)) Z) as [|] eqn:Hdesc.
              ** apply split_and_true in col. destruct col as [desc col].
                 apply descendants_in_or_not_in in desc. rewrite desc in Hdesc. discriminate Hdesc.
              ** apply split_and_true in col. destruct col as [desc col].
                 apply IH in col. apply col.
Admitted.


Theorem reverse_d_connected_paths: forall (u v: node) (l: nodes) (G: graph) (Z: nodes),
  d_connected_2 (u, v, l) G Z -> d_connected_2 (v, u, rev l) G Z.
Proof.
  intros u v l G Z H. unfold d_connected_2 in *. repeat split.
  - destruct (overlap Z (find_mediators_in_path (v, u, rev l) G)) as [|] eqn:Hmed.
    + apply overlap_has_member_in_common in Hmed. destruct Hmed as [m [HmZ Hmed]].
      apply mediators_same_in_reverse_path in Hmed. destruct H as [H _]. apply no_overlap_non_member_rev with (x := m) in H.
      * exfalso. apply H. rewrite <- reverse_list_twice in Hmed. apply Hmed.
      * apply HmZ.
    + reflexivity.
  - destruct (overlap Z (find_confounders_in_path (v, u, rev l) G)) as [|] eqn:Hcon.
    + apply overlap_has_member_in_common in Hcon. destruct Hcon as [m [HmZ Hcon]].
      apply confounders_same_in_reverse_path in Hcon. destruct H as [_ [H _]]. apply no_overlap_non_member_rev with (x := m) in H.
      * exfalso. apply H. rewrite <- reverse_list_twice in Hcon. apply Hcon.
      * apply HmZ.
    + reflexivity.
  - unfold all_colliders_have_descendant_conditioned_on in *. apply forallb_true_iff_mem. intros m Hcol.
    apply colliders_same_in_reverse_path in Hcol. rewrite <- reverse_list_twice in Hcol. destruct H as [_ [_ H]]. apply forallb_true_iff_mem with (x := m) in H.
    + apply H.
    + apply Hcol.
Qed.

Lemma d_connected_path_not_d_separated: forall (u v: node) (l: nodes) (G: graph) (Z: nodes),
  d_connected_2 (u, v, l) G Z
  -> is_path_in_graph (u, v, l) G = true /\ acyclic_path_2 (u, v, l)
  -> d_separated_bool u v G Z = true -> False.
Proof.
  intros u v l G Z. intros Hconn [Hpath Hcyc] Hsep.
  assert (Hconn': exists (l: nodes), (acyclic_path_2 (u, v, l)) /\ (is_path_in_graph (u, v, l) G = true)
                                      /\ d_connected_2 (u, v, l) G Z).
  { exists l. split.
    - apply Hcyc.
    - split.
      + apply Hpath.
      + apply Hconn. }
  apply d_separated_vs_connected in Hconn'. rewrite Hconn' in Hsep. discriminate Hsep.
Qed.

Theorem d_separated_symmetry: forall (u v: node) (G: graph) (Z: nodes),
  d_separated_bool u v G Z = true -> d_separated_bool v u G Z = true.
Proof.
  intros u v G Z H.
  destruct (d_separated_bool v u G Z) as [|] eqn:Hd.
  - reflexivity.
  - apply d_separated_vs_connected in Hd. destruct Hd as [l Hl].
    assert (Hl': exists l: nodes, (acyclic_path_2 (u, v, l)) /\ (is_path_in_graph (u, v, l) G = true)
                                              /\ d_connected_2 (u, v, l) G Z).
    { exists (rev l). split.
      - apply reverse_path_still_acyclic. apply Hl.
      - split. apply reverse_path_in_graph. apply Hl. apply reverse_d_connected_paths. apply Hl. }
    apply d_separated_vs_connected in Hl'. rewrite Hl' in H. discriminate H.
Qed.

Theorem concat_d_connected_paths: forall (u v mid: node) (l1 l2: nodes) (G: graph) (Z: nodes),
  contains_cycle G = false -> is_path_in_graph (concat u mid v l1 l2) G = true
  -> d_connected_2 (u, mid, l1) G Z /\ d_connected_2 (mid, v, l2) G Z /\ acyclic_path_2 (concat u mid v l1 l2)
  -> (In mid (find_mediators_in_path (concat u mid v l1 l2) G) /\ ~ In mid Z)
     \/ (In mid (find_confounders_in_path (concat u mid v l1 l2) G) /\ ~ In mid Z)
     \/ (In mid (find_colliders_in_path (concat u mid v l1 l2) G) /\ (some_descendant_in_Z_bool (find_descendants mid G) Z = true))
  -> d_connected_2 (concat u mid v l1 l2) G Z.
Proof.
  intros u v mid l1 l2 G Z. intros HGcyc Hpath [H1 [H2 Hcyc]]. intros H.
  unfold d_connected_2 in *. repeat split.
  + destruct (overlap Z (find_mediators_in_path (concat u mid v l1 l2) G)) as [|] eqn:Hmeds.
    * apply overlap_has_member_in_common in Hmeds. destruct Hmeds as [m [HmZ Hmedm]].
      assert (Hmem: In m (l1 ++ mid :: l2)). { apply intermediate_node_in_path with (x := m) in Hpath. apply Hpath. left. apply Hmedm. }
      apply membership_append_or in Hmem. destruct Hmem as [Hm1 | Hm2].
      -- (* m must be a mediator of l1 *)
         assert (Hmedm1: In m (find_mediators_in_path (u, mid, l1) G)).
         { apply mediators_vs_edges_in_path in Hmedm. destruct Hmedm as [y [z [Hsub Hedge]]].
           apply sublist_breaks_down_list in Hsub.
           apply mediators_vs_edges_in_path. exists y. exists z. split.
           - apply membership_splits_list in Hm1. destruct Hm1 as [l1s [l1e Hl1]].
             destruct Hsub as [ps [pe Hp]]. simpl in Hp. pose proof Hp as Hp'. rewrite <- Hl1 in Hp. simpl in Hp.
             assert (Hvar: (ps ++ [y]) ++ [m] ++ z :: pe = (u :: l1s) ++ [m] ++ l1e ++ mid :: l2 ++ [v]).
             { simpl. rewrite <- app_assoc. simpl. unfold node. rewrite Hp. f_equal. simpl. rewrite <- app_assoc. simpl.
               rewrite <- app_assoc. simpl. reflexivity. }
             assert (Hvar': (u :: l1s) ++ [m] ++ l1e ++ mid :: l2 ++ [v] = u :: (l1 ++ mid :: l2) ++ [v]).
             { rewrite <- Hl1. simpl. f_equal. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
             assert (Hsubl: ps ++ [y] = u :: l1s /\ z :: pe = l1e ++ mid :: l2 ++ [v]).
             { apply acyclic_path_equate_sublists with (m := m). split.
               - unfold node in *. rewrite Hvar. rewrite Hvar'. unfold concat in Hcyc. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply Hcyc.
               - apply Hvar. }
             destruct Hsubl as [Hps Hpe].
             apply sublist_breaks_down_list. exists ps.
             destruct l1e as [| h1 t1].
             + simpl in Hpe. exists []. simpl. inversion Hpe. rewrite <- Hl1. simpl. rewrite <- app_assoc.
               unfold node in *. rewrite <- append_vs_concat. rewrite Hps. simpl. reflexivity.
             + inversion Hpe. exists (t1 ++ [mid]). simpl. rewrite <- Hl1. simpl.
               unfold node in *. rewrite <- append_vs_concat. rewrite Hps. simpl. f_equal.
               rewrite <- app_assoc. reflexivity.
           - apply Hedge. }
         destruct H1 as [H1 _]. apply no_overlap_non_member with (x := m) in H1.
         ++ exfalso. apply H1. apply HmZ.
         ++ apply Hmedm1.
      -- simpl in Hm2. destruct Hm2 as [Hmmid | Hm2].
         ++ destruct H as [Hmidmed | [Hmidcon | Hmidcol]].
            ** destruct Hmidmed as [Hmid HmidZ]. exfalso. apply HmidZ. rewrite Hmmid. apply HmZ.
            ** destruct Hmidcon as [Hmid HmidZ]. exfalso. apply HmidZ. rewrite Hmmid. apply HmZ.
            ** destruct Hmidcol as [Hmid HmidZ]. apply if_mediator_then_not_confounder_path in Hmedm.
               --- destruct Hmedm as [_ Hmedm]. exfalso. apply Hmedm. rewrite <- Hmmid. apply Hmid.
               --- apply HGcyc.
               --- apply Hcyc.
         ++ (* m must be a mediator of l2 *)
            assert (Hmedm2: In m (find_mediators_in_path (mid, v, l2) G)).
            { apply mediators_vs_edges_in_path in Hmedm. destruct Hmedm as [y [z [Hsub Hedge]]].
              apply sublist_breaks_down_list in Hsub.
              apply mediators_vs_edges_in_path. exists y. exists z. split.
              - apply membership_splits_list in Hm2. destruct Hm2 as [l2s [l2e Hl2]].
                destruct Hsub as [ps [pe Hp]]. simpl in Hp. pose proof Hp as Hp'. rewrite <- Hl2 in Hp. simpl in Hp.
                 assert (Hvar: (ps ++ [y]) ++ [m] ++ z :: pe = (u :: l1 ++ mid :: l2s) ++ [m] ++ l2e ++ [v]).
                 { simpl. rewrite <- app_assoc. simpl. unfold node. rewrite Hp. f_equal. simpl. rewrite <- app_assoc. simpl.
                    rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
                 assert (Hvar': (u :: l1 ++ mid :: l2s) ++ [m] ++ l2e ++ [v] = u :: (l1 ++ mid :: l2) ++ [v]).
                 { rewrite <- Hl2. simpl. f_equal. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
                assert (Hsubl: ps ++ [y] = u :: l1 ++ mid :: l2s /\ z :: pe = l2e ++ [v]).
                { apply acyclic_path_equate_sublists with (m := m). split.
                  - unfold node in *. rewrite Hvar. rewrite Hvar'. unfold concat in Hcyc. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply Hcyc.
                  - apply Hvar. }
                destruct Hsubl as [Hps Hpe].
                apply sublist_breaks_down_list.
                assert (Hlast: l2s = [] \/ exists (l: list nat), l2s = l ++ [y]).
                { apply last_elts_of_equal_lists_2 with (l1 := ps) (l2 := u :: l1 ++ [mid]). simpl. rewrite <- app_assoc. simpl. apply Hps. }
                destruct Hlast as [Hl2s | Hl2s].
                + exists []. exists pe. simpl. simpl in Hp. simpl in Hl2. rewrite <- Hl2. unfold node in *. rewrite Hpe.
                  rewrite Hl2s in Hps. apply last_elts_of_equal_lists with (l2 := u :: l1) in Hps. rewrite Hps. f_equal. rewrite Hl2s. simpl. reflexivity.
                + destruct Hl2s as [l2s' Hl2s]. exists (mid :: l2s'). exists pe. simpl. rewrite <- Hl2. rewrite Hl2s. unfold node in *. rewrite Hpe.
                  f_equal. simpl. rewrite <- app_assoc. simpl. rewrite append_vs_concat. reflexivity.
              - apply Hedge. }
            destruct H2 as [H2 _]. apply no_overlap_non_member with (x := m) in H2.
            ** exfalso. apply H2. apply HmZ.
            ** apply Hmedm2.
    * reflexivity.
  + destruct (overlap Z (find_confounders_in_path (concat u mid v l1 l2) G)) as [|] eqn:Hcons.
    * apply overlap_has_member_in_common in Hcons. destruct Hcons as [m [HmZ Hconm]].
      assert (Hmem: In m (l1 ++ mid :: l2)). { apply intermediate_node_in_path with (x := m) in Hpath. apply Hpath. right. left. apply Hconm. }
      apply membership_append_or in Hmem. destruct Hmem as [Hm1 | Hm2].
      -- (* m must be a confounder of l1 *)
         assert (Hconm1: In m (find_confounders_in_path (u, mid, l1) G)).
         { apply confounders_vs_edges_in_path in Hconm. destruct Hconm as [y [z [Hsub Hedge]]].
           apply sublist_breaks_down_list in Hsub.
           apply confounders_vs_edges_in_path. exists y. exists z. split.
           - apply membership_splits_list in Hm1. destruct Hm1 as [l1s [l1e Hl1]].
             destruct Hsub as [ps [pe Hp]]. simpl in Hp. pose proof Hp as Hp'. rewrite <- Hl1 in Hp. simpl in Hp.
             assert (Hvar: (ps ++ [y]) ++ [m] ++ z :: pe = (u :: l1s) ++ [m] ++ l1e ++ mid :: l2 ++ [v]).
             { simpl. rewrite <- app_assoc. simpl. unfold node. rewrite Hp. f_equal. simpl. rewrite <- app_assoc. simpl.
               rewrite <- app_assoc. simpl. reflexivity. }
             assert (Hvar': (u :: l1s) ++ [m] ++ l1e ++ mid :: l2 ++ [v] = u :: (l1 ++ mid :: l2) ++ [v]).
             { rewrite <- Hl1. simpl. f_equal. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
             assert (Hsubl: ps ++ [y] = u :: l1s /\ z :: pe = l1e ++ mid :: l2 ++ [v]).
             { apply acyclic_path_equate_sublists with (m := m). split.
               - unfold node in *. rewrite Hvar. rewrite Hvar'. unfold concat in Hcyc. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply Hcyc.
               - apply Hvar. }
             destruct Hsubl as [Hps Hpe].
             apply sublist_breaks_down_list. exists ps.
             destruct l1e as [| h1 t1].
             + simpl in Hpe. exists []. simpl. inversion Hpe. rewrite <- Hl1. simpl. rewrite <- app_assoc.
               unfold node in *. rewrite <- append_vs_concat. rewrite Hps. simpl. reflexivity.
             + inversion Hpe. exists (t1 ++ [mid]). simpl. rewrite <- Hl1. simpl.
               unfold node in *. rewrite <- append_vs_concat. rewrite Hps. simpl. f_equal.
               rewrite <- app_assoc. reflexivity.
           - apply Hedge. }
         destruct H1 as [_ [H1 _]]. apply no_overlap_non_member with (x := m) in H1.
         ++ exfalso. apply H1. apply HmZ.
         ++ apply Hconm1.
      -- simpl in Hm2. destruct Hm2 as [Hmmid | Hm2].
         ++ destruct H as [Hmidmed | [Hmidcon | Hmidcol]].
            ** destruct Hmidmed as [Hmid HmidZ]. exfalso. apply HmidZ. rewrite Hmmid. apply HmZ.
            ** destruct Hmidcon as [Hmid HmidZ]. exfalso. apply HmidZ. rewrite Hmmid. apply HmZ.
            ** destruct Hmidcol as [Hmid HmidZ]. apply if_confounder_then_not_mediator_path in Hconm.
               --- destruct Hconm as [_ Hconm]. exfalso. apply Hconm. rewrite <- Hmmid. apply Hmid.
               --- apply HGcyc.
               --- apply Hcyc.
         ++ (* m must be a confounder of l2 *)
            assert (Hconm2: In m (find_confounders_in_path (mid, v, l2) G)).
            { apply confounders_vs_edges_in_path in Hconm. destruct Hconm as [y [z [Hsub Hedge]]].
              apply sublist_breaks_down_list in Hsub.
              apply confounders_vs_edges_in_path. exists y. exists z. split.
              - apply membership_splits_list in Hm2. destruct Hm2 as [l2s [l2e Hl2]].
                destruct Hsub as [ps [pe Hp]]. simpl in Hp. pose proof Hp as Hp'. rewrite <- Hl2 in Hp. simpl in Hp.
                 assert (Hvar: (ps ++ [y]) ++ [m] ++ z :: pe = (u :: l1 ++ mid :: l2s) ++ [m] ++ l2e ++ [v]).
                 { simpl. rewrite <- app_assoc. simpl. unfold node. rewrite Hp. f_equal. simpl. rewrite <- app_assoc. simpl.
                    rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
                 assert (Hvar': (u :: l1 ++ mid :: l2s) ++ [m] ++ l2e ++ [v] = u :: (l1 ++ mid :: l2) ++ [v]).
                 { rewrite <- Hl2. simpl. f_equal. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
                assert (Hsubl: ps ++ [y] = u :: l1 ++ mid :: l2s /\ z :: pe = l2e ++ [v]).
                { apply acyclic_path_equate_sublists with (m := m). split.
                  - unfold node in *. rewrite Hvar. rewrite Hvar'. unfold concat in Hcyc. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply Hcyc.
                  - apply Hvar. }
                destruct Hsubl as [Hps Hpe].
                apply sublist_breaks_down_list.
                assert (Hlast: l2s = [] \/ exists (l: list nat), l2s = l ++ [y]).
                { apply last_elts_of_equal_lists_2 with (l1 := ps) (l2 := u :: l1 ++ [mid]). simpl. rewrite <- app_assoc. simpl. apply Hps. }
                destruct Hlast as [Hl2s | Hl2s].
                + exists []. exists pe. simpl. simpl in Hp. simpl in Hl2. rewrite <- Hl2. unfold node in *. rewrite Hpe.
                  rewrite Hl2s in Hps. apply last_elts_of_equal_lists with (l2 := u :: l1) in Hps. rewrite Hps. f_equal. rewrite Hl2s. simpl. reflexivity.
                + destruct Hl2s as [l2s' Hl2s]. exists (mid :: l2s'). exists pe. simpl. rewrite <- Hl2. rewrite Hl2s. unfold node in *. rewrite Hpe.
                  f_equal. simpl. rewrite <- app_assoc. simpl. rewrite append_vs_concat. reflexivity.
              - apply Hedge. }
            destruct H2 as [_ [H2 _]]. apply no_overlap_non_member with (x := m) in H2.
            ** exfalso. apply H2. apply HmZ.
            ** apply Hconm2.
    * reflexivity.
  + unfold all_colliders_have_descendant_conditioned_on. apply forallb_true_iff_mem. intros m Hcolm.
    assert (Hmem: In m (l1 ++ mid :: l2)). { apply intermediate_node_in_path with (x := m) in Hpath. apply Hpath. right. right. apply Hcolm. }
    apply membership_append_or in Hmem. destruct Hmem as [Hm1 | Hm2].
    * destruct H1 as [_ [_ H1]]. unfold all_colliders_have_descendant_conditioned_on in H1. apply forallb_true with (x := m) in H1.
      - apply H1.
      - apply colliders_vs_edges_in_path in Hcolm. destruct Hcolm as [y [z [Hsub Hedge]]].
        apply sublist_breaks_down_list in Hsub.
        apply colliders_vs_edges_in_path. exists y. exists z. split.
        -- apply membership_splits_list in Hm1. destruct Hm1 as [l1s [l1e Hl1]].
           destruct Hsub as [ps [pe Hp]]. simpl in Hp. pose proof Hp as Hp'. rewrite <- Hl1 in Hp. simpl in Hp.
           assert (Hvar: (ps ++ [y]) ++ [m] ++ z :: pe = (u :: l1s) ++ [m] ++ l1e ++ mid :: l2 ++ [v]).
           { simpl. rewrite <- app_assoc. simpl. unfold node. rewrite Hp. f_equal. simpl. rewrite <- app_assoc. simpl.
             rewrite <- app_assoc. simpl. reflexivity. }
           assert (Hvar': (u :: l1s) ++ [m] ++ l1e ++ mid :: l2 ++ [v] = u :: (l1 ++ mid :: l2) ++ [v]).
           { rewrite <- Hl1. simpl. f_equal. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
           assert (Hsubl: ps ++ [y] = u :: l1s /\ z :: pe = l1e ++ mid :: l2 ++ [v]).
           { apply acyclic_path_equate_sublists with (m := m). split.
             - unfold node in *. rewrite Hvar. rewrite Hvar'. unfold concat in Hcyc. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply Hcyc.
             - apply Hvar. }
           destruct Hsubl as [Hps Hpe].
           apply sublist_breaks_down_list. exists ps.
           destruct l1e as [| h1 t1].
           ++ simpl in Hpe. exists []. simpl. inversion Hpe. rewrite <- Hl1. simpl. rewrite <- app_assoc.
              unfold node in *. rewrite <- append_vs_concat. rewrite Hps. simpl. reflexivity.
           ++ inversion Hpe. exists (t1 ++ [mid]). simpl. rewrite <- Hl1. simpl.
              unfold node in *. rewrite <- append_vs_concat. rewrite Hps. simpl. f_equal.
              rewrite <- app_assoc. reflexivity.
         -- apply Hedge.
    * simpl in Hm2. destruct Hm2 as [Hmmid | Hm2].
      - destruct H as [Hmidmed | [Hmidcon | Hmidcol]].
        ** destruct Hmidmed as [Hmid HmidZ]. apply if_mediator_then_not_confounder_path in Hmid.
           --- destruct Hmid as [_ Hmid]. exfalso. apply Hmid. rewrite Hmmid in *. apply Hcolm.
           --- apply HGcyc.
           --- apply Hcyc.
        ** destruct Hmidcon as [Hmid HmidZ]. apply if_confounder_then_not_mediator_path in Hmid.
           --- destruct Hmid as [_ Hmid]. exfalso. apply Hmid. rewrite Hmmid in *. apply Hcolm.
           --- apply HGcyc.
           --- apply Hcyc.
        ** destruct Hmidcol as [Hmid HmidZ]. rewrite <- Hmmid. apply HmidZ.
      - destruct H2 as [_ [_ H2]]. unfold all_colliders_have_descendant_conditioned_on in H2. apply forallb_true with (x := m) in H2.
        { apply H2. }
        { apply colliders_vs_edges_in_path in Hcolm. destruct Hcolm as [y [z [Hsub Hedge]]].
          apply sublist_breaks_down_list in Hsub.
          apply colliders_vs_edges_in_path. exists y. exists z. split.
          - apply membership_splits_list in Hm2. destruct Hm2 as [l2s [l2e Hl2]].
            destruct Hsub as [ps [pe Hp]]. simpl in Hp. pose proof Hp as Hp'. rewrite <- Hl2 in Hp. simpl in Hp.
            assert (Hvar: (ps ++ [y]) ++ [m] ++ z :: pe = (u :: l1 ++ mid :: l2s) ++ [m] ++ l2e ++ [v]).
            { simpl. rewrite <- app_assoc. simpl. unfold node. rewrite Hp. f_equal. simpl. rewrite <- app_assoc. simpl.
              rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
            assert (Hvar': (u :: l1 ++ mid :: l2s) ++ [m] ++ l2e ++ [v] = u :: (l1 ++ mid :: l2) ++ [v]).
            { rewrite <- Hl2. simpl. f_equal. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
            assert (Hsubl: ps ++ [y] = u :: l1 ++ mid :: l2s /\ z :: pe = l2e ++ [v]).
            { apply acyclic_path_equate_sublists with (m := m). split.
              - unfold node in *. rewrite Hvar. rewrite Hvar'. unfold concat in Hcyc. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply Hcyc.
              - apply Hvar. }
            destruct Hsubl as [Hps Hpe].
            apply sublist_breaks_down_list.
            assert (Hlast: l2s = [] \/ exists (l: list nat), l2s = l ++ [y]).
            { apply last_elts_of_equal_lists_2 with (l1 := ps) (l2 := u :: l1 ++ [mid]). simpl. rewrite <- app_assoc. simpl. apply Hps. }
            destruct Hlast as [Hl2s | Hl2s].
            + exists []. exists pe. simpl. simpl in Hp. simpl in Hl2. rewrite <- Hl2. unfold node in *. rewrite Hpe.
              rewrite Hl2s in Hps. apply last_elts_of_equal_lists with (l2 := u :: l1) in Hps. rewrite Hps. f_equal. rewrite Hl2s. simpl. reflexivity.
            + destruct Hl2s as [l2s' Hl2s]. exists (mid :: l2s'). exists pe. simpl. rewrite <- Hl2. rewrite Hl2s. unfold node in *. rewrite Hpe.
              f_equal. simpl. rewrite <- app_assoc. simpl. rewrite append_vs_concat. reflexivity.
          - apply Hedge. }
Qed.

Theorem d_connected_cat: forall (u v h: node) (t: nodes) (G: graph) (Z: nodes),
  contains_cycle G = false
  -> acyclic_path_2 (u, v, h :: t)
  -> d_connected_2 (h, v, t) G Z
  -> (In h (find_mediators_in_path (u, v, h :: t) G) /\ ~ In h Z)
     \/ (In h (find_confounders_in_path (u, v, h :: t) G) /\ ~ In h Z)
     \/ (In h (find_colliders_in_path (u, v, h :: t) G) /\ (some_descendant_in_Z_bool (find_descendants h G) Z = true))
  -> d_connected_2 (u, v, h :: t) G Z.
Proof.
  intros u v h t G Z. intros HGcyc Hcyc H1. intros H.
  unfold d_connected_2 in *. repeat split.
  + apply no_overlap_non_member. intros m Hm Hm'.
    simpl in Hm. destruct t as [| h' t'].
    * simpl in Hm. destruct (is_mediator_bool u v h G || is_mediator_bool v u h G) as [|] eqn:Hmed.
      - assert (In h (find_mediators_in_path (u, v, [h]) G)). { simpl. rewrite Hmed. left. reflexivity. }
        apply if_mediator_then_not_confounder_path in H0. 2: { apply HGcyc. } 2: { apply Hcyc. }
        destruct H as [H | [H | H]].
        -- destruct H as [_ H]. destruct Hm as [Hm | Hm]. apply H. rewrite Hm. apply Hm'. apply Hm.
        -- destruct H0 as [H0 _]. apply H0. apply H.
        -- destruct H0 as [_ H0]. apply H0. apply H.
      - apply Hm.
    * simpl in Hm. destruct (is_mediator_bool u h' h G || is_mediator_bool h' u h G) as [|] eqn:Hmed.
      - assert (In h (find_mediators_in_path (u, v, h :: h' :: t') G)). { simpl. rewrite Hmed. left. reflexivity. }
        apply if_mediator_then_not_confounder_path in H0. 2: { apply HGcyc. } 2: { apply Hcyc. }
        destruct H as [H | [H | H]].
        -- destruct Hm as [Hm | Hm].
           ++ destruct H as [_ H]. apply H. rewrite Hm. apply Hm'.
           ++ destruct H1 as [H1 _]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
        -- destruct Hm as [Hm | Hm].
           ++ destruct H0 as [H0 _]. apply H0. apply H.
           ++ destruct H1 as [H1 _]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
        -- destruct Hm as [Hm | Hm].
           ++ destruct H0 as [_ H0]. apply H0. apply H.
           ++ destruct H1 as [H1 _]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
      - destruct H1 as [H1 _]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
  + apply no_overlap_non_member. intros m Hm Hm'.
    simpl in Hm. destruct t as [| h' t'].
    * simpl in Hm. destruct (is_confounder_bool u v h G) as [|] eqn:Hmed.
      - assert (In h (find_confounders_in_path (u, v, [h]) G)). { simpl. rewrite Hmed. left. reflexivity. }
        apply if_confounder_then_not_mediator_path in H0. 2: { apply HGcyc. } 2: { apply Hcyc. }
        destruct H as [H | [H | H]].
        -- destruct H0 as [H0 _]. apply H0. apply H.
        -- destruct H as [_ H]. destruct Hm as [Hm | Hm]. apply H. rewrite Hm. apply Hm'. apply Hm.
        -- destruct H0 as [_ H0]. apply H0. apply H.
      - apply Hm.
    * simpl in Hm. destruct (is_confounder_bool u h' h G) as [|] eqn:Hmed.
      - assert (In h (find_confounders_in_path (u, v, h :: h' :: t') G)). { simpl. rewrite Hmed. left. reflexivity. }
        apply if_confounder_then_not_mediator_path in H0. 2: { apply HGcyc. } 2: { apply Hcyc. }
        destruct H as [H | [H | H]].
        -- destruct Hm as [Hm | Hm].
           ++ destruct H0 as [H0 _]. apply H0. apply H.
           ++ destruct H1 as [_ [H1 _]]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
        -- destruct Hm as [Hm | Hm].
           ++ destruct H as [_ H]. apply H. rewrite Hm. apply Hm'.
           ++ destruct H1 as [_ [H1 _]]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
        -- destruct Hm as [Hm | Hm].
           ++ destruct H0 as [_ H0]. apply H0. apply H.
           ++ destruct H1 as [_ [H1 _]]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
      - destruct H1 as [_ [H1 _]]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
  + unfold all_colliders_have_descendant_conditioned_on. apply forallb_true_iff_mem. intros m Hcolm.
    pose proof Hcolm as H0. apply if_collider_then_not_mediator_path in H0.
    simpl in Hcolm. destruct t as [| h' t'].
    * simpl in Hcolm. destruct (is_collider_bool u v h G) as [|] eqn:Hcol.
      - destruct Hcolm as [Hcolm | Hcolm]. rewrite Hcolm in *. destruct H as [H | [H | H]].
        -- exfalso. destruct H0 as [H0 _]. apply H0. apply H.
        -- destruct H0 as [_ H0]. exfalso. apply H0. apply H.
        -- destruct H as [_ H]. apply H.
        -- exfalso. apply Hcolm.
      - exfalso. apply Hcolm.
    * simpl in Hcolm. destruct (is_collider_bool u h' h G) as [|] eqn:Hcol.
      - destruct Hcolm as [Hcolm | Hcolm].
        -- rewrite Hcolm in *. destruct H as [H | [H | H]].
           ++ exfalso. destruct H0 as [H0 _]. apply H0. apply H.
           ++ destruct H0 as [_ H0]. exfalso. apply H0. apply H.
           ++ destruct H as [_ H]. apply H.
        -- destruct H1 as [_ [_ H1]]. apply forallb_true with (x := m) in H1. apply H1. apply Hcolm.
      - destruct H1 as [_ [_ H1]]. apply forallb_true with (x := m) in H1. apply H1. apply Hcolm.
    * apply HGcyc.
    * apply Hcyc.
Qed.

Theorem subpath_still_d_connected_gen: forall (w u v: node) (l1 l2 l3 Z: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ d_connected_2 (w, v, l3) G Z
  -> d_connected_2 (u, v, l2) G Z.
Proof.
  intros w u v l1 l2 l3 Z G. intros [Hl3 H].
  unfold d_connected_2 in *. repeat split.
  - destruct H as [H _].
    destruct (overlap Z (find_mediators_in_path (u, v, l2) G)) as [|] eqn:Hover.
    + apply overlap_has_member_in_common in Hover. destruct Hover as [x [HxZ Hx]].
      apply no_overlap_non_member with (x := x) in H.
      * exfalso. apply H. apply HxZ.
      * apply subpath_preserves_mediators with (u := u) (l1 := l1) (l2 := l2). split. apply Hl3. left. apply Hx.
    + reflexivity.
  - destruct H as [_ [H _]].
    destruct (overlap Z (find_confounders_in_path (u, v, l2) G)) as [|] eqn:Hover.
    + apply overlap_has_member_in_common in Hover. destruct Hover as [x [HxZ Hx]].
      apply no_overlap_non_member with (x := x) in H.
      * exfalso. apply H. apply HxZ.
      * apply subpath_preserves_confounders with (u := u) (l1 := l1) (l2 := l2). split. apply Hl3. left. apply Hx.
    + reflexivity.
  - unfold all_colliders_have_descendant_conditioned_on in *. apply forallb_true_iff_mem. intros x Hx.
    destruct H as [_ [_ H]]. apply forallb_true with (x := x) in H.
    + apply H.
    + apply subpath_preserves_colliders with (u := u) (l1 := l1) (l2 := l2). split. apply Hl3. left. apply Hx.
Qed.

Theorem subpath_still_d_connected_gen_2: forall (w u v: node) (l1 l2 l3 Z: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ d_connected_2 (w, v, l3) G Z
  -> d_connected_2 (w, u, l1) G Z.
Proof.
  intros w u v l1 l2 l3 Z G. intros [Hl3 H].
  unfold d_connected_2 in *. repeat split.
  - destruct H as [H _].
    destruct (overlap Z (find_mediators_in_path (w, u, l1) G)) as [|] eqn:Hover.
    + apply overlap_has_member_in_common in Hover. destruct Hover as [x [HxZ Hx]].
      apply no_overlap_non_member with (x := x) in H.
      * exfalso. apply H. apply HxZ.
      * apply subpath_preserves_mediators with (u := u) (l1 := l1) (l2 := l2). split. apply Hl3. right. apply Hx.
    + reflexivity.
  - destruct H as [_ [H _]].
    destruct (overlap Z (find_confounders_in_path (w, u, l1) G)) as [|] eqn:Hover.
    + apply overlap_has_member_in_common in Hover. destruct Hover as [x [HxZ Hx]].
      apply no_overlap_non_member with (x := x) in H.
      * exfalso. apply H. apply HxZ.
      * apply subpath_preserves_confounders with (u := u) (l1 := l1) (l2 := l2). split. apply Hl3. right. apply Hx.
    + reflexivity.
  - unfold all_colliders_have_descendant_conditioned_on in *. apply forallb_true_iff_mem. intros x Hx.
    destruct H as [_ [_ H]]. apply forallb_true with (x := x) in H.
    + apply H.
    + apply subpath_preserves_colliders with (u := u) (l1 := l1) (l2 := l2). split. apply Hl3. right. apply Hx.
Qed.

Lemma subpath_still_d_connected: forall (G: graph) (u v h: node) (t Z: nodes),
  d_connected_2 (u, v, h :: t) G Z
  -> d_connected_2 (h, v, t) G Z.
Proof.
  intros G u v h t Z H.
  unfold d_connected_2 in *. repeat split.
  - destruct H as [H _].
    destruct (overlap Z (find_mediators_in_path (h, v, t) G)) as [|] eqn:Hover.
    + apply overlap_has_member_in_common in Hover. destruct Hover as [x [HxZ Hx]].
      apply no_overlap_non_member with (x := x) in H.
      * exfalso. apply H. apply HxZ.
      * apply mediators_vs_edges_in_path. apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [Hyz [[Hyx Hxz] | [Hxy Hzx]]]]].
        { exists y. exists z. repeat split.
          -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l2 [l3 Hl23]].
             exists (u :: l2). exists l3. simpl. rewrite <- Hl23. simpl. reflexivity.
          -- left. split. apply Hyx. apply Hxz. }
        { exists y. exists z. repeat split.
          -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l2 [l3 Hl23]].
             exists (u :: l2). exists l3. simpl. rewrite <- Hl23. simpl. reflexivity.
          -- right. split. apply Hxy. apply Hzx. }
    + reflexivity.
  - destruct H as [_ [H _]].
    destruct (overlap Z (find_confounders_in_path (h, v, t) G)) as [|] eqn:Hover.
    + apply overlap_has_member_in_common in Hover. destruct Hover as [x [HxZ Hx]].
      apply no_overlap_non_member with (x := x) in H.
      * exfalso. apply H. apply HxZ.
      * apply confounders_vs_edges_in_path. apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hyz [Hyx Hxz]]]].
        exists y. exists z. repeat split.
        -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l2 [l3 Hl23]].
           exists (u :: l2). exists l3. simpl. rewrite <- Hl23. simpl. reflexivity.
        -- apply Hyx.
        -- apply Hxz.
    + reflexivity.
  - unfold all_colliders_have_descendant_conditioned_on in *. apply forallb_true_iff_mem. intros x Hx.
    destruct H as [_ [_ H]]. apply forallb_true with (x := x) in H.
    + apply H.
    + apply colliders_vs_edges_in_path. apply colliders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hyz [Hyx Hxz]]]].
        exists y. exists z. repeat split.
        -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l2 [l3 Hl23]].
           exists (u :: l2). exists l3. simpl. rewrite <- Hl23. simpl. reflexivity.
        -- apply Hyx.
        -- apply Hxz.
Qed.
