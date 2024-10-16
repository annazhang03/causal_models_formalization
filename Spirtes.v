From FCM Require Export CausalModels.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Equalities.
Import ListNotations.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.PeanoNat.
Require Import Classical.


(* all nodes in the given list of colliders, cols, are ancestors of either u or v *)
Definition all_given_nodes_are_ancestors (cols: nodes) (u v: node) (G: graph) : Prop :=
  forall (c: node), In c cols -> In u (find_descendants c G) \/ In v (find_descendants c G).

Definition all_colliders_are_ancestors (p: path) (G: graph): Prop :=
  match p with
  | (u, v, l) => all_given_nodes_are_ancestors (find_colliders_in_path p G) u v G
  end.

(* return True iff all nodes in O on U are colliders in U *)
Definition observed_nodes_are_colliders (U: path) (O: nodes) (G: graph) : Prop :=
  match U with 
  | (u, v, l) => forall (x: node), In x O /\ In x l -> is_collider_in_path x U G
  end.

(* return True iff U is an inducing path on G over O
   According to Spirtes, this is true iff every non-endpoint member of O on U is a collider on U,
   and every collider on U is an ancestor of either A or B. *)
Definition inducing_path (U: path) (G: graph) (O: nodes) : Prop :=
  is_path_in_graph U G = true /\ all_colliders_are_ancestors U G 
                              /\ observed_nodes_are_colliders U O G.

Lemma inducing_path_out_of_A: forall G: graph, forall O: nodes, forall A B: node,
  contains_cycle G = false ->
  (exists U: path, path_start_and_end U A B = true /\ path_out_of_start U G = true /\ inducing_path U G O) ->
  (forall Z: nodes, subset Z (set_subtract O [A; B]) = true -> 
   exists p: path, is_path_in_graph p G = true /\ path_start_and_end p A B = true
                                                 /\ path_out_of_start p G = true
                                                 /\ d_connected_2 p G Z).
Proof.
  intros G O A B.
  intros Hcyc [U [HUse [HUout HUind]]].
  intros Z Hsub.
  (* if there are no colliders on U, then U d-connects A, B given Z *)
  destruct ((path_has_no_colliders U G)) as [|] eqn:HUcol.
  - exists U. split.
    + unfold inducing_path in HUind. destruct HUind as [Hpath _]. apply Hpath.
    + split. apply HUse. split. apply HUout.
      unfold d_connected_2. unfold inducing_path in HUind. destruct HUind as [Hpath [HcolAc HobsCol]].
      destruct U as [[u v] l].
      (* Lemma: since U has no colliders, and no mediators or confounders of U can be in O,
                no node can be a member of both l and Z. *)
      assert (Hlem: forall x: node, In x l /\ In x Z -> False).
      { intros x [Hxl HxZ].
        unfold observed_nodes_are_colliders in HobsCol.
        (* show that x is in O. This is true because Z \subseteq O\{A,B}, and x neq A or B *)
        assert (Hpathcyc: acyclic_path_2 (u, v, l)).
        { apply contains_cycle_false_correct with (G:=G). apply Hcyc. apply Hpath. }
        unfold path_start_and_end in HUse. simpl in HUse. apply split_and_true in HUse.
        destruct HUse as [HuA HvB]. apply eqb_eq in HuA. apply eqb_eq in HvB.
        assert (HxNeqAB: x <> A /\ x <> B).
        { apply intermediate_node_not_endpoint with (l:=l).
          split. apply Hxl. rewrite <- HuA. rewrite <- HvB. apply Hpathcyc. }
        assert (HxO: In x O).
        { assert (H1: subset Z (set_subtract O [A; B]) = true /\ In x Z). { split. apply Hsub. apply HxZ. }
          apply subset_larger_set_membership in H1.
          assert (H2: subset (set_subtract O [A; B]) O = true). { apply set_subtract_subset. }
          apply subset_larger_set_membership with (l1:=(set_subtract O [A; B])). split.
          apply H2. apply H1. }
        (* show a contradiction: x is a collider even though the path has no colliders *)
        assert (contra: is_collider_in_path x (u, v, l) G).
        { apply HobsCol. split. apply HxO. apply Hxl. }
        unfold path_has_no_colliders in HUcol. apply forallb_forall with (x:=x) in HUcol.
        apply is_collider_in_path_Prop_vs_bool in contra. rewrite contra in HUcol. 
        simpl in HUcol. discriminate HUcol. apply Hxl. }
      split.
      * (* since O contains only colliders on U, there are no mediators in Z *)
        apply no_overlap_non_member.
        intros x Hxmed HxZ.
        specialize (HobsCol x).
        assert (Hxl: In x l).
        { apply intermediate_node_in_path with (x:=x) in Hpath. apply Hpath. left. apply Hxmed. }
        apply Hlem with (x:=x). split. apply Hxl. apply HxZ.
      * split.
      { (* since O contains only colliders on U, there are no confounders in Z (very similar to above) *)
        apply no_overlap_non_member.
        intros x Hxcon HxZ.
        specialize (HobsCol x).
        assert (Hxl: In x l).
        { apply intermediate_node_in_path with (x:=x) in Hpath. apply Hpath. right. left. apply Hxcon. }
        apply Hlem with (x:=x). split. apply Hxl. apply HxZ. }
      { (* the path has no colliders, so this is trivially true *)
        unfold path_has_no_colliders in HUcol.
        assert ((find_colliders_in_path (u, v, l) G) = []).
        { destruct (find_colliders_in_path (u, v, l) G) as [| C t] eqn:HallCol.
          - reflexivity.
          - apply forallb_forall with (x:=C) in HUcol.
            assert (contra: is_collider_in_path C (u, v, l) G).
            { apply colliders_in_path. rewrite HallCol. simpl. left. reflexivity. }
            apply is_collider_in_path_Prop_vs_bool in contra. rewrite contra in HUcol.
            simpl in HUcol. discriminate HUcol.
            apply intermediate_node_in_path with (x:=C) in Hpath. apply Hpath. right. right.
            rewrite HallCol. simpl. left. reflexivity. }
        rewrite H. simpl. reflexivity. }
  - 
Admitted.



Lemma inducing_path_into_A: forall G: graph, forall O: nodes, forall A B: node,
  contains_cycle G = false ->
  (exists U: path, path_start_and_end U A B = true /\ path_into_start U G = true /\ inducing_path U G O) ->
  (forall Z: nodes, subset Z (set_subtract O [A; B]) = true -> 
   exists p: path, is_path_in_graph p G = true /\ path_start_and_end p A B = true
                                                 /\ path_into_start p G = true
                                                 /\ d_connected_2 p G Z).
Proof.
Admitted.

(* for an undirected path U in G from A to B, any node on U is an ancestor of A, B, or some collider on U *)
Theorem path_nodes_ancestors: forall U: path, forall G: graph, forall A B X: node,
  is_path_in_graph U G = true /\ path_start_and_end U A B = true /\ path_contains_node U X = true
  -> In X (find_ancestors A G) \/ In X (find_ancestors B G) 
     \/ (exists C, In C (find_colliders_in_path U G) /\ In X (find_ancestors C G)).
Proof. 
Admitted.


(* Lemma 3 from Spirtes
   If G is a DAG, and A and B are not d-separated by any subset Z of O\{A,B}, then 
   there is an inducing path over O between A and B.
*)
Lemma not_d_separated: forall G: graph, forall O: nodes, forall A B: node,
  contains_cycle G = false ->
  (forall Z: nodes, subset Z (set_subtract O [A; B]) = true -> (d_separated_bool A B G Z = false)) ->
  exists U: path, path_start_and_end U A B = true /\ inducing_path U G O.
Proof.
  intros G O A B.
  intros acyclic d_sep.
  destruct (is_edge (A, B) G) as [|] eqn:edgeAB.
  (* if (A, B) is an edge in G, then that edge is an inducing path *)
  - exists (A, B, []). split.
    + unfold path_start_and_end. simpl. rewrite eqb_refl. simpl. apply eqb_refl.
    + unfold inducing_path. split.
      * simpl. rewrite edgeAB. destruct G as [V E]. reflexivity.
      * split.
        (* no colliders, so trivially all colliders are ancestors of A or B *)
        -- cbn. unfold all_given_nodes_are_ancestors. intros c contra. 
           simpl in contra. exfalso. apply contra.
        (* no observed nodes that are also non-endpoints on U, so trivially all are colliders *)
        -- induction O as [| h t IH].
           ++ simpl. intros x [F1 F2]. apply F1.
           ++ simpl. intros x [_ F]. apply F.
  - destruct (is_edge (B, A) G) as [|] eqn:edgeBA.
    (* if (B, A) is an edge in G, then that edge is an inducing path *)
    + exists (A, B, []). split.
      * unfold path_start_and_end. simpl. rewrite eqb_refl. simpl. apply eqb_refl.
      * unfold inducing_path. split.
        -- simpl. rewrite edgeBA. rewrite orb_comm. destruct G as [V E]. reflexivity.
        -- split.
           (* no colliders, so trivially all colliders are ancestors of A or B *)
            --- simpl. unfold all_given_nodes_are_ancestors. intros c contra.
                simpl in contra. exfalso. apply contra.
            (* no observed nodes that are also non-endpoints on U, so trivially all are colliders *)
            --- induction O as [| h t IH].
                ++ simpl. intros x [F1 F2]. apply F1.
                ++ simpl. intros x [_ F]. apply F.
    (* neither (A, B) nor (B, A) are edges in G *)
    + remember (union (find_ancestors A G) (find_ancestors B G)) as allAnc. (* allAnc = anc(A) \cup anc(B) *)
      remember (intersect (set_subtract O [A; B]) allAnc) as O'. (* O' = allAnc \cap O\{A,B} *)
      specialize (d_sep O').
      assert (Hsubset: subset O' (set_subtract O [A; B]) = true).
      { rewrite HeqO'. apply intersect_correct. }
      apply d_sep in Hsubset.
      unfold d_separated_bool in Hsubset. 
      (* there is a path U between A and B, that is not blocked over O' *)
      apply demorgan_many_bool in Hsubset. destruct Hsubset as [U [HUpath HUblocked]].
      apply paths_start_to_end_correct in HUpath. destruct HUpath as [HUpath [HUse HUacyc]].
      exists U.
      split.
      * apply HUse.
      * unfold inducing_path. split.
        -- apply HUpath.
        -- assert (HcolAnc: all_colliders_are_ancestors U G). 
           (* assert first statement to use it in proof of second statement *)
           {(* show that for all colliders C in U, C is an ancestor of some member of O' *)
              assert (HcolInO': forall C: node, is_collider_in_path C U G 
                                -> exists d: node, In d O' /\ In d (find_descendants C G)).
              { intros C Hcol. unfold path_is_blocked_bool in HUblocked.
                rewrite orb_comm in HUblocked. apply orb_true_elim2 in HUblocked.
                unfold is_blocked_by_collider_2 in HUblocked.
                unfold collider_descendants_not_conditioned2 in HUblocked.
                remember (fun c : node => descendants_not_in_Z_bool (find_descendants c G) O') as P.
                remember (find_colliders_in_path U G) as ls.
                destruct (demorgan_many_bool_2 node P ls) as [Hf _].
                assert (Hfa: forall x : node, In x ls -> P x = false).
                { apply Hf. apply HUblocked. }
                specialize (Hfa C). 
                apply colliders_in_path in Hcol. rewrite <- Heqls in Hcol. apply Hfa in Hcol.
                rewrite HeqP in Hcol.
                unfold descendants_not_in_Z_bool in Hcol. (* exists a desc of C that is in O' *)
                apply demorgan_many_bool in Hcol. destruct Hcol as [desc [Hdesc HdescO]].
                exists desc. split. 
                - apply member_In_equiv. apply negb_both_sides in HdescO. simpl in HdescO. apply HdescO.
                - apply Hdesc. }
              (* since colliders are all ancestors of a member of O', then they must also be
                 ancestors of A or B *)
              destruct U as [[u v] l]. unfold all_colliders_are_ancestors.
              apply path_start_end_equal in HUse. destruct HUse as [HuA HvB].
              rewrite HuA. rewrite HvB.
              unfold all_given_nodes_are_ancestors. intros C Hcol. apply colliders_in_path in Hcol.
              rewrite HuA in HcolInO'. rewrite HvB in HcolInO'.
              assert (Hd: exists d : node, In d O' /\ In d (find_descendants C G)). 
              { apply HcolInO' in Hcol. apply Hcol. }
              destruct Hd as [d [HdO' Hdesc]].
              (* C is an ancestor of d, which is a member of O'
                 In order to show that C is an ancestor of A or B, can show that d is an ancestor of A or B *)
              assert (HdIsAnc: In d (find_ancestors A G) \/ In d (find_ancestors B G)).
              { rewrite HeqO' in HdO'. apply intersect_correct_element in HdO'.
                rewrite HeqallAnc in HdO'. apply union_correct in HdO'. apply HdO'. }
              destruct HdIsAnc as [HdA | HdB].
              ** left. assert (HAdescOfC: In d (find_descendants C G) /\ In A (find_descendants d G)).
                 { split. 
                   - apply Hdesc. 
                   - apply descendants_ancestors_correct. apply HdA. }
                 apply descendants_transitive in HAdescOfC. apply HAdescOfC.
              ** right. assert (HBdescOfC: In d (find_descendants C G) /\ In B (find_descendants d G)).
                 { split. 
                   - apply Hdesc. 
                   - apply descendants_ancestors_correct. apply HdB. }
                 apply descendants_transitive in HBdescOfC. apply HBdescOfC. }
            split.
            ++ apply HcolAnc.
            ++ unfold path_is_blocked_bool in HUblocked.
               apply split_orb_false in HUblocked. destruct HUblocked as [HUblocked Hcol].
               apply split_orb_false in HUblocked. destruct HUblocked as [Hmed Hcon].
               (* show that all mediators and confounders in U are not in O' *)
               assert (HmedNIn: forall M: node, In M (find_mediators_in_path U G)
                                    -> ~(In M O')).
               { intros M HisMed. unfold is_blocked_by_mediator_2 in Hmed.
                 apply no_overlap_non_member with (l2:=(find_mediators_in_path U G)).
                 - apply Hmed.
                 - apply HisMed. }
               assert (HconNIn: forall C: node, In C (find_confounders_in_path U G)
                                    -> ~(In C O')).
               { intros M HisCon. unfold is_blocked_by_confounder_2 in Hcon.
                 apply no_overlap_non_member with (l2:=(find_confounders_in_path U G)).
                 - apply Hcon.
                 - apply HisCon. }
               (* show that all nodes on U in O' are colliders *)
               destruct U as [[u v] l].
               assert (HallCol: forall C: node, In C l /\ In C O' -> is_collider_in_path C (u, v, l) G).
               { intros C [Hmem HCO'].
                 assert (H: is_path_in_graph (u, v, l) G = true /\ In C l). { split. apply HUpath. apply Hmem. }
                 destruct H as [H1 H2]. apply intermediate_node_in_path with (x:=C) in H1. apply H1 in H2.
                 destruct H2 as [contra | [contra | H]].
                 - specialize (HmedNIn C). apply HmedNIn in contra. unfold not in contra. apply contra in HCO'.
                   exfalso. apply HCO'.
                 - specialize (HconNIn C). apply HconNIn in contra. unfold not in contra. apply contra in HCO'.
                   exfalso. apply HCO'.
                 - apply colliders_in_path. apply H. }
               (* show that all nodes on U are ancestors of A or B *)
               assert (HallAnc: all_given_nodes_are_ancestors l A B G).
               { unfold all_given_nodes_are_ancestors. intros x Hmem.
                 assert (H: is_path_in_graph (u, v, l) G = true /\ 
                            path_start_and_end (u, v, l) A B = true /\ 
                            path_contains_node (u, v, l) x = true).
                 { split. apply HUpath. split. apply HUse. unfold path_contains_node.
                   simpl. apply member_In_equiv in Hmem. rewrite Hmem. apply orb_comm. }
                 apply path_nodes_ancestors in H. destruct H as [H | [H | H]].
                 - apply descendants_ancestors_correct in H. left. apply H.
                 - apply descendants_ancestors_correct in H. right. apply H.
                 - (* x is an ancestor of a collider C. Since C is an ancestor of A or B, x is too *)
                   destruct H as [C [HCcol HxC]].
                   apply path_start_end_equal in HUse. destruct HUse as [HuA HvB].
                   unfold all_colliders_are_ancestors in HcolAnc. unfold all_given_nodes_are_ancestors in HcolAnc.
                   specialize (HcolAnc C). apply HcolAnc in HCcol. destruct HCcol as [HAC | HBC].
                   + apply descendants_ancestors_correct in HxC. left. apply descendants_transitive with (y:=C).
                     split. apply HxC. rewrite HuA in HAC. apply HAC.
                   + apply descendants_ancestors_correct in HxC. right. apply descendants_transitive with (y:=C).
                     split. apply HxC. rewrite HvB in HBC. apply HBC. }
               apply path_start_end_equal in HUse. destruct HUse as [HuA HvB].
               (* since O' contains only colliders on U (HallCol), O must contain only nodes on U that are colliders *)
               unfold observed_nodes_are_colliders. intros x [HxO Hxl].
               unfold all_given_nodes_are_ancestors in HallAnc. specialize (HallAnc x).
               (* show that x in O\{A,B} *)
               assert (HxNeqAB: x =? A = false /\ x =? B = false).
               { rewrite eqb_neq. rewrite eqb_neq. apply intermediate_node_not_endpoint with (l:=l).
                 split. apply Hxl. rewrite <- HuA. rewrite <- HvB. apply HUacyc. }
               assert (HxOAB: In x (set_subtract O [A;B])).
               { apply set_subtract_membership. split.
                 - unfold not. intros H. simpl in H. destruct H as [H | [H | H]].
                   + destruct HxNeqAB as [HxNeqAB _]. rewrite H in HxNeqAB. rewrite eqb_refl in HxNeqAB. discriminate HxNeqAB.
                   + destruct HxNeqAB as [_ HxNeqAB]. rewrite H in HxNeqAB. rewrite eqb_refl in HxNeqAB. discriminate HxNeqAB.
                   + apply H.
                 - apply HxO. }
               (* show x is in allAnc (HallAnc) *)
               assert (HxAnc: In x allAnc).
               { apply HallAnc in Hxl. rewrite HeqallAnc. apply union_correct. destruct Hxl as [HAx | HBx].
                 - left. apply descendants_ancestors_correct. apply HAx.
                 - right. apply descendants_ancestors_correct. apply HBx. }
               specialize (HallCol x). apply HallCol. split.
               --- apply Hxl.
               --- rewrite HeqO'. apply intersect_in_both_lists. split. apply HxOAB. apply HxAnc.
Qed.

(* 
Steps:
1. functions: list union and intersection
2. proof: subset A (intersect A B) = true
3. proof: x in (union A B) => x in A || x in B
4. function: find ancestors of a node
5. proof: x descendant of y <=> y ancestor of x
6. proof: every vertex on U is an ancestor of A, B, or a collider on U
*)

(* Theorem 1 from Spirtes
   If G is a DAG over variables V, and O \subseteq V, then A and B are not d-separated 
   by any subset of O\{A, B} <=> there is an inducing path over O between A and B.
   TODO didn't use assumption that vertex_subset O G = true.
*)
Theorem d_separation_and_inducing_paths: forall G: graph, forall O: nodes, forall A B: node,
  contains_cycle G = false /\ vertex_subset O G = true ->
  (forall Z: nodes, subset Z (set_subtract O [A; B]) = true -> d_separated_bool A B G Z = false)
  <-> exists U: path, path_start_and_end U A B = true /\ inducing_path U G O.
Proof.
  intros G O A B.
  intros [acyclic subset].
  split.
  (* forward direction: G acyclic and A and B are not d-separated by any Z => exists an inducing path *)
  - apply not_d_separated. apply acyclic.
  (* backward direction: G acyclic and exists an inducing path between A and B => A and B not d-separated by any Z *)
  - intros [U HU]. intros Z subsetZ. apply d_separated_vs_connected. 
    destruct (path_into_start U G) as [|] eqn:Udir.
    (* inducing path goes into A, apply Lemma 2 *)
    + pose proof inducing_path_into_A as lemma.
      specialize (lemma G O A B).
      specialize (lemma acyclic).
      assert (H: path_start_and_end U A B = true /\ path_into_start U G = true /\ inducing_path U G O).
      { rewrite and_comm. rewrite and_assoc. rewrite and_comm. split.
        - rewrite and_comm. apply HU.
        - apply Udir. }
      specialize (lemma (ex_intro _ U H)).
      specialize (lemma Z subsetZ).
      destruct lemma as [p [p_in_graph [p_A_to_B [p_into_A p_d_conn]]]]. destruct p as [[u v] l].
      apply path_start_end_equal in p_A_to_B. destruct p_A_to_B as [HuA HvB].
      rewrite <- HuA. rewrite <- HvB. exists l.
      split. 
      * apply contains_cycle_false_correct with (G:=G). apply acyclic. apply p_in_graph.
      * split. apply p_in_graph. apply p_d_conn.
    (* inducing path goes out of A, apply Lemma 1 *)
    + pose proof inducing_path_out_of_A as lemma.
      specialize (lemma G O A B).
      specialize (lemma acyclic).
      assert (H: path_start_and_end U A B = true /\ path_out_of_start U G = true /\ inducing_path U G O).
      { rewrite and_comm. rewrite and_assoc. rewrite and_comm. split.
        - rewrite and_comm. apply HU.
        - apply path_must_have_direction in Udir. apply Udir.
          destruct HU as [UAB indpath].
          unfold inducing_path in indpath. destruct indpath as [p_in_G _]. apply p_in_G. }
      specialize (lemma (ex_intro _ U H)).
      specialize (lemma Z subsetZ).
      destruct lemma as [p [p_in_graph [p_A_to_B [p_out_of_A p_d_conn]]]]. destruct p as [[u v] l].
      apply path_start_end_equal in p_A_to_B. destruct p_A_to_B as [HuA HvB].
      rewrite <- HuA. rewrite <- HvB. exists l.
      split. 
      * apply contains_cycle_false_correct with (G:=G). apply acyclic. apply p_in_graph.
      * split. apply p_in_graph. apply p_d_conn.
Qed.