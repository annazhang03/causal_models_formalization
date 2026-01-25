From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import DSeparation.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.

Import ListNotations.


(* This file introduces the concept of unblocked ancestors.

   Given a node u and a conditioning set Z, a node w is an unblocked ancestor of u if
   either w = u, or there exists a directed path from w to u such that no internal
   nodes on the path (including w) are in Z *)


(* p represents a path backwards. Return nodes in path before any node in Z is reached *)
Fixpoint find_unblocked_members_of_nodes (p: nodes) (Z: nodes): nodes :=
  match p with
  | [] => []
  | h :: t => if (member h Z) then [] else h :: (find_unblocked_members_of_nodes t Z)
  end.

Lemma unblocked_member_means_in_path: forall (p: nodes) (Z: nodes) (a: node),
  In a (find_unblocked_members_of_nodes p Z) -> In a p /\ ~(In a Z).
Proof.
  intros p Z a H.
  induction p as [| h t IH].
  - simpl in H. exfalso. apply H.
  - simpl in H. destruct (member h Z) as [|] eqn:Hh.
    + exfalso. apply H.
    + destruct H as [H | H].
      * split. rewrite H. left. reflexivity. rewrite <- H. apply member_In_equiv_F. apply Hh.
      * apply IH in H. split. right. apply H. apply H.
Qed.

Lemma unblocked_member_means_in_path_2: forall (p: nodes) (Z: nodes) (a: node),
  In a (find_unblocked_members_of_nodes p Z) <-> exists (l1 l2: nodes), l1 ++ [a] ++ l2 = p /\ forall (x: node), In x (l1 ++ [a]) -> ~ In x Z.
Proof.
  intros p Z a. split.
  { intros H.
    induction p as [| h t IH].
    - simpl in H. exfalso. apply H.
    - simpl in H. destruct (member h Z) as [|] eqn:Hh.
      + exfalso. apply H.
      + destruct H as [H | H].
        * exists []. exists t. split. rewrite H. reflexivity. intros x Hx. simpl in Hx. destruct Hx as [Hx | Hx].
          rewrite <- Hx. rewrite <- H. apply member_In_equiv_F. apply Hh. exfalso. apply Hx.
        * apply IH in H. destruct H as [l1 [l2 H]]. exists (h :: l1). exists l2. split. destruct H as [H _]. rewrite <- H. reflexivity.
          intros x Hx. destruct Hx as [Hx | Hx]. rewrite <- Hx. apply member_In_equiv_F. apply Hh. apply H. apply Hx. }
  { intros [l1 [l2 [Hp Hx]]]. generalize dependent l1. induction p as [| h t IH].
    - intros l1 Hp Hx. destruct l1 as [| hl1 tl1]. discriminate Hp. discriminate Hp.
    - intros l1 Hp Hx. destruct l1 as [| hl1 tl1].
      + inversion Hp. simpl. destruct (member h Z) as [|] eqn:Hh.
        * exfalso. assert (Hh': ~ In h Z). { apply Hx. left. apply H0. } apply Hh'. apply member_In_equiv. apply Hh.
        * left. reflexivity.
      + inversion Hp. simpl. destruct (member h Z) as [|] eqn:Hh.
        * exfalso. assert (Hh': ~ In h Z). { apply Hx. left. apply H0. } apply Hh'. apply member_In_equiv. apply Hh.
        * right. rewrite H1. apply IH with (l1 := tl1). apply H1. intros x Hxmem. apply Hx. right. apply Hxmem. }
Qed.



(* does NOT include the end node of any path *)
Fixpoint find_unblocked_ancestors_given_paths (P: paths) (Z: nodes): nodes :=
  match P with
  | [] => []
  | p :: P' => match p with
               | (u, v, l) => (find_unblocked_members_of_nodes ((rev l) ++ [u]) Z) ++ (find_unblocked_ancestors_given_paths P' Z)
               end
  end.

Lemma in_unblocked_ancestors_of_some_path: forall (P: paths) (Z: nodes) (a: node),
  In a (find_unblocked_ancestors_given_paths P Z)
  <-> exists (p: path), In p P /\ In a (find_unblocked_members_of_nodes ((rev (path_int p)) ++ [path_start p]) Z).
Proof.
  intros P Z a. split.
  { intros Ha.
    induction P as [| hp tp IH].
    - simpl in Ha. exfalso. apply Ha.
    - simpl in Ha. destruct hp as [[uh vh] lh].
      apply membership_append_or in Ha. destruct Ha as [Ha | Ha].
      + exists (uh, vh, lh). split. left. reflexivity. simpl. apply Ha.
      + apply IH in Ha. destruct Ha as [p Hp]. exists p. split. right. apply Hp. apply Hp. }
  { intros [p [Hp Ha]]. induction P as [| hp tp IH].
    - exfalso. apply Hp.
    - destruct Hp as [Hp | Hp].
      + simpl. destruct hp as [[uh vh] lh]. apply membership_append. rewrite <- Hp in Ha. simpl in Ha. apply Ha.
      + apply IH in Hp. simpl. destruct hp as [[uh vh] lh]. apply membership_append_r. apply Hp. }
Qed.


(* return all ancestors of u with an unblocked directed path to u *)
Definition find_unblocked_ancestors (G: graph) (v: node) (Z: nodes): nodes :=
  v :: (find_unblocked_ancestors_given_paths (find_directed_paths_to_end v G) Z).


Theorem unblocked_ancestors_have_unblocked_directed_path: forall (G: graph) (v a: node) (Z: nodes),
  In a (find_unblocked_ancestors G v Z)
  <-> (a = v)
      \/ (exists (l: nodes), is_directed_path_in_graph (a, v, l) G = true
         /\ acyclic_path_2 (a, v, l)
         /\ forall (w: node), (w = a \/ In w l) -> ~(In w Z)).
Proof.
  (* path can be acyclic because if there is a directed path, can remove cycle *)
  intros G v a Z. split.
  - intros H. unfold find_unblocked_ancestors in H. simpl in H. destruct H as [H | H].
    + left. rewrite H. reflexivity.
    + right. apply in_unblocked_ancestors_of_some_path in H. destruct H as [p [Hp Ha]].
      destruct p as [[u v'] l].
      assert (Hv: v' = v).
      { unfold find_directed_paths_to_end in Hp. apply filter_true in Hp. destruct Hp as [_ Hp]. simpl in Hp. apply eqb_eq. apply Hp. }
      rewrite Hv in *. clear Hv. apply unblocked_member_means_in_path_2 in Ha as Ha'. destruct Ha' as [l1 [l2 [Hal HlZ]]]. simpl in Ha. simpl in Hal.
      exists (rev l1). rewrite <- and_assoc. split.
      * apply directed_paths_to_end_correct in Hp. apply path_breaks_down_midpoint_vs_endpoint in Hal.
        destruct (rev l2) as [| hl2 tl2] eqn:Hl2.
        -- destruct Hal as [Hal _]. assert (Hal': a = u /\ l1 = rev l). { apply Hal. apply Hl2. }
           destruct Hal' as [Ha' Hl1]. rewrite Ha'. rewrite Hl1. rewrite <- reverse_list_twice. split. apply Hp. apply Hp.
        -- destruct Hal as [_ Hal]. specialize Hal with (hl2 := hl2) (tl2 := tl2). assert (Hal': u = hl2 /\ rev l = l1 ++ [a] ++ rev tl2). { apply Hal. apply Hl2. }
           destruct Hal' as [Hu Hl]. split.
           { apply subpath_still_directed with (w := u) (l1 := tl2) (l3 := l). split.
             rewrite reverse_list_twice with (l := l). unfold nodes in *. unfold node in *. rewrite Hl. rewrite reverse_list_append. simpl.
             rewrite <- reverse_list_twice. rewrite <- app_assoc. reflexivity. apply Hp. }
           { apply subpath_still_acyclic with (w := u) (l1 := tl2) (l3 := l). split.
             rewrite reverse_list_twice with (l := l). unfold nodes in *. unfold node in *. rewrite Hl. rewrite reverse_list_append. simpl.
             rewrite <- reverse_list_twice. rewrite <- app_assoc. reflexivity. apply Hp. }
      * intros w Hw. apply HlZ. destruct Hw as [Hw | Hw]. apply membership_append_r. left. symmetry. apply Hw. apply membership_append. apply membership_rev. apply Hw.
  - intros [H | H].
    + unfold find_unblocked_ancestors. simpl. left. rewrite H. reflexivity.
    + destruct H as [l [Hp [Hc Hw]]]. unfold find_unblocked_ancestors. right. apply in_unblocked_ancestors_of_some_path.
      exists (a, v, l). split.
      * apply directed_paths_to_end_correct. split. apply Hp. split. simpl. apply eqb_refl. apply Hc.
      * simpl. apply unblocked_member_means_in_path_2. exists (rev l). exists []. split. rewrite append_identity. reflexivity.
        intros x Hx. apply Hw. apply membership_append_or in Hx. destruct Hx as [Hx | [Hx | Hx]]. right. apply membership_rev. apply Hx.
        left. symmetry. apply Hx. exfalso. apply Hx.
Qed.

Lemma colliders_have_unblocked_path_to_descendant: forall (G: graph) (Z: nodes) (c: node) (p: path),
  In c (find_colliders_in_path p G)
  -> d_connected_2 p G Z
  -> In c Z \/
     (~ In c Z
       /\ exists (z: node) (dp: nodes), is_directed_path_in_graph (c, z, dp) G = true /\ acyclic_path_2 (c, z, dp)
                                        /\ overlap dp Z = false /\ In z Z).
Proof.
  intros G Z c p Hc Hp.
  unfold d_connected_2 in Hp. destruct Hp as [_ [_ Hp]]. unfold all_colliders_have_descendant_conditioned_on in Hp.
  apply forallb_true_iff_mem with (x := c) in Hp.
  - unfold some_descendant_in_Z_bool in Hp. apply overlap_has_member_in_common in Hp. destruct Hp as [d [Hd HdZ]].
    apply find_descendants_correct in Hd. destruct Hd as [Hcd | Hd].
    + left. rewrite Hcd. apply HdZ.
    + destruct Hd as [dp [Hdp Hcd]]. destruct dp as [[c' d'] dp]. apply path_start_end_equal in Hcd. destruct Hcd as [Hc' Hd'].
      rewrite Hc' in *. rewrite Hd' in *. clear Hc'. clear Hd'.

      remember (length dp) as n.
      assert (Hn: exists (n': nat), n' = length dp /\ n' <= n). { exists n. split. apply Heqn. lia. }
      clear Heqn.

      generalize dependent d. generalize dependent dp. induction n as [| n' IH].
      * intros dp Hn d Hdp HdZ. destruct Hn as [n' [Hn' H0]]. assert (Hn0: n' = 0). { lia. }
        assert (Hl: dp = []). { destruct dp as [| hdp tdp]. reflexivity. rewrite Hn0 in Hn'. simpl in Hn'. discriminate Hn'. }
        destruct (member c Z) as [|] eqn:HcZ.
        -- left. apply member_In_equiv. apply HcZ.
        -- right. split. apply member_In_equiv_F. apply HcZ. exists d. exists []. split. rewrite Hl in Hdp. apply Hdp. repeat split.
           ++ intros Hcd. rewrite Hcd in HcZ. apply member_In_equiv_F in HcZ. apply HcZ. apply HdZ.
           ++ intros F. apply F.
           ++ intros F. apply F.
           ++ apply HdZ.
      * intros dp Hn d Hdp HdZ. destruct (overlap dp Z) as [|] eqn:Hover.
        -- apply overlap_has_member_in_common in Hover. destruct Hover as [z [Hz HzZ]]. apply membership_splits_list in Hz.
           destruct Hz as [dp1 [dp2 Hdp12]].
           specialize IH with (dp := dp1) (d := z). apply IH.
           ++ exists (length dp1). split. reflexivity. destruct Hn as [n [Hndp Hnn']].
              assert (Hlen: length (dp1 ++ [z] ++ dp2) = n). { rewrite Hdp12. symmetry. apply Hndp. }
              rewrite length_app in Hlen. simpl in Hlen. lia.
           ++ apply subpath_still_directed_2 with (v := d) (l2 := dp2) (l3 := dp). split. apply Hdp12. apply Hdp.
           ++ apply HzZ.
        -- destruct (member c Z) as [|] eqn:HcZ.
           ++ left. apply member_In_equiv. apply HcZ.
           ++ right. split. apply member_In_equiv_F. apply HcZ.
              apply directed_path_can_be_acyclic in Hdp. destruct Hdp as [dp' Hdp].
              exists d. exists dp'. split. apply Hdp. split. apply Hdp. split.
              ** apply no_overlap_non_member. intros x Hx1 Hx2. apply no_overlap_non_member with (x := x) in Hover.
                 apply Hover. apply subset_larger_set_membership with (l1 := dp'). split. apply Hdp. apply Hx2. apply Hx1.
              ** apply HdZ.
              ** intros Hcd. apply member_In_equiv_F in HcZ. apply HcZ. rewrite Hcd. apply HdZ.
  - apply Hc.
Qed.


Theorem acyclic_path_if_common_ancestor: forall (u v anc: node) (lv lu: nodes) (Z: nodes) (G: graph) (len: nat),
  u <> v /\ ~(In u (find_unblocked_ancestors G v Z)) /\ ~(In v (find_unblocked_ancestors G u Z))
  -> length lu < len
  -> is_directed_path_in_graph (anc, v, lv) G = true /\ acyclic_path_2 (anc, v, lv) /\ (forall w : node, w = anc \/ In w lv -> ~ In w Z)
  -> is_directed_path_in_graph (anc, u, lu) G = true /\ acyclic_path_2 (anc, u, lu) /\ (forall w : node, w = anc \/ In w lu -> ~ In w Z)
  -> exists (anc': node) (lu' lv': nodes), is_directed_path_in_graph (anc', u, lu') G = true /\ is_directed_path_in_graph (anc', v, lv') G = true
      /\ (forall w : node, w = anc' \/ In w lu' \/ In w lv' -> ~ In w Z) /\ acyclic_path_2 (u, v, (rev lu') ++ (anc' :: lv')).
Proof.
  intros u v anc lv lu Z G len. intros [Huv [HuvZ HvuZ]] Hlen [Hdirv [Hcycv HlvZ]]. intros [Hdiru [Hcycu HluZ]].
  (* u <- ..lu.. <- anc -> ..lv.. -> v *)
  generalize dependent anc. generalize dependent lv. generalize dependent lu. induction len as [| len' IH].
  - intros lu Hlen lv anc Hdirv Hcycv HlvZ Hdiru Hcycu HluZ. lia. (* Hlen *)
  - intros lu Hlen lv anc Hdirv Hcycv HlvZ Hdiru Hcycu HluZ.
    (* u <- ..lu.. <- anc -> ..lv.. -> v *)
    destruct (overlap lu lv) as [|] eqn:Hover.
    { apply overlap_has_member_in_common in Hover. destruct Hover as [x [Hxlu Hxlv]].
      apply membership_splits_list in Hxlu. destruct Hxlu as [lu1 [lu2 Hxlu]].
      apply membership_splits_list in Hxlv. destruct Hxlv as [lv1 [lv2 Hxlv]].
      (* u <- ..lu2.. <- x -> ..lv2.. -> v *)
      specialize IH with (lu := lu2) (lv := lv2) (anc := x). apply IH.
      - apply sublist_length_less with (l1 := (lu1 ++ [x])) (l3 := lu). repeat split.
        + apply Hlen.
        + rewrite <- app_assoc. apply Hxlu.
        + destruct lu1 as [| hlu1 tlu1]. intros F. discriminate F. intros F. discriminate F.
      - apply subpath_still_directed with (w := anc) (l1 := lv1) (l3 := lv). split. apply Hxlv. apply Hdirv.
      - apply subpath_still_acyclic with (w := anc) (l1 := lv1) (l3 := lv). split. apply Hxlv. apply Hcycv.
      - intros w Hw. apply HlvZ. right. destruct Hw as [Hw | Hw].
        + apply membership_splits_list. rewrite Hw. exists lv1. exists lv2. apply Hxlv.
        + apply sublist_member with (l1 := lv2). split. apply Hw. apply sublist_breaks_down_list. exists (lv1 ++ [x]). exists [].
          rewrite append_identity. rewrite <- app_assoc. apply Hxlv.
      - apply subpath_still_directed with (w := anc) (l1 := lu1) (l3 := lu). split. apply Hxlu. apply Hdiru.
      - apply subpath_still_acyclic with (w := anc) (l1 := lu1) (l3 := lu). split. apply Hxlu. apply Hcycu.
      - intros w Hw. apply HluZ. right. destruct Hw as [Hw | Hw].
        + apply membership_splits_list. rewrite Hw. exists lu1. exists lu2. apply Hxlu.
        + apply sublist_member with (l1 := lu2). split. apply Hw. apply sublist_breaks_down_list. exists (lu1 ++ [x]). exists [].
          rewrite append_identity. rewrite <- app_assoc. apply Hxlu. }
    { (* no overlap, so already acyclic - use original paths. *)
      exists anc. exists lu. exists lv. split. apply Hdiru. split. apply Hdirv. split.
      + intros w [Hw | [Hw | Hw]].
        * apply HluZ. left. apply Hw.
        * apply HluZ. right. apply Hw.
        * apply HlvZ. right. apply Hw.
      + apply concat_paths_acyclic. split. apply Huv. split.
        * apply reverse_path_still_acyclic. apply Hcycu.
        * apply Hcycv.
        * split. (* u and v cannot be unblocked ancestors of each other *)
          { intros Hu. apply HuvZ. apply unblocked_ancestors_have_unblocked_directed_path. right.
            pose proof Hu as Hu'. apply membership_splits_list in Hu. destruct Hu as [l1 [l2 Hu]]. exists l2. split.
            ++ apply subpath_still_directed with (w := anc) (l1 := l1) (l3 := lv). split. apply Hu. apply Hdirv.
            ++ split.
               ** apply subpath_still_acyclic with (w := anc) (l1 := l1) (l3 := lv). split. apply Hu. apply Hcycv.
                ** intros w Hw. destruct Hw as [Hw | Hw].
                  --- apply HlvZ. right. rewrite Hw. apply Hu'.
                  --- apply HlvZ. right. apply sublist_member with (l1 := l2). split. apply Hw. apply sublist_breaks_down_list.
                      exists (l1 ++ [u]). exists []. rewrite append_identity. rewrite <- app_assoc. apply Hu. }
          { intros Hv. apply membership_rev in Hv. rewrite <- reverse_list_twice in Hv.
            apply HvuZ. apply unblocked_ancestors_have_unblocked_directed_path. right.
            pose proof Hv as Hv'. apply membership_splits_list in Hv. destruct Hv as [l1 [l2 Hv]]. exists l2. split.
            ++ apply subpath_still_directed with (w := anc) (l1 := l1) (l3 := lu). split. apply Hv. apply Hdiru.
            ++ split.
               ** apply subpath_still_acyclic with (w := anc) (l1 := l1) (l3 := lu). split. apply Hv. apply Hcycu.
               ** intros w Hw. destruct Hw as [Hw | Hw].
                  --- apply HluZ. right. rewrite Hw. apply Hv'.
                  --- apply HluZ. right. apply sublist_member with (l1 := l2). split. apply Hw. apply sublist_breaks_down_list.
                      exists (l1 ++ [v]). exists []. rewrite append_identity. rewrite <- app_assoc. apply Hv. }
        * destruct (overlap (rev lu) lv) as [|] eqn:Hover'.
          -- apply overlap_has_member_in_common in Hover'. destruct Hover' as [x [Hx1 Hx2]].
             apply no_overlap_non_member_rev with (x := x) in Hover.
             ++ exfalso. apply Hover. apply Hx2.
             ++ apply membership_rev. apply Hx1.
          -- reflexivity. }
Qed.


Theorem acyclic_paths_intersect_if_common_endpoint: forall (anc1 anc2 z: node) (l1 l2: nodes) (Z: nodes) (G: graph),
  contains_cycle G = false
  -> is_directed_path_in_graph (anc1, z, l1) G = true /\ acyclic_path_2 (anc1, z, l1) /\ (forall w : node, w = anc1 \/ In w l1 -> ~ In w Z)
  -> is_directed_path_in_graph (anc2, z, l2) G = true /\ acyclic_path_2 (anc2, z, l2) /\ (forall w : node, w = anc2 \/ In w l2 -> ~ In w Z)
  -> overlap l1 l2 = false \/
     exists (l2': nodes), is_directed_path_in_graph (anc2, z, l2') G = true /\ acyclic_path_2 (anc2, z, l2')
      /\ (forall w : node, (w = anc2 \/ In w l2') -> ~ In w Z)
      /\ exists (l1'' l2'': nodes) (l3 l3': nodes) (x: node), l1 = l1'' ++ [x] ++ l3 /\ l2' = l2'' ++ [x] ++ l3 /\ l2 = l2'' ++ [x] ++ l3' /\ overlap l1'' l2'' = false.
Proof.
  intros anc1 anc2 z l1 l2 Z G. intros HG [Hdir1 [Hcyc1 HZ1]] [Hdir2 [Hcyc2 HZ2]].
  destruct (overlap l1 l2) as [|] eqn:Hover.
  - right.
    assert (H: exists (l1' l1'' l2' l2'': list nat) (x: nat), l1 = l1' ++ [x] ++ l1'' /\ l2 = l2' ++ [x] ++ l2'' /\ overlap l1' l2' = false).
    { apply lists_have_first_elt_in_common. apply Hover. }
    destruct H as [l1' [l1'' [l2' [l2'' [x [Hl1 [Hl2 Hover']]]]]]].
    exists (l2' ++ [x] ++ l1''). split.
    -- apply concat_directed_paths. split.
       ++ apply subpath_still_directed_2 with (v := z) (l2 := l2'') (l3 := l2). split. symmetry. apply Hl2. apply Hdir2.
       ++ apply subpath_still_directed with (w := anc1) (l1 := l1') (l3 := l1). split. symmetry. apply Hl1. apply Hdir1.
    -- split.
       ++ apply concat_paths_acyclic.
          ** split.
             --- unfold acyclic_path_2 in Hcyc2. destruct Hcyc2 as [Hcyc2 _]. apply Hcyc2.
             --- split.
                 +++ apply subpath_still_acyclic_2 with (v := z) (l2 := l2'') (l3 := l2). split. symmetry. apply Hl2. apply Hcyc2.
                 +++ apply subpath_still_acyclic with (w := anc1) (l1 := l1') (l3 := l1). split. symmetry. apply Hl1. apply Hcyc1.
          ** split.
             --- intros H. (* cycle anc2 -> ..l2'.. -> x -> ..l1''.. *)
                 apply membership_splits_list in H. destruct H as [c1 [c2 Hc]].
                 assert (Hcyc: is_directed_path_in_graph (anc2, anc2, l2' ++ [x] ++ c1) G = true).
                 { apply concat_directed_paths. split.
                   - apply subpath_still_directed_2 with (v := z) (l2 := l2'') (l3 := l2). split. symmetry. apply Hl2. apply Hdir2.
                   - apply subpath_still_directed_2 with (v := z) (l2 := c2) (l3 := l1''). split. apply Hc.
                     apply subpath_still_directed with (w := anc1) (l1 := l1') (l3 := l1). split. symmetry. apply Hl1. apply Hdir1. }
                 apply contains_cycle_false_correct with (p := (anc2, anc2, l2' ++ [x] ++ c1)) in HG.
                 +++ unfold acyclic_path_2 in HG. destruct HG as [HG _]. apply HG. reflexivity.
                 +++ admit.
                 +++ apply Hcyc.
             --- intros H. unfold acyclic_path_2 in Hcyc2. destruct Hcyc2 as [_ [_ [Hcyc2 _]]]. apply Hcyc2. apply membership_append with (l2 := [x] ++ l2'') in H.
                 rewrite Hl2. apply H.
          ** destruct (overlap l2' l1'') as [|] eqn:F.
             apply overlap_has_member_in_common in F. destruct F as [x' [Hx2' Hx1']]. apply membership_splits_list in Hx2'. destruct Hx2' as [s1 [s2 Hs]].
             apply membership_splits_list in Hx1'. destruct Hx1' as [t1 [t2 Ht]].
             assert (Hcyc: is_directed_path_in_graph (x', x', s2 ++ [x] ++ t1) G = true).
             { apply concat_directed_paths. split.
               - apply subpath_still_directed with (w := anc2) (l1 := s1) (l3 := l2'). split. apply Hs.
                 apply subpath_still_directed_2 with (v := z) (l2 := l2'') (l3 := l2). split. symmetry. apply Hl2. apply Hdir2.
               - apply subpath_still_directed_2 with (v := z) (l2 := t2) (l3 := l1''). split. apply Ht.
                 apply subpath_still_directed with (w := anc1) (l1 := l1') (l3 := l1). split. symmetry. apply Hl1. apply Hdir1. }
             apply contains_cycle_false_correct with (p := (x', x', s2 ++ [x] ++ t1)) in HG.
             +++ unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
             +++ admit.
             +++ apply Hcyc.
             +++ reflexivity.
       ++ split.
          ** intros w Hw. destruct Hw as [Hw | Hw].
             --- apply HZ2. left. apply Hw.
             --- apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                 +++ apply HZ2. right. apply membership_append with (l2 := [x] ++ l2'') in Hw. rewrite Hl2. apply Hw.
                 +++ apply HZ1. right. apply membership_append_r with (l1 := l1') in Hw. rewrite Hl1. apply Hw.
          ** exists l1'. exists l2'. exists l1''. exists l2''. exists x. repeat split.
             --- apply Hl1.
             --- apply Hl2.
             --- apply Hover'.
  - left. reflexivity.
Admitted.


Lemma unblocked_ancestor_if_in_unblocked_directed_path: forall (anc u v: node) (l Z: nodes) (G: graph),
  is_directed_path_in_graph (anc, v, l) G = true /\ acyclic_path_2 (anc, v, l) /\ (forall w : node, w = anc \/ In w l -> ~ In w Z)
  -> In u l
  -> In u (find_unblocked_ancestors G v Z).
Proof.
  intros anc u v l Z G. intros [Hdir [Hcyc HlZ]]. intros Hu.
  apply unblocked_ancestors_have_unblocked_directed_path. right.
  - apply membership_splits_list in Hu. destruct Hu as [l1 [l2 Hl]].
    exists l2. split.
    + apply subpath_still_directed with (w := anc) (l1 := l1) (l3 := l). split. apply Hl. apply Hdir.
    + split.
      * apply subpath_still_acyclic with (w := anc) (l1 := l1) (l3 := l). split. apply Hl. apply Hcyc.
      * intros w Hw. apply HlZ. right. destruct Hw as [Hw | Hw].
        -- apply membership_splits_list. rewrite Hw. exists l1. exists l2. apply Hl.
        -- apply sublist_member with (l1 := l2). split. apply Hw. apply sublist_breaks_down_list. exists (l1 ++ [u]). exists [].
           rewrite append_identity. rewrite <- app_assoc. apply Hl.
Qed.

Lemma unblocked_ancestor_if_in_unblocked_directed_path_2: forall (anc u v: node) (l Z: nodes) (G: graph),
  is_directed_path_in_graph (anc, v, l) G = true /\ acyclic_path_2 (anc, v, l) /\ (forall w : node, w = anc \/ In w l -> ~ In w Z)
  -> In u l
  -> In anc (find_unblocked_ancestors G u Z).
Proof.
  intros anc u v l Z G. intros [Hdir [Hcyc HlZ]]. intros Hu.
  apply unblocked_ancestors_have_unblocked_directed_path. right.
  - apply membership_splits_list in Hu. destruct Hu as [l1 [l2 Hl]].
    exists l1. split.
    + apply subpath_still_directed_2 with (v := v) (l2 := l2) (l3 := l). split. apply Hl. apply Hdir.
    + split.
      * apply subpath_still_acyclic_2 with (v := v) (l2 := l2) (l3 := l). split. apply Hl. apply Hcyc.
      * intros w Hw. apply HlZ. destruct Hw as [Hw | Hw].
        -- left. apply Hw.
        -- right. apply membership_splits_list in Hw. destruct Hw as [l3 [l4 Hw]]. apply membership_splits_list. exists l3. exists (l4 ++ [u] ++ l2).
           rewrite app_assoc. rewrite app_assoc. rewrite app_assoc in Hw. rewrite Hw. apply Hl.
Qed.

Lemma unblocked_ancestors_transitive: forall (u ancu' ancu'': node) (G: graph) (Z: nodes),
  In ancu' (find_unblocked_ancestors G u Z)
  -> In ancu'' (find_unblocked_ancestors G ancu' Z)
  -> In ancu'' (find_unblocked_ancestors G u Z).
Proof.
  intros u ancu' ancu'' G Z Hu Hancu'. apply unblocked_ancestors_have_unblocked_directed_path in Hancu'.
  destruct (ancu'' =? ancu') as [|] eqn:Heq.
  - apply eqb_eq in Heq. rewrite Heq. apply Hu.
  - destruct Hancu' as [Hancu' | Hancu']. rewrite Hancu' in Heq. rewrite eqb_refl in Heq. discriminate Heq.
    apply unblocked_ancestors_have_unblocked_directed_path in Hu.
    destruct (ancu'' =? u) as [|] eqn:Heq'. { left. apply eqb_eq in Heq'. symmetry. apply Heq'. }
    destruct Hu as [Hu | Hu].
    + rewrite <- Hu. apply unblocked_ancestors_have_unblocked_directed_path. right. apply Hancu'.
    + apply unblocked_ancestors_have_unblocked_directed_path. right.
      destruct Hu as [l1 Hu]. destruct Hancu' as [l2 Hancu'].
      assert (Hdir: is_directed_path_in_graph (ancu'', u, l2 ++ [ancu'] ++ l1) G = true).
      { apply concat_directed_paths. split. apply Hancu'. apply Hu. }
      apply directed_path_can_be_acyclic in Hdir. destruct Hdir as [l Hl]. rewrite <- and_assoc in Hl. destruct Hl as [Hl Hsub].
      exists l. rewrite <- and_assoc. split. apply Hl.
      intros w [Hw | Hw].
      * destruct Hancu' as [_ [_ Hancu']]. apply Hancu'. left. apply Hw.
      * assert (Hmem: In w (l2 ++ [ancu'] ++ l1)).
        { apply subset_larger_set_membership with (l1 := l). split. apply Hsub. apply Hw. }
        apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
        ** destruct Hancu' as [_ [_ Hancu']]. apply Hancu'. right. apply Hmem.
        ** destruct Hu as [_ [_ Hu]]. apply Hu. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. left. symmetry. apply Hmem. right. apply Hmem.
      * apply eqb_neq. apply Heq'.
Qed.


Lemma no_common_unblocked_ancestors_transitive: forall (u v ancu': node) (G: graph) (Z: nodes),
  overlap (find_unblocked_ancestors G u Z) (find_unblocked_ancestors G v Z) = false
  /\ In ancu' (find_unblocked_ancestors G u Z)
  -> overlap (find_unblocked_ancestors G ancu' Z) (find_unblocked_ancestors G v Z) = false.
Proof.
  intros u v ancu' G Z [Hover Hanc].
  apply unblocked_ancestors_have_unblocked_directed_path in Hanc. destruct Hanc as [Hanc | Hanc].
  { rewrite Hanc. apply Hover. }
  { destruct Hanc as [lu Hlu].
    destruct (overlap (find_unblocked_ancestors G ancu' Z) (find_unblocked_ancestors G v Z)) as [|] eqn:F.
    - apply overlap_has_member_in_common in F. destruct F as [x [Hxancu' Hxv]].
      apply no_overlap_non_member with (x := x) in Hover. apply unblocked_ancestors_transitive with (u := u) in Hxancu'.
      + exfalso. apply Hover. apply Hxancu'.
      + apply unblocked_ancestors_have_unblocked_directed_path. right. exists lu. apply Hlu.
      + apply Hxv.
    - reflexivity. }
Qed.



Definition G_anc: graph := ([1; 2; 3; 4; 5; 6], [(2, 1); (2, 3); (4, 1); (6, 4); (5, 6); (5, 3)]).

Example unblocked_ancestors_1: find_unblocked_ancestors G_anc 1 [2;4] = [1].
Proof. reflexivity. Qed.

Lemma single_edge_unblocked_ancestor: forall (u h: node) (G: graph) (Z: nodes),
  is_edge (u, h) G = true
  -> ~In u Z
  -> u <> h
  -> In u (find_unblocked_ancestors G h Z).
Proof.
  intros u h G Z. intros Huh HuZ Hcyc.
  apply unblocked_ancestors_have_unblocked_directed_path. right. exists []. split. simpl. rewrite Huh. reflexivity.
  split. simpl. split. apply Hcyc. easy.
  intros w [Hw | Hw].
  rewrite Hw. apply HuZ. exfalso. apply Hw.
Qed.

Lemma single_edge_unblocked_ancestor_path: forall (u h v: node) (t: nodes) (G: graph) (Z: nodes),
  is_edge (u, h) G = true
  -> ~In u Z
  -> acyclic_path_2 (u, v, h :: t)
  -> In u (find_unblocked_ancestors G h Z).
Proof.
  intros u h v t G Z. intros Huh HuZ Hcyc.
  apply single_edge_unblocked_ancestor. apply Huh. apply HuZ. intros H. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. left. symmetry. apply H.
Qed.
