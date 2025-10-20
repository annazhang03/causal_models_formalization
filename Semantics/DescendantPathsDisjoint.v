From Semantics Require Import ColliderDescendants.
From CausalDiagrams Require Import Assignments.
From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import DSeparation.
From CausalDiagrams Require Import CausalPaths.
From CausalDiagrams Require Import UnblockedAncestors.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.

Theorem exists_d_connected_path_with_collider_descendants_disjoint: forall (G: graph) (Z l: nodes) (u v: node),
  G_well_formed G = true /\ contains_cycle G = false
  -> acyclic_path_2 (u, v, l)
  -> d_connected_2 (u, v, l) G Z
  -> is_path_in_graph (u, v, l) G = true
  -> exists (l': nodes),
     acyclic_path_2 (u, v, l') /\ d_connected_2 (u, v, l') G Z /\ is_path_in_graph (u, v, l') G = true
     /\
     (forall (w: node), (node_in_path w (u, v, l') = true /\ node_in_path w (u, v, l) = false) \/
                        (exists (b: bool), path_out_of_node w (u, v, l) G = Some b /\ path_out_of_node w (u, v, l') G = Some (negb b))
      -> ((exists (du: node) (pu: nodes), is_directed_path_in_graph (w, du, pu) G = true /\ In du Z /\ ~In w Z)
          \/ path_out_of_node w (u, v, l') G <> Some true /\ In w Z)
           (* if path changed direction into u, then it's due to a descendant path *)
         /\ (path_out_of_node w (u, v, l') G = Some true -> ~(In w Z)))
     /\
     exists (D: assignments (nodes * node)), descendant_paths_disjoint D u v l' G Z.
Proof.
  intros G Z l u v HG. unfold descendant_paths_disjoint.

  generalize dependent u. induction l as [| h t IH].
  - intros u Hcyc Hconn Hpath.
    exists []. split. apply Hcyc. split. apply Hconn. split. apply Hpath. split.
    + intros w Hw. destruct Hw as [[Hw1 Hw2] | Hw].
      * rewrite Hw1 in Hw2. discriminate Hw2.
      * destruct Hw as [b [Hw1 Hw2]]. rewrite Hw1 in Hw2. inversion Hw2. destruct b as [|]. discriminate H0. discriminate H0.
    + exists []. split.
      * unfold is_exact_assignment_for. simpl. split. reflexivity. reflexivity.
      * intros c Hc. simpl in Hc. exfalso. apply Hc.
  - intros u Hcyc Hconn Hpath.
    specialize IH with (u := h).
    assert (Hcyc': acyclic_path_2 (h, v, t)). { apply acyclic_path_cat with (u := u). apply Hcyc. }
    apply IH in Hcyc'. clear IH.
    + destruct Hcyc' as [lhv Hlhv]. rewrite <- and_assoc in Hlhv. rewrite <- and_assoc in Hlhv. destruct Hlhv as [Hlhv [Hout [Dh HDh]]].
      assert (HLh: exists (Lh: nodes), get_collider_descendants_from_assignments Dh (find_colliders_in_path (h, v, lhv) G) = Some Lh).
      { apply collider_descendants_from_assignments_existence. intros c Hc. apply HDh in Hc. destruct Hc as [Hc | Hc].
        - left. apply Hc.
        - destruct Hc as [p [d Hc]]. right. exists p. exists d. apply Hc. }
      destruct HLh as [L HLh].

      assert (Hpath': is_path_in_graph (u, v, h :: lhv) G = true).
      { simpl. destruct G as [V E]. apply split_and_true. split.
        - simpl in Hpath. apply split_and_true in Hpath. apply Hpath.
        - apply Hlhv. }

      assert (Hl2: forall (l1 l2 l3: nodes) (a b: node), l1 ++ [a] ++ l2 = l3 ++ [b] ->
                        (rev l2 = [] -> a = b /\ l1 = l3) /\ (forall (hl2: node) (tl2: nodes), rev l2 = hl2 :: tl2 -> b = hl2 /\ l3 = l1 ++ [a] ++ rev tl2)).
      { intros l1' l2' l3 a b H. split.
        { intros Hlp2.
          assert (Hlem: rev (l1' ++ [a]) = rev (l3 ++ [b])).
          { rewrite <- H. rewrite reverse_list_append. rewrite reverse_list_append. rewrite reverse_list_append. unfold nodes in *. unfold node in *. rewrite Hlp2.
            simpl. reflexivity. }
          rewrite reverse_list_append in Hlem. rewrite reverse_list_append in Hlem. simpl in Hlem.
          inversion Hlem. split. reflexivity. rewrite reverse_list_twice with (l := l1'). rewrite H2. rewrite <- reverse_list_twice.
          reflexivity. }
        { intros hlp2' tlp2' Hlp2'. assert (Hlem: rev (l1' ++ [a] ++ l2') = rev (l3 ++ [b])).
          { rewrite <- H. reflexivity. }
          rewrite reverse_list_append in Hlem. rewrite reverse_list_append in Hlem. unfold nodes in *. unfold node in *. rewrite Hlp2' in Hlem. simpl in Hlem. rewrite reverse_list_append in Hlem.
          simpl in Hlem. inversion Hlem. split. reflexivity. rewrite reverse_list_twice with (l := l3).
          rewrite <- H2. repeat rewrite reverse_list_append. rewrite <- reverse_list_twice. simpl. reflexivity. } }

      assert (Hhu: (h =? u) = false).
      { destruct (h =? u) as [|] eqn:Hhu.
        - apply eqb_eq in Hhu. destruct Hcyc as [_ [Hcyc _]]. exfalso. apply Hcyc. left. apply Hhu.
        - reflexivity. }

      destruct (member u lhv) as [|] eqn:Hulhv.
      * (* CASE 1: if u intersects lhv, then use path along lhv starting from v *)
        apply member_In_equiv in Hulhv. apply membership_splits_list in Hulhv. destruct Hulhv as [lhv1 [lhv2 Hulhv]].
        exists lhv2. split.
        { apply subpath_still_acyclic with (w := h) (l1 := lhv1) (l3 := lhv). split. apply Hulhv. apply Hlhv. } split.
        { apply subpath_still_d_connected_gen with (w := h) (l1 := lhv1) (l3 := lhv). split. apply Hulhv. apply Hlhv. } split.
        { apply subpath_still_path with (w := h) (l1 := lhv1) (l3 := lhv). split. apply Hulhv. apply Hlhv. } split.

        { intros w Hw.
          assert (Houtw: path_out_of_node w (u, v, lhv2) G = path_out_of_node w (h, v, lhv) G).
          { assert (Houtw: exists (b: bool), path_out_of_node w (u, v, lhv2) G = Some b).
            { destruct Hw as [Hw | Hw].
              - apply path_out_of_node_mem_2. unfold node_in_path in Hw. simpl in Hw. destruct (w =? u) as [|] eqn:Hwu.
                + left. apply eqb_eq in Hwu. rewrite Hwu. reflexivity.
                + simpl in Hw. destruct (w =? v) as [|] eqn:Hwv.
                  * simpl in Hw. destruct Hw as [_ Hw]. discriminate Hw.
                  * simpl in Hw. right. apply member_In_equiv. apply Hw.
              - destruct Hw as [b Hw]. exists (negb b). apply Hw. }
            destruct Houtw as [b Houtw]. rewrite Houtw. symmetry. apply subpath_preserves_path_out_of_node with (u := u) (l1 := lhv1) (l2 := lhv2).
            split. apply Hulhv. apply Houtw. apply Hlhv. }

          unfold nodes in *. unfold node in *. rewrite Houtw. apply Hout.
          destruct Hw as [Hw | Hw].
           - (* all nodes in (u, v, lhv2) but not (u, v, h :: t) must also be in (h, v, lhv), so Hout applies *)
            unfold node_in_path in Hw. simpl in Hw. destruct (w =? u) as [|] eqn:Hwu. simpl in Hw. destruct Hw as [_ Hw]. discriminate Hw.
            simpl in Hw. destruct (w =? v) as [|] eqn:Hwv. simpl in Hw. destruct Hw as [_ Hw]. discriminate Hw. simpl in Hw.
            left. unfold node_in_path. simpl. split.
            + apply split_orb_true. right. apply member_In_equiv. rewrite <- Hulhv. apply membership_append_r. right. apply member_In_equiv. apply Hw.
            + rewrite Hwv. destruct (h =? w) as [|] eqn:Hhw. destruct Hw as [_ Hw]. discriminate Hw. rewrite eqb_sym in Hhw. rewrite Hhw.
              simpl. apply Hw.
          - destruct Hw as [b Hw]. destruct (w =? u) as [|] eqn:Hwu.
            + left. split.
              * unfold node_in_path. simpl. rewrite orb_comm. apply split_orb_true. left. apply member_In_equiv. rewrite <- Hulhv.
                apply membership_append_r. left. apply eqb_eq in Hwu. rewrite Hwu. reflexivity.
              * apply eqb_eq in Hwu. rewrite Hwu. apply acyclic_path_correct in Hcyc. simpl in Hcyc.
                unfold node_in_path. simpl. destruct (v =? u) as [|] eqn:Hvu. simpl in Hcyc. discriminate Hcyc. rewrite eqb_sym in Hvu. rewrite Hvu.
                rewrite eqb_sym in Hhu. rewrite Hhu. simpl.
                apply split_and_true in Hcyc. destruct Hcyc as [Hcyc _]. destruct (member u t) as [|] eqn:Hut. rewrite eqb_sym in Hhu. rewrite Hhu in Hcyc. discriminate Hcyc. reflexivity.
            + right. exists b. split.
              * rewrite <- path_out_of_node_cat with (u := u). apply Hw. apply Hwu.
              * rewrite <- Houtw. apply Hw. }

        assert (HD: exists (D: assignments (nodes * node)), get_collider_descendants_for_subpath Dh (find_colliders_in_path (u, v, lhv2) G) = Some D).
        { apply collider_descendants_for_subpath_existence_2 with (u := h) (l1 := lhv1) (L := L).
          unfold concat. simpl in Hulhv. unfold nodes in *. unfold node in *. rewrite Hulhv. apply HLh. }
        destruct HD as [D HD]. exists D. split. apply collider_subpath_is_exact_assignment with (D := Dh). apply HD.

        intros c Hc.
        assert (Hc': In c (find_colliders_in_path (h, v, lhv) G)).
        { apply subpath_preserves_colliders with (u := u) (l1 := lhv1) (l2 := lhv2). split. apply Hulhv. left. apply Hc. }
        apply HDh in Hc'. clear HDh. destruct Hc' as [Hc' | Hc'].
        -- left. split. apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (u, v, lhv2) G). apply HD. apply Hc'. apply Hc. apply Hc'.
        -- right. destruct Hc' as [p [d HDh]]. exists p. exists d. split.
           apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (u, v, lhv2) G). apply HD. apply HDh. apply Hc.

           rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc.
           split. repeat split; apply HDh. split.

           apply no_overlap_non_member. intros x Hx Hx'.
           destruct HDh as [_ [_ [_ [_ [_ [HDh _]]]]]]. apply no_overlap_non_member with (x := x) in HDh. apply HDh. apply Hx'.
           rewrite app_comm_cons in Hx. right. rewrite <- Hulhv. apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
           ++ apply membership_append. apply membership_append_r. apply Hx.
           ++ apply membership_append_r. apply Hx.
           ++ intros c' d' p' Hcdp. destruct HDh as [_ [_ [_ [_ [_ HDh]]]]]. apply HDh. split. apply Hcdp.
              apply collider_descendants_preserved_for_subpath with (D' := D) (col := find_colliders_in_path (u, v, lhv2) G). apply HD. apply Hcdp.

      * (* CASE 2: u does not intersect lhv. check if u intersects any descendant paths of Dh *)
        assert (Houtw_revdir: forall (w y c d: node) (lyc lyc2 p: nodes),
                    In w (y :: rev lyc)
                    -> lyc ++ [y] ++ lyc2 = p ++ [d]
                    -> In d Z /\ is_directed_path_in_graph (c, d, p) G = true /\ overlap (c :: p) Z = false
                    -> is_directed_path_in_graph (c, y, lyc) G = true
                    -> ((exists (du : node) (pu : nodes),
                          is_directed_path_in_graph (w, du, pu) G = true /\
                          In du Z /\ ~ In w Z) \/
                       path_out_of_node w (y, c, rev lyc) G <> Some true /\
                       In w Z) /\
                      (path_out_of_node w (y, c, rev lyc) G = Some true ->
                       ~ In w Z)).
        { intros w y c d lp1 lp2 p Hw' Hldp Hpdy' Hdir. split.
          - apply membership_splits_list in Hw'. destruct Hw' as [lw1 [lw2 Hw']].
             destruct (rev lp2) as [| hlp2 tlp2] eqn:Hlp2eq.
             * destruct lw1 as [| hlw1 tlw1].
               -- (* u = w = d *) right. split.
                  ++ inversion Hw'. unfold path_out_of_node. simpl. rewrite eqb_refl. pose proof Hdir as Hdir'.
                     apply directed_path_has_directed_edge_end in Hdir. destruct Hdir as [Hdir | Hdir].
                     ** rewrite Hdir in *. simpl. simpl in Hdir'. rewrite andb_comm in Hdir'. simpl in Hdir'. apply acyclic_no_two_cycle in Hdir'.
                        rewrite edge_in_graph_equiv in Hdir'. rewrite Hdir'. easy. apply HG. apply HG.
                     ** destruct Hdir as [lp1' [u' [Hdir1 Hdir2]]]. rewrite Hdir1 in *. rewrite reverse_list_append. simpl.
                        apply acyclic_no_two_cycle in Hdir2. rewrite edge_in_graph_equiv in Hdir2. rewrite Hdir2. easy. apply HG. apply HG.
                  ++ inversion Hw'. assert (Hud: y = d). { apply Hl2 in Hldp. apply Hldp in Hlp2eq. apply Hlp2eq. } rewrite Hud. apply Hpdy'.
               -- left. exists d. exists (rev tlw1). split.
                  ++ apply subpath_still_directed with (w := c) (l1 := rev lw2) (l3 := p). split.
                     ** assert (Hp: lp1 = p). { apply Hl2 in Hldp. apply Hldp in Hlp2eq. apply Hlp2eq. } inversion Hw'. rewrite <- Hp. rewrite reverse_list_twice with (l := lp1).
                        unfold nodes in *. unfold node in *. rewrite <- H1. rewrite reverse_list_append. simpl. rewrite <- app_assoc. reflexivity.
                     ** apply Hpdy'.
                  ++ split. apply Hpdy'. destruct Hpdy' as [_ [_ Hpd']]. intros HwZ. apply no_overlap_non_member with (x := w) in Hpd'.
                     apply Hpd'. right. inversion Hw'. assert (Hp: lp1 = p). { apply Hl2 in Hldp. apply Hldp in Hlp2eq as Hlp2. apply Hlp2. } rewrite <- Hp. rewrite reverse_list_twice with (l := lp1).
                     unfold nodes in *. unfold node in *. rewrite <- H1. rewrite reverse_list_append. apply membership_append. apply membership_rev. left. reflexivity.
                     apply HwZ.
             * assert (Hd: d = hlp2 /\ p = lp1 ++ [y] ++ rev tlp2). { apply Hl2 in Hldp. apply Hldp in Hlp2eq. apply Hlp2eq. }
               destruct lw1 as [| hlw1 tlw1].
               -- left. exists d. exists (rev tlp2). inversion Hw'. repeat split. apply subpath_still_directed with (w := c) (l1 := lp1) (l3 := p).
                  split. symmetry. apply Hd. apply Hpdy'. apply Hpdy'.
                  destruct Hpdy' as [_ [_ Hpd']]. intros HwZ. apply no_overlap_non_member with (x := y) in Hpd'.
                  apply Hpd'. right. destruct Hd as [_ Hd]. rewrite Hd. apply membership_append_r. left. reflexivity.
                  apply HwZ.
               -- left. exists d. exists (rev tlw1 ++ [y] ++ rev tlp2). inversion Hw'. repeat split.
                  ++ apply subpath_still_directed with (w := c) (l1 := rev lw2) (l3 := p). split.
                     destruct Hd as [_ Hd]. rewrite Hd. rewrite reverse_list_twice with (l := lp1). unfold nodes in *. unfold node in *. rewrite <- H1. rewrite reverse_list_append. simpl.
                     rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hpdy'.
                  ++ apply Hpdy'.
                  ++ destruct Hpdy' as [_ [_ Hpd']]. intros HwZ. apply no_overlap_non_member with (x := w) in Hpd'.
                     apply Hpd'. right. destruct Hd as [_ Hd]. rewrite Hd. apply membership_append. apply membership_rev. unfold nodes in *. unfold node in *. rewrite <- H1. apply membership_append_r. left. reflexivity.
                     apply HwZ.
           - intros F. exfalso. (* reverse directed path *)
             rewrite reverse_list_twice with (l := lp1) in Hdir. apply path_out_in_directed_path_rev with (x := w) in Hdir.
             * unfold nodes in *. unfold node in *. rewrite F in Hdir. discriminate Hdir.
             * apply HG.
             * apply Hw'. }

        destruct (member u L) as [|] eqn:HuL.
        ** (* CASE 2A *)
           apply member_In_equiv in HuL. apply membership_splits_list in HuL. destruct HuL as [l1 [l2 HuL]].

           assert (Hu: exists (c d: node) (p: nodes), In c (find_colliders_in_path (h, v, lhv) G)
                        /\ get_assigned_value Dh c = Some (p, d) /\ d =? c = false
                        /\ In u (p ++ [d])).
           { apply collider_descendants_from_assignments_belong_to_collider with (L := L). apply HLh. rewrite <- HuL. apply membership_append_r. left. reflexivity. }
           destruct Hu as [c [d [p [Hcolc [HDc [Hdc Hu]]]]]]. apply membership_splits_list in Hu. destruct Hu as [lp1 [lp2 Hlp]].

           assert (Hclhv: In c lhv).
           { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := c) in Hlhv. apply Hlhv. right. right. apply Hcolc. } 
           apply membership_splits_list in Hclhv. destruct Hclhv as [lc1 [lc2 Hlhvc]].

           pose proof Hcolc as Hcolc'. apply HDh in Hcolc. destruct Hcolc as [[F _] | Hcolc]. rewrite HDc in F. inversion F. rewrite H1 in Hdc. rewrite eqb_refl in Hdc. discriminate Hdc.
           destruct Hcolc as [p' [d' [Hpd'' Hpd']]]. rewrite HDc in Hpd''. inversion Hpd''. clear Hpd''. rewrite <- H0 in *. rewrite <- H1 in *. clear H0. clear H1.

           assert (Hlp2: rev lp2 = [] -> u = d /\ lp1 = p).
           { apply Hl2. apply Hlp. }
           assert (Hlp2': forall (hlp2: node) (tlp2: nodes), rev lp2 = hlp2 :: tlp2 -> d = hlp2 /\ p = lp1 ++ [u] ++ (rev tlp2)).
           { apply Hl2. apply Hlp. }

           assert (Hcyc': acyclic_path_2 (u, v, rev lp1 ++ [c] ++ lc2)).
           { apply concat_paths_acyclic.
             - split.
               --- destruct Hpd' as [_ [_ [_ [_ [Hpd' _]]]]]. intros Hyv. apply no_overlap_non_member with (x := u) in Hpd'.
                   + apply Hpd'. rewrite <- Hlp. apply membership_append_r. left. reflexivity.
                   + rewrite Hyv. right. apply membership_append_r. left. reflexivity.
               --- split.
                   + destruct (rev lp2) as [| hlp2 tlp2].
                     * assert (Hyd: u = d /\ lp1 = p). { apply Hlp2. reflexivity. } destruct Hyd as [Hyd Hlp1]. rewrite Hyd.
                       apply reverse_path_still_acyclic. rewrite Hlp1. apply Hpd'.
                     * assert (Hd: d = hlp2 /\ p = lp1 ++ [u] ++ (rev tlp2)). { apply Hlp2'. reflexivity. }
                       apply reverse_path_still_acyclic. apply subpath_still_acyclic_2 with (v := d) (l2 := rev tlp2) (l3 := p). split. symmetry. apply Hd.
                       apply Hpd'.
                   + apply subpath_still_acyclic with (w := h) (l1 := lc1) (l3 := lhv). split. apply Hlhvc. apply Hlhv.
             - apply demorgan. intros Hmem. (* y cannot overlap with lhv path, v cannot overlap desc path (both Hpd') *)
               destruct Hpd' as [_ [_ [_ [_ [Hpd' _]]]]]. destruct Hmem as [Hmem | Hmem].
               + apply no_overlap_non_member with (x := u) in Hpd'.
                 * apply Hpd'. rewrite <- Hlp. apply membership_append_r. left. reflexivity.
                 * rewrite <- Hlhvc. right. apply membership_append. apply membership_append_r. apply membership_append_r. apply Hmem.
               + apply no_overlap_non_member with (x := v) in Hpd'.
                 * apply Hpd'. rewrite <- Hlp. apply membership_append. apply membership_rev. apply Hmem.
                 * right. apply membership_append_r. left. reflexivity.
             - apply no_overlap_non_member. intros x' Hmem Hmem2. destruct Hpd' as [_ [_ [_ [_ [Hpd' _]]]]].
               apply no_overlap_non_member with (x := x') in Hpd'.
               + apply Hpd'. rewrite <- Hlp. apply membership_append. apply membership_rev. apply Hmem2.
               + right. apply membership_append. rewrite <- Hlhvc. apply membership_append_r. apply membership_append_r. apply Hmem. }

           assert (Hpath'': is_path_in_graph (u, v, rev lp1 ++ [c] ++ lc2) G = true).
           { apply concat_paths_still_a_path. split.
             - destruct (rev lp2) as [| hlp2 tlp2].
               + (* Hlp -> u = d, use HD to show that in fact, path is directed *)
                 assert (Hyd: u = d /\ lp1 = p). { apply Hlp2. reflexivity. }
                 apply reverse_path_in_graph. destruct Hyd as [Hyd Hlp1]. rewrite Hyd. rewrite Hlp1.
                 apply directed_path_is_path. apply Hpd'.
               + (* Hlp -> d = hlp2, so use subpath with l2 := tlp2, then use HD *)
                 assert (Hd: d = hlp2 /\ p = lp1 ++ [u] ++ (rev tlp2)). { apply Hlp2'. reflexivity. }
                 apply reverse_path_in_graph. apply subpath_still_path_2 with (v := d) (l2 := rev tlp2) (l3 := p). split. symmetry. apply Hd.
                 apply directed_path_is_path. apply Hpd'.

             - apply subpath_still_path with (w := h) (l1 := lc1) (l3 := lhv). split.
               + apply Hlhvc.
               + apply Hlhv. }


           exists (rev lp1 ++ [c] ++ lc2).

           assert (Hpath''': is_path_in_graph (c, v, lc2) G = true). { apply subpath_still_path with (w := h) (l1 := lc1) (l3 := lhv). split. apply Hlhvc. apply Hlhv. }
           assert (Hdir: is_directed_path_in_graph (c, u, lp1) G = true).
           { destruct (rev lp2) as [| hlp2 tlp2].
             + assert (Hyd: u = d /\ lp1 = p). { apply Hlp2. reflexivity. } destruct Hyd as [Hyd Hlp1]. rewrite Hyd. rewrite Hlp1.
               apply Hpd'.
             + assert (Hyd: d = hlp2 /\ p = lp1 ++ [u] ++ rev tlp2). { apply Hlp2'. reflexivity. }
               apply subpath_still_directed_2 with (v := d) (l2 := rev tlp2) (l3 := p). split. symmetry. apply Hyd. apply Hpd'. }

           assert (Hc: In c (find_mediators_in_path (concat u c v (rev lp1) lc2) G)).
           { destruct lc2 as [| hlc2 tlc2].
             + simpl in Hpath'''. destruct G as [V E]. rewrite andb_comm in Hpath'''. simpl in Hpath'''. apply split_orb_true in Hpath'''. destruct Hpath''' as [Hcv | Hvc].
               * (* Hcolc' -> (v, c) is an edge, makes cycle with Hcv *)
                 apply colliders_vs_edges_in_path in Hcolc'. destruct Hcolc' as [y [z [Hsub Hcolc']]]. apply end_of_sublist_still_sublist in Hsub.
                 assert (Hz: z = v).
                 { apply two_sublists_the_same with (l := lhv ++ [v]) (a := c). apply Hsub.
                   apply sublist_breaks_down_list. exists lc1. exists []. simpl. rewrite <- Hlhvc. simpl. rewrite <- app_assoc. reflexivity.
                   destruct Hlhv as [[Hlhv _] _]. apply acyclic_path_count with (x := c) in Hlhv. simpl in Hlhv. destruct (h =? c) as [|] eqn:Hhc.
                   - inversion Hlhv. rewrite <- Hlhvc in H0. rewrite count_app in H0. rewrite count_app in H0. simpl in H0. rewrite eqb_refl in H0. lia.
                   - apply Hlhv.
                   - right. rewrite <- Hlhvc. apply membership_append. apply membership_append_r. left. reflexivity. }
                 rewrite Hz in Hcolc'. destruct Hcolc' as [_ Hcolc'].
                 destruct HG as [_ HG]. apply contains_cycle_false_correct with (p := (v, v, [c])) in HG. exfalso. destruct HG as [HG _]. apply HG. reflexivity.
                 simpl. simpl in Hcv. rewrite Hcv. simpl in Hcolc'. rewrite Hcolc'. reflexivity.
               * destruct lp1 as [| hlp1 tlp1].
                 ++ apply mediators_vs_edges_in_path. exists u. exists v. split. simpl. repeat rewrite eqb_refl. reflexivity. right.
                    split. simpl in Hdir. apply split_and_true in Hdir. apply Hdir. apply Hvc.
                 ++ apply mediators_vs_edges_in_path. exists hlp1. exists v. split.
                    ** apply sublist_breaks_down_list. exists (u :: rev tlp1). exists []. simpl. repeat rewrite <- app_assoc. simpl. reflexivity.
                    ** right. split. simpl in Hdir. apply split_and_true in Hdir. apply Hdir. apply Hvc.

             + simpl in Hpath'''. destruct G as [V E]. apply split_and_true in Hpath'''. destruct Hpath''' as [Hpath''' _]. apply split_orb_true in Hpath'''. destruct Hpath''' as [Hcv | Hvc].
               * (* Hcolc' -> (hlc2, c) is an edge, makes cycle with Hcv *)
                 apply colliders_vs_edges_in_path in Hcolc'. destruct Hcolc' as [y [z [Hsub Hcolc']]]. apply end_of_sublist_still_sublist in Hsub.
                 assert (Hz: z = hlc2).
                 { apply two_sublists_the_same with (l := lhv ++ [v]) (a := c). apply Hsub.
                   apply sublist_breaks_down_list. exists lc1. exists (tlc2 ++ [v]). simpl. rewrite <- Hlhvc. simpl. rewrite <- app_assoc. reflexivity.
                   destruct Hlhv as [[Hlhv _] _]. apply acyclic_path_count with (x := c) in Hlhv. simpl in Hlhv. destruct (h =? c) as [|] eqn:Hhc.
                   - inversion Hlhv. rewrite <- Hlhvc in H0. rewrite count_app in H0. rewrite count_app in H0. simpl in H0. rewrite eqb_refl in H0. lia.
                   - apply Hlhv.
                   - right. rewrite <- Hlhvc. apply membership_append. apply membership_append_r. left. reflexivity. }
                 rewrite Hz in Hcolc'. destruct Hcolc' as [_ Hcolc'].
                 destruct HG as [_ HG]. apply contains_cycle_false_correct with (p := (hlc2, hlc2, [c])) in HG. exfalso. destruct HG as [HG _]. apply HG. reflexivity.
                 simpl. simpl in Hcv. rewrite Hcv. simpl in Hcolc'. rewrite Hcolc'. reflexivity.
               * destruct lp1 as [| hlp1 tlp1].
                 ++ apply mediators_vs_edges_in_path. exists u. exists hlc2. split. simpl. repeat rewrite eqb_refl. reflexivity. right.
                    split. simpl in Hdir. apply split_and_true in Hdir. apply Hdir. apply Hvc.
                 ++ apply mediators_vs_edges_in_path. exists hlp1. exists hlc2. split.
                    ** apply sublist_breaks_down_list. exists (u :: rev tlp1). exists (tlc2 ++ [v]). simpl. repeat rewrite <- app_assoc. simpl. reflexivity.
                    ** right. split. simpl in Hdir. apply split_and_true in Hdir. apply Hdir. apply Hvc. }

           assert (Hccol: ~ In c (find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G)).
           { apply if_mediator_then_not_confounder_path in Hc. 2: { apply HG. } 2: { apply Hcyc'. } apply Hc. }

           assert (Hx': forall (x': node),
                          In x' (find_mediators_in_path (u, c, rev lp1) G) \/
                          In x' (find_confounders_in_path (u, c, rev lp1) G) \/
                          In x' (find_colliders_in_path (u, c, rev lp1) G) -> In x' (rev lp1)).
           { intros x'. assert (Hpath'''': is_path_in_graph (u, c, rev lp1) G = true).
             { apply subpath_still_path_2 with (v := v) (l2 := lc2) (l3 := rev lp1 ++ [c] ++ lc2). split. reflexivity. apply Hpath''. }
             apply intermediate_node_in_path with (x := x') in Hpath''''. apply Hpath''''. }

           assert (Hx'': forall (x': node), In x' (rev lp1) -> In x' (find_mediators_in_path (u, c, rev lp1) G)).
           { intros x' Hmem. apply mediators_same_in_reverse_path. apply directed_path_all_mediators. split.
             - apply Hdir.
             - apply membership_rev. apply Hmem. }

           split. apply Hcyc'. split.
           { apply concat_d_connected_paths. apply HG. apply Hpath''.
             - rewrite <- and_assoc. rewrite and_comm. split. apply Hcyc'. split.
               + (* directed path, so all mediators. none are in Z (except possible y if y = d) *)
                 unfold d_connected_2. 
                 repeat split.
                 * (* mediators in lp1, so in p, so not in Z by Hpd' *)
                   apply no_overlap_non_member. intros x' Hmem Hmem2.
                   assert (Hmem3: In x' (rev lp1)). { apply Hx'. left. apply Hmem. }
                   apply membership_rev in Hmem3. rewrite <- reverse_list_twice in Hmem3.
                   assert (Hmem4: In x' p).
                   { destruct (rev lp2) as [| hlp2 tlp2].
                     - assert (Hlem: lp1 = p). { apply Hlp2. reflexivity. } rewrite <- Hlem. apply Hmem3.
                     - assert (Hlem: p = lp1 ++ [u] ++ rev tlp2). { apply Hlp2' with (hlp2 := hlp2). reflexivity. }
                       rewrite Hlem. apply membership_append. apply Hmem3. }
                   destruct Hpd' as [_ [_ [_ [Hpd' _]]]]. apply no_overlap_non_member with (x := x') in Hpd'.
                   -- apply Hpd'. right. apply Hmem4.
                   -- apply Hmem2.
                * (* no confounders, since directed path *)
                  apply no_overlap_non_member. intros x' Hmem _.
                  assert (Hcon: In x' (find_mediators_in_path (u, c, rev lp1) G)).
                  { apply Hx''. apply Hx'. right. left. apply Hmem. }
                  apply if_mediator_then_not_confounder_path in Hcon. destruct Hcon as [Hcon _]. apply Hcon. apply Hmem. apply HG.
                  apply subpath_still_acyclic_2 with (v := v) (l2 := lc2) (l3 := rev lp1 ++ [c] ++ lc2). split. reflexivity. apply Hcyc'.
                * unfold all_colliders_have_descendant_conditioned_on. apply forallb_true_iff_mem. intros x' Hmem.
                  assert (Hcon: In x' (find_mediators_in_path (u, c, rev lp1) G)).
                  { apply Hx''. apply Hx'. right. right. apply Hmem. }
                  apply if_mediator_then_not_confounder_path in Hcon. destruct Hcon as [_ Hcon]. exfalso. apply Hcon. apply Hmem. apply HG.
                  apply subpath_still_acyclic_2 with (v := v) (l2 := lc2) (l3 := rev lp1 ++ [c] ++ lc2). split. reflexivity. apply Hcyc'.
               + apply subpath_still_d_connected_gen with (w := h) (l1 := lc1) (l3 := lhv). split. apply Hlhvc. apply Hlhv.
             - (* since c starts descendant path, cannot be collider. not in Z by Hpd'. *)
               (* need to determine first edge c <-> ...lc2 *)
               assert (HcZ: ~ In c Z). { destruct Hpd' as [_ [_ [_ [Hpd' _]]]]. intros Hmem. apply no_overlap_non_member with (x := c) in Hpd'. exfalso. apply Hpd'. left. reflexivity. apply Hmem. }

               left. split. apply Hc. apply HcZ. } split. apply Hpath''. split.

           { intros w Hw.

             assert (Hwv: w =? v = false).
             { destruct (w =? v) as [|] eqn:Hwv. destruct Hw as [Hw | Hw].
               - destruct Hw as [_ Hw]. unfold node_in_path in Hw. simpl in Hw. rewrite Hwv in Hw. rewrite <- orb_assoc in Hw. rewrite orb_comm in Hw. simpl in Hw. discriminate Hw.
               - destruct Hw as [b [Hb _]]. assert (Hv: In v (u :: (h :: t))). { apply path_out_of_node_mem_gen with (l := h :: t) (x := v) (u := u) (v := v) (G := G). exists b. apply eqb_eq in Hwv. rewrite <- Hwv in *. apply Hb. }
                 exfalso. destruct Hv as [Hv | Hv]. destruct Hcyc as [Hcyc _]. apply Hcyc. apply Hv. destruct Hcyc as [_ [_ [Hcyc _]]]. apply Hcyc. apply Hv.
               - reflexivity. }

             assert (Hwnode: In w (u :: (rev lp1 ++ [c] ++ lc2))).
             { pose proof Hw as Hw'. destruct Hw as [Hw | Hw].
               - destruct Hw as [Hw _]. rewrite node_in_path_equiv in Hw. apply member_In_equiv in Hw. rewrite app_comm_cons in Hw. apply membership_append_or in Hw.
                 destruct Hw as [Hw | Hw]. apply Hw. destruct Hw as [Hw | Hw]. rewrite Hw in Hwv. rewrite eqb_refl in Hwv. discriminate Hwv. exfalso. apply Hw.
               - destruct Hw as [b [_ Hw]]. apply path_out_of_node_mem_gen with (v := v) (G := G). exists (negb b). apply Hw. }

             (* w is in (u, c, rev lp1): exists d, p. path_out_of_node = false *)
             assert (Hw': In w (u :: rev lp1) \/ In w (c :: lc2)).
             { rewrite app_comm_cons in Hwnode. apply membership_append_or in Hwnode. apply Hwnode. }
             destruct Hw' as [Hw' | Hw'].
             - assert (Houtw: path_out_of_node w (u, v, rev lp1 ++ [c] ++ lc2) G = path_out_of_node w (u, c, rev lp1) G).
               { assert (Hwlp1: exists (b: bool), path_out_of_node w (u, c, rev lp1) G = Some b). { apply path_out_of_node_mem_2. apply Hw'. }
                 destruct Hwlp1 as [b Hb]. rewrite Hb. apply subpath_preserves_path_out_of_node_2 with (u := c) (l1 := rev lp1) (l2 := lc2). split. reflexivity. apply Hb. }
               unfold nodes in *. unfold node in *. rewrite Houtw. apply Houtw_revdir with (d := d) (lyc2 := lp2) (p := p). apply Hw'. apply Hlp. repeat split; apply Hpd'. apply Hdir.
             - assert (Hwlhv: path_out_of_node w (u, v, rev lp1 ++ [c] ++ lc2) G = path_out_of_node w (h, v, lhv) G).
               { assert (exists (b: bool), path_out_of_node w (h, v, lhv) G = Some b).
                 { apply path_out_of_node_mem_gen. right. rewrite <- Hlhvc. apply membership_append_r. apply Hw'. }
                 destruct H as [b Hb]. rewrite Hb.
                 apply subpath_preserves_path_out_of_node with (u := c) (l1 := rev lp1) (l2 := lc2). split. reflexivity.
                 - apply superpath_preserves_path_out_of_node with (w := h) (l1 := lc1) (l3 := lhv). apply Hlhvc. apply Hb. apply Hlhv. apply Hw'.
                 - apply Hcyc'. }
               assert (Hwu: w =? u = false).
               { destruct (w =? u) as [|] eqn:Hwu.
                 - exfalso. destruct Hcyc' as [_ [Hcyc' _]]. apply Hcyc'. apply membership_append_r. apply eqb_eq in Hwu. rewrite Hwu in Hw'. apply Hw'.
                 - reflexivity. }
               unfold nodes in *. unfold node in *. rewrite Hwlhv. apply Hout.
               destruct Hw as [Hw | Hw].
               + left. split.
                 * rewrite node_in_path_equiv. apply member_In_equiv. right. apply membership_append. rewrite <- Hlhvc. apply membership_append_r. apply Hw'.
                 * rewrite node_in_path_equiv. destruct Hw as [_ Hw]. rewrite node_in_path_equiv in Hw. simpl in Hw. rewrite eqb_sym in Hwu. rewrite Hwu in Hw.
                   apply Hw.
               + right. destruct Hw as [b [Hb1 Hb2]]. exists b. split.
                 * rewrite <- path_out_of_node_cat with (u := u). apply Hb1. apply Hwu.
                 * rewrite <- Hwlhv. apply Hb2. }

           assert (Hcol: find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G = find_colliders_in_path (c, v, lc2) G).
           { assert (Hcolyv: find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G = (find_colliders_in_path (u, c, rev lp1) G) ++ [c] ++ (find_colliders_in_path (c, v, lc2) G)
                           \/ find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G = (find_colliders_in_path (u, c, rev lp1) G) ++ (find_colliders_in_path (c, v, lc2) G)).
             { apply subpath_preserves_colliders_2. reflexivity. }
             assert (Hcolyv': find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G = (find_colliders_in_path (u, c, rev lp1) G) ++ (find_colliders_in_path (c, v, lc2) G)).
             { (* by Hc, c cannot be a collider *) destruct Hcolyv as [Hcolyv | Hcolyv].
               - exfalso. apply Hccol. rewrite Hcolyv. apply membership_append_r. left. reflexivity.
               - apply Hcolyv. } clear Hcolyv.
             destruct (find_colliders_in_path (u, c, rev lp1) G) as [| huc tuc] eqn:Hcoluc.
             - rewrite Hcolyv'. reflexivity.
             - assert (Hhuc: In huc (find_mediators_in_path (u, c, rev lp1) G)).
               { apply Hx''. apply Hx'. right. right. left. reflexivity. }
               apply if_mediator_then_not_confounder_path in Hhuc. exfalso. apply Hhuc. rewrite Hcoluc. left. reflexivity. apply HG.
               apply subpath_still_acyclic_2 with (v := v) (l2 := lc2) (l3 := rev lp1 ++ [c] ++ lc2). split. reflexivity. apply Hcyc'. }

           assert (HD: exists (D: assignments (nodes * node)), get_collider_descendants_for_subpath Dh (find_colliders_in_path (c, v, lc2) G) = Some D).
           { apply collider_descendants_for_subpath_existence_2 with (u := h) (l1 := lc1) (L := L).
             unfold concat. simpl in Hlhvc. unfold nodes in *. unfold node in *. rewrite Hlhvc. apply HLh. }
           destruct HD as [D HD]. exists D. split.
           { apply collider_subpath_is_exact_assignment with (D := Dh).
             unfold nodes in *. unfold node in *. rewrite Hcol. apply HD. }

           (* use the same paths for remaining colliders, since from HD, they do not overlap y desc path *)
           intros c' Hc'.
           assert (Hcol': In c' (find_colliders_in_path (h, v, lhv) G)).
           { apply subpath_preserves_colliders with (u := c) (l1 := lc1) (l2 := lc2). split. apply Hlhvc. left.
             unfold nodes in *. unfold node in *. rewrite Hcol in Hc'. apply Hc'. }
           apply HDh in Hcol'. destruct Hcol' as [Hcol' | Hcol'].
           -- left. split. apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G). rewrite Hcol. apply HD. apply Hcol'. apply Hc'. apply Hcol'.
           -- right. destruct Hcol' as [pc [dc HDh']]. exists pc. exists dc. split.
              apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G). rewrite Hcol. apply HD. apply HDh'. apply Hc'.
 
              rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc.
              split. repeat split; apply HDh'. split.
 
              apply no_overlap_non_member. intros x Hx1 Hx2.
              ++ assert (Hx1': In x ((u :: rev lp1) ++ (c :: lc2 ++ [v]))).
                 { rewrite app_comm_cons. rewrite app_assoc. rewrite <- app_comm_cons. apply Hx1. }
                 clear Hx1. apply membership_append_or in Hx1'. destruct Hx1' as [Hx1 | Hx1].
                 --- destruct HDh' as [_ [_ [_ [_ [_ [_ HDh']]]]]]. specialize HDh' with (c' := c) (d' := d) (p' := p).
                     assert (Hover: overlap (c' :: pc ++ [dc]) (c :: p ++ [d]) = false).
                     { apply HDh'. rewrite and_comm. split. apply HDc. destruct (c' =? c) as [|] eqn:Hcc'.
                       - apply eqb_eq in Hcc'. exfalso. apply Hccol. rewrite <- Hcc' in *. apply Hc'.
                       - reflexivity. }
                     apply no_overlap_non_member with (x := x) in Hover. apply Hover. right. apply Hx2. right. rewrite <- Hlp.
                     destruct Hx1 as [Hx1 | Hx1]. apply membership_append_r. left. apply Hx1. apply membership_append. apply membership_rev. apply Hx1.
                 --- destruct HDh' as [_ [_ [_ [_ [_ [HDh' _]]]]]]. apply no_overlap_non_member with (x := x) in HDh'. apply HDh'. apply Hx2.
                     right. rewrite <- Hlhvc. rewrite <- app_assoc. apply membership_append_r. apply Hx1.
              ++ intros c'' d'' p'' Hcdp. destruct HDh' as [_ [_ [_ [_ [_ HDh']]]]]. apply HDh'. split. apply Hcdp.
                 apply collider_descendants_preserved_for_subpath with (D' := D) (col := find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G). rewrite Hcol. apply HD. apply Hcdp.

        ** (* u does not intersect any part of (h, v, lhv). see if h is a mediator, confounder, or collider *)
           assert (Hh: In h (find_mediators_in_path (u, v, h :: lhv) G) \/
                       In h (find_confounders_in_path (u, v, h :: lhv) G) \/
                       In h (find_colliders_in_path (u, v, h :: lhv) G)).
           { assert (Hh: In h (h :: lhv)). { left. reflexivity. }
             apply intermediate_node_in_path with (x := h) in Hpath'. apply Hpath' in Hh. apply Hh. }

           assert (Hu_h_lhv_cyc: acyclic_path_2 (u, v, h :: lhv)).
           { apply acyclic_path_correct_2. simpl. rewrite Hhu. apply split_and_true. split. apply negb_true_iff. apply member_In_equiv_F. intros Humem.
             apply membership_append_or in Humem. destruct Humem as [Humem | [Humem | Humem]]. apply member_In_equiv_F in Hulhv. apply Hulhv. apply Humem.
             destruct Hcyc as [Hcyc _]. apply Hcyc. symmetry. apply Humem. apply Humem.
             destruct Hlhv as [[Hlhv _] _]. apply acyclic_path_correct_2 in Hlhv. simpl in Hlhv. apply Hlhv. }


           rewrite <- or_assoc in Hh. destruct Hh as [Hh | Hh].
           --- (* CASE 2B: h is not a collider *)
               assert (HFcol: find_colliders_in_path (u, v, h :: lhv) G = find_colliders_in_path (h, v, lhv) G).
               { assert (HFcol: ~In h (find_colliders_in_path (u, v, h :: lhv) G)).
                 { destruct Hh as [Hh | Hh].
                   - apply if_mediator_then_not_confounder_path in Hh. apply Hh. apply HG. apply Hu_h_lhv_cyc.
                   - apply if_confounder_then_not_mediator_path in Hh. apply Hh. apply HG. apply Hu_h_lhv_cyc. }

                 simpl. destruct lhv as [| h' t'].
                 - simpl. destruct (is_collider_bool u v h G) as [|] eqn:Hcol.
                   + assert (Hcol': In h (find_colliders_in_path (u, v, [h]) G)). { simpl. rewrite Hcol. left. reflexivity. }
                     exfalso. apply HFcol. apply Hcol'.
                   + reflexivity.
                  - simpl. destruct (is_collider_bool u h' h G) as [|] eqn:Hcol.
                    + assert (Hcol': In h (find_colliders_in_path (u, v, h :: h' :: t') G)). { simpl. rewrite Hcol. left. reflexivity. }
                      exfalso. apply HFcol. apply Hcol'.
                    + reflexivity. }

               exists (h :: lhv). split. repeat split.
               { apply Hcyc. }
               { intros Hmem. destruct Hmem as [Hmem | Hmem].
                 - unfold acyclic_path_2 in Hcyc. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. left. apply Hmem.
                 - apply member_In_equiv_F in Hulhv. apply Hulhv. apply Hmem. }
               { unfold acyclic_path_2 in Hlhv. intros Hmem. destruct Hmem as [Hmem | Hmem].
                 - destruct Hlhv as [[[Hlhv _] _] _]. apply Hlhv. apply Hmem.
                 - destruct Hlhv as [[[_ [_ [Hlhv _]]] _] _]. apply Hlhv. apply Hmem. }
               { destruct Hlhv as [[Hlhv _] _]. apply acyclic_path_correct_2 in Hlhv. apply acyclic_path_reverse in Hlhv.
                 simpl in Hlhv. rewrite reverse_list_append in Hlhv. simpl in Hlhv. apply split_and_true in Hlhv. destruct Hlhv as [_ Hlhv].
                 apply acyclic_path_reverse in Hlhv. rewrite reverse_list_append in Hlhv. rewrite <- reverse_list_twice in Hlhv. apply Hlhv. } split.

               pose proof Hh as Hh'. clear Hh.
               assert (Hsub: forall (y z: node), sublist [y; h; z] (u :: (h :: lhv) ++ [v]) = true
                             -> (lhv = [] -> y = u /\ z = v) /\
                                (forall (hlhv: node) (tlhv: nodes), lhv = hlhv :: tlhv -> y = u /\ z = hlhv)).
               { intros y z Hh. split.
                 * intros Hht. rewrite Hht in Hh. simpl in Hh. repeat rewrite eqb_refl in Hh. simpl in Hh. rewrite andb_assoc in Hh. apply split_orb_true in Hh. rewrite andb_comm in Hh. simpl in Hh.
                   destruct Hh as [Hh | Hh]. apply split_and_true in Hh. repeat rewrite eqb_eq in Hh. apply Hh.
                   rewrite andb_assoc in Hh. rewrite andb_comm in Hh. simpl in Hh. rewrite andb_comm in Hh. simpl in Hh. discriminate Hh.
                 * intros hlhv tlhv Hht. rewrite Hht in Hh. unfold sublist in Hh. apply split_orb_true in Hh. destruct Hh as [Hh | Hh].
                   - simpl in Hh. repeat rewrite eqb_refl in Hh. simpl in Hh. rewrite andb_assoc in Hh. apply split_and_true in Hh. destruct Hh as [Hh _]. apply split_and_true in Hh. repeat rewrite eqb_eq in Hh. apply Hh.
                   - assert (Hu: In h ((hlhv :: tlhv) ++ [v])). { apply middle_elt_of_sublist_not_first_elt with (a := y) (c := z). apply Hh. }
                     destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv.
                     apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]].
                     + destruct Hlhv as [_ [Hlhv _]]. exfalso. apply Hlhv. rewrite Hht. apply Hu.
                     + destruct Hlhv as [Hlhv _]. exfalso. apply Hlhv. symmetry. apply Hu.
                     + exfalso. apply Hu. }

               pose proof Hh' as Hh. clear Hh'. repeat split.
               { destruct Hh as [Hh | Hh].
                 - (* if h is a mediator in the new path, then u->h->...lhv or u<-h<-...lhv
                      if arrow didn't change, then mediator in original path, so not in Z
                      if arrow changed, then in original path either u->h<- and not in Z, or u<-h-> (not in Z since d-conn) *)
                   apply mediators_vs_edges_in_path in Hh. destruct Hh as [y [z [Hh Hyz]]].
                   apply Hsub in Hh as Hsub'. destruct Hsub' as [Hlhv0 Hhlhv].

                   assert (Hyu: y = u). { destruct lhv as [| hlhv tlhv] eqn:Hl. apply Hlhv0. reflexivity. apply Hhlhv with (hlhv := hlhv) (tlhv := tlhv). reflexivity. }
                   rewrite Hyu in *. clear Hyu.

                   assert (HhZ: ~In h Z).
                   { destruct Hyz as [Hyz | Hyz].
                     + (* u->h->z *)
                       assert (Houth: path_out_of_node h (h, v, lhv) G = Some true).
                       { unfold path_out_of_node. simpl. rewrite eqb_refl. destruct lhv as [| hlhv tlhv].
                         - simpl. assert (Hz: z = v). { apply Hlhv0. reflexivity. }
                           rewrite Hz in Hyz. destruct Hyz as [_ Hyz]. unfold is_edge in Hyz.
                           destruct G as [V E]. apply split_and_true in Hyz. destruct Hyz as [_ Hyz]. simpl. rewrite Hyz. reflexivity.
                         - simpl. assert (Hz: z = hlhv). { apply Hhlhv with (tlhv := tlhv). reflexivity. }
                           rewrite Hz in *. destruct Hyz as [_ Hyz]. destruct G as [V E]. apply split_and_true in Hyz. destruct Hyz as [_ Hyz]. simpl. rewrite Hyz. reflexivity. }

                       destruct (path_out_of_node h (u, v, h :: t) G) as [[|]|] eqn:Houth'.
                       - assert (Hmed: In h (find_mediators_in_path (u, v, h :: t) G)).
                         { simpl. unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'.
                           destruct t as [| h' t'].
                           - simpl. simpl in Houth'. rewrite eqb_refl in Houth'. unfold is_mediator_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                             destruct (edge_in_graph (h, v) G) as [|] eqn:Hhv. apply edge_in_graph_then_is_edge in Hhv. rewrite Hhv. simpl. left. reflexivity. apply HG. discriminate Houth'.
                           - simpl. rewrite eqb_refl in Houth'. simpl in Houth'. unfold is_mediator_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                             destruct (edge_in_graph (h, h') G) as [|] eqn:Hhh'. apply edge_in_graph_then_is_edge in Hhh'. rewrite Hhh'. simpl. left. reflexivity. apply HG. discriminate Houth'. }

                         unfold d_connected_2 in Hconn. destruct Hconn as [Hconn _]. apply no_overlap_non_member with (x := h) in Hconn.
                         apply Hconn. apply Hmed.
                       - assert (Hlem: path_out_of_node h (h, v, lhv) G = Some true -> ~ In h Z).
                         { apply Hout. right. exists false. split.
                           - rewrite <- path_out_of_node_cat with (u := u). apply Houth'. apply Hhu.
                           - simpl. apply Houth. }
                         apply Hlem. apply Houth.
                       - unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'. rewrite eqb_refl in Houth'.
                         destruct t as [| h' t']. simpl in Houth'. destruct (edge_in_graph (h, v) G) as [|]. discriminate Houth'. discriminate Houth'.
                         simpl in Houth'. destruct (edge_in_graph (h, h') G) as [|]. discriminate Houth'. discriminate Houth'.

                     + (* u<-h<-z *)
                       assert (Houth: path_out_of_node h (h, v, lhv) G = Some false).
                       { unfold path_out_of_node. simpl. rewrite eqb_refl. destruct lhv as [| hlhv tlhv].
                         - simpl. assert (Hz: z = v). { apply Hlhv0. reflexivity. }
                           rewrite Hz in Hyz. destruct Hyz as [_ Hyz]. apply acyclic_no_two_cycle in Hyz as Hyz'. unfold is_edge in Hyz.
                           destruct G as [V E]. apply split_and_true in Hyz. unfold is_edge in Hyz'. destruct Hyz as [Hyz1 Hyz2]. rewrite andb_comm in Hyz1. rewrite Hyz1 in Hyz'.
                           simpl. simpl in Hyz'. rewrite Hyz'. reflexivity. apply HG.
                         - simpl. assert (Hz: z = hlhv). { apply Hhlhv with (tlhv := tlhv). reflexivity. }
                           rewrite Hz in *. destruct Hyz as [_ Hyz]. apply acyclic_no_two_cycle in Hyz as Hyz'. unfold is_edge in Hyz.
                           destruct G as [V E]. apply split_and_true in Hyz. unfold is_edge in Hyz'. destruct Hyz as [Hyz1 Hyz2]. rewrite andb_comm in Hyz1. rewrite Hyz1 in Hyz'.
                           simpl. simpl in Hyz'. rewrite Hyz'. reflexivity. apply HG. }

                       destruct (path_out_of_node h (u, v, h :: t) G) as [[|]|] eqn:Houth'.
                       - assert (Hmed: In h (find_confounders_in_path (u, v, h :: t) G)).
                         { simpl. unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'.
                           destruct t as [| h' t'].
                           - simpl. simpl in Houth'. rewrite eqb_refl in Houth'. unfold is_confounder_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                             destruct (edge_in_graph (h, v) G) as [|] eqn:Hhv. apply edge_in_graph_then_is_edge in Hhv. rewrite Hhv. simpl. left. reflexivity. apply HG. discriminate Houth'.
                           - simpl. rewrite eqb_refl in Houth'. simpl in Houth'. unfold is_confounder_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                             destruct (edge_in_graph (h, h') G) as [|] eqn:Hhh'. apply edge_in_graph_then_is_edge in Hhh'. rewrite Hhh'. simpl. left. reflexivity. apply HG. discriminate Houth'. }
                         unfold d_connected_2 in Hconn. destruct Hconn as [_ [Hconn _]]. apply no_overlap_non_member with (x := h) in Hconn.
                         apply Hconn. apply Hmed.
                       - assert (Hmed: In h (find_mediators_in_path (u, v, h :: t) G)).
                         { simpl. unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'.
                           destruct t as [| h' t'].
                           - simpl. simpl in Houth'. rewrite eqb_refl in Houth'. unfold is_mediator_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                             destruct (edge_in_graph (h, v) G) as [|] eqn:Hhv. discriminate Houth'. simpl in Hpath.
                             destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [Hpath _].
                             simpl in Hhv. simpl in Hpath. rewrite Hhv in Hpath. rewrite andb_comm in Hpath. simpl in Hpath. simpl. rewrite Hpath. rewrite orb_comm. simpl. left. reflexivity.
                           - simpl. simpl in Houth'. rewrite eqb_refl in Houth'. unfold is_mediator_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                             destruct (edge_in_graph (h, h') G) as [|] eqn:Hhv. discriminate Houth'. simpl in Hpath.
                             destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [Hpath _].
                             simpl in Hhv. simpl in Hpath. rewrite Hhv in Hpath. rewrite andb_comm in Hpath. simpl in Hpath. simpl. rewrite Hpath. rewrite orb_comm. simpl. left. reflexivity. }
                         unfold d_connected_2 in Hconn. destruct Hconn as [Hconn _]. apply no_overlap_non_member with (x := h) in Hconn.
                         apply Hconn. apply Hmed.
                       - unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'. rewrite eqb_refl in Houth'.
                         destruct t as [| h' t']. simpl in Houth'. destruct (edge_in_graph (h, v) G) as [|]. discriminate Houth'. discriminate Houth'.
                         simpl in Houth'. destruct (edge_in_graph (h, h') G) as [|]. discriminate Houth'. discriminate Houth'. }

                     simpl. destruct lhv as [| hlhv tlhv].
                     -- simpl. destruct (is_mediator_bool u v h G || is_mediator_bool v u h G) as [|].
                        ++ apply overlap_flip. simpl. apply member_In_equiv_F in HhZ. rewrite HhZ. reflexivity.
                        ++ apply overlap_with_empty.
                     -- simpl. destruct (is_mediator_bool u hlhv h G || is_mediator_bool hlhv u h G) as [|].
                        ++ apply overlap_flip. simpl. apply member_In_equiv_F in HhZ. rewrite HhZ. apply overlap_flip. apply Hlhv.
                        ++ apply Hlhv.
                 - (* h is a confounder, so not a mediator. then find_mediators(new path) = find_mediators(old path) *)
                   simpl. destruct lhv as [| hlhv tlhv].
                   + simpl. destruct (is_mediator_bool u v h G || is_mediator_bool v u h G) as [|] eqn:Hmed.
                     * assert (Hmedh: In h (find_mediators_in_path (u, v, [h]) G)). { simpl. rewrite Hmed. left. reflexivity. }
                       apply if_mediator_then_not_confounder_path in Hmedh. exfalso. destruct Hmedh as [Hmedh _]. apply Hmedh. apply Hh. apply HG. apply Hu_h_lhv_cyc.
                     * apply overlap_with_empty.
                   + simpl. destruct (is_mediator_bool u hlhv h G || is_mediator_bool hlhv u h G) as [|] eqn:Hmed.
                     * assert (Hmedh: In h (find_mediators_in_path (u, v, h :: hlhv :: tlhv) G)). { simpl. rewrite Hmed. left. reflexivity. }
                       apply if_mediator_then_not_confounder_path in Hmedh. exfalso. destruct Hmedh as [Hmedh _]. apply Hmedh. apply Hh. apply HG. apply Hu_h_lhv_cyc.
                     * apply Hlhv. }

               { destruct Hh as [Hh | Hh].
                 - (* h is a mediator, so not a confounder. then find_confounders(new path) = find_confounders(old path) *)
                   simpl. destruct lhv as [| hlhv tlhv].
                   + simpl. destruct (is_confounder_bool u v h G) as [|] eqn:Hmed.
                     * assert (Hmedh: In h (find_confounders_in_path (u, v, [h]) G)). { simpl. rewrite Hmed. left. reflexivity. }
                       apply if_mediator_then_not_confounder_path in Hh. exfalso. destruct Hh as [Hh _]. apply Hh. apply Hmedh. apply HG. apply Hu_h_lhv_cyc.
                     * apply overlap_with_empty.
                   + simpl. destruct (is_confounder_bool u hlhv h G) as [|] eqn:Hmed.
                     * assert (Hmedh: In h (find_confounders_in_path (u, v, h :: hlhv :: tlhv) G)). { simpl. rewrite Hmed. left. reflexivity. }
                       apply if_mediator_then_not_confounder_path in Hh. exfalso. destruct Hh as [Hh _]. apply Hh. apply Hmedh. apply HG. apply Hu_h_lhv_cyc.
                     * apply Hlhv.
                 - (* if h is a confounder in the new path, then u<-h->...lhv
                      if arrow didn't change, then confounder in original path, so not in Z
                      if arrow changed, then in original path u<-h<- (not in Z since d-conn) *)
                   apply confounders_vs_edges_in_path in Hh. destruct Hh as [y [z [Hh Hyz]]].

                   apply Hsub in Hh as Hsub'. destruct Hsub' as [Hlhv0 Hhlhv].

                   assert (Hyu: y = u). { destruct lhv as [| hlhv tlhv] eqn:Hl. apply Hlhv0. reflexivity. apply Hhlhv with (hlhv := hlhv) (tlhv := tlhv). reflexivity. }
                   rewrite Hyu in *. clear Hyu.

                   assert (HhZ: ~In h Z).
                   { assert (Houth: path_out_of_node h (h, v, lhv) G = Some true).
                     { unfold path_out_of_node. simpl. rewrite eqb_refl. destruct lhv as [| hlhv tlhv].
                       - simpl. assert (Hz: z = v). { apply Hlhv0. reflexivity. }
                         rewrite Hz in Hyz. destruct Hyz as [_ Hyz]. unfold is_edge in Hyz.
                         destruct G as [V E]. apply split_and_true in Hyz. destruct Hyz as [_ Hyz]. simpl. rewrite Hyz. reflexivity.
                       - simpl. assert (Hz: z = hlhv). { apply Hhlhv with (tlhv := tlhv). reflexivity. }
                         rewrite Hz in *. destruct Hyz as [_ Hyz]. destruct G as [V E]. apply split_and_true in Hyz. destruct Hyz as [_ Hyz]. simpl. rewrite Hyz. reflexivity. }

                     destruct (path_out_of_node h (u, v, h :: t) G) as [[|]|] eqn:Houth'.
                     - assert (Hmed: In h (find_confounders_in_path (u, v, h :: t) G)).
                       { simpl. unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'.
                         destruct t as [| h' t'].
                         - simpl. simpl in Houth'. rewrite eqb_refl in Houth'. unfold is_confounder_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                           destruct (edge_in_graph (h, v) G) as [|] eqn:Hhv. apply edge_in_graph_then_is_edge in Hhv. rewrite Hhv. simpl. left. reflexivity. apply HG. discriminate Houth'.
                         - simpl. rewrite eqb_refl in Houth'. simpl in Houth'. unfold is_confounder_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                           destruct (edge_in_graph (h, h') G) as [|] eqn:Hhh'. apply edge_in_graph_then_is_edge in Hhh'. rewrite Hhh'. simpl. left. reflexivity. apply HG. discriminate Houth'. }

                       unfold d_connected_2 in Hconn. destruct Hconn as [_ [Hconn _]]. apply no_overlap_non_member with (x := h) in Hconn.
                       apply Hconn. apply Hmed.
                     - assert (Hlem: path_out_of_node h (h, v, lhv) G = Some true -> ~ In h Z).
                       { apply Hout. right. exists false. split.
                         - rewrite <- path_out_of_node_cat with (u := u). apply Houth'. apply Hhu.
                         - simpl. apply Houth. }
                       apply Hlem. apply Houth.
                     - unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'. rewrite eqb_refl in Houth'.
                       destruct t as [| h' t']. simpl in Houth'. destruct (edge_in_graph (h, v) G) as [|]. discriminate Houth'. discriminate Houth'.
                       simpl in Houth'. destruct (edge_in_graph (h, h') G) as [|]. discriminate Houth'. discriminate Houth'. }

                     simpl. destruct lhv as [| hlhv tlhv].
                     -- simpl. destruct (is_confounder_bool u v h G) as [|].
                        ++ apply overlap_flip. simpl. apply member_In_equiv_F in HhZ. rewrite HhZ. reflexivity.
                        ++ apply overlap_with_empty.
                     -- simpl. destruct (is_confounder_bool u hlhv h G) as [|].
                        ++ apply overlap_flip. simpl. apply member_In_equiv_F in HhZ. rewrite HhZ. apply overlap_flip. apply Hlhv.
                        ++ apply Hlhv. }

               { unfold nodes in *. rewrite HFcol. apply Hlhv. } split.
               { apply Hpath'. } split.

               { intros w H. destruct (w =? u) as [|] eqn:Hwu.
                 - (* contradicts H, since would be the same *) apply eqb_eq in Hwu. rewrite Hwu in H. destruct H as [H | H].
                   + destruct H as [_ H]. unfold node_in_path in H. simpl in H. rewrite eqb_refl in H. simpl in H. discriminate H.
                   + unfold path_out_of_node in H. simpl in H. rewrite eqb_refl in H. destruct (edge_in_graph (u, h) G) as [|].
                     * destruct H as [b Hb]. destruct Hb as [Hb1 Hb2]. rewrite Hb1 in Hb2. inversion Hb2. destruct b as [|]. discriminate H0. discriminate H0.
                     * destruct H as [b Hb]. destruct Hb as [Hb1 Hb2]. rewrite Hb1 in Hb2. inversion Hb2. destruct b as [|]. discriminate H0. discriminate H0.
                 - assert (Houtw: path_out_of_node w (u, v, h :: lhv) G = path_out_of_node w (h, v, lhv) G).
                   { apply path_out_of_node_cat. apply Hwu. }
                   assert (Houtw': path_out_of_node w (u, v, h :: t) G = path_out_of_node w (h, v, t) G).
                   { apply path_out_of_node_cat. apply Hwu. }
                   unfold nodes in *. rewrite Houtw in H. rewrite Houtw' in H.
                   assert (Hnode: node_in_path w (u, v, h :: lhv) = node_in_path w (h, v, lhv)).
                   { symmetry. apply node_in_path_cat. apply Hwu. }
                   assert (Hnode': node_in_path w (u, v, h :: t) = node_in_path w (h, v, t)).
                   { symmetry. apply node_in_path_cat. apply Hwu. }
                   rewrite Hnode in H. rewrite Hnode' in H. apply Hout in H. rewrite Houtw. apply H. }

               exists Dh. split.
               { unfold nodes in *. rewrite HFcol. apply HDh. }
               intros c Hc. unfold nodes in *. rewrite HFcol in Hc. destruct HDh as [_ HDh]. pose proof Hc as Hc'. apply HDh in Hc. destruct Hc as [Hc | Hc].
               left. apply Hc.
               right. destruct Hc as [p [d Hc]]. exists p. exists d.
               rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite and_comm. rewrite <- and_assoc.
               split. repeat split; apply Hc.
               apply overlap_flip. simpl.
               assert (Hu: member u (p ++ [d]) = false).
               { destruct (member u (p ++ [d])) as [|] eqn:Hu.
                 - assert (HuL': In u L).
                   { apply collider_descendants_from_assignments_mem with (D := Dh) (G := G) (c := c) (p' := (h, v, lhv)) (p := p) (d := d).
                     apply Hc'. 2: { apply HLh. } 2: { apply member_In_equiv. apply Hu. }
                     split. apply Hc. destruct (d =? c) as [|] eqn:Hdc.
                     { destruct Hc as [_ [HdZ [_ [_ [HcZ _]]]]]. simpl in HcZ. destruct (member c Z) as [|] eqn:HcZ'. discriminate HcZ.
                       apply member_In_equiv_F in HcZ'. exfalso. apply HcZ'. apply eqb_eq in Hdc. rewrite <- Hdc. apply HdZ. }
                     { reflexivity. } }
                   apply member_In_equiv_F in HuL. exfalso. apply HuL. apply HuL'.
                 - reflexivity. }
               rewrite Hu. destruct Hc as [_ [_ [_ [_ [_ [Hc _]]]]]]. apply overlap_flip in Hc. apply Hc.

           --- (* CASE 2C *)
               assert (Huh: is_edge (u, h) G = true).
               { simpl in Hh. destruct lhv as [| hlhv tlhv].
                 - simpl in Hh. destruct (is_collider_bool u v h G) as [|] eqn:Huhv.
                   + unfold is_collider_bool in Huhv. apply split_and_true in Huhv. apply Huhv.
                   + exfalso. apply Hh.
                 - simpl in Hh. destruct (is_collider_bool u hlhv h G) as [|] eqn:Huhv.
                   + unfold is_collider_bool in Huhv. apply split_and_true in Huhv. apply Huhv.
                   + assert (Hmem: In h (hlhv :: tlhv)).
                     { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := h) in Hlhv. apply Hlhv. right. right. apply Hh. }
                     destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. exfalso. apply Hlhv. apply Hmem. }

               assert (Hhv: (lhv = [] -> is_edge (v, h) G = true) /\ (forall (hlhv: node) (tlhv: nodes), lhv = hlhv :: tlhv -> is_edge (hlhv, h) G = true)).
               { split.
                 - intros Hlhv0. rewrite Hlhv0 in Hh. simpl in Hh.
                   destruct (is_collider_bool u v h G) as [|] eqn:Huhv.
                   * unfold is_collider_bool in Huhv. apply split_and_true in Huhv. apply Huhv.
                   * exfalso. apply Hh.
                 - intros hlhv tlhv Hlhv0. rewrite Hlhv0 in *. simpl in Hh. destruct (is_collider_bool u hlhv h G) as [|] eqn:Huhv.
                   + unfold is_collider_bool in Huhv. apply split_and_true in Huhv. apply Huhv.
                   + assert (Hmem: In h (hlhv :: tlhv)).
                     { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := h) in Hlhv. apply Hlhv. right. right. apply Hh. }
                     destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. exfalso. apply Hlhv. apply Hmem. }

               assert (Hcol: find_colliders_in_path (u, v, h :: lhv) G = h :: find_colliders_in_path (h, v, lhv) G).
               { simpl. destruct lhv as [| hlhv tlhv].
                 - simpl. simpl in Hh. destruct (is_collider_bool u v h G) as [|]. reflexivity. exfalso. apply Hh.
                 - simpl. simpl in Hh. destruct (is_collider_bool u hlhv h G) as [|]. reflexivity.
                   assert (Hhmem: In h (hlhv :: tlhv)).
                   { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := h) in Hlhv. apply Hlhv. right. right. apply Hh. }
                   destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. exfalso. apply Hlhv. apply Hhmem. }

               assert (Hconn': d_connected_2 (u, v, h :: lhv) G Z).
               { apply d_connected_cat. apply HG. apply Hu_h_lhv_cyc. apply Hlhv. right. right. split. apply Hh.

                 pose proof Hconn as Hconn'. destruct Hconn as [_ [_ Hconn]]. simpl in Hconn. destruct t as [| ht tt].
                 + simpl in Hconn. destruct (is_collider_bool u v h G) as [|] eqn:Hcolht.
                   * apply forallb_true_iff_mem with (x := h) in Hconn. apply Hconn. left. reflexivity.
                   * (* h is not a collider in original path, so path_out = true in original, false in new *)
                     assert (Houth: ((exists (du : node) (pu : nodes),
                                         is_directed_path_in_graph (h, du, pu) G = true /\
                                         In du Z /\ ~ In h Z) \/
                                      path_out_of_node h (h, v, lhv) G <> Some true /\ In h Z) /\
                                     (path_out_of_node h (h, v, lhv) G = Some true -> ~ In h Z)).
                     { apply Hout. right. exists true. split.
                       - unfold path_out_of_node. simpl. rewrite eqb_refl. unfold is_collider_bool in Hcolht.
                         rewrite Huh in Hcolht. simpl in Hcolht. simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath.
                         destruct Hpath as [_ Hpath]. rewrite Hcolht in Hpath. rewrite andb_comm in Hpath. rewrite orb_comm in Hpath. simpl in Hpath.
                         simpl. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. rewrite Hpath. reflexivity.
                       - unfold path_out_of_node. simpl. rewrite eqb_refl. destruct lhv as [| hlhv tlhv] eqn:Hlhveq.
                         + simpl. assert (Huhv: is_edge (v, h) G = true). { apply Hhv. reflexivity. } apply acyclic_no_two_cycle in Huhv.
                           rewrite edge_in_graph_equiv in Huhv. rewrite Huhv. reflexivity. apply HG. apply HG.
                         + simpl. assert (Huhv: is_edge (hlhv, h) G = true). { apply Hhv with (hlhv := hlhv) (tlhv := tlhv). reflexivity. } apply acyclic_no_two_cycle in Huhv.
                           rewrite edge_in_graph_equiv in Huhv. rewrite Huhv. reflexivity. apply HG. apply HG. }

                     assert (HhZ: ~In h Z).
                     { apply intermediate_node_in_path with (x := h) in Hpath. assert (Hhh: In h [h]). { left. reflexivity. } apply Hpath in Hhh.
                       destruct Hhh as [Hhh | [Hhh | Hhh]].
                       - destruct Hconn' as [Hconn' _]. apply no_overlap_non_member with (x := h) in Hconn'. apply Hconn'. apply Hhh.
                       - destruct Hconn' as [_ [Hconn' _]]. apply no_overlap_non_member with (x := h) in Hconn'. apply Hconn'. apply Hhh.
                       - simpl in Hhh. rewrite Hcolht in Hhh. exfalso. apply Hhh. }

                     destruct Houth as [[[dh [ph Houth]] | Houth] _].
                     unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists dh. split.
                     apply find_descendants_correct. right. exists (h, dh, ph). split. apply Houth. apply path_start_end_refl. apply Houth.
                     exfalso. apply HhZ. apply Houth.

                 + simpl in Hconn. destruct (is_collider_bool u ht h G) as [|] eqn:Hcolht.
                   * apply forallb_true_iff_mem with (x := h) in Hconn. apply Hconn. left. reflexivity.
                   * (* h is not a collider in original path, so path_out = true in original, false in new *)
                     assert (Houth: ((exists (du : node) (pu : nodes),
                                         is_directed_path_in_graph (h, du, pu) G = true /\
                                         In du Z /\ ~ In h Z) \/
                                      path_out_of_node h (h, v, lhv) G <> Some true /\ In h Z) /\
                                     (path_out_of_node h (h, v, lhv) G = Some true -> ~ In h Z)).
                     { apply Hout. right. exists true. split.
                       - unfold path_out_of_node. simpl. rewrite eqb_refl. unfold is_collider_bool in Hcolht.
                         rewrite Huh in Hcolht. simpl in Hcolht. simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath.
                         destruct Hpath as [_ Hpath]. rewrite Hcolht in Hpath. rewrite andb_comm in Hpath. rewrite orb_comm in Hpath. simpl in Hpath.
                         simpl. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. rewrite Hpath. reflexivity.
                       - unfold path_out_of_node. simpl. rewrite eqb_refl. destruct lhv as [| hlhv tlhv] eqn:Hlhveq.
                         + simpl. assert (Huhv: is_edge (v, h) G = true). { apply Hhv. reflexivity. } apply acyclic_no_two_cycle in Huhv.
                           rewrite edge_in_graph_equiv in Huhv. rewrite Huhv. reflexivity. apply HG. apply HG.
                         + simpl. assert (Huhv: is_edge (hlhv, h) G = true). { apply Hhv with (hlhv := hlhv) (tlhv := tlhv). reflexivity. } apply acyclic_no_two_cycle in Huhv.
                           rewrite edge_in_graph_equiv in Huhv. rewrite Huhv. reflexivity. apply HG. apply HG. }
                     assert (HhZ: ~In h Z).
                     { pose proof Hpath as Hpathh. apply intermediate_node_in_path with (x := h) in Hpath. assert (Hhh: In h (h :: ht :: tt)). { left. reflexivity. } apply Hpath in Hhh.
                       destruct Hhh as [Hhh | [Hhh | Hhh]].
                       - destruct Hconn' as [Hconn' _]. apply no_overlap_non_member with (x := h) in Hconn'. apply Hconn'. apply Hhh.
                       - destruct Hconn' as [_ [Hconn' _]]. apply no_overlap_non_member with (x := h) in Hconn'. apply Hconn'. apply Hhh.
                       - simpl in Hhh. rewrite Hcolht in Hhh.
                         assert (Htt: In h (ht :: tt)).
                         { assert (Hpathh': is_path_in_graph (h, v, ht :: tt) G = true). { simpl in Hpathh. destruct G as [V E]. apply split_and_true in Hpathh. apply Hpathh. }
                         apply intermediate_node_in_path with (x := h) in Hpathh'. apply Hpathh'. right. right. apply Hhh. }
                         apply acyclic_path_cat in Hcyc. destruct Hcyc as [_ [Hcyc _]]. exfalso. apply Hcyc. apply Htt. }

                     destruct Houth as [[[dh [ph Houth]] | Houth] _].
                     unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists dh. split.
                     apply find_descendants_correct. right. exists (h, dh, ph). split. apply Houth. apply path_start_end_refl. apply Houth.
                     exfalso. apply HhZ. apply Houth. }

               assert (Hh': In h Z \/ (~In h Z /\ exists (z: node) (dp: nodes), is_directed_path_in_graph (h, z, dp) G = true /\ acyclic_path_2 (h, z, dp) /\ overlap dp Z = false /\ In z Z)).
               { apply colliders_have_unblocked_path_to_descendant with (p := (u, v, h :: lhv)). apply Hh. apply Hconn'. }

               destruct Hh' as [Hh' | Hh'].
               { (* CASE 2C.1 *) exists (h :: lhv). split. repeat split.
                 { apply Hcyc. }
                 { intros Hmem. destruct Hmem as [Hmem | Hmem].
                   - unfold acyclic_path_2 in Hcyc. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. left. apply Hmem.
                   - apply member_In_equiv_F in Hulhv. apply Hulhv. apply Hmem. }
                 { unfold acyclic_path_2 in Hlhv. intros Hmem. destruct Hmem as [Hmem | Hmem].
                   - destruct Hlhv as [[[Hlhv _] _] _]. apply Hlhv. apply Hmem.
                   - destruct Hlhv as [[[_ [_ [Hlhv _]]] _] _]. apply Hlhv. apply Hmem. }
                 { destruct Hlhv as [[Hlhv _] _]. apply acyclic_path_correct_2 in Hlhv. apply acyclic_path_reverse in Hlhv.
                   simpl in Hlhv. rewrite reverse_list_append in Hlhv. simpl in Hlhv. apply split_and_true in Hlhv. destruct Hlhv as [_ Hlhv].
                   apply acyclic_path_reverse in Hlhv. rewrite reverse_list_append in Hlhv. rewrite <- reverse_list_twice in Hlhv. apply Hlhv. } split.
                 apply Hconn'. split. apply Hpath'. split.
                 { intros w H. destruct (w =? u) as [|] eqn:Hwu.
                   - (* contradicts H, since would be the same *) apply eqb_eq in Hwu. rewrite Hwu in H. destruct H as [H | H].
                     + destruct H as [_ H]. unfold node_in_path in H. simpl in H. rewrite eqb_refl in H. simpl in H. discriminate H.
                     + unfold path_out_of_node in H. simpl in H. rewrite eqb_refl in H. destruct (edge_in_graph (u, h) G) as [|].
                       * destruct H as [b Hb]. destruct Hb as [Hb1 Hb2]. rewrite Hb1 in Hb2. inversion Hb2. destruct b as [|]. discriminate H0. discriminate H0.
                       * destruct H as [b Hb]. destruct Hb as [Hb1 Hb2]. rewrite Hb1 in Hb2. inversion Hb2. destruct b as [|]. discriminate H0. discriminate H0.
                   - assert (Houtw: path_out_of_node w (u, v, h :: lhv) G = path_out_of_node w (h, v, lhv) G).
                     { apply path_out_of_node_cat. apply Hwu. }
                     assert (Houtw': path_out_of_node w (u, v, h :: t) G = path_out_of_node w (h, v, t) G).
                     { apply path_out_of_node_cat. apply Hwu. }
                     unfold nodes in *. rewrite Houtw in H. rewrite Houtw' in H.
                     assert (Hnode: node_in_path w (u, v, h :: lhv) = node_in_path w (h, v, lhv)).
                     { symmetry. apply node_in_path_cat. apply Hwu. }
                     assert (Hnode': node_in_path w (u, v, h :: t) = node_in_path w (h, v, t)).
                     { symmetry. apply node_in_path_cat. apply Hwu. }
                     rewrite Hnode in H. rewrite Hnode' in H. apply Hout in H. rewrite Houtw. apply H. }

                 exists ((h, ([], h)) :: Dh). split. unfold nodes in *. rewrite Hcol. split.
                 - simpl. rewrite eqb_refl. simpl. apply is_assignment_for_cat. apply HDh.
                 - intros w Hw. simpl in Hw. simpl. destruct (h =? w) as [|] eqn:Hhw. discriminate Hw. rewrite eqb_sym in Hhw. rewrite Hhw.
                   simpl. destruct HDh as [[_ HDh] _]. apply HDh. apply Hw.
                 - intros c Hc. unfold nodes in *. rewrite Hcol in Hc. destruct Hc as [Hc | Hc].
                   + left. rewrite <- Hc in *. split. simpl. rewrite eqb_refl. reflexivity. apply Hh'.
                   + assert (HcDh: get_assigned_value ((h, ([], h)) :: Dh) c = get_assigned_value Dh c).
                     { simpl. destruct (h =? c) as [|] eqn:Hhc.
                       - apply eqb_eq in Hhc. rewrite <- Hhc in Hc.
                         assert (Hhmem: In h lhv).
                         { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := h) in Hlhv. apply Hlhv. right. right. apply Hc. }
                         destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. exfalso. apply Hlhv. apply Hhmem.
                       - reflexivity. }
                     rewrite HcDh. pose proof Hc as Hcolc.
                     destruct HDh as [_ HDh]. apply HDh in Hc. destruct Hc as [Hc | Hc]. left. apply Hc. right.
                     destruct Hc as [p [d Hc]]. exists p. exists d. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc.
                     split. repeat split; apply Hc. split.
                     apply overlap_flip. simpl. destruct (member u (p ++ [d])) as [|] eqn:Humem.
                     * exfalso. apply member_In_equiv_F in HuL. apply HuL. 
                       apply collider_descendants_from_assignments_mem with (D := Dh) (p' := (h, v, lhv)) (p := p) (d := d) (c := c) (G := G).
                       apply Hcolc. split. apply Hc. destruct (d =? c) as [|] eqn:Hdc. apply eqb_eq in Hdc. destruct Hc as [_ [HdZ [_ [_ [HcZ _]]]]].
                       exfalso. apply no_overlap_non_member with (x := c) in HcZ. apply HcZ. left. reflexivity. rewrite <- Hdc. apply HdZ. reflexivity.
                       apply HLh. apply member_In_equiv. apply Humem.
                     * destruct Hc as [_ [_ [_ [_ [_ [Hc _]]]]]]. apply overlap_flip in Hc. apply Hc.
                     * intros c' d' p' Hc'. simpl in Hc'. destruct (h =? c') as [|] eqn:Hhc'.
                       -- destruct Hc' as [Hcc' Hc']. inversion Hc'. rewrite <- H1. apply eqb_eq in Hhc'. rewrite <- Hhc'.
                          apply overlap_flip. simpl. rewrite <- Hhc' in Hcc'. rewrite Hcc'. destruct (member h (p ++ [d])) as [|] eqn:Hmem.
                          ++ destruct Hc as [_ [_ [_ [_ [_ [Hc _]]]]]]. apply no_overlap_non_member with (x := h) in Hc. exfalso. apply Hc. apply member_In_equiv. apply Hmem.
                             left. reflexivity.
                          ++ reflexivity.
                       -- apply Hc. apply Hc'. }

               { destruct Hh' as [HhZ [zh [ph Hh']]].
                 assert (Hacyc: forall (cy dy y: node) (l1 l2 l3: nodes), l1 ++ [y] ++ l2 = l3 ++ [dy] /\ acyclic_path_2 (cy, dy, l3)
                                   -> acyclic_path_2 (cy, y, l1)).
                 { intros cy dy y l1 l2 l3 [H1 H2].
                   destruct (rev l2) as [| hl2 tl2] eqn:Hl.
                   - assert (Hl': rev l2 = [] -> y = dy /\ l1 = l3). { apply Hl2. apply H1. } apply Hl' in Hl.
                     clear Hl'. destruct Hl as [Hl Hl']. rewrite Hl. rewrite Hl'. apply H2.
                   - assert (Hl': rev l2 = hl2 :: tl2 -> dy = hl2 /\ l3 = l1 ++ [y] ++ rev tl2). { apply Hl2. apply H1. } apply Hl' in Hl. clear Hl'.
                     destruct Hl as [Hl Hl']. apply subpath_still_acyclic_2 with (v := dy) (l2 := rev tl2) (l3 := l3).
                     split. symmetry. apply Hl'. apply H2. }

                 assert (Hcyccy': forall (cy dy y: node) (py lhcy1 lhcy2 lcyd1 lcyd2: nodes),
                                  (In dy Z /\
                                   is_directed_path_in_graph (cy, dy, py) G = true /\
                                   acyclic_path_2 (cy, dy, py) /\
                                   overlap (cy :: py) Z = false /\
                                   overlap (py ++ [dy]) (h :: lhv ++ [v]) = false /\
                                   (forall (c' d' : node) (p' : nodes),
                                    (cy =? c') = false /\
                                    get_assigned_value Dh c' = Some (p', d') ->
                                    overlap (cy :: py ++ [dy]) (c' :: p' ++ [d']) = false))
                                  -> lhcy1 ++ [cy] ++ lhcy2 = lhv
                                  -> py ++ [dy] = lcyd1 ++ [y] ++ lcyd2
                                  -> acyclic_path_2 (y, v, rev lcyd1 ++ [cy] ++ lhcy2)
                                     /\ ~In h (rev lcyd1 ++ [cy] ++ lhcy2)).
                 { intros cy dy y py lhcy1 lhcy2 lcyd1 lcyd2 Hpdy'' Hcy Hy'. split.
                   { apply concat_paths_acyclic. split.
                     -- intros Hyv. destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := y) in Hpdy''. apply Hpdy''.
                        rewrite Hy'. apply membership_append_r. left. reflexivity.
                        right. apply membership_append_r. left. symmetry. apply Hyv.
                     -- split.
                        ++ apply reverse_path_still_acyclic. apply Hacyc with (dy := dy) (l2 := lcyd2) (l3 := py). split. symmetry. apply Hy'.
                           apply Hpdy''.
                        ++ apply subpath_still_acyclic with (w := h) (l1 := lhcy1) (l3 := lhv). split. apply Hcy. apply Hlhv.
                     -- split.
                        ++ (* Hpdy'', cy's desc path cannot intersect lhv *)
                           intros Hmem. destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := y) in Hpdy''.
                           apply Hpdy''. rewrite Hy'. apply membership_append_r. left. reflexivity.
                           right. apply membership_append. rewrite <- Hcy. apply membership_append_r. apply membership_append_r. apply Hmem.

                        ++ (* Hpdy'', v cannot intersect cy's desc path *)
                           intros Hmem. destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := v) in Hpdy''.
                           apply Hpdy''. rewrite Hy'. apply membership_append. apply membership_rev. apply Hmem.
                           right. apply membership_append_r. left. reflexivity.

                     -- (* Hpdy'', cy's desc path cannot intersect lhv *)
                        apply no_overlap_non_member. intros w Hw Hw'. destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := w) in Hpdy''.
                        apply Hpdy''. rewrite Hy'. apply membership_append. apply membership_rev. apply Hw'.
                        right. apply membership_append. rewrite <- Hcy. apply membership_append_r. apply membership_append_r. apply Hw. }
                   { intros Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                     -- destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := h) in Hpdy''. apply Hpdy''.
                        rewrite Hy'. apply membership_append. apply membership_rev. apply Hmem. left. reflexivity.
                     -- destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. apply Hlhv.
                        rewrite <- Hcy. apply membership_append_r. apply Hmem. } }

                 assert (Hpathcy': forall (cy dy y: node) (py l1 l2: nodes),
                                  is_directed_path_in_graph (cy, dy, py) G = true
                                  -> py ++ [dy] = l1 ++ [y] ++ l2
                                  -> is_directed_path_in_graph (cy, y, l1) G = true).
                 { intros cy dy y py l1 l2 Hdir Hpdy. symmetry in Hpdy.
                   destruct (rev l2) as [| hl2 tl2] eqn:Hrevl2.
                   - apply Hl2 in Hpdy. apply Hpdy in Hrevl2. destruct Hrevl2 as [Hdy Hpy]. rewrite Hdy. rewrite Hpy. apply Hdir.
                   - apply Hl2 in Hpdy. apply Hpdy in Hrevl2. destruct Hrevl2 as [Hdy Hpy].
                     apply subpath_still_directed_2 with (v := dy) (l2 := rev tl2) (l3 := py). split. symmetry. apply Hpy. apply Hdir. }

                 assert (Hconncy: forall (p l1 l2: nodes) (d c x: node),
                                      p ++ [d] = l1 ++ [x] ++ l2
                                      -> is_directed_path_in_graph (c, d, p) G = true /\ overlap p Z = false /\ acyclic_path_2 (c, d, p)
                                      -> d_connected_2 (c, x, l1) G Z).
                 { intros p l1 l2 d c x Hpd [Hdir [Hover Hcyclic]].
                   assert (Hpath'': is_directed_path_in_graph (c, x, l1) G = true).
                   { apply Hpathcy' with (dy := d) (py := p) (l2 := l2). apply Hdir. apply Hpd. }
                   repeat split.
                   + apply no_overlap_non_member. intros w Hw Hw'.
                     assert (Hw'': In w l1).
                     { apply directed_path_is_path in Hpath''. apply intermediate_node_in_path with (x := w) in Hpath''. apply Hpath''. left. apply Hw. }
                     apply no_overlap_non_member with (x := w) in Hover. apply Hover. symmetry in Hpd.
                     destruct (rev l2) as [| hl2 tl2] eqn:Hl2eq.
                     * apply Hl2 in Hpd. apply Hpd in Hl2eq. destruct Hl2eq as [_ Hl2eq]. rewrite <- Hl2eq. apply Hw''.
                     * apply Hl2 in Hpd. apply Hpd in Hl2eq. destruct Hl2eq as [_ Hl2eq]. rewrite Hl2eq. apply membership_append. apply Hw''.
                     * apply Hw'.
                   + apply no_overlap_non_member. intros w Hw Hw'.
                     assert (Hw'': In w l1).
                     { apply directed_path_is_path in Hpath''. apply intermediate_node_in_path with (x := w) in Hpath''. apply Hpath''. right. left. apply Hw. }
                     assert (Hmed: In w (find_mediators_in_path (c, x, l1) G)). { apply directed_path_all_mediators. split. apply Hpath''. apply Hw''. }
                     apply if_confounder_then_not_mediator_path in Hw. destruct Hw as [Hw _]. apply Hw. apply Hmed. apply HG.
                     apply Hacyc with (dy := d) (l2 := l2) (l3 := p). split. symmetry. apply Hpd. apply Hcyclic.
                   + apply forallb_true_iff_mem. intros w Hw.
                     assert (Hw'': In w l1).
                     { apply directed_path_is_path in Hpath''. apply intermediate_node_in_path with (x := w) in Hpath''. apply Hpath''. right. right. apply Hw. }
                     assert (Hmed: In w (find_mediators_in_path (c, x, l1) G)). { apply directed_path_all_mediators. split. apply Hpath''. apply Hw''. }
                     apply if_collider_then_not_mediator_path in Hw. destruct Hw as [Hw _]. exfalso. apply Hw. apply Hmed. apply HG.
                     apply Hacyc with (dy := d) (l2 := l2) (l3 := p). split. symmetry. apply Hpd. apply Hcyclic. }

                 assert (Huph: member u (ph ++ [zh]) = false).
                 { (* since u->h->...ph...->zh is a directed path and G is acyclic *)
                   destruct (member u (ph ++ [zh])) as [|] eqn:Hu.
                   - apply member_In_equiv in Hu.
                     (* cycle u -> h ->...ph..-> u *) apply membership_splits_list in Hu. destruct Hu as [lphu1 [lphu2 Hlphu]].
                     destruct HG as [_ HG]. apply contains_cycle_false_correct with (p := (u, u, h :: lphu1)) in HG.
                     + exfalso. destruct HG as [HG _]. apply HG. reflexivity.
                     + destruct (rev lphu2) as [| hlphu2 tlphu2] eqn:Hlphu2.
                       -- assert (Huv: rev lphu2 = [] -> u = zh /\ lphu1 = ph). { apply Hl2. apply Hlphu. } apply Huv in Hlphu2. destruct Hlphu2 as [Hlphu2 Hlphu2'].
                          simpl. apply split_and_true. split. apply Huh. rewrite Hlphu2. rewrite Hlphu2'. apply Hh'.
                       -- apply subpath_still_directed_2 with (v := zh) (l2 := rev tlphu2) (l3 := h :: ph). split. simpl. f_equal.
                          assert (Hlphu1: rev lphu2 = hlphu2 :: tlphu2 -> zh = hlphu2 /\ ph = lphu1 ++ [u] ++ rev tlphu2).
                          { apply Hl2. apply Hlphu. } apply Hlphu1 in Hlphu2. clear Hlphu1. symmetry. apply Hlphu2. simpl. apply split_and_true. split. apply Huh. apply Hh'.
                   - reflexivity. }


                 assert (Hph1ph: forall (w x': node) (ph1' ph2': nodes), In w ph1' -> ph ++ [zh] = ph1' ++ x' :: ph2' -> In w ph).
                 { intros w x' ph1' ph2' Hwph1 Hx'. symmetry in Hx'. destruct (rev ph2') as [| hph2 tph2] eqn:Hph2.
                   - apply Hl2 in Hx'. apply Hx' in Hph2. destruct Hph2 as [_ Hph2]. rewrite <- Hph2. apply Hwph1.
                   - apply Hl2 in Hx'. apply Hx' in Hph2. destruct Hph2 as [_ Hph2]. rewrite Hph2. apply membership_append. apply Hwph1. }

                 assert (Houtwu: forall (w : node) (x': node) (l1 l2: nodes),
                                node_in_path w (u, x', h :: l1) = true /\
                                node_in_path w (u, x', h :: l2) = false \/
                                (exists b : bool,
                                   path_out_of_node w (u, x', h :: l2) G = Some b /\
                                   path_out_of_node w (u, x', h :: l1) G = Some (negb b)) -> w =? u = false).
                 { intros w x' l1 l2 Hw. destruct (w =? u) as [|] eqn:Hwu. destruct Hw as [Hw | Hw].
                   - destruct Hw as [_ Hw]. unfold node_in_path in Hw. simpl in Hw. rewrite Hwu in Hw. simpl in Hw. discriminate Hw.
                   - destruct Hw as [b Hb]. unfold path_out_of_node in Hb. simpl in Hb. rewrite eqb_sym in Hwu. rewrite Hwu in Hb.
                     assert (F: negb b = b). { destruct Hb as [Hb1 Hb2]. destruct (edge_in_graph (u, h) G) as [|]. rewrite Hb2 in Hb1. inversion Hb1. rewrite H0. apply H0.
                                               rewrite Hb2 in Hb1. inversion Hb1. rewrite H0. apply H0. }
                     destruct b as [|]. discriminate F. discriminate F.
                   - reflexivity. }

                 assert (Houtwv: forall (x' w : node) (l1 l2: nodes), acyclic_path_2 (x', v, l2) ->
                                node_in_path w (x', v, l1) = true /\
                                node_in_path w (x', v, l2) = false \/
                                (exists b : bool,
                                   path_out_of_node w (x', v, l2) G = Some b /\
                                   path_out_of_node w (x', v, l1) G = Some (negb b)) -> w =? v = false).
                 { intros x' w l1 l2 Hcycv Hw. destruct (w =? v) as [|] eqn:Hwv. destruct Hw as [Hw | Hw].
                   - destruct Hw as [_ Hw]. unfold node_in_path in Hw. simpl in Hw. rewrite Hwv in Hw. rewrite <- orb_assoc in Hw. rewrite orb_comm in Hw. discriminate Hw.
                   - destruct Hw as [bw Hb]. assert (Hvmem: In v (x' :: l2)). { apply path_out_of_node_mem_gen with (G := G) (v := v). exists bw. apply eqb_eq in Hwv. rewrite Hwv in *. apply Hb. }
                     exfalso. destruct Hvmem as [Hvmem | Hvmem]. destruct Hcycv as [Hcycv _]. apply Hcycv. apply Hvmem. destruct Hcycv as [_ [_ [Hcycv _]]]. apply Hcycv. apply Hvmem.
                   - reflexivity. }

                 assert (Houtwph1: forall (w x': node) (ph1' ph2': nodes), In w ph1' -> ph ++ [zh] = ph1' ++ x' :: ph2' ->
                                ((exists (du : node) (pu : nodes),
                                    is_directed_path_in_graph (w, du, pu) G = true /\
                                    In du Z /\ ~ In w Z) \/
                                 path_out_of_node w (u, x', h :: ph1') G <> Some true /\ In w Z) /\
                                (path_out_of_node w (u, x', h :: ph1') G = Some true -> ~ In w Z)).
                 { intros w x' ph1' ph2' Hwmem Hx'. split.
                   - left. apply membership_splits_list in Hwmem. destruct Hwmem as [ph11 [ph22 Hph1]].
                     exists zh.
                     assert (Hphw: exists (pw: nodes), is_directed_path_in_graph (w, zh, pw) G = true).
                     { symmetry in Hx'. destruct (rev ph2') as [| hph2 tph2] eqn:Hph2.
                       - apply Hl2 in Hx'. exists ph22. apply subpath_still_directed with (w := h) (l1 := ph11) (l3 := ph1'). split. apply Hph1.
                         apply Hx' in Hph2. destruct Hph2 as [_ Hph2]. rewrite Hph2. apply Hh'.
                       - apply Hl2 in Hx'. exists (ph22 ++ [x'] ++ rev tph2). apply Hx' in Hph2. apply subpath_still_directed with (w := h) (l1 := ph11) (l3 := ph).
                         split. destruct Hph2 as [_ Hph2]. rewrite Hph2. rewrite <- Hph1. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hh'. }
                     destruct Hphw as [pw Hphw]. exists pw. split. apply Hphw. split. apply Hh'. intros HwZ.
                     destruct Hh' as [_ [_ [Hh' _]]]. apply no_overlap_non_member with (x := w) in Hh'. apply Hh'. apply Hph1ph with (x' := x') (ph1' := ph1') (ph2' := ph2'). rewrite <- Hph1. apply membership_append_r. left. reflexivity.
                     apply Hx'. apply HwZ.
                   - intros H. intros HwZ. destruct Hh' as [_ [_ [Hh' _]]]. apply no_overlap_non_member with (x := w) in Hh'. apply Hh'.
                     apply Hph1ph with (x' := x') (ph1' := ph1') (ph2' := ph2'). apply Hwmem. apply Hx'. apply HwZ. }


                 assert (Houtwcy: forall (w cy: node) (l1 lcy1 lcy2: nodes), In w (cy :: lcy2) -> lhv = lcy1 ++ [cy] ++ lcy2 -> acyclic_path_2 (h, v, l1 ++ [cy] ++ lcy2) ->
                                node_in_path w (h, v, l1 ++ [cy] ++ lcy2) = true /\
                                node_in_path w (h, v, t) = false \/
                                (exists b : bool,
                                   path_out_of_node w (h, v, t) G = Some b /\
                                   path_out_of_node w (h, v, l1 ++ [cy] ++ lcy2) G = Some (negb b)) ->

                                ((exists (du : node) (pu : nodes),
                                    is_directed_path_in_graph (w, du, pu) G = true /\
                                    In du Z /\ ~ In w Z) \/
                                 path_out_of_node w (h, v, l1 ++ [cy] ++ lcy2) G <> Some true /\ In w Z) /\
                                (path_out_of_node w (h, v, l1 ++ [cy] ++ lcy2) G = Some true -> ~ In w Z)).
                 { intros w cy l1 lcy1 lcy2 Hwcy Hlhv' Hcychv Hw.
                   assert (Hwlhv: path_out_of_node w (h, v, l1 ++ [cy] ++ lcy2) G = path_out_of_node w (h, v, lhv) G).
                   { assert (exists (b: bool), path_out_of_node w (h, v, lhv) G = Some b).
                     { apply path_out_of_node_mem_gen. right. rewrite Hlhv'. apply membership_append_r. apply Hwcy. }
                     destruct H as [bw Hb]. rewrite Hb.
                     apply subpath_preserves_path_out_of_node with (u := cy) (l1 := l1) (l2 := lcy2). split. reflexivity.
                     - apply superpath_preserves_path_out_of_node with (w := h) (l1 := lcy1) (l3 := lhv). symmetry. apply Hlhv'.
                       apply Hb. apply Hlhv. apply Hwcy.
                     - apply Hcychv. }
                    unfold nodes in *. unfold node in *. rewrite Hwlhv. apply Hout.
                    destruct Hw as [Hw | Hw].
                    -- left. split.
                       ++ rewrite node_in_path_equiv. apply member_In_equiv. right. apply membership_append. rewrite Hlhv'. apply membership_append_r. apply Hwcy.
                       ++ rewrite node_in_path_equiv. destruct Hw as [_ Hw]. rewrite node_in_path_equiv in Hw. simpl in Hw. apply Hw.
                    -- right. destruct Hw as [bw [Hb1 Hb2]]. exists bw. split.
                       ++ apply Hb1.
                       ++ rewrite <- Hwlhv. apply Hb2. }

                 assert (Hcolph1: forall (x': node) (ph1' ph2': nodes), ph ++ [zh] = ph1' ++ x' :: ph2' ->
                                find_colliders_in_path (u, x', h :: ph1') G = []). (* the path is directed *)
                 { intros x' ph1' ph2' Hph'. destruct (find_colliders_in_path (u, x', h :: ph1') G) as [| ch ct] eqn:Hcolc. reflexivity.
                   assert (Hdir': is_directed_path_in_graph (h, x', ph1') G = true).
                   { apply Hpathcy' with (dy := zh) (py := ph) (l2 := ph2'). apply Hh'. apply Hph'. }
                   assert (Hdir: is_directed_path_in_graph (u, x', h :: ph1') G = true).
                   { simpl. rewrite Huh. simpl. apply Hdir'. } clear Hdir'.

                   assert (Hch: In ch (find_mediators_in_path (u, x', h :: ph1') G)).
                   { apply directed_path_all_mediators. split. apply Hdir. apply directed_path_is_path in Hdir. apply intermediate_node_in_path with (x := ch) in Hdir.
                     apply Hdir. right. right. unfold nodes in *. unfold node in *. rewrite Hcolc. left. reflexivity. }
                   apply if_mediator_then_not_confounder_path in Hch. exfalso. destruct Hch as [_ Hch]. apply Hch. unfold nodes in *. unfold node in *. rewrite Hcolc. left. reflexivity.
                   apply HG. apply acyclic_path_cat_2. apply Hacyc with (dy := zh) (l2 := ph2') (l3 := ph). split. symmetry. apply Hph'. apply Hh'. intros Humem. destruct Humem as [Humem | Humem].
                   rewrite Humem in Hhu. rewrite eqb_refl in Hhu. discriminate Hhu. apply member_In_equiv_F in Huph. apply Huph. rewrite Hph'. rewrite <- append_vs_concat. apply membership_append. apply Humem. }

                 assert (Hcoldir: forall (c x' d: node) (p' p1' p2': nodes), p' ++ [d] = p1' ++ x' :: p2' -> is_directed_path_in_graph (c, d, p') G = true -> acyclic_path_2 (c, d, p')
                                -> find_colliders_in_path (x', c, rev p1') G = []). (* the path is reverse of directed *)
                 { intros c x' d ph' ph1' ph2' Hph' Hdir Hcyc'. destruct (find_colliders_in_path (x', c, rev ph1') G) as [| ch ct] eqn:Hcolc. reflexivity.
                   assert (Hdir': is_directed_path_in_graph (c, x', ph1') G = true).
                   { apply Hpathcy' with (dy := d) (py := ph') (l2 := ph2'). apply Hdir. apply Hph'. }
                   assert (Hch: In ch (find_mediators_in_path (x', c, rev ph1') G)).
                   { apply mediators_same_in_reverse_path. apply directed_path_all_mediators. split. apply Hdir'. apply directed_path_is_path in Hdir'. apply intermediate_node_in_path with (x := ch) in Hdir'.
                     apply Hdir'. right. right. rewrite reverse_list_twice with (l := ph1'). apply colliders_same_in_reverse_path. unfold nodes in *. unfold node in *. rewrite Hcolc. left. reflexivity. }
                   apply if_mediator_then_not_confounder_path in Hch. exfalso. destruct Hch as [_ Hch]. apply Hch. unfold nodes in *. unfold node in *. rewrite Hcolc. left. reflexivity.
                   apply HG. apply reverse_path_still_acyclic. apply Hacyc with (dy := d) (l2 := ph2') (l3 := ph'). split. symmetry. apply Hph'. apply Hcyc'. }

                 destruct (overlap (ph ++ [zh]) (lhv ++ [v])) as [|] eqn:Hoverh.
                 - apply overlap_rev_true in Hoverh.
                   apply list_has_first_elt_in_common_with_other_list in Hoverh. destruct Hoverh as [ph1 [ph2 [lx1 [lx2 [x Hx]]]]]. rewrite reverse_list_append in Hx. simpl in Hx.

                   assert (Hcychx: acyclic_path_2 (h, x, ph1)).
                   { apply Hacyc with (dy := zh) (l2 := ph2) (l3 := ph). split. symmetry. apply Hx. apply Hh'. }

                   assert (Hdir: is_directed_path_in_graph (u, x, h :: ph1) G = true).
                   { simpl. apply split_and_true. split. apply Huh.
                     assert (Hdir: is_directed_path_in_graph (h,x, ph1) G = true).
                     { destruct (rev ph2) as [| hph2 tph2] eqn:Hph2.
                       - assert (Hph2': rev ph2 = [] -> x = zh /\ ph1 = ph). { apply Hl2. symmetry. apply Hx. } apply Hph2' in Hph2. clear Hph2'.
                         destruct Hph2 as [Hph2 Hph2']. rewrite Hph2'. rewrite Hph2. apply Hh'.
                       - apply subpath_still_directed_2 with (v := zh) (l2 := rev tph2) (l3 := ph). split.
                         assert (Hph2': rev ph2 = hph2 :: tph2 -> zh = hph2 /\ ph = ph1 ++ [x] ++ rev tph2). { apply Hl2. symmetry. apply Hx. }
                         apply Hph2' in Hph2. symmetry. apply Hph2. apply Hh'. }
                     apply Hdir. }

                   destruct lx1 as [| hlx1 tlx1].
                   + (* CASE 2C.2: x = v *)
                     destruct Hx as [Hx [Hx' _]]. inversion Hx'. rewrite H0 in *.
                     exists (h :: ph1). (* directed path u -> h -> ... -> v *)

                     split.
                     { apply acyclic_path_correct_2. simpl. apply split_and_true. split.
                       - (* u not in [h, ph1] bc cycle *)
                         apply negb_true_iff. rewrite Hhu. apply member_In_equiv_F. intros F. apply member_In_equiv_F in Huph. apply Huph.
                         rewrite Hx. rewrite <- append_vs_concat. apply membership_append. apply F.
                       - apply acyclic_path_correct_2 in Hcychx. apply Hcychx. }

                     split.
                     { apply d_connected_cat. apply HG. apply acyclic_path_cat_2. apply Hcychx. intros [Humem | Humem].
                       rewrite Humem in Hhu. rewrite eqb_refl in Hhu. discriminate Hhu. apply member_In_equiv_F in Huph. apply Huph. rewrite Hx. rewrite <- append_vs_concat. apply membership_append. apply Humem.
                       - apply Hconncy with (p := ph) (l2 := ph2) (d := zh). apply Hx. split. apply Hh'. split. apply Hh'. apply Hh'.
                       - left. split.
                         + apply directed_path_all_mediators. split. apply Hdir. left. reflexivity.
                         + apply HhZ. } split.
                     { apply directed_path_is_path. apply Hdir. } split.

                     { intros w Hw.
                       assert (Hwu: w =? u = false).
                       { apply Houtwu with (x' := x) (l1 := ph1) (l2 := t). apply Hw. }
                       rewrite <- node_in_path_cat in Hw. rewrite <- node_in_path_cat in Hw. 2: { apply Hwu. } 2: { apply Hwu. }
                       (* w = h: path to zh, h not in Z *)
                       destruct (w =? h) as [|] eqn:Hwh.
                       - apply eqb_eq in Hwh. rewrite Hwh. split.
                         + left. exists zh. exists ph. split. apply Hh'. split. apply Hh'. apply HhZ.
                         + intros H. apply HhZ.
                       - (* w = x: if x = zh, then right: path_out = None, in Z. Else, left. *)
                         destruct (w =? x) as [|] eqn:Hwx.
                         + apply eqb_eq in Hwx. rewrite Hwx in *.
                           assert (path_out_of_node x (u, x, h :: ph1) G = None).
                           { destruct (path_out_of_node x (u, x, h :: ph1) G) as [b|] eqn:Hb.
                             - assert (Hwmem: In x (u :: h :: ph1)). { apply path_out_of_node_mem_gen with (G := G) (v := x). exists b. apply Hb. }
                               destruct Hwmem as [Hwmem | Hwmem].
                               + exfalso. destruct Hcyc as [Hcyc _]. apply Hcyc. apply Hwmem.
                               + exfalso. destruct Hwmem as [Hwmem | Hwmem]. destruct Hcychx as [Hcychx _]. apply Hcychx. apply Hwmem.
                                 destruct Hcychx as [_ [_ [Hcychx _]]]. apply Hcychx. apply Hwmem.
                             - reflexivity. }
                           split.
                           * symmetry in Hx. apply Hl2 in Hx. destruct (rev ph2) as [| hph2 tph2] eqn:Hph2.
                             -- right. split. unfold nodes in *. unfold node in *. rewrite H. easy. assert (x = zh /\ ph1 = ph). { apply Hx. apply Hph2. }
                                destruct H2 as [H2 _]. rewrite H2. apply Hh'.
                             -- left. exists zh. exists (rev tph2). repeat split.
                                ++ apply subpath_still_directed with (w := h) (l1 := ph1) (l3 := ph). split. apply Hx in Hph2. symmetry. apply Hph2. apply Hh'.
                                ++ apply Hh'.
                                ++ intros HxZ. destruct Hh' as [_ [_ [Hh' _]]]. apply no_overlap_non_member with (x := x) in Hh'. apply Hh'.
                                   apply Hx in Hph2. destruct Hph2 as [_ Hph2]. rewrite Hph2. apply membership_append_r. left. reflexivity. apply HxZ.
                           * intros F. unfold nodes in *. unfold node in *. rewrite F in H. discriminate H.
                         + (* w in ph1: directed path to zh. path out is true, not in Z *)
                           assert (Hwmem: In w ph1).
                           { destruct Hw as [[Hw _] | Hw].
                             - unfold node_in_path in Hw. simpl in Hw. rewrite Hwh in Hw. rewrite Hwx in Hw. simpl in Hw. apply member_In_equiv. apply Hw.
                             - destruct Hw as [b [_ Hb]]. assert (In w (u :: h :: ph1)). { apply path_out_of_node_mem_gen with (G := G) (v := x). exists (negb b). apply Hb. }
                               apply member_In_equiv in H. simpl in H. rewrite eqb_sym in Hwu. rewrite Hwu in H. rewrite eqb_sym in Hwh. rewrite Hwh in H. apply member_In_equiv. apply H. }
                           apply Houtwph1 with (ph2' := ph2). apply Hwmem. apply Hx. }

                     exists []. assert (Hcol': find_colliders_in_path (u, x, h :: ph1) G = []). { apply Hcolph1 with (ph2' := ph2). apply Hx. }

                     unfold nodes in *. unfold node in *. rewrite Hcol'. split. unfold is_exact_assignment_for. split. simpl. reflexivity. simpl. reflexivity.
                     intros c F. unfold nodes in *. unfold node in *. rewrite Hcol' in F. exfalso. apply F.

                   + (* CASE 2C.3: v = hlx1 *)
                     destruct Hx as [Hx [Hx' Hx'']]. inversion Hx'. rewrite <- H0 in *.
                     assert (Hbout: exists (b: bool), path_out_of_node x (h, v, lhv) G = Some b).
                     { apply path_out_of_node_mem_2. right. apply membership_rev. rewrite H1. apply membership_append_r. left. reflexivity. }
                     destruct Hbout as [b Hbout].

                     assert (Hlhvrev: lhv = rev lx2 ++ [x] ++ rev tlx1).
                     { rewrite reverse_list_twice with (l := lhv).
                       rewrite H1. rewrite reverse_list_append. simpl. rewrite <- app_assoc. reflexivity. }

                     assert (HDx: exists (D: assignments (nodes * node)), get_collider_descendants_for_subpath Dh (find_colliders_in_path (x, v, rev tlx1) G) = Some D).
                     { apply collider_descendants_for_subpath_existence_2 with (u := h) (l1 := rev lx2) (L := L).
                       unfold concat. unfold nodes in *. unfold node in *. simpl in Hlhvrev. rewrite <- Hlhvrev. apply HLh. }
                     destruct HDx as [Dx HDx].
                     assert (HL: exists (L: nodes), get_collider_descendants_from_assignments Dx (find_colliders_in_path (x, v, rev tlx1) G) = Some L).
                     { apply collider_descendants_from_assignments_existence. intros c Hc.
                       assert (Hc': In c (find_colliders_in_path (h, v, lhv) G)).
                       { apply subpath_preserves_colliders with (u := x) (l1 := rev lx2) (l2 := rev tlx1). split. symmetry. apply Hlhvrev. left. apply Hc. }
                       apply HDh in Hc'. destruct Hc' as [Hc' | Hc']. left. apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G).
                       apply HDx. apply Hc'. apply Hc. right. destruct Hc' as [p [d Hc']]. exists p. exists d.
                       apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hc'. apply Hc. }
                     destruct HL as [Lx HLx].

                     assert (Hcycxv: acyclic_path_2 (x, v, rev tlx1)).
                     { apply subpath_still_acyclic with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }

                     assert (Hcyccy: forall (cy dy y: node) (py lcyv1 lcyv2 lcyd1 lcyd2: nodes),
                                  (In dy Z /\
                                   is_directed_path_in_graph (cy, dy, py) G = true /\
                                   acyclic_path_2 (cy, dy, py) /\
                                   overlap (cy :: py) Z = false /\
                                   overlap (py ++ [dy]) (h :: lhv ++ [v]) = false /\
                                   (forall (c' d' : node) (p' : nodes),
                                    (cy =? c') = false /\
                                    get_assigned_value Dh c' = Some (p', d') ->
                                    overlap (cy :: py ++ [dy]) (c' :: p' ++ [d']) = false))
                                  -> lcyv1 ++ [cy] ++ lcyv2 = rev tlx1
                                  -> py ++ [dy] = lcyd1 ++ [y] ++ lcyd2
                                  -> acyclic_path_2 (y, v, rev lcyd1 ++ [cy] ++ lcyv2)
                                     /\ ~In h (rev lcyd1 ++ [cy] ++ lcyv2)).
                     { intros cy dy y py lcyv1 lcyv2 lcyd1 lcyd2 Hpdy'' Hcy Hy'. apply Hcyccy' with (dy := dy) (py := py) (lcyd2 := lcyd2) (lhcy1 := rev lx2 ++ [x] ++ lcyv1).
                       apply Hpdy''. rewrite <- app_assoc. rewrite <- app_assoc. unfold node in *. rewrite Hcy. symmetry. apply Hlhvrev. apply Hy'. }

                     assert (HLcy: forall (cy dy y' w: node) (py: nodes),
                                   In cy (find_colliders_in_path (x, v, rev tlx1) G) /\
                                   get_assigned_value Dx cy = Some (py, dy) /\
                                   (dy =? cy) = false /\ In y' (py ++ [dy])
                                   -> In w (py ++ [dy]) -> In w L).
                     { intros cy dy y' w py Hpdy Hmem.
                       apply collider_descendants_from_assignments_mem with (D := Dh) (p' := (h, v, lhv)) (p := py) (d := dy) (c := cy) (G := G).
                       -- apply subpath_preserves_colliders with (u := x) (l1 := rev lx2) (l2 := rev tlx1). split. symmetry. apply Hlhvrev.
                          left. apply Hpdy.
                       -- split. apply collider_descendants_preserved_for_subpath with (D' := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hpdy. apply Hpdy.
                       -- apply HLh.
                       -- apply Hmem. }

                     assert (HyDcy: forall (py' lcyv2: nodes) (cy dy' y: node) (D Dcy: assignments (nodes * node)), D = (y, (py', dy')) :: Dcy
                                       -> get_collider_descendants_for_subpath Dh (find_colliders_in_path (cy, v, lcyv2) G) = Some Dcy
                                       -> is_exact_assignment_for D (y :: find_colliders_in_path (cy, v, lcyv2) G)).
                     { intros py'' lcyv2 cy dy'' y D Dcy HD HDcy. rewrite HD. apply exact_assignment_cat. apply collider_subpath_is_exact_assignment with (D := Dh). apply HDcy. }


                     destruct (overlap ph1 Lx) as [|] eqn:Hoverph1.
                     { (* CASE 2C.3.i: take ph1 until intersect with desc path, then take that path to collider, then to v *)
                       apply overlap_rev_true in Hoverph1.
                       apply list_has_first_elt_in_common_with_other_list in Hoverph1. destruct Hoverph1 as [ph11' [ph12' [Lx1 [Lx2 [y' Hy]]]]].
                       assert (Hy': exists (c d: node) (p: nodes), In c (find_colliders_in_path (x, v, rev tlx1) G)
                                   /\ get_assigned_value Dx c = Some (p, d) /\ d =? c = false
                                   /\ In y' (p ++ [d])).
                       { apply collider_descendants_from_assignments_belong_to_collider with (L := Lx). apply HLx. apply membership_rev.
                         destruct Hy as [_ [Hy _]]. rewrite Hy. apply membership_append_r. left. reflexivity. }
                       destruct Hy' as [cy [dy [py Hpdy]]].

                       assert (Hcolcy: In cy (find_colliders_in_path (h, v, lhv) G)).
                       { apply subpath_preserves_colliders with (u := x) (l1 := rev lx2) (l2 := rev tlx1). split. symmetry. apply Hlhvrev. left. apply Hpdy. }
                       destruct HDh as [HDh HDh']. apply HDh' in Hcolcy.
                       pose proof Hpdy as Hpdy'. destruct Hpdy' as [_ [Hpdy' _]]. apply collider_descendants_preserved_for_subpath with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G) in Hpdy'.
                       2: { apply HDx. }
                       destruct Hcolcy as [Hcolcy | Hcolcy]. rewrite Hpdy' in Hcolcy. inversion Hcolcy. inversion H. rewrite H5 in Hpdy. destruct Hpdy as [_ [_ [Hpdy _]]]. rewrite eqb_refl in Hpdy. discriminate Hpdy.
                       destruct Hcolcy as [py' [dy' Hpdy'']]. destruct Hpdy'' as [Hpdy''' Hpdy'']. rewrite Hpdy' in Hpdy'''. inversion Hpdy'''. rewrite <- H2 in *. rewrite <- H3 in *. clear Hpdy'''. clear H2. clear H3.

                       assert (Hovery: overlap ph1 (py ++ [dy]) = true).
                       { apply overlap_has_member_in_common. exists y'. split.
                         - destruct Hy as [Hy _]. rewrite Hy. apply membership_append_r. left. reflexivity.
                         - apply Hpdy. }
                       apply list_has_first_elt_in_common_with_other_list in Hovery. destruct Hovery as [ph11 [ph12 [lyd1 [lyd2 [y Hy']]]]].

                       assert (Hcy: In cy (rev tlx1)).
                       { assert (Hpath'': is_path_in_graph (x, v, rev tlx1) G = true).
                         { apply subpath_still_path with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }
                         apply intermediate_node_in_path with (x := cy) in Hpath''. apply Hpath''. right. right. apply Hpdy. }
                       apply membership_splits_list in Hcy. destruct Hcy as [lcyv1 [lcyv2 Hcy]].

                       exists (h :: ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2).

                       assert (Hcychv: acyclic_path_2 (h, v, ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2)).
                       { apply concat_paths_acyclic. split. apply Hlhv. split.
                         - apply subpath_still_acyclic_2 with (v := x) (l2 := ph12) (l3 := ph1). split. symmetry. apply Hy'. apply Hcychx.
                         - apply Hcyccy with (dy := dy) (py := py) (lcyv1 := lcyv1) (lcyd2 := lyd2). apply Hpdy''. apply Hcy. apply Hy'.
                         - split.
                           + apply Hcyccy with (dy := dy) (py := py) (lcyv1 := lcyv1) (lcyd2 := lyd2) (y := y). apply Hpdy''. apply Hcy. apply Hy'.
                           + (* Hx'': ph1 does not intersect lhv after x *)
                             intros Hmem. apply no_overlap_non_member with (x := v) in Hx''. apply Hx''. rewrite Hx.
                             apply membership_append. destruct Hy' as [Hy' _]. rewrite Hy'. apply membership_append. apply Hmem.
                             left. reflexivity.
                         - (* lyd1: Hy'. [cy, lcyv2]: Hx'', ph1 does not intersect lhv after x *)
                           apply no_overlap_non_member. intros w Hw Hw'. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                           + destruct Hy' as [Hph1 [_ Hy']]. apply no_overlap_non_member with (x := w) in Hy'. apply Hy'. rewrite Hph1. apply membership_append. apply Hw'.
                             apply membership_rev. apply Hw.
                           + apply no_overlap_non_member with (x := w) in Hx''. apply Hx''. rewrite Hx. apply membership_append. destruct Hy' as [Hy' _]. rewrite Hy'. apply membership_append. apply Hw'.
                             right. apply membership_rev. rewrite <- Hcy. apply membership_append_r. apply Hw. }

                       assert (Hcycuhv: acyclic_path_2 (u, v, h :: ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2)).
                       { apply acyclic_path_cat_2.
                         apply Hcychv.
                         { (* u not in [ph1,y] b/c cycle. u not in [rev lyd1] b/c HuL. u not in [cy, lcyv2] b/c Hulhv *)
                           intros Hmem. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. rewrite Hmem in Hhu. rewrite eqb_refl in Hhu. discriminate Hhu.
                           rewrite app_comm_cons in Hmem. rewrite app_assoc in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                           - apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                             + rewrite <- append_vs_concat in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                               * apply member_In_equiv_F in Huph. apply Huph. rewrite Hx. apply membership_append. destruct Hy' as [Hy' _]. rewrite Hy'.
                                 rewrite app_assoc. apply membership_append. apply Hmem.
                               * apply member_In_equiv_F in HuL. apply HuL. apply HLcy with (cy := cy) (dy := dy) (y' := y') (py := py). apply Hpdy.
                                 destruct Hy' as [_ [Hy' _]]. rewrite Hy'. rewrite app_assoc. apply membership_append. apply membership_rev. rewrite reverse_list_append. simpl. right. apply Hmem.
                             + apply member_In_equiv_F in Hulhv. apply Hulhv. rewrite Hlhvrev. apply membership_append_r. right. simpl. rewrite <- Hcy. apply membership_append_r. apply Hmem.
                           - destruct Hmem as [Hmem | Hmem]. destruct Hcyc as [Hcyc _]. apply Hcyc. symmetry. apply Hmem. apply Hmem. } }

                       split.
                       { apply Hcycuhv. }

                        assert (Hphv: is_path_in_graph (h, v, ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2) G = true).
                        { apply concat_paths_still_a_path. split.
                          - apply subpath_still_path_2 with (v := x) (l2 := ph12) (l3 := ph1). split. symmetry. apply Hy'.
                            apply directed_path_is_path. simpl in Hdir. apply split_and_true in Hdir. apply Hdir.
                          - apply concat_paths_still_a_path. split.
                            + apply reverse_path_in_graph. apply directed_path_is_path. apply Hpathcy' with (dy := dy) (py := py) (l2 := lyd2).
                              apply Hpdy''. apply Hy'.
                            + apply subpath_still_path with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. symmetry. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy. apply Hlhvrev.
                              apply Hlhv. }

                        assert (Hcymed: In cy (find_mediators_in_path (concat y cy v (rev lyd1) lcyv2) G)).
                        { apply collider_becomes_mediator_when_concat_directed with (x := x) (dy := dy) (txv := rev tlx1) (py := py) (lv1 := lcyv1) (ly2 := lyd2).
                          apply Hpdy. apply Hcy.
                          apply subpath_still_acyclic with (w := h) (l1 := rev lx2) (l3 := lhv). split. simpl in Hcy. symmetry. apply Hlhvrev. apply Hlhv.
                          apply Hy'. apply Hpdy''. }

                        assert (Hycol: In y (find_colliders_in_path (concat h y v ph11 (rev lyd1 ++ [cy] ++ lcyv2)) G)).
                        { apply subpath_preserves_colliders with (u := cy) (l1 := ph11 ++ [y] ++ rev lyd1) (l2 := lcyv2). split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. right.
                          apply intersection_of_directed_paths_is_collider with (d1 := zh) (d2 := dy) (l1 := ph) (l2 := py) (l1'' := ph12 ++ x :: ph2) (l2'' := lyd2). apply Hh'. apply Hpdy''.
                          destruct Hy' as [Hy' _]. rewrite app_assoc. rewrite app_assoc. unfold nodes in *. unfold node in *. rewrite <- app_assoc with (l := ph11). rewrite <- Hy'. apply Hx. apply Hy'. }

                        assert (Hhmed: In h (find_mediators_in_path (u, v, h :: ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2) G)).
                        { assert (Hph: ph ++ [zh] = ph11 ++ [y] ++ (ph12 ++ x :: ph2)). { destruct Hy' as [Hy' _]. rewrite Hx. rewrite Hy'. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
                          apply mediator_means_edge_out with (c := h) (G := G) in Hph.
                          destruct ph11 as [| hph11 tph11].
                          * apply mediators_vs_edges_in_path. exists u. exists y. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                            -- apply Huh.
                            -- destruct Hph as [Hph _]. apply Hph. reflexivity.
                          * apply mediators_vs_edges_in_path. exists u. exists hph11. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                            -- apply Huh.
                            -- destruct Hph as [_ Hph]. apply Hph with (tly1 := tph11). reflexivity.
                          * apply Hh'. }

                        split.
                        { (* h is a mediator and not in Z (HhZ). ph1 directed path. y collider with desc path to dy (already in Dx)
                             lyd1 directed path. cy now mediator, not in Z. everything else same as before *) 
                          apply d_connected_cat. apply HG. apply Hcycuhv.
                          - apply concat_d_connected_paths. apply HG. apply Hphv. split.
                            + apply Hconncy with (p := ph) (l2 := ph12 ++ [x] ++ ph2) (d := zh). destruct Hy' as [Hy' _]. rewrite Hx. rewrite Hy'. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                              split. apply Hh'. split. apply Hh'. apply Hh'.
                            + split.
                              * apply concat_d_connected_paths. apply HG.
                                unfold concat. apply subpath_still_path with (w := h) (l1 := ph11) (l3 := ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2). split. reflexivity. apply Hphv.
                                split.
                                -- apply reverse_d_connected_paths. apply Hconncy with (p := py) (l2 := lyd2) (d := dy). apply Hy'. split. apply Hpdy''. split.
                                   apply overlap_cat with (x := cy). apply Hpdy''. apply Hpdy''.
                                -- split.
                                   ++ apply subpath_still_d_connected_gen with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. symmetry. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy. apply Hlhvrev.
                                      apply Hlhv.
                                   ++ unfold concat. apply subpath_still_acyclic with (w := h) (l1 := ph11) (l3 := ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2). split. reflexivity. apply Hcychv.
                                -- left. apply and_comm. split.
                                   ++ destruct Hpdy'' as [_ [_ [_ [Hpdy'' _]]]]. simpl in Hpdy''. destruct (member cy Z) as [|] eqn:HcyZ. discriminate Hpdy''. apply member_In_equiv_F. apply HcyZ.
                                   ++ apply Hcymed.
                              * apply Hcychv.
                            + right. right. rewrite and_comm. split.
                              * unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists dy. rewrite and_comm. split. apply Hpdy''.
                                apply find_descendants_correct. destruct Hy' as [_ [Hy' _]]. symmetry in Hy'. destruct (rev lyd2) as [| hlyd2 tlyd2] eqn:Hlyd2.
                                -- apply Hl2 in Hy'. left. apply Hy'. apply Hlyd2.
                                -- apply Hl2 in Hy'. right. exists (y, dy, rev tlyd2). split. apply subpath_still_directed with (w := cy) (l1 := lyd1) (l3 := py). split. symmetry. apply Hy' with (hl2 := hlyd2) (tl2 := tlyd2). apply Hlyd2. apply Hpdy''.
                                   apply path_start_end_refl.
                              * apply Hycol.
                          - left. apply and_comm. split.
                            + apply HhZ.
                            + apply Hhmed. }

                        split.
                        { simpl. destruct G as [V E]. rewrite Huh. simpl. apply Hphv. }

                        split.
                        { intros w Hw. (* [h, y): pydy, not in Z. y: either = dy or not in Z. [lyd1]: path in, exists dy, py *)
                          assert (Hwu: w =? u = false). { apply Houtwu with (x' := v) (l1 := ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2) (l2 := t). apply Hw. }

                          assert (Hwv: w =? v = false). { apply Houtwv with (x' := u) (l1 := h :: ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2) (l2 := h :: t).
                            apply Hcyc. apply Hw. }
                          rewrite <- node_in_path_cat in Hw. rewrite <- node_in_path_cat in Hw. 2: { apply Hwu. } 2: { apply Hwu. }
                          rewrite path_out_of_node_cat. 2: { apply Hwu. }

                          destruct (w =? h) as [|] eqn:Hwh.
                          - apply eqb_eq in Hwh. rewrite Hwh. split.
                            + left. exists zh. exists ph. split. apply Hh'. split. apply Hh'. apply HhZ.
                            + intros H. apply HhZ.
                          - destruct (member w ph11) as [|] eqn:Hwph1.
                            + assert (Houtph1: path_out_of_node w (h, v, ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2) G = path_out_of_node w (u, x, h :: ph1) G).
                              { rewrite path_out_of_node_cat. 2: { apply Hwu. } assert (exists (b: bool), path_out_of_node w (h, x, ph1) G = Some b).
                                { apply path_out_of_node_mem_2. right. destruct Hy' as [Hy' _]. rewrite Hy'. apply membership_append. apply member_In_equiv. apply Hwph1. }
                                destruct H as [bw Hbw]. unfold nodes in *. unfold node in *. rewrite Hbw. apply subpath_preserves_path_out_of_node_2 with (u := y) (l1 := ph11) (l2 := rev lyd1 ++ [cy] ++ lcyv2). split. reflexivity.
                                apply superpath_preserves_path_out_of_node_2 with (v := x) (l2 := ph12) (l3 := ph1). symmetry. apply Hy'. apply Hbw. right. apply member_In_equiv. apply Hwph1. }
                              unfold nodes in *. unfold node in *. rewrite Houtph1. apply Houtwph1 with (ph2' := ph2). destruct Hy' as [Hy' _]. rewrite Hy'. apply membership_append. apply member_In_equiv. apply Hwph1. apply Hx.
                            + destruct (member w (y :: rev lyd1)) as [|] eqn:Hwy.
                              * apply member_In_equiv in Hwy.
                                assert (Houtw: path_out_of_node w (h, v, ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2) G = path_out_of_node w (y, cy, rev lyd1) G).
                                { assert (Hwlp1: exists (b: bool), path_out_of_node w (y, cy, rev lyd1) G = Some b). { apply path_out_of_node_mem_2. apply Hwy. }
                                  destruct Hwlp1 as [bw Hbw]. rewrite Hbw. apply subpath_preserves_path_out_of_node with (u := y) (l1 := ph11) (l2 := rev lyd1 ++ [cy] ++ lcyv2). split. reflexivity.
                                  apply subpath_preserves_path_out_of_node_2 with (u := cy) (l1 := rev lyd1) (l2 := lcyv2). split. reflexivity. apply Hbw.
                                  apply Hcychv. }
                                unfold nodes in *. unfold node in *. rewrite Houtw. apply Houtw_revdir with (d := dy) (lyc2 := lyd2) (p := py). apply Hwy. symmetry. apply Hy'. repeat split; apply Hpdy''.
                                apply Hpathcy' with (dy := dy) (py := py) (l2 := lyd2). apply Hpdy''. apply Hy'.
                              * assert (Hwcy: In w (cy :: lcyv2)).
                                { assert (Hwmem: In w (u :: h :: ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2)).
                                  { destruct Hw as [[Hw _] | Hw].
                                    - rewrite node_in_path_equiv in Hw. right. apply member_In_equiv in Hw. rewrite app_comm_cons in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                      apply Hw. destruct Hw as [Hw | Hw]. rewrite Hw in Hwv. rewrite eqb_refl in Hwv. discriminate Hwv. exfalso. apply Hw.
                                    - destruct Hw as [bw [_ Hw]]. apply path_out_of_node_mem_gen with (G := G) (v := v). exists (negb bw). apply Hw. }
                                  apply member_In_equiv in Hwmem. simpl in Hwmem. rewrite eqb_sym in Hwmem. rewrite Hwu in Hwmem. rewrite eqb_sym in Hwmem. rewrite Hwh in Hwmem.
                                  apply member_In_equiv in Hwmem. apply membership_append_or in Hwmem. destruct Hwmem as [Hwmem | Hwmem]. apply member_In_equiv in Hwmem. rewrite Hwmem in Hwph1. discriminate Hwph1.
                                  rewrite app_comm_cons in Hwmem. apply membership_append_or in Hwmem. destruct Hwmem as [Hwmem | Hwmem]. apply member_In_equiv in Hwmem. rewrite Hwmem in Hwy. discriminate Hwy.
                                  apply Hwmem. }
                                assert (Hwlhv: path_out_of_node w (h, v, ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2) G = path_out_of_node w (h, v, lhv) G).
                                { assert (exists (b: bool), path_out_of_node w (h, v, lhv) G = Some b).
                                  { apply path_out_of_node_mem_gen. right. rewrite Hlhvrev. rewrite <- Hcy. apply membership_append_r. right. apply membership_append_r. apply membership_append_r. apply Hwcy. }
                                  destruct H as [bw Hb]. rewrite Hb.
                                  apply subpath_preserves_path_out_of_node with (u := cy) (l1 := ph11 ++ [y] ++ rev lyd1) (l2 := lcyv2). split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                                  - apply superpath_preserves_path_out_of_node with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). rewrite Hlhvrev. rewrite <- Hcy. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                                    apply Hb. apply Hlhv. apply Hwcy.
                                  - apply Hcychv. }
                                  unfold nodes in *. unfold node in *. rewrite Hwlhv. apply Hout.
                                  destruct Hw as [Hw | Hw].
                                  -- left. split.
                                     ++ rewrite node_in_path_equiv. apply member_In_equiv. right. apply membership_append. rewrite Hlhvrev. apply membership_append_r. right. rewrite <- Hcy. simpl. apply membership_append_r. apply Hwcy.
                                     ++ rewrite node_in_path_equiv. destruct Hw as [_ Hw]. rewrite node_in_path_equiv in Hw. simpl in Hw. apply Hw.
                                  -- right. destruct Hw as [bw [Hb1 Hb2]]. exists bw. split.
                                     ++ rewrite <- path_out_of_node_cat with (u := u). apply Hb1. apply Hwu.
                                     ++ rewrite <- Hwlhv. rewrite <- path_out_of_node_cat with (u := u). apply Hb2. apply Hwu. }

                        assert (HDcy: exists (D: assignments (nodes * node)), get_collider_descendants_for_subpath Dh (find_colliders_in_path (cy, v, lcyv2) G) = Some D).
                        { apply collider_descendants_for_subpath_existence_2 with (u := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (L := L).
                          unfold concat. rewrite <- app_assoc. rewrite <- app_assoc. rewrite app_assoc. simpl in Hcy. unfold nodes in *. unfold node in *. rewrite Hcy. rewrite <- app_assoc. rewrite <- Hlhvrev. apply HLh. }
                        destruct HDcy as [Dcy HDcy].

                        assert (Hcolhv: find_colliders_in_path (u, v, h :: ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2) G = y :: (find_colliders_in_path (cy, v, lcyv2) G)).
                        { assert (Hcoluv: [] ++ h :: ph11 ++ [y] ++ (rev lyd1 ++ [cy] ++ lcyv2) = h :: ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2).
                          { reflexivity. }
                          apply subpath_preserves_colliders_2 with (w := u) (v := v) (G := G) in Hcoluv. destruct Hcoluv as [Hcoluv | Hcoluv].
                          - (* h is a mediator, not a collider *)
                            apply if_mediator_then_not_confounder_path in Hhmed. exfalso. destruct Hhmed as [_ Hhmed]. apply Hhmed. unfold concat. unfold nodes in *.
                            unfold node in *. simpl in Hcoluv. simpl. rewrite Hcoluv. left. reflexivity. apply HG. apply Hcycuhv.
                          - unfold nodes in *. rewrite Hcoluv.

                            assert (Hcolhv: ph11 ++ [y] ++ (rev lyd1 ++ [cy] ++ lcyv2) = ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2).
                            { reflexivity. }
                            assert (Hcoluy: find_colliders_in_path (u, y, h :: ph11) G = []). { apply Hcolph1 with (ph2' := ph12 ++ [x] ++ ph2). destruct Hy' as [Hy' _]. rewrite Hx. rewrite Hy'. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
                            assert (Hcolhy: find_colliders_in_path (h, y, ph11) G = []). { destruct (find_colliders_in_path (h, y, ph11) G) as [| ch ct] eqn:Hhy. reflexivity.
                              assert (Hch: In ch (find_colliders_in_path (u, y, h :: ph11) G)). { apply subpath_preserves_colliders with (u := h) (l1 := []) (l2 := ph11). split. reflexivity. left. simpl. simpl in Hhy. rewrite Hhy. left. reflexivity. }
                              rewrite Hcoluy in Hch. exfalso. apply Hch. }

                            apply subpath_preserves_colliders_2 with (w := h) (u := y) (v := v) (G := G) in Hcolhv. destruct Hcolhv as [Hcolhv | Hcolhv].
                            + unfold nodes in *. rewrite Hcolhv. unfold node in *. rewrite Hcolhy.
                              assert (Hcolyv: rev lyd1 ++ [cy] ++ lcyv2 = rev lyd1 ++ [cy] ++ lcyv2). { reflexivity. } apply subpath_preserves_colliders_2 with (w := y) (v := v) (G := G) in Hcolyv.
                              assert (Hcolycy: find_colliders_in_path (y, cy, rev lyd1) G = []). { apply Hcoldir with (d := dy) (p' := py) (p2' := lyd2). apply Hy'. apply Hpdy''. apply Hpdy''. }
                              unfold nodes in *. unfold node in *. rewrite Hcolycy in *. destruct Hcolyv as [Hcolyv | Hcolyv].
                              * (* cy is a mediator, not a collider *)
                                apply if_mediator_then_not_confounder_path in Hcymed. exfalso. destruct Hcymed as [_ Hcymed]. apply Hcymed. unfold concat. unfold nodes in *.
                                unfold node in *. simpl in Hcolyv. simpl. rewrite Hcolyv. left. reflexivity. apply HG. unfold concat. apply subpath_still_acyclic with (w := h) (l1 := ph11) (l3 := ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2).
                                split. reflexivity. apply Hcychv.
                              * rewrite Hcolyv. simpl. reflexivity.
                            + (* y is a collider, so should be included in Hcolhv *)
                              unfold concat in Hycol.
                              unfold nodes in *. unfold node in *. rewrite <- append_vs_concat in Hycol. rewrite <- app_assoc in Hycol. rewrite Hcolhv in Hycol. apply membership_append_or in Hycol.
                              destruct Hycol as [Hycol | Hycol]. (* contradicts acyclic *)
                              * assert (Hphy: is_path_in_graph (h, y, ph11) G = true). { apply subpath_still_path_2 with (v := v) (l2 := rev lyd1 ++ [cy] ++ lcyv2) (l3 := ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2).
                                  split. reflexivity. apply Hphv. } apply intermediate_node_in_path with (x := y) in Hphy.
                                assert (Hyph11: In y ph11). { apply Hphy. right. right. apply Hycol. }
                                assert (Hchy: acyclic_path_2 (h, y, ph11)). { apply subpath_still_acyclic_2 with (v := v) (l2 := rev lyd1 ++ [cy] ++ lcyv2) (l3 := ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2).
                                  split. reflexivity. apply Hcychv. } exfalso. destruct Hchy as [_ [_ [Hchy _]]]. apply Hchy. apply Hyph11.
                              * assert (Hphy: is_path_in_graph (y, v, rev lyd1 ++ [cy] ++ lcyv2) G = true). { apply subpath_still_path with (w := h) (l1 := ph11) (l3 := ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2).
                                  split. reflexivity. apply Hphv. } apply intermediate_node_in_path with (x := y) in Hphy.
                                assert (Hyph11: In y (rev lyd1 ++ [cy] ++ lcyv2)). { apply Hphy. right. right. apply Hycol. }
                                assert (Hchy: acyclic_path_2 (y, v, rev lyd1 ++ [cy] ++ lcyv2)). { apply subpath_still_acyclic with (w := h) (l1 := ph11) (l3 := ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2).
                                  split. reflexivity. apply Hcychv. } exfalso. destruct Hchy as [_ [Hchy _]]. apply Hchy. apply Hyph11. }

                        unfold nodes in *. rewrite Hcolhv.

                        assert (HyDcy': forall (py': nodes) (dy': node) (D: assignments (nodes * node)), D = (y, (py', dy')) :: Dcy
                                       -> forall c : node,
                                          (c =? y) = false
                                           -> In c (y :: find_colliders_in_path (cy, v, lcyv2) G)
                                           -> get_assigned_value D c = Some ([], c) /\ In c Z \/
                                               (exists (p : list node) (d : node),
                                                  get_assigned_value D c = Some (p, d) /\
                                                  In d Z /\
                                                  is_directed_path_in_graph (c, d, p) G = true /\
                                                  acyclic_path_2 (c, d, p) /\
                                                  overlap (c :: p) Z = false /\
                                                  overlap (p ++ [d])
                                                    (u :: (h :: ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2) ++ [v]) =
                                                  false /\ overlap (c :: p ++ [d]) (cy :: py ++ [dy]) = false
                                                  /\ (forall (c' d' : node) (p' : list node),
                                                     (c =? c') = false /\ get_assigned_value Dcy c' = Some (p', d') ->
                                                     overlap (c :: p ++ [d]) (c' :: p' ++ [d']) = false))).
                        { intros py'' dy'' D HDeq c Hyc Hc.
                          destruct Hc as [Hc | Hc]. rewrite Hc in Hyc. rewrite eqb_refl in Hyc. discriminate Hyc.
                          (* induction case *) assert (Hc': In c (find_colliders_in_path (h, v, lhv) G)).
                          { apply subpath_preserves_colliders with (u := cy) (l1 := rev lx2 ++ [x] ++ lcyv1) (l2 := lcyv2). split. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy. symmetry. apply Hlhvrev. left. apply Hc. }
                          pose proof Hc' as Hc''. apply HDh' in Hc'. rewrite HDeq in *. destruct Hc' as [Hc' | Hc'].
                          -- left. split. simpl. rewrite eqb_sym. rewrite Hyc. rewrite <- collider_descendants_preserved_for_subpath_3 with (D := Dh) (col := find_colliders_in_path (cy, v, lcyv2) G).
                             apply Hc'. apply HDcy. apply Hc. apply Hc'.
                          -- right. destruct Hc' as [pc [dc Hc']]. exists pc. exists dc. split. simpl. rewrite eqb_sym. rewrite Hyc. simpl. rewrite <- collider_descendants_preserved_for_subpath_3 with (D := Dh) (col := find_colliders_in_path (cy, v, lcyv2) G).
                             apply Hc'. apply HDcy. apply Hc. split. apply Hc'. split. apply Hc'. split. apply Hc'. split. apply Hc'.
                             assert (Hovercy: overlap (c :: pc ++ [dc]) (cy :: py ++ [dy]) = false).
                             { apply Hc'. rewrite and_comm. split. apply collider_descendants_preserved_for_subpath with (D' := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hpdy.
                               destruct (c =? cy) as [|] eqn:Hccy. exfalso. apply eqb_eq in Hccy.
                               assert (Hmemcy: In cy lcyv2).
                               { assert (Hpcy: is_path_in_graph (cy, v, lcyv2) G = true).
                                 { apply subpath_still_path with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy. symmetry. apply Hlhvrev. apply Hlhv. }
                                 apply intermediate_node_in_path with (x := cy) in Hpcy. apply Hpcy. right. right. rewrite <- Hccy in *. apply Hc. }
                               assert (Hccy': acyclic_path_2 (cy, v, lcyv2)).
                               { apply subpath_still_acyclic with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy. symmetry. apply Hlhvrev. apply Hlhv. }
                               destruct Hccy' as [_ [Hccy' _]]. apply Hccy'. apply Hmemcy. reflexivity. }

                             repeat split.
                             ++ (* u: HuL. h: HDh'. ph11: Hy. [u, lyd1]: HDh' (desc path of cy). [cy, v]: HDh'. *) apply no_overlap_non_member. intros w Hw Hw'.
                                assert (HwL: In w L).
                                { apply collider_descendants_from_assignments_mem with (D := Dh) (G := G) (p' := (h, v, lhv)) (p := pc) (d := dc) (c := c). apply Hc''. split. apply Hc'.
                                  destruct (dc =? c) as [|] eqn:Hdcc. apply eqb_eq in Hdcc. destruct Hc' as [_ [_ [_ [[Hc' _] _]]]]. exfalso. apply Hc'. symmetry. apply Hdcc. reflexivity.
                                  apply HLh. apply Hw'. }
                                destruct Hw as [Hw | Hw].
                                { apply member_In_equiv_F in HuL. apply HuL. rewrite Hw. apply HwL. } destruct Hw as [Hw | Hw].
                                { destruct Hc' as [_ [_ [_ [_ [_ [Hc' _]]]]]]. apply no_overlap_non_member with (x := h) in Hc'. apply Hc'. rewrite Hw. apply Hw'. left. reflexivity. }
                                rewrite <- app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                { (* w is in Lx. (py ++ [dy]) comes before (pc ++ [dc]) in Lx, since cy comes before c. Then, y' comes before w, so w in Lx1 *)
                                  (* Hy -> ph11' and Lx1 have no overlap. ph11 is a prefix of ph11' because y is first intersection point of ph1 and (py,dy) (Hy') *)
                                  (* Thus ph11 and Lx1 have no overlap, contradiction *)
                                  assert (HLxy: exists (l1' l2' l3': nodes), Lx = l1' ++ py ++ [dy] ++ l2' ++ pc ++ [dc] ++ l3').
                                  { apply get_collider_descendants_from_assignments_preserves_order with (D := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G) (c1 := cy) (c2 := c).
                                    apply HLx. split. apply Hpdy. rewrite eqb_sym. apply Hpdy. split.
                                    - apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hc'. rewrite <- Hcy. apply subpath_preserves_colliders with (u := cy) (l1 := lcyv1) (l2 := lcyv2). split. reflexivity. left. apply Hc.
                                    - apply eqb_neq. destruct Hc' as [_ [_ [_ [[Hc' _] _]]]]. apply Hc'.
                                    - pose proof Hcy as Hcy'. apply subpath_preserves_colliders_2 with (w := x) (v := v) (G := G) in Hcy. destruct Hcy as [Hcy | Hcy].
                                      + exists (find_colliders_in_path (x, cy, lcyv1) G). unfold nodes in *. unfold node in *. rewrite Hcy.
                                        apply membership_splits_list in Hc. destruct Hc as [lc1 [lc2 Hc]]. exists lc1. exists lc2. rewrite Hc. reflexivity.
                                      + (* contradiction in Hcy, since cy is a collider *) exfalso. destruct Hpdy as [Hpdy _]. unfold nodes in *. unfold node in *. rewrite Hcy in Hpdy. apply membership_append_or in Hpdy.
                                        destruct Hpdy as [Hpdy | Hpdy].
                                        * assert (HcyF: In cy lcyv1). { assert (Hcyp: is_path_in_graph (x, cy, lcyv1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := lcyv2) (l3 := rev tlx1). split. apply Hcy'.
                                            apply subpath_still_path with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }
                                            apply intermediate_node_in_path with (x := cy) in Hcyp. apply Hcyp. right. right. apply Hpdy. }
                                          assert (Hcycyc: acyclic_path_2 (x, cy, lcyv1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := lcyv2) (l3 := rev tlx1). split. apply Hcy'. apply Hcycxv. }
                                          destruct Hcycyc as [_ [_ [Hcycyc _]]]. apply Hcycyc. apply HcyF.
                                        * assert (HcyF: In cy lcyv2). { assert (Hcyp: is_path_in_graph (cy, v, lcyv2) G = true). { apply subpath_still_path with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy'.
                                            symmetry. apply Hlhvrev. apply Hlhv. }
                                            apply intermediate_node_in_path with (x := cy) in Hcyp. apply Hcyp. right. right. apply Hpdy. }
                                          assert (Hcycyc: acyclic_path_2 (cy, v, lcyv2)). { apply subpath_still_acyclic with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy'.
                                            symmetry. apply Hlhvrev. apply Hlhv. }
                                          destruct Hcycyc as [_ [Hcycyc _]]. apply Hcycyc. apply HcyF. }

                                  destruct Hpdy as [_ [_ [_ Hpdy]]]. apply membership_splits_list in Hpdy. destruct Hpdy as [ly1' [ly2' Hpdy]]. destruct HLxy as [Lx1' [Lx2' [Lx3' HLxy]]]. unfold nodes in *. unfold node in *. simpl in Hpdy. rewrite app_assoc in HLxy. rewrite app_assoc in HLxy. rewrite <- app_assoc with (l := Lx1') in HLxy. rewrite <- Hpdy in HLxy.
                                  assert (Hcounty: count y' Lx = 1).
                                  { apply get_collider_descendants_from_assignments_preserves_count with (D := Dx) (G := G) (Z := Z) (u := x) (v := v) (l' := rev tlx1).
                                    2: { apply HLx. } 2: { apply subpath_still_acyclic with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }
                                    2: { apply subpath_still_path with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }
                                    2: { rewrite HLxy. apply membership_append. apply membership_append_r. apply membership_append_r. left. reflexivity. }
                                    apply descendant_paths_disjoint_subpath with (Dh := Dh) (h := h) (l1 := rev lx2) (lhv := lhv). split. apply HDh. apply HDh'. apply HDx. apply Hlhvrev. }

                                  assert (HLx1: rev Lx1 = ly2' ++ Lx2' ++ pc ++ dc :: Lx3').
                                  { apply two_sublists_the_same_gen with (l := Lx) (a := y') (l1 := rev Lx2) (l1' := Lx1' ++ ly1'). destruct Hy as [_ [Hy _]].
                                    rewrite reverse_list_twice with (l := Lx). rewrite Hy. rewrite reverse_list_append. simpl. rewrite <- app_assoc. reflexivity.
                                    rewrite <- app_assoc in HLxy. rewrite <- app_assoc in HLxy. rewrite <- app_assoc. simpl in HLxy. apply HLxy. apply Hcounty. }
                                  assert (HwLx1: In w Lx1). { apply membership_rev. rewrite HLx1. apply membership_append_r. apply membership_append_r. rewrite <- append_vs_concat. apply membership_append. apply Hw'. }

                                  destruct Hy as [_ [_ Hy]]. apply no_overlap_non_member with (x := w) in Hy. apply Hy.
                                  destruct Hy' as [Hy' _]. rewrite Hy'. apply membership_append. apply Hw. apply HwLx1. }

                                rewrite <- app_assoc in Hw. rewrite <- app_assoc in Hw. rewrite app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                { destruct Hc' as [_ [_ [_ [_ [_ [_ Hc']]]]]]. specialize Hc' with (c' := cy) (d' := dy) (p' := py).
                                  apply no_overlap_non_member with (x := w) in Hovercy. apply Hovercy. right. apply Hw'. right. destruct Hy' as [_ [Hy' _]]. rewrite Hy'. rewrite app_assoc. apply membership_append.
                                  apply membership_rev. rewrite reverse_list_append. apply Hw. }
                                { destruct Hc' as [_ [_ [_ [_ [_ [Hc' _]]]]]]. apply no_overlap_non_member with (x := w) in Hc'. apply Hc'. apply Hw'. right. rewrite Hlhvrev. rewrite <- app_assoc. apply membership_append_r. rewrite <- Hcy. rewrite <- app_assoc. rewrite <- app_assoc. right.
                                  simpl. apply membership_append_r. apply Hw. }
                             ++ apply Hovercy.
                             ++ intros c' d' p' [Hcc' Hcdp'].
                                apply Hc'. split. apply Hcc'. apply collider_descendants_preserved_for_subpath with (D' := Dcy) (col := find_colliders_in_path (cy, v, lcyv2) G). apply HDcy. apply Hcdp'. }


                        (* destruct on y = dy or not *) destruct (rev lyd2) as [| hy ty] eqn:Hlyd2.
                        - exists ((y, ([], y)) :: Dcy). split.
                          + apply HyDcy with (py' := []) (dy' := y) (Dcy := Dcy). reflexivity. apply HDcy.
                          + intros c Hc. destruct (c =? y) as [|] eqn:Hyc.
                            * apply eqb_eq in Hyc. left. split. simpl. rewrite Hyc. rewrite eqb_refl. reflexivity. rewrite Hyc. destruct Hy' as [_ [Hy' _]]. symmetry in Hy'. apply Hl2 in Hy'.
                              apply Hy' in Hlyd2. destruct Hlyd2 as [Hlyd2 _]. rewrite Hlyd2. apply Hpdy''.
                            * unfold nodes in *. rewrite Hcolhv in Hc. destruct Hc as [Hc | Hc]. rewrite Hc in Hyc. rewrite eqb_refl in Hyc. discriminate Hyc.

                              apply HyDcy' with (D := (y, ([], y)) :: Dcy) (py' := []) (dy' := y) in Hyc.
                              -- destruct Hyc as [Hyc | Hyc]. left. apply Hyc. right. destruct Hyc as [pc [dc Hyc]]. exists pc. exists dc.

                                 rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split. repeat split; apply Hyc.
                                 intros c' d' p' [Hcc' Hcdp']. simpl in Hcdp'. destruct (y =? c') as [|] eqn:Hyc'.
                                 ** inversion Hcdp'. rewrite <- H3. apply eqb_eq in Hyc'. rewrite <- Hyc'. simpl. (* y is original member of cy's desc path, so doesn't overlap c's desc path (HDh') *)
                                    rewrite <- Hyc' in Hcc'. rewrite eqb_sym in Hcc'. rewrite Hcc'. apply overlap_flip. simpl.
                                    assert (Hmemy: ~In y (pc ++ [dc])).
                                    { intros F. destruct Hyc as [_ [_ [_ [_ [_ [_ [Hovercy _]]]]]]]. apply no_overlap_non_member with (x := y) in Hovercy. apply Hovercy. right. apply F. right.
                                      destruct Hy' as [_ [Hy' _]]. rewrite Hy'. apply membership_append_r. left. reflexivity. }
                                    apply member_In_equiv_F in Hmemy. rewrite Hmemy. reflexivity.
                                 ** apply Hyc. split. apply Hcc'. apply Hcdp'.
                              -- reflexivity.
                              -- right. apply Hc.

                        - destruct Hy' as [Hy'' [Hy' Hovery']]. symmetry in Hy'. apply Hl2 in Hy'. apply Hy' in Hlyd2. exists ((y, (rev ty, dy)) :: Dcy). split.
                          + apply HyDcy with (py' := rev ty) (dy' := dy) (Dcy := Dcy). reflexivity. apply HDcy.
                          + intros c Hc.
                            assert (Hwmempy: forall (w: node), In w (rev ty ++ [dy]) -> In w (py ++ [dy])).
                            { intros w Hw. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2. rewrite <- app_assoc. apply membership_append_r. simpl. right. apply Hw. }

                            destruct (c =? y) as [|] eqn:Hyc.
                            * apply eqb_eq in Hyc. right. exists (rev ty). exists dy. split.
                              { simpl. rewrite Hyc. rewrite eqb_refl. simpl. reflexivity. }
                              split. apply Hpdy''. split.
                              { apply subpath_still_directed with (w := cy) (l1 := lyd1) (l3 := py). split. rewrite Hyc. symmetry. apply Hlyd2. apply Hpdy''. } split.
                              { apply subpath_still_acyclic with (w := cy) (l1 := lyd1) (l3 := py). split. rewrite Hyc. symmetry. apply Hlyd2. apply Hpdy''. } split.
                              { apply no_overlap_non_member. intros w Hw Hw'. destruct Hpdy'' as [_ [_ [_ [Hpdy'' _]]]]. apply no_overlap_non_member with (x := w) in Hpdy''.
                                apply Hpdy''. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2. right. apply membership_append_r. rewrite <- Hyc. apply Hw'. apply Hw. } split.
                              { (* u: HuL. h: Hpdy''. ph11: Hy. [y, lyd, cy]: acyclic Hpdy''. [lcyv2, v]: Hpdy''. *)
                                apply no_overlap_non_member. intros w Hw Hw'.
                                assert (HwL: In w L).
                                { apply collider_descendants_from_assignments_mem with (D := Dh) (G := G) (p' := (h, v, lhv)) (p := py) (d := dy) (c := cy).
                                  - apply subpath_preserves_colliders with (u := x) (l1 := rev lx2) (l2 := rev tlx1). split. symmetry. apply Hlhvrev. left. apply Hpdy.
                                  - split. apply collider_descendants_preserved_for_subpath with (D' := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hpdy. apply Hpdy.
                                  - apply HLh.
                                  - apply Hwmempy. apply Hw'. }
                                destruct Hw as [Hw | Hw].
                                { apply member_In_equiv_F in HuL. apply HuL. rewrite Hw. apply HwL. } destruct Hw as [Hw | Hw].
                                { destruct Hpdy'' as [_ [_ [_ [_ [Hc' _]]]]]. apply no_overlap_non_member with (x := h) in Hc'. apply Hc'. rewrite Hw.
                                  apply Hwmempy. apply Hw'. left. reflexivity. }

                                rewrite <- app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                { (* cycle! w ->...ph11...->y->...py...->w *)
                                  apply membership_splits_list in Hw. destruct Hw as [l1 [l2 Hw]]. apply membership_splits_list in Hw'. destruct Hw' as [l3 [l4 Hw']].
                                  assert (Hcycle: is_directed_path_in_graph (w, w, l2 ++ [y] ++ l3) G = true).
                                  { apply concat_directed_paths. split.
                                    - apply subpath_still_directed with (w := h) (l1 := l1) (l3 := ph11). split. apply Hw. apply Hpathcy' with (dy := zh) (py := ph) (l2 := ph12 ++ [x] ++ ph2).
                                      apply Hh'. unfold nodes in *. unfold node in *. rewrite Hx. rewrite Hy''. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                                    - apply subpath_still_directed with (w := cy) (l1 := lyd1) (l3 := lyd1 ++ [y] ++ l3). split. reflexivity.
                                      apply Hpathcy' with (dy := dy) (py := py) (l2 := l4). apply Hpdy''. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2. rewrite <- app_assoc. rewrite <- app_assoc.
                                      unfold nodes in *. unfold node in *. rewrite <- Hw'. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
                                  destruct HG as [_ HG]. apply contains_cycle_false_correct with (p := (w, w, l2 ++ [y] ++ l3)) in HG. destruct HG as [HG _]. apply HG. reflexivity.
                                  apply Hcycle. }

                                rewrite <- app_assoc in Hw. rewrite <- app_assoc in Hw. rewrite app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                { destruct Hpdy'' as [_ [_ [Hpdy'' _]]]. apply acyclic_path_count with (x := w) in Hpdy''. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2 in Hpdy''.
                                  apply membership_rev in Hw. simpl in Hw. rewrite <- reverse_list_twice in Hw. apply member_count_at_least_1 in Hw. apply member_count_at_least_1 in Hw'.
                                  rewrite <- app_assoc in Hpdy''. rewrite <- app_assoc in Hpdy''. rewrite app_assoc in Hpdy''. simpl in Hpdy''. unfold nodes in *. unfold node in *. destruct (cy =? w) as [|]. rewrite count_app in Hpdy''. lia. rewrite count_app in Hpdy''. lia.
                                  right. apply Hwmempy. apply Hw'. }
                                { destruct Hpdy'' as [_ [_ [_ [_ [Hc' _]]]]]. apply no_overlap_non_member with (x := w) in Hc'. apply Hc'. apply Hwmempy. apply Hw'.
                                  right. rewrite Hlhvrev. rewrite <- app_assoc. apply membership_append_r. rewrite <- Hcy. rewrite <- app_assoc. rewrite <- app_assoc. right.
                                  simpl. apply membership_append_r. apply Hw. } }

                              { intros c' d' p'. intros [Hcc' Hcdp']. simpl in Hcdp'. rewrite <- Hyc in Hcdp'. rewrite Hcc' in Hcdp'.
                                apply no_overlap_non_member. intros w Hw Hw'.
                                assert (Hc': In c' (find_colliders_in_path (cy, v, lcyv2) G)).
                                { apply collider_subpath_is_exact_assignment in HDcy. unfold is_exact_assignment_for in HDcy.
                                  destruct (member c' (find_colliders_in_path (cy, v, lcyv2) G)) as [|] eqn:Hmem. apply member_In_equiv. apply Hmem.
                                  apply HDcy in Hmem. apply assigned_is_false in Hmem. unfold nodes in *. rewrite Hmem in Hcdp'. discriminate Hcdp'. }
                                rewrite eqb_sym in Hcc'. rewrite Hyc in Hcc'. pose proof Hcc' as Hyc'. apply HyDcy' with (py' := rev ty) (dy' := dy) (D := (y, (rev ty, dy)) :: Dcy) in Hcc'.
                                - destruct Hcc' as [Hcc' | Hcc'].
                                  + simpl in Hcc'. rewrite eqb_sym in Hyc'. rewrite Hyc' in Hcc'. destruct Hcc' as [Hcc' _]. unfold nodes in *. rewrite Hcc' in Hcdp'. inversion Hcdp'.
                                    rewrite <- H3 in Hw. rewrite <- H2 in Hw. (* w = c', so py/dy path overlaps with lhv, contradicts Hpdy'' *)
                                    assert (Hwc': c' = w). { simpl in Hw. destruct Hw as [Hw | [Hw | Hw]]. apply Hw. apply Hw. exfalso. apply Hw. }
                                    destruct Hw' as [Hw' | Hw'].
                                    * rewrite <- Hyc in Hyc'. rewrite Hw' in Hyc'. rewrite Hwc' in Hyc'. rewrite eqb_refl in Hyc'. discriminate Hyc'.
                                    * destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := w) in Hpdy''. apply Hpdy''.
                                      apply Hwmempy. apply Hw'.
                                      assert (Hmemc': In c' lcyv2).
                                      { assert (Hpcyv: is_path_in_graph (cy, v, lcyv2) G = true). { apply subpath_still_path with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite <- app_assoc. rewrite <- app_assoc.
                                          unfold nodes in *. unfold node in *. rewrite Hcy. symmetry. apply Hlhvrev. apply Hlhv. }
                                        apply intermediate_node_in_path with (x := c') in Hpcyv. apply Hpcyv. right. right. apply Hc'. }
                                      rewrite <- Hwc'. right. apply membership_append. rewrite Hlhvrev. apply membership_append_r. simpl. right. rewrite <- Hcy.
                                      apply membership_append_r. simpl. right. apply Hmemc'.
                                  + destruct Hcc' as [p'' [d'' [Hcdp'' Hcc']]]. simpl in Hcdp''. rewrite eqb_sym in Hyc'. rewrite Hyc' in Hcdp''. unfold nodes in *. rewrite Hcdp'' in Hcdp'.
                                    inversion Hcdp'. rewrite H2 in *. rewrite H3 in *. destruct Hcc' as [_ [_ [_ [_ [_ [Hcc' _]]]]]]. apply no_overlap_non_member with (x := w) in Hcc'.
                                    apply Hcc'. apply Hw. right. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2. rewrite <- app_assoc. apply membership_append_r. rewrite <- Hyc. apply Hw'.
                                - reflexivity.
                                - right. apply Hc'. }

                            * unfold nodes in *. rewrite Hcolhv in Hc. destruct Hc as [Hc | Hc]. rewrite Hc in Hyc. rewrite eqb_refl in Hyc. discriminate Hyc.

                              apply HyDcy' with (D := (y, (rev ty, dy)) :: Dcy) (py' := rev ty) (dy' := dy) in Hyc.
                              -- destruct Hyc as [Hyc | Hyc]. left. apply Hyc. right. destruct Hyc as [pc [dc Hyc]]. exists pc. exists dc.

                                 rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split. repeat split; apply Hyc.
                                 intros c' d' p' [Hcc' Hcdp']. simpl in Hcdp'. destruct (y =? c') as [|] eqn:Hyc'.
                                 ** inversion Hcdp'. rewrite <- H3. apply eqb_eq in Hyc'. rewrite <- Hyc'.
                                    apply no_overlap_non_member. intros w Hw Hw'. destruct Hyc as [_ [_ [_ [_ [_ [_ [Hyc _]]]]]]].
                                    apply no_overlap_non_member with (x := w) in Hyc. apply Hyc. apply Hw'. right. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2.
                                    rewrite <- app_assoc. apply membership_append_r. apply Hw.
                                 ** apply Hyc. split. apply Hcc'. apply Hcdp'.
                              -- reflexivity.
                              -- right. apply Hc. }

                     destruct ((negb b) && (negb (eqblist ph2 [])) && overlap ph2 Lx) as [|] eqn:HbLx.
                     * (* CASE 2C.3.ii *) apply split_and_true in HbLx. destruct HbLx as [Hb Hoverx]. apply split_and_true in Hb. destruct Hb as [Hb Hph2'].
                       apply negb_true_iff in Hb. rewrite Hb in *. clear Hb. apply negb_true_iff in Hph2'. destruct (rev ph2) as [| hph2 tph2] eqn:Hph2.
                       rewrite reverse_list_twice with (l := ph2) in Hph2'. rewrite Hph2 in Hph2'. simpl in Hph2'. discriminate Hph2'. clear Hph2'.
                       pose proof Hx as Hx'''. symmetry in Hx'''. apply Hl2 in Hx'''. apply Hx''' in Hph2 as Hph2'. destruct Hph2' as [Hzh Hph]. rewrite <- Hzh in *. clear Hzh. clear Hx'''.
                       clear Hx'. assert (Hph2': ph2 = rev tph2 ++ [zh]). { rewrite reverse_list_twice with (l := ph2). rewrite Hph2. simpl. reflexivity. }

                       (* choose first overlap in path of last collider that overlaps *)
                       (* use first overlap of path + last overlap of Lx to find collider, then find first overlap in two paths *)
                       apply overlap_rev_true in Hoverx.
                       apply list_has_first_elt_in_common_with_other_list in Hoverx. destruct Hoverx as [tzh1 [tzh2 [Lx1 [Lx2 [y' Hy]]]]].
                       assert (Hy': exists (c d: node) (p: nodes), In c (find_colliders_in_path (x, v, rev tlx1) G)
                                   /\ get_assigned_value Dx c = Some (p, d) /\ d =? c = false
                                   /\ In y' (p ++ [d])).
                       { apply collider_descendants_from_assignments_belong_to_collider with (L := Lx). apply HLx. apply membership_rev.
                         destruct Hy as [_ [Hy _]]. rewrite Hy. apply membership_append_r. left. reflexivity. }
                       destruct Hy' as [cy [dy [py Hpdy]]].

                       assert (Hovery: overlap ph2 (py ++ [dy]) = true).
                       { apply overlap_has_member_in_common. exists y'. split.
                         - destruct Hy as [Hy _]. rewrite Hy. apply membership_append_r. left. reflexivity.
                         - apply Hpdy. }
                       apply lists_have_first_elt_in_common in Hovery. destruct Hovery as [lxy1 [lxy2 [lcyd1 [lcyd2 [y Hy']]]]].

                       assert (Hlxy1y: forall (w: node), In w (lxy1 ++ [y]) -> In w (ph ++ [zh])).
                       { intros w Hmem. rewrite Hx. apply membership_append_r. right. destruct Hy' as [Hy' _]. rewrite Hy'. rewrite app_assoc. apply membership_append. apply Hmem. }

                       assert (Hlxy1: forall (w: node), In w lxy1 -> In w ph).
                       { intros w Hmem. rewrite reverse_list_twice with (l := ph2) in Hy'.
                         destruct Hy' as [Hy' _]. rewrite Hph2 in Hy'. simpl in Hy'. symmetry in Hy'. apply Hl2 in Hy'. rewrite Hph. apply membership_append_r. right.
                         destruct (rev lxy2) as [| hlxy2 tlxy2] eqn:Hlxy2.
                         apply Hy' in Hlxy2. destruct Hlxy2 as [_ Hlxy2]. simpl. unfold nodes in *. unfold node in *. rewrite <- Hlxy2. apply Hmem.
                         apply Hy' in Hlxy2. destruct Hlxy2 as [_ Hlxy2]. simpl. unfold nodes in *. unfold node in *. rewrite Hlxy2. apply membership_append. apply Hmem. }

                       assert (Hcolcy: In cy (find_colliders_in_path (h, v, lhv) G)).
                       { apply subpath_preserves_colliders with (u := x) (l1 := rev lx2) (l2 := rev tlx1). split. symmetry. apply Hlhvrev. left. apply Hpdy. }
                       destruct HDh as [HDh HDh']. apply HDh' in Hcolcy.
                       pose proof Hpdy as Hpdy'. destruct Hpdy' as [_ [Hpdy' _]]. apply collider_descendants_preserved_for_subpath with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G) in Hpdy'.
                       2: { apply HDx. }
                       destruct Hcolcy as [Hcolcy | Hcolcy]. rewrite Hpdy' in Hcolcy. inversion Hcolcy. inversion H. rewrite H5 in Hpdy. destruct Hpdy as [_ [_ [Hpdy _]]]. rewrite eqb_refl in Hpdy. discriminate Hpdy.
                       destruct Hcolcy as [py' [dy' Hpdy'']]. destruct Hpdy'' as [Hpdy''' Hpdy'']. rewrite Hpdy' in Hpdy'''. inversion Hpdy'''. rewrite <- H2 in *. rewrite <- H3 in *. clear Hpdy'''. clear H2. clear H3.

                       assert (Hcy: In cy (rev tlx1)).
                       { assert (Hpath'': is_path_in_graph (x, v, rev tlx1) G = true). { apply subpath_still_path with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }
                         apply intermediate_node_in_path with (x := cy) in Hpath''. apply Hpath''. right. right. apply Hpdy. }
                       apply membership_splits_list in Hcy. destruct Hcy as [lcyv1 [lcyv2 Hcy]].

                       exists (h :: ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).

                       assert (Hcychv: acyclic_path_2 (concat h x v ph1 (lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2))).
                       { apply concat_paths_acyclic.
                         - split. apply Hlhv. split. apply Hcychx. apply concat_paths_acyclic.
                           + (* x->..tph2..->zh acyclic, this is a subpath. *) split.
                             destruct Hlhv as [[Hlhv _] _]. destruct Hlhv as [_ [_ [Hlhv _]]]. intros Hxv. apply Hlhv. apply membership_rev. rewrite H1.
                             apply membership_append_r. left. apply Hxv. split.
                             * apply Hacyc with (dy := zh) (l2 := lxy2) (l3 := rev tph2). split. symmetry. unfold nodes in *. unfold node in *. rewrite <- Hph2'. apply Hy'.
                               apply subpath_still_acyclic with (w := h) (l1 := ph1) (l3 := ph1 ++ [x] ++ rev tph2). split. reflexivity.
                               unfold node in *. rewrite <- Hph. apply Hh'.
                             * apply Hcyccy with (dy := dy) (py := py) (lcyd2 := lcyd2) (lcyv1 := lcyv1). apply Hpdy''. apply Hcy. apply Hy'.

                           + split.
                             * intros Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                               -- (* lcyd1: cy's desc path cannot intersect lhv *)
                                  destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := x) in Hpdy''.
                                  apply Hpdy''. destruct Hy' as [_ [Hy' _]]. rewrite Hy'. apply membership_append. apply membership_rev. apply Hmem.
                                  right. apply membership_append. rewrite Hlhvrev. apply membership_append_r. left. reflexivity.
                               -- (* [cy, lcyv1]: lhv acyclic *) unfold acyclic_path_2 in Hcycxv. destruct Hcycxv as [_ [Hcycxv _]]. apply Hcycxv.
                                  rewrite <- Hcy. apply membership_append_r. apply Hmem.

                             * (* Hx, v cannot intersect h's desc path *)
                               intros Hmem. apply no_overlap_non_member with (x := v) in Hx''. apply Hx''. apply Hlxy1 in Hmem. apply membership_append. apply Hmem.
                               left. reflexivity.

                           + (* lcyd1: Hy'. [cy, lcyv2]: Hx *)
                             apply no_overlap_non_member. intros w Hw Hw'. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                             * destruct Hy' as [_ [_ Hy']]. apply no_overlap_non_member with (x := w) in Hy'. apply Hy'. apply Hw'. apply membership_rev. apply Hw.
                             * apply no_overlap_non_member with (x := w) in Hx''. apply Hx''. apply Hlxy1 in Hw'. apply membership_append. apply Hw'.
                               right. apply membership_rev. rewrite <- Hcy. apply membership_append_r. apply Hw.

                         - split.
                           + (* [lxy1, y]: h's desc path acyclic. lcyd1: HDh: h doesn't not overlap with any desc path. [cy, lcyv1]: lhv acyclic *)
                             intros Hmem. rewrite app_assoc in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                             * destruct Hh' as [_ [Hh' _]]. unfold acyclic_path_2 in Hh'. apply Hlxy1y in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                               -- destruct Hh' as [_ [Hh' _]]. apply Hh'. apply Hmem.
                               -- destruct Hh' as [Hh' _]. apply Hh'. destruct Hmem as [Hmem | Hmem]. symmetry. apply Hmem. exfalso. apply Hmem.
                             * assert (F: ~In h (rev lcyd1 ++ [cy] ++ lcyv2)). { apply Hcyccy with (dy := dy) (py := py) (lcyv1 := lcyv1) (lcyd2 := lcyd2) (y := y). apply Hpdy''. apply Hcy. apply Hy'. }
                               apply F. apply Hmem.

                           + (* Hx *) intros Hmem. apply no_overlap_non_member with (x := v) in Hx''. apply Hx''. apply membership_append.
                             rewrite Hph. apply membership_append. apply Hmem.
                             left. reflexivity.
                         - (* lxy1, y: Hh' ph path acyclic. lcyd1: Hoverph1. [cy, lcyv2]: Hx'' *)
                           apply no_overlap_non_member. intros w Hw Hw'. rewrite app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                           + destruct Hh' as [_ [Hh' _]]. apply acyclic_path_correct_2 in Hh'.
                             assert (Hc: count w (h :: ph ++ [zh]) = 0 \/ count w (h :: ph ++ [zh]) = 1). { apply acyclic_path_intermediate_nodes. apply Hh'. }
                             assert (Hc': count w (h :: ph ++ [zh]) > 1).
                             { rewrite Hph. destruct Hy' as [Hy' _]. rewrite <- app_assoc. rewrite <- app_assoc. unfold node in *. rewrite <- Hph2'. rewrite Hy'.
                               simpl. rewrite count_app. apply member_count_at_least_1 in Hw'. simpl. rewrite <- append_vs_concat. rewrite count_app.
                               apply member_count_at_least_1 in Hw. destruct (h =? w). destruct (x =? w). lia. lia. destruct (x =? w). lia. lia. }
                             lia.
                           + apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                             * apply no_overlap_non_member with (x := w) in Hoverph1. apply Hoverph1. apply Hw'.
                               apply collider_descendants_from_assignments_mem with (D := Dx) (p' := (x, v, rev tlx1)) (p := py) (d := dy) (c := cy) (G := G).
                               apply Hpdy. split. apply Hpdy. apply Hpdy. apply HLx. destruct Hy' as [_ [Hy' _]]. rewrite Hy'. apply membership_append. apply membership_rev. apply Hw.
                             * apply no_overlap_non_member with (x := w) in Hx''. apply Hx''. apply membership_append. rewrite Hph. apply membership_append. apply Hw'.
                               right. apply membership_rev. rewrite <- Hcy. apply membership_append_r. apply Hw. }

                       assert (Hcycuhv: acyclic_path_2 (u, v, h :: ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2)).
                       { apply acyclic_path_cat_2.
                         { apply Hcychv. }

                         (* u not in [ph1,x, lxy1] b/c cycle. u not in [y,lcyd1] b/c HuL. u not in [cy, lcyv2] b/c Hulhv *)
                         { intros Hmem. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. rewrite Hmem in Hhu. rewrite eqb_refl in Hhu. discriminate Hhu.
                           rewrite app_comm_cons in Hmem. rewrite app_assoc in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                           - apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                             + apply member_In_equiv_F in Huph. apply Huph. rewrite Hph. apply membership_append. rewrite <- append_vs_concat in Hmem. apply membership_append_or in Hmem.
                               destruct Hmem as [Hmem | Hmem]. rewrite app_assoc. apply membership_append. apply Hmem.
                               rewrite <- Hph. apply Hlxy1. apply Hmem.
                             + rewrite app_comm_cons in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                               * apply member_In_equiv_F in HuL. apply HuL. apply HLcy with (cy := cy) (dy := dy) (py := py) (y' := y'). apply Hpdy.
                                 destruct Hy' as [_ [Hy' _]]. rewrite Hy'. rewrite app_assoc. apply membership_append. apply membership_rev. rewrite reverse_list_append. simpl. apply Hmem.
                               * apply member_In_equiv_F in Hulhv. apply Hulhv. rewrite Hlhvrev. apply membership_append_r. right. simpl. rewrite <- Hcy. apply membership_append_r. apply Hmem.
                           - destruct Hmem as [Hmem | Hmem]. destruct Hcyc as [Hcyc _]. apply Hcyc. symmetry. apply Hmem. apply Hmem. } }

                       split. apply Hcycuhv.

                       assert (Hphv: is_path_in_graph (concat h x v ph1 (lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2)) G = true).
                       { apply concat_paths_still_a_path. split.
                         - apply directed_path_is_path. apply Hpathcy' with (dy := zh) (py := ph) (l2 := ph2). apply Hh'. apply Hx.
                         - apply concat_paths_still_a_path. split.
                           + apply subpath_still_path with (w := h) (l1 := ph1) (l3 := ph1 ++ [x] ++ lxy1). split. reflexivity.
                             apply directed_path_is_path. apply Hpathcy' with (dy := zh) (py := ph) (l2 := lxy2). apply Hh'. rewrite <- app_assoc. rewrite <- app_assoc. rewrite Hx. destruct Hy' as [Hy' _]. rewrite Hy'. reflexivity.
                           + apply concat_paths_still_a_path. split.
                             * apply reverse_path_in_graph. apply directed_path_is_path. apply Hpathcy' with (dy := dy) (py := py) (l2 := lcyd2). apply Hpdy''. apply Hy'.
                             * apply subpath_still_path with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite Hlhvrev. rewrite <- Hcy. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hlhv. }

                       assert (Hhmed: In h (find_mediators_in_path (u, v, h :: ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2) G)).
                       { apply mediator_means_edge_out with (c := h) (G := G) in Hx.
                         destruct ph1 as [| hph11 tph11].
                         * apply mediators_vs_edges_in_path. exists u. exists x. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                           -- apply Huh.
                           -- destruct Hx as [Hx _]. apply Hx. reflexivity.
                         * apply mediators_vs_edges_in_path. exists u. exists hph11. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                           -- apply Huh.
                           -- destruct Hx as [_ Hx]. apply Hx with (tly1 := tph11). reflexivity.
                         * apply Hh'. }

                       assert (Hxmed: In x (find_mediators_in_path (concat h x v ph1 (lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2)) G)).
                       { unfold concat. apply subpath_preserves_mediators with (u := y) (l1 := ph1 ++ x :: lxy1) (l2 := rev lcyd1 ++ [cy] ++ lcyv2). split. rewrite <- app_assoc. reflexivity.
                         right. apply directed_path_all_mediators. split.
                         -- apply Hpathcy' with (dy := zh) (py := ph) (l2 := lxy2). apply Hh'. rewrite Hx. destruct Hy' as [Hy' _]. rewrite Hy'. rewrite <- app_assoc. reflexivity.
                         -- apply membership_append_r. left. reflexivity. }

                       assert (Hycol: In y (find_colliders_in_path (concat x y v lxy1 (rev lcyd1 ++ [cy] ++ lcyv2)) G)).
                       { apply subpath_preserves_colliders with (u := cy) (l1 := lxy1 ++ [y] ++ rev lcyd1) (l2 := lcyv2). split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. right.
                         apply intersection_of_directed_paths_is_collider with (d1 := zh) (d2 := dy) (l1 := rev tph2) (l2 := py) (l1'' := lxy2) (l2'' := lcyd2).
                         apply subpath_still_directed with (w := h) (l1 := ph1) (l3 := ph). split. symmetry. apply Hph. apply Hh'. apply Hpdy''.
                         destruct Hy' as [Hy' _]. unfold nodes in *. unfold node in *. rewrite <- Hy'. symmetry. apply Hph2'. apply Hy'. }

                       assert (Hcymed: In cy (find_mediators_in_path (concat y cy v (rev lcyd1) lcyv2) G)).
                       { apply collider_becomes_mediator_when_concat_directed with (x := x) (dy := dy) (txv := rev tlx1) (py := py) (lv1 := lcyv1) (ly2 := lcyd2).
                         apply Hpdy. apply Hcy.
                         apply subpath_still_acyclic with (w := h) (l1 := rev lx2) (l3 := lhv). split. simpl in Hcy. symmetry. apply Hlhvrev. apply Hlhv.
                         apply Hy'. apply Hpdy''. }

                       split.
                       { (* (u, h, ph1, x) all mediators. x is mediator (not in z, Hh'). [lxy1] mediators
                            y collider, either = zh = dy and in Z, or not in Z but has path to dy
                            [lcyd1 mediators, not in Z. cy mediator, not in Z. lcyv2 from lhv d-conn *) 
                         apply d_connected_cat. apply HG. apply Hcycuhv.
                         - apply concat_d_connected_paths. apply HG. apply Hphv. split.
                           + apply Hconncy with (p := ph) (l2 := ph2) (d := zh). apply Hx. split. apply Hh'. split. apply Hh'. apply Hh'.
                           + split. apply concat_d_connected_paths. apply HG. unfold concat. apply subpath_still_path with (w := h) (l1 := ph1) (l3 := ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).
                             split. reflexivity. apply Hphv. split.
                             * apply subpath_still_d_connected_gen with (w := h) (l1 := ph1) (l3 := ph1 ++ [x] ++ lxy1). split. reflexivity.
                               apply Hconncy with (p := ph) (l2 := lxy2) (d := zh). rewrite <- app_assoc. rewrite <- app_assoc. rewrite Hx. destruct Hy' as [Hy' _]. rewrite Hy'. reflexivity.
                               split. apply Hh'. split. apply Hh'. apply Hh'.
                             * split. apply concat_d_connected_paths. apply HG. apply subpath_still_path with (w := h) (l1 := ph1 ++ [x] ++ lxy1) (l3 := ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).
                               rewrite <- app_assoc. rewrite <- app_assoc. split. reflexivity. apply Hphv. split.
                               -- apply reverse_d_connected_paths. apply Hconncy with (p := py) (l2 := lcyd2) (d := dy). apply Hy'. split. apply Hpdy''. split.
                                  apply overlap_cat with (x := cy). apply Hpdy''. apply Hpdy''.
                               -- split. apply subpath_still_d_connected_gen with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite Hlhvrev. rewrite <- Hcy. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hlhv.
                                  apply subpath_still_acyclic with (w := h) (l1 := ph1 ++ [x] ++ lxy1) (l3 := ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2). split.
                                  rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hcychv.
                               -- left. apply and_comm. split.
                                  ++ destruct Hpdy'' as [_ [_ [_ [Hpdy'' _]]]]. simpl in Hpdy''. destruct (member cy Z) as [|] eqn:HcyZ. discriminate Hpdy''. apply member_In_equiv_F. apply HcyZ.
                                  ++ apply Hcymed.
                               -- apply subpath_still_acyclic with (w := h) (l1 := ph1) (l3 := ph1 ++ [x]  ++lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2). split. reflexivity. apply Hcychv.
                             * right. right. rewrite and_comm. split.
                               ++ unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists dy. rewrite and_comm. split. apply Hpdy''.
                                  apply find_descendants_correct. destruct Hy' as [_ [Hy' _]]. symmetry in Hy'. destruct (rev lcyd2) as [| hlyd2 tlyd2] eqn:Hlyd2.
                                  -- apply Hl2 in Hy'. left. apply Hy'. apply Hlyd2.
                                  -- apply Hl2 in Hy'. right. exists (y, dy, rev tlyd2). split. apply subpath_still_directed with (w := cy) (l1 := lcyd1) (l3 := py). split. symmetry. apply Hy' with (hl2 := hlyd2) (tl2 := tlyd2). apply Hlyd2. apply Hpdy''.
                                     apply path_start_end_refl.
                               ++ apply Hycol.
                             * apply Hcychv.
                           + left. apply and_comm. split.
                             * destruct Hh' as [_ [_ [Hh' _]]]. intros HxZ. apply no_overlap_non_member with (x := x) in Hh'. apply Hh'.
                               rewrite Hph. apply membership_append_r. left. reflexivity. apply HxZ.
                             * apply Hxmed.
                         - left. apply and_comm. split.
                            + apply HhZ.
                            + apply Hhmed. }

                       split.
                       { simpl. rewrite Huh. simpl. destruct G as [V E]. apply Hphv. }
                       split.
                       { intros w Hw. (* w = h: exists zh, ph, h not in Z. w in ph1: all not in Z, exists zh, ph. w = x: exists zh, ph, not in Z (Hh')
                            w in lxy1: exists zh, ph, not in Z. w = y: exists dy, lcdy2 (or =dy), path in. w in lcyd1: exists dy, lcdy2, path in
                            w = cy: exists dy, lcdy2, path in. w in lcyv2: use Hout *)
                         assert (Hwu: w =? u = false). { apply Houtwu with (x' := v) (l1 := ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2) (l2 := t). apply Hw. }
                         assert (Hwv: w =? v = false). { apply Houtwv with (x' := u) (l1 := h :: ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2) (l2 := h :: t). apply Hcyc. apply Hw. }
                         rewrite <- node_in_path_cat in Hw. rewrite <- node_in_path_cat in Hw. 2: { apply Hwu. } 2: { apply Hwu. }
                         rewrite path_out_of_node_cat. 2: { apply Hwu. }

                         destruct (w =? h) as [|] eqn:Hwh.
                         - apply eqb_eq in Hwh. rewrite Hwh. split.
                           + left. exists zh. exists ph. split. apply Hh'. split. apply Hh'. apply HhZ.
                           + intros H. apply HhZ.
                         - destruct (member w (ph1 ++ [x] ++ lxy1)) as [|] eqn:Hwph1.
                           + assert (Houtph1: path_out_of_node w (h, v, ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2) G = path_out_of_node w (u, y, h :: ph1 ++ [x] ++ lxy1) G).
                             { rewrite path_out_of_node_cat. 2: { apply Hwu. } assert (exists (b: bool), path_out_of_node w (h, y, ph1 ++ [x] ++ lxy1) G = Some b).
                               { apply path_out_of_node_mem_2. right. apply member_In_equiv. apply Hwph1. }
                               destruct H as [bw Hbw]. unfold nodes in *. unfold node in *. rewrite Hbw. apply subpath_preserves_path_out_of_node_2 with (u := y) (l1 := ph1 ++ [x] ++ lxy1) (l2 := rev lcyd1 ++ [cy] ++ lcyv2). split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                               apply Hbw. }
                             unfold nodes in *. unfold node in *. rewrite Houtph1. apply Houtwph1 with (ph2' := lxy2). apply member_In_equiv. apply Hwph1. rewrite <- app_assoc. rewrite <- app_assoc.
                             destruct Hy' as [Hy' _]. rewrite Hx. rewrite Hy'. reflexivity.
                           + destruct (member w (y :: rev lcyd1)) as [|] eqn:Hwy.
                             * apply member_In_equiv in Hwy.
                               assert (Houtw: path_out_of_node w (h, v, ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2) G = path_out_of_node w (y, cy, rev lcyd1) G).
                               { assert (Hwlp1: exists (b: bool), path_out_of_node w (y, cy, rev lcyd1) G = Some b). { apply path_out_of_node_mem_2. apply Hwy. }
                                 destruct Hwlp1 as [bw Hbw]. rewrite Hbw. apply subpath_preserves_path_out_of_node with (u := y) (l1 := ph1 ++ [x] ++ lxy1) (l2 := rev lcyd1 ++ [cy] ++ lcyv2). split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                                 apply subpath_preserves_path_out_of_node_2 with (u := cy) (l1 := rev lcyd1) (l2 := lcyv2). split. reflexivity. apply Hbw.
                                 apply Hcychv. }
                               unfold nodes in *. unfold node in *. rewrite Houtw. apply Houtw_revdir with (d := dy) (lyc2 := lcyd2) (p := py). apply Hwy. symmetry. apply Hy'. repeat split; apply Hpdy''.
                               apply Hpathcy' with (dy := dy) (py := py) (l2 := lcyd2). apply Hpdy''. apply Hy'.
                             * assert (Hwcy: In w (cy :: lcyv2)).
                               { assert (Hwmem: In w (u :: h :: ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2)).
                                 { destruct Hw as [[Hw _] | Hw].
                                   - rewrite node_in_path_equiv in Hw. right. apply member_In_equiv in Hw. rewrite app_comm_cons in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                     apply Hw. destruct Hw as [Hw | Hw]. rewrite Hw in Hwv. rewrite eqb_refl in Hwv. discriminate Hwv. exfalso. apply Hw.
                                   - destruct Hw as [bw [_ Hw]]. apply path_out_of_node_mem_gen with (G := G) (v := v). exists (negb bw). apply Hw. }
                                 apply member_In_equiv in Hwmem. simpl in Hwmem. rewrite eqb_sym in Hwmem. rewrite Hwu in Hwmem. rewrite eqb_sym in Hwmem. rewrite Hwh in Hwmem.
                                 rewrite <- append_vs_concat in Hwmem. rewrite app_assoc in Hwmem.
                                 apply member_In_equiv in Hwmem. apply membership_append_or in Hwmem. destruct Hwmem as [Hwmem | Hwmem]. apply member_In_equiv in Hwmem. rewrite <- app_assoc in Hwmem. rewrite Hwmem in Hwph1. discriminate Hwph1.
                                 rewrite app_comm_cons in Hwmem. apply membership_append_or in Hwmem. destruct Hwmem as [Hwmem | Hwmem]. apply member_In_equiv in Hwmem. rewrite Hwmem in Hwy. discriminate Hwy.
                                 apply Hwmem. }
                               specialize Houtwcy with (cy := cy) (l1 := ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1) (lcy2 := lcyv2). rewrite <- app_assoc in Houtwcy. rewrite <- app_assoc in Houtwcy. rewrite <- app_assoc in Houtwcy. rewrite <- app_assoc in Houtwcy.
                               apply Houtwcy with (lcy1 := rev lx2 ++ [x] ++ lcyv1).
                               -- apply Hwcy.
                               -- rewrite Hlhvrev. rewrite <- Hcy. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                               -- apply Hcychv.
                               -- rewrite path_out_of_node_cat in Hw. rewrite path_out_of_node_cat in Hw. apply Hw. apply Hwu. apply Hwu. }

                       assert (HDcy: exists (D: assignments (nodes * node)), get_collider_descendants_for_subpath Dh (find_colliders_in_path (cy, v, lcyv2) G) = Some D).
                       { apply collider_descendants_for_subpath_existence_2 with (u := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (L := L).
                         unfold concat. unfold nodes in *. unfold node in *. rewrite <- app_assoc. rewrite <- app_assoc. simpl in Hcy. rewrite Hcy. rewrite <- Hlhvrev. apply HLh. }
                       destruct HDcy as [Dcy HDcy].

                       assert (Hcolhv: find_colliders_in_path (u, v, h :: ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2) G = y :: (find_colliders_in_path (cy, v, lcyv2) G)).
                       { assert (Hcoluv: [] ++ h :: ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2 = h :: ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).
                          { reflexivity. }
                          apply subpath_preserves_colliders_2 with (w := u) (v := v) (G := G) in Hcoluv. destruct Hcoluv as [Hcoluv | Hcoluv].
                          - (* h is a mediator, not a collider *)
                            apply if_mediator_then_not_confounder_path in Hhmed. exfalso. destruct Hhmed as [_ Hhmed]. apply Hhmed. unfold concat. unfold nodes in *.
                            unfold node in *. simpl in Hcoluv. simpl. rewrite Hcoluv. left. reflexivity. apply HG. apply Hcycuhv.
                          - unfold nodes in *. rewrite Hcoluv.

                            assert (Hcolhv: (ph1 ++ [x] ++ lxy1) ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2 = ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).
                            { rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
                            assert (Hcoluy: find_colliders_in_path (u, y, h :: ph1 ++ [x] ++ lxy1) G = []). { apply Hcolph1 with (ph2' := lxy2). destruct Hy' as [Hy' _]. rewrite Hx. rewrite Hy'. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
                            assert (Hcolhy: find_colliders_in_path (h, y, ph1 ++ [x] ++ lxy1) G = []). { destruct (find_colliders_in_path (h, y, ph1 ++ [x] ++ lxy1) G) as [| ch ct] eqn:Hhy. reflexivity.
                              assert (Hch: In ch (find_colliders_in_path (u, y, h :: ph1 ++ [x] ++ lxy1) G)). { apply subpath_preserves_colliders with (u := h) (l1 := []) (l2 := ph1 ++ [x] ++ lxy1). split. reflexivity. left. simpl. simpl in Hhy. rewrite Hhy. left. reflexivity. }
                              rewrite Hcoluy in Hch. exfalso. apply Hch. }

                            apply subpath_preserves_colliders_2 with (w := h) (u := y) (v := v) (G := G) in Hcolhv. destruct Hcolhv as [Hcolhv | Hcolhv].
                            + unfold nodes in *. rewrite Hcolhv. unfold node in *. rewrite Hcolhy.
                              assert (Hcolyv: rev lcyd1 ++ [cy] ++ lcyv2 = rev lcyd1 ++ [cy] ++ lcyv2). { reflexivity. } apply subpath_preserves_colliders_2 with (w := y) (v := v) (G := G) in Hcolyv.
                              assert (Hcolycy: find_colliders_in_path (y, cy, rev lcyd1) G = []). { apply Hcoldir with (d := dy) (p' := py) (p2' := lcyd2). apply Hy'. apply Hpdy''. apply Hpdy''. }
                              unfold nodes in *. unfold node in *. rewrite Hcolycy in *. destruct Hcolyv as [Hcolyv | Hcolyv].
                              * (* cy is a mediator, not a collider *)
                                apply if_mediator_then_not_confounder_path in Hcymed. exfalso. destruct Hcymed as [_ Hcymed]. apply Hcymed. unfold concat. unfold nodes in *.
                                unfold node in *. simpl in Hcolyv. simpl. rewrite Hcolyv. left. reflexivity. apply HG. unfold concat. unfold concat in Hcychv. apply subpath_still_acyclic with (w := h) (l1 := ph1 ++ x :: lxy1) (l3 := ph1 ++ x :: lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).
                                split. rewrite <- app_assoc. reflexivity. apply Hcychv.
                              * rewrite Hcolyv. simpl. reflexivity.
                            + (* y is a collider, so should be included in Hcolhv *)
                              unfold concat in Hycol.
                              unfold nodes in *. unfold node in *. rewrite <- append_vs_concat in Hycol. rewrite <- app_assoc in Hycol.
                              assert (Hycol': In y (find_colliders_in_path (h, v, ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2) G)).
                              { apply subpath_preserves_colliders with (u := x) (l1 := ph1) (l2 := lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2). split. reflexivity. left. apply Hycol. }
                              clear Hycol. pose proof Hycol' as Hycol. clear Hycol'. rewrite Hcolhv in Hycol. apply membership_append_or in Hycol.
                              destruct Hycol as [Hycol | Hycol]. (* contradicts acyclic *)
                              * assert (Hphy: is_path_in_graph (h, y, ph1 ++ [x] ++ lxy1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := rev lcyd1 ++ [cy] ++ lcyv2) (l3 := ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).
                                  split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hphv. } apply intermediate_node_in_path with (x := y) in Hphy.
                                assert (Hyph11: In y (ph1 ++ [x] ++ lxy1)). { apply Hphy. right. right. apply Hycol. }
                                assert (Hchy: acyclic_path_2 (h, y, ph1 ++ [x] ++ lxy1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := rev lcyd1 ++ [cy] ++ lcyv2) (l3 := ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).
                                  split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hcychv. } exfalso. destruct Hchy as [_ [_ [Hchy _]]]. apply Hchy. apply Hyph11.
                              * assert (Hphy: is_path_in_graph (y, v, rev lcyd1 ++ [cy] ++ lcyv2) G = true). { apply subpath_still_path with (w := h) (l1 := ph1 ++ [x] ++ lxy1) (l3 := ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).
                                  split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hphv. } apply intermediate_node_in_path with (x := y) in Hphy.
                                assert (Hyph11: In y (rev lcyd1 ++ [cy] ++ lcyv2)). { apply Hphy. right. right. apply Hycol. }
                                assert (Hchy: acyclic_path_2 (y, v, rev lcyd1 ++ [cy] ++ lcyv2)). { apply subpath_still_acyclic with (w := h) (l1 := ph1 ++ [x] ++ lxy1) (l3 := ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).
                                  split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hcychv. } exfalso. destruct Hchy as [_ [Hchy _]]. apply Hchy. apply Hyph11. }

                        unfold nodes in *. rewrite Hcolhv.

                        assert (HyDcy': forall (py': nodes) (dy': node) (D: assignments (nodes * node)), D = (y, (py', dy')) :: Dcy
                                       -> forall c : node,
                                          (c =? y) = false
                                           -> In c (y :: find_colliders_in_path (cy, v, lcyv2) G)
                                           -> get_assigned_value D c = Some ([], c) /\ In c Z \/
                                               (exists (p : list node) (d : node),
                                                  get_assigned_value D c = Some (p, d) /\
                                                  In d Z /\
                                                  is_directed_path_in_graph (c, d, p) G = true /\
                                                  acyclic_path_2 (c, d, p) /\
                                                  overlap (c :: p) Z = false /\
                                                  overlap (p ++ [d])
                                                    (u :: (h :: ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2) ++ [v]) =
                                                  false /\ overlap (c :: p ++ [d]) (cy :: py ++ [dy]) = false
                                                  /\ (forall (c' d' : node) (p' : list node),
                                                     (c =? c') = false /\ get_assigned_value Dcy c' = Some (p', d') ->
                                                     overlap (c :: p ++ [d]) (c' :: p' ++ [d']) = false))).
                        { intros py'' dy'' D HDeq c Hyc Hc.
                          destruct Hc as [Hc | Hc]. rewrite Hc in Hyc. rewrite eqb_refl in Hyc. discriminate Hyc.
                          (* induction case *) assert (Hc': In c (find_colliders_in_path (h, v, lhv) G)).
                          { apply subpath_preserves_colliders with (u := cy) (l1 := rev lx2 ++ [x] ++ lcyv1) (l2 := lcyv2). split. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy. symmetry. apply Hlhvrev. left. apply Hc. }
                          pose proof Hc' as Hc''. apply HDh' in Hc'. rewrite HDeq in *. destruct Hc' as [Hc' | Hc'].
                          -- left. split. simpl. rewrite eqb_sym. rewrite Hyc. rewrite <- collider_descendants_preserved_for_subpath_3 with (D := Dh) (col := find_colliders_in_path (cy, v, lcyv2) G).
                             apply Hc'. apply HDcy. apply Hc. apply Hc'.
                          -- right. destruct Hc' as [pc [dc Hc']]. exists pc. exists dc. split. simpl. rewrite eqb_sym. rewrite Hyc. simpl. rewrite <- collider_descendants_preserved_for_subpath_3 with (D := Dh) (col := find_colliders_in_path (cy, v, lcyv2) G).
                             apply Hc'. apply HDcy. apply Hc. split. apply Hc'. split. apply Hc'. split. apply Hc'. split. apply Hc'.
                             assert (Hovercy: overlap (c :: pc ++ [dc]) (cy :: py ++ [dy]) = false).
                             { apply Hc'. rewrite and_comm. split. apply collider_descendants_preserved_for_subpath with (D' := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hpdy.
                               destruct (c =? cy) as [|] eqn:Hccy. exfalso. apply eqb_eq in Hccy.
                               assert (Hmemcy: In cy lcyv2).
                               { assert (Hpcy: is_path_in_graph (cy, v, lcyv2) G = true).
                                 { apply subpath_still_path with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy. symmetry. apply Hlhvrev. apply Hlhv. }
                                 apply intermediate_node_in_path with (x := cy) in Hpcy. apply Hpcy. right. right. rewrite <- Hccy in *. apply Hc. }
                               assert (Hccy': acyclic_path_2 (cy, v, lcyv2)).
                               { apply subpath_still_acyclic with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy. symmetry. apply Hlhvrev. apply Hlhv. }
                               destruct Hccy' as [_ [Hccy' _]]. apply Hccy'. apply Hmemcy. reflexivity. }

                             repeat split.
                             ++ (* u: HuL. h: HDh'. ph1: Hoverph1. x: HDh'. (x, y): Hy. [y, lcyd1]: HDh' (desc path of cy). [cy, v]: HDh'. *) apply no_overlap_non_member. intros w Hw Hw'.
                                assert (HwL: In w L).
                                { apply collider_descendants_from_assignments_mem with (D := Dh) (G := G) (p' := (h, v, lhv)) (p := pc) (d := dc) (c := c). apply Hc''. split. apply Hc'.
                                  destruct (dc =? c) as [|] eqn:Hdcc. apply eqb_eq in Hdcc. destruct Hc' as [_ [_ [_ [[Hc' _] _]]]]. exfalso. apply Hc'. symmetry. apply Hdcc. reflexivity.
                                  apply HLh. apply Hw'. }
                                destruct Hw as [Hw | Hw].
                                { apply member_In_equiv_F in HuL. apply HuL. rewrite Hw. apply HwL. } destruct Hw as [Hw | Hw].
                                { destruct Hc' as [_ [_ [_ [_ [_ [Hc' _]]]]]]. apply no_overlap_non_member with (x := h) in Hc'. apply Hc'. rewrite Hw. apply Hw'. left. reflexivity. }
                                rewrite <- app_assoc in Hw. apply membership_append_or in Hw.

                                destruct Hw as [Hw | Hw].
                                { (* w is in Lx, so Hoverph1 contradicts *)
                                  assert (HLxy: exists (l1' l2': nodes), Lx = l1' ++ pc ++ [dc] ++ l2').
                                  { apply get_collider_descendants_from_assignments_contains_path with (D := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G) (c := c).
                                    apply HLx. split.
                                    - apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hc'. rewrite <- Hcy. apply subpath_preserves_colliders with (u := cy) (l1 := lcyv1) (l2 := lcyv2). split. reflexivity. left. apply Hc.
                                    - apply eqb_neq. destruct Hc' as [_ [_ [_ [[Hc' _] _]]]]. apply Hc'.
                                    - apply subpath_preserves_colliders with (u := cy) (l1 := lcyv1) (l2 := lcyv2). split. apply Hcy. left. apply Hc. }

                                  assert (HwLx: In w Lx).
                                  { destruct HLxy as [Lx1' [Lx2' HLxy]]. rewrite HLxy. apply membership_append_r. rewrite app_assoc. apply membership_append. apply Hw'. }
                                  apply no_overlap_non_member with (x := w) in Hoverph1. apply Hoverph1. apply Hw. apply HwLx. }

                                rewrite <- app_assoc in Hw. simpl in Hw. destruct Hw as [Hw | Hw].
                                { destruct Hc' as [_ [_ [_ [_ [_ [Hc' _]]]]]]. apply no_overlap_non_member with (x := w) in Hc'. apply Hc'. apply Hw'. right. rewrite Hlhvrev. rewrite <- app_assoc. apply membership_append_r. simpl. left. apply Hw. }

                                rewrite <- app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                { (* w is in Lx. (py ++ [dy]) comes before (pc ++ [dc]) in Lx, since cy comes before c. Then, y' comes before w, so w in Lx1 *)
                                  (* Hy -> ph2 and Lx1 have no overlap. *)
                                  assert (HLxy: exists (l1' l2' l3': nodes), Lx = l1' ++ py ++ [dy] ++ l2' ++ pc ++ [dc] ++ l3').
                                  { apply get_collider_descendants_from_assignments_preserves_order with (D := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G) (c1 := cy) (c2 := c).
                                    apply HLx. split. apply Hpdy. rewrite eqb_sym. apply Hpdy. split.
                                    - apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hc'. rewrite <- Hcy. apply subpath_preserves_colliders with (u := cy) (l1 := lcyv1) (l2 := lcyv2). split. reflexivity. left. apply Hc.
                                    - apply eqb_neq. destruct Hc' as [_ [_ [_ [[Hc' _] _]]]]. apply Hc'.
                                    - pose proof Hcy as Hcy'. apply subpath_preserves_colliders_2 with (w := x) (v := v) (G := G) in Hcy. destruct Hcy as [Hcy | Hcy].
                                      + exists (find_colliders_in_path (x, cy, lcyv1) G). unfold nodes in *. unfold node in *. rewrite Hcy.
                                        apply membership_splits_list in Hc. destruct Hc as [lc1 [lc2 Hc]]. exists lc1. exists lc2. rewrite Hc. reflexivity.
                                      + (* contradiction in Hcy, since cy is a collider *) exfalso. destruct Hpdy as [Hpdy _]. unfold nodes in *. unfold node in *. rewrite Hcy in Hpdy. apply membership_append_or in Hpdy.
                                        destruct Hpdy as [Hpdy | Hpdy].
                                        * assert (HcyF: In cy lcyv1). { assert (Hcyp: is_path_in_graph (x, cy, lcyv1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := lcyv2) (l3 := rev tlx1). split. apply Hcy'.
                                            apply subpath_still_path with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }
                                            apply intermediate_node_in_path with (x := cy) in Hcyp. apply Hcyp. right. right. apply Hpdy. }
                                          assert (Hcycyc: acyclic_path_2 (x, cy, lcyv1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := lcyv2) (l3 := rev tlx1). split. apply Hcy'. apply Hcycxv. }
                                          destruct Hcycyc as [_ [_ [Hcycyc _]]]. apply Hcycyc. apply HcyF.
                                        * assert (HcyF: In cy lcyv2). { assert (Hcyp: is_path_in_graph (cy, v, lcyv2) G = true). { apply subpath_still_path with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy'.
                                            symmetry. apply Hlhvrev. apply Hlhv. }
                                            apply intermediate_node_in_path with (x := cy) in Hcyp. apply Hcyp. right. right. apply Hpdy. }
                                          assert (Hcycyc: acyclic_path_2 (cy, v, lcyv2)). { apply subpath_still_acyclic with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy'.
                                            symmetry. apply Hlhvrev. apply Hlhv. }
                                          destruct Hcycyc as [_ [Hcycyc _]]. apply Hcycyc. apply HcyF. }

                                  destruct Hpdy as [_ [_ [_ Hpdy]]]. apply membership_splits_list in Hpdy. destruct Hpdy as [ly1' [ly2' Hpdy]]. destruct HLxy as [Lx1' [Lx2' [Lx3' HLxy]]]. unfold nodes in *. unfold node in *. simpl in Hpdy. rewrite app_assoc in HLxy. rewrite app_assoc in HLxy. rewrite <- app_assoc with (l := Lx1') in HLxy. rewrite <- Hpdy in HLxy.
                                  assert (Hcounty: count y' Lx = 1).
                                  { apply get_collider_descendants_from_assignments_preserves_count with (D := Dx) (G := G) (Z := Z) (u := x) (v := v) (l' := rev tlx1).
                                    2: { apply HLx. } 2: { apply subpath_still_acyclic with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }
                                    2: { apply subpath_still_path with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }
                                    2: { rewrite HLxy. apply membership_append. apply membership_append_r. apply membership_append_r. left. reflexivity. }
                                    apply descendant_paths_disjoint_subpath with (Dh := Dh) (h := h) (l1 := rev lx2) (lhv := lhv). split. apply HDh. apply HDh'. apply HDx. apply Hlhvrev. }

                                  assert (HLx1: rev Lx1 = ly2' ++ Lx2' ++ pc ++ dc :: Lx3').
                                  { apply two_sublists_the_same_gen with (l := Lx) (a := y') (l1 := rev Lx2) (l1' := Lx1' ++ ly1'). destruct Hy as [_ [Hy _]].
                                    rewrite reverse_list_twice with (l := Lx). rewrite Hy. rewrite reverse_list_append. simpl. rewrite <- app_assoc. reflexivity.
                                    rewrite <- app_assoc in HLxy. rewrite <- app_assoc in HLxy. rewrite <- app_assoc. simpl in HLxy. apply HLxy. apply Hcounty. }
                                  assert (HwLx1: In w Lx1). { apply membership_rev. rewrite HLx1. apply membership_append_r. apply membership_append_r. rewrite <- append_vs_concat. apply membership_append. apply Hw'. }

                                  destruct Hy as [_ [_ Hy]]. apply no_overlap_non_member with (x := w) in Hy. apply Hy.
                                  destruct Hy' as [Hy' _]. rewrite Hy'. apply membership_append. apply Hw. apply HwLx1. }

                                rewrite app_comm_cons in Hw. rewrite <- app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                { destruct Hc' as [_ [_ [_ [_ [_ [_ Hc']]]]]]. specialize Hc' with (c' := cy) (d' := dy) (p' := py).
                                  apply no_overlap_non_member with (x := w) in Hovercy. apply Hovercy. right. apply Hw'. right. destruct Hy' as [_ [Hy' _]]. rewrite Hy'. rewrite app_assoc. apply membership_append.
                                  apply membership_rev. rewrite reverse_list_append. apply Hw. }
                                { destruct Hc' as [_ [_ [_ [_ [_ [Hc' _]]]]]]. apply no_overlap_non_member with (x := w) in Hc'. apply Hc'. apply Hw'. right. rewrite Hlhvrev. rewrite <- app_assoc. apply membership_append_r. rewrite <- Hcy. rewrite <- app_assoc. rewrite <- app_assoc. right.
                                  simpl. apply membership_append_r. apply Hw. }
                             ++ apply Hovercy.
                             ++ intros c' d' p' [Hcc' Hcdp'].
                                apply Hc'. split. apply Hcc'. apply collider_descendants_preserved_for_subpath with (D' := Dcy) (col := find_colliders_in_path (cy, v, lcyv2) G). apply HDcy. apply Hcdp'. }


                        (* destruct on y = zh = d or not *) destruct (rev lcyd2) as [| hy ty] eqn:Hlyd2.
                        { exists ((y, ([], y)) :: Dcy). split.
                          + apply HyDcy with (py' := []) (dy' := y) (Dcy := Dcy). reflexivity. apply HDcy.
                          + intros c Hc. destruct (c =? y) as [|] eqn:Hyc.
                            * apply eqb_eq in Hyc. left. split. simpl. rewrite Hyc. rewrite eqb_refl. reflexivity. rewrite Hyc. destruct Hy' as [_ [Hy' _]]. symmetry in Hy'. apply Hl2 in Hy'.
                              apply Hy' in Hlyd2. destruct Hlyd2 as [Hlyd2 _]. rewrite Hlyd2. apply Hpdy''.
                            * unfold nodes in *. rewrite Hcolhv in Hc. destruct Hc as [Hc | Hc]. rewrite Hc in Hyc. rewrite eqb_refl in Hyc. discriminate Hyc.

                              apply HyDcy' with (D := (y, ([], y)) :: Dcy) (py' := []) (dy' := y) in Hyc.
                              -- destruct Hyc as [Hyc | Hyc]. left. apply Hyc. right. destruct Hyc as [pc [dc Hyc]]. exists pc. exists dc.

                                 rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split. repeat split; apply Hyc.
                                 intros c' d' p' [Hcc' Hcdp']. simpl in Hcdp'. destruct (y =? c') as [|] eqn:Hyc'.
                                 ** inversion Hcdp'. rewrite <- H3. apply eqb_eq in Hyc'. rewrite <- Hyc'. simpl. (* y is original member of cy's desc path, so doesn't overlap c's desc path (HDh') *)
                                    rewrite <- Hyc' in Hcc'. rewrite eqb_sym in Hcc'. rewrite Hcc'. apply overlap_flip. simpl.
                                    assert (Hmemy: ~In y (pc ++ [dc])).
                                    { intros F. destruct Hyc as [_ [_ [_ [_ [_ [_ [Hovercy _]]]]]]]. apply no_overlap_non_member with (x := y) in Hovercy. apply Hovercy. right. apply F. right.
                                      destruct Hy' as [_ [Hy' _]]. rewrite Hy'. apply membership_append_r. left. reflexivity. }
                                    apply member_In_equiv_F in Hmemy. rewrite Hmemy. reflexivity.
                                 ** apply Hyc. split. apply Hcc'. apply Hcdp'.
                              -- reflexivity.
                              -- right. apply Hc. }

                        { destruct Hy' as [Hy'' [Hy' Hovery']]. symmetry in Hy'. apply Hl2 in Hy'. apply Hy' in Hlyd2. exists ((y, (rev ty, dy)) :: Dcy). split.
                          + apply HyDcy with (py' := rev ty) (dy' := dy) (Dcy := Dcy). reflexivity. apply HDcy.
                          + intros c Hc.
                            assert (Hwmempy: forall (w: node), In w (rev ty ++ [dy]) -> In w (py ++ [dy])).
                            { intros w Hw. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2. rewrite <- app_assoc. apply membership_append_r. simpl. right. apply Hw. }

                            destruct (c =? y) as [|] eqn:Hyc.
                            * apply eqb_eq in Hyc. right. exists (rev ty). exists dy. split.
                              { simpl. rewrite Hyc. rewrite eqb_refl. simpl. reflexivity. }
                              split. apply Hpdy''. split.
                              { apply subpath_still_directed with (w := cy) (l1 := lcyd1) (l3 := py). split. rewrite Hyc. symmetry. apply Hlyd2. apply Hpdy''. } split.
                              { apply subpath_still_acyclic with (w := cy) (l1 := lcyd1) (l3 := py). split. rewrite Hyc. symmetry. apply Hlyd2. apply Hpdy''. } split.
                              { apply no_overlap_non_member. intros w Hw Hw'. destruct Hpdy'' as [_ [_ [_ [Hpdy'' _]]]]. apply no_overlap_non_member with (x := w) in Hpdy''.
                                apply Hpdy''. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2. right. apply membership_append_r. rewrite <- Hyc. apply Hw'. apply Hw. } split.
                              { (* u: HuL. h: Hpdy''. ph11: Hy. [y, lyd, cy]: acyclic Hpdy''. [lcyv2, v]: Hpdy''. *)
                                apply no_overlap_non_member. intros w Hw Hw'.
                                assert (HwL: In w L).
                                { apply collider_descendants_from_assignments_mem with (D := Dh) (G := G) (p' := (h, v, lhv)) (p := py) (d := dy) (c := cy).
                                  - apply subpath_preserves_colliders with (u := x) (l1 := rev lx2) (l2 := rev tlx1). split. symmetry. apply Hlhvrev. left. apply Hpdy.
                                  - split. apply collider_descendants_preserved_for_subpath with (D' := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hpdy. apply Hpdy.
                                  - apply HLh.
                                  - apply Hwmempy. apply Hw'. }
                                destruct Hw as [Hw | Hw].
                                { apply member_In_equiv_F in HuL. apply HuL. rewrite Hw. apply HwL. } destruct Hw as [Hw | Hw].
                                { destruct Hpdy'' as [_ [_ [_ [_ [Hc' _]]]]]. apply no_overlap_non_member with (x := h) in Hc'. apply Hc'. rewrite Hw.
                                  apply Hwmempy. apply Hw'. left. reflexivity. }

                                rewrite <- app_assoc in Hw. rewrite <- app_assoc in Hw. rewrite <- app_assoc in Hw. rewrite app_assoc in Hw. rewrite app_assoc in Hw.
                                rewrite <- app_assoc with (l := ph1) in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                { (* cycle! w ->...ph1,x,lxy1...->y->...rev ty...->w *)
                                  apply membership_splits_list in Hw. destruct Hw as [l1 [l2 Hw]]. apply membership_splits_list in Hw'. destruct Hw' as [l3 [l4 Hw']].
                                  assert (Hcycle: is_directed_path_in_graph (w, w, l2 ++ [y] ++ l3) G = true).
                                  { apply concat_directed_paths. split.
                                    - apply subpath_still_directed with (w := h) (l1 := l1) (l3 := ph1 ++ [x] ++ lxy1). split. apply Hw. apply Hpathcy' with (dy := zh) (py := ph) (l2 := lxy2).
                                      apply Hh'. unfold nodes in *. unfold node in *. rewrite Hx. rewrite Hy''. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                                    - apply subpath_still_directed with (w := cy) (l1 := lcyd1) (l3 := lcyd1 ++ [y] ++ l3). split. reflexivity.
                                      apply Hpathcy' with (dy := dy) (py := py) (l2 := l4). apply Hpdy''. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2. rewrite <- app_assoc. rewrite <- app_assoc.
                                      unfold nodes in *. unfold node in *. rewrite <- Hw'. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
                                  destruct HG as [_ HG]. apply contains_cycle_false_correct with (p := (w, w, l2 ++ [y] ++ l3)) in HG. destruct HG as [HG _]. apply HG. reflexivity.
                                  apply Hcycle. }

                                rewrite <- app_assoc in Hw. rewrite <- app_assoc in Hw. rewrite app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                { destruct Hpdy'' as [_ [_ [Hpdy'' _]]]. apply acyclic_path_count with (x := w) in Hpdy''. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2 in Hpdy''.
                                  apply membership_rev in Hw. simpl in Hw. rewrite <- reverse_list_twice in Hw. apply member_count_at_least_1 in Hw. apply member_count_at_least_1 in Hw'.
                                  rewrite <- app_assoc in Hpdy''. rewrite <- app_assoc in Hpdy''. rewrite app_assoc in Hpdy''. simpl in Hpdy''. unfold nodes in *. unfold node in *. destruct (cy =? w) as [|]. rewrite count_app in Hpdy''. lia. rewrite count_app in Hpdy''. lia.
                                  right. apply Hwmempy. apply Hw'. }
                                { destruct Hpdy'' as [_ [_ [_ [_ [Hc' _]]]]]. apply no_overlap_non_member with (x := w) in Hc'. apply Hc'. apply Hwmempy. apply Hw'.
                                  right. rewrite Hlhvrev. rewrite <- app_assoc. apply membership_append_r. rewrite <- Hcy. rewrite <- app_assoc. rewrite <- app_assoc. right.
                                  simpl. apply membership_append_r. apply Hw. } }

                              { intros c' d' p'. intros [Hcc' Hcdp']. simpl in Hcdp'. rewrite <- Hyc in Hcdp'. rewrite Hcc' in Hcdp'.
                                apply no_overlap_non_member. intros w Hw Hw'.
                                assert (Hc': In c' (find_colliders_in_path (cy, v, lcyv2) G)).
                                { apply collider_subpath_is_exact_assignment in HDcy. unfold is_exact_assignment_for in HDcy.
                                  destruct (member c' (find_colliders_in_path (cy, v, lcyv2) G)) as [|] eqn:Hmem. apply member_In_equiv. apply Hmem.
                                  apply HDcy in Hmem. apply assigned_is_false in Hmem. unfold nodes in *. rewrite Hmem in Hcdp'. discriminate Hcdp'. }
                                rewrite eqb_sym in Hcc'. rewrite Hyc in Hcc'. pose proof Hcc' as Hyc'. apply HyDcy' with (py' := rev ty) (dy' := dy) (D := (y, (rev ty, dy)) :: Dcy) in Hcc'.
                                - destruct Hcc' as [Hcc' | Hcc'].
                                  + simpl in Hcc'. rewrite eqb_sym in Hyc'. rewrite Hyc' in Hcc'. destruct Hcc' as [Hcc' _]. unfold nodes in *. rewrite Hcc' in Hcdp'. inversion Hcdp'.
                                    rewrite <- H3 in Hw. rewrite <- H2 in Hw. (* w = c', so py/dy path overlaps with lhv, contradicts Hpdy'' *)
                                    assert (Hwc': c' = w). { simpl in Hw. destruct Hw as [Hw | [Hw | Hw]]. apply Hw. apply Hw. exfalso. apply Hw. }
                                    destruct Hw' as [Hw' | Hw'].
                                    * rewrite <- Hyc in Hyc'. rewrite Hw' in Hyc'. rewrite Hwc' in Hyc'. rewrite eqb_refl in Hyc'. discriminate Hyc'.
                                    * destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := w) in Hpdy''. apply Hpdy''.
                                      apply Hwmempy. apply Hw'.
                                      assert (Hmemc': In c' lcyv2).
                                      { assert (Hpcyv: is_path_in_graph (cy, v, lcyv2) G = true). { apply subpath_still_path with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite <- app_assoc. rewrite <- app_assoc.
                                          unfold nodes in *. unfold node in *. rewrite Hcy. symmetry. apply Hlhvrev. apply Hlhv. }
                                        apply intermediate_node_in_path with (x := c') in Hpcyv. apply Hpcyv. right. right. apply Hc'. }
                                      rewrite <- Hwc'. right. apply membership_append. rewrite Hlhvrev. apply membership_append_r. simpl. right. rewrite <- Hcy.
                                      apply membership_append_r. simpl. right. apply Hmemc'.
                                  + destruct Hcc' as [p'' [d'' [Hcdp'' Hcc']]]. simpl in Hcdp''. rewrite eqb_sym in Hyc'. rewrite Hyc' in Hcdp''. unfold nodes in *. rewrite Hcdp'' in Hcdp'.
                                    inversion Hcdp'. rewrite H2 in *. rewrite H3 in *. destruct Hcc' as [_ [_ [_ [_ [_ [Hcc' _]]]]]]. apply no_overlap_non_member with (x := w) in Hcc'.
                                    apply Hcc'. apply Hw. right. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2. rewrite <- app_assoc. apply membership_append_r. rewrite <- Hyc. apply Hw'.
                                - reflexivity.
                                - right. apply Hc'. }
                            * unfold nodes in *. rewrite Hcolhv in Hc. destruct Hc as [Hc | Hc]. rewrite Hc in Hyc. rewrite eqb_refl in Hyc. discriminate Hyc.

                              apply HyDcy' with (D := (y, (rev ty, dy)) :: Dcy) (py' := rev ty) (dy' := dy) in Hyc.
                              -- destruct Hyc as [Hyc | Hyc]. left. apply Hyc. right. destruct Hyc as [pc [dc Hyc]]. exists pc. exists dc.

                                 rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split. repeat split; apply Hyc.
                                 intros c' d' p' [Hcc' Hcdp']. simpl in Hcdp'. destruct (y =? c') as [|] eqn:Hyc'.
                                 ** inversion Hcdp'. rewrite <- H3. apply eqb_eq in Hyc'. rewrite <- Hyc'.
                                    apply no_overlap_non_member. intros w Hw Hw'. destruct Hyc as [_ [_ [_ [_ [_ [_ [Hyc _]]]]]]].
                                    apply no_overlap_non_member with (x := w) in Hyc. apply Hyc. apply Hw'. right. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2.
                                    rewrite <- app_assoc. apply membership_append_r. apply Hw.
                                 ** apply Hyc. split. apply Hcc'. apply Hcdp'.
                              -- reflexivity.
                              -- right. apply Hc. }

                     * (* CASE 2C.3.iii: either b = true, so x is not a collider (Hbout) (and not in Z since lhv d-conn)
                          or (ph2 ++ [zh]) doesn't overlap Lx, so using ph2++[z] as x's desc path works *)

                       exists (h :: ph1 ++ [x] ++ rev tlx1).

                       assert (Hcyc': acyclic_path_2 (h, v, ph1 ++ [x] ++ rev tlx1)).
                       { apply concat_paths_acyclic. split. apply Hlhv. split. apply Hcychx.
                         - apply subpath_still_acyclic with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv.
                         - split.
                           + intros Hht. destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. apply Hlhv.
                             apply membership_rev. rewrite H1. apply membership_append. apply membership_rev. apply Hht.
                           + intros Hvph1. apply no_overlap_non_member with (x := v) in Hx''. apply Hx''. rewrite Hx. apply membership_append. apply Hvph1.
                             left. reflexivity.
                         - apply no_overlap_non_member. intros w Hw Hw'. apply no_overlap_non_member with (x := w) in Hx''. apply Hx''. rewrite Hx. apply membership_append. apply Hw'.
                           right. apply membership_rev. apply Hw. }

                       assert (Hpath'': is_path_in_graph (h, v, ph1 ++ [x] ++ rev tlx1) G = true).
                       { apply concat_paths_still_a_path. split.
                         - apply directed_path_is_path. simpl in Hdir. apply split_and_true in Hdir. apply Hdir.
                         - apply subpath_still_path with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }

                       assert (Hcycuhv: acyclic_path_2 (u, v, h :: ph1 ++ [x] ++ rev tlx1)).
                       { apply acyclic_path_correct_2. simpl. rewrite Hhu.
                         apply split_and_true. split.
                         - rewrite <- app_assoc. simpl. rewrite <- append_vs_concat. apply negb_true_iff. apply member_In_equiv_F. intros Hu. apply membership_append_or in Hu.
                           destruct Hu as [Hu | Hu]. (* ph1 ++ [x] because cycle, rev tlx1 ++ [v] because Hulhv *)
                           + apply member_In_equiv_F in Huph. apply Huph. rewrite Hx. rewrite <- append_vs_concat. apply membership_append. apply Hu.
                           + apply membership_append_or in Hu. destruct Hu as [Hu | Hu].
                             * apply member_In_equiv_F in Hulhv. apply Hulhv. apply membership_rev. rewrite H1. apply membership_append. apply membership_rev. apply Hu.
                             * destruct Hcyc as [Hcyc _]. apply Hcyc. destruct Hu as [Hu | Hu]. symmetry. apply Hu. exfalso. apply Hu.
                         - apply acyclic_path_correct_2 in Hcyc'. simpl in Hcyc'. rewrite <- app_assoc in Hcyc'. simpl in Hcyc'. rewrite <- app_assoc. simpl. apply Hcyc'. }

                       split. apply Hcycuhv.

                       assert (Hhmed: In h (find_mediators_in_path (u, v, h :: ph1 ++ [x] ++ rev tlx1) G)).
                       { apply mediator_means_edge_out with (c := h) (G := G) in Hx.
                         destruct ph1 as [| hph11 tph11].
                         * apply mediators_vs_edges_in_path. exists u. exists x. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                           -- apply Huh.
                           -- destruct Hx as [Hx _]. apply Hx. reflexivity.
                         * apply mediators_vs_edges_in_path. exists u. exists hph11. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                           -- apply Huh.
                           -- destruct Hx as [_ Hx]. apply Hx with (tly1 := tph11). reflexivity.
                         * apply Hh'. }

                       assert (Hxmed: b = true -> In x (find_mediators_in_path (concat h x v ph1 (rev tlx1)) G)).
                       { intros Hb. rewrite Hb in *.
                         apply mediator_end_means_edge_in with (c := h) (G := G) in Hx.
                         assert (Hbout': path_out_of_node x (x, v, rev tlx1) G = Some true).
                         { apply superpath_preserves_path_out_of_node with (w := h) (l1 := rev lx2) (l3 := lhv). symmetry. apply Hlhvrev.
                           apply Hbout. apply Hlhv. left. reflexivity. }
                         destruct (rev ph1) as [| hph11 tph11] eqn:Hph1.
                         ++ assert (Hph1': ph1 = []). { rewrite reverse_list_twice with (l := ph1). rewrite Hph1. reflexivity. } rewrite Hph1' in *.
                            apply mediators_vs_edges_in_path. exists h.
                            destruct (rev tlx1) as [| hx1 tx1] eqn:Htlx1.
                            ** exists v. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                               -- apply Hx. reflexivity.
                               -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, v) G) as [|] eqn:Hedge.
                                  apply edge_in_graph_then_is_edge. apply HG. apply Hedge. unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'.
                            ** exists hx1. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                               -- apply Hx. reflexivity.
                               -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, hx1) G) as [|] eqn:Hedge.
                                  apply edge_in_graph_then_is_edge. apply HG. apply Hedge. unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'.
                         ++ assert (Hph1': ph1 = rev tph11 ++ [hph11]). { rewrite reverse_list_twice with (l := ph1). rewrite Hph1. reflexivity. } rewrite Hph1' in *.
                            apply mediators_vs_edges_in_path. exists hph11.
                            destruct (rev tlx1) as [| hx1 tx1] eqn:Htlx1.
                            ** exists v. split. apply sublist_breaks_down_list. exists (h :: rev tph11). exists []. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. left. split.
                               -- apply Hx with (hly1 := hph11) (tly1 := tph11). rewrite reverse_list_append. rewrite <- reverse_list_twice. reflexivity.
                               -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, v) G) as [|] eqn:Hedge.
                                  apply edge_in_graph_then_is_edge. apply HG. apply Hedge. unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'.
                            ** exists hx1. split. apply sublist_breaks_down_list. exists (h :: rev tph11). exists (tx1 ++ [v]). rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. left. split.
                               -- apply Hx with (hly1 := hph11) (tly1 := tph11). rewrite reverse_list_append. rewrite <- reverse_list_twice. reflexivity.
                               -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, hx1) G) as [|] eqn:Hedge.
                                  apply edge_in_graph_then_is_edge. apply HG. apply Hedge. unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'.
                         ++ apply Hh'. }

                       assert (Hxcol: b = false -> In x (find_colliders_in_path (concat h x v ph1 (rev tlx1)) G)).
                       { intros Hb. rewrite Hb in *.
                         apply mediator_end_means_edge_in with (c := h) (G := G) in Hx.
                         assert (Hbout': path_out_of_node x (x, v, rev tlx1) G = Some false).
                         { apply superpath_preserves_path_out_of_node with (w := h) (l1 := rev lx2) (l3 := lhv). symmetry. apply Hlhvrev.
                           apply Hbout. apply Hlhv. left. reflexivity. }
                         destruct (rev ph1) as [| hph11 tph11] eqn:Hph1.
                         ++ assert (Hph1': ph1 = []). { rewrite reverse_list_twice with (l := ph1). rewrite Hph1. reflexivity. } rewrite Hph1' in *.
                            apply colliders_vs_edges_in_path. exists h.
                            destruct (rev tlx1) as [| hx1 tx1] eqn:Htlx1.
                            ** exists v. split. simpl. repeat rewrite eqb_refl. reflexivity. split.
                               -- apply Hx. reflexivity.
                               -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, v) G) as [|] eqn:Hedge.
                                  unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'. simpl in Hpath''. destruct G as [V E]. apply split_and_true in Hpath''. destruct Hpath'' as [_ Hpath''].
                                  rewrite <- edge_in_graph_equiv in Hedge. rewrite Hedge in Hpath''. simpl in Hpath''. rewrite andb_comm in Hpath''. simpl in Hpath''. simpl. apply Hpath''. apply HG.
                            ** exists hx1. split. simpl. repeat rewrite eqb_refl. reflexivity. split.
                               -- apply Hx. reflexivity.
                               -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, hx1) G) as [|] eqn:Hedge.
                                  unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'. simpl in Hpath''. destruct G as [V E]. apply split_and_true in Hpath''. destruct Hpath'' as [_ Hpath''].
                                  apply split_and_true in Hpath''. destruct Hpath'' as [Hpath'' _].
                                  rewrite <- edge_in_graph_equiv in Hedge. rewrite Hedge in Hpath''. simpl in Hpath''. simpl. apply Hpath''. apply HG.
                         ++ assert (Hph1': ph1 = rev tph11 ++ [hph11]). { rewrite reverse_list_twice with (l := ph1). rewrite Hph1. reflexivity. } rewrite Hph1' in *.
                            apply colliders_vs_edges_in_path. exists hph11.
                            destruct (rev tlx1) as [| hx1 tx1] eqn:Htlx1.
                            ** exists v. split. apply sublist_breaks_down_list. exists (h :: rev tph11). exists []. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. split.
                               -- apply Hx with (hly1 := hph11) (tly1 := tph11). rewrite reverse_list_append. rewrite <- reverse_list_twice. reflexivity.
                               -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, v) G) as [|] eqn:Hedge.
                                  unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'.
                                  assert (Hpath''': is_path_in_graph (hph11, v, [x]) G = true). { apply subpath_still_path with (w := h) (l1 := rev tph11) (l3 := rev tph11 ++ [hph11] ++ [x]). split. reflexivity. rewrite <- app_assoc in Hpath''. apply Hpath''. }
                                  clear Hpath''. simpl in Hpath'''. destruct G as [V E]. apply split_and_true in Hpath'''. destruct Hpath''' as [_ Hpath''].
                                  rewrite <- edge_in_graph_equiv in Hedge. rewrite Hedge in Hpath''. simpl in Hpath''. rewrite andb_comm in Hpath''. simpl in Hpath''. simpl. apply Hpath''. apply HG.
                            ** exists hx1. split. apply sublist_breaks_down_list. exists (h :: rev tph11). exists (tx1 ++ [v]). rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. split.
                               -- apply Hx with (hly1 := hph11) (tly1 := tph11). rewrite reverse_list_append. rewrite <- reverse_list_twice. reflexivity.
                               -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, hx1) G) as [|] eqn:Hedge.
                                  unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'.
                                  assert (Hpath''': is_path_in_graph (hph11, v, [x] ++ hx1 :: tx1) G = true). { apply subpath_still_path with (w := h) (l1 := rev tph11) (l3 := rev tph11 ++ [hph11] ++ [x] ++ hx1 :: tx1). split. reflexivity. rewrite <- app_assoc in Hpath''. apply Hpath''. }
                                  clear Hpath''. simpl in Hpath'''. destruct G as [V E]. apply split_and_true in Hpath'''. destruct Hpath''' as [_ Hpath''].
                                  apply split_and_true in Hpath''. destruct Hpath'' as [Hpath'' _].
                                  rewrite <- edge_in_graph_equiv in Hedge. rewrite Hedge in Hpath''. simpl in Hpath''. simpl. apply Hpath''. apply HG.
                         ++ apply Hh'. }

                       split.
                       { apply d_connected_cat. apply HG. apply Hcycuhv. apply concat_d_connected_paths. apply HG. apply Hpath''. split.
                         - apply Hconncy with (p := ph) (d := zh) (l2 := ph2). apply Hx. split. apply Hh'. split. apply Hh'. apply Hh'.
                         - split. apply subpath_still_d_connected_gen with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv.
                           apply Hcyc'.
                         - destruct b as [|] eqn:Hb. (* HbLx: either x is not a collider (Houtx), so not in Z, or collider with ph2++[zh] desc path. *)
                           + left. apply and_comm. split.
                             * destruct Hlhv as [[Hcyclhv Hconnlhv] Hlhv]. apply intermediate_node_in_path with (x := x) in Hlhv. assert (Hxlhv: In x lhv). { rewrite Hlhvrev. apply membership_append_r. left. reflexivity. } apply Hlhv in Hxlhv.
                               destruct Hxlhv as [Hhh | [Hhh | Hhh]].
                               -- destruct Hconnlhv as [Hconnlhv _]. apply no_overlap_non_member with (x := x) in Hconnlhv. apply Hconnlhv. apply Hhh.
                               -- destruct Hconnlhv as [_ [Hconnlhv _]]. apply no_overlap_non_member with (x := x) in Hconnlhv. apply Hconnlhv. apply Hhh.
                               -- (* Hhh contradicts Hbout *) apply path_out_not_collider in Hbout. intros F. apply Hbout. apply Hhh. apply HG. apply Hcyclhv.
                             * apply Hxmed. reflexivity.
                           + right. right. apply and_comm. split.
                             * apply overlap_has_member_in_common. exists zh. symmetry in Hx. apply Hl2 in Hx. destruct (rev ph2) as [| hph2 tph2] eqn:Hph2.
                               -- assert (Hxzh: x = zh /\ ph1 = ph). { apply Hx. apply Hph2. } destruct Hxzh as [Hxzh _]. split. rewrite Hxzh. unfold find_descendants. left. reflexivity.
                                  apply Hh'.
                               -- assert (Hxzh: zh = hph2 /\ ph = ph1 ++ [x] ++ rev tph2). { apply Hx. apply Hph2. } destruct Hxzh as [_ Hxzh]. split. apply find_descendants_correct.
                                  right. exists (x, zh, rev tph2). split. apply subpath_still_directed with (w := h) (l1 := ph1) (l3 := ph). split. symmetry. apply Hxzh. apply Hh'. apply path_start_end_refl. apply Hh'.
                             * apply Hxcol. reflexivity.
                         - left. apply and_comm. split.
                           + apply HhZ.
                           + apply Hhmed. }

                       split.
                       { simpl. simpl in Hdir. apply split_and_true in Hdir. destruct Hdir as [Hdir _]. rewrite Hdir. simpl. destruct G as [V E]. apply Hpath''. } split.
                       { intros w Hw. (* [h, x): exists zh, ph, not in Z. x: did not change. tlx1: did not change *)
                         assert (Hwu: w =? u = false). { apply Houtwu with (x' := v) (l1 := ph1 ++ [x] ++ rev tlx1) (l2 := t). apply Hw. }
                         assert (Hwv: w =? v = false). { apply Houtwv with (x' := u) (l1 := h :: ph1 ++ [x] ++ rev tlx1) (l2 := h :: t). apply Hcyc. apply Hw. }
                         rewrite <- node_in_path_cat in Hw. rewrite <- node_in_path_cat in Hw. 2: { apply Hwu. } 2: { apply Hwu. }
                         rewrite path_out_of_node_cat. 2: { apply Hwu. }

                         destruct (w =? h) as [|] eqn:Hwh.
                         - apply eqb_eq in Hwh. rewrite Hwh. split.
                           + left. exists zh. exists ph. split. apply Hh'. split. apply Hh'. apply HhZ.
                           + intros H. apply HhZ.
                         - destruct (member w ph1) as [|] eqn:Hwph1.
                           + assert (Houtph1: path_out_of_node w (h, v, ph1 ++ [x] ++ rev tlx1) G = path_out_of_node w (u, x, h :: ph1) G).
                             { rewrite path_out_of_node_cat. 2: { apply Hwu. } assert (exists (b: bool), path_out_of_node w (h, x, ph1) G = Some b).
                               { apply path_out_of_node_mem_2. right. apply member_In_equiv. apply Hwph1. }
                               destruct H as [bw Hbw]. unfold nodes in *. unfold node in *. rewrite Hbw. apply subpath_preserves_path_out_of_node_2 with (u := x) (l1 := ph1) (l2 := rev tlx1). split. reflexivity.
                               apply Hbw. }
                             unfold nodes in *. unfold node in *. rewrite Houtph1. apply Houtwph1 with (ph2' := ph2). apply member_In_equiv. apply Hwph1.
                             apply Hx.
                           + assert (Hwcy: In w (x :: rev tlx1)).
                             { assert (Hwmem: In w (u :: h :: ph1 ++ [x] ++ rev tlx1)).
                               { destruct Hw as [[Hw _] | Hw].
                                 - rewrite node_in_path_equiv in Hw. right. apply member_In_equiv in Hw. rewrite app_comm_cons in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                   apply Hw. destruct Hw as [Hw | Hw]. rewrite Hw in Hwv. rewrite eqb_refl in Hwv. discriminate Hwv. exfalso. apply Hw.
                                 - destruct Hw as [bw [_ Hw]]. apply path_out_of_node_mem_gen with (G := G) (v := v). exists (negb bw). apply Hw. }
                               apply member_In_equiv in Hwmem. simpl in Hwmem. rewrite eqb_sym in Hwmem. rewrite Hwu in Hwmem. rewrite eqb_sym in Hwmem. rewrite Hwh in Hwmem.
                               apply member_In_equiv in Hwmem. apply membership_append_or in Hwmem. destruct Hwmem as [Hwmem | Hwmem]. apply member_In_equiv in Hwmem. rewrite Hwmem in Hwph1. discriminate Hwph1.
                               apply Hwmem. }
                              specialize Houtwcy with (cy := x) (l1 := ph1) (lcy2 := rev tlx1).
                              apply Houtwcy with (lcy1 := rev lx2).
                              -- apply Hwcy.
                              -- apply Hlhvrev.
                              -- apply Hcyc'.
                              -- rewrite path_out_of_node_cat in Hw. rewrite path_out_of_node_cat in Hw. apply Hw. apply Hwu. apply Hwu. }

                       (* Dx for subpath of colliders after x (if x is not a collider). else, either x = zh, so Dx, or (tph2++zh) :: Dx *)
                       destruct b as [|] eqn:Hb.
                       { (* x is not a collider *) exists Dx.
                         assert (Hcolhv: find_colliders_in_path (u, v, h :: ph1 ++ [x] ++ rev tlx1) G = find_colliders_in_path (x, v, rev tlx1) G).
                         { assert (Hcoluv: [] ++ h :: ph1 ++ [x] ++ rev tlx1 = h :: ph1 ++ [x] ++ rev tlx1).
                            { reflexivity. }
                            apply subpath_preserves_colliders_2 with (w := u) (v := v) (G := G) in Hcoluv. destruct Hcoluv as [Hcoluv | Hcoluv].
                            - (* h is a mediator, not a collider *)
                              apply if_mediator_then_not_confounder_path in Hhmed. exfalso. destruct Hhmed as [_ Hhmed]. apply Hhmed. unfold concat. unfold nodes in *.
                              unfold node in *. simpl in Hcoluv. simpl. rewrite Hcoluv. left. reflexivity. apply HG. apply Hcycuhv.
                            - unfold nodes in *. rewrite Hcoluv.

                              assert (Hcolhv: ph1 ++ [x] ++ rev tlx1 = ph1 ++ [x] ++ rev tlx1).
                              { reflexivity. }
                              assert (Hcoluy: find_colliders_in_path (u, x, h :: ph1) G = []). { apply Hcolph1 with (ph2' := ph2). apply Hx. }
                              assert (Hcolhy: find_colliders_in_path (h, x, ph1) G = []). { destruct (find_colliders_in_path (h, x, ph1) G) as [| ch ct] eqn:Hhy. reflexivity.
                                assert (Hch: In ch (find_colliders_in_path (u, x, h :: ph1) G)). { apply subpath_preserves_colliders with (u := h) (l1 := []) (l2 := ph1). split. reflexivity. left. simpl. simpl in Hhy. rewrite Hhy. left. reflexivity. }
                                rewrite Hcoluy in Hch. exfalso. apply Hch. }

                              apply subpath_preserves_colliders_2 with (w := h) (u := x) (v := v) (G := G) in Hcolhv. destruct Hcolhv as [Hcolhv | Hcolhv].
                              + (* x is a mediator, not a collider *)
                                apply if_mediator_then_not_confounder_path in Hxmed. exfalso. destruct Hxmed as [_ Hxmed]. apply Hxmed. unfold concat. unfold nodes in *.
                                unfold node in *. simpl in Hcolhv. simpl. rewrite Hcolhv. apply membership_append_r. left. reflexivity. apply HG. apply Hcyc'. reflexivity.
                              + unfold node in *. simpl in Hcolhv. simpl. rewrite Hcolhv. simpl in Hcolhy. rewrite Hcolhy. simpl. reflexivity. }

                         unfold nodes in *. rewrite Hcolhv. split. apply collider_subpath_is_exact_assignment with (D := Dh). apply HDx.
                         intros c Hc. unfold nodes in *. rewrite Hcolhv in Hc.
                         assert (Hc': In c (find_colliders_in_path (h, v, lhv) G)).
                         { apply subpath_preserves_colliders with (u := x) (l1 := rev lx2) (l2 := rev tlx1). split. symmetry. apply Hlhvrev. left. apply Hc. }
                         pose proof Hc' as Hc''. destruct HDh as [HDh HDh']. apply HDh' in Hc'. destruct Hc' as [Hc' | Hc'].
                         - left. split. simpl. rewrite <- collider_descendants_preserved_for_subpath_3 with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G).
                           apply Hc'. apply HDx. apply Hc. apply Hc'.
                         - right. destruct Hc' as [pc [dc Hc']]. exists pc. exists dc. split. rewrite <- collider_descendants_preserved_for_subpath_3 with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G).
                           apply Hc'. apply HDx. apply Hc. split. apply Hc'. split. apply Hc'. split. apply Hc'. split. apply Hc'. split.
                           + (* u: HuL. h: Hc', lhv. ph1: Hoverph1. [x,v]: Hc', lhv. *)
                             apply no_overlap_non_member. intros w Hw Hw'.
                             assert (HwL: In w L).
                             { apply collider_descendants_from_assignments_mem with (D := Dh) (G := G) (p' := (h, v, lhv)) (p := pc) (d := dc) (c := c). apply Hc''. split. apply Hc'.
                               destruct (dc =? c) as [|] eqn:Hdcc. apply eqb_eq in Hdcc. destruct Hc' as [_ [_ [_ [[Hc' _] _]]]]. exfalso. apply Hc'. symmetry. apply Hdcc. reflexivity.
                               apply HLh. apply Hw'. }
                             destruct Hw as [Hw | Hw].

                             { apply member_In_equiv_F in HuL. apply HuL. rewrite Hw. apply HwL. } destruct Hw as [Hw | Hw].
                             { destruct Hc' as [_ [_ [_ [_ [_ [Hc' _]]]]]]. apply no_overlap_non_member with (x := h) in Hc'. apply Hc'. rewrite Hw. apply Hw'. left. reflexivity. }
                             rewrite <- app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].

                             { (* w is in Lx, so Hoverph1 contradicts *)
                               assert (HLxy: exists (l1' l2': nodes), Lx = l1' ++ pc ++ [dc] ++ l2').
                               { apply get_collider_descendants_from_assignments_contains_path with (D := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G) (c := c).
                                 apply HLx. split.
                                 - apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hc'. apply Hc.
                                 - apply eqb_neq. destruct Hc' as [_ [_ [_ [[Hc' _] _]]]]. apply Hc'.
                                 - apply Hc. }

                               assert (HwLx: In w Lx).
                               { destruct HLxy as [Lx1' [Lx2' HLxy]]. rewrite HLxy. apply membership_append_r. rewrite app_assoc. apply membership_append. apply Hw'. }
                               apply no_overlap_non_member with (x := w) in Hoverph1. apply Hoverph1. apply Hw. apply HwLx. }

                             { destruct Hc' as [_ [_ [_ [_ [_ [Hc' _]]]]]]. apply no_overlap_non_member with (x := w) in Hc'. apply Hc'. apply Hw'. right. rewrite Hlhvrev. rewrite <- app_assoc. apply membership_append_r.  apply Hw. }

                           + intros c' d' p' [Hcc' Hcdp'].
                             apply Hc'. split. apply Hcc'. apply collider_descendants_preserved_for_subpath with (D' := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hcdp'. }

                       { assert (Hcolhv: find_colliders_in_path (u, v, h :: ph1 ++ [x] ++ rev tlx1) G = x :: (find_colliders_in_path (x, v, rev tlx1) G)).
                         { assert (Hcoluv: [] ++ h :: ph1 ++ [x] ++ rev tlx1 = h :: ph1 ++ [x] ++ rev tlx1).
                            { reflexivity. }
                            apply subpath_preserves_colliders_2 with (w := u) (v := v) (G := G) in Hcoluv. destruct Hcoluv as [Hcoluv | Hcoluv].
                            - (* h is a mediator, not a collider *)
                              apply if_mediator_then_not_confounder_path in Hhmed. exfalso. destruct Hhmed as [_ Hhmed]. apply Hhmed. unfold concat. unfold nodes in *.
                              unfold node in *. simpl in Hcoluv. simpl. rewrite Hcoluv. left. reflexivity. apply HG. apply Hcycuhv.
                            - unfold nodes in *. rewrite Hcoluv.

                              assert (Hcolhv: ph1 ++ [x] ++ rev tlx1 = ph1 ++ [x] ++ rev tlx1).
                              { reflexivity. }
                              assert (Hcoluy: find_colliders_in_path (u, x, h :: ph1) G = []). { apply Hcolph1 with (ph2' := ph2). apply Hx. }
                              assert (Hcolhy: find_colliders_in_path (h, x, ph1) G = []). { destruct (find_colliders_in_path (h, x, ph1) G) as [| ch ct] eqn:Hhy. reflexivity.
                                assert (Hch: In ch (find_colliders_in_path (u, x, h :: ph1) G)). { apply subpath_preserves_colliders with (u := h) (l1 := []) (l2 := ph1). split. reflexivity. left. simpl. simpl in Hhy. rewrite Hhy. left. reflexivity. }
                                rewrite Hcoluy in Hch. exfalso. apply Hch. }

                              apply subpath_preserves_colliders_2 with (w := h) (u := x) (v := v) (G := G) in Hcolhv. destruct Hcolhv as [Hcolhv | Hcolhv].
                              + unfold node in *. simpl in Hcolhv. simpl. rewrite Hcolhv. simpl in Hcolhy. rewrite Hcolhy. simpl. reflexivity.
                              + (* x is a collider, so should be included in Hcolhv *)
                                unfold concat in Hxcol.
                                unfold nodes in *. unfold node in *. rewrite <- append_vs_concat in Hxcol. rewrite <- app_assoc in Hxcol.
                                rewrite Hcolhv in Hxcol. apply membership_append_or in Hxcol.
                                destruct Hxcol as [Hxcol | Hxcol]. (* contradicts acyclic *)
                                * assert (Hphy: is_path_in_graph (h, x, ph1) G = true). { apply directed_path_is_path. simpl in Hdir. apply split_and_true in Hdir. apply Hdir. }
                                  apply intermediate_node_in_path with (x := x) in Hphy.
                                  assert (Hyph11: In x ph1). { apply Hphy. right. right. apply Hxcol. }
                                  exfalso. destruct Hcychx as [_ [_ [Hchy _]]]. apply Hchy. apply Hyph11.
                                * assert (Hphy: is_path_in_graph (x, v, rev tlx1) G = true). { apply subpath_still_path with (w := h) (l1 := ph1) (l3 := ph1 ++ [x] ++ rev tlx1).
                                    split. reflexivity. apply Hpath''. } apply intermediate_node_in_path with (x := x) in Hphy.
                                  assert (Hyph11: In x (rev tlx1)). { apply Hphy. right. right. apply Hxcol. }
                                  assert (Hchy: acyclic_path_2 (x, v, rev tlx1)). { apply subpath_still_acyclic with (w := h) (l1 := ph1) (l3 := ph1 ++ [x] ++ rev tlx1).
                                    split. reflexivity. apply Hcyc'. } exfalso. destruct Hchy as [_ [Hchy _]]. apply Hchy. apply Hyph11.
                                * reflexivity. }

                         unfold nodes in *. rewrite Hcolhv.

                         assert (HyDcy': forall (py': nodes) (dy': node) (D: assignments (nodes * node)), D = (x, (py', dy')) :: Dx
                                       -> forall c : node,
                                          (c =? x) = false
                                           -> In c (x :: find_colliders_in_path (x, v, rev tlx1) G)
                                           -> get_assigned_value D c = Some ([], c) /\ In c Z \/
                                               (exists (p : list node) (d : node),
                                                  get_assigned_value D c = Some (p, d) /\
                                                  In d Z /\
                                                  is_directed_path_in_graph (c, d, p) G = true /\
                                                  acyclic_path_2 (c, d, p) /\
                                                  overlap (c :: p) Z = false /\
                                                  overlap (p ++ [d]) (u :: (h :: ph1 ++ [x] ++ rev tlx1) ++ [v]) = false
                                                  /\ (forall (c' d' : node) (p' : list node),
                                                     (c =? c') = false /\ get_assigned_value Dx c' = Some (p', d') ->
                                                     overlap (c :: p ++ [d]) (c' :: p' ++ [d']) = false))).
                        { intros py'' dy'' D HDeq c Hyc Hc.
                          destruct Hc as [Hc | Hc]. rewrite Hc in Hyc. rewrite eqb_refl in Hyc. discriminate Hyc.
                          (* induction case *) assert (Hc': In c (find_colliders_in_path (h, v, lhv) G)).
                          { apply subpath_preserves_colliders with (u := x) (l1 := rev lx2) (l2 := rev tlx1). split. symmetry. apply Hlhvrev. left. apply Hc. }
                          pose proof Hc' as Hc''. destruct HDh as [HDh HDh']. apply HDh' in Hc'. rewrite HDeq in *. destruct Hc' as [Hc' | Hc'].
                          -- left. split. simpl. rewrite eqb_sym. rewrite Hyc. rewrite <- collider_descendants_preserved_for_subpath_3 with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G).
                             apply Hc'. apply HDx. apply Hc. apply Hc'.
                          -- right. destruct Hc' as [pc [dc Hc']]. exists pc. exists dc. split. simpl. rewrite eqb_sym. rewrite Hyc. simpl. rewrite <- collider_descendants_preserved_for_subpath_3 with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G).
                             apply Hc'. apply HDx. apply Hc. split. apply Hc'. split. apply Hc'. split. apply Hc'. split. apply Hc'.

                             repeat split.
                             ++ (* u: HuL. h: HDh'. ph1: Hoverph1. x: HDh'. (x, y): Hy. [y, lcyd1]: HDh' (desc path of cy). [cy, v]: HDh'. *) apply no_overlap_non_member. intros w Hw Hw'.
                                assert (HwL: In w L).
                                { apply collider_descendants_from_assignments_mem with (D := Dh) (G := G) (p' := (h, v, lhv)) (p := pc) (d := dc) (c := c). apply Hc''. split. apply Hc'.
                                  destruct (dc =? c) as [|] eqn:Hdcc. apply eqb_eq in Hdcc. destruct Hc' as [_ [_ [_ [[Hc' _] _]]]]. exfalso. apply Hc'. symmetry. apply Hdcc. reflexivity.
                                  apply HLh. apply Hw'. }
                                destruct Hw as [Hw | Hw].
                                { apply member_In_equiv_F in HuL. apply HuL. rewrite Hw. apply HwL. } destruct Hw as [Hw | Hw].
                                { destruct Hc' as [_ [_ [_ [_ [_ [Hc' _]]]]]]. apply no_overlap_non_member with (x := h) in Hc'. apply Hc'. rewrite Hw. apply Hw'. left. reflexivity. }
                                rewrite <- app_assoc in Hw. apply membership_append_or in Hw.

                                destruct Hw as [Hw | Hw].
                                { (* w is in Lx, so Hoverph1 contradicts *)
                                  assert (HLxy: exists (l1' l2': nodes), Lx = l1' ++ pc ++ [dc] ++ l2').
                                  { apply get_collider_descendants_from_assignments_contains_path with (D := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G) (c := c).
                                    apply HLx. split.
                                    - apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hc'. apply Hc.
                                    - apply eqb_neq. destruct Hc' as [_ [_ [_ [[Hc' _] _]]]]. apply Hc'.
                                    - apply Hc. }

                                  assert (HwLx: In w Lx).
                                  { destruct HLxy as [Lx1' [Lx2' HLxy]]. rewrite HLxy. apply membership_append_r. rewrite app_assoc. apply membership_append. apply Hw'. }
                                  apply no_overlap_non_member with (x := w) in Hoverph1. apply Hoverph1. apply Hw. apply HwLx. }

                                { destruct Hc' as [_ [_ [_ [_ [_ [Hc' _]]]]]]. apply no_overlap_non_member with (x := w) in Hc'. apply Hc'. apply Hw'. right. rewrite Hlhvrev. rewrite <- app_assoc. apply membership_append_r. apply Hw. }

                             ++ intros c' d' p' [Hcc' Hcdp'].
                                apply Hc'. split. apply Hcc'. apply collider_descendants_preserved_for_subpath with (D' := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hcdp'. }


                         simpl in HbLx. destruct (rev ph2) as [| hph2 tph2] eqn:Hph2.
                         -- (* x = zh *) exists ((x, ([], x)) :: Dx). split.
                            + apply HyDcy with (py' := []) (dy' := x) (Dcy := Dx). reflexivity. apply HDx.
                            + intros c Hc. destruct (c =? x) as [|] eqn:Hyc.
                              * apply eqb_eq in Hyc. left. split. simpl. rewrite Hyc. rewrite eqb_refl. reflexivity. rewrite Hyc. symmetry in Hx.
                                apply Hl2 in Hx. apply Hx in Hph2. destruct Hph2 as [Hph2 _]. rewrite Hph2. apply Hh'.
                              * apply HyDcy' with (D := (x, ([], x)) :: Dx) (py' := []) (dy' := x) in Hyc.
                                ++ destruct Hyc as [Hyc | Hyc]. left. apply Hyc. right. destruct Hyc as [pc [dc Hyc]]. exists pc. exists dc.

                                   rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split. repeat split; apply Hyc.
                                   intros c' d' p' [Hcc' Hcdp']. simpl in Hcdp'. destruct (x =? c') as [|] eqn:Hyc'.
                                   ** inversion Hcdp'. rewrite <- H3. apply eqb_eq in Hyc'. rewrite <- Hyc'. simpl.
                                      rewrite <- Hyc' in Hcc'. rewrite eqb_sym in Hcc'. rewrite Hcc'. apply overlap_flip. simpl.
                                      assert (Hmemy: ~In x (pc ++ [dc])).
                                      { intros F. destruct Hyc as [_ [_ [_ [_ [_ [Hyc _]]]]]]. apply no_overlap_non_member with (x := x) in Hyc. apply Hyc. apply F.
                                        right. right. rewrite <- app_assoc. apply membership_append_r. simpl. left. reflexivity. } 
                                      apply member_In_equiv_F in Hmemy. rewrite Hmemy. reflexivity.
                                   ** apply Hyc. split. apply Hcc'. apply Hcdp'.
                                ++ reflexivity.
                                ++ unfold nodes in *. rewrite Hcolhv in Hc. apply Hc.


                         -- (* use desc path, since no overlap with Lx *) simpl in HbLx. exists ((x, (rev tph2, zh)) :: Dx). split.
                            + apply HyDcy with (py' := rev tph2) (dy' := zh) (Dcy := Dx). reflexivity. apply HDx.
                            + intros c Hc.
                              assert (Hph2': ph2 = rev tph2 ++ [hph2]). { rewrite reverse_list_twice with (l := ph2). rewrite Hph2. simpl. reflexivity. }
                              symmetry in Hx. apply Hl2 in Hx. apply Hx in Hph2.
                              assert (Hoverx: forall (c' d' : node) (p' : list node),
                                                (x =? c') = false /\ get_assigned_value ((x, (rev tph2, zh)) :: Dx) c' = Some (p', d') ->
                                                overlap (x :: rev tph2 ++ [zh]) (c' :: p' ++ [d']) = false).
                              { intros c' d' p'. intros [Hcc' Hcdp']. simpl in Hcdp'. rewrite Hcc' in Hcdp'.
                                  apply no_overlap_non_member. intros w Hw Hw'.
                                  assert (Hc': In c' (find_colliders_in_path (x, v, rev tlx1) G)).
                                  { apply collider_subpath_is_exact_assignment in HDx. unfold is_exact_assignment_for in HDx.
                                    destruct (member c' (find_colliders_in_path (x, v, rev tlx1) G)) as [|] eqn:Hmem. apply member_In_equiv. apply Hmem.
                                    apply HDx in Hmem. apply assigned_is_false in Hmem. unfold nodes in *. unfold node in *. rewrite Hmem in Hcdp'. discriminate Hcdp'. }
                                  (* w can't equal c' since (ph,zh) doesn't overlap with lhv. w can't be in (p'++[d']) since overlap ph2 Lx = false (HbLx) *)
                                  assert (Hcw: c' = w -> False).
                                  { intros Hcw. assert (Hpxv: is_path_in_graph (x, v, rev tlx1) G = true). { apply subpath_still_path with (w := h) (l1 := ph1) (l3 := ph1 ++ [x] ++ rev tlx1). split. reflexivity. apply Hpath''. }
                                    apply intermediate_node_in_path with (x := c') in Hpxv.
                                    assert (Hwmem: In c' (rev tlx1)). { apply Hpxv. right. right. apply Hc'. }
                                    apply no_overlap_non_member with (x := c') in Hx''. apply Hx''. destruct Hph2 as [_ Hph2]. rewrite Hph2. rewrite <- app_assoc. apply membership_append_r. rewrite Hcw. apply Hw'.
                                    right. apply membership_rev. apply Hwmem. }
                                  destruct Hw as [Hw | Hw].
                                  - apply Hcw. apply Hw.
                                  - assert (Hc'': In c' (find_colliders_in_path (h, v, lhv) G)). { apply subpath_preserves_colliders with (u := x) (l1 := rev lx2) (l2 := rev tlx1). split. symmetry. apply Hlhvrev. left. apply Hc'. }
                                    apply HDh in Hc''. destruct Hc'' as [Hc'' | Hc''].
                                    + destruct Hc'' as [Hc'' HcZ]. rewrite collider_descendants_preserved_for_subpath_3 with (D' := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G) in Hc''.
                                      unfold nodes in *. unfold node in *. rewrite Hc'' in Hcdp'. inversion Hcdp'. rewrite <- H2 in Hw. rewrite <- H3 in Hw.
                                      (* c' = w *) apply Hcw. destruct Hw as [Hw | Hw]. apply Hw. exfalso. apply Hw. apply HDx. apply Hc'.
                                    + destruct Hc'' as [p'' [d'' [Hc'' Hc''']]]. rewrite collider_descendants_preserved_for_subpath_3 with (D' := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G) in Hc''.
                                      unfold nodes in *. unfold node in *. rewrite Hc'' in Hcdp'. inversion Hcdp'. rewrite H2 in *. rewrite H3 in *.

                                      assert (HcLx: In w Lx).
                                      { apply collider_descendants_from_assignments_mem with (D := Dx) (G := G) (p' := (x, v, rev tlx1)) (p := p') (d := d') (c := c').
                                        apply Hc'. split. apply Hc''. destruct Hc''' as [_ [_ [[Hc''' _] _]]]. apply eqb_neq in Hc'''.
                                        rewrite eqb_sym. apply Hc'''. apply HLx. apply Hw. }

                                      destruct Hw' as [Hw' | Hw'].
                                      * destruct Hc''' as [_ [_ [_ [_ [Hc''' _]]]]]. apply no_overlap_non_member with (x := x) in Hc'''. apply Hc'''.
                                        rewrite Hw'. apply Hw. right. apply membership_append. rewrite Hlhvrev. apply membership_append_r. left. reflexivity.
                                      * rewrite Hph2' in HbLx. destruct Hph2 as [Hhph2 Hph2].

                                        assert (Hph20: (eqblist (rev tph2 ++ [hph2]) []) = false). { apply eqblist_empty. } rewrite Hph20 in HbLx. simpl in HbLx.
                                        apply no_overlap_non_member with (x := w) in HbLx. apply HbLx. rewrite <- Hhph2. apply Hw'. apply HcLx.
                                      * apply HDx.
                                      * apply Hc'. }

                              destruct (c =? x) as [|] eqn:Hyc.
                              * apply eqb_eq in Hyc. right. exists (rev tph2). exists zh. split.
                                { simpl. rewrite Hyc. rewrite eqb_refl. simpl. reflexivity. }
                                split. apply Hh'. split.
                                { apply subpath_still_directed with (w := h) (l1 := ph1) (l3 := ph). split. rewrite Hyc. symmetry. apply Hph2. apply Hh'. } split.
                                { apply subpath_still_acyclic with (w := h) (l1 := ph1) (l3 := ph). split. rewrite Hyc. symmetry. apply Hph2. apply Hh'. } split.
                                { apply no_overlap_non_member. intros w Hw Hw'. destruct Hh' as [_ [_ [Hh' _]]]. apply no_overlap_non_member with (x := w) in Hh'.
                                  apply Hh'. destruct Hph2 as [_ Hph2]. rewrite Hph2. apply membership_append_r. rewrite <- Hyc. apply Hw'. apply Hw. } split.
                                { (* u: Huph. [h, x]:  Hh' acyclic. (rev tlx1, v]: Hx'' no overlap . *)
                                  apply no_overlap_non_member. intros w Hw Hw'.
                                  destruct Hw as [Hw | Hw].
                                  { apply member_In_equiv_F in Huph. apply Huph. rewrite Hw. destruct Hph2 as [_ Hph2]. rewrite Hph2. rewrite <- app_assoc. apply membership_append_r. simpl. right. apply Hw'. }
                                  rewrite app_comm_cons in Hw. rewrite <- app_assoc in Hw. rewrite <- app_assoc in Hw. rewrite app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                  { destruct Hh' as [_ [Hh' _]]. apply acyclic_path_count with (x := w) in Hh'. destruct Hph2 as [_ Hph2]. rewrite Hph2 in Hh'. rewrite <- app_assoc in Hh'. rewrite <- app_assoc in Hh'. rewrite app_comm_cons in Hh'. rewrite app_assoc in Hh'.
                                    rewrite count_app in Hh'. apply member_count_at_least_1 in Hw. apply member_count_at_least_1 in Hw'. unfold nodes in *. unfold node in *. lia. 
                                    destruct Hph2 as [_ Hph2]. rewrite Hph2. rewrite <- app_assoc. rewrite <- app_assoc. rewrite app_comm_cons. rewrite app_assoc. apply membership_append. apply Hw. }

                                  apply no_overlap_non_member with (x := w) in Hx''. apply Hx''. destruct Hph2 as [_ Hph2]. rewrite Hph2. rewrite <- app_assoc. rewrite <- app_assoc. apply membership_append_r.
                                  simpl. right. apply Hw'. apply membership_rev. simpl. apply Hw. }

                                { rewrite Hyc in *. apply Hoverx. }

                              * unfold nodes in *. rewrite Hcolhv in Hc. destruct Hc as [Hc | Hc]. rewrite Hc in Hyc. rewrite eqb_refl in Hyc. discriminate Hyc.

                                apply HyDcy' with (D := (x, (rev tph2, zh)) :: Dx) (py' := rev tph2) (dy' := zh) in Hyc.
                                ++ destruct Hyc as [Hyc | Hyc]. left. apply Hyc. right. destruct Hyc as [pc [dc Hyc]]. exists pc. exists dc.

                                   rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split. repeat split; apply Hyc.
                                   intros c' d' p' [Hcc' Hcdp']. simpl in Hcdp'. destruct (x =? c') as [|] eqn:Hyc'.
                                   ** inversion Hcdp'. rewrite <- H3. apply eqb_eq in Hyc'. rewrite <- Hyc'. apply overlap_flip. apply Hoverx. split. rewrite eqb_sym. rewrite <- Hyc' in Hcc'. apply Hcc'.
                                      apply Hyc.
                                   ** apply Hyc. split. apply Hcc'. apply Hcdp'.
                                ++ reflexivity.
                                ++ right. apply Hc. }

                 - destruct (overlap (ph ++ [zh]) L) as [|] eqn:HoverL.
                   + (* CASE 2C.4.i find the first point of overlap betw ph++[zh] and last collider that overlaps in L *)
                     apply overlap_rev_true in HoverL.
                     apply list_has_first_elt_in_common_with_other_list in HoverL. destruct HoverL as [ph1 [ph2 [L1 [L2 [y' Hy]]]]].
                     assert (Hy': exists (c d: node) (p: nodes), In c (find_colliders_in_path (h, v, lhv) G)
                                 /\ get_assigned_value Dh c = Some (p, d) /\ d =? c = false
                                 /\ In y' (p ++ [d])).
                     { apply collider_descendants_from_assignments_belong_to_collider with (L := L). apply HLh. apply membership_rev.
                       destruct Hy as [_ [Hy _]]. rewrite Hy. apply membership_append_r. left. reflexivity. }
                     destruct Hy' as [cy [dy [py Hpdy]]].

                     assert (Hovery: overlap (ph ++ [zh]) (py ++ [dy]) = true).
                     { apply overlap_has_member_in_common. exists y'. split.
                       - destruct Hy as [Hy _]. rewrite Hy. apply membership_append_r. left. reflexivity.
                       - apply Hpdy. }
                     apply lists_have_first_elt_in_common in Hovery. destruct Hovery as [lhy1 [lhy2 [lcy1 [lcy2 [y Hy']]]]].

                     assert (Hcy: In cy lhv).
                     { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := cy) in Hlhv. apply Hlhv. right. right. apply Hpdy. }
                     apply membership_splits_list in Hcy. destruct Hcy as [lhcy1 [lhcy2 Hcy]].
                     exists (h :: lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2).

                     destruct HDh as [HDh HDh']. destruct Hpdy as [Hcolcy Hpdy]. pose proof Hcolcy as Hcolcy'. apply HDh' in Hcolcy.
                     pose proof Hpdy as Hpdy'. destruct Hpdy' as [Hpdy' _].
                     destruct Hcolcy as [Hcolcy | Hcolcy]. rewrite Hpdy' in Hcolcy. inversion Hcolcy. inversion H. rewrite H3 in Hpdy. destruct Hpdy as [_ [Hpdy _]]. rewrite eqb_refl in Hpdy. discriminate Hpdy.
                     destruct Hcolcy as [py' [dy' Hpdy'']]. destruct Hpdy'' as [Hpdy''' Hpdy'']. rewrite Hpdy' in Hpdy'''. inversion Hpdy'''. rewrite <- H0 in *. rewrite <- H1 in *. clear Hpdy'''. clear H0. clear H1.

                     assert (Hcychv: acyclic_path_2 (h, v, lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2)).
                     { apply concat_paths_acyclic. split. apply Hlhv. split.
                       - apply Hacyc with (dy := zh) (l2 := lhy2) (l3 := ph). split. symmetry. apply Hy'. apply Hh'.
                       - specialize Hcyccy' with (py := py) (dy := dy) (lhcy1 := lhcy1) (lcyd1 := lcy1) (cy := cy) (y := y) (lhcy2 := lhcy2) (lcyd2 := lcy2).
                         apply Hcyccy'. apply Hpdy''. apply Hcy. apply Hy'.
                       - split.
                         + specialize Hcyccy' with (py := py) (dy := dy) (lhcy1 := lhcy1) (lcyd1 := lcy1) (cy := cy) (y := y) (lhcy2 := lhcy2) (lcyd2 := lcy2).
                           apply Hcyccy'. apply Hpdy''. apply Hcy. apply Hy'.
                         + (* Hoverh: no overlap in ph++zh path and lhv path *)
                           intros Hmem. apply no_overlap_non_member with (x := v) in Hoverh. apply Hoverh. destruct Hy' as [Hy' _]. rewrite Hy'. apply membership_append. apply Hmem.
                           apply membership_append_r. left. reflexivity.
                       - (* lcy1: Hy'. [cy, lhcy2]: Hoverh *)
                         apply no_overlap_non_member. intros w Hw Hw'. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                         + destruct Hy' as [_ [_ Hy']]. apply no_overlap_non_member with (x := w) in Hy'. apply Hy'. apply Hw'. apply membership_rev. apply Hw.
                         + apply no_overlap_non_member with (x := w) in Hoverh. apply Hoverh. destruct Hy' as [Hy' _]. rewrite Hy'. apply membership_append. apply Hw'.
                          rewrite <- Hcy. apply membership_append. apply membership_append_r. apply Hw. }

                     assert (Hcycuhv: acyclic_path_2 (u, v, h :: lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2)).
                     { apply acyclic_path_cat_2.
                       apply Hcychv.
                       { (* u not in [lhy1,y] b/c cycle. u not in [rev lcy1] b/c HuL. u not in [cy, lhcy2] b/c Hulhv *)
                         intros Hmem. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. rewrite Hmem in Hhu. rewrite eqb_refl in Hhu. discriminate Hhu.
                         rewrite app_comm_cons in Hmem. rewrite app_assoc in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                         - apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                           + rewrite <- append_vs_concat in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                             * apply member_In_equiv_F in Huph. apply Huph. destruct Hy' as [Hy' _]. rewrite Hy'.
                               rewrite app_assoc. apply membership_append. apply Hmem.
                             * apply member_In_equiv_F in HuL. apply HuL.
                               apply collider_descendants_from_assignments_mem with (D := Dh) (p' := (h, v, lhv)) (p := py) (d := dy) (c := cy) (G := G).
                               apply Hcolcy'. split. apply Hpdy'. apply Hpdy. apply HLh. destruct Hy' as [_ [Hy' _]]. rewrite Hy'. apply membership_append. apply membership_rev. apply Hmem.
                           + apply member_In_equiv_F in Hulhv. apply Hulhv. rewrite <- Hcy. apply membership_append_r. apply Hmem.
                         - destruct Hmem as [Hmem | Hmem]. destruct Hcyc as [Hcyc _]. apply Hcyc. symmetry. apply Hmem. apply Hmem. } }

                     split. apply Hcycuhv.

                     assert (Hphv: is_path_in_graph (concat h y v lhy1 (rev lcy1 ++ [cy] ++ lhcy2)) G = true).
                     { apply concat_paths_still_a_path. split.
                       - apply directed_path_is_path. apply Hpathcy' with (dy := zh) (py := ph) (l2 := lhy2). apply Hh'. apply Hy'.
                       - apply concat_paths_still_a_path. split.
                         + apply reverse_path_in_graph. apply directed_path_is_path. apply Hpathcy' with (dy := dy) (py := py) (l2 := lcy2). apply Hpdy''. apply Hy'.
                         + apply subpath_still_path with (w := h) (l1 := lhcy1) (l3 := lhv). split. apply Hcy. apply Hlhv. }

                     assert (Hhmed: In h (find_mediators_in_path (u, v, h :: lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2) G)).
                     { destruct Hy' as [Hy' _]. apply mediator_means_edge_out with (c := h) (G := G) in Hy'.
                       destruct lhy1 as [| hph11 tph11].
                       * apply mediators_vs_edges_in_path. exists u. exists y. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                         -- apply Huh.
                         -- destruct Hy' as [Hx _]. apply Hx. reflexivity.
                       * apply mediators_vs_edges_in_path. exists u. exists hph11. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                         -- apply Huh.
                         -- destruct Hy' as [_ Hx]. apply Hx with (tly1 := tph11). reflexivity.
                       * apply Hh'. }

                     assert (Hcymed: In cy (find_mediators_in_path (concat y cy v (rev lcy1) lhcy2) G)).
                     { apply collider_becomes_mediator_when_concat_directed with (x := h) (dy := dy) (txv := lhv) (py := py) (lv1 := lhcy1) (ly2 := lcy2).
                       apply Hcolcy'. apply Hcy. apply Hlhv. apply Hy'. apply Hpdy''. }

                     assert (Hycol: In y (find_colliders_in_path (concat h y v lhy1 (rev lcy1 ++ [cy] ++ lhcy2)) G)).
                     { apply subpath_preserves_colliders with (u := cy) (l1 := lhy1 ++ [y] ++ rev lcy1) (l2 := lhcy2). split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. right.
                       apply intersection_of_directed_paths_is_collider with (d1 := zh) (d2 := dy) (l1 := ph) (l2 := py) (l1'' := lhy2) (l2'' := lcy2).
                       apply Hh'. apply Hpdy''. apply Hy'. apply Hy'. }

                     split.
                     { apply d_connected_cat. apply HG. apply Hcycuhv. apply concat_d_connected_paths. apply HG.
                       apply Hphv. split.
                       - apply Hconncy with (p := ph) (l2 := lhy2) (d := zh). apply Hy'. split. apply Hh'. split. apply Hh'. apply Hh'.
                       - split. apply concat_d_connected_paths. apply HG. apply subpath_still_path with (w := h) (l1 := lhy1) (l3 := lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2). split. reflexivity. apply Hphv. split.
                         + apply reverse_d_connected_paths. apply Hconncy with (p := py) (l2 := lcy2) (d := dy). apply Hy'. split. apply Hpdy''. split. apply overlap_cat with (x := cy). apply Hpdy''. apply Hpdy''.
                         + split. apply subpath_still_d_connected_gen with (w := h) (l1 := lhcy1) (l3 := lhv). split. apply Hcy. apply Hlhv.
                           apply subpath_still_acyclic with (w := h) (l1 := lhy1) (l3 := lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2). split. reflexivity. apply Hcychv.
                         + left. apply and_comm. split.
                           * destruct Hpdy'' as [_ [_ [_ [Hpdy'' _]]]]. simpl in Hpdy''. destruct (member cy Z) as [|] eqn:HcyZ. discriminate Hpdy''. apply member_In_equiv_F. apply HcyZ.
                           * apply Hcymed.
                         + apply Hcychv.
                       - right. right. rewrite and_comm. split.
                         ++ unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists dy. rewrite and_comm. split. apply Hpdy''.
                            apply find_descendants_correct. destruct Hy' as [_ [Hy' _]]. symmetry in Hy'. destruct (rev lcy2) as [| hlyd2 tlyd2] eqn:Hlyd2.
                            -- apply Hl2 in Hy'. left. apply Hy'. apply Hlyd2.
                            -- apply Hl2 in Hy'. right. exists (y, dy, rev tlyd2). split. apply subpath_still_directed with (w := cy) (l1 := lcy1) (l3 := py). split. symmetry. apply Hy' with (hl2 := hlyd2) (tl2 := tlyd2). apply Hlyd2. apply Hpdy''.
                               apply path_start_end_refl.
                         ++ apply Hycol.
                       - left. apply and_comm. split.
                         + apply HhZ.
                         + apply Hhmed. }

                     split.
                     { simpl. rewrite Huh. simpl. destruct G as [V E]. apply Hphv. } split.

                     { intros w Hw.
                       assert (Hwu: w =? u = false). { apply Houtwu with (x' := v) (l1 := lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2) (l2 := t). apply Hw. }
                       assert (Hwv: w =? v = false). { apply Houtwv with (x' := u) (l1 := h :: lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2) (l2 := h :: t). apply Hcyc. apply Hw. }
                       rewrite <- node_in_path_cat in Hw. rewrite <- node_in_path_cat in Hw. 2: { apply Hwu. } 2: { apply Hwu. }
                       rewrite path_out_of_node_cat. 2: { apply Hwu. }

                       destruct (w =? h) as [|] eqn:Hwh.
                       - apply eqb_eq in Hwh. rewrite Hwh. split.
                         + left. exists zh. exists ph. split. apply Hh'. split. apply Hh'. apply HhZ.
                         + intros H. apply HhZ.
                       - destruct (member w lhy1) as [|] eqn:Hwph1.
                         + assert (Houtph1: path_out_of_node w (h, v, lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2) G = path_out_of_node w (u, y, h :: lhy1) G).
                           { rewrite path_out_of_node_cat. 2: { apply Hwu. } assert (exists (b: bool), path_out_of_node w (h, y, lhy1) G = Some b).
                             { apply path_out_of_node_mem_2. right. apply member_In_equiv. apply Hwph1. }
                             destruct H as [bw Hbw]. unfold nodes in *. unfold node in *. rewrite Hbw. apply subpath_preserves_path_out_of_node_2 with (u := y) (l1 := lhy1) (l2 := rev lcy1 ++ [cy] ++ lhcy2). split. reflexivity.
                             apply Hbw. }
                           unfold nodes in *. unfold node in *. rewrite Houtph1. apply Houtwph1 with (ph2' := lhy2). apply member_In_equiv. apply Hwph1.
                           apply Hy'.
                         + destruct (member w (y :: rev lcy1)) as [|] eqn:Hwy.
                           * apply member_In_equiv in Hwy.
                             assert (Houtw: path_out_of_node w (h, v, lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2) G = path_out_of_node w (y, cy, rev lcy1) G).
                             { assert (Hwlp1: exists (b: bool), path_out_of_node w (y, cy, rev lcy1) G = Some b). { apply path_out_of_node_mem_2. apply Hwy. }
                               destruct Hwlp1 as [bw Hbw]. rewrite Hbw. apply subpath_preserves_path_out_of_node with (u := y) (l1 := lhy1) (l2 := rev lcy1 ++ [cy] ++ lhcy2). split. reflexivity.
                               apply subpath_preserves_path_out_of_node_2 with (u := cy) (l1 := rev lcy1) (l2 := lhcy2). split. reflexivity. apply Hbw.
                               apply Hcychv. }
                             unfold nodes in *. unfold node in *. rewrite Houtw. apply Houtw_revdir with (d := dy) (lyc2 := lcy2) (p := py). apply Hwy. symmetry. apply Hy'. repeat split; apply Hpdy''.
                             apply Hpathcy' with (dy := dy) (py := py) (l2 := lcy2). apply Hpdy''. apply Hy'.
                           * assert (Hwcy: In w (cy :: lhcy2)).
                             { assert (Hwmem: In w (u :: h :: lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2)).
                               { destruct Hw as [[Hw _] | Hw].
                                 - rewrite node_in_path_equiv in Hw. right. apply member_In_equiv in Hw. rewrite app_comm_cons in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                   apply Hw. destruct Hw as [Hw | Hw]. rewrite Hw in Hwv. rewrite eqb_refl in Hwv. discriminate Hwv. exfalso. apply Hw.
                                 - destruct Hw as [bw [_ Hw]]. apply path_out_of_node_mem_gen with (G := G) (v := v). exists (negb bw). apply Hw. }
                               apply member_In_equiv in Hwmem. simpl in Hwmem. rewrite eqb_sym in Hwmem. rewrite Hwu in Hwmem. rewrite eqb_sym in Hwmem. rewrite Hwh in Hwmem.
                               rewrite app_comm_cons in Hwmem. apply member_In_equiv in Hwmem. apply membership_append_or in Hwmem. destruct Hwmem as [Hwmem | Hwmem].
                               apply member_In_equiv in Hwmem. rewrite Hwmem in Hwph1. discriminate Hwph1.
                               apply membership_append_or in Hwmem. destruct Hwmem as [Hwmem | Hwmem]. apply member_In_equiv in Hwmem. rewrite Hwmem in Hwy. discriminate Hwy.
                               apply Hwmem. }
                              specialize Houtwcy with (cy := cy) (l1 := lhy1 ++ [y] ++ rev lcy1) (lcy2 := lhcy2). rewrite <- app_assoc in Houtwcy. rewrite <- app_assoc in Houtwcy.
                              apply Houtwcy with (lcy1 := lhcy1).
                              -- apply Hwcy.
                              -- symmetry. apply Hcy.
                              -- apply Hcychv.
                              -- rewrite path_out_of_node_cat in Hw. rewrite path_out_of_node_cat in Hw. apply Hw. apply Hwu. apply Hwu. }

                     assert (HDcy: exists (D: assignments (nodes * node)), get_collider_descendants_for_subpath Dh (find_colliders_in_path (cy, v, lhcy2) G) = Some D).
                     { apply collider_descendants_for_subpath_existence_2 with (u := h) (l1 := lhcy1) (L := L).
                       unfold concat. unfold nodes in *. unfold node in *. simpl in Hcy. rewrite Hcy. apply HLh. }
                     destruct HDcy as [Dcy HDcy].

                     assert (Hcolhv: find_colliders_in_path (u, v, h :: lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2) G = y :: (find_colliders_in_path (cy, v, lhcy2) G)).
                     { assert (Hcoluv: [] ++ h :: lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2 = h :: lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2).
                        { reflexivity. }
                        apply subpath_preserves_colliders_2 with (w := u) (v := v) (G := G) in Hcoluv. destruct Hcoluv as [Hcoluv | Hcoluv].
                        - (* h is a mediator, not a collider *)
                          apply if_mediator_then_not_confounder_path in Hhmed. exfalso. destruct Hhmed as [_ Hhmed]. apply Hhmed. unfold concat. unfold nodes in *.
                          unfold node in *. simpl in Hcoluv. simpl. rewrite Hcoluv. left. reflexivity. apply HG. apply Hcycuhv.
                        - unfold nodes in *. rewrite Hcoluv.

                          assert (Hcolhv: lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2 = lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2).
                          { reflexivity. }
                          assert (Hcoluy: find_colliders_in_path (u, y, h :: lhy1) G = []). { apply Hcolph1 with (ph2' := lhy2). apply Hy'. }
                          assert (Hcolhy: find_colliders_in_path (h, y, lhy1) G = []). { destruct (find_colliders_in_path (h, y, lhy1) G) as [| ch ct] eqn:Hhy. reflexivity.
                            assert (Hch: In ch (find_colliders_in_path (u, y, h :: lhy1) G)). { apply subpath_preserves_colliders with (u := h) (l1 := []) (l2 := lhy1). split. reflexivity. left. simpl. simpl in Hhy. rewrite Hhy. left. reflexivity. }
                            rewrite Hcoluy in Hch. exfalso. apply Hch. }

                          apply subpath_preserves_colliders_2 with (w := h) (u := y) (v := v) (G := G) in Hcolhv. destruct Hcolhv as [Hcolhv | Hcolhv].
                          + unfold nodes in *. rewrite Hcolhv. unfold node in *. rewrite Hcolhy.
                            assert (Hcolyv:rev lcy1 ++ [cy] ++ lhcy2 = rev lcy1 ++ [cy] ++ lhcy2). { reflexivity. } apply subpath_preserves_colliders_2 with (w := y) (v := v) (G := G) in Hcolyv.
                            assert (Hcolycy: find_colliders_in_path (y, cy, rev lcy1) G = []). { apply Hcoldir with (d := dy) (p' := py) (p2' := lcy2). apply Hy'. apply Hpdy''. apply Hpdy''. }
                            unfold nodes in *. unfold node in *. rewrite Hcolycy in *. destruct Hcolyv as [Hcolyv | Hcolyv].
                            * (* cy is a mediator, not a collider *)
                              apply if_mediator_then_not_confounder_path in Hcymed. exfalso. destruct Hcymed as [_ Hcymed]. apply Hcymed. unfold concat. unfold nodes in *.
                              unfold node in *. simpl in Hcolyv. simpl. rewrite Hcolyv. left. reflexivity. apply HG. unfold concat. apply subpath_still_acyclic with (w := h) (l1 := lhy1) (l3 := lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2).
                              split. reflexivity. apply Hcychv.
                            * rewrite Hcolyv. simpl. reflexivity.
                          + (* y is a collider, so should be included in Hcolhv *)
                            unfold concat in Hycol.
                            unfold nodes in *. unfold node in *. rewrite <- append_vs_concat in Hycol. rewrite <- app_assoc in Hycol.
                            rewrite Hcolhv in Hycol. apply membership_append_or in Hycol.
                            destruct Hycol as [Hycol | Hycol]. (* contradicts acyclic *)
                            * assert (Hphy: is_path_in_graph (h, y, lhy1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := (rev lcy1 ++ [cy] ++ lhcy2)) (l3 := lhy1 ++ [y] ++ (rev lcy1 ++ [cy] ++ lhcy2)).
                                split. reflexivity. apply Hphv. } apply intermediate_node_in_path with (x := y) in Hphy.
                              assert (Hyph11: In y (lhy1)). { apply Hphy. right. right. apply Hycol. }
                              assert (Hchy: acyclic_path_2 (h, y, lhy1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := (rev lcy1 ++ [cy] ++ lhcy2)) (l3 := lhy1 ++ [y] ++ (rev lcy1 ++ [cy] ++ lhcy2)).
                                split. reflexivity. apply Hcychv. } exfalso. destruct Hchy as [_ [_ [Hchy _]]]. apply Hchy. apply Hyph11.
                            * assert (Hphy: is_path_in_graph (y, v, rev lcy1 ++ [cy] ++ lhcy2) G = true). { apply subpath_still_path with (w := h) (l1 := lhy1) (l3 := lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2).
                                split. reflexivity. apply Hphv. } apply intermediate_node_in_path with (x := y) in Hphy.
                              assert (Hyph11: In y (rev lcy1 ++ [cy] ++ lhcy2)). { apply Hphy. right. right. apply Hycol. }
                              assert (Hchy: acyclic_path_2 (y, v, rev lcy1 ++ [cy] ++ lhcy2)). { apply subpath_still_acyclic with (w := h) (l1 := lhy1) (l3 := lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2).
                                split. reflexivity. apply Hcychv. } exfalso. destruct Hchy as [_ [Hchy _]]. apply Hchy. apply Hyph11. }

                        unfold nodes in *. rewrite Hcolhv.

                        assert (HyDcy': forall (py': nodes) (dy': node) (D: assignments (nodes * node)), D = (y, (py', dy')) :: Dcy
                                       -> forall c : node,
                                          (c =? y) = false
                                           -> In c (y :: find_colliders_in_path (cy, v, lhcy2) G)
                                           -> get_assigned_value D c = Some ([], c) /\ In c Z \/
                                               (exists (p : list node) (d : node),
                                                  get_assigned_value D c = Some (p, d) /\
                                                  In d Z /\
                                                  is_directed_path_in_graph (c, d, p) G = true /\
                                                  acyclic_path_2 (c, d, p) /\
                                                  overlap (c :: p) Z = false /\
                                                  overlap (p ++ [d])
                                                    (u :: (h :: lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2) ++ [v]) =
                                                  false /\ overlap (c :: p ++ [d]) (cy :: py ++ [dy]) = false
                                                  /\ (forall (c' d' : node) (p' : list node),
                                                     (c =? c') = false /\ get_assigned_value Dcy c' = Some (p', d') ->
                                                     overlap (c :: p ++ [d]) (c' :: p' ++ [d']) = false))).
                        { intros py'' dy'' D HDeq c Hyc Hc.
                          destruct Hc as [Hc | Hc]. rewrite Hc in Hyc. rewrite eqb_refl in Hyc. discriminate Hyc.
                          (* induction case *) assert (Hc': In c (find_colliders_in_path (h, v, lhv) G)).
                          { apply subpath_preserves_colliders with (u := cy) (l1 := lhcy1) (l2 := lhcy2). split. apply Hcy. left. apply Hc. }
                          pose proof Hc' as Hc''. apply HDh' in Hc'. rewrite HDeq in *. destruct Hc' as [Hc' | Hc'].
                          -- left. split. simpl. rewrite eqb_sym. rewrite Hyc. rewrite <- collider_descendants_preserved_for_subpath_3 with (D := Dh) (col := find_colliders_in_path (cy, v, lhcy2) G).
                             apply Hc'. apply HDcy. apply Hc. apply Hc'.
                          -- right. destruct Hc' as [pc [dc Hc']]. exists pc. exists dc. split. simpl. rewrite eqb_sym. rewrite Hyc. simpl. rewrite <- collider_descendants_preserved_for_subpath_3 with (D := Dh) (col := find_colliders_in_path (cy, v, lhcy2) G).
                             apply Hc'. apply HDcy. apply Hc. split. apply Hc'. split. apply Hc'. split. apply Hc'. split. apply Hc'.
                             assert (Hovercy: overlap (c :: pc ++ [dc]) (cy :: py ++ [dy]) = false).
                             { apply Hc'. rewrite and_comm. split. apply Hpdy'. destruct (c =? cy) as [|] eqn:Hccy. exfalso. apply eqb_eq in Hccy.
                               assert (Hmemcy: In cy lhcy2).
                               { assert (Hpcy: is_path_in_graph (cy, v, lhcy2) G = true).
                                 { apply subpath_still_path with (w := h) (l1 := lhcy1) (l3 := lhv). split. apply Hcy. apply Hlhv. }
                                 apply intermediate_node_in_path with (x := cy) in Hpcy. apply Hpcy. right. right. rewrite <- Hccy in *. apply Hc. }
                               assert (Hccy': acyclic_path_2 (cy, v, lhcy2)).
                               { apply subpath_still_acyclic with (w := h) (l1 := lhcy1) (l3 := lhv). split. apply Hcy. apply Hlhv. }
                               destruct Hccy' as [_ [Hccy' _]]. apply Hccy'. apply Hmemcy. reflexivity. }

                             repeat split.
                             ++ (* u: HuL. h: HDh'. lhy1: Hy. [y, lcy1]: HDh' (desc path of cy). [cy, v]: HDh'. *) apply no_overlap_non_member. intros w Hw Hw'.
                                assert (HwL: In w L).
                                { apply collider_descendants_from_assignments_mem with (D := Dh) (G := G) (p' := (h, v, lhv)) (p := pc) (d := dc) (c := c). apply Hc''. split. apply Hc'.
                                  destruct (dc =? c) as [|] eqn:Hdcc. apply eqb_eq in Hdcc. destruct Hc' as [_ [_ [_ [[Hc' _] _]]]]. exfalso. apply Hc'. symmetry. apply Hdcc. reflexivity.
                                  apply HLh. apply Hw'. }
                                destruct Hw as [Hw | Hw].
                                { apply member_In_equiv_F in HuL. apply HuL. rewrite Hw. apply HwL. } destruct Hw as [Hw | Hw].
                                { destruct Hc' as [_ [_ [_ [_ [_ [Hc' _]]]]]]. apply no_overlap_non_member with (x := h) in Hc'. apply Hc'. rewrite Hw. apply Hw'. left. reflexivity. }
                                rewrite <- app_assoc in Hw. apply membership_append_or in Hw.

                                destruct Hw as [Hw | Hw].
                                { (* w is in Lx. (py ++ [dy]) comes before (pc ++ [dc]) in Lx, since cy comes before c. Then, y' comes before w, so w in Lx1 *)
                                  (* Hy -> ph2 and Lx1 have no overlap. *)
                                  assert (HLxy: exists (l1' l2' l3': nodes), L = l1' ++ py ++ [dy] ++ l2' ++ pc ++ [dc] ++ l3').
                                  { apply get_collider_descendants_from_assignments_preserves_order with (D := Dh) (col := find_colliders_in_path (h, v, lhv) G) (c1 := cy) (c2 := c).
                                    apply HLh. split. apply Hpdy. rewrite eqb_sym. apply Hpdy. split.
                                    - apply Hc'.
                                    - apply eqb_neq. destruct Hc' as [_ [_ [_ [[Hc' _] _]]]]. apply Hc'.
                                    - pose proof Hcy as Hcy'. apply subpath_preserves_colliders_2 with (w := h) (v := v) (G := G) in Hcy. destruct Hcy as [Hcy | Hcy].
                                      + exists (find_colliders_in_path (h, cy, lhcy1) G). unfold nodes in *. unfold node in *. rewrite Hcy.
                                        apply membership_splits_list in Hc. destruct Hc as [lc1 [lc2 Hc]]. exists lc1. exists lc2. rewrite Hc. reflexivity.
                                      + (* contradiction in Hcy, since cy is a collider *) exfalso. unfold nodes in *. unfold node in *. rewrite Hcy in Hcolcy'. apply membership_append_or in Hcolcy'.
                                        destruct Hcolcy' as [Hcolcy' | Hcolcy'].
                                        * assert (HcyF: In cy lhcy1). { assert (Hcyp: is_path_in_graph (h, cy, lhcy1) G = true). { apply subpath_still_path_2 with (v := v) (l2 := lhcy2) (l3 := lhv). split. apply Hcy'. apply Hlhv. }
                                            apply intermediate_node_in_path with (x := cy) in Hcyp. apply Hcyp. right. right. apply Hcolcy'. }
                                          assert (Hcycyc: acyclic_path_2 (h, cy, lhcy1)). { apply subpath_still_acyclic_2 with (v := v) (l2 := lhcy2) (l3 := lhv). split. apply Hcy'. apply Hlhv. }
                                          destruct Hcycyc as [_ [_ [Hcycyc _]]]. apply Hcycyc. apply HcyF.
                                        * assert (HcyF: In cy lhcy2). { assert (Hcyp: is_path_in_graph (cy, v, lhcy2) G = true). { apply subpath_still_path with (w := h) (l1 := lhcy1) (l3 := lhv). split. apply Hcy'.
                                            apply Hlhv. }
                                            apply intermediate_node_in_path with (x := cy) in Hcyp. apply Hcyp. right. right. apply Hcolcy'. }
                                          assert (Hcycyc: acyclic_path_2 (cy, v, lhcy2)). { apply subpath_still_acyclic with (w := h) (l1 := lhcy1) (l3 := lhv). split. apply Hcy'.
                                            apply Hlhv. }
                                          destruct Hcycyc as [_ [Hcycyc _]]. apply Hcycyc. apply HcyF. }

                                  destruct Hpdy as [_ [_ Hpdy]]. apply membership_splits_list in Hpdy. destruct Hpdy as [ly1' [ly2' Hpdy]]. destruct HLxy as [Lx1' [Lx2' [Lx3' HLxy]]]. unfold nodes in *. unfold node in *. simpl in Hpdy. rewrite app_assoc in HLxy. rewrite app_assoc in HLxy. rewrite <- app_assoc with (l := Lx1') in HLxy. rewrite <- Hpdy in HLxy.
                                  assert (Hcounty: count y' L = 1).
                                  { apply get_collider_descendants_from_assignments_preserves_count with (D := Dh) (G := G) (Z := Z) (u := h) (v := v) (l' := lhv).
                                    2: { apply HLh. } 2: { apply Hlhv. } 2: { apply Hlhv. } split. apply HDh. apply HDh'.
                                    rewrite HLxy. apply membership_append. apply membership_append_r. apply membership_append_r. left. reflexivity. }

                                  assert (HLx1: rev L1 = ly2' ++ Lx2' ++ pc ++ dc :: Lx3').
                                  { apply two_sublists_the_same_gen with (l := L) (a := y') (l1 := rev L2) (l1' := Lx1' ++ ly1'). destruct Hy as [_ [Hy _]].
                                    rewrite reverse_list_twice with (l := L). rewrite Hy. rewrite reverse_list_append. simpl. rewrite <- app_assoc. reflexivity.
                                    rewrite <- app_assoc in HLxy. rewrite <- app_assoc in HLxy. rewrite <- app_assoc. simpl in HLxy. apply HLxy. apply Hcounty. }
                                  assert (HwLx1: In w L1). { apply membership_rev. rewrite HLx1. apply membership_append_r. apply membership_append_r. rewrite <- append_vs_concat. apply membership_append. apply Hw'. }

                                  destruct Hy as [_ [_ Hy]]. apply no_overlap_non_member with (x := w) in Hy. apply Hy. apply membership_append. apply Hph1ph with (x' := y) (ph1' := lhy1) (ph2' := lhy2). apply Hw. apply Hy'. apply HwLx1. }

                                rewrite <- app_assoc in Hw. rewrite <- app_assoc in Hw. rewrite app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                { destruct Hc' as [_ [_ [_ [_ [_ [_ Hc']]]]]]. specialize Hc' with (c' := cy) (d' := dy) (p' := py).
                                  apply no_overlap_non_member with (x := w) in Hovercy. apply Hovercy. right. apply Hw'. right. destruct Hy' as [_ [Hy' _]]. rewrite Hy'. rewrite app_assoc. apply membership_append.
                                  apply membership_rev. rewrite reverse_list_append. apply Hw. }
                                { destruct Hc' as [_ [_ [_ [_ [_ [Hc' _]]]]]]. apply no_overlap_non_member with (x := w) in Hc'. apply Hc'. apply Hw'. right. rewrite <- Hcy. rewrite <- app_assoc. apply membership_append_r. apply Hw. }
                             ++ apply Hovercy.
                             ++ intros c' d' p' [Hcc' Hcdp'].
                                apply Hc'. split. apply Hcc'. apply collider_descendants_preserved_for_subpath with (D' := Dcy) (col := find_colliders_in_path (cy, v, lhcy2) G). apply HDcy. apply Hcdp'. }

                        (* destruct on y = zh = d or not *) destruct (rev lcy2) as [| hy ty] eqn:Hlyd2.
                         { exists ((y, ([], y)) :: Dcy). split.
                           + apply exact_assignment_cat. apply collider_subpath_is_exact_assignment with (D := Dh). apply HDcy.
                           + intros c Hc. destruct (c =? y) as [|] eqn:Hyc.
                             * apply eqb_eq in Hyc. left. split. simpl. rewrite Hyc. rewrite eqb_refl. reflexivity. rewrite Hyc. destruct Hy' as [_ [Hy' _]]. symmetry in Hy'. apply Hl2 in Hy'.
                               apply Hy' in Hlyd2. destruct Hlyd2 as [Hlyd2 _]. rewrite Hlyd2. apply Hpdy''.
                             * unfold nodes in *. rewrite Hcolhv in Hc. destruct Hc as [Hc | Hc]. rewrite Hc in Hyc. rewrite eqb_refl in Hyc. discriminate Hyc.
                               apply HyDcy' with (D := (y, ([], y)) :: Dcy) (py' := []) (dy' := y) in Hyc.
                                -- destruct Hyc as [Hyc | Hyc]. left. apply Hyc. right. destruct Hyc as [pc [dc Hyc]]. exists pc. exists dc.

                                   rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split. repeat split; apply Hyc.
                                   intros c' d' p' [Hcc' Hcdp']. simpl in Hcdp'. destruct (y =? c') as [|] eqn:Hyc'.
                                   ** inversion Hcdp'. rewrite <- H1. apply eqb_eq in Hyc'. rewrite <- Hyc'. simpl. (* y is original member of cy's desc path, so doesn't overlap c's desc path (HDh') *)
                                      rewrite <- Hyc' in Hcc'. rewrite eqb_sym in Hcc'. rewrite Hcc'. apply overlap_flip. simpl.
                                      assert (Hmemy: ~In y (pc ++ [dc])).
                                      { intros F. destruct Hyc as [_ [_ [_ [_ [_ [_ [Hovercy _]]]]]]]. apply no_overlap_non_member with (x := y) in Hovercy. apply Hovercy. right. apply F. right.
                                        destruct Hy' as [_ [Hy' _]]. rewrite Hy'. apply membership_append_r. left. reflexivity. }
                                      apply member_In_equiv_F in Hmemy. rewrite Hmemy. reflexivity.
                                   ** apply Hyc. split. apply Hcc'. apply Hcdp'.
                                -- reflexivity.
                                -- right. apply Hc. }

                         { destruct Hy' as [Hy'' [Hy' Hovery']]. symmetry in Hy'. apply Hl2 in Hy'. apply Hy' in Hlyd2. exists ((y, (rev ty, dy)) :: Dcy). split.
                           + apply exact_assignment_cat. apply collider_subpath_is_exact_assignment with (D := Dh). apply HDcy.
                          + intros c Hc.
                            assert (Hwmempy: forall (w: node), In w (rev ty ++ [dy]) -> In w (py ++ [dy])).
                            { intros w Hw. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2. rewrite <- app_assoc. apply membership_append_r. simpl. right. apply Hw. }

                            destruct (c =? y) as [|] eqn:Hyc.
                            * apply eqb_eq in Hyc. right. exists (rev ty). exists dy. split.
                              { simpl. rewrite Hyc. rewrite eqb_refl. simpl. reflexivity. }
                              split. apply Hpdy''. split.
                              { apply subpath_still_directed with (w := cy) (l1 := lcy1) (l3 := py). split. rewrite Hyc. symmetry. apply Hlyd2. apply Hpdy''. } split.
                              { apply subpath_still_acyclic with (w := cy) (l1 := lcy1) (l3 := py). split. rewrite Hyc. symmetry. apply Hlyd2. apply Hpdy''. } split.
                              { apply no_overlap_non_member. intros w Hw Hw'. destruct Hpdy'' as [_ [_ [_ [Hpdy'' _]]]]. apply no_overlap_non_member with (x := w) in Hpdy''.
                                apply Hpdy''. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2. right. apply membership_append_r. rewrite <- Hyc. apply Hw'. apply Hw. } split.
                              { (* u: HuL. h: Hpdy''. lhy1: Hy. [y, lcy1, cy]: acyclic Hpdy''. [lhcy2, v]: Hpdy''. *)
                                apply no_overlap_non_member. intros w Hw Hw'.
                                assert (HwL: In w L).
                                { apply collider_descendants_from_assignments_mem with (D := Dh) (G := G) (p' := (h, v, lhv)) (p := py) (d := dy) (c := cy).
                                  - apply Hcolcy'.
                                  - split. apply Hpdy. apply Hpdy.
                                  - apply HLh.
                                  - apply Hwmempy. apply Hw'. }
                                destruct Hw as [Hw | Hw].
                                { apply member_In_equiv_F in HuL. apply HuL. rewrite Hw. apply HwL. } destruct Hw as [Hw | Hw].
                                { destruct Hpdy'' as [_ [_ [_ [_ [Hc' _]]]]]. apply no_overlap_non_member with (x := h) in Hc'. apply Hc'. rewrite Hw.
                                  apply Hwmempy. apply Hw'. left. reflexivity. }

                                rewrite <- app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                { (* cycle! w ->...lhy1...->y->...rev ty...->w *)
                                  apply membership_splits_list in Hw. destruct Hw as [l1 [l2 Hw]]. apply membership_splits_list in Hw'. destruct Hw' as [l3 [l4 Hw']].
                                  assert (Hcycle: is_directed_path_in_graph (w, w, l2 ++ [y] ++ l3) G = true).
                                  { apply concat_directed_paths. split.
                                    - apply subpath_still_directed with (w := h) (l1 := l1) (l3 := lhy1). split. apply Hw. apply Hpathcy' with (dy := zh) (py := ph) (l2 := lhy2).
                                      apply Hh'. apply Hy''.
                                    - apply subpath_still_directed with (w := cy) (l1 := lcy1) (l3 := lcy1 ++ [y] ++ l3). split. reflexivity.
                                      apply Hpathcy' with (dy := dy) (py := py) (l2 := l4). apply Hpdy''. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2. rewrite <- app_assoc. rewrite <- app_assoc.
                                      unfold nodes in *. unfold node in *. rewrite <- Hw'. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
                                  destruct HG as [_ HG]. apply contains_cycle_false_correct with (p := (w, w, l2 ++ [y] ++ l3)) in HG. destruct HG as [HG _]. apply HG. reflexivity.
                                  apply Hcycle. }

                                rewrite <- app_assoc in Hw. rewrite <- app_assoc in Hw. rewrite app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                                { destruct Hpdy'' as [_ [_ [Hpdy'' _]]]. apply acyclic_path_count with (x := w) in Hpdy''. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2 in Hpdy''.
                                  apply membership_rev in Hw. simpl in Hw. rewrite <- reverse_list_twice in Hw. apply member_count_at_least_1 in Hw. apply member_count_at_least_1 in Hw'.
                                  rewrite <- app_assoc in Hpdy''. rewrite <- app_assoc in Hpdy''. rewrite app_assoc in Hpdy''. simpl in Hpdy''. unfold nodes in *. unfold node in *. destruct (cy =? w) as [|]. rewrite count_app in Hpdy''. lia. rewrite count_app in Hpdy''. lia.
                                  right. apply Hwmempy. apply Hw'. }
                                { destruct Hpdy'' as [_ [_ [_ [_ [Hc' _]]]]]. apply no_overlap_non_member with (x := w) in Hc'. apply Hc'. apply Hwmempy. apply Hw'.
                                  right. rewrite <- Hcy. rewrite <- app_assoc. apply membership_append_r. apply Hw. } }

                              { intros c' d' p'. intros [Hcc' Hcdp']. simpl in Hcdp'. rewrite <- Hyc in Hcdp'. rewrite Hcc' in Hcdp'.
                                apply no_overlap_non_member. intros w Hw Hw'.
                                assert (Hc': In c' (find_colliders_in_path (cy, v, lhcy2) G)).
                                { apply collider_subpath_is_exact_assignment in HDcy. unfold is_exact_assignment_for in HDcy.
                                  destruct (member c' (find_colliders_in_path (cy, v, lhcy2) G)) as [|] eqn:Hmem. apply member_In_equiv. apply Hmem.
                                  apply HDcy in Hmem. apply assigned_is_false in Hmem. unfold nodes in *. rewrite Hmem in Hcdp'. discriminate Hcdp'. }
                                rewrite eqb_sym in Hcc'. rewrite Hyc in Hcc'. pose proof Hcc' as Hyc'. apply HyDcy' with (py' := rev ty) (dy' := dy) (D := (y, (rev ty, dy)) :: Dcy) in Hcc'.
                                - destruct Hcc' as [Hcc' | Hcc'].
                                  + simpl in Hcc'. rewrite eqb_sym in Hyc'. rewrite Hyc' in Hcc'. destruct Hcc' as [Hcc' _]. unfold nodes in *. rewrite Hcc' in Hcdp'. inversion Hcdp'.
                                    rewrite <- H0 in Hw. rewrite <- H1 in Hw. (* w = c', so py/dy path overlaps with lhv, contradicts Hpdy'' *)
                                    assert (Hwc': c' = w). { simpl in Hw. destruct Hw as [Hw | [Hw | Hw]]. apply Hw. apply Hw. exfalso. apply Hw. }
                                    destruct Hw' as [Hw' | Hw'].
                                    * rewrite <- Hyc in Hyc'. rewrite Hw' in Hyc'. rewrite Hwc' in Hyc'. rewrite eqb_refl in Hyc'. discriminate Hyc'.
                                    * destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := w) in Hpdy''. apply Hpdy''.
                                      apply Hwmempy. apply Hw'.
                                      assert (Hmemc': In c' lhcy2).
                                      { assert (Hpcyv: is_path_in_graph (cy, v, lhcy2) G = true). { apply subpath_still_path with (w := h) (l1 := lhcy1) (l3 := lhv). split. apply Hcy.
                                          apply Hlhv. }
                                        apply intermediate_node_in_path with (x := c') in Hpcyv. apply Hpcyv. right. right. apply Hc'. }
                                      rewrite <- Hwc'. right. apply membership_append. rewrite <- Hcy. apply membership_append_r. simpl. right. apply Hmemc'.

                                  + destruct Hcc' as [p'' [d'' [Hcdp'' Hcc']]]. simpl in Hcdp''. rewrite eqb_sym in Hyc'. rewrite Hyc' in Hcdp''. unfold nodes in *. rewrite Hcdp'' in Hcdp'.
                                    inversion Hcdp'. rewrite H0 in *. rewrite H1 in *. destruct Hcc' as [_ [_ [_ [_ [_ [Hcc' _]]]]]]. apply no_overlap_non_member with (x := w) in Hcc'.
                                    apply Hcc'. apply Hw. right. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2. rewrite <- app_assoc. apply membership_append_r. rewrite <- Hyc. apply Hw'.
                                - reflexivity.
                                - right. apply Hc'. }
                            * unfold nodes in *. rewrite Hcolhv in Hc. destruct Hc as [Hc | Hc]. rewrite Hc in Hyc. rewrite eqb_refl in Hyc. discriminate Hyc.

                              apply HyDcy' with (D := (y, (rev ty, dy)) :: Dcy) (py' := rev ty) (dy' := dy) in Hyc.
                              -- destruct Hyc as [Hyc | Hyc]. left. apply Hyc. right. destruct Hyc as [pc [dc Hyc]]. exists pc. exists dc.

                                 rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split. repeat split; apply Hyc.
                                 intros c' d' p' [Hcc' Hcdp']. simpl in Hcdp'. destruct (y =? c') as [|] eqn:Hyc'.
                                 ** inversion Hcdp'. rewrite <- H1. apply eqb_eq in Hyc'. rewrite <- Hyc'.
                                    apply no_overlap_non_member. intros w Hw Hw'. destruct Hyc as [_ [_ [_ [_ [_ [_ [Hyc _]]]]]]].
                                    apply no_overlap_non_member with (x := w) in Hyc. apply Hyc. apply Hw'. right. destruct Hlyd2 as [_ Hlyd2]. rewrite Hlyd2.
                                    rewrite <- app_assoc. apply membership_append_r. apply Hw.
                                 ** apply Hyc. split. apply Hcc'. apply Hcdp'.
                              -- reflexivity.
                              -- right. apply Hc. }

                   + (* CASE 2C.4.ii *) exists (h :: lhv).

                     split. repeat split.
                     { apply Hcyc. }
                     { intros Hmem. destruct Hmem as [Hmem | Hmem].
                       - unfold acyclic_path_2 in Hcyc. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. left. apply Hmem.
                       - apply member_In_equiv_F in Hulhv. apply Hulhv. apply Hmem. }
                     { unfold acyclic_path_2 in Hlhv. intros Hmem. destruct Hmem as [Hmem | Hmem].
                       - destruct Hlhv as [[[Hlhv _] _] _]. apply Hlhv. apply Hmem.
                       - destruct Hlhv as [[[_ [_ [Hlhv _]]] _] _]. apply Hlhv. apply Hmem. }
                     { destruct Hlhv as [[Hlhv _] _]. apply acyclic_path_correct_2 in Hlhv. apply acyclic_path_reverse in Hlhv.
                       simpl in Hlhv. rewrite reverse_list_append in Hlhv. simpl in Hlhv. apply split_and_true in Hlhv. destruct Hlhv as [_ Hlhv].
                       apply acyclic_path_reverse in Hlhv. rewrite reverse_list_append in Hlhv. rewrite <- reverse_list_twice in Hlhv. apply Hlhv. } split.
                     apply Hconn'. split. apply Hpath'. split.
                     { intros w H. destruct (w =? u) as [|] eqn:Hwu.
                       - (* contradicts H, since would be the same *) apply eqb_eq in Hwu. rewrite Hwu in H. destruct H as [H | H].
                         + destruct H as [_ H]. unfold node_in_path in H. simpl in H. rewrite eqb_refl in H. simpl in H. discriminate H.
                         + unfold path_out_of_node in H. simpl in H. rewrite eqb_refl in H. destruct (edge_in_graph (u, h) G) as [|].
                           * destruct H as [b Hb]. destruct Hb as [Hb1 Hb2]. rewrite Hb1 in Hb2. inversion Hb2. destruct b as [|]. discriminate H0. discriminate H0.
                           * destruct H as [b Hb]. destruct Hb as [Hb1 Hb2]. rewrite Hb1 in Hb2. inversion Hb2. destruct b as [|]. discriminate H0. discriminate H0.
                       - assert (Houtw: path_out_of_node w (u, v, h :: lhv) G = path_out_of_node w (h, v, lhv) G).
                         { apply path_out_of_node_cat. apply Hwu. }
                         assert (Houtw': path_out_of_node w (u, v, h :: t) G = path_out_of_node w (h, v, t) G).
                         { apply path_out_of_node_cat. apply Hwu. }
                         unfold nodes in *. rewrite Houtw in H. rewrite Houtw' in H.
                         assert (Hnode: node_in_path w (u, v, h :: lhv) = node_in_path w (h, v, lhv)).
                         { symmetry. apply node_in_path_cat. apply Hwu. }
                         assert (Hnode': node_in_path w (u, v, h :: t) = node_in_path w (h, v, t)).
                         { symmetry. apply node_in_path_cat. apply Hwu. }
                         rewrite Hnode in H. rewrite Hnode' in H. apply Hout in H. rewrite Houtw. apply H. }

                     exists ((h, (ph, zh)) :: Dh). split. unfold nodes in *. rewrite Hcol. split.
                     { simpl. rewrite eqb_refl. simpl. apply is_assignment_for_cat. apply HDh. }
                     { intros w Hw. simpl in Hw. simpl. destruct (h =? w) as [|] eqn:Hhw. discriminate Hw. rewrite eqb_sym in Hhw. rewrite Hhw.
                       simpl. destruct HDh as [[_ HDh] _]. apply HDh. apply Hw. }
                     { intros c Hc. unfold nodes in *. rewrite Hcol in Hc.

                       assert (HpdL: forall (w: node) (c d: node) (p: nodes), 
                                     In c (find_colliders_in_path (h, v, lhv) G)
                                     -> In d Z
                                     -> overlap (c :: p) Z = false
                                     -> get_assigned_value Dh c = Some (p, d)
                                     -> In w (p ++ [d]) -> In w L).
                       { intros w c' d p Hccol HdZ HcZ Hc'.
                         apply collider_descendants_from_assignments_mem with (D := Dh) (p' := (h, v, lhv)) (p := p) (d := d) (c := c') (G := G).
                         apply Hccol. split. apply Hc'. destruct (d =? c') as [|] eqn:Hdc. apply eqb_eq in Hdc.
                         - exfalso. apply no_overlap_non_member with (x := d) in HcZ.
                           apply HcZ. left. symmetry. apply Hdc. apply HdZ.
                         - reflexivity.
                         - apply HLh. }

                       destruct Hc as [Hc | Hc].
                       + right. exists ph. exists zh. rewrite <- Hc in *. split.
                         * simpl. rewrite eqb_refl. reflexivity.
                         * rewrite <- and_assoc. rewrite <- and_assoc. split. repeat split; apply Hh'. repeat split.
                           -- simpl. apply member_In_equiv_F in HhZ. rewrite HhZ. apply Hh'.
                           -- apply overlap_flip. simpl. rewrite Huph. destruct Hh' as [_ [Hh' _]]. destruct (member h (ph ++ [zh])) as [|] eqn:Hmem.
                              ++ apply member_In_equiv in Hmem. apply membership_append_or in Hmem. exfalso. destruct Hmem as [Hmem | Hmem]. 
                                 destruct Hh' as [_ [Hh' _]]. apply Hh'. apply Hmem. destruct Hmem as [Hmem | Hmem]. destruct Hh' as [Hh' _]. apply Hh'. symmetry. apply Hmem. apply Hmem.
                              ++ apply overlap_flip. apply Hoverh.
                           -- intros c' d' p' Hc'. simpl in Hc'. destruct Hc' as [Hc' Hc'']. rewrite Hc' in Hc''. simpl. rewrite eqb_sym. rewrite Hc'.
                              assert (Hcolc': In c' (find_colliders_in_path (h, v, lhv) G)).
                              { apply assigned_true_then_in_list with (A := Dh). split. apply assigned_is_true. exists (p', d'). apply Hc''. apply HDh. }
                              destruct (member h (p' ++ [d'])) as [|] eqn:Hmem.
                              ++ destruct HDh as [_ HDh]. apply HDh in Hcolc'. destruct Hcolc' as [Hcolc' | Hcolc'].
                                 ** destruct Hcolc' as [Hcolc' _]. unfold nodes in *. rewrite Hc'' in Hcolc'. inversion Hcolc'. rewrite H0 in Hmem. rewrite H1 in Hmem. simpl in Hmem. rewrite eqb_sym in Hc'.
                                    rewrite Hc' in Hmem. discriminate Hmem.
                                 ** destruct Hcolc' as [p'' [d'' Hcolc']]. destruct Hcolc' as [Hpd'' Hcolc']. unfold nodes in *. rewrite Hc'' in Hpd''.
                                    inversion Hpd''. rewrite <- H0 in Hcolc'. rewrite <- H1 in Hcolc'. clear H0. clear H1. clear Hpd''.
                                    destruct Hcolc' as [_ [_ [_ [_ [Hcolc' _]]]]]. apply overlap_flip in Hcolc'. simpl in Hcolc'. rewrite Hmem in Hcolc'. discriminate Hcolc'.
                              ++ apply no_overlap_non_member. intros w Hw Hw'. destruct Hw as [Hw | Hw].
                                 ** apply no_overlap_non_member with (x := c') in Hoverh. apply Hoverh. rewrite Hw. apply Hw'. apply membership_append.
                                    destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := c') in Hlhv. apply Hlhv. right. right. apply Hcolc'.
                                 ** pose proof Hcolc' as Hcolc''. destruct HDh as [_ HDh]. apply HDh in Hcolc'. destruct Hcolc' as [Hcolc' | Hcolc'].
                                    --- destruct Hcolc' as [Hcolc' _]. unfold nodes in *. rewrite Hc'' in Hcolc'. inversion Hcolc'. rewrite H0 in Hw. rewrite H1 in Hw. simpl in Hw. rewrite or_comm in Hw. destruct Hw as [Hw | Hw]. apply Hw.
                                        apply no_overlap_non_member with (x := c') in Hoverh. apply Hoverh. rewrite Hw. apply Hw'. apply membership_append.
                                        destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := c') in Hlhv. apply Hlhv. right. right. apply Hcolc''.
                                    --- apply no_overlap_non_member with (x := w) in HoverL. apply HoverL. apply Hw'.
                                        destruct Hcolc' as [p'' [d'' Hcolc']]. destruct Hcolc' as [Hpd'' Hcolc']. unfold nodes in *. rewrite Hc'' in Hpd''.
                                        inversion Hpd''. rewrite <- H1 in Hcolc'. rewrite <- H2 in Hcolc'. clear H1. clear H2. clear Hpd''.
                                        apply HpdL with (c := c') (p := p') (d := d'). apply Hcolc''. apply Hcolc'. apply Hcolc'. apply Hc''.
                                        apply Hw.

                       + assert (HcDh: get_assigned_value ((h, (ph, zh)) :: Dh) c = get_assigned_value Dh c).
                         { simpl. destruct (h =? c) as [|] eqn:Hhc.
                           - apply eqb_eq in Hhc. rewrite <- Hhc in Hc.
                             assert (Hhmem: In h lhv).
                             { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := h) in Hlhv. apply Hlhv. right. right. apply Hc. }
                             destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. exfalso. apply Hlhv. apply Hhmem.
                           - reflexivity. }
                         rewrite HcDh. pose proof Hc as Hcolc.
                         destruct HDh as [_ HDh]. apply HDh in Hc. destruct Hc as [Hc | Hc]. left. apply Hc. right.
                         destruct Hc as [p [d Hc]]. exists p. exists d. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc.
                         split. repeat split; apply Hc.

                         split.
                         apply overlap_flip. simpl. destruct (member u (p ++ [d])) as [|] eqn:Humem.
                         * apply member_In_equiv_F in HuL. exfalso. apply HuL. apply HpdL with (c := c) (p := p) (d := d). apply Hcolc. apply Hc. apply Hc. apply Hc. apply member_In_equiv. apply Humem.
                         * destruct Hc as [_ [_ [_ [_ [_ [Hc _]]]]]]. apply overlap_flip in Hc. apply Hc.
                         * intros c' d' p' Hc'. simpl in Hc'. destruct (h =? c') as [|] eqn:Hhc'.
                           -- destruct Hc' as [Hcc' Hc']. inversion Hc'. rewrite <- H1. rewrite <- H0. apply eqb_eq in Hhc'. rewrite <- Hhc'.
                              apply overlap_flip. simpl. rewrite <- Hhc' in Hcc'. rewrite Hcc'. destruct (member h (p ++ [d])) as [|] eqn:Hmem.
                              ++ destruct Hc as [_ [_ [_ [_ [_ [Hc _]]]]]]. apply no_overlap_non_member with (x := h) in Hc. exfalso. apply Hc. apply member_In_equiv. apply Hmem.
                                 left. reflexivity.
                              ++ apply no_overlap_non_member. intros w Hw Hw'. destruct Hw as [Hw | Hw].
                                 ** apply no_overlap_non_member with (x := w) in Hoverh. apply Hoverh. apply Hw'.
                                    assert (Hclhv: In c lhv).
                                    { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := c) in Hlhv. apply Hlhv. right. right. apply Hcolc. }
                                    apply membership_splits_list in Hclhv. destruct Hclhv as [lhvc1 [lhvc2 Hclhv]].
                                    apply membership_append. rewrite <- Hclhv. apply membership_append_r. left. apply Hw.
                                 ** apply no_overlap_non_member with (x := w) in HoverL. apply HoverL. apply Hw'.
                                    apply HpdL with (c := c) (d := d) (p := p). apply Hcolc. apply Hc. apply Hc. apply Hc. apply Hw.
                           -- apply Hc. apply Hc'. } }
    + apply subpath_still_d_connected with (u := u). apply Hconn.
    + simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. apply Hpath.
Qed.