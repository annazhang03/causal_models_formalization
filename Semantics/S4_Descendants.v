From CausalDiagrams Require Import CausalPaths.
From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import Assignments.
From Semantics Require Import ColliderDescendants.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.


(* This file expands upon the concepts in ColliderDescendants.v, specifically providing
   a mapping of descendant d to index i, where pa(d)[i] is the previous node in the descendant
   path which d is a part of. *)


(* c -> ...p... -> d is the descendant path. Return assignments of nodes to index i
   as described above *)
Fixpoint get_descendants_for_path' (c d: node) (p: nodes) (G: graph): option (assignments nat) :=
  match p with
   | [] => match (index (find_parents d G) c) with
           | Some i => Some [(d, i)]
           | None => None
           end
   | h :: t => match (index (find_parents h G) c) with
               | Some i => match (get_descendants_for_path' h d t G) with
                           | Some r => Some ((h, i) :: r)
                           | None => None
                           end
               | None => None
               end
   end.

Definition get_descendants_for_path (c d: node) (p: nodes) (G: graph): option (assignments nat) :=
  match (c =? d) with
  | true => Some []
  | false => get_descendants_for_path' c d p G
  end.

Lemma get_descendants_for_path_assignment: forall (c d: node) (p: nodes) (G: graph) (A: assignments nat),
  c =? d = false
  -> get_descendants_for_path c d p G = Some A
  -> is_exact_assignment_for A (p ++ [d]).
Proof.
  intros c d p G A Hcd HA.
  unfold is_exact_assignment_for. split.
  - unfold is_assignment_for. apply forallb_true_iff_mem. intros x Hx. unfold get_descendants_for_path in HA. rewrite Hcd in HA.
    clear Hcd. generalize dependent c. generalize dependent A. induction p as [| hp tp].
    + intros A c HA. simpl in HA. destruct (index (find_parents d G) c) as [i|].
      * inversion HA. simpl. simpl in Hx. destruct Hx as [Hx | F]. rewrite Hx. rewrite eqb_refl. reflexivity. exfalso. apply F.
      * discriminate HA.
    + intros A c HA. simpl in HA. destruct (index (find_parents hp G) c) as [i|] eqn:Hi.
      * destruct (get_descendants_for_path' hp d tp G) as [r|] eqn:Hr.
        -- inversion HA. simpl. destruct (x =? hp) as [|] eqn:Hxhp. reflexivity. simpl.
           simpl in Hx. destruct Hx as [Hx | Hx]. rewrite Hx in Hxhp. rewrite eqb_refl in Hxhp. discriminate Hxhp.
           apply IHtp with (c := hp). apply Hx. apply Hr.
        -- discriminate HA.
      * discriminate HA.
  - intros u Hmem. unfold get_descendants_for_path in HA. rewrite Hcd in HA.
    clear Hcd. generalize dependent c. generalize dependent A. induction p as [| hp tp].
    + intros A c HA. simpl in HA. destruct (index (find_parents d G) c) as [i|].
      * inversion HA. simpl. simpl in Hmem. destruct (u =? d) as [|] eqn:Hud. rewrite eqb_sym in Hud. rewrite Hud in Hmem. discriminate Hmem.
        reflexivity.
      * discriminate HA.
    + intros A c HA. simpl in HA. destruct (index (find_parents hp G) c) as [i|] eqn:Hi.
      * destruct (get_descendants_for_path' hp d tp G) as [r|] eqn:Hr.
        -- inversion HA. simpl. destruct (u =? hp) as [|] eqn:Hxhp. simpl in Hmem. rewrite eqb_sym in Hxhp. rewrite Hxhp in Hmem. discriminate Hmem. simpl.
           apply IHtp with (c := hp). simpl in Hmem. rewrite eqb_sym in Hxhp. rewrite Hxhp in Hmem. apply Hmem. apply Hr.
        -- discriminate HA.
      * discriminate HA.
Qed.


(* Using the descendant paths in D,
   return the mappings from get_descendants_for_path for each collider, flattened into
   one set of assignments *)
Fixpoint get_A4_assignments_for_desc_paths (D: assignments (nodes * node)) (G: graph) (col: nodes): option (assignments nat) :=
  match col with
  | [] => Some []
  | h :: t => match (get_assigned_value D h) with
              | Some (p, d) => match (get_A4_assignments_for_desc_paths D G t) with
                                    | Some r => if (d =? h) then Some r
                                                            else match (get_descendants_for_path h d p G) with
                                                                 | Some A => Some (A ++ r)
                                                                 | None => None
                                                                 end
                                    | None => None
                               end
              | None => None
              end
  end.

Lemma A4_descendant_nodes_existence: forall (D: assignments (nodes * node)) (G: graph) (u v: node) (l: nodes) (Z: nodes),
  descendant_paths_disjoint_col D u v l G Z
  -> exists (A4: assignments nat), get_A4_assignments_for_desc_paths D G (find_colliders_in_path (u, v, l) G) = Some A4.
Proof.
  intros D G u v l Z H.
  generalize dependent u. induction l as [| h t IH].
  - simpl. exists []. reflexivity.
  - intros u H. simpl.
    assert (HA: forall (d: node) (p: nodes), is_directed_path_in_graph (h, d, p) G = true
                -> exists (A: assignments nat), get_descendants_for_path' h d p G = Some A).
    { intros d p Hh. clear IH. clear H. generalize dependent h. induction p as [| hp tp IHp].
      -- intros h Hh. unfold get_descendants_for_path'.
         assert (Hi: exists i: nat, index (find_parents d G) h = Some i).
         { assert (Hd: In h (find_parents d G)).
           { apply edge_from_parent_to_child. simpl in Hh. unfold is_edge in Hh. destruct G as [V E]. simpl. rewrite andb_comm in Hh. simpl in Hh. apply split_and_true in Hh. apply Hh. }
           apply index_exists in Hd. destruct Hd as [i Hi]. exists i. rewrite Hi. reflexivity. }
         destruct Hi as [iu Hiu]. rewrite Hiu. exists [(d, iu)]. reflexivity.
      -- intros h Hh. unfold get_descendants_for_path'.
         assert (Hi: exists i: nat, index (find_parents hp G) h = Some i).
         { assert (Hd: In h (find_parents hp G)).
           { apply edge_from_parent_to_child. simpl in Hh. unfold is_edge in Hh. destruct G as [V E]. simpl. apply split_and_true in Hh. destruct Hh as [Hh _]. apply split_and_true in Hh. apply Hh. }
           apply index_exists in Hd. destruct Hd as [i Hi]. exists i. rewrite Hi. reflexivity. }
         destruct Hi as [iu Hiu]. rewrite Hiu.
         assert (Hind: exists (A: assignments nat), get_descendants_for_path' hp d tp G = Some A). { apply IHp. simpl in Hh. apply split_and_true in Hh. apply Hh. }
         destruct Hind as [A Hind]. unfold get_descendants_for_path' in Hind. rewrite Hind. exists ((hp, iu) :: A). reflexivity. }

    destruct t as [| h' t'].
    + simpl. destruct (is_collider_bool u v h G) as [|] eqn:Hcol.
      * simpl. unfold descendant_paths_disjoint in H.
        assert (Hh: In h (find_colliders_in_path (u, v, [h]) G)).
        { simpl. rewrite Hcol. left. reflexivity. }
        apply H in Hh. destruct Hh as [Hh | Hh].
        -- destruct Hh as [Hh _]. rewrite Hh. rewrite eqb_refl. exists []. reflexivity.
        -- destruct Hh as [p [d [Hpd Hh]]]. rewrite Hpd. assert (Hdh: d =? h = false).
           { destruct (d =? h) as [|] eqn:Hdh. apply eqb_eq in Hdh. destruct Hh as [HdZ [_ [_ [Hh _]]]]. apply no_overlap_non_member with (x := h) in Hh.
             exfalso. apply Hh. left. reflexivity. rewrite <- Hdh. apply HdZ. reflexivity. }
           rewrite Hdh.
           unfold get_descendants_for_path. rewrite eqb_sym in Hdh. rewrite Hdh.
           destruct Hh as [_ [Hh _]]. apply HA in Hh. destruct Hh as [A Hh]. rewrite Hh. exists A. rewrite append_identity. reflexivity.
      * simpl. exists []. reflexivity.
    + apply descendant_paths_disjoint_col_cat in H as H'. apply IH in H'. destruct H' as [A4 H'].
      simpl. destruct (is_collider_bool u h' h G) as [|] eqn:Hcol.
      * assert (Hh: In h (find_colliders_in_path (u, v, h :: h' :: t') G)).
        { simpl. rewrite Hcol. left. reflexivity. }
        apply H in Hh. destruct Hh as [Hh | Hh].
        -- simpl. destruct Hh as [Hh _]. rewrite Hh. rewrite eqb_refl. simpl in H'. rewrite H'. exists A4. reflexivity.
        -- destruct Hh as [p [d [Hpd Hh]]]. simpl. rewrite Hpd. assert (Hdh: d =? h = false).
           { destruct (d =? h) as [|] eqn:Hdh. apply eqb_eq in Hdh. destruct Hh as [HdZ [_ [_ [Hh _]]]]. apply no_overlap_non_member with (x := h) in Hh.
             exfalso. apply Hh. left. reflexivity. rewrite <- Hdh. apply HdZ. reflexivity. }
           rewrite Hdh. unfold get_descendants_for_path. rewrite eqb_sym in Hdh. rewrite Hdh.
           destruct Hh as [_ [Hh _]]. apply HA in Hh. destruct Hh as [A Hh]. rewrite Hh. simpl in H'. rewrite H'. exists (A ++ A4). reflexivity.
      * simpl in H'. rewrite H'. exists A4. reflexivity.
Qed.


Lemma A4_nodes_belong_to_collider: forall (D: assignments (nodes * node)) (G: graph) (u v: node) (l: nodes) (A4: assignments nat) (x: node),
  get_A4_assignments_for_desc_paths D G (find_colliders_in_path (u, v, l) G) = Some A4
  -> is_assigned A4 x = true
  -> exists (c d: node) (p: nodes), In c (find_colliders_in_path (u, v, l) G)
      /\ get_assigned_value D c = Some (p, d) /\ d =? c = false
      /\ In x (p ++ [d]).
Proof.
  intros D G u v l A4 x. intros HA4 Hx.

  generalize dependent D. generalize dependent A4. induction (find_colliders_in_path (u, v, l) G) as [| h t IH].
  - intros A4 Hx D HA4. simpl in HA4. inversion HA4. rewrite <- H0 in Hx. simpl in Hx. discriminate Hx.
  - intros A4 Hx D HA4.
    simpl in HA4. destruct (get_assigned_value D h) as [[p d] | ] eqn:Hpd.
    + destruct (get_A4_assignments_for_desc_paths D G t) as [r|] eqn:Hr.
      * destruct (d =? h) as [|] eqn:Hdh.
        -- inversion HA4. rewrite H0 in Hr. apply IH in Hr. destruct Hr as [c' [d' [p' Hcdp]]]. exists c'. exists d'. exists p'.
           split. right. apply Hcdp. apply Hcdp. apply Hx.
        -- destruct (get_descendants_for_path h d p G) as [A|] eqn:HA.
           ++ inversion HA4. rewrite <- H0 in Hx. destruct (is_assigned A x) as [|] eqn:HAx.
              ** apply get_descendants_for_path_assignment in HA. unfold is_exact_assignment_for in HA. exists h. exists d. exists p. split.
                 left. reflexivity. split. apply Hpd. split. apply Hdh. apply member_In_equiv. destruct (member x (p ++ [d])) as [|] eqn:Hmem.
                 --- reflexivity.
                 --- destruct HA as [_ HA]. apply HA in Hmem. rewrite Hmem in HAx. discriminate HAx.
                 --- rewrite eqb_sym. apply Hdh.
              ** apply assigned_is_true in Hx. apply assigned_is_false in HAx. assert (Hrx: is_assigned r x = true).
                 { apply assigned_is_true. destruct Hx as [xr Hx]. exists xr. rewrite get_assigned_app_None in Hx. apply Hx. apply HAx. }
                 apply IH with (D := D) in Hrx. destruct Hrx as [c' [d' [p' Hcdp]]]. exists c'. exists d'. exists p'.
                 split. right. apply Hcdp. apply Hcdp. apply Hr.
           ++ discriminate HA4.
      * discriminate HA4.
    + discriminate HA4.
Qed.

Lemma desc_path_nodes_in_A4: forall (D: assignments (nodes * node)) (G: graph) (u v d c: node) (l p: nodes) (A4: assignments nat) (x: node),
  get_A4_assignments_for_desc_paths D G (find_colliders_in_path (u, v, l) G) = Some A4
  -> get_assigned_value D c = Some (p, d) /\ d =? c = false
  -> In c (find_colliders_in_path (u, v, l) G)
  -> In x (p ++ [d])
  -> is_assigned A4 x = true.
Proof.
  intros D G u v d c l p A4 x. intros HA4 Hpd Hc Hx.

  generalize dependent D. generalize dependent A4. induction (find_colliders_in_path (u, v, l) G) as [| h t IH].
  - intros A4 D HA4 Hpd. exfalso. apply Hc.
  - intros A4 D HA4 Hpd.
    simpl in HA4. destruct (get_assigned_value D h) as [[ph dh] | ] eqn:Hpdh. 2: { discriminate HA4. }

    destruct (get_A4_assignments_for_desc_paths D G t) as [r|] eqn:Hr. 2: { discriminate HA4. }
    destruct (h =? c) as [|] eqn:Hhc.
    + apply eqb_eq in Hhc. rewrite Hhc in *. clear Hhc. destruct Hpd as [Hpd Hdc]. rewrite Hpd in Hpdh. inversion Hpdh. clear Hpdh.
      rewrite <- H0 in *. rewrite <- H1 in *. clear H0. clear H1.
      rewrite Hdc in HA4. destruct (get_descendants_for_path c d p G) as [rc | ] eqn:Hrc. 2: { discriminate HA4. }
      inversion HA4. apply is_assigned_app.
      apply get_descendants_for_path_assignment in Hrc. apply assigned_is_true. apply assigned_has_value with (L := p ++ [d]).
      split. apply Hx. apply Hrc. rewrite eqb_sym. apply Hdc.
    + destruct Hc as [Hc | Hc]. rewrite Hc in Hhc. rewrite eqb_refl in Hhc. discriminate Hhc.
      destruct (dh =? h) as [|] eqn:Hdh.
      -- inversion HA4. rewrite H0 in Hr. apply IH in Hr. apply Hr.
         apply Hc. apply Hpd.
      -- destruct (get_descendants_for_path h dh ph G) as [rh|] eqn:Hrh. 2: { discriminate HA4. }
         inversion HA4. destruct (is_assigned rh x) as [|] eqn:Hrhx. apply is_assigned_app. apply Hrhx.
         apply is_assigned_app2. apply IH in Hr. apply Hr. apply Hc. apply Hpd.
Qed.

Lemma A4_nodes_map_to_parent: forall (D: assignments (nodes * node)) (A4: assignments nat) (w: node) (G: graph) (u v: node) (l: nodes) (Z: nodes),
  get_A4_assignments_for_desc_paths D G (find_colliders_in_path (u, v, l) G) = Some A4
  -> descendant_paths_disjoint D u v l G Z
  -> is_assigned A4 w = true
  -> exists (c d: node) (p: nodes) (ipd: nat), In c (find_colliders_in_path (u, v, l) G)
      /\ get_assigned_value D c = Some (p, d) /\ d =? c = false
      /\ index (c :: p ++ [d]) w = Some (S ipd)
      /\ exists (w': node) (iw: nat), get_assigned_value A4 w = Some iw /\ index (c :: p ++ [d]) w' = Some ipd /\ index (find_parents w G) w' = Some iw.
Proof.
  intros D A4 w G u v l Z. intros HA4 HD Hw.
  apply A4_nodes_belong_to_collider with (x := w) in HA4 as Hpd. 2: { apply Hw. }
  destruct Hpd as [c [d [p [Hccol [HDc [Hdc Hmem]]]]]]. exists c. exists d. exists p.
  apply index_exists in Hmem as Hipd. destruct Hipd as [ipd Hipd]. exists ipd.
  split. apply Hccol. split. apply HDc. split. apply Hdc.
  unfold descendant_paths_disjoint in HD. destruct HD as [_ HD]. apply HD in Hccol. destruct Hccol as [[Hccol _] | Hccol].
  - rewrite Hccol in HDc. inversion HDc. rewrite H1 in Hdc. rewrite eqb_refl in Hdc. discriminate Hdc.
  - destruct Hccol as [p' [d' [HDc' Hccol]]]. rewrite HDc' in HDc. inversion HDc. rewrite H0 in *. rewrite H1 in *. clear H0. clear H1. clear HDc.
    split.
    + simpl. destruct (c =? w) as [|] eqn:Hcw.
      * apply membership_append_or in Hmem. destruct Hmem as [Hmem | [Hmem | Hmem]].
        -- destruct Hccol as [_ [_ [[_ [Hccol _]] _]]]. exfalso. apply Hccol. apply eqb_eq in Hcw. rewrite Hcw. apply Hmem.
        -- destruct Hccol as [_ [_ [[Hccol _] _]]]. exfalso. apply Hccol. rewrite Hmem. apply eqb_eq. apply Hcw.
        -- exfalso. apply Hmem.
      * rewrite <- Hipd. reflexivity.
    + clear HD. generalize dependent A4. induction (find_colliders_in_path (u, v, l) G) as [| h t IH].
      * intros A4 HA4 Hw. simpl in HA4. inversion HA4. rewrite <- H0 in Hw. simpl in Hw. discriminate Hw.
      * intros A4 HA4 Hw. simpl in HA4.
        assert (Hhpd: exists (hp: nodes) (hd: node), get_assigned_value D h = Some (hp, hd)).
        { destruct (get_assigned_value D h) as [[hp hd] | ] eqn:Hhpd. exists hp. exists hd. reflexivity. discriminate HA4. }
        destruct Hhpd as [hp [hd Hhpd]]. rewrite Hhpd in *.
        assert (Hr: exists (r: assignments nat), get_A4_assignments_for_desc_paths D G t = Some r).
        { destruct (get_A4_assignments_for_desc_paths D G t) as [r | ] eqn:Hr. exists r. reflexivity. discriminate HA4. }
        destruct Hr as [r Hr]. rewrite Hr in *.

        destruct (hd =? h) as [|] eqn:Hhdh.
        -- apply IH in HA4. apply HA4. apply Hw.
        -- assert (Hrh: exists (r: assignments nat), get_descendants_for_path h hd hp G = Some r).
           { destruct (get_descendants_for_path h hd hp G) as [rh | ] eqn:Hrh. exists rh. reflexivity. discriminate HA4. }
           destruct Hrh as [rh Hrh]. rewrite Hrh in *.

           inversion HA4. rewrite <- H0 in Hw. destruct (h =? c) as [|] eqn:Hhc.
           { unfold get_descendants_for_path in Hrh. rewrite eqb_sym in Hhdh. rewrite Hhdh in Hrh.
             apply eqb_eq in Hhc. rewrite Hhc in *. clear Hhc. rewrite HDc' in Hhpd. inversion Hhpd. rewrite <- H1 in *. rewrite <- H2 in *.
             clear H1. clear H2. clear Hhpd. clear IH. clear HDc'. destruct Hccol as [_ [_ [Hccol _]]]. clear H0. clear HA4. clear Hhdh. clear Hdc.
             generalize dependent ipd. generalize dependent rh. generalize dependent c. induction p as [| ph pt IH].
             - intros c Hcyc rh Hw Hrh ipd Hipd. assert (Hdw: d = w). { simpl in Hmem. destruct Hmem as [Hmem | Hmem]. apply Hmem. exfalso. apply Hmem. }
               simpl in Hrh. destruct (index (find_parents d G) c) as [iw|] eqn:Hiw.
               + exists c. exists iw. repeat split.
                 * inversion Hrh. simpl.
                   rewrite Hdw. rewrite eqb_refl. reflexivity.
                 * simpl. rewrite eqb_refl. simpl in Hipd. rewrite Hdw in Hipd. rewrite eqb_refl in Hipd. symmetry. apply Hipd.
                 * rewrite <- Hdw. apply Hiw.
               + discriminate Hrh.
             - intros c Hcyc rh Hw Hrh ipd Hipd. simpl in Hrh. destruct (index (find_parents ph G) c) as [iph|] eqn:Hiph. 2: { discriminate Hrh. }
               destruct (get_descendants_for_path' ph d pt G) as [rph|] eqn:Hrph. 2: { discriminate Hrh. }
               destruct (ph =? w) as [|] eqn:Hphw.
               -- apply eqb_eq in Hphw. rewrite Hphw in *. inversion Hrh. exists c. exists iph. repeat split.
                  ++ simpl. rewrite eqb_refl. reflexivity.
                  ++ simpl. rewrite eqb_refl. simpl in Hipd. rewrite eqb_refl in Hipd. symmetry. apply Hipd.
                  ++ apply Hiph.
               -- destruct Hmem as [Hmem | Hmem]. rewrite Hmem in Hphw. rewrite eqb_refl in Hphw. discriminate Hphw. simpl in Hipd.
                  rewrite Hphw in Hipd. destruct (index (pt ++ [d]) w) as [ipd'|]. 2: { discriminate Hipd. }
                  apply IH with (rh := rph) (ipd := ipd') (c := ph) in Hmem.
                  ++ destruct Hmem as [w' [iw [Hiw [Hipd' Hw']]]]. exists w'. exists iw. repeat split.
                     ** inversion Hrh. simpl. rewrite Hphw. apply Hiw.
                     ** simpl. destruct (c =? w') as [|] eqn:Hcw'.
                        --- assert (Hmem: In w' ((ph :: pt) ++ [d])). { apply index_exists. exists ipd'. symmetry. apply Hipd'. }
                            apply acyclic_path_count with (x := w') in Hcyc. simpl in Hcyc. rewrite Hcw' in Hcyc. inversion Hcyc.
                            apply member_count_at_least_1 in Hmem. simpl in Hmem. lia. right. apply Hmem.
                        --- simpl in Hipd'. rewrite Hipd'. symmetry. apply Hipd.
                     ** apply Hw'.
                  ++ apply acyclic_path_cat with (u := c). apply Hcyc.
                  ++ inversion Hrh. rewrite <- H0 in Hw. simpl in Hw. rewrite eqb_sym in Hw. rewrite Hphw in Hw. simpl in Hw. apply Hw.
                  ++ apply Hrph.
                  ++ reflexivity. }

           apply get_descendants_for_path_assignment in Hrh. 2: { rewrite eqb_sym. apply Hhdh. }
           assert (Hrhw: is_assigned rh w = false).
           { unfold is_exact_assignment_for in Hrh. apply Hrh. destruct (member w (hp ++ [hd])) as [|] eqn:Hmemw.
             - destruct Hccol as [_ [_ [_ [_ [_ Hccol]]]]]. assert (Hover: overlap (c :: p ++ [d]) (h :: hp ++ [hd]) = false).
               { apply Hccol. split. rewrite eqb_sym. apply Hhc. apply Hhpd. }
               exfalso. apply no_overlap_non_member with (x := w) in Hover. apply Hover. right. apply Hmem. right. apply member_In_equiv. apply Hmemw.
             - reflexivity. }
           assert (Hrw: is_assigned r w = true).
           { apply assigned_is_true in Hw. destruct Hw as [x Hw]. rewrite get_assigned_app_None in Hw. apply assigned_is_true. exists x. apply Hw.
             apply assigned_is_false. apply Hrhw. }
           apply IH in Hrw. 2: { reflexivity. }
           destruct Hrw as [w' [iw Hrw]]. exists w'. exists iw. split.
           rewrite get_assigned_app_None. apply Hrw. apply assigned_is_false. apply Hrhw. apply Hrw.
Qed.