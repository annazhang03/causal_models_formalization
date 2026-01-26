From Semantics Require Import FunctionRepresentation.
From Semantics Require Import FindValue.
From Semantics Require Import SemanticSeparationDef.
From CausalDiagrams Require Import CausalPaths.
From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import Assignments.
From CausalDiagrams Require Import DSeparation.
From CausalDiagrams Require Import UnblockedAncestors.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import TopologicalSort.
From DAGs Require Import Descendants.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.

Import ListNotations.
From Utils Require Import EqType.



(*
   This file contains the primary lemmas of the backward direction of the equivalence proof:
   that d-separation implies semantic separation. We prove the contrapositive: that if u and v
   are not semantically separated, then there must exist a d-connected path between them.

   In particular, if u and v are not semantically separated, then there exists some graph function
   and sequence of unobserved-terms assignments satisfying the definition of semantically_separated
   (SemanticSeparationDef.v), such that f(v) changes between the first and last elements of the
   sequence. In this file, we attribute that change in a node's value to a specific unblocked
   ancestor, which allows us to construct a d-connected path by concatenating several smaller
   paths created from unblocked ancestors.
*)


(* For any node u such that f(u) changes under U1 vs U2, and U1 and U2 both properly condition
   on Z, there must exist an unblocked ancestor of u, `a` (possibly u itself) such that
   U1(a) \neq U2(a) and f(a) changes under U1 vs U2. We can thus "attribute" the change in
   u to a. *)
Lemma nodefun_value_only_affected_by_unblocked_ancestors {X: Type} `{EqType X}: forall (G: graph) (u: node) (Z: nodes) (U1 U2 AZ: assignments X) (g: graphfun),
  G_well_formed G = true /\ contains_cycle G = false
  -> find_value G g u U1 [] <> find_value G g u U2 []
  -> is_assignment_for U1 (nodes_in_graph G) = true /\ is_assignment_for U2 (nodes_in_graph G) = true
  -> node_in_graph u G = true
  -> unobs_conditions_on_Z G g U1 AZ Z /\ unobs_conditions_on_Z G g U2 AZ Z
  -> exists (a: node), In a (find_unblocked_ancestors G u Z)
      /\ get_assigned_value U1 a <> get_assigned_value U2 a
      /\ find_value G g a U1 [] <> find_value G g a U2 [].
Proof.
  intros G u Z U1 U2 AZ g.
  intros HG Hg [HU1 HU2] HuG [HZ1 HZ2].

  assert (Hpa1: exists (P: assignments X), find_values G g (find_parents u G) U1 [] = Some P
                /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents u G)
                /\ exists (unobs: X), get_assigned_value U1 u = Some unobs
                /\ find_value G g u U1 [] = Some (g u (unobs, pa))).
  { apply find_value_evaluates_to_g. easy. }
  assert (Hpa2: exists (P: assignments X), find_values G g (find_parents u G) U2 [] = Some P
                /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents u G)
                /\ exists (unobs: X), get_assigned_value U2 u = Some unobs
                /\ find_value G g u U2 [] = Some (g u (unobs, pa))).
  { apply find_value_evaluates_to_g. easy. }
  destruct Hpa1 as [P1 [HP1 [pa1 [Hpa1 [unobs1 [Hunobs1 Hg1]]]]]].
  destruct Hpa2 as [P2 [HP2 [pa2 [Hpa2 [unobs2 [Hunobs2 Hg2]]]]]].

  destruct (eqb unobs1 unobs2) as [|] eqn:Hunobs.
  - apply eqb_eq' in Hunobs.

    assert (Hts: exists (ts: nodes), topological_sort G = Some ts).
    { apply topo_sort_exists_for_acyclic. easy. }
    destruct Hts as [ts Hts].

    assert (Hi: exists (i: nat), Some i = index ts u).
    { apply index_exists. apply topo_sort_contains_nodes with (u := u) in Hts. apply Hts. apply HuG. }
    destruct Hi as [i Hi].

    assert (Hj: exists (j: nat), Some j = index ts u /\ j <= i).
    { exists i. split. apply Hi. easy. }
    clear Hi.

    (* Perform induction on the index of u in the topological sort of the graph, with
       the hypothesis that the statement holds for any node with index less than i *)
    generalize dependent pa2. generalize dependent P2. generalize dependent pa1. generalize dependent P1.
    generalize dependent unobs2. generalize dependent unobs1. generalize dependent u. induction i as [| i' IH].
    + intros u Hg HuG Hj unobs1 Hunobs1 unobs2 Hunobs2 Hunobs P1 HP1 pa1 Hpa1 Hg1 P2 HP2 pa2 Hpa2 Hg2.
      (* j = 0, so u is the first node, i.e. has no parents. Then, f(u) cannot change
         if U1(u) = U2(u), since no arguments change to the nodefun *)
      destruct Hj as [j [Hi Hj0]].
      destruct j as [| j'].
      * assert (Hpar: find_parents u G = []).
        { destruct ts as [| h t].
          - simpl in Hi. discriminate Hi.
          - simpl in Hi. destruct (h =? u) as [|] eqn:Hhu.
            + apply topo_sort_first_node_no_parents with (ts := t). split. easy. apply eqb_eq in Hhu. rewrite Hhu in Hts. apply Hts.
            + destruct (index t u) as [j|]. inversion Hi. discriminate Hi. }
        rewrite Hpar in *. simpl in Hpa1. inversion Hpa1. rewrite H1 in *.
        simpl in Hpa2. inversion Hpa2. rewrite H2 in *.
        exfalso. apply Hg. rewrite Hg1. rewrite Hg2. rewrite Hunobs. reflexivity.
      * lia.
    + intros u Hg HuG Hj unobs1 Hunobs1 unobs2 Hunobs2 Hunobs P1 HP1 pa1 Hpa1 Hg1 P2 HP2 pa2 Hpa2 Hg2.
      rewrite Hg1 in Hg. rewrite Hg2 in Hg. rewrite Hunobs in Hg.
      assert (HP: Some P1 <> Some P2).
      { intros F.
        assert (Hpa: Some pa1 <> Some pa2).
        { intros F'. apply Hg. inversion F'. reflexivity. }
        apply Hpa. rewrite Hpa1. rewrite Hpa2. inversion F. reflexivity. }
      assert (Hp: exists (p: node), In p (find_parents u G) /\ find_value G g p U1 [] <> find_value G g p U2 []).
      { apply find_values_unequal with (P1 := P1) (P2 := P2). easy. easy. intros F. apply HP. rewrite F. reflexivity. }
      destruct Hp as [p [Hmemp Hp]].
      (* f(p) changes between U1 and U2, so we can apply the induction hypothesis to p,
         since p is a parent of u and thus precedes u in the topological sort *)

      assert (HpG: node_in_graph p G = true /\ node_in_graph u G = true).
      { apply edge_corresponds_to_nodes_in_well_formed. split. easy. apply edge_from_parent_to_child. apply Hmemp. }
      destruct HpG as [HpG _].

      assert (Hppa1: exists (P: assignments X), find_values G g (find_parents p G) U1 [] = Some P
                /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents p G)
                /\ exists (unobs: X), get_assigned_value U1 p = Some unobs
                /\ find_value G g p U1 [] = Some (g p (unobs, pa))).
      { apply find_value_evaluates_to_g. easy. }
      assert (Hppa2: exists (P: assignments X), find_values G g (find_parents p G) U2 [] = Some P
                    /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents p G)
                    /\ exists (unobs: X), get_assigned_value U2 p = Some unobs
                    /\ find_value G g p U2 [] = Some (g p (unobs, pa))).
      { apply find_value_evaluates_to_g. easy. }
      destruct Hppa1 as [P1p [HP1p [pa1p [Hpa1p [unobs1p [Hunobs1p Hg1p]]]]]].
      destruct Hppa2 as [P2p [HP2p [pa2p [Hpa2p [unobs2p [Hunobs2p Hg2p]]]]]].

      assert (Hpu: In p (find_unblocked_ancestors G u Z)).
      { apply unblocked_ancestors_have_unblocked_directed_path. right. exists []. repeat split.
         ++ simpl. unfold is_edge. destruct G as [V E]. simpl in HuG. rewrite HuG. simpl in HpG. rewrite HpG.
            apply edge_from_parent_to_child in Hmemp. simpl in Hmemp. rewrite Hmemp. reflexivity.
         ++ repeat split. intros F.
            apply edge_from_parent_to_child in Hmemp. rewrite F in Hmemp.
            assert (Hmemp': is_edge (u, u) G = false). { apply acyclic_no_self_loop. apply HG. easy. }
            unfold is_edge in Hmemp'. destruct G as [V E]. simpl in HuG. rewrite HuG in Hmemp'. simpl in Hmemp'.
            simpl in Hmemp. rewrite Hmemp in Hmemp'. discriminate Hmemp'.
         ++ intros F. apply F.
         ++ intros F. apply F.
         ++ intros w [Hw | Hw].
            ** intros Hmem. unfold unobs_conditions_on_Z in HZ1. unfold unobs_conditions_on_Z in HZ2.
               assert (Hpmem: In p Z /\ node_in_graph p G = true).
               { split. rewrite <- Hw. apply Hmem. apply HpG. }
               apply HZ1 in Hpmem as HAZ1. apply HZ2 in Hpmem as HAZ2.
               rewrite Hw in *. apply Hp. rewrite HAZ1. rewrite HAZ2. reflexivity.
            ** exfalso. apply Hw. }

      destruct (eqb unobs1p unobs2p) as [|] eqn:Hunobsp.
      * specialize IH with (u := p) (unobs1 := unobs1p) (unobs2 := unobs2p) (P1 := P1p) (pa1 := pa1p) (P2 := P2p) (pa2 := pa2p).
        assert (Hind: exists a : node,
                       In a (find_unblocked_ancestors G p Z) /\
                       get_assigned_value U1 a <> get_assigned_value U2 a /\
                       find_value G g a U1 [] <> find_value G g a U2 []).
        { apply IH. clear IH. easy. easy.
          - assert (Hpj: exists (j i': nat), Some j = index ts p /\ Some i' = index ts u /\ j < i').
            { apply topo_sort_parents with (G := G). easy. easy. }
            destruct Hpj as [ixp [ixu [Hixp [Hixu Hix]]]].
            exists ixp. split. apply Hixp.
            destruct Hj as [j [Hj Hji']]. rewrite <- Hj in Hixu. inversion Hixu. rewrite H1 in Hix. lia.
          - easy.
          - easy.
          - apply eqb_eq' in Hunobsp. apply Hunobsp.
          - easy.
          - easy.
          - easy.
          - easy.
          - easy.
          - easy. }
        destruct Hind as [a Ha]. exists a. repeat split.
        -- apply unblocked_ancestors_transitive with (ancu' := p).
           ++ apply Hpu.
           ++ apply Ha.
        -- apply Ha.
        -- apply Ha.
      * exists p. repeat split.
        -- apply Hpu.
        -- intros F. rewrite Hunobs1p in F. rewrite Hunobs2p in F. inversion F. rewrite H1 in Hunobsp. rewrite eqb_refl' in Hunobsp. discriminate Hunobsp.
        -- apply Hp.

  - (* u itself satisfies the criteria! *) exists u. repeat split.
    + unfold find_unblocked_ancestors. left. reflexivity.
    + intros F. rewrite Hunobs1 in F. rewrite Hunobs2 in F. inversion F. rewrite H1 in Hunobs. rewrite eqb_refl' in Hunobs. discriminate Hunobs.
    + apply Hg.
Qed.


(* Return conditioned nodes (nodes in Z) that have an unblocked ancestor in S
   Assumes AZ is set of assignments for Z *)
Fixpoint find_unblocked_ancestors_in_Z_contributors {X: Type} `{EqType X} (G: graph) (Z: nodes) (AZ: assignments X) (S: nodes): nodes :=
  match AZ with
  | [] => []
  | (z, x) :: AZ' => if (overlap (find_unblocked_ancestors G z Z) S)
                       then z :: (find_unblocked_ancestors_in_Z_contributors G Z AZ' S)
                       else find_unblocked_ancestors_in_Z_contributors G Z AZ' S
  end.

Lemma contributor_then_in_AZ {X: Type} `{EqType X}: forall (G: graph) (Z: nodes) (AZ: assignments X) (S: nodes) (z: node),
  In z (find_unblocked_ancestors_in_Z_contributors G Z AZ S)
  -> is_assigned AZ z = true.
Proof.
  intros G Z AZ S z Hz.
  induction AZ as [| [z1 x1] AZ' IH].
  - simpl in Hz. exfalso. apply Hz.
  - simpl. destruct (z =? z1) as [|] eqn:Hzz1. reflexivity.
    destruct (overlap (find_unblocked_ancestors G z1 Z) S) as [|] eqn:Hz1.
    + simpl. simpl in Hz. simpl in Hz1. rewrite Hz1 in Hz. destruct Hz as [Hz | Hz]. rewrite Hz in Hzz1. rewrite eqb_refl in Hzz1. discriminate Hzz1.
      apply IH. apply Hz.
    + simpl. apply IH. simpl in Hz. simpl in Hz1. rewrite Hz1 in Hz. apply Hz.
Qed.

Lemma ancestors_overlap_with_seq_then_contributor {X: Type} `{EqType X}: forall (G: graph) (Z: nodes) (AZ: assignments X) (S: nodes) (z: node),
  is_assigned AZ z = true
  -> overlap (find_unblocked_ancestors G z Z) S = true
     <-> In z (find_unblocked_ancestors_in_Z_contributors G Z AZ S).
Proof.
  intros G Z AZ S z HAZ. split.
  { intros Hover.
    induction AZ as [| [z1 x1] AZ' IH].
    - simpl in HAZ. discriminate HAZ.
    - simpl in HAZ. apply split_orb_true in HAZ. destruct HAZ as [HAZ | HAZ].
      + apply eqb_eq in HAZ. rewrite <- HAZ in *. simpl. simpl in Hover. rewrite Hover. left. reflexivity.
      + apply IH in HAZ. destruct (overlap (find_unblocked_ancestors G z1 Z) S) as [|] eqn:Hz1.
        * simpl. simpl in Hz1. rewrite Hz1. right. apply HAZ.
        * simpl. simpl in Hz1. rewrite Hz1. apply HAZ. }
  { intros Hz.
    induction AZ as [| [z1 x1] AZ' IH].
    - simpl in HAZ. discriminate HAZ.
    - simpl in HAZ. destruct (z =? z1) as [|] eqn:Hzz1.
      + apply eqb_eq in Hzz1. rewrite <- Hzz1 in *. destruct (overlap (find_unblocked_ancestors G z Z) S) as [|] eqn:Hover. reflexivity.
        simpl in Hz. simpl in Hover. rewrite Hover in Hz. apply IH. apply contributor_then_in_AZ in Hz. apply Hz. apply Hz.
      + simpl in Hz. simpl in HAZ. destruct (overlap (find_unblocked_ancestors G z1 Z) S) as [|] eqn:Hover.
        * simpl in Hover. rewrite Hover in Hz. destruct Hz as [Hz | Hz]. rewrite Hz in Hzz1. rewrite eqb_refl in Hzz1. discriminate Hzz1.
          apply IH. apply HAZ. apply Hz.
        * simpl in Hover. rewrite Hover in Hz. apply IH. apply HAZ. apply Hz. }
Qed.



(* Return conditioned nodes that were disturbed by the sequence of unobserved-terms assignments, as described in the
   definition of semantic separation *)
Fixpoint get_conditioned_nodes_that_change_in_seq_simpler {X: Type} `{EqType X} (L: list (assignments X)) (Z: nodes) (AZ: assignments X) (G: graph): nodes :=
  match L with
  | U1 :: L' => match L' with
                | U2 :: U3 :: L''' => find_unblocked_ancestors_in_Z_contributors G Z AZ (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) U1 U2)
                                                       ++ get_conditioned_nodes_that_change_in_seq_simpler L' Z AZ G
                | _ => []
                end
  | _ => []
  end.

Fixpoint get_conditioned_nodes_that_change_in_seq {X: Type} `{EqType X} (L: list (assignments X)) (Z: nodes) (AZ: assignments X) (G: graph): nodes :=
  match L with
  | [] => []
  | U1 :: L' => match L' with
                      | [] => []
                      | U2 :: L'' => match L'' with
                                           | [] => []
                                           | U3 :: L''' =>
                                                       find_unblocked_ancestors_in_Z_contributors G Z AZ (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) U1 U2)
                                                       ++ get_conditioned_nodes_that_change_in_seq L' Z AZ G
                                           end
                      end
  end.

Lemma get_conditioned_nodes_that_change_in_seq_equiv {X: Type} `{EqType X}: forall (L: list (assignments X)) (Z: nodes) (AZ: assignments X) (G: graph),
  get_conditioned_nodes_that_change_in_seq_simpler L Z AZ G = get_conditioned_nodes_that_change_in_seq L Z AZ G.
Proof.
  intros L Z AZ G.
  induction L as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct t as [| h' t'].
    + reflexivity.
    + destruct t' as [| h'' t''].
      * reflexivity.
      * reflexivity.
Qed.


Lemma conditioned_nodes_that_change_in_Z {X: Type} `{EqType X}: forall (L: list (assignments X)) (Z: nodes) (AZ: assignments X) (G: graph) (z: node),
  In z (get_conditioned_nodes_that_change_in_seq L Z AZ G)
  -> is_assigned AZ z = true.
Proof.
  intros L Z AZ G z Hz.
  induction L as [| Ua L' IH].
  - simpl in Hz. exfalso. apply Hz.
  - destruct L' as [| Ub L']. exfalso. apply Hz.
    destruct L' as [| U1 L']. exfalso. apply Hz.
    simpl in Hz. apply membership_append_or in Hz. destruct Hz as [Hz | Hz].
    + clear IH. induction AZ as [| [z1 x1] AZ' IH].
      * exfalso. apply Hz.
      * destruct (overlap (find_unblocked_ancestors G z1 Z) (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub)) as [|] eqn:Hover.
        -- simpl in Hz. simpl in Hover. rewrite Hover in Hz. destruct Hz as [Hz | Hz].
           ++ simpl. rewrite Hz. rewrite eqb_refl. reflexivity.
           ++ simpl. apply split_orb_true. right. apply IH. apply Hz.
        -- simpl in Hz. simpl in Hover. rewrite Hover in Hz. simpl. apply split_orb_true. right. apply IH. apply Hz.
    + apply IH. apply Hz.
Qed.



(* the generalization of `nodefun_value_only_affected_by_unblocked_ancestors` to sequences of unobserved-terms assignments:
   if f(v) changes from Ua to Ub' over some sequence, then either
   1. u and v share an unblocked ancestor, or
   2. there is some
      unblocked ancestor of v, `a`, such that a is also an unblocked ancestor of a conditioned node that was disturbed at some
      point during the sequence propagation *)
Lemma nodefun_value_only_affected_by_unblocked_ancestors_seq {X: Type} `{EqType X}: forall (G: graph) (u v: node) (Z: nodes) (Ua Ub Ub' AZ: assignments X) (L: list (assignments X)) (g: graphfun),
  G_well_formed G = true /\ contains_cycle G = false
  -> Ub' = last (Ub :: L) Ub
  -> find_value G g v Ua [] <> find_value G g v Ub' []
  -> is_assignment_for Ua (nodes_in_graph G) = true /\ is_assignment_for Ub' (nodes_in_graph G) = true
  -> node_in_graph v G = true
  -> unobs_conditions_on_Z G g Ua AZ Z /\ unobs_conditions_on_Z G g Ub' AZ Z
  -> assignments_change_only_for_subset Ua Ub (find_unblocked_ancestors G u Z)
  -> assignments_change_only_for_Z_anc_seq (Ua :: Ub :: L) Z AZ G
  -> exists (a: node), In a (find_unblocked_ancestors G v Z)
      /\ (In a (find_unblocked_ancestors G u Z) \/
         exists (z: node),
           In a (find_unblocked_ancestors G z Z)
           /\ In z (get_conditioned_nodes_that_change_in_seq (Ua :: Ub :: L) Z AZ G)).
Proof.
  intros G u v Z Ua Ub Ub' AZ L g. intros HG HeqUb' Hfv [HUa HUb'] Hnodev [HcondUa HcondUb'] HUab Hseq.
  assert (Ha: exists (a: node), In a (find_unblocked_ancestors G v Z)
      /\ get_assigned_value Ua a <> get_assigned_value Ub' a
      /\ find_value G g a Ua [] <> find_value G g a Ub' []).
  { apply nodefun_value_only_affected_by_unblocked_ancestors with (AZ := AZ). apply HG. apply Hfv. split. apply HUa. apply HUb'.
    apply Hnodev. split. apply HcondUa. apply HcondUb'. }
  destruct Ha as [a [Hav [Hua Hfa]]]. exists a. split. apply Hav.

  assert (Hnodea: In a (nodes_in_graph G)).
  { apply unblocked_ancestors_have_unblocked_directed_path in Hav. destruct Hav as [Hav | Hav]. rewrite Hav. destruct G as [V E]. simpl. simpl in Hnodev. apply member_In_equiv. apply Hnodev.
    destruct Hav as [l [Hl _]]. apply directed_path_is_path in Hl. apply node_in_path_has_edge with (w := a) in Hl. destruct Hl as [x [_ Hx]].
    assert (node_in_graph a G = true).
    { apply is_edge_then_node_in_graph with (v := x). apply or_comm. apply Hx. }
    destruct G as [V E]. simpl. apply member_In_equiv. apply H0. rewrite node_in_path_equiv. simpl. rewrite eqb_refl. reflexivity. }

  destruct (member a (find_unblocked_ancestors G u Z)) as [|] eqn:Hmem.
  - left. apply member_In_equiv in Hmem. apply Hmem.
  - destruct L as [| U1 L'].
    + simpl in HeqUb'. rewrite HeqUb' in *. unfold assignments_change_only_for_subset in HUab. exfalso.
      apply member_In_equiv_F in Hmem. apply HUab in Hmem. apply Hua. apply Hmem.
    + assert (Huaa: exists (ua: X), get_assigned_value Ua a = Some ua).
      { apply assigned_has_value with (L := nodes_in_graph G). split. apply Hnodea. apply HUa. } destruct Huaa as [ua Hua'].
      assert (HUb: is_assignment_for Ub (nodes_in_graph G) = true).
      { apply sequence_of_ancestors_assignment with (U := Ub) (S := (find_unblocked_ancestors G u Z)) in Hseq. apply Hseq. apply HUa. apply HUab. right. left. reflexivity. }
      assert (Huaa': exists (ub: X), get_assigned_value Ub a = Some ub).
      { apply assigned_has_value with (L := nodes_in_graph G). split. apply Hnodea. apply HUb. }
      destruct Huaa' as [ub Hub].
      destruct (eqb ua ub) as [|] eqn:Huab.
      2: { (* if Ua(a) \neq Ub(a), then a is an unblocked ancestor of u, since only unb(u) are allowed to change
              between Ua and Ub *)
           left. unfold assignments_change_only_for_subset in HUab.
           apply member_In_equiv_F in Hmem. apply HUab in Hmem. rewrite Hua' in Hmem. rewrite Hub in Hmem. inversion Hmem. rewrite H1 in Huab.
           rewrite eqb_refl' in Huab. discriminate Huab. }
      (* Ua(a) = Ub(a)*)
      assert (Hubb': get_assigned_value Ub a <> get_assigned_value Ub' a).
      { intros F. rewrite Hub in F. apply eqb_eq' in Huab. rewrite <- Huab in F.
        rewrite <- Hua' in F. apply Hua. apply F. }
      right.
      clear HUab. clear HcondUa. clear Hfa. clear Hfv. clear Hua'. generalize dependent ub. generalize dependent Ua. generalize dependent Ub. generalize dependent U1.
      induction L' as [| U2 L' IH].
      * (* the sequence is only Ua, Ub, U1. Thus, a changed value from Ub to U1, so a must be an unblocked ancestor of some z \in Z
           whose value changed from Ua to Ub and was repaired with U1 *)
        intros U1 Ub HeqUb' HUb Hubb' Ua HUa Hseq Hua ub Hub Huab. simpl in HeqUb'. rewrite HeqUb' in *. simpl in Hseq.
        assert (Hz: exists (z: node), In a (find_unblocked_ancestors G z Z)
                    /\ overlap (find_unblocked_ancestors G z Z) (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub) = true
                    /\ is_assigned AZ z = true).
        { apply ancestor_in_Z_corresponds_to_conditioned_node_rev.
          destruct (member a (find_unblocked_ancestors_in_Z G Z AZ
                        (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub))) as [|] eqn:HmemZ.
          + apply member_In_equiv in HmemZ. apply HmemZ.
          + assert (F: get_assigned_value Ub a = get_assigned_value U1 a).
            { destruct Hseq as [Hseq _]. unfold assignments_change_only_for_subset in Hseq. apply Hseq. intros F. apply member_In_equiv_F in HmemZ. apply HmemZ. apply F. }
            exfalso. apply Hubb'. apply F. }
        destruct Hz as [z [Haz [Hoverz HAZz]]]. exists z. split. apply Haz. simpl. rewrite append_identity.
        apply ancestors_overlap_with_seq_then_contributor. apply HAZz. apply Hoverz.
      * (* the sequence has an additional U2, we apply the induction hypothesis, since the unobserved value of a does not
           change from Ua to Ub *)
        intros U1 Ub HeqUb' HUb Hubb' Ua HUa Hseq Hua ub Hub Huab.

        assert (HU1: is_assignment_for U1 (nodes_in_graph G) = true).
        { destruct Hseq as [Hseq1 Hseq2].
          apply sequence_of_ancestors_assignment with (U := U1) (L := U2 :: L') (G := G) (Z := Z) (AZ := AZ) in Hseq1.
          apply Hseq1. apply HUb. simpl in Hseq2. apply Hseq2. right. left. reflexivity. }

        assert (Hu1a: exists (u1: X), get_assigned_value U1 a = Some u1).
        { apply assigned_has_value with (L := nodes_in_graph G). split. apply Hnodea. apply HU1. }
        destruct Hu1a as [u1 Hu1].

        specialize IH with (U1 := U2) (Ub := U1) (Ua := Ub) (ub := u1).
        destruct (eqb ub u1) as [|] eqn:Hub1.
        -- assert (Hind: exists z : node,
                           In a (find_unblocked_ancestors G z Z) /\
                           In z (get_conditioned_nodes_that_change_in_seq (Ub :: U1 :: U2 :: L') Z AZ G)).
           { apply IH.
             - rewrite HeqUb'. apply last_suffix.
             - apply HU1.
             - intros F. apply Hubb'. rewrite Hub. apply eqb_eq' in Hub1. rewrite Hub1. rewrite <- Hu1. apply F.
             - apply HUb.
             - simpl in Hseq. apply Hseq.
             - apply Hubb'.
             - apply Hu1.
             - apply eqb_eq' in Huab. rewrite Huab. apply Hub1. }
            destruct Hind as [z Hz]. exists z. split. apply Hz. simpl. apply membership_append_r. destruct Hz as [_ Hz].
            simpl in Hz. apply Hz.

        -- (* the unobserved value of a changes from Ub to U1, so find conditioned node z whose value was disturbed
              by Ub and repaired by U1 *)
              assert (Hz: exists (z: node), In a (find_unblocked_ancestors G z Z)
                      /\ overlap (find_unblocked_ancestors G z Z) (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub) = true
                      /\ is_assigned AZ z = true).
           { apply ancestor_in_Z_corresponds_to_conditioned_node_rev.
             destruct (member a (find_unblocked_ancestors_in_Z G Z AZ
                           (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub))) as [|] eqn:HmemZ.
             + apply member_In_equiv in HmemZ. apply HmemZ.
             + assert (F: get_assigned_value Ub a = get_assigned_value U1 a).
               { destruct Hseq as [Hseq _]. unfold assignments_change_only_for_subset in Hseq. apply Hseq. intros F. apply member_In_equiv_F in HmemZ. apply HmemZ. apply F. }
               exfalso. rewrite Hub in F. rewrite Hu1 in F. inversion F. rewrite H1 in Hub1. rewrite eqb_refl' in Hub1. discriminate Hub1. }

           destruct Hz as [z [Haz [Hoverz HAZz]]]. exists z. split. apply Haz. simpl. apply membership_append.
           apply ancestors_overlap_with_seq_then_contributor. apply HAZz. apply Hoverz.
Qed.



(* If z is repaired at some point during the reparation steps of the semantic separation definition, then
   we can pinpoint the change in z to a subsequence of three unobserved-terms assignments [U1, U2, U3] such that
   the value of z was disturbed by changes from U1 to U2 (and repaired by U3) *)
Lemma conditioned_nodes_that_change_in_seq_attached_to_U_sublist {X: Type} `{EqType X}: forall (G: graph) (z: node) (Z: nodes) (Ua Ub AZ: assignments X) (L: list (assignments X)),
  In z (get_conditioned_nodes_that_change_in_seq (Ua :: Ub :: L) Z AZ G)
  <-> exists (U1 U2 U3: assignments X), sublist_X [U1; U2; U3] (Ua :: Ub :: L) = true
     /\ In z (find_unblocked_ancestors_in_Z_contributors G Z AZ (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) U1 U2)).
Proof.
  intros G z Z Ua Ub AZ L. split.
  { intros Hz.
    generalize dependent Ub. generalize dependent Ua. induction L as [| U1 L' IH].
    - intros Ua Ub Hz. simpl in Hz. exfalso. apply Hz.
    - intros Ua Ub Hz. simpl in Hz. apply membership_append_or in Hz. destruct Hz as [Hz | Hz].
      + exists Ua. exists Ub. exists U1. split.
        * simpl. apply split_orb_true. left. repeat rewrite eqb_asmt_refl. reflexivity.
        * apply Hz.
      + apply IH in Hz. destruct Hz as [U [U' [U'' HU]]]. exists U. exists U'. exists U''. split.
        * simpl. apply split_orb_true. right. apply HU.
        * apply HU. }
  { intros [Ui [Ui' [Ui'' [Hsub Hz]]]].
    generalize dependent Ub. generalize dependent Ua. induction L as [| U1 L' IH].
    - intros Ua Ub Hsub. simpl in Hsub. rewrite andb_assoc in Hsub. rewrite andb_comm in Hsub. simpl in Hsub. rewrite andb_comm in Hsub. discriminate Hsub.
    - intros Ua Ub Hsub. simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [Hsub | Hsub].
      + apply split_and_true in Hsub. destruct Hsub as [HUi HUi']. apply eqb_asmt_eq in HUi. rewrite HUi in *.
        apply split_and_true in HUi'. destruct HUi' as [HUi' HUi'']. apply eqb_asmt_eq in HUi'. rewrite HUi' in *.
        rewrite andb_comm in HUi''. simpl in HUi''. apply eqb_asmt_eq in HUi''. rewrite HUi'' in *.
        simpl. apply membership_append. apply Hz.
      + simpl. apply membership_append_r. apply IH. apply Hsub. }
Qed.



(* This lemma allows us to relate two consecutive conditioned nodes. If z is disturbed from Ui' to Ui'', and Ui' is not
   the first element of the sequence ([Ui, Ui', Ui''] is a sublist), then there exists another conditioned node, z',
   such that z and z' share an unblocked ancestor a, and z' was disturbed from Ui to Ui' *)
Lemma path_between_two_conditioned_nodes {X: Type} `{EqType X}: forall (G: graph) (z: node) (Z: nodes) (Ua Ub Ui Ui' Ui'' AZ: assignments X) (L: list (assignments X)),
  G_well_formed G = true /\ contains_cycle G = false
  -> is_assigned AZ z = true
  -> assignments_change_only_for_Z_anc_seq (Ua :: Ub :: L) Z AZ G
  -> sublist_X [Ui; Ui'; Ui''] (Ua :: Ub :: L) = true
  -> In z (find_unblocked_ancestors_in_Z_contributors G Z AZ (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ui' Ui''))
  -> exists (z' a: node),
       In a (find_unblocked_ancestors G z Z) /\ In a (find_unblocked_ancestors G z' Z)
       /\ In z' (find_unblocked_ancestors_in_Z_contributors G Z AZ (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ui Ui')).
Proof.
  intros G z Z Ua Ub Ui Ui' Ui'' AZ L. intros HG HAZ Hseq Hsub Hz.
  generalize dependent Ub. generalize dependent Ua. induction L as [| U1 L' IH].
  - intros Ua Ub Hseq Hsub. rewrite sublist_X_false in Hsub. discriminate Hsub.
  - intros Ua Ub Hseq Hsub. specialize IH with (Ua := Ub) (Ub := U1). simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [Hsub | Hsub].
    + assert (HUi: Ui = Ua). { apply split_and_true in Hsub. destruct Hsub as [Hsub _]. apply eqb_asmt_eq in Hsub. apply Hsub. } rewrite HUi in *.
      assert (HUi': Ui' = Ub). { apply split_and_true in Hsub. destruct Hsub as [_ Hsub]. apply split_and_true in Hsub. destruct Hsub as [Hsub _]. apply eqb_asmt_eq in Hsub. apply Hsub. } rewrite HUi' in *.
      assert (HUi'': Ui'' = U1). { rewrite andb_assoc in Hsub. rewrite andb_comm in Hsub. apply split_and_true in Hsub. destruct Hsub as [Hsub _]. rewrite andb_comm in Hsub. simpl in Hsub. apply eqb_asmt_eq in Hsub. apply Hsub. } rewrite HUi'' in *.

      destruct Hseq as [Hseq _]. apply ancestors_overlap_with_seq_then_contributor in Hz. 2: { apply HAZ. }

      apply overlap_has_member_in_common in Hz. destruct Hz as [a [Ha Haz]].
      assert (Hz: exists (z': node), In a (find_unblocked_ancestors G z' Z)
                  /\ overlap (find_unblocked_ancestors G z' Z) (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub) = true
                  /\ is_assigned AZ z' = true).
      { apply ancestor_in_Z_corresponds_to_conditioned_node_rev.
        destruct (member a (find_unblocked_ancestors_in_Z G Z AZ
                     (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub))) as [|] eqn:HmemZ.
        + apply member_In_equiv in HmemZ. apply HmemZ.
        + assert (F: get_assigned_value Ub a = get_assigned_value U1 a).
          { unfold assignments_change_only_for_subset in Hseq. apply Hseq. intros F. apply member_In_equiv_F in HmemZ. apply HmemZ. apply F. }
          apply in_unblocked_that_changed in Haz. exfalso. apply Haz. apply F. }

      destruct Hz as [z' Hz']. exists z'. exists a. split. apply Ha. split. apply Hz'. apply ancestors_overlap_with_seq_then_contributor.
      apply Hz'. apply Hz'.
    + apply IH.
      * apply Hseq.
      * apply Hsub.
Qed.
