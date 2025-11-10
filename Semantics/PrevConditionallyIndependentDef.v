From Semantics Require Import FunctionRepresentation.
From Semantics Require Import FindValue.
From Semantics Require Import ChangeOrigUnbAnc.
From CausalDiagrams Require Import Assignments.
From CausalDiagrams Require Import UnblockedAncestors.
From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import DSeparation.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.

From Utils Require Import EqType.

(* find all unblocked ancestors of nodes in Z that are not properly conditioned in A' *)
Fixpoint find_unblocked_ancestors_in_Z {X: Type} `{EqType X} (G: graph) (Z: nodes) (AZ A': assignments X): nodes :=
  match AZ with
  | [] => []
  | (u, x) :: AZ' => match (get_assigned_value A' u) with
                     | Some y => if (eqb x y) then find_unblocked_ancestors_in_Z G Z AZ' A'
                                             else (find_unblocked_ancestors G u Z) ++ (find_unblocked_ancestors_in_Z G Z AZ' A')
                     | None => find_unblocked_ancestors_in_Z G Z AZ' A'
                     end
  end.

(* find all unblocked ancestors of nodes in Z that are not properly conditioned in A' *)
Fixpoint find_unblocked_ancestors_in_Z' {X: Type} `{EqType X} (G: graph) (Z: nodes) (AZ A': assignments X) (S: nodes): nodes :=
  match AZ with
  | [] => []
  | (u, x) :: AZ' => match (get_assigned_value A' u) with
                     | Some y => if (eqb x y) then find_unblocked_ancestors_in_Z' G Z AZ' A' S
                                              else if (overlap (find_unblocked_ancestors G u Z) S)
                                                   then (find_unblocked_ancestors G u Z) ++ (find_unblocked_ancestors_in_Z' G Z AZ' A' S)
                                                   else find_unblocked_ancestors_in_Z' G Z AZ' A' S
                     | None => find_unblocked_ancestors_in_Z' G Z AZ' A' S
                     end
  end.


Theorem unblocked_ancestor_of_node_in_Z' {X: Type} `{EqType X}: forall (G: graph) (Z S: nodes) (AZ Ab Ub: assignments X) (anc: node) (g: graphfun),
  In anc (find_unblocked_ancestors_in_Z' G Z AZ Ab S) /\ get_values G g Ub [] = Some Ab /\ each_node_assigned_once AZ
  -> exists (z: node), In anc (find_unblocked_ancestors G z Z) /\ overlap (find_unblocked_ancestors G z Z) S = true
     /\ is_assigned AZ z = true /\ find_value G g z Ub [] <> get_assigned_value AZ z.
Proof.
  intros G Z SS AZ Ab Ub anc g. intros [Hanc [HAb HAZ]].
  induction AZ as [| [z1 x1] t IH].
  - simpl in Hanc. exfalso. apply Hanc.
  - simpl in Hanc.
    assert (forall (z: node), (z1 =? z) = true -> is_assigned t z = false).
    { intros z Hz1z.
      unfold each_node_assigned_once in HAZ. specialize HAZ with (u := z1). simpl in HAZ. rewrite eqb_refl in HAZ. simpl in HAZ.
      assert (S (length (filter (fun x : node * X => fst x =? z1) t)) = 1). { apply HAZ. reflexivity. }
      inversion H0. (* contradiction, H2 -> z1 is not assigned in t, contradicts Ht. might not need HZ. *)
      assert ((filter (fun x : node * X => fst x =? z1) t) = []). { apply length_0_list_empty. apply H2. }
      destruct (is_assigned t z) as [|] eqn:Ha.
      - assert (exists (x: X), In (z, x) t). { apply is_assigned_membership. apply Ha. }
        destruct H3 as [x Hx].
        assert (In (z, x) (filter (fun x : node * X => fst x =? z1) t)).
        { apply filter_In. split. 
          - apply Hx.
          - simpl. rewrite eqb_sym. apply Hz1z. }
        rewrite H1 in H3. exfalso. apply H3.
      - reflexivity. }

    destruct (get_assigned_value Ab z1) as [y|] eqn:HAbz1.
    + destruct (eqb x1 y) as [|] eqn:Hx1y.
      * apply IH in Hanc. destruct Hanc as [z [Hancz [Hover [Ht Hz]]]]. exists z. repeat split.
        -- apply Hancz.
        -- apply Hover.
        -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
        -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
           ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
           ++ apply Hz.
        -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
           destruct (z1 =? u) as [|] eqn:Huz1.
           ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
           ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity.
      * destruct (member z1 SS || overlap (find_unblocked_ancestors_given_paths (find_directed_paths_to_end z1 G) Z) SS) as [|] eqn:Hover.
        -- apply split_orb_true in Hover. destruct Hover as [Hover | Hover].
      { rewrite Hover in Hanc. apply membership_append_or with (l1 := z1 :: find_unblocked_ancestors_given_paths (find_directed_paths_to_end z1 G) Z) in Hanc.
        destruct Hanc as [Hanc | Hanc].
        { exists z1. repeat split.
        -- apply Hanc.
        -- apply overlap_has_member_in_common. exists z1. split.
           ++ unfold find_unblocked_ancestors. left. reflexivity.
           ++ apply member_In_equiv. apply Hover.
        -- simpl. rewrite eqb_refl. reflexivity.
        -- simpl. rewrite eqb_refl. unfold find_value. rewrite HAb. rewrite HAbz1. intros Hx1y'. inversion Hx1y'. rewrite H2 in Hx1y. rewrite eqb_refl' in Hx1y. discriminate Hx1y. }
        { apply IH in Hanc. destruct Hanc as [z [Hancz [Hover' [Ht Hz]]]]. exists z. repeat split.
        -- apply Hancz.
        -- apply Hover'.
        -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
        -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
           ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
           ++ apply Hz.
        -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
           destruct (z1 =? u) as [|] eqn:Huz1.
           ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
           ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity. } }
      { rewrite Hover in Hanc. destruct (member z1 SS) as [|] eqn:Hmem.
        { apply membership_append_or with (l1 := z1 :: find_unblocked_ancestors_given_paths (find_directed_paths_to_end z1 G) Z) in Hanc.
          destruct Hanc as [Hanc | Hanc].
          { exists z1. repeat split.
          -- apply Hanc.
          -- apply overlap_has_member_in_common. exists z1. split.
             ++ unfold find_unblocked_ancestors. left. reflexivity.
             ++ apply member_In_equiv. apply Hmem.
          -- simpl. rewrite eqb_refl. reflexivity.
          -- simpl. rewrite eqb_refl. unfold find_value. rewrite HAb. rewrite HAbz1. intros Hx1y'. inversion Hx1y'. rewrite H2 in Hx1y. rewrite eqb_refl' in Hx1y. discriminate Hx1y. }
          { apply IH in Hanc. destruct Hanc as [z [Hancz [Hover' [Ht Hz]]]]. exists z. repeat split.
          -- apply Hancz.
          -- apply Hover'.
          -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
          -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
             ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
             ++ apply Hz.
          -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
             destruct (z1 =? u) as [|] eqn:Huz1.
             ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
             ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity. } }
        { apply membership_append_or with (l1 := z1 :: find_unblocked_ancestors_given_paths (find_directed_paths_to_end z1 G) Z) in Hanc.
          destruct Hanc as [Hanc | Hanc].
          { exists z1. repeat split.
          -- apply Hanc.
          -- apply overlap_has_member_in_common in Hover. destruct Hover as [x [Hx1 Hx2]]. apply overlap_has_member_in_common. exists x. split.
             ++ unfold find_unblocked_ancestors. right. apply Hx1.
             ++ apply Hx2.
          -- simpl. rewrite eqb_refl. reflexivity.
          -- simpl. rewrite eqb_refl. unfold find_value. rewrite HAb. rewrite HAbz1. intros Hx1y'. inversion Hx1y'. rewrite H2 in Hx1y. rewrite eqb_refl' in Hx1y. discriminate Hx1y. }
          { apply IH in Hanc. destruct Hanc as [z [Hancz [Hover' [Ht Hz]]]]. exists z. repeat split.
          -- apply Hancz.
          -- apply Hover'.
          -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
          -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
             ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
             ++ apply Hz.
          -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
             destruct (z1 =? u) as [|] eqn:Huz1.
             ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
             ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity. } } }
        -- apply split_orb_false in Hover. destruct Hover as [Hover1 Hover2]. rewrite Hover1 in Hanc. rewrite Hover2 in Hanc.
           apply IH in Hanc. destruct Hanc as [z [Hancz [Hover [Ht Hz]]]]. exists z. repeat split.
           ++ apply Hancz.
           ++ apply Hover.
           ++ simpl. rewrite Ht. rewrite orb_comm. reflexivity.
           ++ simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
              ** specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
              ** apply Hz.
           ++ unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
              destruct (z1 =? u) as [|] eqn:Huz1.
              ** specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
              ** apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity.
     + apply IH in Hanc. destruct Hanc as [z [Hancz [Hover [Ht Hz]]]]. exists z. repeat split.
        -- apply Hancz.
        -- apply Hover.
        -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
        -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
           ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
           ++ apply Hz.
        -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
           destruct (z1 =? u) as [|] eqn:Huz1.
           ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
           ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity.
Qed.

Theorem unblocked_ancestor_of_node_in_Z {X: Type} `{EqType X}: forall (G: graph) (Z: nodes) (AZ Ab Ub: assignments X) (anc: node) (g: graphfun),
  In anc (find_unblocked_ancestors_in_Z G Z AZ Ab) /\ get_values G g Ub [] = Some Ab /\ each_node_assigned_once AZ
  -> exists (z: node), In anc (find_unblocked_ancestors G z Z) /\ is_assigned AZ z = true
                       /\ find_value G g z Ub [] <> get_assigned_value AZ z.
Proof.
  intros G Z AZ Ab Ub anc g. intros [Hanc [HAb HAZ]].
  induction AZ as [| [z1 x1] t IH].
  - simpl in Hanc. exfalso. apply Hanc.
  - simpl in Hanc.
    assert (forall (z: node), (z1 =? z) = true -> is_assigned t z = false).
    { intros z Hz1z.
      unfold each_node_assigned_once in HAZ. specialize HAZ with (u := z1). simpl in HAZ. rewrite eqb_refl in HAZ. simpl in HAZ.
      assert (S (length (filter (fun x : node * X => fst x =? z1) t)) = 1). { apply HAZ. reflexivity. }
      inversion H0. (* contradiction, H2 -> z1 is not assigned in t, contradicts Ht. might not need HZ. *)
      assert ((filter (fun x : node * X => fst x =? z1) t) = []). { apply length_0_list_empty. apply H2. }
      destruct (is_assigned t z) as [|] eqn:Ha.
      - assert (exists (x: X), In (z, x) t). { apply is_assigned_membership. apply Ha. }
        destruct H3 as [x Hx].
        assert (In (z, x) (filter (fun x : node * X => fst x =? z1) t)).
        { apply filter_In. split. 
          - apply Hx.
          - simpl. rewrite eqb_sym. apply Hz1z. }
        rewrite H1 in H3. exfalso. apply H3.
      - reflexivity. }

    destruct (get_assigned_value Ab z1) as [y|] eqn:HAbz1.
    + destruct (eqb x1 y) as [|] eqn:Hx1y.
      * apply IH in Hanc. destruct Hanc as [z [Hancz [Ht Hz]]]. exists z. repeat split.
        -- apply Hancz.
        -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
        -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
           ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
           ++ apply Hz.
        -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
           destruct (z1 =? u) as [|] eqn:Huz1.
           ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
           ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity.
      * apply membership_append_or with (l1 := z1 :: find_unblocked_ancestors_given_paths (find_directed_paths_to_end z1 G) Z) in Hanc.
        destruct Hanc as [Hanc | Hanc].
        { exists z1. repeat split.
        -- apply Hanc.
        -- simpl. rewrite eqb_refl. reflexivity.
        -- simpl. rewrite eqb_refl. unfold find_value. rewrite HAb. rewrite HAbz1. intros Hx1y'. inversion Hx1y'. rewrite H2 in Hx1y. rewrite eqb_refl' in Hx1y. discriminate Hx1y. }
        { apply IH in Hanc. destruct Hanc as [z [Hancz [Ht Hz]]]. exists z. repeat split.
        -- apply Hancz.
        -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
        -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
           ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
           ++ apply Hz.
        -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
           destruct (z1 =? u) as [|] eqn:Huz1.
           ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
           ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity. }
    + apply IH in Hanc. destruct Hanc as [z [Hancz [Ht Hz]]]. exists z. repeat split.
        -- apply Hancz.
        -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
        -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
           ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
           ++ apply Hz.
        -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
           destruct (z1 =? u) as [|] eqn:Huz1.
           ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
           ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity.
Qed.

(* assumes A corresponds to get_values with U *)
Definition unobs_valid_given_u {X: Type} (G: graph) (U A: assignments X) (u: node) (a: X): Prop :=
  is_assignment_for U (nodes_in_graph G) = true /\ get_assigned_value A u = Some a.

Definition unobs_conditions_on_Z {X: Type} (G: graph) (g: graphfun) (U AZ: assignments X) (Z: nodes): Prop :=
  forall (w: node), In w Z /\ node_in_graph w G = true -> find_value G g w U [] = get_assigned_value AZ w.

Definition conditionally_independent (X: Type) `{EqType X} (G: graph) (u v: node) (Z: nodes): Prop :=
  forall (AZ: assignments X), is_exact_assignment_for AZ Z /\ each_node_assigned_once AZ
  (* properly conditioned, consistent assignments where f(u)=a *)
  -> forall (g: graphfun) (a: X) (Ua Aa: assignments X),
      get_values G g Ua [] = Some Aa /\ unobs_valid_given_u G Ua Aa u a /\ unobs_conditions_on_Z G g Ua AZ Z
  (* assignments after setting f(u)=b and propagating *)
  -> forall (b: X) (Ub Ab: assignments X),
      (assignments_change_only_for_subset Ua Ub (find_unblocked_ancestors G u Z))
      /\ get_values G g Ub [] = Some Ab /\ (unobs_valid_given_u G Ub Ab u b)
  (* assignments after resetting changed conditioned variables and propagating *)
  -> forall (Ub' Ab': assignments X),
      (assignments_change_only_for_subset Ub Ub' (find_unblocked_ancestors_in_Z G Z AZ Ab))
      /\ get_values G g Ub' [] = Some Ab' /\ (unobs_valid_given_u G Ub' Ab' u b) /\ (unobs_conditions_on_Z G g Ub' AZ Z)
  (* value of v must stay constant *)
  -> get_assigned_value Aa v = get_assigned_value Ab' v.


Fixpoint unblocked_ancestors_that_changed_A_to_B {X: Type} `{EqType X} (V: nodes) (Ua Ub: assignments X): nodes :=
  match V with
  | [] => []
  | h :: t => match (get_assigned_value Ua h) with
              | Some xa => match (get_assigned_value Ub h) with
                           | Some xb => if (eqb xa xb) then (unblocked_ancestors_that_changed_A_to_B t Ua Ub)
                                                       else h :: (unblocked_ancestors_that_changed_A_to_B t Ua Ub)
                           | None => (unblocked_ancestors_that_changed_A_to_B t Ua Ub)
                           end
              | None => (unblocked_ancestors_that_changed_A_to_B t Ua Ub)
              end
  end.


Lemma in_unblocked_that_changed {X: Type} `{EqType X}: forall (G: graph) (Ua Ub: assignments X) (x: node),
  In x (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub)
  -> get_assigned_value Ua x <> get_assigned_value Ub x.
Proof.
  intros G Ua Ub x Hmem.
  induction (nodes_in_graph G) as [| h t IH].
  - simpl in Hmem. exfalso. apply Hmem.
  - simpl in Hmem. destruct (get_assigned_value Ua h) as [xa|] eqn:Hxa.
    + destruct (get_assigned_value Ub h) as [xb|] eqn:Hxb.
      * destruct (eqb xa xb) as [|] eqn:Hxab.
        -- apply IH. apply Hmem.
        -- destruct Hmem as [Hmem | Hmem].
           ++ intros F. rewrite Hmem in *. rewrite Hxa in F. rewrite Hxb in F. inversion F. rewrite H1 in Hxab. rewrite eqb_refl' in Hxab. discriminate Hxab.
           ++ apply IH. apply Hmem.
      * apply IH. apply Hmem.
    + apply IH. apply Hmem.
Qed.

Lemma in_unblocked_that_changed_cat {X: Type} `{EqType X}: forall (G: graph) (U: assignments X) (u: node) (r x: X),
  get_assigned_value U u = Some r
  -> is_assignment_for U (nodes_in_graph G) = true
  -> In u (nodes_in_graph G)
  -> r <> x
  -> In u (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) U ((u, x) :: U))
     /\ forall (w: node), w =? u = false -> ~ In w (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) U ((u, x) :: U)).
Proof.
  intros G U u r x Hr HUG HU Hrx.
  induction (nodes_in_graph G) as [| h t IH].
  - exfalso. apply HU.
  - simpl.
    assert (HhU: exists (hu: X), get_assigned_value U h = Some hu). { apply assigned_has_value with (L := h :: t). split. left. reflexivity. apply HUG. }
    destruct HhU as [hr Hh].
    destruct (u =? h) as [|] eqn:Huh.
    * apply eqb_eq in Huh. rewrite <- Huh in *. rewrite Hr. rewrite Hr in Hh. inversion Hh. destruct (eqb hr x) as [|] eqn:Hhr.
      -- exfalso. apply Hrx. rewrite H1. apply eqb_eq'. apply Hhr.
      -- split. left. reflexivity. intros w Hwu Hw. destruct Hw as [Hw | Hw]. rewrite Hw in Hwu. rewrite eqb_refl in Hwu. discriminate Hwu.
         destruct (member u t) as [|] eqn:Hut.
         ++ apply member_In_equiv in Hut. apply IH in Hut.
            ** destruct Hut as [_ Hut]. specialize Hut with (w := w). apply Hut. apply Hwu. apply Hw.
            ** simpl in HUG. apply split_and_true in HUG. apply HUG.
         ++ clear IH. clear HU. induction t as [| h' t' IH].
            ** simpl in Hw. apply Hw.
            ** simpl in Hw. 
               assert (HhU': exists (hu: X), get_assigned_value U h' = Some hu). { apply assigned_has_value with (L := u :: h' :: t'). split. right. left. reflexivity. apply HUG. }
               destruct HhU' as [hu Hhu].
               destruct (u =? h') as [|] eqn:Huh'. simpl in Hut. rewrite eqb_sym in Hut. rewrite Huh' in Hut. discriminate Hut.
               rewrite Hhu in Hw. rewrite eqb_refl' in Hw. apply IH in Hw. apply Hw.
               +++ simpl in HUG. apply split_and_true in HUG.
                   simpl. apply split_and_true. split. apply HUG. destruct HUG as [_ HUG]. apply split_and_true in HUG. apply HUG.
               +++ simpl in Hut. rewrite eqb_sym in Huh'. rewrite Huh' in Hut. apply Hut.
    * rewrite Hh. rewrite eqb_refl'. apply IH.
      simpl in HUG. apply split_and_true in HUG. apply HUG.
      destruct HU as [HU | HU]. rewrite HU in Huh. rewrite eqb_refl in Huh. discriminate Huh. apply HU.
Qed.

Definition conditionally_independent' (X: Type) `{EqType X} (G: graph) (u v: node) (Z: nodes): Prop :=
  forall (AZ: assignments X), is_exact_assignment_for AZ Z /\ each_node_assigned_once AZ
  (* properly conditioned, consistent assignments where f(u)=a *)
  -> forall (g: graphfun) (a: X) (Ua Aa: assignments X),
      get_values G g Ua [] = Some Aa /\ unobs_valid_given_u G Ua Aa u a /\ unobs_conditions_on_Z G g Ua AZ Z
  (* assignments after setting f(u)=b and propagating *)
  -> forall (b: X) (Ub Ab: assignments X),
      (assignments_change_only_for_subset Ua Ub (find_unblocked_ancestors G u Z))
      /\ get_values G g Ub [] = Some Ab /\ (unobs_valid_given_u G Ub Ab u b)
  (* assignments after resetting changed conditioned variables and propagating *)
  -> forall (Ub' Ab': assignments X),
      (assignments_change_only_for_subset Ub Ub' (find_unblocked_ancestors_in_Z' G Z AZ Ab (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub)))
      /\ get_values G g Ub' [] = Some Ab' /\ (unobs_valid_given_u G Ub' Ab' u b) /\ (unobs_conditions_on_Z G g Ub' AZ Z)
  (* value of v must stay constant *)
  -> get_assigned_value Aa v = get_assigned_value Ab' v.

(* S := nodes that changed from subset Ua to Ub
        { w: Ua(w) neq Ub(w), Aa(w) neq Ab(w) } *)


Fixpoint assignments_change_only_for_Z_anc_seq {X: Type} `{EqType X} (L: list (assignments X * assignments X)) (Z: nodes) (AZ: assignments X) (G: graph): Prop :=
  match L with
  | [] => True
  | (U1, A1) :: L' => match L' with
                      | [] => True
                      | (U2, A2) :: L'' => match L'' with
                                           | [] => True
                                           | (U3, A3) :: L''' =>
                                                       assignments_change_only_for_subset U2 U3
                                                          (find_unblocked_ancestors_in_Z' G Z AZ A2 (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) U1 U2))
                                                       /\ assignments_change_only_for_Z_anc_seq L' Z AZ G
                                           end
                      end
  end.

Definition conditionally_independent''' (X: Type) `{EqType X} (G: graph) (u v: node) (Z: nodes): Prop :=
  forall (AZ: assignments X), is_exact_assignment_for AZ Z /\ each_node_assigned_once AZ
  (* properly conditioned, consistent assignments where f(u)=a *)
  -> forall (g: graphfun) (a: X) (Ua Aa: assignments X),
      get_values G g Ua [] = Some Aa /\ unobs_valid_given_u G Ua Aa u a /\ unobs_conditions_on_Z G g Ua AZ Z
  (* assignments after setting f(u)=b and propagating *)
  -> forall (b: X) (Ub Ab: assignments X),
      (assignments_change_only_for_subset Ua Ub (find_unblocked_ancestors G u Z))
      /\ get_values G g Ub [] = Some Ab /\ (unobs_valid_given_u G Ub Ab u b)
  (* assignments after resetting changed conditioned variables and propagating *)
  -> forall (L: list (assignments X * assignments X)),
      length L <= num_nodes G
      /\ (forall (Uz Az: assignments X), In (Uz, Az) L -> get_values G g Uz [] = Some Az)
  -> forall (Ub' Ab': assignments X), last ((Ub, Ab) :: L) (Ub, Ab) = (Ub', Ab')
     -> (unobs_conditions_on_Z G g Ub' AZ Z) /\ (unobs_valid_given_u G Ub' Ab' u b)
  -> assignments_change_only_for_Z_anc_seq ((Ua, Aa) :: (Ub, Ab) :: L) Z AZ G
  (* value of v must stay constant *)
  -> get_assigned_value Aa v = get_assigned_value Ab' v.

Theorem conditional_independence_d_separation_backward_old_definition {X : Type} `{EqType X}: forall (G: graph) (u v: node),
  u <> v /\ generic_graph_and_type_properties_hold X G /\ node_in_graph v G = true
  -> forall (Z: nodes), subset Z (nodes_in_graph G) = true /\ each_node_appears_once Z /\ member u Z = false /\ member v Z = false
  -> d_separated_bool u v G Z = true -> conditionally_independent' X G u v Z.
Proof.
  intros G u' v'. intros [Huveq [HG Hnodev]] Z HZ.
  intros Hdsep. unfold conditionally_independent'.
  intros AZ HAZ g a Ua Aa [HAa [HUa HZUa]]. intros b Ub Ab [HUab [HAb HUb]]. intros Ub' Ab' [HUbb' [HAb' [HUb' HZUb']]].

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

    assert (Hanc_con: forall (u ancu' z v: node) (lu luz lv: nodes),
                is_directed_path_in_graph (ancu', z, luz) G = true
                -> is_directed_path_in_graph (ancu', u, lu) G = true /\ ~(In ancu' Z)
                -> In ancu' (find_confounders_in_path (concat u ancu' v (rev lu) (luz ++ z :: rev lv)) G) /\ ~ In ancu' Z).
    { intros u z x v lu luz1 lv1 Hdirluz1 [Hdirlu HluZ]. split.
      + apply confounders_vs_edges_in_path. destruct lu as [| hlu tlu].
        * destruct luz1 as [| hluz tluz].
          -- exists u. exists x. split.
             ++ simpl. repeat rewrite eqb_refl. reflexivity.
             ++ simpl in Hdirlu. rewrite andb_comm in Hdirlu. simpl in Hdirlu. split. apply Hdirlu.
                simpl in Hdirluz1. rewrite andb_comm in Hdirluz1. simpl in Hdirluz1. apply Hdirluz1.
          -- exists u. exists hluz. split.
             ++ apply sublist_breaks_down_list. exists []. exists (tluz ++ x :: rev lv1 ++ [v]). simpl. rewrite <- app_assoc. simpl. reflexivity.
             ++ simpl in Hdirlu. rewrite andb_comm in Hdirlu. simpl in Hdirlu. split. apply Hdirlu.
                simpl in Hdirluz1. apply split_and_true in Hdirluz1. destruct Hdirluz1 as [Hdirluz1 _]. apply Hdirluz1.
        * destruct luz1 as [| hluz tluz].
          -- exists hlu. exists x. split.
             ++ apply sublist_breaks_down_list. exists (u :: rev tlu). exists (rev lv1 ++ [v]). simpl. repeat rewrite <- app_assoc; simpl. reflexivity.
             ++ simpl in Hdirlu. apply split_and_true in Hdirlu. destruct Hdirlu as [Hdirlu _]. split. apply Hdirlu.
                simpl in Hdirluz1. rewrite andb_comm in Hdirluz1. simpl in Hdirluz1. apply Hdirluz1.
          -- exists hlu. exists hluz. split.
             ++ apply sublist_breaks_down_list. exists (u :: rev tlu). exists (tluz ++ x :: rev lv1 ++ [v]). simpl. repeat rewrite <- app_assoc; simpl. rewrite <- app_assoc. simpl. reflexivity.
             ++ simpl in Hdirlu. apply split_and_true in Hdirlu. destruct Hdirlu as [Hdirlu _]. split. apply Hdirlu.
                simpl in Hdirluz1. apply split_and_true in Hdirluz1. destruct Hdirluz1 as [Hdirluz1 _]. apply Hdirluz1.
      + apply HluZ. }

    assert (Hconn_col: forall (u z v: node) (lu lv: nodes),
              In z Z /\ u <> v /\ overlap (find_unblocked_ancestors G u Z) (find_unblocked_ancestors G v Z) = false
              -> is_directed_path_in_graph (u, z, lu) G = true /\ acyclic_path_2 (u, z, lu) /\ (forall w : node, w = u \/ In w lu -> ~ In w Z)
              -> is_directed_path_in_graph (v, z, lv) G = true /\ acyclic_path_2 (v, z, lv) /\ (forall w : node, w = v \/ In w lv -> ~ In w Z)
              -> (is_path_in_graph (concat u z v lu (rev lv)) G = true /\ acyclic_path_2 (concat u z v lu (rev lv)) /\ d_connected_2 (concat u z v lu (rev lv)) G Z)
                 \/ (exists (lu1 lu2 lv' lv1 lv2: nodes) (x: node), is_directed_path_in_graph (v, z, lv') G = true /\ acyclic_path_2 (v, z, lv') /\ (forall w : node, (w = v \/ In w lv') -> ~ In w Z)
                      /\ lu = lu1 ++ [x] ++ lu2 /\ lv = lv1 ++ [x] ++ lv2 /\ lv' = lv1 ++ [x] ++ lu2 /\ overlap lu1 lv1 = false
                      /\ d_connected_2 (u, v, lu1 ++ [x] ++ (rev lv1)) G Z /\ is_path_in_graph (u, v, lu1 ++ [x] ++ (rev lv1)) G = true /\ acyclic_path_2 (u, v, lu1 ++ [x] ++ (rev lv1)))).
    { intros u z v lu lv. intros [HzZ [Huv Hover]] [Hdiru [Hcycu HluZ]] [Hdirv [Hcycv HlvZ]].
      assert (Hacyc: overlap lu lv = false \/
                     exists (l2': nodes), is_directed_path_in_graph (v, z, l2') G = true /\ acyclic_path_2 (v, z, l2')
                      /\ (forall w : node, (w = v \/ In w l2') -> ~ In w Z)
                      /\ exists (l1'' l2'': nodes) (l3 l3': nodes) (x: node), lu = l1'' ++ [x] ++ l3 /\ l2' = l2'' ++ [x] ++ l3 /\ lv = l2'' ++ [x] ++ l3' /\ overlap l1'' l2'' = false).
      { apply acyclic_paths_intersect_if_common_endpoint with (anc1 := u).
        - destruct HG as [_ [_ HG]]. apply HG.
        - split. apply Hdiru. split. apply Hcycu. apply HluZ.
        - split. apply Hdirv. split. apply Hcycv. apply HlvZ. }
      destruct Hacyc as [Hacyc | Hacyc].
      *** (* lu and lv have no overlap, so the path is acyclic *) left.
          assert (Hpath: is_path_in_graph (concat u z v lu (rev lv)) G = true).
          { apply concat_paths_still_a_path. split.
            + apply directed_path_is_path in Hdiru. apply Hdiru.
            + apply reverse_path_in_graph. apply directed_path_is_path in Hdirv. apply Hdirv. }
          assert (Hcat: acyclic_path_2 (concat u z v lu (rev lv))).
          { apply concat_paths_acyclic.
            - split. apply Huv. split. apply Hcycu. apply reverse_path_still_acyclic. apply Hcycv.
            - split.
              + intros F. apply membership_rev in F. rewrite <- reverse_list_twice in F.
                apply no_overlap_non_member with (x := v) in Hover.
                * apply Hover. apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := lv). split.
                  -- apply Hdirv.
                  -- split. apply Hcycv. apply HlvZ.
                  -- apply F.
                * unfold find_unblocked_ancestors. left. reflexivity.
              + intros F. apply no_overlap_non_member_rev with (x := u) in Hover.
                * apply Hover. apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := lu). split.
                  -- apply Hdiru.
                  -- split. apply Hcycu. apply HluZ.
                  -- apply F.
                * unfold find_unblocked_ancestors. left. reflexivity.
            - apply overlap_rev. apply Hacyc. }
          split. apply Hpath. split. apply Hcat.
          apply concat_d_connected_paths.
          - destruct HG as [_ [_ HG]]. apply HG.
          - apply Hpath.
          - split.
            + apply Hdconn1. split.
              * apply Hdiru.
              * apply HluZ.
              * apply Hcycu.
            + split.
              * apply reverse_d_connected_paths. apply Hdconn1. split. apply Hdirv. apply HlvZ. apply Hcycv.
              * apply Hcat.
          - right. right. split.
            + apply colliders_vs_edges_in_path.
              apply directed_path_has_directed_edge_end in Hdiru as Hdiru'. destruct Hdiru' as [Hdiru' | Hdiru'].
              * apply directed_path_has_directed_edge_end in Hdirv as Hdirv'. destruct Hdirv' as [Hdirv' | Hdirv'].
                exists u. exists v. split.
                -- rewrite Hdirv'. rewrite Hdiru'. apply sublist_breaks_down_list. exists []. exists []. simpl. reflexivity.
                -- split. rewrite Hdiru' in Hdiru. simpl in Hdiru. rewrite andb_comm in Hdiru. simpl in Hdiru. apply Hdiru.
                   rewrite Hdirv' in Hdirv. simpl in Hdirv. rewrite andb_comm in Hdirv. simpl in Hdirv. apply Hdirv.
                -- destruct Hdirv' as [l' [x Hdirv']]. exists u. exists x. split.
                   ++ apply sublist_breaks_down_list. exists []. exists (rev l' ++ [v]).
                      simpl. rewrite Hdiru'. destruct Hdirv' as [Hdirv' Hxz]. rewrite Hdirv'. rewrite reverse_list_append.
                      simpl. reflexivity.
                   ++ split. rewrite Hdiru' in Hdiru. simpl in Hdiru. rewrite andb_comm in Hdiru. simpl in Hdiru. apply Hdiru.
                      destruct Hdirv' as [_ Hdirv']. apply Hdirv'.
              * destruct Hdiru' as [lu' [x1 [Hlu' Hx1z]]].
                apply directed_path_has_directed_edge_end in Hdirv as Hdirv'. destruct Hdirv' as [Hdirv' | Hdirv'].
                { exists x1. exists v. split.
                  -- rewrite Hdirv'. apply sublist_breaks_down_list. rewrite Hlu'. exists (u :: lu'). exists []. simpl. unfold node.
                     f_equal. repeat rewrite <- app_assoc; simpl. reflexivity.
                  -- split. apply Hx1z. rewrite Hdirv' in Hdirv. simpl in Hdirv. rewrite andb_comm in Hdirv. simpl in Hdirv. apply Hdirv. }
                { destruct Hdirv' as [lv' [x2 [Hlv' Hx2z]]]. exists x1. exists x2. split.
                  -- apply sublist_breaks_down_list. exists (u :: lu'). exists (rev lv' ++ [v]).
                     simpl. rewrite Hlv'. rewrite reverse_list_append.
                     simpl. rewrite Hlu'. simpl. unfold node. f_equal. repeat rewrite <- app_assoc; simpl. reflexivity.
                  -- split. apply Hx1z. apply Hx2z. }
            + unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists z.
              split.
              * unfold find_descendants. left. reflexivity.
              * apply HzZ.
      *** right. (* need to address case of the two paths meeting prior to z, in which case z is the descendant of a collider *)
          clear Hdirv. clear Hcycv. clear HlvZ.
          destruct Hacyc as [lv' [Hdirv [Hcycv [HlvZ [lu'' [lv'' [l [l' [x [Hlu' [Hlv' [Hlv'' Hacyc]]]]]]]]]]]]. remember lu as lu'.
          assert (Hpath: is_path_in_graph (concat u x v lu'' (rev lv'')) G = true).
          { apply concat_paths_still_a_path. split.
            + apply directed_path_is_path. apply subpath_still_directed_2 with (v := z) (l2 := l) (l3 := lu'). split. rewrite Hlu'. reflexivity. apply Hdiru.
            + apply reverse_path_in_graph. apply directed_path_is_path. apply subpath_still_directed_2 with (v := z) (l2 := l) (l3 := lv'). split.
              symmetry. apply Hlv'. apply Hdirv. }
          assert (Hcat: acyclic_path_2 (concat u x v lu'' (rev lv''))).
          { apply concat_paths_acyclic.
            - split. apply Huv. split. apply subpath_still_acyclic_2 with (v := z) (l2 := l) (l3 := lu'). split. symmetry. apply Hlu'. apply Hcycu.
              apply reverse_path_still_acyclic. apply subpath_still_acyclic_2 with (v := z) (l2 := l) (l3 := lv'). split. symmetry. apply Hlv'. apply Hcycv.
            - split.
              + intros F. apply membership_rev in F. rewrite <- reverse_list_twice in F.
                apply no_overlap_non_member with (x := v) in Hover.
                * apply Hover. apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := lv'). split.
                  -- apply Hdirv.
                  -- split. apply Hcycv. apply HlvZ.
                  -- apply membership_splits_list in F. destruct F as [lu1 [lu2 F]]. apply membership_splits_list. exists lu1. exists (lu2 ++ [x] ++ l).
                     rewrite Hlv'. rewrite <- F. rewrite <- app_assoc. reflexivity.
                * unfold find_unblocked_ancestors. left. reflexivity.
              + intros F. apply no_overlap_non_member_rev with (x := u) in Hover.
                * apply Hover. apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := lu'). split.
                  -- apply Hdiru.
                  -- split. apply Hcycu. apply HluZ.
                  -- apply membership_splits_list in F. destruct F as [lv1 [lv2 F]]. apply membership_splits_list. exists lv1. exists (lv2 ++ [x] ++ l).
                     rewrite Hlu'. rewrite <- F. rewrite <- app_assoc. reflexivity.
                * unfold find_unblocked_ancestors. left. reflexivity.
            - apply overlap_rev. apply Hacyc. }
          assert (Hdiru': is_directed_path_in_graph (u, x, lu'') G = true). { apply subpath_still_directed_2 with (v := z) (l2 := l) (l3 := lu'). split. rewrite Hlu'. reflexivity. apply Hdiru. }
          assert (Hdirv': is_directed_path_in_graph (v, x, lv'') G = true). { apply subpath_still_directed_2 with (v := z) (l2 := l) (l3 := lv'). split. rewrite Hlv'. reflexivity. apply Hdirv. }
          exists lu''. exists l. exists lv'. exists lv''. exists l'. exists x. split. apply Hdirv. split. apply Hcycv. split. apply HlvZ.
          split. apply Hlu'. split. apply Hlv''. split. apply Hlv'. split. apply Hacyc. split.
          apply concat_d_connected_paths.
          - destruct HG as [_ [_ HG]]. apply HG.
          - apply Hpath.
          - split.
            + apply Hdconn1. split.
              * apply Hdiru'.
              * intros w Hw. apply HluZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. apply membership_append with (l2 := [x] ++ l) in Hw. rewrite Hlu'. apply Hw.
              * unfold concat in Hcat. apply subpath_still_acyclic_2 with (v := v) (l2 := rev lv'') (l3 := lu'' ++ [x] ++ rev lv''). split. reflexivity. apply Hcat.
            + split.
              * apply reverse_d_connected_paths. apply Hdconn1. split.
                -- apply Hdirv'.
                -- intros w Hw. apply HlvZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. apply membership_append with (l2 := [x] ++ l) in Hw. rewrite Hlv'. apply Hw.
                -- rewrite reverse_list_twice with (l := lv''). apply reverse_path_still_acyclic. apply subpath_still_acyclic with (w := u) (l1 := lu'') (l3 := lu'' ++ [x] ++ rev lv''). split. reflexivity. apply Hcat.
              * apply Hcat.
          - right. right. split.
            + apply colliders_vs_edges_in_path.
              apply directed_path_has_directed_edge_end in Hdiru' as Hdiru''. destruct Hdiru'' as [Hdiru'' | Hdiru''].
              * apply directed_path_has_directed_edge_end in Hdirv' as Hdirv''. destruct Hdirv'' as [Hdirv'' | Hdirv''].
                exists u. exists v. rewrite Hdirv'' in *. rewrite Hdiru'' in *. split.
                -- apply sublist_breaks_down_list. exists []. exists []. simpl. reflexivity.
                -- split. simpl in Hdiru'. rewrite andb_comm in Hdiru'. simpl in Hdiru'. apply Hdiru'.
                   simpl in Hdirv'. rewrite andb_comm in Hdirv'. simpl in Hdirv'. apply Hdirv'.
                -- destruct Hdirv'' as [l'' [x' Hdirv'']]. exists u. exists x'. split.
                   ++ apply sublist_breaks_down_list. exists []. exists (rev l'' ++ [v]).
                      simpl. rewrite Hdiru''. destruct Hdirv'' as [Hdirv'' Hxz]. rewrite Hdirv''. rewrite reverse_list_append.
                      simpl. reflexivity.
                   ++ split. rewrite Hdiru'' in Hdiru'. simpl in Hdiru'. rewrite andb_comm in Hdiru'. simpl in Hdiru'. apply Hdiru'.
                      destruct Hdirv'' as [_ Hdirv'']. apply Hdirv''.
              * destruct Hdiru'' as [l'' [x'' [Hl' Hxx']]].
                apply directed_path_has_directed_edge_end in Hdirv' as Hdirv''. destruct Hdirv'' as [Hdirv'' | Hdirv''].
                { exists x''. exists v. rewrite Hdirv'' in *. split.
                  -- apply sublist_breaks_down_list. rewrite Hl'. exists (u :: l''). exists []. simpl. unfold node.
                     f_equal. repeat rewrite <- app_assoc; simpl. reflexivity.
                  -- split. apply Hxx'. simpl in Hdirv'. rewrite andb_comm in Hdirv'. simpl in Hdirv'. apply Hdirv'. }
                { destruct Hdirv'' as [l''' [x''' [Hl'' Hxx'']]]. exists x''. exists x'''. split.
                  -- apply sublist_breaks_down_list. exists (u :: l''). exists (rev l''' ++ [v]).
                     simpl. rewrite Hl''. rewrite reverse_list_append.
                     simpl. rewrite Hl'. simpl. unfold node. f_equal. repeat rewrite <- app_assoc; simpl. reflexivity.
                  -- split. apply Hxx'. apply Hxx''. }
            + unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists z.
              split.
              * apply find_descendants_correct. right. exists (x, z, l). split.
                -- apply subpath_still_directed with (w := u) (l1 := lu'') (l3 := lu'). split. symmetry. apply Hlu'. apply Hdiru.
                -- apply path_start_end_refl.  
              * apply HzZ.
          - split. apply Hpath. apply Hcat. }

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
      - split. destruct HUb' as [HUb' _]. apply HUb'. apply Hnodev. }
    destruct HvUa as [va HvUa]. destruct HvUb as [vb HvUb]. destruct HvUb' as [vb' HvUb'].

    destruct (overlap (find_unblocked_ancestors G u' Z) (find_unblocked_ancestors G v' Z)) as [|] eqn:Hover.
    { (* contradiction: d-connected path u' <- ... <- anc -> ... -> v' *)
      apply overlap_has_member_in_common in Hover. destruct Hover as [anc [Hancu Hancv]].
      specialize Hdconn_con' with (anc := anc) (u := u') (v := v'). exfalso. apply Hdconn_con'. repeat split.
      + apply Huveq.
      + split. apply Hancv. apply Hancu.
      + apply Hdsep. }
    { destruct (eqb va vb') as [|] eqn:Hvavb'.
      - apply eqb_eq' in Hvavb'. rewrite Hvavb' in HvUa. unfold find_value in HvUa. unfold find_value in HvUb'. rewrite HAa in HvUa. rewrite HAb' in HvUb'.
        rewrite HvUa. rewrite HvUb'. reflexivity.
      - assert (Hfvavb': find_value G g v' Ua [] <> find_value G g v' Ub' []).
        { rewrite HvUa. rewrite HvUb'. intros F. inversion F. rewrite H1 in Hvavb'. rewrite eqb_refl' in Hvavb'. discriminate Hvavb'. }
        assert (Hancv: exists a : node,
            In a (find_unblocked_ancestors G v' Z) /\
            get_assigned_value Ua a <> get_assigned_value Ub' a /\
            find_value G g a Ua [] <> find_value G g a Ub' []).
        { apply nodefun_value_only_affected_by_unblocked_ancestors with (Z := Z) (AZ := AZ). 
          - apply HG.
          - apply Hfvavb'.
          - split. apply HUa. apply HUb'.
          - apply Hnodev.
          - split. apply HZUa. apply HZUb'. }
        destruct Hancv as [ancv [Hancv [HancvU Hancvf]]].
        assert (HancvUab: get_assigned_value Ua ancv = get_assigned_value Ub ancv).
        { unfold assignments_change_only_for_subset in HUab. specialize HUab with (x := ancv). destruct HUab as [_ HUab]. apply HUab.
          apply no_overlap_non_member with (x := ancv) in Hover.
          - apply Hover.
          - apply Hancv. }

        unfold assignments_change_only_for_subset in HUbb'. specialize HUbb' with (x := ancv).
        assert (Hz: exists (z: node), In ancv (find_unblocked_ancestors G z Z) /\ overlap (find_unblocked_ancestors G z Z)
                                                (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub) = true
                                                /\ is_assigned AZ z = true /\ find_value G g z Ub [] <> get_assigned_value AZ z).
        { apply unblocked_ancestor_of_node_in_Z' with (Ab := Ab). repeat split.
          - destruct (member ancv (find_unblocked_ancestors_in_Z' G Z AZ Ab
                        (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub))) as [|] eqn:HmemZ.
            + apply member_In_equiv in HmemZ. apply HmemZ.
            + assert (F: get_assigned_value Ub ancv = get_assigned_value Ub' ancv).
              { destruct HUbb' as [_ HUbb']. apply HUbb'. intros F. apply member_In_equiv in F. rewrite F in HmemZ. discriminate HmemZ. }
              exfalso. apply HancvU. rewrite HancvUab. apply F.
          - apply HAb.
          - destruct HAZ as [_ HAZ]. apply HAZ. }
        destruct Hz as [z [Hancvz [Hoverz [HAZz HUbz]]]].
        (* now show that z shares and unblocked ancestor with u due to HUab *)
        assert (HzZ: In z Z /\ node_in_graph z G = true).
        { split. destruct (member z Z) as [|] eqn:HzZ.
          - apply member_In_equiv in HzZ. apply HzZ.
          - unfold is_exact_assignment_for in HAZ. destruct HAZ as [[_ HAZ] _]. specialize HAZ with (u := z).
            apply HAZ in HzZ. rewrite HzZ in HAZz. discriminate HAZz.
          - apply unblocked_ancestors_have_unblocked_directed_path in Hancvz. destruct Hancvz as [Hz | Hz].
            + apply unblocked_ancestors_have_unblocked_directed_path in Hancv. destruct Hancv as [Hz' | Hz'].
              * rewrite <- Hz. rewrite Hz'. apply Hnodev.
              * destruct Hz' as [l Hz']. apply nodes_in_graph_in_V with (p := (ancv, v', l)). split.
                -- unfold node_in_path. simpl. rewrite Hz. rewrite eqb_refl. reflexivity.
                -- apply directed_path_is_path. apply Hz'.
            + destruct Hz as [l Hz]. apply nodes_in_graph_in_V with (p := (ancv, z, l)). split.
              * unfold node_in_path. simpl. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
              * apply directed_path_is_path. apply Hz. }

        assert (Hfzazb: find_value G g z Ua [] <> find_value G g z Ub []).
        { (* show that f(z, Ua) = AZ(z) using HZUa *)
          unfold unobs_conditions_on_Z in HZUa. specialize HZUa with (w := z). apply HZUa in HzZ. rewrite HzZ. intros F. rewrite F in HUbz. apply HUbz. reflexivity. }

        apply overlap_has_member_in_common in Hoverz. destruct Hoverz as [ancu [Hancuz Hancu]].
        assert (HancuU: get_assigned_value Ua ancu <> get_assigned_value Ub ancu).
        { apply in_unblocked_that_changed with (G := G). apply Hancu. }
        clear Hancu.

        unfold assignments_change_only_for_subset in HUab. specialize HUab with (x := ancu).
        assert (Hancu: In ancu (find_unblocked_ancestors G u' Z)).
        { destruct (member ancu (find_unblocked_ancestors G u' Z)) as [|] eqn:Hancu'.
          - apply member_In_equiv. apply Hancu'.
          - destruct HUab as [_ HUab]. assert (Hancu: ~ In ancu (find_unblocked_ancestors G u' Z)).
            { intros F. apply member_In_equiv in F. rewrite Hancu' in F. discriminate F. }
            clear Hancu'. apply HUab in Hancu. rewrite Hancu in HancuU. exfalso. apply HancuU. reflexivity. }

            (* u <- ... <- ancu -> ... -> z <- ... <- ancv -> ... -> v is a d-connected path *)
            pose proof Hdconn_con as Hconvz. specialize Hconvz with (anc := ancv) (u := z) (v := v').
            pose proof Hdsep as Hdsep'. clear Hdsep. pose proof Hover as Hover'. clear Hover. pose proof Huveq as Hequv'. clear Huveq.

            assert (Hconn_con_col': forall (u v ancu': node) (lv lu luz: nodes), z <> v /\ u <> z /\ u <> v
                      -> d_connected_2 (v, z, lv) G Z /\ is_directed_path_in_graph (v, z, lv) G = true /\ acyclic_path_2 (v, z, lv) /\ (forall w : node, w = v \/ In w lv -> ~ In w Z)
                      -> d_connected_2 (u, z, rev lu ++ ancu' :: luz) G Z /\ is_path_in_graph (u, z, rev lu ++ ancu' :: luz) G = true /\ acyclic_path_2 (u, z, rev lu ++ ancu' :: luz)
                         /\ is_directed_path_in_graph (ancu', u, lu) G = true /\ is_directed_path_in_graph (ancu', z, luz) G = true /\ (forall w : node, w = ancu' \/ In w lu \/ In w luz -> ~ In w Z)
                      -> overlap (find_unblocked_ancestors G u Z) (find_unblocked_ancestors G v Z) = false
                      -> exists (x: node) (luz1 lv1: nodes), (d_connected_2 (concat u x v (rev lu ++ ancu' :: luz1) (rev lv1)) G Z /\ is_path_in_graph (concat u x v (rev lu ++ ancu' :: luz1) (rev lv1)) G = true
                          /\ acyclic_path_2 (concat u x v (rev lu ++ ancu' :: luz1) (rev lv1)))
                          /\ ((luz1 = luz /\ lv1 = lv /\ z = x) \/ (exists (luz2 lv2: nodes), luz = luz1 ++ [x] ++ luz2 /\ lv = lv1 ++ [x] ++ lv2))).
            { intros u v ancu' lv lu luz. intros [Hzv [Huz Huveq]]. intros [Hconnvz [Hdirvz [Hcycvz HlvZ]]]. intros [Hconnuz [Hpathuz [Hcycuz [Hdirlu [Hdirluz HluZ]]]]].
              intros Hover.
              (* helper lemmas to use later on *)
              assert (Hvancu': ancu' <> v). (* else, v is an unblocked ancestor of u *)
              { intros F. apply no_overlap_non_member with (x := v) in Hover.
                - apply Hover. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lu.
                  rewrite F in *. split. apply Hdirlu. split. rewrite reverse_list_twice with (l := lu). apply reverse_path_still_acyclic.
                  apply subpath_still_acyclic_2 with (v := z) (l2 := luz) (l3 := rev lu ++ [v] ++ luz).
                  + split. reflexivity. apply Hcycuz.
                  + intros w Hw. apply HluZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. left. apply Hw.
                - unfold find_unblocked_ancestors. left. reflexivity. }
              specialize Hconn_col with (u := ancu') (z := z) (v := v) (lu := luz) (lv := lv).

              assert (Heqvancu': In z Z /\ ancu' <> v /\ overlap (find_unblocked_ancestors G ancu' Z) (find_unblocked_ancestors G v Z) = false).
              { split. apply HzZ. split. apply Hvancu'.
                (* else, the member in common is a common unblocked ancestor of u and v *)
                destruct (overlap (find_unblocked_ancestors G ancu' Z) (find_unblocked_ancestors G v Z)) as [|] eqn:F.
                - apply overlap_has_member_in_common in F. destruct F as [x [Hxancu' Hxv]].
                  apply no_overlap_non_member with (x := x) in Hover.
                  + exfalso. apply Hover. apply unblocked_ancestors_have_unblocked_directed_path in Hxancu'. destruct Hxancu' as [Hxancu' | [lx [Hdirx [Hcycx HlxZ]]]].
                    -- rewrite Hxancu'. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lu. split. apply Hdirlu. split.
                       rewrite reverse_list_twice with (l := lu). apply reverse_path_still_acyclic.
                       apply subpath_still_acyclic_2 with (v := z) (l2 := luz) (l3 := rev lu ++ [ancu'] ++ luz).
                       ++ split. reflexivity. apply Hcycuz.
                       ++ intros w Hw. apply HluZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. left. apply Hw.
                    -- apply unblocked_ancestors_have_unblocked_directed_path. right.
                       assert (Hdir: is_directed_path_in_graph (x, u, lx ++ [ancu'] ++ lu) G = true).
                       { apply concat_directed_paths. split. apply Hdirx. apply Hdirlu. }
                       apply directed_path_can_be_acyclic in Hdir. destruct Hdir as [lx' [Hdir' [Hcyc' Hlx']]].
                       exists lx'. split. apply Hdir'. split. apply Hcyc'.
                       intros w Hw. destruct Hw as [Hw | Hw].
                       ++ apply HlxZ. left. apply Hw.
                       ++ assert (Hmem: In w (lx ++ [ancu'] ++ lu)). { apply subset_larger_set_membership with (l1 := lx'). split. apply Hlx'. apply Hw. }
                          apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                          ** apply HlxZ. right. apply Hmem.
                          ** apply HluZ. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. left. symmetry. apply Hmem. right. left. apply Hmem.
                       ++ (* otherwise, x is shared unblocked ancestor of v and u *)
                          intros F. apply Hover. left. symmetry. apply F.
                  + apply Hxv.
                - reflexivity. }
              apply Hconn_col in Heqvancu'.
              -- (* helper lemmas *)
                 assert (Hcyclu: acyclic_path_2 (u, ancu', rev lu)).
                 { apply subpath_still_acyclic_2 with (v := z) (l2 := luz) (l3 := rev lu ++ [ancu'] ++ luz). split. reflexivity. apply Hcycuz. }
                 assert (Hvlu: ~(In v lu)).
                 { intros Hvlu. (* contradiction: then v is an unblocked ancestor of u *)
                   apply no_overlap_non_member with (x := v) in Hover.
                   ++ apply Hover. apply unblocked_ancestor_if_in_unblocked_directed_path with (anc := ancu') (l := lu).
                      ** split. apply Hdirlu. split. apply reverse_path_still_acyclic in Hcyclu. rewrite <- reverse_list_twice in Hcyclu. apply Hcyclu. intros w Hw. apply HluZ.
                         rewrite <- or_assoc. left. apply Hw.
                      ** apply Hvlu.
                   ++ unfold find_unblocked_ancestors. left. reflexivity. }
                 assert (Hulv: ~(In u lv)).
                 { (* contradiction: then v is an unblocked ancestor of u *)
                   intros Hu.
                   apply no_overlap_non_member with (x := v) in Hover.
                   ++ apply Hover. apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := lv).
                      ** easy.
                      ** apply Hu.
                   ++ unfold find_unblocked_ancestors. left. reflexivity. }
                 assert (Hlulv: overlap lu lv = false).
                 { destruct (overlap lu lv) as [|] eqn: F. apply overlap_has_member_in_common in F. destruct F as [x [Hxlu Hx]].
                   { (* contradiction: v is an unblocked ancestor of u, through x *)
                     apply no_overlap_non_member with (x := v) in Hover.
                     exfalso. apply Hover. apply membership_splits_list in Hx. destruct Hx as [lv1 [lv2 Hx]]. apply membership_splits_list in Hxlu. destruct Hxlu as [lu1 [lu2 Hxlu]]. apply unblocked_ancestors_have_unblocked_directed_path. right. exists (lv1 ++ [x] ++ lu2).
                      split. apply concat_directed_paths. split. apply subpath_still_directed_2 with (v := z) (l2 := lv2) (l3 := lv). split. apply Hx. apply Hdirvz.
                      apply subpath_still_directed with (w := ancu') (l1 := lu1) (l3 := lu). split. apply Hxlu. apply Hdirlu. split.
                      - apply concat_paths_acyclic. split. intros Hequv. apply Huveq. symmetry. apply Hequv. split.
                        apply subpath_still_acyclic_2 with (v := z) (l2 := lv2) (l3 := lv). split. apply Hx. apply Hcycvz.
                        apply subpath_still_acyclic with (w := ancu') (l1 := lu1) (l3 := lu). split. apply Hxlu. rewrite reverse_list_twice with (l := lu). apply reverse_path_still_acyclic. apply Hcyclu.
                        split.
                        + intros Hvlu2. apply Hvlu. apply membership_append_r with (l1 := lu1 ++ [x]) in Hvlu2. rewrite <- Hxlu. rewrite app_assoc. apply Hvlu2.
                        + intros Hulv1. apply Hulv. apply membership_append with (l2 := [x] ++ lv2) in Hulv1. rewrite <- Hx. apply Hulv1.
                        + (* if there were overlap, then there would be a cycle with x *) 
                          destruct (overlap lv1 lu2) as [|] eqn:F.
                          * apply overlap_has_member_in_common in F. destruct F as [x' [Hxlv1' Hxlu2']]. apply membership_splits_list in Hxlv1'. destruct Hxlv1' as [lv1' [lv1'' Hlv1]].
                            apply membership_splits_list in Hxlu2'. destruct Hxlu2' as [lu2' [lu2'' Hlu2]].
                            assert (Hcycle: is_directed_path_in_graph (concat x' x x' lv1'' lu2') G = true).
                            { apply concat_directed_paths. split. apply subpath_still_directed with (w := v) (l1 := lv1') (l3 := lv1). split. apply Hlv1.
                              apply subpath_still_directed_2 with (v := z) (l2 := lv2) (l3 := lv). split. apply Hx. apply Hdirvz.
                              apply subpath_still_directed_2 with (v := u) (l2 := lu2'') (l3 := lu2). split. apply Hlu2.
                              apply subpath_still_directed with (w := ancu') (l1 := lu1) (l3 := lu). split. apply Hxlu. apply Hdirlu. }
                            destruct HG as [_ [_ HG]]. apply contains_cycle_false_correct with (p := (concat x' x x' lv1'' lu2')) in HG. unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
                            apply Hcycle.
                          * reflexivity.
                      - intros w Hw. destruct Hw as [Hw | Hw]. apply HlvZ. left. apply Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                        + apply HlvZ. right. apply membership_append with (l2 := [x] ++ lv2) in Hw. rewrite <- Hx. apply Hw.
                        + apply HluZ. right. left. apply membership_append_r with (l1 := lu1) in Hw. rewrite <- Hxlu. apply Hw.
                      - unfold find_unblocked_ancestors. left. reflexivity. }
                    { reflexivity. } }
                assert (Hluluz: overlap lu luz = false).
                { destruct (overlap lu luz) as [|] eqn:F.
                  - (* contradicts Hcycuz, which passes through both lu and luz *)
                    apply overlap_has_member_in_common in F. destruct F as [x [Hxlu Hx]].
                    apply acyclic_path_correct in Hcycuz. simpl in Hcycuz. apply split_and_true in Hcycuz; destruct Hcycuz as [_ Hcycuz]. apply split_and_true in Hcycuz; destruct Hcycuz as [_ Hcycuz].
                    apply acyclic_path_intermediate_nodes with (p := rev lu ++ ancu' :: luz) (x := x) in Hcycuz. destruct Hcycuz as [Hc | Hc].
                    ** rewrite count_app in Hc. apply member_count_at_least_1 in Hxlu. apply member_count_at_least_1 in Hx. rewrite count_reverse in Hc. rewrite <- reverse_list_twice in Hc. lia.
                    ** rewrite count_app in Hc. apply member_count_at_least_1 in Hxlu. apply member_count_at_least_1 in Hx. rewrite count_reverse in Hc. rewrite <- reverse_list_twice in Hc. simpl in Hc. destruct (ancu' =? x) as [|] eqn:F. lia. lia.
                  - reflexivity. }
                assert (Hancu_con: forall (z: node) (luz: nodes) (lv: nodes), is_directed_path_in_graph (ancu', z, luz) G = true
                                -> In ancu' (find_confounders_in_path (concat u ancu' v (rev lu) (luz ++ z :: rev lv)) G) /\ ~ In ancu' Z).
                { intros x luz1 lv1 Hdirluz1. split.
                  + apply confounders_vs_edges_in_path. destruct lu as [| hlu tlu].
                    * destruct luz1 as [| hluz tluz].
                      -- exists u. exists x. split.
                         ++ simpl. repeat rewrite eqb_refl. reflexivity.
                         ++ simpl in Hdirlu. rewrite andb_comm in Hdirlu. simpl in Hdirlu. split. apply Hdirlu.
                            simpl in Hdirluz1. rewrite andb_comm in Hdirluz1. simpl in Hdirluz1. apply Hdirluz1.
                      -- exists u. exists hluz. split.
                         ++ apply sublist_breaks_down_list. exists []. exists (tluz ++ x :: rev lv1 ++ [v]). simpl. rewrite <- app_assoc. simpl. reflexivity.
                         ++ simpl in Hdirlu. rewrite andb_comm in Hdirlu. simpl in Hdirlu. split. apply Hdirlu.
                            simpl in Hdirluz1. apply split_and_true in Hdirluz1. destruct Hdirluz1 as [Hdirluz1 _]. apply Hdirluz1.
                    * destruct luz1 as [| hluz tluz].
                      -- exists hlu. exists x. split.
                         ++ apply sublist_breaks_down_list. exists (u :: rev tlu). exists (rev lv1 ++ [v]). simpl. repeat rewrite <- app_assoc; simpl. reflexivity.
                         ++ simpl in Hdirlu. apply split_and_true in Hdirlu. destruct Hdirlu as [Hdirlu _]. split. apply Hdirlu.
                            simpl in Hdirluz1. rewrite andb_comm in Hdirluz1. simpl in Hdirluz1. apply Hdirluz1.
                      -- exists hlu. exists hluz. split.
                         ++ apply sublist_breaks_down_list. exists (u :: rev tlu). exists (tluz ++ x :: rev lv1 ++ [v]). simpl. repeat rewrite <- app_assoc; simpl. rewrite <- app_assoc. simpl. reflexivity.
                         ++ simpl in Hdirlu. apply split_and_true in Hdirlu. destruct Hdirlu as [Hdirlu _]. split. apply Hdirlu.
                            simpl in Hdirluz1. apply split_and_true in Hdirluz1. destruct Hdirluz1 as [Hdirluz1 _]. apply Hdirluz1.
                  + apply HluZ. left. reflexivity. }

                destruct Heqvancu' as [Hcol | Hcol].
                ++ (* no overlap between luz and lv, z is the collider *) destruct Hcol as [Hpathz [Hcycz Hconnz]].
                    exists z. exists luz. exists lv.
                    assert (Hconn: d_connected_2 (concat u ancu' v (rev lu) (luz ++ z :: (rev lv))) G Z /\ is_path_in_graph (u, v, rev lu ++ ancu' :: luz ++ z :: rev lv) G = true
                                    /\ acyclic_path_2 (u, v, rev lu ++ ancu' :: luz ++ z :: rev lv)).
                    { assert (Hpath: is_path_in_graph (u, v, rev lu ++ ancu' :: luz ++ z :: rev lv) G = true).
                      { apply concat_paths_still_a_path. split. apply reverse_path_in_graph. apply directed_path_is_path. apply Hdirlu.
                        apply concat_paths_still_a_path. split. apply directed_path_is_path. apply Hdirluz. apply reverse_path_in_graph. apply directed_path_is_path. apply Hdirvz. }
                      assert (Hcyc: acyclic_path_2 (u, v, rev lu ++ ancu' :: luz ++ z :: rev lv)).
                      { apply concat_paths_acyclic.
                        * split. apply Huveq. split.
                          -- apply Hcyclu.
                          -- apply Hcycz.
                        * split.
                          -- intros Hu. apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]].
                             ++ (* contradicts Hcycuz, which starts at u and passes through luz *)
                                unfold acyclic_path_2 in Hcycuz. destruct Hcycuz as [_ [Hcycuz _]]. apply Hcycuz. apply membership_append_r. right. apply Hu.
                             ++ (* contradiction: z is in Z, while u is not *)
                                apply Huz. symmetry. apply Hu.
                             ++ (* contradiction: then v is an unblocked ancestor of u *)
                                apply Hulv. apply membership_rev. apply Hu.
                          -- intros Hvlu'. apply Hvlu. apply membership_rev. apply Hvlu'.
                        * destruct (overlap (rev lu) (luz ++ z :: rev lv)) as [|] eqn:F.
                          -- apply overlap_has_member_in_common in F. destruct F as [x [Hxlu Hx]].
                             apply membership_append_or in Hx. destruct Hx as [Hx | [Hx | Hx]].
                             ++ apply no_overlap_non_member with (x := x) in Hluluz.
                                ** exfalso. apply Hluluz. apply membership_rev. apply Hxlu.
                                ** apply Hx.
                             ++ (* contradiction: HluZ implies z is not in Z *)
                                exfalso. apply HluZ with (w := z). right. left. rewrite Hx. apply membership_rev. apply Hxlu. apply HzZ.
                             ++ apply no_overlap_non_member with (x := x) in Hlulv.
                                ** exfalso. apply Hlulv. apply membership_rev. apply Hxlu.
                                ** apply membership_rev. apply Hx.
                          -- reflexivity. }
                      split. apply concat_d_connected_paths.
                      - apply HG.
                      - apply Hpath.
                      - split.
                        + apply reverse_d_connected_paths. apply Hdconn1. split. apply Hdirlu. intros w [Hw | Hw]. apply HluZ. left. apply Hw. apply HluZ. right. left. apply Hw.
                          apply reverse_path_still_acyclic in Hcyclu. rewrite <- reverse_list_twice in Hcyclu. apply Hcyclu.
                        + split. apply Hconnz. apply Hcyc.
                      - right. left. apply Hanc_con. apply Hdirluz. split. apply Hdirlu. apply HluZ. left. reflexivity.
                      - split. apply Hpath. apply Hcyc. }
                     split. unfold concat in Hconn. unfold concat. rewrite <- app_assoc. apply Hconn.
                     left. easy.
                 ++ (* z is a descendant of the collider (overlapping point of lu and lv) *) 
                    destruct Hcol as [luz1 [luz2 [lv' [lv1 [lv2 [x [Hdirvz' [Hcycvz' [HlvZ' [Hluz [Hlv [Hlv' [Hlu1lv1 [Hconnx [Hpathx Hcycx]]]]]]]]]]]]]]].
                    exists x. exists luz1. exists lv1.
                    assert (Hconn: d_connected_2 (concat u ancu' v (rev lu) (luz1 ++ x :: (rev lv1))) G Z /\ is_path_in_graph (concat u ancu' v (rev lu) (luz1 ++ x :: (rev lv1))) G = true
                                    /\ acyclic_path_2 (concat u ancu' v (rev lu) (luz1 ++ x :: (rev lv1)))).
                    { assert (Hpath: is_path_in_graph (concat u ancu' v (rev lu) (luz1 ++ x :: (rev lv1))) G = true).
                      { apply concat_paths_still_a_path. split. apply reverse_path_in_graph. apply directed_path_is_path. apply Hdirlu.
                        apply concat_paths_still_a_path. split. apply directed_path_is_path.
                        apply subpath_still_directed_2 with (v := z) (l2 := luz2) (l3 := luz). split. symmetry. apply Hluz. apply Hdirluz.
                        apply reverse_path_in_graph. apply directed_path_is_path. apply subpath_still_directed_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply Hlv. apply Hdirvz. }
                      assert (Hcyc: acyclic_path_2 (concat u ancu' v (rev lu) (luz1 ++ x :: (rev lv1)))).
                      { apply concat_paths_acyclic.
                        * split. apply Huveq. split.
                          -- apply Hcyclu.
                          -- apply concat_paths_acyclic. split. apply Hvancu'.
                             ++ split. apply subpath_still_acyclic_2 with (v := z) (l2 := luz2) (l3 := luz). split. symmetry. apply Hluz.
                                apply subpath_still_acyclic with (w := u) (l1 := rev lu) (l3 := rev lu ++ [ancu'] ++ luz). split. reflexivity. apply Hcycuz.
                                apply reverse_path_still_acyclic. apply subpath_still_acyclic_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply Hlv. apply Hcycvz.
                             ++ split.
                                ** (* contradiction: then v is an unblocked ancestor of u *)
                                   intros Hancu'. apply membership_rev in Hancu'. rewrite <- reverse_list_twice in Hancu'.
                                   apply membership_splits_list in Hancu'. destruct Hancu' as [lv1' [lv1'' Hlv1]].

                                   assert (Hlv1': forall (x': node), In x' lv1' -> In x' lv).
                                   { intros x' Hxlv1'. apply membership_append with (l2 := [ancu'] ++ lv1'') in Hxlv1'. apply membership_append with (l2 := [x] ++ lv2) in Hxlv1'.
                                     rewrite Hlv. rewrite <- Hlv1. apply Hxlv1'. }

                                   apply no_overlap_non_member with (x := v) in Hover. apply Hover.
                                   --- apply unblocked_ancestors_have_unblocked_directed_path. right. exists (lv1' ++ ancu' :: lu).
                                       split. apply concat_directed_paths. split. apply subpath_still_directed_2 with (v := x) (l2 := lv1'') (l3 := lv1).
                                       split. apply Hlv1. apply subpath_still_directed_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply Hlv. apply Hdirvz.
                                       apply Hdirlu. split. apply concat_paths_acyclic.
                                       +++ split. intros Hvu. apply Huveq. symmetry. apply Hvu. split.
                                           *** apply subpath_still_acyclic_2 with (v := x) (l2 := lv1'') (l3 := lv1). split. apply Hlv1.
                                               apply subpath_still_acyclic_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply Hlv. apply Hcycvz.
                                           *** rewrite reverse_list_twice with (l := lu). apply reverse_path_still_acyclic. apply Hcyclu.
                                       +++ split.
                                           *** apply Hvlu.
                                           *** intros Hulv1. apply Hlv1' in Hulv1. apply Hulv. apply Hulv1.
                                       +++ destruct (overlap lv1' lu) as [|] eqn:F. apply overlap_has_member_in_common in F. destruct F as [x' [Hxlv1' Hxlu]].
                                           apply no_overlap_non_member with (x := x') in Hlulv.
                                           *** exfalso. apply Hlulv. apply Hxlu.
                                           *** apply Hlv1'. apply Hxlv1'.
                                           *** reflexivity.
                                       +++ intros w [Hw | Hw]. apply HlvZ'. left. apply Hw. apply membership_append_or in Hw. destruct Hw as [Hw | [Hw | Hw]].
                                           *** apply HlvZ. right. apply Hlv1'. apply Hw.
                                           *** apply HluZ. left. symmetry. apply Hw.
                                           *** apply HluZ. right. left. apply Hw.
                                   --- unfold find_unblocked_ancestors. left. reflexivity.
                                ** intros Hvluz1. 
                                   (* contradicts Hcycx, which passes through both v and luz1 *)
                                   unfold acyclic_path_2 in Hcycx. destruct Hcycx as [_ [_ [Hcycx _]]]. apply Hcycx. apply membership_append. apply Hvluz1.
                             ++ apply overlap_rev. apply Hlu1lv1.
                        * split.
                          -- intros Hu. apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]].
                             ++ (* contradicts Hcycuz, which starts at u and passes through luz *)
                                unfold acyclic_path_2 in Hcycuz. destruct Hcycuz as [_ [Hcycuz _]]. apply Hcycuz. apply membership_append_r. right. apply membership_append with (l2 := [x] ++ luz2) in Hu. rewrite Hluz. apply Hu.
                             ++ (* contradiction: contradicts Hcycuz, which starts at u and passes through luz *)
                                unfold acyclic_path_2 in Hcycuz. destruct Hcycuz as [_ [Hcycuz _]]. apply Hcycuz. apply membership_append_r. right. rewrite Hluz. apply membership_append_r. apply membership_append. left. apply Hu.
                             ++ apply Hulv. apply membership_rev in Hu. rewrite <- reverse_list_twice in Hu. apply membership_append with (l2 := [x] ++ lv2) in Hu. rewrite Hlv. apply Hu.
                          -- intros Hvlu'. apply Hvlu. apply membership_rev. apply Hvlu'.
                        * destruct (overlap (rev lu) (luz1 ++ x :: rev lv1)) as [|] eqn:F.
                          -- apply overlap_has_member_in_common in F. destruct F as [x' [Hxlu Hx]].
                             apply membership_append_or in Hx. destruct Hx as [Hx | [Hx | Hx]].
                             ++ apply no_overlap_non_member with (x := x') in Hluluz.
                                ** exfalso. apply Hluluz. apply membership_rev. apply Hxlu.
                                ** apply membership_append with (l2 := [x] ++ luz2) in Hx. rewrite Hluz. apply Hx.
                             ++ apply no_overlap_non_member with (x := x) in Hluluz.
                                ** exfalso. apply Hluluz. apply membership_rev. rewrite Hx. apply Hxlu.
                                ** rewrite Hluz. apply membership_append_r. apply membership_append. left. reflexivity.
                             ++ apply no_overlap_non_member with (x := x') in Hlulv.
                                ** exfalso. apply Hlulv. apply membership_rev. apply Hxlu.
                                ** rewrite Hlv. apply membership_append. apply membership_rev. apply Hx.
                          -- reflexivity. }
                      split. apply concat_d_connected_paths.
                      - apply HG.
                      - apply Hpath.
                      - split.
                        + apply reverse_d_connected_paths. apply Hdconn1. split. apply Hdirlu. intros w [Hw | Hw]. apply HluZ. left. apply Hw. apply HluZ. right. left. apply Hw.
                          apply reverse_path_still_acyclic in Hcyclu. rewrite <- reverse_list_twice in Hcyclu. apply Hcyclu.
                        + split. apply Hconnx. apply Hcyc.
                      - right. left. apply Hanc_con. apply subpath_still_directed_2 with (v := z) (l2 := luz2) (l3 := luz).
                        split. symmetry. apply Hluz. apply Hdirluz. split. apply Hdirlu. apply HluZ. left. reflexivity.
                      - split. apply Hpath. apply Hcyc. }
                     split. unfold concat in Hconn. unfold concat. rewrite <- app_assoc. apply Hconn.
                     right. exists luz2. exists lv2. easy.
              -- split. apply Hdirluz. split. apply subpath_still_acyclic with (w := u) (l1 := rev lu) (l3 := rev lu ++ [ancu'] ++ luz).
                 ++ split. reflexivity. apply Hcycuz.
                 ++ intros w Hw. apply HluZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. right. apply Hw.
              -- split. apply Hdirvz. split. apply Hcycvz. apply HlvZ. }


            (* in a path with structure u <- ..lu.. <- ancu' -> ..luz.. -> z <- ..lv.. <- v, where z is the only node in the path in Z,
               u and v cannot be d-separated *)
            assert (Hconn_con_col: forall (u v ancu': node) (lv lu luz: nodes), z <> v /\ u <> z /\ u <> v
                      -> d_connected_2 (v, z, lv) G Z /\ is_directed_path_in_graph (v, z, lv) G = true /\ acyclic_path_2 (v, z, lv) /\ (forall w : node, w = v \/ In w lv -> ~ In w Z)
                      -> d_connected_2 (u, z, rev lu ++ ancu' :: luz) G Z /\ is_path_in_graph (u, z, rev lu ++ ancu' :: luz) G = true /\ acyclic_path_2 (u, z, rev lu ++ ancu' :: luz)
                         /\ is_directed_path_in_graph (ancu', u, lu) G = true /\ is_directed_path_in_graph (ancu', z, luz) G = true /\ (forall w : node, w = ancu' \/ In w lu \/ In w luz -> ~ In w Z)
                      -> d_separated_bool u v G Z = true
                      -> overlap (find_unblocked_ancestors G u Z) (find_unblocked_ancestors G v Z) = false
                      -> False).
            { intros u v ancu' lv lu luz. intros Heq. intros Hvz. intros Huz. intros Hdsep. intros Hover.
              specialize Hconn_con_col' with (u := u) (v := v) (ancu' := ancu') (lv := lv) (lu := lu) (luz := luz).

              assert (Hcol: exists (x : node) (luz1 lv1 : nodes),
                     (d_connected_2 (concat u x v (rev lu ++ ancu' :: luz1) (rev lv1)) G Z /\
                      is_path_in_graph (concat u x v (rev lu ++ ancu' :: luz1) (rev lv1)) G = true /\
                      acyclic_path_2 (concat u x v (rev lu ++ ancu' :: luz1) (rev lv1))) /\
                     (luz1 = luz /\ lv1 = lv /\ z = x \/
                      (exists luz2 lv2 : nodes, luz = luz1 ++ [x] ++ luz2 /\ lv = lv1 ++ [x] ++ lv2))).
              { apply Hconn_con_col'. easy. easy. easy. easy. }
              destruct Hcol as [x [luz1 [lvz1 [Hpath Hcol]]]].
              unfold concat in Hpath. apply d_connected_path_not_d_separated with (l := (rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) in Hdsep.
              + exfalso. apply Hdsep.
              + apply Hpath.
              + apply Hpath. }

            destruct HzZ as [HzZ Hnodez].
            assert (Hzv: z <> v'). { intros Hzv. rewrite Hzv in HzZ. destruct HZ as [_ [_ [_ HZ]]]. apply member_In_equiv in HzZ. rewrite HzZ in HZ. discriminate HZ. }
            assert (Hzu: u' <> z). { intros Hzu. rewrite <- Hzu in HzZ. destruct HZ as [_ [_ [HZ _]]]. apply member_In_equiv in HzZ. rewrite HzZ in HZ. discriminate HZ. }
            pose proof Hdsep' as Hdsep. clear Hdsep'. pose proof Hover' as Hover. clear Hover'. pose proof Hequv' as Huveq. clear Hequv'.
            remember u' as u. remember v' as v.

            apply Hconvz in Hzv as Hzv'. clear Hconvz. destruct Hzv' as [Hvlz | [Hzlv | Hconvz]].
            + destruct Hvlz as [lv [Hconnvz [Hdirvz [Hcycvz HlvZ]]]]. (* z <- ..lv.. <- v *)
              pose proof Hdconn_con as Hconuz. specialize Hconuz with (anc := ancu) (u := u) (v := z).
              apply Hconuz in Hzu as Hzu'. clear Hconuz. destruct Hzu' as [Hzlu | [Hulz | Hconuz]].
              * destruct Hzlu as [lz [Hconnzu [Hdirzu [Hcyczu HlzZ]]]]. (* u <- ..lz.. <- z *)
                (* contradiction, HlzZ says z is not in Z. *)
                specialize HlzZ with (w := z). exfalso. apply HlzZ. left. reflexivity. apply HzZ.
              * destruct Hulz as [lu [Hconnuz [Hdiruz [Hcycuz HluZ]]]].
                (* u -> ..lu.. -> z <- ..lv.. <- v *)
                assert (Hconn: exists (l: nodes), d_connected_2 (u, v, l) G Z /\ is_path_in_graph (u, v, l) G = true /\ acyclic_path_2 (u, v, l)).
                { assert (Hcol: is_path_in_graph (concat u z v lu (rev lv)) G = true /\
                                acyclic_path_2 (concat u z v lu (rev lv)) /\
                                d_connected_2 (concat u z v lu (rev lv)) G Z \/
                                (exists (lu1 lu2 lv' lv1 lv2 : nodes) (x : node),
                                   is_directed_path_in_graph (v, z, lv') G = true /\
                                   acyclic_path_2 (v, z, lv') /\
                                   (forall w : node, w = v \/ In w lv' -> ~ In w Z) /\
                                   lu = lu1 ++ [x] ++ lu2 /\
                                   lv = lv1 ++ [x] ++ lv2 /\
                                   lv' = lv1 ++ [x] ++ lu2 /\
                                   overlap lu1 lv1 = false /\
                                   d_connected_2 (u, v, lu1 ++ [x] ++ rev lv1) G Z /\
                                   is_path_in_graph (u, v, lu1 ++ [x] ++ rev lv1) G = true /\
                                   acyclic_path_2 (u, v, lu1 ++ [x] ++ rev lv1))).
                  { apply Hconn_col.
                    - split. apply HzZ. split. apply Huveq. apply Hover.
                    - split. apply Hdiruz. split. apply Hcycuz. apply HluZ.
                    - split. apply Hdirvz. split. apply Hcycvz. apply HlvZ. }
                  destruct Hcol as [[Hpath [Hcyc Hconn]] | [lu'' [l [lv' [lv'' [l' [x [_ [_ [_ [_ [_ [_ [_ Hcol]]]]]]]]]]]]]].
                  - exists (lu ++ z :: (rev lv)). split. apply Hconn. split. apply Hpath. apply Hcyc.
                  - exists (lu'' ++ [x] ++ (rev lv'')). apply Hcol. }
                exfalso. destruct Hconn as [l Hconn]. apply d_connected_path_not_d_separated with (u := u) (v := v) (l := l) (G := G) (Z := Z).
                ** apply Hconn.
                ** apply Hconn.
                ** apply Hdsep.
              * destruct Hconuz as [lu [luz [ancu' [Hconnuz [Hpathuz [Hdirlu [Hdirluz [Hcycuz HluZ]]]]]]]].
                (* u <- ..lu.. <- ancu' -> ..luz.. -> z <- ..lv.. <- v *)
                exfalso. specialize Hconn_con_col with (u := u) (v := v) (ancu' := ancu') (lv := lv) (lu := lu) (luz := luz).
                apply Hconn_con_col. easy. easy. easy. easy. easy.
              * split. apply Hancuz. apply Hancu.
            + destruct Hzlv as [lz [Hconnzv [Hdirzv [Hcyczv HlzZ]]]].
              (* contradiction, HlzZ says z is not in Z. *)
              specialize HlzZ with (w := z). exfalso. apply HlzZ. left. reflexivity. apply HzZ.
            + destruct Hconvz as [lvz [lv [ancv' [Hconnzv [Hpathzv [Hdirlvz [Hdirlv [Hcyczv HlvZ]]]]]]]].
              (* z <- ..lvz.. <- ancv' -> ..lv.. -> v *)
              pose proof Hdconn_con as Hconuz. specialize Hconuz with (anc := ancu) (u := u) (v := z).
              apply Hconuz in Hzu as Hzu'. clear Hconuz. destruct Hzu' as [Hzlu | [Hulz | Hconuz]].
              * destruct Hzlu as [lz [Hconnzu [Hdirzu [Hcyczu HlzZ]]]]. (* u <- ..lz.. <- z *)
                (* contradiction, HlzZ says z is not in Z. *)
                specialize HlzZ with (w := z). exfalso. apply HlzZ. left. reflexivity. apply HzZ.
              * destruct Hulz as [lu [Hconnuz [Hdiruz [Hcycuz HluZ]]]].
                (* u -> ..lu.. -> z <- ..lvz.. <- ancv' -> ..lv.. -> v *)
                exfalso. specialize Hconn_con_col with (u := v) (v := u) (ancu' := ancv') (lv := lu) (lu := lv) (luz := lvz).
                apply Hconn_con_col. easy. easy.
                rewrite reverse_list_twice with (l := rev lv ++ ancv' :: lvz). rewrite reverse_list_append. rewrite <- reverse_list_twice.
                split.
                -- apply reverse_d_connected_paths. simpl. rewrite <- app_assoc. apply Hconnzv.
                -- split.
                   ++ simpl. apply reverse_path_in_graph. rewrite append_vs_concat. apply Hpathzv.
                   ++ split. simpl. apply reverse_path_still_acyclic. rewrite append_vs_concat. apply Hcyczv.
                      split. easy. split. easy. intros w Hw. apply HlvZ. destruct Hw as  [Hw | [Hw | Hw]].
                      left. apply Hw. right. right. apply Hw. right. left. apply Hw.
                -- apply d_separated_symmetry. apply Hdsep.
                -- apply overlap_flip. apply Hover.
              * destruct Hconuz as [lu [luz [ancu' [Hconnuz [Hpathuz [Hdirlu [Hdirluz [Hcycuz HluZ]]]]]]]].
                assert (Hvancv': is_directed_path_in_graph (ancv', v, lv) G = true /\ acyclic_path_2 (ancv', v, lv) /\ (forall w : node, w = ancv' \/ In w lv -> ~ In w Z)).
                { split. apply Hdirlv. split.
                  - apply subpath_still_acyclic with (w := z) (l1 := rev lvz) (l3 := rev lvz ++ [ancv'] ++ lv).
                    split. reflexivity. apply Hcyczv.
                  - intros w Hw. apply HlvZ. rewrite <- or_assoc. rewrite or_comm. rewrite <- or_assoc. left. rewrite or_comm. apply Hw. }
                assert (Huancu': is_directed_path_in_graph (ancu', u, lu) G = true /\ acyclic_path_2 (ancu', u, lu) /\ (forall w : node, w = ancu' \/ In w lu -> ~ In w Z)).
                { split. apply Hdirlu. split.
                  ++ rewrite reverse_list_twice with (l := lu). apply reverse_path_still_acyclic.
                     apply subpath_still_acyclic_2 with (v := z) (l2 := luz) (l3 := rev lu ++ [ancu'] ++ luz).
                     split. reflexivity. apply Hcycuz.
                  ++ intros w Hw. apply HluZ. rewrite <- or_assoc. left. apply Hw. }
                assert (Hzancu': is_directed_path_in_graph (ancu', z, luz) G = true /\ acyclic_path_2 (ancu', z, luz) /\ (forall w : node, w = ancu' \/ In w luz -> ~ In w Z)).
                { split. apply Hdirluz. split. apply subpath_still_acyclic with (w := u) (l1 := rev lu) (l3 := rev lu ++ [ancu'] ++ luz). split. reflexivity. apply Hcycuz.
                  intros w [Hw | Hw]. apply HluZ. left. apply Hw. apply HluZ. right. right. apply Hw. }

                (* u <- ..lu.. <- ancu' -> ..luz.. -> z <- ..lvz.. <- ancv' -> ..lv.. -> v *)
                specialize Hconn_con_col' with (u := u) (v := ancv') (ancu' := ancu') (lv := lvz) (lu := lu) (luz := luz).
                assert (Hcol: exists (x : node) (luz1 lv1 : nodes),
                     (d_connected_2
                        (concat u x ancv' (rev lu ++ ancu' :: luz1) (rev lv1)) G Z /\
                      is_path_in_graph
                        (concat u x ancv' (rev lu ++ ancu' :: luz1) (rev lv1)) G =
                      true /\
                      acyclic_path_2
                        (concat u x ancv' (rev lu ++ ancu' :: luz1) (rev lv1))) /\
                     (luz1 = luz /\ lv1 = lvz /\ z = x \/
                      (exists luz2 lv2 : nodes,
                         luz = luz1 ++ [x] ++ luz2 /\ lvz = lv1 ++ [x] ++ lv2))).
                { apply Hconn_con_col'.
                  - repeat split.
                    + intros Hancvz'. apply HlvZ with (w := z). left. apply Hancvz'. apply HzZ.
                    + apply Hzu.
                    + (* else, u is an unblocked ancestor of v *) intros F. apply no_overlap_non_member_rev with (x := u) in Hover.
                      { apply Hover. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lv.
                        rewrite F in *. apply Hvancv'. }
                      { unfold find_unblocked_ancestors. left. reflexivity. }
                  - split.
                    + apply Hdconn1. split. apply Hdirlvz. intros w Hw. apply HlvZ. rewrite <- or_assoc. left. apply Hw.
                      rewrite reverse_list_twice with (l := lvz). apply reverse_path_still_acyclic. apply subpath_still_acyclic_2 with (v := v) (l2 := lv) (l3 := rev lvz ++ ancv' :: lv). split. reflexivity. apply Hcyczv.
                    + split. apply Hdirlvz. split.
                      * rewrite reverse_list_twice with (l := lvz). apply reverse_path_still_acyclic.
                        apply subpath_still_acyclic_2 with (v := v) (l2 := lv) (l3 := rev lvz ++ [ancv'] ++ lv).
                        split.  reflexivity. apply Hcyczv.
                      * intros w Hw. apply HlvZ. rewrite <- or_assoc. left. apply Hw.
                  - easy.
                  - (* otherwise, u and v would have a common unblocked ancestor *) apply overlap_flip. apply no_common_unblocked_ancestors_transitive with (u := v).
                    split. apply overlap_flip. apply Hover. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lv. easy. }
                unfold concat in Hcol. destruct Hcol as [x [luz1 [lvz1 Hcol]]]. destruct Hcol as [[Hconnu [Hpathu Hcycu]] Hcol].
                assert (Hconn: d_connected_2 (concat u ancv' v ((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) lv) G Z
                                  /\ is_path_in_graph (concat u ancv' v ((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) lv) G = true
                                  /\ acyclic_path_2 (concat u ancv' v ((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) lv)).
                { assert (Hpath: is_path_in_graph (concat u ancv' v ((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) lv) G = true).
                  { apply concat_paths_still_a_path. split. apply Hpathu. apply directed_path_is_path. apply Hdirlv. }
                  assert (Hcyc: acyclic_path_2 (concat u ancv' v ((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) lv)).
                  { apply concat_paths_acyclic.
                    - split. apply Huveq. split. apply Hcycu. apply subpath_still_acyclic with (w := z) (l1 := rev lvz) (l3 := rev lvz ++ [ancv'] ++ lv).
                      split. reflexivity. apply Hcyczv.
                    - split.
                      + (* contradiction: then u is an unblocked ancestor of v *)
                        intros Hu.
                        apply no_overlap_non_member with (x := u) in Hover.
                        ++ apply Hover. unfold find_unblocked_ancestors. left. reflexivity.
                        ++ apply unblocked_ancestor_if_in_unblocked_directed_path with (anc := ancv') (l := lv).
                           ** easy.
                           ** apply Hu.
                      + intros Hvmem. apply membership_append_or in Hvmem. destruct Hvmem as [Hvmem | Hmem].
                        * apply membership_append_or in Hvmem. destruct Hvmem as [Hvmem | Hmem].
                          -- apply no_overlap_non_member with (x := v) in Hover. (* contradiction: then v is an unblocked ancestor of u *)
                             apply Hover.
                             apply unblocked_ancestor_if_in_unblocked_directed_path with (anc := ancu') (l := lu).
                             ** apply Huancu'.
                             ** apply membership_rev. apply Hvmem.
                             ** unfold find_unblocked_ancestors. left. reflexivity.
                          -- destruct Hmem as [F | F].
                             { apply no_overlap_non_member with (x := v) in Hover.
                               - apply Hover. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lu. rewrite <- F. apply Huancu'.
                               - unfold find_unblocked_ancestors. left. reflexivity. }
                             { (* contradiction: then ancu' is a common ancestor of u and v *)
                               apply no_overlap_non_member with (x := ancu') in Hover.
                               - apply Hover. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lu. apply Huancu'.
                               - apply unblocked_ancestors_have_unblocked_directed_path. right. apply membership_splits_list in F. destruct F as [luz1' [luz1'' Hluz1]]. exists luz1'.
                                 destruct Hcol as [Hcol | Hcol].
                                 + destruct Hcol as [Hcol _]. rewrite Hcol in *. split. apply subpath_still_directed_2 with (v := z) (l2 := luz1'') (l3 := luz). split. apply Hluz1.
                                   apply Hdirluz. split. apply subpath_still_acyclic_2 with (v := z) (l2 := luz1'') (l3 := luz). split. apply Hluz1. apply Hzancu'.
                                   intros w Hw. destruct Hzancu' as [_ [_ Hzancu']]. apply Hzancu'. destruct Hw as [Hw | Hw]. left. apply Hw. right. apply membership_append with (l2 := [v] ++ luz1'') in Hw. rewrite <- Hluz1. apply Hw.
                                 + destruct Hcol as [luz2 [_ [Hluz _]]]. split. apply subpath_still_directed_2 with (v := x) (l2 := luz1'') (l3 := luz1). split. apply Hluz1.
                                   apply subpath_still_directed_2 with (v := z) (l2 := luz2) (l3 := luz). split. symmetry. apply Hluz. apply Hdirluz.
                                   split. apply subpath_still_acyclic_2 with (v := x) (l2 := luz1'') (l3 := luz1). split. apply Hluz1.
                                   apply subpath_still_acyclic_2 with (v := z) (l2 := luz2) (l3 := luz). split. symmetry. apply Hluz. apply Hzancu'.
                                   intros w Hw. destruct Hzancu' as [_ [_ Hzancu']]. apply Hzancu'. destruct Hw as [Hw | Hw]. left. apply Hw. right. apply membership_append with (l2 := [v] ++ luz1'') in Hw. rewrite Hluz. rewrite <- Hluz1. apply membership_append. apply Hw. }
                        * unfold acyclic_path_2 in Hcyczv. destruct Hcol as [Hcol | Hcol].
                          -- destruct Hmem as [Hmem | Hmem]. destruct Hcyczv as [Hcyczv _]. apply Hcyczv. destruct Hcol as [_ [_ Hcol]]. rewrite Hcol. apply Hmem.
                             destruct Hcyczv as [_ [_ [Hcycvz _]]]. apply Hcycvz. apply membership_append. destruct Hcol as [_ [Hcol _]]. rewrite Hcol in Hmem. apply Hmem.
                          -- destruct Hcyczv as [_ [_ [Hcycvz _]]]. apply Hcycvz. apply membership_append. destruct Hcol as [_ [lvz2 [_ Hluz]]]. rewrite Hluz.
                             rewrite app_assoc. rewrite reverse_list_append. apply membership_append_r. rewrite reverse_list_append. simpl. simpl in Hmem. apply Hmem.
                    - apply no_overlap_non_member. intros x' Hxlv Hx'.
                      assert (Hxv': In x' (find_unblocked_ancestors G v Z)).
                      { apply unblocked_ancestor_if_in_unblocked_directed_path with (anc := ancv') (l := lv). apply Hvancv'. apply Hxlv. }
                      rewrite <- append_vs_concat in Hx'. apply membership_append_or in Hx'. destruct Hx' as [Hx' | Hx'].
                      + (* contradiction: ancu' is a shared unblocked ancestor of u and v *)
                        assert (Hxu': In ancu' (find_unblocked_ancestors G v Z)).
                        { apply unblocked_ancestors_transitive with (ancu' := x'). apply Hxv'.
                          apply membership_append_or in Hx'; destruct Hx' as [Hx' | Hx']. apply membership_append_or in Hx'; destruct Hx' as [Hx' | Hx'].
                          - apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := u) (l := lu). apply Huancu'. apply membership_rev. apply Hx'.
                          - destruct Hx' as [Hx' | Hx']. apply unblocked_ancestors_have_unblocked_directed_path. left. apply Hx'.
                            apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := luz). apply Hzancu'.
                            destruct Hcol as [Hcol | Hcol].
                            + destruct Hcol as [Hcol _]. rewrite <- Hcol. apply Hx'.
                            + destruct Hcol as [luz2 [_ [Hluz _]]]. rewrite Hluz. apply membership_append. apply Hx'.
                          - destruct Hcol as [Hcol | Hcol].
                            + simpl in Hx'. destruct Hx' as [Hx' | F]. rewrite <- Hx'. destruct Hcol as [_ [_ Hcol]]. rewrite <- Hcol.
                              apply unblocked_ancestors_have_unblocked_directed_path. right. exists luz. apply Hzancu'. exfalso. apply F.
                            + apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := luz). apply Hzancu'.
                              destruct Hcol as [luz2 [_ [Hluz _]]]. rewrite Hluz. apply membership_append_r. apply membership_append. apply Hx'. }
                        apply no_overlap_non_member with (x := ancu') in Hover.
                        * apply Hover. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lu. apply Huancu'.
                        * apply Hxu'.
                      + (* contradicts Hcyczv *)
                        apply acyclic_path_correct in Hcyczv. simpl in Hcyczv. apply split_and_true in Hcyczv; destruct Hcyczv as [_ Hcyczv]. apply split_and_true in Hcyczv; destruct Hcyczv as [_ Hcyczv].
                        apply acyclic_path_intermediate_nodes with (p := rev lvz ++ ancv' :: lv) (x := x') in Hcyczv. destruct Hcyczv as [Hc | Hc].
                        ** rewrite count_app in Hc. apply member_count_at_least_1 in Hxlv. apply membership_rev in Hx'. rewrite <- reverse_list_twice in Hx'.
                           apply member_count_at_least_1 in Hx'. simpl in Hc. destruct (ancv' =? x') as [|]. lia. lia.
                        ** destruct Hcol as [Hcol | Hcol].
                           -- destruct Hcol as [_ [Hcol _]]. rewrite Hcol in Hx'. apply member_count_at_least_1 in Hx'. rewrite <- count_reverse in Hx'. apply member_count_at_least_1 in Hxlv.
                              rewrite count_app in Hc. rewrite count_reverse in Hc. rewrite <- reverse_list_twice in Hc. simpl in Hc. destruct (ancv' =? x') as [|]. lia. lia.
                           -- destruct Hcol as [_ [lvz2 [_ Hlvz]]]. apply <- membership_rev in Hx'. rewrite <- reverse_list_twice in Hx'. apply membership_append with (l2 := [x] ++ lvz2) in Hx'. rewrite <- Hlvz in Hx'.
                              apply member_count_at_least_1 in Hx'. apply member_count_at_least_1 in Hxlv. rewrite count_app in Hc. simpl in Hc. rewrite count_reverse in Hc. rewrite <- reverse_list_twice in Hc. destruct (ancv' =? x') as [|]. lia. lia. }
                  split.
                  - apply concat_d_connected_paths.
                    + apply HG.
                    + apply Hpath.
                    + split. apply Hconnu. split.
                      * apply Hdconn1. split. apply Hvancv'. apply Hvancv'. apply Hvancv'.
                      * apply Hcyc.
                    + right. left. split.
                      * assert (Hcon: In ancv' (find_confounders_in_path (concat v ancv' ancu' (rev lv) (lvz1 ++ x :: rev luz1)) G) /\ ~(In ancv' Z)).
                        { specialize Hanc_con with (u := v) (ancu' := ancv') (z := x) (v := ancu') (lu := lv) (luz := lvz1) (lv := luz1). apply Hanc_con.
                          - destruct Hcol as [Hcol | Hcol].
                            + destruct Hcol as [_ [Hlvz Hzx]]. rewrite Hlvz. rewrite <- Hzx. apply Hdirlvz.
                            + destruct Hcol as [luz2 [lvz2 [Hluz Hlvz]]]. apply subpath_still_directed_2 with (v := z) (l2 := lvz2) (l3 := lvz). split. symmetry. apply Hlvz. apply Hdirlvz.
                          - split. apply Hvancv'. apply HlvZ. left. reflexivity. }
                        unfold concat in Hcon. destruct Hcon as [Hcon Hancv']. apply confounders_same_in_reverse_path in Hcon. rewrite reverse_list_append in Hcon.
                        rewrite <- reverse_list_twice in Hcon.
                        apply concat_preserves_confounders_r with (u := u) (l1 := rev lu) in Hcon.
                        unfold concat in Hcon. unfold concat.
                        replace (((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) ++ ancv' :: lv) with (rev lu ++ ancu' :: rev (ancv' :: lvz1 ++ x :: rev luz1) ++ lv).
                        -- apply Hcon.
                        -- simpl. rewrite reverse_list_append. simpl. rewrite <- reverse_list_twice. simpl. rewrite <- app_assoc. clear Hconn_con_col. clear Hconn_con_col'. clear Hconn_col. clear Hdconn_con.
                           rewrite <- append_vs_concat. rewrite <- app_assoc. simpl. rewrite <- app_assoc. rewrite <- app_assoc. simpl.
                           replace ((rev lu ++ ancu' :: luz) ++ x :: rev lvz) with (rev lu ++ ancu' :: luz ++ x :: rev lvz). repeat rewrite <- app_assoc.
                           simpl. reflexivity.
                           rewrite <- app_assoc. simpl. reflexivity.
                      * apply HlvZ. left. reflexivity.
                  - split. apply Hpath. apply Hcyc. }
                unfold concat in Hconn. apply d_connected_path_not_d_separated with (l := ((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) ++ ancv' :: lv) in Hdsep.
                -- exfalso. apply Hdsep.
                -- apply Hconn.
                -- apply Hconn.
              * split. apply Hancuz. apply Hancu.
            + split. apply Hancv. apply Hancvz. }
Qed.

