From Semantics Require Import FunctionRepresentation.
From Semantics Require Import FindValue.
From CausalDiagrams Require Import Assignments.
From CausalDiagrams Require Import UnblockedAncestors.
(* From CausalDiagrams Require Import DSeparation.
From CausalDiagrams Require Import CausalPaths. *)
From DAGs Require Import Basics.
(* From DAGs Require Import CycleDetection. *)
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

