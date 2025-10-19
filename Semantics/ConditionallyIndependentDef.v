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

(* find all unblocked ancestors of nodes in Z that have unblocked ancestor that changed in prev round TODO added 3.21, would be nice
   to show that this is equivalent to node in Z changing value? *)
Fixpoint find_unblocked_ancestors_in_Z'' {X: Type} `{EqType X} (G: graph) (Z: nodes) (AZ: assignments X) (S: nodes): nodes :=
  match AZ with
  | [] => []
  | (u, x) :: AZ' => if (overlap (find_unblocked_ancestors G u Z) S)
                       then (find_unblocked_ancestors G u Z) ++ (find_unblocked_ancestors_in_Z'' G Z AZ' S)
                       else find_unblocked_ancestors_in_Z'' G Z AZ' S
  end.

Theorem ancestor_in_Z_corresponds_to_conditioned_node {X: Type} `{EqType X}: forall (G: graph) (Z S: nodes) (AZ: assignments X) (anc z: node),
  is_assigned AZ z = true
  -> In anc (find_unblocked_ancestors G z Z) /\
     (exists (anc': node), In anc' (find_unblocked_ancestors G z Z) /\ In anc' S)
  -> In anc (find_unblocked_ancestors_in_Z'' G Z AZ S).
Proof.
  intros G Z S AZ anc z. intros Hz [Hanc [anc' Hanc']].
  induction AZ as [| [h x] AZ' IH].
  - simpl in Hz. discriminate Hz.
  - simpl. destruct (overlap (find_unblocked_ancestors G h Z) S) as [|] eqn:HhS.
    + simpl in HhS. rewrite HhS. rewrite app_comm_cons. destruct (h =? z) as [|] eqn:Hhz.
      * apply membership_append.
        apply unblocked_ancestors_have_unblocked_directed_path in Hanc. destruct Hanc as [Hanc | Hanc].
        ++ left. rewrite Hanc. apply eqb_eq. apply Hhz.
        ++ destruct Hanc as [l Hanc]. apply eqb_eq in Hhz. rewrite Hhz. apply unblocked_ancestors_have_unblocked_directed_path. right. exists l. apply Hanc.
      * apply membership_append_r. apply IH. simpl in Hz. rewrite eqb_sym in Hhz. rewrite Hhz in Hz. simpl in Hz. apply Hz.
    + simpl in Hz. destruct (z =? h) as [|] eqn:Hzh.
      * exfalso. apply no_overlap_non_member with (x := anc') in HhS.
        ++ apply HhS. apply eqb_eq in Hzh. rewrite <- Hzh. apply Hanc'.
        ++ apply Hanc'.
      * simpl in HhS. rewrite HhS. apply IH. simpl in Hz. apply Hz.
Qed.

Theorem ancestor_in_Z_corresponds_to_conditioned_node_rev {X: Type} `{EqType X}: forall (G: graph) (Z S: nodes) (AZ: assignments X) (anc: node),
  In anc (find_unblocked_ancestors_in_Z'' G Z AZ S)
  -> exists (z: node), In anc (find_unblocked_ancestors G z Z) /\ overlap (find_unblocked_ancestors G z Z) S = true
     /\ is_assigned AZ z = true.
Proof.
  intros G Z S AZ anc.
  intros Hanc.
  induction AZ as [| [z1 x1] AZ' IH].
  - simpl in Hanc. exfalso. apply Hanc.
  - destruct (overlap (find_unblocked_ancestors G z1 Z) S) as [|] eqn:Hover.
    + simpl in Hanc. simpl in Hover. rewrite Hover in Hanc. rewrite app_comm_cons in Hanc. apply membership_append_or in Hanc.
      destruct Hanc as [Hanc | Hanc].
      * exists z1. split. apply Hanc. split. apply Hover. simpl. rewrite eqb_refl. reflexivity.
      * apply IH in Hanc.
        destruct Hanc as [z Hz]. exists z. split. apply Hz. split. apply Hz. simpl. apply split_orb_true. right. apply Hz.
    + simpl in Hanc. simpl in Hover. rewrite Hover in Hanc.
      apply IH in Hanc.
      destruct Hanc as [z Hz]. exists z. split. apply Hz. split. apply Hz. simpl. apply split_orb_true. right. apply Hz.
Qed.


(* assumes A corresponds to get_values with U *)
Definition unobs_valid_given_u {X: Type} (G: graph) (U A: assignments X) (u: node) (a: X): Prop :=
  is_assignment_for U (nodes_in_graph G) = true /\ get_assigned_value A u = Some a.

Definition unobs_conditions_on_Z {X: Type} (G: graph) (g: graphfun) (U AZ: assignments X) (Z: nodes): Prop :=
  forall (w: node), In w Z /\ node_in_graph w G = true -> find_value G g w U [] = get_assigned_value AZ w.

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

Lemma equiv_assignments_preserve_unb_anc_changed {X: Type} `{EqType X}: forall (h h' h1 h1': assignments X) (V: nodes),
  assignments_equiv h h'
  -> assignments_equiv h1 h1'
  -> unblocked_ancestors_that_changed_A_to_B V h' h1' = unblocked_ancestors_that_changed_A_to_B V h h1.
Proof.
  intros h h' h1 h1' V Hh Hh1. induction V as [| v1 V'].
  - simpl. reflexivity.
  - simpl. rewrite Hh1. rewrite Hh. rewrite IHV'. reflexivity.
Qed.



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


Fixpoint assignments_change_only_for_Z_anc_seq' {X: Type} `{EqType X} (L: list (assignments X)) (Z: nodes) (AZ: assignments X) (G: graph): Prop :=
  match L with
  | [] => True
  | U1 :: L' => match L' with
                      | [] => True
                      | U2 :: L'' => match L'' with
                                           | [] => True
                                           | U3 :: L''' =>
                                                       assignments_change_only_for_subset U2 U3
                                                          (find_unblocked_ancestors_in_Z'' G Z AZ (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) U1 U2))
                                                       /\ assignments_change_only_for_Z_anc_seq' L' Z AZ G
                                           end
                      end
  end.

Lemma equiv_assignments_preserve_anc {X: Type} `{EqType X}: forall (L L': list (assignments X)) (Z: nodes) (AZ: assignments X) (G: graph),
  list_assignments_equiv L L'
  -> assignments_change_only_for_Z_anc_seq' L Z AZ G
  -> assignments_change_only_for_Z_anc_seq' L' Z AZ G.
Proof.
  intros L L' Z AZ G Heq HL.
  generalize dependent L. induction L' as [| h' t' IH].
  - intros L Heq HL. simpl. apply I.
  - intros L Heq HL. simpl. destruct t' as [| h1' t1']. apply I. destruct t1' as [| h2' t2']. apply I.
    destruct L as [| h t]. simpl in Heq. exfalso. apply Heq.
    destruct t as [| h1 t1]. simpl in Heq. exfalso. apply Heq.
    destruct t1 as [| h2 t2]. simpl in Heq. exfalso. apply Heq.
    simpl in Heq. split.
    + unfold assignments_change_only_for_Z_anc_seq' in HL. destruct HL as [HL _]. unfold assignments_change_only_for_subset.
      intros x. split.
      * split.
        { intros Hx. apply assigned_is_true. destruct Heq as [_ [Hh1 [Hh2 _]]]. rewrite <- Hh2. apply assigned_is_true. apply HL.
          apply assigned_is_true. rewrite Hh1. apply assigned_is_true. apply Hx. }
        { intros Hx. apply assigned_is_true. destruct Heq as [_ [Hh1 [Hh2 _]]]. rewrite <- Hh1. apply assigned_is_true. apply HL.
          apply assigned_is_true. rewrite Hh2. apply assigned_is_true. apply Hx. }
      * intros Hx. destruct Heq as [Hh [Hh1 [Hh2 _]]]. rewrite <- Hh1. rewrite <- Hh2. apply HL.
        assert (Hanc: unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) h' h1' = unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) h h1).
        { apply equiv_assignments_preserve_unb_anc_changed. apply Hh. apply Hh1. }
        rewrite <- Hanc. apply Hx.
    + apply IH with (L := h1 :: h2 :: t2). apply Heq. simpl in HL. apply HL.
Qed.


Definition conditionally_independent'' (X: Type) `{EqType X} (G: graph) (u v: node) (Z: nodes): Prop :=
  forall (AZ: assignments X), is_exact_assignment_for AZ Z /\ each_node_assigned_once AZ
  (* properly conditioned, consistent assignments where f(u)=a *)
  -> forall (g: graphfun) (a: X) (Ua Aa: assignments X),
      get_values G g Ua [] = Some Aa /\ unobs_valid_given_u G Ua Aa u a /\ unobs_conditions_on_Z G g Ua AZ Z
  (* assignments after setting f(u)=b and propagating *)
  -> forall (b: X) (Ub Ab: assignments X),
      (assignments_change_only_for_subset Ua Ub (find_unblocked_ancestors G u Z))
      /\ get_values G g Ub [] = Some Ab /\ (unobs_valid_given_u G Ub Ab u b)
  (* assignments after resetting changed conditioned variables and propagating *)
  -> forall (L: list (assignments X)),
      length L <= num_nodes G
  -> forall (Ub' Ab': assignments X), last (Ub :: L) Ub = Ub' /\ get_values G g Ub' [] = Some Ab'
     -> (unobs_conditions_on_Z G g Ub' AZ Z) /\ (unobs_valid_given_u G Ub' Ab' u b)
  -> assignments_change_only_for_Z_anc_seq' (Ua :: Ub :: L) Z AZ G
  (* value of v must stay constant *)
  -> get_assigned_value Aa v = get_assigned_value Ab' v.