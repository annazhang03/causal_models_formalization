From CausalDiagrams Require Import CausalPaths.
From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import Assignments.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.


(* This file provides the framework for colliders, which along with sources and
   transmitters (S1_Sources.v and S2_transmitters.v) partition the nodes along a path.
   They are important in the context of descendant maps, described in ColliderDescendants.v
   and DescendantPathsDisjoint.v *)


Definition get_colliders_in_g_path (G: graph) (p: path): nodes :=
  find_colliders_in_path p G.

Lemma colliders_induction_into_start_out_of_h: forall (G: graph) (u h v: node) (t: nodes),
  contains_cycle G = false
  -> (path_into_start (u, v, h :: t) G = true \/ path_out_of_h G u v h t = true)
  -> get_colliders_in_g_path G (u, v, h :: t) = get_colliders_in_g_path G (h, v, t).
Proof.
  intros G u h v t Hcyc Hin.
  unfold get_colliders_in_g_path.
  simpl. destruct t as [| h' t'].
  - simpl. unfold is_collider_bool. destruct Hin as [Hin | Hin].
    + simpl in Hin. apply acyclic_no_two_cycle in Hin. rewrite Hin. simpl. reflexivity. apply Hcyc.
    + rewrite path_out_of_h_same in Hin. simpl in Hin. apply acyclic_no_two_cycle in Hin.
      rewrite Hin. rewrite andb_comm. simpl. reflexivity. apply Hcyc.
  - simpl. assert (is_collider_bool u h' h G = false).
    { unfold is_collider_bool. destruct Hin as [Hin | Hin].
      - simpl in Hin. apply acyclic_no_two_cycle in Hin.
        + rewrite Hin. simpl. reflexivity.
        + apply Hcyc.
      - rewrite path_out_of_h_same in Hin. simpl in Hin. apply acyclic_no_two_cycle in Hin. rewrite Hin. rewrite andb_comm. reflexivity.
        apply Hcyc. }
    rewrite H. reflexivity.
Qed.

Definition S3_nodes_colliders_in_graph {X: Type} (G: graph) (p: path) (A3: assignments (nat * nat * X * X)): Prop :=
  forall (c: node) (i j: nat) (x y: X), In (c, (i, j, x, y)) A3
  -> exists (a b: node), nth_error (find_parents c G) i = Some a /\ nth_error (find_parents c G) j = Some b
     /\ sublist [a; c; b] ((path_start p) :: (path_int p) ++ [path_end p]) = true /\ is_collider_bool a b c G = true.

Definition A3_consistent_with_D {X: Type} (D: assignments (nodes * node)) (A3: assignments (nat * nat * X * X)) (AZ: assignments X) : Prop :=
  forall (w: node) (iw jw: nat) (xw yw: X), get_assigned_value A3 w = Some (iw, jw, xw, yw)
  -> exists (p: nodes) (d: node), get_assigned_value D w = Some (p, d) /\ get_assigned_value AZ d = Some xw /\ xw <> yw.