From Utils Require Import Lists.
From Utils Require Import Logic.

From Coq Require Export Init.Nat.
From Coq Require Export Lists.List.
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.PeanoNat.
Require Import Coq.Program.Wf.

Import ListNotations.

From DAGs Require Import Basics.


(* this file defines an adjacency list representation of DAGs and proves its relationship
   to the vertices and edges representation. *)

(* [(node 1, all nodes to which node 1 has edges), (node 2, ...), ...] *)
Definition adj_list : Type := list (node * nodes).

(* neighbors of a node s are all nodes to which s has directed edges (immediate children of s) *)
Fixpoint neighbors_of_node (s: node) (E: edges) : nodes :=
  match E with
  | [] => []
  | h :: t => match h with
              | (u, v) => if (u =? s) then v :: neighbors_of_node s t else neighbors_of_node s t
              end
  end.

Lemma neighbors_vs_edges: forall u v: node, forall E: edges,
  member v (neighbors_of_node u E) = true <-> member_edge (u, v) E = true.
Proof.
  intros u v E.
  split.
  - intros H. induction E as [| h t IH].
    + simpl. simpl in H. apply H.
    + simpl. destruct (eqbedge h (u, v)) as [|] eqn:Hedge.
      * reflexivity.
      * apply IH. simpl in H. destruct h as [a b].
        simpl in Hedge. destruct (a =? u) as [|] eqn:Hau.
        -- simpl in Hedge. simpl in H. rewrite Hedge in H. apply H.
        -- apply H.
  - intros H. induction E as [| h t IH].
    + simpl. simpl in H. apply H.
    + simpl. destruct h as [a b]. simpl in H.
      destruct (a =? u) as [|] eqn:Hau.
      * simpl in H. simpl. destruct (b =? v) as [|] eqn:Hbv.
        -- reflexivity.
        -- apply IH. apply H.
      * simpl in H. apply IH. apply H.
Qed.

Example neighbors_of_3: neighbors_of_node 3 E = [2; 1].
Proof. reflexivity. Qed.

(* compute the neighbors of each node and append together into an adjacency list *)
Fixpoint get_adjacency_list (V: nodes) (E: edges) : adj_list :=
  match V with
  | [] => []
  | h :: t => [(h, neighbors_of_node h E)] ++ get_adjacency_list t E
  end.

Compute get_adjacency_list V E.

Theorem adjacency_list_equiv: forall V neighbors: nodes, forall E: edges, forall u v: node, 
  (neighbors = neighbors_of_node u E) ->
  ((In (u, neighbors) (get_adjacency_list V E) /\ In v neighbors) <-> (In (u, v) E /\ In u V)).
Proof.
  intros V neighbors E u v.
  intros Hneighbors.
  split.
  - intros [Hadj Hv]. split.
    -- induction V as [| h t IH].
        + simpl in Hadj. exfalso. apply Hadj.
        + simpl in Hadj. destruct Hadj as [Hadj | Hadj].
          * injection Hadj as Hhu Hnb. 
            rewrite <- Hnb in Hv. apply member_In_equiv in Hv. apply neighbors_vs_edges in Hv.
            apply member_edge_In_equiv in Hv. rewrite Hhu in Hv. apply Hv.
          * apply IH. apply Hadj.
    -- induction V as [| h t IH].
        + simpl. simpl in Hadj. apply Hadj.
        + simpl. simpl in Hadj. destruct Hadj as [Hadj | Hadj].
          * injection Hadj as Hhu Hnb. left. apply Hhu.
          * right. apply IH. apply Hadj. 
  - intros H. split.
    + induction V as [| h t IH].
      * simpl. simpl in H. destruct H as [_ H]. apply H.
      * simpl in H. destruct H as [H1 [H2 | H3]].
        -- rewrite -> H2. simpl. left. rewrite Hneighbors. reflexivity.
        -- simpl. right. apply IH. split. apply H1. apply H3.
    + destruct H as [H _]. apply member_edge_In_equiv in H. apply neighbors_vs_edges in H.
      apply member_In_equiv in H. rewrite <- Hneighbors in H. apply H.
Qed.