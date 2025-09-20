From FCM Require Export Helpers.

From Coq Require Export Init.Nat.
From Coq Require Export Lists.List.
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.PeanoNat.
Require Import Coq.Program.Wf.

Import ListNotations.

(* Representation of a causal model (nodes, edges) *)

Definition node : Type := nat.
Check 1 : node.
Definition nodes := list node.

Definition edge : Type := node * node.
Check (1, 2) : edge.
Definition edges := list edge.

Definition graph : Type := nodes * edges.

Definition path : Type := node * node * nodes. (* start node, end node, [list of intermediate nodes] *)
Check (4, 5, [1;2;3]) : path.
Definition paths := list path.

Definition eqbedge (e1 e2 : edge) : bool := match e1, e2 with
  | (u1, v1), (u2, v2) => (u1 =? u2) && (v1 =? v2)
end.

Fixpoint member_edge (e : edge) (all_edges : edges) : bool :=
  match all_edges with
      | [] => false
      | h :: t => (eqbedge h e) || (member_edge e t)
  end.

Definition path_start (p: path) : node :=
  match p with
  | (u, v, l) => u
  end.

Definition path_end (p: path) : node :=
  match p with
  | (u, v, l) => v
  end.

Definition path_int (p: path) : nodes :=
  match p with
  | (u, v, l) => l
  end.

Definition path_length (p: path) := 2 + length (path_int p).

Definition path_start_and_end (U: path) (A B: node) : bool :=
  ((path_start U) =? A) && ((path_end U) =? B).


Definition node_in_path (X: node) (U: path) : bool :=
  (X =? (path_start U)) || (X =? (path_end U)) || (member X (path_int U)).



Definition concat (u1 mid v2: node) (l1 l2: nodes) : path :=
  (u1, v2, l1 ++ (mid :: l2)).

Example concat_two_paths: concat 1 3 6 [2] [4;5] = (1, 6, [2;3;4;5]).
Proof. reflexivity. Qed.

Fixpoint acyclic_path (p: nodes) : bool :=
  match p with
  | [] => true
  | h :: t => (negb (member h t)) && (acyclic_path t)
  end.


Definition acyclic_path_2 (p: path) : Prop :=
  match p with
  | (u, v, int) => (u <> v) /\ ~(In u int) /\ ~(In v int) /\ match int with
                          | [] => True
                          | h :: t => acyclic_path (h :: t) = true
                         end
  end.



Definition eqbpath (p1 p2 : path) : bool := match p1, p2 with
  | (u1, v1, l1), (u2, v2, l2) => (u1 =? u2) && (v1 =? v2) && (eqblist l1 l2)
end.


Fixpoint member_path (p : path) (all_paths : paths) : bool :=
  match all_paths with
      | [] => false
      | h :: t => if (eqbpath h p) then true else member_path p t
  end.

Fixpoint count_path (p : path) (all_paths : paths) : nat :=
  match all_paths with
      | [] => 0
      | h :: t => if (eqbpath h p) then S (count_path p t) else count_path p t
  end.

Definition measure_path (p: path) : nat :=
  match p with
  | (u, v, l) => 2 + length l
  end.

Example length_of_2_path: measure_path (1, 2, []) = 2.
Proof. reflexivity. Qed.

Example length_of_longer_path: measure_path (1, 5, [2; 3; 4]) = 5.
Proof. reflexivity. Qed.

Fixpoint count_edge (e : edge) (E : edges) : nat :=
  match E with
      | [] => 0
      | h :: t => if (eqbedge h e) then S (count_edge e t) else count_edge e t
  end.




Definition G_well_formed (G: graph) : bool :=
  match G with
  | (V, E) => forallb (fun e => match e with
                                | (u, v) => member u V && member v V end) E
              && forallb (fun v => count v V =? 1) V
              && forallb (fun e => count_edge e E =? 1) E
  end.

Definition node_in_graph (u: node) (G: graph) : bool :=
  match G with
  | (V, E) => member u V
  end.

Definition max_node_in_graph (G: graph) : node :=
  match G with
  | (V, E) => max_list V
  end.

Definition nodes_in_graph (G: graph) : nodes :=
  match G with
  | (V, E) => V
  end.

Definition edges_in_graph (G: graph) : edges :=
  match G with
  | (V, E) => E
  end.

Definition edge_in_graph (e: edge) (G: graph) : bool :=
  match G with
  | (V, E) => member_edge e E
  end.

Definition remove_associated_edges (u: node) (E: edges) : edges :=
  filter (fun edg => negb (snd edg =? u) && negb (fst edg =? u)) E.

Definition remove_node (u: node) (V: nodes) : nodes :=
  filter (fun v => negb (v =? u) ) V.


Definition remove_node_from_graph (G: graph) (u: node) : graph :=
  match G with
  | (V, E) => (remove_node u V, remove_associated_edges u E)
  end.


Definition num_nodes (G: graph) : nat :=
  match G with
  | (V, E) => length V
  end.


(* example graphs *)
Definition E : edges := [(1, 2); (3, 2); (3, 1); (4, 1)].
Definition V : nodes := [1; 2; 3; 4].
Definition G : graph := (V, E).

(* example coin flip graph (Figure 2.4 of primer) *)
Definition V_cf : nodes := [1; 2; 3; 4; 5; 6; 7; 8]. (* UX, UZ, UY, X, Z, Y, UW, W *)
Definition E_cf : edges := [(1, 4); (4, 5); (2, 5); (3, 6); (6, 5); (5, 8); (7, 8)].
Definition G_cf : graph := (V_cf, E_cf).

(* example graph (Figure 2.7 of primer) *)
Definition V_d : nodes := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]. (* UZ UW UX UY Z W X Y UU U *)
Definition E_d : edges := [(1, 5); (5, 6); (2, 6); (7, 6); (3, 7); (4, 8); (7, 8); (6, 10); (9, 10)].
Definition G_d : graph := (V_d, E_d).

Definition G_d_modified : graph := (V_d ++ [11; 12], E_d ++ [(11, 5); (11, 8); (12, 11)]).

(* temperature (Z=5), ice cream sales (X=4), and crime rates (Y=6), Figure 3.1 of primer *)
Definition V_temp : nodes := [1; 2; 3; 4; 5; 6].
Definition E_temp : edges := [(1, 4); (2, 5); (3, 6); (5, 4); (5, 6)].
Definition G_temp : graph := (V_temp, E_temp).

(* new drug (X=1), recovery (Y=2), weight (W=3), socioeconomic status (unmeasured, Z=4), Fig 3.6 *)
Definition V_drug : nodes := [1; 2; 3; 4].
Definition E_drug : edges := [(1, 2); (3, 2); (4, 1); (4, 3)].
Definition G_drug : graph := (V_drug, E_drug).

Definition vertex_subset (S: nodes) (G: graph) : bool :=
  match G with
  | (V, E) => subset S V
  end.

Fixpoint no_one_cycles (E: edges) : bool :=
  match E with
  | [] => true
  | h :: t => match h with
              | (a, b) => if a =? b then false else no_one_cycles t
              end
  end.

(* determine if edges/paths are in a graph G *)
Definition is_edge (e: edge) (G: graph) : bool :=
  match G with
  | (V, E) => match e with
              | (u, v) => member u V && member v V && member_edge (u, v) E
              end
  end.

Example test_is_edge_true : is_edge (3, 1) G = true.
Proof. reflexivity. Qed.

Example test_is_edge_false_reverse : is_edge (1, 3) G = false.
Proof. reflexivity. Qed.

Example test_is_edge_false : is_edge (4, 3) G = false.
Proof. reflexivity. Qed.

Example test_is_edge_false_node : is_edge (5, 3) G = false.
Proof. reflexivity. Qed.



(* outputs true iff, for every pair of adjacent nodes in path,
   there is an edge between those nodes in graph (in either direction) *)
Fixpoint is_path_in_graph_helper (l: nodes) (G: graph) : bool :=
  match G with
  | (V, E) => match l with
              | [] => true
              | h :: t => match t with
                          | [] => true
                          | h' :: t' => (is_edge (h, h') G || is_edge (h', h) G) && is_path_in_graph_helper t G
                          end
              end
  end.


Definition is_path_in_graph (p: path) (G: graph) : bool :=
  match p with
  | (u, v, l) => is_path_in_graph_helper ((u :: l) ++ [v]) G
  end.


Example path_in_graph: is_path_in_graph (2, 4, [1]) G = true.
Proof. reflexivity. Qed.

Example path_not_in_graph: is_path_in_graph (2, 4, [5]) G = false.
Proof. reflexivity. Qed.

(* outputs true iff, for every pair of adjacent nodes in path,
   there is an edge between those nodes in the given order in graph *)
Fixpoint is_dir_path_in_graph_helper (l: nodes) (G: graph) : bool :=
  match l with
  | [] => true
  | h :: t => match t with
              | [] => true
              | h' :: t' => is_edge (h, h') G && is_dir_path_in_graph_helper t G
              end
  end.


Definition is_directed_path_in_graph (p: path) (G: graph) : bool :=
  match p with
  | (u, v, l) => is_dir_path_in_graph_helper ((u :: l) ++ [v]) G
  end.

Example dir_path_in_graph: is_directed_path_in_graph (3, 2, [1]) G = true.
Proof. reflexivity. Qed.

Example dir_path_not_in_graph: is_directed_path_in_graph (2, 4, [1]) G = false.
Proof. reflexivity. Qed.



Program Fixpoint is_path_in_graph_2 (p: path) (G: graph) {measure (measure_path p)} : bool :=
  match G with
  | (V, E) => match p with
              | (u, v, []) => is_edge (u, v) G || is_edge (v, u) G
              | (u, v, h :: t) => ((is_edge (u, h) G) || (is_edge (h, u) G)) && is_path_in_graph_2 (h, v, t) G
              end
  end.
