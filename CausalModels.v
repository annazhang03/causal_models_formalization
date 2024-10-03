From FCM Require Export Helpers.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Equalities.
Import ListNotations.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.PeanoNat.




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

Theorem eqbedge_refl : forall e: edge,
  true = eqbedge e e.
Proof.
  intros e.
  destruct e as [u v]. simpl.
  rewrite -> eqb_refl. rewrite -> eqb_refl. simpl.
  reflexivity.
Qed. 

Fixpoint member_edge (e : edge) (all_edges : edges) : bool :=
  match all_edges with
      | [] => false
      | h :: t => if (eqbedge h e) then true else member_edge e t
  end.

Lemma member_edge_In_equiv : 
  forall (l : edges) (x: edge), member_edge x l = true <-> In x l.
Proof.
  intros l x.
  split.
  - intros H. induction l as [| h t IH].
    + simpl in H. discriminate H.
    + simpl in H. simpl. destruct (eqbedge h x) as [|] eqn:Hhx.
      * left. destruct h as [h1 h2]. destruct x as [x1 x2]. 
        simpl in Hhx. apply split_and_true in Hhx. destruct Hhx as [H1 H2].
        apply eqb_eq in H1. rewrite H1. apply eqb_eq in H2. rewrite H2. reflexivity.
      * right. apply IH. apply H.
  - intros H. induction l as [| h t IH].
    + simpl in H. exfalso. apply H.
    + simpl. simpl in H. destruct H as [H | H].
      * rewrite H. rewrite <- eqbedge_refl. reflexivity.
      * destruct (eqbedge h x) as [|] eqn:Hhx.
        -- reflexivity.
        -- apply IH. apply H.
Qed.

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

Fixpoint acyclic_path (p: nodes) : bool := 
  match p with 
  | [] => true
  | h :: t => if (member h t) then false else acyclic_path t
  end.

Theorem acyclic_path_intermediate_nodes :
  forall (p : nodes) (x : node), (acyclic_path p = true) -> (count x p = 0) \/ (count x p = 1).
Proof.
  intros p x Hcyc.
  induction p as [| h t IH].
  - left. reflexivity.
  - destruct (h =? x) as [|] eqn:Hhx.
    + right. simpl. rewrite Hhx. apply f_equal.
      simpl in Hcyc. destruct (member h t) as [|] eqn:Hmem.
      * discriminate Hcyc.
      * apply eqb_eq in Hhx. rewrite Hhx in Hmem. apply not_member_count_0. apply Hmem.
    + simpl. rewrite Hhx. apply IH.
      simpl in Hcyc. destruct (member h t) as [|] eqn:Hmem.
      * discriminate Hcyc.
      * apply Hcyc.
Qed.

Definition acyclic_path_2 (p: path) : Prop :=
  match p with 
  | (u, v, int) => (u <> v) /\ ~(In u int) /\ ~(In v int) /\ match int with
                          | [] => True
                          | h :: t => acyclic_path (h :: t) = true
                         end
  end.

Lemma prop_refl : forall (u: nat), u = u.
Proof.
  intros n. apply eq_refl.
Qed.

Theorem acyclic_path_correct : 
  forall (p : path), 
    (acyclic_path_2 p) -> acyclic_path ([path_start p; path_end p] ++ (path_int p)) = true. 
Proof.
  intros ((u, v), l) H.
  simpl. induction l as [| h t IH].
  - simpl. destruct (v =? u) as [|] eqn:Hvu.
    + simpl in H. destruct H as [H].
      apply eqb_neq in H. apply eqb_eq in Hvu. rewrite Hvu in H. 
      rewrite -> eqb_refl in H. discriminate H.
    + reflexivity.
  - simpl. simpl in H. simpl in IH.
    destruct (h =? u) as [|] eqn:Hhu.
    + apply eqb_eq in Hhu. destruct H as [H1 [H2 [H3 H4]]].
      unfold not in H2. exfalso. apply H2.
      left. apply Hhu.
    + destruct H as [H1 [H2 [H3 H4]]]. apply not_eq_sym in H1. apply eqb_neq in H1. 
      rewrite H1.
      destruct (member u t) as [|] eqn:Hmemu.
        * unfold not in H2.
          exfalso. apply H2. right. apply member_In_equiv. apply Hmemu.
        * rewrite H1 in IH. destruct (h =? v) as [|] eqn:Hhv.
          -- apply eqb_eq in Hhv. unfold not in H3. exfalso. apply H3.
             left. apply Hhv.
          -- destruct (member v t) as [|] eqn:Hmemv.
             ++ unfold not in H3. exfalso. apply H3. right.
                apply member_In_equiv. apply Hmemv.
             ++ apply H4.
Qed.

Definition eqbpath (p1 p2 : path) : bool := match p1, p2 with
  | (u1, v1, l1), (u2, v2, l2) => (u1 =? u2) && (v1 =? v2) && (eqblist l1 l2)
end.

Theorem eqbpath_refl : forall p: path,
  true = eqbpath p p.
Proof.
  intros p.
  destruct p as [[u v] l]. simpl.
  rewrite -> eqb_refl. rewrite -> eqb_refl. simpl.
  rewrite <- eqblist_refl.
  reflexivity.
Qed. 

Fixpoint member_path (p : path) (all_paths : paths) : bool :=
  match all_paths with
      | [] => false
      | h :: t => if (eqbpath h p) then true else member_path p t
  end.

Definition measure_path (p: path) : nat :=
  match p with
  | (u, v, l) => 2 + length l
  end.

Example length_of_2_path: measure_path (1, 2, []) = 2.
Proof. reflexivity. Qed.

Example length_of_longer_path: measure_path (1, 5, [2; 3; 4]) = 5.
Proof. reflexivity. Qed.


(* example graph *)
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

Fixpoint no_one_cycles (E: edges) : bool :=
  match E with
  | [] => true
  | h :: t => match h with
              | (a, b) => if a =? b then false else no_one_cycles t
              end
  end.

Theorem no_self_loops : forall E: edges, forall u v: node,
  member_edge (u, v) E = true -> no_one_cycles E = true -> u <> v.
Proof.
  intros E u v Hmem Hcyc.
  induction E as [| h t IH].
  - simpl in Hmem. discriminate Hmem.
  - simpl in Hmem. destruct (eqbedge h (u, v)) as [|] eqn:Hedge.
    + simpl in Hcyc. destruct (u =? v) as [|] eqn:Huv.
      * destruct h as [a b]. simpl in Hedge. apply split_and_true in Hedge.
        destruct Hedge as [Hau Hbv].
        apply eqb_eq in Huv. rewrite <- Huv in Hbv. 
        apply eqb_eq in Hbv. rewrite <-  Hbv in Hau. 
        rewrite Hau in Hcyc. discriminate Hcyc.
      * apply eqb_neq in Huv. apply Huv.
    + simpl in Hcyc. destruct (u =? v) as [|] eqn:Huv. 
      * destruct h as [a b]. simpl in Hedge. destruct (a =? b) as [|] eqn:Hab.
        -- discriminate Hcyc.
        -- apply IH. apply Hmem. apply Hcyc.
      * apply eqb_neq in Huv. apply Huv.
Qed.


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
                          | [] => member h V
                          | h' :: t' => (is_edge (h, h') G || is_edge (h', h) G) && is_path_in_graph_helper t G
                          end
              end
  end.

Definition is_path_in_graph (p: path) (G: graph) : bool :=
  match p with
  | (u, v, l) => is_path_in_graph_helper ((u :: l) ++ [v]) G
  end.


Theorem one_paths_correct : forall G: graph, forall u v: node,
  is_path_in_graph (u, v, []) G = true <-> is_edge (u, v) G = true \/ is_edge (v, u) G = true.
Proof.
  intros G u v.
  split.
  - intros Hpath.
    simpl in Hpath.
    destruct (is_edge (u, v) G) as [|] eqn:Huv.
    + left. reflexivity.
    + right. simpl in Hpath. destruct (is_edge (v, u) G) as [|] eqn:Hvu.
      * reflexivity.
      * simpl in Hpath. destruct G as [V E]. apply Hpath. 
  - intros Hedge. destruct Hedge as [Huv | Hvu].
    + simpl. rewrite Huv. simpl. destruct G as [V E].
      unfold is_edge in Huv. 
      rewrite (andb_comm (member u V) (member v V)) in Huv.
      apply andb_true_elim2 in Huv. apply andb_true_elim2 in Huv. apply Huv.
    + simpl. rewrite Hvu. rewrite (orb_comm (is_edge (u, v) G) true). simpl. destruct G as [V E].
      unfold is_edge in Hvu. apply andb_true_elim2 in Hvu. apply andb_true_elim2 in Hvu.
      apply Hvu.
Qed.

Lemma two_paths_first_edge_correct : forall G: graph, forall a b c: node, 
  is_path_in_graph (a, b, [c]) G = true -> is_edge (a, c) G = true \/ is_edge (c, a) G = true.
Proof.
  intros G a b c.
  intros Hpath.
  destruct (is_edge (a, c) G) as [|] eqn:Hac.
  - left. reflexivity.
  - right. simpl in Hpath. rewrite Hac in Hpath. destruct G as [V E]. 
    rewrite orb_false_l in Hpath. apply andb_true_elim2 in Hpath. apply Hpath.
Qed.

Lemma two_paths_second_edge_correct : forall G: graph, forall a b c: node, 
  is_path_in_graph (a, b, [c]) G = true -> is_edge (c, b) G = true \/ is_edge (b, c) G = true.
Proof.
  intros G a b c.
  intros Hpath.
  destruct (is_edge (c, b) G) as [|] eqn:Hcb.
  - left. reflexivity.
  - right. simpl in Hpath. rewrite Hcb in Hpath. destruct G as [V E].
    rewrite andb_comm in Hpath. 
    apply andb_true_elim2 in Hpath.
    apply andb_true_elim2 in Hpath.
    rewrite orb_false_l in Hpath. apply Hpath.
Qed.

Theorem two_paths_correct : forall G: graph, forall a b c: node,
  is_path_in_graph (a, b, [c]) G = true -> (is_edge (a, c) G = true \/ is_edge (c, a) G = true) /\
                                             (is_edge (c, b) G = true \/ is_edge (b, c) G = true).
Proof.
  intros G a b c.
  intros Hpath.
  split.
  - apply two_paths_first_edge_correct in Hpath. apply Hpath.
  - apply two_paths_second_edge_correct in Hpath. apply Hpath.
Qed.





(* Finding paths in a graph *)

(* add p to end of l if p is not already in l *)
Definition add_path_no_repeats (p: path) (l: paths) : paths := 
  if (member_path p l) then l else l ++ [p].

Example test_path_to_empty: add_path_no_repeats (1, 2, []) [] = [(1, 2, [])].
Proof. reflexivity. Qed.

Example test_add_new_path: 
  add_path_no_repeats (1, 2, []) [(2, 2, []); (1, 2, [3])] = [(2, 2, []); (1, 2, [3]); (1, 2, [])].
Proof. reflexivity. Qed.

Example test_add_duplicate_path:
  add_path_no_repeats (1, 2, [3]) [(1, 2, []); (1, 2, [3])] = [(1, 2, []); (1, 2, [3])].
Proof. reflexivity. Qed.


(* find paths from u to v in G *)

(* return list of 1-paths starting from u (undirected) *)
Fixpoint edges_as_paths_from_start (u: node) (E: edges) : paths :=
  match E with
  | [] => []
  | h :: t => match h with 
              | (a, b) => if (u =? a) then (a, b, []) :: edges_as_paths_from_start u t
                          else if (u =? b) then (b, a, []) :: edges_as_paths_from_start u t
                          else edges_as_paths_from_start u t
              end
  end.

Example edges_from_1: edges_as_paths_from_start 1 E = [(1, 2, []); (1, 3, []); (1, 4, [])].
Proof. reflexivity. Qed.

Example edges_from_2: edges_as_paths_from_start 2 E = [(2, 1, []); (2, 3, [])].
Proof. reflexivity. Qed.

Example edges_from_3: edges_as_paths_from_start 3 E = [(3, 2, []); (3, 1, [])].
Proof. reflexivity. Qed.

Example edges_from_4: edges_as_paths_from_start 4 E = [(4, 1, [])].
Proof. reflexivity. Qed.

(* given an edge e, grow each path in l by e if the endpoints match *)
Fixpoint extend_paths_from_start_by_edge (e : edge) (l: paths) : paths :=
  match l with
  | [] => []
  | h :: t => match h, e with
                | (u1, v1, l1), (u2, v2) =>
                      if ((u1 =? u2) || (u1 =? v2)) then h :: extend_paths_from_start_by_edge e t
                      else if (member u2 l1 || member v2 l1) then h :: extend_paths_from_start_by_edge e t
                      else if (v1 =? u2) then add_path_no_repeats (u1, v2, l1 ++ [v1]) (h :: extend_paths_from_start_by_edge e t)
                      else if (v1 =? v2) then add_path_no_repeats (u1, u2, l1 ++ [v1]) (h :: extend_paths_from_start_by_edge e t)
                      else h :: extend_paths_from_start_by_edge e t
               end
end.


Example extend_edges_from_1: extend_paths_from_start_by_edge (3, 2) [(1, 2, []); (1, 3, []); (1, 4, [])] 
  = [(1, 2, []); (1, 3, []); (1, 4, []); (1, 2, [3]); (1, 3, [2])].
Proof. reflexivity. Qed.

Example no_extend_edges_from_1: extend_paths_from_start_by_edge (3, 1) [(1, 2, []); (1, 3, []); (1, 4, [])] 
  = [(1, 2, []); (1, 3, []); (1, 4, [])].
Proof. reflexivity. Qed.

(* given a path p, add all concatenations of p with paths in l to the list of paths *)
Fixpoint extend_paths_from_start_by_edges (E : edges) (l: paths) : paths :=
  match E with
  | [] => l
  | h :: t => extend_paths_from_start_by_edges t (extend_paths_from_start_by_edge h l)
  end.

Compute extend_paths_from_start_by_edges E (edges_as_paths_from_start 1 E).

(* iteratively extend paths k times, like a for loop *)
Fixpoint extend_paths_from_start_iter (E: edges) (l: paths) (k: nat) : paths :=
  match k with
  | 0 => l
  | S k' => extend_paths_from_start_iter E (extend_paths_from_start_by_edges E l) k'
  end.

Compute extend_paths_from_start_iter E (edges_as_paths_from_start 1 E) 4.

(* determine all paths existing in the graph made up of edges E *)
Definition find_all_paths_from_start (s: node) (G: graph) : paths :=
  match G with
  | (V, E) => extend_paths_from_start_iter E (edges_as_paths_from_start s E) (length V)  
  (* each path can have at most |V| vertices *)
  end.

Compute find_all_paths_from_start 1 G.
Compute find_all_paths_from_start 2 G.
Compute find_all_paths_from_start 3 G.
Compute find_all_paths_from_start 4 G.

(* determine all paths existing in the graph made up of edges E *)
Fixpoint find_all_paths_to_end (v: node) (l: paths) : paths :=
  match l with
  | [] => []
  | h :: t => match h with 
              | (a, b, int) => if (b =? v) then h :: (find_all_paths_to_end v t) else find_all_paths_to_end v t
              end
  end.

(* determine all paths existing in the graph made up of edges E *)
Definition find_all_paths_from_start_to_end (u v: node) (G: graph) : paths :=
  find_all_paths_to_end v (find_all_paths_from_start u G).

Example paths_from_4_to_2: find_all_paths_from_start_to_end 4 2 G = [(4, 2, [1]); (4, 2, [1; 3])].
Proof. reflexivity. Qed.




(* dfs for cycle detection in directed graph G *)

(* return list of directed 1-paths (each edge becomes one 1-path) *)
Fixpoint directed_edges_as_paths (E: edges) : paths :=
  match E with
  | [] => []
  | h :: t => match h with 
              | (u, v) => (u, v, []) :: directed_edges_as_paths t
              end
  end.

Compute directed_edges_as_paths [(1, 2); (4, 3); (3, 2); (3, 4)].

(* return (bool, paths) representing whether a cycle was encountered, and the extended (acyclic) list of paths if not *)
Fixpoint dfs_extend_by_edge (e : edge) (l: paths) : bool * paths :=
  match l with
  | [] => (false, l)
  | h :: t => match h, e with
                | (u1, v1, l1), (u2, v2) =>
                      if (u2 =? v2) then (true, []) (* self loop *)
                      else if ((u2 =? v1) && (u1 =? v2)) then (true, []) (* cycle! *)
                      else if ((u2 =? v1) && (member v2 l1)) then (true, []) (* cycle inside path *)
                      else if (u2 =? v1) then let res := dfs_extend_by_edge e t in
                                              (fst res, h :: (add_path_no_repeats (u1, v2, l1 ++ [v1]) (snd res)))
                      else let res := dfs_extend_by_edge e t in
                           (fst res, h :: (snd res))
               end
end.

Compute dfs_extend_by_edge (4, 3) (directed_edges_as_paths [(1, 2); (4, 3); (3, 2); (3, 4)]).

(* for each edge, see if extending by this edge would create a cycle. 
   return (bool, paths) representing whether a cycle was encountered for any edge
   and the extended (acyclic) list of all directed paths if not *)
Fixpoint dfs_extend_by_edges (E : edges) (l: paths) : bool * paths :=
  match E with
  | [] => (false, l)
  | h :: t => let dfs := dfs_extend_by_edge h l in
              if (fst dfs) then (true, [])
              else dfs_extend_by_edges t (snd dfs)
  end.

(* iteratively extend paths k times, like a for loop, 
   ultimately returning whether the graph contains a cycle *)
Fixpoint dfs_extend_by_edges_iter (E: edges) (l: paths) (k: nat) : bool * paths :=
  match k with
  | 0 => (false, l)
  | S k' => let dfs := dfs_extend_by_edges E l in
            if (fst dfs) then (true, snd dfs)
            else dfs_extend_by_edges_iter E (snd dfs) k'
  end.

(* determine if directed graph G contains a cycle *)
Definition contains_cycle (G: graph) : bool :=
  match G with
  | (V, E) => fst (dfs_extend_by_edges_iter E (directed_edges_as_paths E) (length V))
  (* each path can have at most |V| vertices *)
  end.

Example acyclic_when_edges_directed: contains_cycle G = false.
Proof. reflexivity. Qed.

Example contains_self_loop: contains_cycle ([1; 2; 3], [(2, 3); (2, 2)]) = true.
Proof. reflexivity. Qed.

Example contains_2_cycle: contains_cycle ([1; 2; 3; 4], [(1, 2); (4, 3); (3, 2); (3, 4)]) = true.
Proof. reflexivity. Qed.

Example acyclic_larger_graph: contains_cycle G_cf = false.
Proof. reflexivity. Qed.

Example cyclic_when_edge_added: contains_cycle (V_cf, (8, 4) :: E_cf) = true.
Proof. reflexivity. Qed.

Example cyclic_when_edge_added2: contains_cycle (V_cf, (8, 1) :: E_cf) = true.
Proof. reflexivity. Qed.

Example cyclic_when_edges_added: contains_cycle (V_cf, (8, 6) :: E_cf ++ [(6, 1)]) = true.
Proof. reflexivity. Qed.

Example but_not_when_only_one_added: contains_cycle (V_cf, E_cf ++ [(6, 1)]) = false.
Proof. reflexivity. Qed.


(* find all descendants of a node *)

(* return list of directed 1-paths (each edge becomes one 1-path) starting from s *)
Fixpoint directed_edges_as_paths_from_start (s: node) (E: edges) : paths :=
  match E with
  | [] => []
  | h :: t => match h with 
              | (u, v) => if (u =? s) then (u, v, []) :: directed_edges_as_paths_from_start s t
                          else directed_edges_as_paths_from_start s t
              end
  end.

(* determine all directed paths starting from u in G *)
(* assumes that G is acyclic *)
Definition find_directed_paths_from_start (u: node) (G: graph) : paths :=
  match G with
  | (V, E) => snd (dfs_extend_by_edges_iter E (directed_edges_as_paths_from_start u E) (length V))
  (* each path can have at most |V| vertices *)
  end.

Example directed_paths_from_1: find_directed_paths_from_start 1 G = [(1, 2, [])].
Proof. reflexivity. Qed.

Example directed_paths_from_3: find_directed_paths_from_start 3 G = [(3, 2, []); (3, 1, []); (3, 2, [1])].
Proof. reflexivity. Qed.

Fixpoint get_endpoints (p: paths) : nodes :=
  match p with
  | [] => []
  | h :: t => match h with
              | (u, v, l) => let int := get_endpoints t in
                             if (member v int) then int else v :: int
              end
  end.

Definition find_descendants (s: node) (G: graph) : nodes := 
  s :: get_endpoints (find_directed_paths_from_start s G).

Example descendants_of_1: find_descendants 1 G = [1; 2].
Proof. reflexivity. Qed.

Example descendants_of_3: find_descendants 3 G = [3; 1; 2].
Proof. reflexivity. Qed.

Example descendants_of_4: find_descendants 4 G = [4; 1; 2].
Proof. reflexivity. Qed.





(* find all undirected acyclic paths in G *)

(* return list of 1-paths (each edge becomes two 1-paths) *)
Fixpoint edges_as_paths (E: edges) : paths :=
  match E with
  | [] => []
  | h :: t => match h with 
              | (u, v) => (u, v, []) :: ((v, u, []) :: edges_as_paths t)
              end
  end.

Theorem no_edges_no_paths: forall E: edges, edges_as_paths E = [] <-> E = [].
Proof.
  intros E.
  split.
  - intros H. induction E as [| h t IH].
    + reflexivity.
    + simpl in H. destruct h as [u v]. discriminate.
  - intros H. rewrite H. simpl. reflexivity. 
Qed.

Example test_edges_as_paths: edges_as_paths E = 
    (* this only works for exact order paths are added *)
    [(1, 2, []); (2, 1, []); (3, 2, []); (2, 3, []); (3, 1, []); (1, 3, []); (4, 1, []); (1, 4, [])].
Proof. reflexivity. Qed.


(* given a path p, add all concatenations of p with paths in l to the list of paths *)
Fixpoint extend_all_paths_one (p : path) (l: paths) : paths :=
  match l with
  | [] => []
  | h :: t => match p, h with
                | (u1, v1, l1), (u2, v2, l2) =>
                      let t1 := add_path_no_repeats h (extend_all_paths_one p t) in
                      if ((v1 =? u2) && (u1 =? v2)) then t1 (* cycle, don't add *)
                      else if (overlap (l1 ++ [u1;v1]) l2 || overlap l1 (l2 ++ [u2;v2])) then t1 (* contains cycle, don't add *)
                      else if (v1 =? u2) then (* p' concat h is a path from u1 to v2 *) 
                        add_path_no_repeats (u1, v2, (l1 ++ v1 :: l2)) t1
                      else if (u1 =? v2) then (* h concat p' is a path from u2 to v1 *)
                        add_path_no_repeats (u2, v1, (l2 ++ v2 :: l1)) t1
                      else t1
               end
end.

Compute extend_all_paths_one (4, 1, []) (edges_as_paths E).

(* given a list of paths l1, call extend_all_paths for each path in l1 on l2 *)
Fixpoint extend_all_paths_mul (l1: paths) (l2: paths) : paths :=
  match l1 with
  | [] => l2
  | h :: t => extend_all_paths_mul t (extend_all_paths_one h l2)
end.

(* iteratively extend paths k times, like a for loop *)
Fixpoint extend_graph_paths_iter (l: paths) (k: nat) : paths :=
  match k with
  | 0 => l
  | S k' => extend_graph_paths_iter (extend_all_paths_mul l l) k'
  end.

(* determine all paths existing in the graph made up of edges E *)
Definition find_all_paths (G: graph) : paths :=
  match G with
  | (V, E) => let edge_paths := edges_as_paths E in 
             extend_graph_paths_iter edge_paths (length V)  (* each path can have at most |V| vertices *)
  end.

Compute find_all_paths G.


Theorem general_path_of_G : forall G: graph, forall p: path, 
  member_path p (find_all_paths G) = true <-> is_path_in_graph p G = true.
Proof.
  intros G p.
  split.
  - intros Hmem. destruct p as [[u v] l]. 
    simpl. destruct l as [| h t].
    + simpl. destruct G as [V E].
Admitted.





Definition adj_list : Type := list (node * nodes).

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




(* Mediators, confounders, colliders *)
Fixpoint find_mediators_helper (u v: node) (V: nodes) (E: edges): nodes :=
  match V with
  | [] => []
  | h :: t => if (member_edge (u, h) E && member_edge (h, v) E) then
                 h :: find_mediators_helper u v t E else find_mediators_helper u v t E
  end.

(* find all mediators, such as B in A -> B -> C. *)
Definition find_mediators (u v: node) (V: nodes) (E: edges) : nodes :=
  if (member u V && member v V) 
  then find_mediators_helper u v V E
  else [].

Definition is_mediator (u v med: node) (G: graph) : Prop :=
  if (is_edge (u, med) G && is_edge (med, v) G) then True else False.

Example test_no_mediator: find_mediators 1 2 V E = [].
Proof. reflexivity. Qed.

Example test_not_mediator: ~(is_mediator 1 2 3 G).
Proof. 
  unfold not.
  intros H.
  unfold is_mediator in H. simpl in H. apply H.
Qed.

Example test_one_mediator: find_mediators 4 2 V E = [1].
Proof. reflexivity. Qed.

Example test_two_mediators: find_mediators 1 2 [1;2;3;4;5] [(1, 2); (4, 2); (3, 2); (1, 4)] = [4].
Proof. reflexivity. Qed.

Example test_is_mediator: is_mediator 4 2 1 G.
Proof. 
  unfold is_mediator. simpl. apply I.
Qed.

Fixpoint edges_correspond_to_vertices (V: nodes) (E: edges) : bool :=
  match E with
  | [] => true
  | h :: t => match h with
              | (u, v) => if (member u V && member v V) then edges_correspond_to_vertices V t else false
              end
  end.

Example test_E_corresponds_to_V : edges_correspond_to_vertices [1; 2; 3] [(1, 2); (3, 1)] = true.
Proof. reflexivity. Qed.

Example test_E_not_correspond_to_V : edges_correspond_to_vertices [1; 2; 3] [(1, 2); (3, 1); (4, 2)] = false.
Proof. reflexivity. Qed.

Lemma mediator_and_edges : forall V: nodes, forall E: edges, forall a b c: node,
  member b V = true /\ member_edge (a, b) E = true /\ member_edge (b, c) E = true <-> In b (find_mediators_helper a c V E).
Proof.
  intros V E a b c.
  split.
  { intros [H1 [H2 H3]].
  induction V as [| h t IH].
  - simpl in H1. discriminate H1.
  - simpl. destruct (h =? b) as [|] eqn:Hhb.
    + apply eqb_eq in Hhb. rewrite Hhb. rewrite H2. rewrite H3. simpl. left. reflexivity.
    + destruct (member_edge (a, h) E && member_edge (h, c) E) as [|] eqn:H.
      * simpl. right.
        apply IH. simpl in H1. rewrite Hhb in H1. apply H1.
      * apply IH. simpl in H1. rewrite Hhb in H1. apply H1. }
  { intros H.
  induction V as [| h t IH].
  - simpl in H. exfalso. apply H.
  - simpl in H. destruct (member_edge (a, h) E && member_edge (h, c) E) as [|] eqn:Hmem.
    + destruct (h =? b) as [|] eqn:Hhb.
      * apply eqb_eq in Hhb. rewrite Hhb. split.
        -- simpl. rewrite eqb_refl. reflexivity.
        -- rewrite Hhb in Hmem. split.
           ++ apply andb_true_elim2 in Hmem. apply Hmem.
           ++ rewrite andb_comm in Hmem. apply andb_true_elim2 in Hmem. apply Hmem.
      * simpl in H. destruct H as [H | H].
        -- rewrite H in Hhb. rewrite eqb_refl in Hhb. discriminate Hhb.
        -- apply IH in H. destruct H as [H1 [H2 H3]]. split.
           ++ simpl. rewrite Hhb. apply H1.
           ++ split. apply H2. apply H3.
    + apply IH in H. destruct H as [H1 [H2 H3]]. destruct (h =? b) as [|] eqn:Hhb.
      * apply eqb_eq in Hhb. rewrite Hhb. split.
        -- simpl. rewrite eqb_refl. reflexivity.
        -- split. apply H2. apply H3.
      * split. 
        -- simpl. rewrite Hhb. apply H1.
        -- split. apply H2. apply H3. }
Qed.

Lemma mediator_given_membership : forall V: nodes, forall E: edges, forall a b c: node,
  In b (find_mediators_helper a c V E) /\ member a V = true /\ member c V = true -> is_mediator a c b (V, E).
Proof.
  intros V E a b c.
  intros [H1 [Ha Hc]].
  induction V as [| h t IH].
  - simpl in Ha. discriminate Ha.
  - apply mediator_and_edges in H1. destruct H1 as [Hb [Hab Hbc]].
    unfold is_mediator. unfold is_edge. rewrite Ha. rewrite Hb. rewrite Hab. rewrite Hc. rewrite Hbc.
    simpl. apply I.
Qed.

Theorem mediator_correct : forall V: nodes, forall E: edges, forall a b c: node,
  (is_mediator a c b (V, E) <-> In b (find_mediators a c V E)). (* a -> b -> c *)
Proof.
  intros V E a b c.
  split.
  - intros Hmed.
    unfold find_mediators.
    unfold is_mediator in Hmed. 
    destruct (is_edge (a, b) (V, E) && is_edge (b, c) (V, E)) as [|] eqn:Hedges.
    + unfold is_edge in Hedges. apply split_and_true in Hedges.
      destruct Hedges as [H1 H3].
      apply split_and_true in H1. destruct H1 as [H1 Hab]. 
      apply split_and_true in H1. destruct H1 as [Ha Hb]. rewrite Ha.
      apply split_and_true in H3. destruct H3 as [Hc Hbc]. rewrite andb_comm in Hc. apply andb_true_elim2 in Hc. 
      rewrite Hc. simpl.
      apply mediator_and_edges.
      split.
      * apply Hb.
      * split. apply Hab. apply Hbc.
    + exfalso. apply Hmed.
  - intros Hmed. unfold find_mediators in Hmed. destruct (member a V && member c V) as [|] eqn:Hac.
    + apply mediator_given_membership. split.
      * apply Hmed.
      * apply split_and_true in Hac. apply Hac.
    + simpl in Hmed. exfalso. apply Hmed.
Qed.

(* find all confounders, such as B in A <- B -> C. Pass in same two sets of edges (one is for recursion) *)
Fixpoint find_confounders_helper (u v: node) (V: nodes) (E: edges): nodes :=
  match V with
  | [] => []
  | h :: t => if (member_edge (h, u) E && member_edge (h, v) E) then
                 h :: find_confounders_helper u v t E else find_confounders_helper u v t E
  end.

Definition find_confounders (u v: node) (V: nodes) (E: edges) : nodes :=
  if (member u V && member v V) 
  then find_confounders_helper u v V E
  else [].


Definition is_confounder (u v con: node) (G: graph) : Prop :=
  match G with
  | (V, E) => if (is_edge (con, u) G && is_edge (con, v) G) then True else False
  end.

Example test_no_confounder: find_confounders 3 2 V E = [].
Proof. reflexivity. Qed.

Example test_not_confounder: ~(is_confounder 3 2 1 G).
Proof.
  unfold not.
  unfold is_confounder. 
  simpl.
  easy.
Qed.

Example test_one_confounder: find_confounders 2 1 V E = [3].
Proof. reflexivity. Qed.

Example test_is_confounder: is_confounder 2 1 3 G.
Proof.
  unfold is_confounder.
  simpl.
  apply I.
Qed.

Lemma confounder_and_edges : forall V: nodes, forall E: edges, forall a b c: node,
  member b V = true /\ member_edge (b, a) E = true /\ member_edge (b, c) E = true <-> In b (find_confounders_helper a c V E).
Proof.
  intros V E a b c.
  split.
  { intros [H1 [H2 H3]].
  induction V as [| h t IH].
  - simpl in H1. discriminate H1.
  - simpl. destruct (h =? b) as [|] eqn:Hhb.
    + apply eqb_eq in Hhb. rewrite Hhb. rewrite H2. rewrite H3. simpl. left. reflexivity.
    + destruct (member_edge (h, a) E && member_edge (h, c) E) as [|] eqn:H.
      * simpl. right.
        apply IH. simpl in H1. rewrite Hhb in H1. apply H1.
      * apply IH. simpl in H1. rewrite Hhb in H1. apply H1. }
  { intros H.
  induction V as [| h t IH].
  - simpl in H. exfalso. apply H.
  - simpl in H. destruct (member_edge (h, a) E && member_edge (h, c) E) as [|] eqn:Hcon.
    + destruct (h =? b) as [|] eqn:Hhb.
      * apply eqb_eq in Hhb. rewrite Hhb. split.
        -- simpl. rewrite eqb_refl. reflexivity.
        -- rewrite Hhb in Hcon. split.
           ++ apply andb_true_elim2 in Hcon. apply Hcon.
           ++ rewrite andb_comm in Hcon. apply andb_true_elim2 in Hcon. apply Hcon.
      * simpl in H. destruct H as [H | H].
        -- rewrite H in Hhb. rewrite eqb_refl in Hhb. discriminate Hhb.
        -- apply IH in H. destruct H as [H1 [H2 H3]]. split.
           ++ simpl. rewrite Hhb. apply H1.
           ++ split. apply H2. apply H3.
    + apply IH in H. destruct H as [H1 [H2 H3]]. destruct (h =? b) as [|] eqn:Hhb.
      * apply eqb_eq in Hhb. rewrite Hhb. split.
        -- simpl. rewrite eqb_refl. reflexivity.
        -- split. apply H2. apply H3.
      * split. 
        -- simpl. rewrite Hhb. apply H1.
        -- split. apply H2. apply H3. }
Qed.

Lemma confounder_given_membership : forall V: nodes, forall E: edges, forall a b c: node,
  In b (find_confounders_helper a c V E) /\ member a V = true /\ member c V = true -> is_confounder a c b (V, E).
Proof.
  intros V E a b c.
  intros [H1 [Ha Hc]].
  induction V as [| h t IH].
  - simpl in Ha. discriminate Ha.
  - apply confounder_and_edges in H1. destruct H1 as [Hb [Hba Hbc]].
    unfold is_confounder. unfold is_edge. rewrite Ha. rewrite Hb. rewrite Hba. rewrite Hc. rewrite Hbc.
    simpl. apply I.
Qed.


Theorem confounder_correct : forall V: nodes, forall E: edges, forall a b c: node,
  (is_confounder a c b (V, E) <-> In b (find_confounders a c V E)). (* a <- b -> c *)
Proof.
  intros V E a b c.
  split.
  - intros Hcon.
    unfold find_confounders.
    unfold is_confounder in Hcon. 
    destruct (is_edge (b, a) (V, E) && is_edge (b, c) (V, E)) as [|] eqn:Hedges.
    + unfold is_edge in Hedges. apply split_and_true in Hedges.
      destruct Hedges as [H1 H3].
      apply split_and_true in H1. destruct H1 as [H1 Hba]. 
      apply split_and_true in H1. destruct H1 as [Hb Ha]. rewrite Ha.
      apply split_and_true in H3. destruct H3 as [Hc Hbc]. rewrite andb_comm in Hc. apply andb_true_elim2 in Hc. 
      rewrite Hc. simpl.
      apply confounder_and_edges.
      split.
      * apply Hb.
      * split. apply Hba. apply Hbc.
    + exfalso. apply Hcon.
  - intros Hcon. unfold find_confounders in Hcon. destruct (member a V && member c V) as [|] eqn:Hac.
    + apply confounder_given_membership. split.
      * apply Hcon.
      * apply split_and_true in Hac. apply Hac.
    + simpl in Hcon. exfalso. apply Hcon.
Qed.


(* find all colliders, such as B in A -> B <- C. *)
Fixpoint find_colliders_helper (u v: node) (V: nodes) (E: edges): nodes :=
  match V with
  | [] => []
  | h :: t => if (member_edge (u, h) E && member_edge (v, h) E) then
                 h :: find_colliders_helper u v t E else find_colliders_helper u v t E
  end.

Definition find_colliders (u v: node) (V: nodes) (E: edges) : nodes :=
  if (member u V && member v V) 
  then find_colliders_helper u v V E
  else [].

Definition is_collider (u v col: node) (G: graph) : Prop :=
  match G with
  | (V, E) => if (is_edge (u, col) G && is_edge (v, col) G) then True else False
  end.

Example test_no_collider: find_colliders 2 3 V E = [].
Proof. reflexivity. Qed.

Example test_not_collider: ~(is_collider 2 3 1 G).
Proof.
  unfold not.
  unfold is_collider.
  simpl.
  easy.
Qed.

Example test_one_collider: find_colliders 4 3 V E = [1].
Proof. simpl. reflexivity. Qed.

Example test_is_collider: is_collider 4 3 1 G.
Proof.
  unfold is_collider.
  simpl.
  apply I.
Qed.

Lemma collider_and_edges : forall V: nodes, forall E: edges, forall a b c: node,
  member b V = true /\ member_edge (a, b) E = true /\ member_edge (c, b) E = true <-> In b (find_colliders_helper a c V E).
Proof.
  intros V E a b c.
  split.
  { intros [H1 [H2 H3]].
  induction V as [| h t IH].
  - simpl in H1. discriminate H1.
  - simpl. destruct (h =? b) as [|] eqn:Hhb.
    + apply eqb_eq in Hhb. rewrite Hhb. rewrite H2. rewrite H3. simpl. left. reflexivity.
    + destruct (member_edge (a, h) E && member_edge (c, h) E) as [|] eqn:H.
      * simpl. right.
        apply IH. simpl in H1. rewrite Hhb in H1. apply H1.
      * apply IH. simpl in H1. rewrite Hhb in H1. apply H1. }
  { intros H.
  induction V as [| h t IH].
  - simpl in H. exfalso. apply H.
  - simpl in H. destruct (member_edge (a, h) E && member_edge (c, h) E) as [|] eqn:Hcol.
    + destruct (h =? b) as [|] eqn:Hhb.
      * apply eqb_eq in Hhb. rewrite Hhb. split.
        -- simpl. rewrite eqb_refl. reflexivity.
        -- rewrite Hhb in Hcol. split.
           ++ apply andb_true_elim2 in Hcol. apply Hcol.
           ++ rewrite andb_comm in Hcol. apply andb_true_elim2 in Hcol. apply Hcol.
      * simpl in H. destruct H as [H | H].
        -- rewrite H in Hhb. rewrite eqb_refl in Hhb. discriminate Hhb.
        -- apply IH in H. destruct H as [H1 [H2 H3]]. split.
           ++ simpl. rewrite Hhb. apply H1.
           ++ split. apply H2. apply H3.
    + apply IH in H. destruct H as [H1 [H2 H3]]. destruct (h =? b) as [|] eqn:Hhb.
      * apply eqb_eq in Hhb. rewrite Hhb. split.
        -- simpl. rewrite eqb_refl. reflexivity.
        -- split. apply H2. apply H3.
      * split. 
        -- simpl. rewrite Hhb. apply H1.
        -- split. apply H2. apply H3. }
Qed.

Lemma collider_given_membership : forall V: nodes, forall E: edges, forall a b c: node,
  In b (find_colliders_helper a c V E) /\ member a V = true /\ member c V = true -> is_collider a c b (V, E).
Proof.
  intros V E a b c.
  intros [H1 [Ha Hc]].
  induction V as [| h t IH].
  - simpl in Ha. discriminate Ha.
  - apply collider_and_edges in H1. destruct H1 as [Hb [Hab Hcb]].
    unfold is_collider. unfold is_edge. rewrite Ha. rewrite Hb. rewrite Hab. rewrite Hc. rewrite Hcb.
    simpl. apply I.
Qed.


Theorem collider_correct : forall V: nodes, forall E: edges, forall a b c: node,
  (is_collider a c b (V, E) <-> In b (find_colliders a c V E)). (* a -> b <- c *)
Proof.
  intros V E a b c.
  split.
  - intros Hcol.
    unfold find_colliders.
    unfold is_collider in Hcol. 
    destruct (is_edge (a, b) (V, E) && is_edge (c, b) (V, E)) as [|] eqn:Hedges.
    + unfold is_edge in Hedges. apply split_and_true in Hedges.
      destruct Hedges as [H1 H3].
      apply split_and_true in H1. destruct H1 as [H1 Hab]. 
      apply split_and_true in H1. destruct H1 as [Ha Hb]. rewrite Ha.
      apply split_and_true in H3. destruct H3 as [Hc Hcb]. apply andb_true_elim2 in Hc. 
      rewrite Hc. simpl.
      apply collider_and_edges.
      split.
      * apply Hb.
      * split. apply Hab. apply Hcb.
    + exfalso. apply Hcol.
  - intros Hcol. unfold find_colliders in Hcol. destruct (member a V && member c V) as [|] eqn:Hac.
    + apply collider_given_membership. split.
      * apply Hcol.
      * apply split_and_true in Hac. apply Hac.
    + simpl in Hcol. exfalso. apply Hcol.
Qed.

Theorem middle_node_in_two_path : forall G: graph, forall a b c: node,
  is_path_in_graph (a, b, [c]) G = true -> 
        (is_mediator a b c G) \/ (is_mediator b a c G) \/ (is_confounder a b c G) \/ (is_collider a b c G).
Proof. 
  intros G a b c.
  intros Hpath.
  apply two_paths_correct in Hpath.
  destruct Hpath as [[Hac | Hca] [Hcb | Hbc]].
  - left. unfold is_mediator. rewrite Hac. rewrite Hcb. simpl. apply I.
  - right. right. right. unfold is_collider. rewrite Hac. rewrite Hbc. simpl. destruct G as [V E]. apply I.
  - right. right. left. unfold is_confounder. rewrite Hca. rewrite Hcb. simpl. destruct G as [V E]. apply I.
  - right. left. unfold is_mediator. rewrite Hca. rewrite Hbc. simpl. apply I.
Qed. 

(* causal and backdoor paths *)
Definition is_causal (p: path) (G: graph) : bool :=
  match p with 
  | (u, v, l) => match l with
                | [] => is_edge (u, v) G
                | h :: t => is_edge (u, h) G
               end
  end.
  
Definition is_backdoor (p: path) (G: graph) : bool :=
  match p with 
  | (u, v, l) => match l with
                | [] => is_edge (v, u) G
                | h :: t => is_edge (h, u) G
               end
  end.

Fixpoint no_two_cycles (V: nodes) (E: edges): bool :=
  match E with
  | [] => true
  | h :: t => match h with
                | (u, v) => if (is_edge (v, u) (V, E)) then false else no_two_cycles V t
              end
  end.

Example dag: no_two_cycles V E = true.
Proof. reflexivity. Qed.

Example cycle: no_two_cycles [1; 2; 3; 4] [(1, 2); (3, 2); (2, 1)] = false.
Proof. reflexivity. Qed.

Theorem causal_or_backdoor : forall p: path, forall V: nodes, forall E: edges,
  no_two_cycles V E = true -> (is_causal p (V, E) = true -> is_backdoor p (V, E) = false).
Proof.
  (* intros P E.
  intros H2c Hcaus.
  destruct P as [u v l]. simpl.
  destruct l as [| h t].
  - reflexivity.
  - simpl in Hcaus. 
    induction E as [| h' t' IH].
    + reflexivity.
    + simpl. destruct h' as [u1 v1]. destruct ((u1 =? h) && (v1 =? u)) as [|] eqn:E1.
      * simpl in Hcaus. destruct ((u1 =? u) && (v1 =? h)) as [|] eqn:E2.
        ++ simpl in H2c. assert (Heq: (u1 =? v1) && (v1 =? u1) = true).
           { replace (h) with v1 in E1. replace (u) with u1 in E1.
             -- apply E1.
             -- rewrite andb_commutative in E2. apply andb_true_elim2 with (b:=v1 =? h) in E2. apply eqb_eq in E2. apply E2.
             -- apply andb_true_elim2 with (b:=u1 =? u) in E2. apply eqb_eq in E2. apply E2. }
           rewrite Heq in H2c. discriminate.
        ++ simpl in H2c. assert (Heq: (u1 =? v1) && (v1 =? u1) = false).
           { replace (u) with v1 in E2. replace (h) with u1 in E2.
             -- apply E2.
             -- rewrite andb_commutative in E1. apply andb_true_elim2 with (b:=v1 =? u) in E1. apply eqb_eq in E1. apply E1.
             -- apply andb_true_elim2 with (b:=u1 =? h) in E1. apply eqb_eq in E1. apply E1. }
           rewrite Heq in H2c. replace (u) with v1 in Hcaus. replace (h) with u1 in Hcaus.
           -- rewrite Hcaus in H2c. discriminate.
           -- rewrite andb_commutative in E1. apply andb_true_elim2 with (b:=v1 =? u) in E1. apply eqb_eq in E1. apply E1.
           -- apply andb_true_elim2 with (b:=u1 =? h) in E1. apply eqb_eq in E1. apply E1.
     * simpl in Hcaus. simpl in H2c.   *)
Admitted.




(* Conditional independence *)

(* p contains chain A -> B -> C, where B in Z (the conditioning set) *)
Program Fixpoint is_blocked_by_mediator (p: path) (G: graph) (Z: nodes) {measure (measure_path p)} : Prop :=
  match p with 
  | (u, v, []) => False
  | (u, v, h :: []) => is_mediator u v h G /\ In h Z
  | (u, v, h :: (h1 :: t)) => (is_mediator u h1 h G /\ In h Z) \/ is_blocked_by_mediator (h, v, h1 :: t) G Z
  end.

Example mediator_in_conditioning_set: is_blocked_by_mediator (1, 3, [2]) ([1; 2; 3], [(1, 2); (2, 3)]) [2].
Proof.
  cbn. split. 
  - apply I. 
  - left. reflexivity.
Qed.

Example mediator_not_in_conditioning_set: ~(is_blocked_by_mediator (1, 3, [2]) ([1; 2; 3], [(1, 2); (2, 3)]) []).
Proof.
  unfold not. intros H. cbn in H. destruct H as [_ contra]. apply contra.
Qed.

Example mediator_in_longer_path: is_blocked_by_mediator (1, 4, [2; 3]) ([1; 2; 3; 4], [(2, 1); (2, 3); (3, 4)]) [3].
Proof. 
  cbn. right. split.
  - apply I.
  - left. reflexivity.
Qed.

(* p contains fork A <- B -> C, where B in Z (the conditioning set) *)
Program Fixpoint is_blocked_by_confounder (p: path) (G: graph) (Z: nodes) {measure (measure_path p)} : Prop :=
  match p with 
  | (u, v, []) => False
  | (u, v, h :: []) => is_confounder u v h G /\ In h Z
  | (u, v, h :: (h1 :: t)) => (is_confounder u h1 h G /\ In h Z) \/ is_blocked_by_confounder (h, v, h1 :: t) G Z
  end.

Example confounder_in_conditioning_set: is_blocked_by_confounder (1, 3, [2]) ([1; 2; 3], [(2, 1); (2, 3)]) [2].
Proof.
  cbn. split. 
  - apply I. 
  - left. reflexivity.
Qed.

Example confounder_not_in_conditioning_set: ~(is_blocked_by_confounder (1, 3, [2]) ([1; 2; 3], [(2, 1); (2, 3)]) []).
Proof.
  unfold not. intros H. cbn in H. destruct H as [_ contra]. apply contra.
Qed.

Example confounder_in_longer_path: is_blocked_by_confounder (1, 4, [2; 3]) ([1; 2; 3; 4], [(2, 1); (2, 3); (3, 4)]) [2].
Proof. 
  cbn. left. split.
  - apply I.
  - left. reflexivity.
Qed.

Fixpoint descendants_not_in_Z (d: nodes) (Z: nodes) : Prop :=
  match d with
  | [] => True
  | h :: t => ~(In h Z) /\ descendants_not_in_Z t Z
  end.

(* p contains collision A -> B <- C, where B and descendants are not in Z (the conditioning set) *)
Program Fixpoint is_blocked_by_collider (p: path) (G: graph) (Z: nodes) {measure (measure_path p)} : Prop :=
  match p with 
  | (u, v, []) => False
  | (u, v, h :: []) => is_collider u v h G /\ descendants_not_in_Z (find_descendants h G) Z
  | (u, v, h :: (h1 :: t)) => (is_collider u h1 h G /\ descendants_not_in_Z (find_descendants h G) Z)
                              \/ is_blocked_by_collider (h, v, h1 :: t) G Z
  end.


Example collider_in_conditioning_set: ~(is_blocked_by_collider (1, 3, [2]) ([1; 2; 3], [(1, 2); (3, 2)]) [2]).
Proof. 
  unfold not. intros H. 
  cbn in H. destruct H as [_ [Hcontra _]]. unfold not in Hcontra. 
  apply Hcontra. left. reflexivity.
Qed.

Example collider_not_in_conditioning_set: is_blocked_by_collider (1, 3, [2]) ([1; 2; 3], [(1, 2); (3, 2)]) [].
Proof. 
  cbn. split.
  - apply I.
  - split.
    + unfold not. intros Hfalse. apply Hfalse.
    + apply I.
Qed.

Example descendant_in_conditioning_set: ~(is_blocked_by_collider (1, 3, [2]) ([1; 2; 3; 4], [(1, 2); (3, 2); (2, 4)]) [4]).
Proof. 
  unfold not. intros H. 
  cbn in H. destruct H as [_ [_ [Hcontra _]]]. unfold not in Hcontra. 
  apply Hcontra. left. reflexivity.
Qed.

Example collider_in_longer_path: is_blocked_by_collider (1, 4, [2; 3]) ([1; 2; 3; 4], [(1, 2); (3, 2); (3, 4)]) [].
Proof. 
  cbn. left. split. 
  - apply I.
  - split.
    + unfold not. intros Hfalse. apply Hfalse.
    + apply I.
Qed.

Definition path_is_blocked (p: path) (G: graph) (Z: nodes) : Prop :=
  is_blocked_by_mediator p G Z \/ is_blocked_by_confounder p G Z \/ is_blocked_by_collider p G Z.

Example collider_no_conditioning_needed: path_is_blocked (5, 8, [6; 7]) G_d [].
Proof.
  compute. right. right. left. tauto.
Qed.


(* conditioning on W unblocks the path from Z to Y *)
Example condition_on_collider: ~(path_is_blocked (5, 8, [6; 7]) G_d [6]).
Proof.
  unfold not. intros H. compute in H. destruct H as [H | [H | [H | H]]].
  - destruct H as [[H _] | [H _]]. apply H. apply H.
  - destruct H as [[H _] | [_ H]]. apply H. destruct H as [H | H]. 
    + discriminate H.
    + apply H.
  - destruct H as [_ [H _]]. apply H. left. reflexivity.
  - destruct H as [H _]. apply H.
Qed.

(* conditioning on U (a descendant of W) unblocks the path from Z to Y *)
Example condition_on_descendant_collider: ~(path_is_blocked (5, 8, [6; 7]) G_d [10]).
Proof.
  unfold not. intros H. compute in H. destruct H as [H | [H | [H | H]]].
  - destruct H as [[H _] | [H _]]. apply H. apply H.
  - destruct H as [[H _] | [_ H]]. apply H. destruct H as [H | H]. 
    + discriminate H.
    + apply H.
  - destruct H as [_ [_ [H _]]]. apply H. left. reflexivity.
  - destruct H as [H _]. apply H.
Qed.

(* conditioning on X blocks the path from Z to Y, even if W unblocks it *)
Example condition_on_collider_and_mediator: path_is_blocked (5, 8, [6; 7]) G_d [6; 7].
Proof.
  compute. tauto.
Qed.

Fixpoint paths_all_blocked (p: paths) (G: graph) (Z: nodes) : Prop :=
  match p with
  | [] => True
  | h :: t => path_is_blocked h G Z /\ paths_all_blocked t G Z
  end.

(* determine whether u and v are independent in G conditional on the nodes in Z *)
Definition d_separated (u v: node) (G: graph) (Z: nodes) : Prop :=
  paths_all_blocked (find_all_paths_from_start_to_end u v G) G Z.

(* Z to Y are unconditionally independent due to collider at W *)
Example unconditionally_independent: d_separated 5 8 G_d [].
Proof.
  compute. tauto.
Qed.

(* conditioning on W unblocks the path from Z to Y *)
Example conditionally_dependent: ~(d_separated 5 8 G_d [6]).
Proof.
  compute. intros H. destruct H as [[H | H] _].
  - destruct H as [[H _] | [H _]]. apply H. apply H.
  - destruct H as [H | H].
    + destruct H as [[H _] | [_ H]]. apply H. destruct H as [H | H]. discriminate H. apply H. 
    + destruct H as [H | H].
      * destruct H as [_ [H _]]. apply H. left. reflexivity.
      * destruct H as [H _]. apply H.
Qed.

(* based on figure 2.8 of primer *)
(* conditioning on nothing leaves the path Z <- T -> Y open *)
Example unconditionally_dependent: ~(d_separated 5 8 (V_d ++ [11; 12], E_d ++ [(11, 5); (11, 8); (12, 11)]) []).
Proof.
  unfold not. compute. tauto.
Qed.

(* conditioning on T blocks the second path from Z to Y *)
Example conditionally_independent: d_separated 5 8 (V_d ++ [11; 12], E_d ++ [(11, 5); (11, 8); (12, 11)]) [11].
Proof.
  compute. split.
  - right. right. left. split.
    + apply I.
    + split.
      * intros H. destruct H as [H | H]. discriminate H. apply H.
      * split.
        -- intros H. destruct H as [H | H]. discriminate H. apply H.
        -- apply I.
  - split.
    + right. left. split. apply I. left. reflexivity.
    + apply I.
Qed.

(* conditioning on T and W unblocks the path Z -> W <- X -> Y *)
Example condition_on_T_W : ~(d_separated 5 8 (V_d ++ [11; 12], E_d ++ [(11, 5); (11, 8); (12, 11)]) [11; 6]).
Proof.
  compute. intros H. destruct H as [Hpath1 [Hpath2 _]].
  destruct Hpath1 as [Hm | [Hcf | Hcl]].
  - destruct Hm as [[contra _] | [contra _]]. apply contra. apply contra.
  - destruct Hcf as [[contra _] | [_ contra]]. apply contra. 
    destruct contra as [contra | [contra | contra]].
    discriminate contra. discriminate contra. apply contra.
  - destruct Hcl as [[_ [contra _]] | [contra _]].
    + apply contra. right. left. reflexivity.
    + apply contra.
Qed.

(* conditioning on X closes the path Z -> W <- X -> Y *)
Example condition_on_T_W_X : d_separated 5 8 (V_d ++ [11; 12], E_d ++ [(11, 5); (11, 8); (12, 11)]) [11; 6; 7].
Proof.
  compute. tauto.
Qed.
