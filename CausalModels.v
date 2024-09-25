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
                          | h :: t => if (member h t) then False else acyclic_path t = true
                         end
  end.

Theorem acyclic_path_correct : 
  forall (p : path), 
    (acyclic_path_2 p) -> acyclic_path (((path_start p) :: (path_int p)) ++ [path_end p]) = true. 
Proof.
Admitted.


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

(* example graph *)
Definition E : edges := [(1, 2); (3, 2); (3, 1); (4, 1)].
Definition V : nodes := [1; 2; 3; 4].
Definition G : graph := (V, E).
(* TODO need to force graphs (not just paths) to have no cycles *)


(* Finding all paths in a graph *)

(* return list of 1-paths (each edge becomes two paths) *)
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

(* add p to l if p is not already in l *)
Fixpoint add_path_no_repeats (p: path) (l: paths) : paths := 
  match l with
  | [] => [p]
  | h :: t => if (eqbpath h p) then l else h :: add_path_no_repeats p t
end.

Example test_path_to_empty: add_path_no_repeats (1, 2, []) [] = [(1, 2, [])].
Proof. reflexivity. Qed.

Example test_add_new_path: 
  add_path_no_repeats (1, 2, []) [(2, 2, []); (1, 2, [3])] = [(2, 2, []); (1, 2, [3]); (1, 2, [])].
Proof. reflexivity. Qed.

Example test_add_duplicate_path:
  add_path_no_repeats (1, 2, [3]) [(1, 2, []); (1, 2, [3])] = [(1, 2, []); (1, 2, [3])].
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



(* Mediators, confounders, colliders *)

Fixpoint is_edge (e: edge) (E: edges) : bool :=
  match E with
      | [] => false
      | h :: t => match h, e with 
                   | (u1, v1), (u2, v2) => if ((u1 =? u2) && (v1 =? v2)) then true else is_edge e t
                  end
  end.

(* find all mediators, such as B in A -> B -> C. *)
Fixpoint find_mediators (u v: node) (V: nodes) (E: edges) : nodes :=
  match V with
  | [] => []
  | h :: t => if (is_edge (u, h) E && is_edge (h, v) E) then
                 h :: find_mediators u v t E
              else find_mediators u v t E
  end.


Definition is_mediator (u v med: node) (G: graph) : bool :=
  match G with
  | (V, E) => is_edge (u, med) E && is_edge (med, v) E
  end.

Example test_no_mediator: find_mediators 1 2 V E = [].
Proof. reflexivity. Qed.

Example test_not_mediator: is_mediator 1 2 3 G = false.
Proof. reflexivity. Qed.

Example test_one_mediator: find_mediators 4 2 V E = [1].
Proof. reflexivity. Qed.

Example test_is_mediator: is_mediator 4 2 1 G = true.
Proof. reflexivity. Qed.


(* find all confounders, such as B in A <- B -> C. Pass in same two sets of edges (one is for recursion) *)
Fixpoint find_confounders (u v: node) (E E_all: edges) : nodes :=
  match E with
    | [] => []
    | h :: t => match h with
                | (u', v') => if ((v' =? u) && is_edge (u', v) E_all) then u' :: find_confounders u v t E_all else find_confounders u v t E_all
                end
  end.

Definition is_confounder (u v con: node) (G: graph) : bool :=
  match G with
  | (V, E) => is_edge (con, u) E && is_edge (con, v) E
  end.

Example test_no_confounder: find_confounders 3 2 E E = [].
Proof. reflexivity. Qed.

Example test_not_confounder: is_confounder 3 2 1 G = false.
Proof. reflexivity. Qed.

Example test_one_confounder: find_confounders 2 1 E E = [3].
Proof. reflexivity. Qed.

Example test_is_confounder: is_confounder 2 1 3 G = true.
Proof. reflexivity. Qed.

(* find all colliders, such as B in A -> B <- C. Pass in same two sets of edges (one is for recursion) *)
Fixpoint find_colliders (u v: node) (E E_all: edges) : nodes :=
  match E with
    | [] => []
    | h :: t => match h with
                | (u', v') => if ((u' =? u) && is_edge (v, v') E_all) then v' :: find_colliders u v t E_all else find_colliders u v t E_all
                end
  end.

Definition is_collider (u v col: node) (G: graph) : bool :=
  match G with
  | (V, E) => is_edge (u, col) E && is_edge (v, col) E
  end.

Example test_no_collider: find_colliders 2 3 E E = [].
Proof. reflexivity. Qed.

Example test_not_collider: is_collider 2 3 1 G = false.
Proof. reflexivity. Qed.

Example test_one_collider: find_colliders 4 3 E E = [1].
Proof. simpl. reflexivity. Qed.

Example test_is_collider: is_collider 4 3 1 G = true.
Proof. reflexivity. Qed.

Theorem one_paths_of_G : forall V: nodes, forall E: edges, forall u v: node,
  member_path (u, v, []) (find_all_paths (V, E)) = true -> u <> v -> is_edge (u, v) E = true \/ is_edge (v, u) E = true.
Proof.
Admitted.

Theorem two_paths_of_G : forall V: nodes, forall E: edges, forall a b c: node, 
  member_path (a, b, [c]) (find_all_paths (V, E)) = true -> acyclic_path_2 (a, b, [c]) ->
     is_edge (a, c) E = true /\ is_edge (c, a) E = true.
Proof.
Admitted.

(* outputs true iff, for every pair of adjacent nodes in path, 
   there is an edge between those nodes in graph (in either direction) 
*)
Fixpoint is_path_in_graph (l: nodes) (G: graph) : bool :=
  match G with
  | (V, E) => match l with
              | [] => true
              | h :: t => match t with
                          | [] => member h V
                          | h' :: t' => (is_edge (h, h') E || is_edge (h', h) E) && is_path_in_graph t G
                          end
              end
  end.

Definition is_path_in_graph_2 (p: path) (G: graph) : bool :=
  match G with
  | (V, E) => match p with
              | (u, v, l) => is_path_in_graph ((u :: l) ++ [v]) G
              end
  end.


Theorem general_path_of_G : forall V: nodes, forall E: edges, forall p: path, 
  member_path p (find_all_paths G) = true <-> is_path_in_graph_2 p G = true.
Proof. Admitted.

Definition is_length_3_a_to_b (p: path) (a b: node) : bool :=
  match p with
  | (u, v, l) => (u =? a) && (v =? b) && ((length l) =? 1)
  end.

Definition extract_midpoint (p: path) (a b: node) : node := (* assumes is_length_3_a_to_b is true *)
  match p with
  | (u, v, l) => hd 0 l
  end.

Theorem length_three_path : forall G: graph, forall a b c: node,
  member_path (a, b, [c]) (find_all_paths G) = true -> 
        (is_mediator a b c G) || (is_confounder a b c G) || (is_collider a b c G) = true.
Proof. 
Admitted.

(* causal and backdoor paths *)
Definition is_causal (p: path) (E: edges) : bool :=
  match p with 
  | (u, v, l) => match l with
                | [] => is_edge (u, v) E
                | h :: t => is_edge (u, h) E
               end
  end.
  
Definition is_backdoor (p: path) (E: edges) : bool :=
  match p with 
  | (u, v, l) => match l with
                | [] => is_edge (v, u) E
                | h :: t => is_edge (h, u) E
               end
  end.

Fixpoint no_two_cycles (E: edges): bool :=
  match E with
  | [] => true
  | h :: t => match h with
                | (u, v) => if (is_edge (v, u) E) then false else no_two_cycles t
              end
  end.

Example dag: no_two_cycles E = true.
Proof. reflexivity. Qed.

Example cycle: no_two_cycles [(1, 2); (3, 2); (2, 1)] = false.
Proof. reflexivity. Qed.

Theorem causal_or_backdoor : forall P: path, forall E: edges,
  no_two_cycles E = true -> (is_causal P E = true -> is_backdoor P E = false).
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