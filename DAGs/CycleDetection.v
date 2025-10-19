From DAGs Require Import Basics.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.

From Coq Require Import Classical.
Import ListNotations.

(* this file provides functions and correctness theorems for cycle detection
   within a directed graph by performing DFS in a manner similar to in DAG_PathFinding *)


(* return list of directed 1-paths from a list of edges
   e.g. each edge (a,b) becomes 1-path a->b, or (a, b, []) *)
Fixpoint directed_edges_as_paths (E: edges) : paths :=
  match E with
  | [] => []
  | h :: t => match h with
              | (u, v) => (u, v, []) :: directed_edges_as_paths t
              end
  end.

Compute directed_edges_as_paths [(1, 2); (4, 3); (3, 2); (3, 4)].


(* return a tuple (bool, paths). the first element represents whether a cycle was encountered.
   if false, then the second element contains the extended (acyclic) list of paths after attempting
   to extend paths in l by e *)
Fixpoint dfs_extend_by_edge (e : edge) (l: paths) : bool * paths :=
  match l with
  | [] => (false, l) (* no cycle and nothing more to extend *)
  | h :: t => match h, e with
                | (u1, v1, l1), (u2, v2) =>
                      if (u2 =? v2) then (true, []) (* self loop: the edge (u2, u2) exists *)
                      else if ((u2 =? v1) && (u1 =? v2)) then (true, []) (* cycle! u1 --l1--> v1=u2 -> v2=u1 *)
                      else if ((u2 =? v1) && (member v2 l1)) then (true, [])
                           (* cycle inside path: u1 --l1--> v1=u2 -> v2, which already appeared in l1 *)
                      else if (u2 =? v1) then let res := dfs_extend_by_edge e t in (* can extend h by e *)
                                              (fst res, h :: (add_path_no_repeats (u1, v2, l1 ++ [v1]) (snd res)))
                      else let res := dfs_extend_by_edge e t in (* cannot extend h by e *)
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

Example k_cycle: contains_cycle ([1; 2; 3; 4; 5], [(5, 1); (4, 5); (3, 4); (2, 3); (1, 2)]) = true.
Proof. reflexivity. Qed.

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


(* correctness proof for contains_cycle function and the contrapositive *)
Theorem contains_cycle_true_correct : forall G: graph,
  (exists p: path, is_directed_path_in_graph p G = true /\ ~(acyclic_path_2 p))
  <-> contains_cycle G = true.
Proof.
Admitted.

Theorem contains_cycle_false_correct : forall G: graph, forall p: path,
  contains_cycle G = false -> ((is_directed_path_in_graph p G = true) -> acyclic_path_2 p).
Proof.
  intros G p.
  pose proof contains_cycle_true_correct as cycle_true.
  specialize (cycle_true G).
  intros Hcyc Hpath.
  destruct (classic (acyclic_path_2 p)) as [HnC | HC].
  - apply HnC.
  - assert (H: (exists p' : path, is_directed_path_in_graph p' G = true /\ ~ acyclic_path_2 p')).
    { exists p. split. apply Hpath. apply HC. }
    apply cycle_true in H. rewrite H in Hcyc. discriminate Hcyc.
Qed.



(* simple properties of acyclic graphs *)
Lemma remove_node_preserves_acyclic: forall (G: graph) (u: node),
  contains_cycle G = false -> contains_cycle (remove_node_from_graph G u) = false.
Proof.
  intros G u H.
  destruct (contains_cycle (remove_node_from_graph G u)) as [|] eqn:Hcyc.
  - apply contains_cycle_true_correct in Hcyc. destruct Hcyc as [p Hp].
    apply contains_cycle_false_correct with (p := p) in H.
    + destruct Hp as [_ Hp]. exfalso. apply Hp. apply H.
    + apply remove_node_preserves_directed_path with (u := u). apply Hp.
  - reflexivity.
Qed.

Lemma acyclic_no_self_loop: forall (G: graph) (u: node),
  contains_cycle G = false -> is_edge (u, u) G = false.
Proof.
  intros G u Hcyc.
  destruct (is_edge (u, u) G) as [|] eqn:Hedge.
  - apply contains_cycle_false_correct with (p := (u, u, [])) in Hcyc.
    + simpl in Hcyc. destruct Hcyc as [Hcyc _]. unfold not in Hcyc.
        exfalso. apply Hcyc. reflexivity.
    + simpl. rewrite Hedge. reflexivity.
  - reflexivity.
Qed.

Lemma acyclic_no_two_cycle: forall (G: graph) (u v: node),
  contains_cycle G = false -> is_edge (u, v) G = true -> is_edge (v, u) G = false.
Proof.
  intros G u v Hcyc He.
  destruct (is_edge (v, u) G) as [|] eqn:Hvu.
  - apply contains_cycle_false_correct with (p := (u, u, [v])) in Hcyc.
    + simpl in Hcyc. destruct Hcyc as [F _]. exfalso. apply F. reflexivity.
    + simpl. rewrite He. rewrite Hvu. reflexivity.
  - reflexivity.
Qed.
