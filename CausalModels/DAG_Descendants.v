From CausalModels Require Import DAG_Basics.
From CausalModels Require Import DAG_CycleDetection.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.

Import ListNotations.

(* this file defines the functions necessary to find directed paths in a graph that start
   and end at specific nodes, find all descendants of a node in a graph, and thereby find
   all ancestors of a node in a graph. *)


(* return list of directed 1-paths (each edge becomes one 1-path) starting from s *)
Fixpoint directed_edges_as_paths_from_start (s: node) (E: edges) : paths :=
  match E with
  | [] => []
  | h :: t => match h with 
              | (u, v) => if (u =? s) then (u, v, []) :: directed_edges_as_paths_from_start s t
                          else directed_edges_as_paths_from_start s t
              end
  end.

(* determine all directed paths starting from u in G, assuming that G is acyclic,
   so we do not need to check the boolean output of `dfs_extend_by_edges_iter` *)
Definition find_directed_paths_from_start (u: node) (G: graph) : paths :=
  match G with
  | (V, E) => snd (dfs_extend_by_edges_iter E (directed_edges_as_paths_from_start u E) (length V))
  (* each path can have at most |V| vertices *)
  end.

Definition find_directed_paths_to_end (t: node) (G: graph): paths :=
  filter (fun (p: path) => path_end p =? t)
         (snd (dfs_extend_by_edges_iter (edges_in_graph G) (directed_edges_as_paths (edges_in_graph G)) (num_nodes G))).

Theorem directed_paths_to_end_correct : forall p: path, forall v: node, forall G: graph,
      (is_directed_path_in_graph p G = true) /\ (path_end p =? v = true) /\ acyclic_path_2 p
  <-> In p (find_directed_paths_to_end v G).
Proof.
Admitted.


Example directed_paths_from_1: find_directed_paths_from_start 1 G = [(1, 2, [])].
Proof. reflexivity. Qed.

Example directed_paths_from_3: find_directed_paths_from_start 3 G = [(3, 2, []); (3, 1, []); (3, 2, [1])].
Proof. reflexivity. Qed.

Example directed_paths_to_1: find_directed_paths_to_end 4 G = [].
Proof. reflexivity. Qed.

Example directed_paths_to_2: find_directed_paths_to_end 2 G = [(1, 2, []); (3, 2, []); (4, 2, [1]); (3, 2, [1])].
Proof. reflexivity. Qed.


(* return set of ending points of all paths in p, with no repeats
   example: if p = [[1 -> 2 -> 3], [1 -> 3], [1 -> 2]], then get_endpoints p returns [2, 3] *)
Fixpoint get_endpoints (p: paths) : nodes :=
  match p with
  | [] => []
  | h :: t => match h with
              | (u, v, l) => let int := get_endpoints t in
                             if (member v int) then int else v :: int
              end
  end.

(* every node is always a descendant of itself.
   other descendants are all possible ending points of directed paths in G that
   start from s *)
Definition find_descendants (s: node) (G: graph) : nodes := 
  s :: get_endpoints (find_directed_paths_from_start s G).

Example descendants_of_1: find_descendants 1 G = [1; 2].
Proof. reflexivity. Qed.

Example descendants_of_3: find_descendants 3 G = [3; 1; 2].
Proof. reflexivity. Qed.

Example descendants_of_4: find_descendants 4 G = [4; 1; 2].
Proof. reflexivity. Qed.

Lemma node_is_descendant_of_itself: forall s: node, forall G: graph,
  In s (find_descendants s G).
Proof.
  intros s G. unfold find_descendants. simpl. left. reflexivity.
Qed.

(* v is a descendant of u iff u = v or there is a directed path from u to v *)
Theorem find_descendants_correct: forall G: graph, forall u v: node,
  In v (find_descendants u G) <-> 
  u = v \/ exists U: path, is_directed_path_in_graph U G = true /\ path_start_and_end U u v = true.
Proof.
  intros G u v. split.
  - intros Hv. unfold find_descendants in Hv. destruct Hv as [Hv | Hv].
    + left. apply Hv.
    + right. induction (find_directed_paths_from_start u G) as [| h t IH].
      * simpl in Hv. exfalso. apply Hv.
      * simpl in Hv. destruct h as [[uh vh] lh]. destruct (member vh (get_endpoints t)) as [|] eqn:Hmem.
        -- apply IH. apply Hv.
        -- destruct Hv as [Hv | Hv].
Admitted.


(* find ancestors of a node by finding all nodes in G of which the given
   node is a descendant *)
Definition find_ancestors (e: node) (G: graph) : nodes := 
  match G with
  | (V, E) => filter (fun s => member e (find_descendants s G)) V
  end.

Example ancestors_of_1: find_ancestors 1 G = [1; 3; 4].
Proof. reflexivity. Qed.

Example ancestors_of_3: find_ancestors 3 G = [3].
Proof. reflexivity. Qed.

Example ancestors_of_4: find_ancestors 4 G = [4].
Proof. reflexivity. Qed.

Theorem descendants_ancestors_correct: forall G: graph, forall u v: node,
  node_in_graph u G = true /\ node_in_graph v G = true
  -> (In u (find_descendants v G) <-> In v (find_ancestors u G)).
Proof.
  intros [V E] u v Huv.
  split.
  - intros H. destruct Huv as [Hu Hv].
    destruct V as [| h t].
    + simpl in Hu. discriminate Hu.
    + apply filter_true. split.
      * simpl in Hv. destruct (h =? v) as [|] eqn:Hhv.
        -- left. apply eqb_eq. apply Hhv.
        -- right. apply member_In_equiv. apply Hv.
      * apply member_In_equiv. apply H.
  - intros H. destruct V as [| h t].
    + simpl in H. exfalso. apply H.
    + apply filter_true in H. destruct H as [_ H].
      apply member_In_equiv. apply H.
Qed.


(* if x is descendant of y, and y is descendant of z, then x is descendant of z *)
Theorem descendants_transitive: forall G: graph, forall x y z: node,
  In y (find_descendants z G) /\ In x (find_descendants y G) -> In x (find_descendants z G).
Proof.
  intros G x y z [Hy Hx].
  apply find_descendants_correct in Hy. destruct Hy as [Hy | Hy].
  { apply find_descendants_correct in Hx. destruct Hx as [Hx | Hx].
    - unfold find_descendants. left. rewrite <- Hx. apply Hy.
    - destruct Hx as [Uyx [dirUyx seUyx]]. destruct Uyx as [[vy vx] lyx].
      apply find_descendants_correct. right. exists (vy, vx, lyx). split. apply dirUyx. rewrite Hy. apply seUyx. }
  { destruct Hy as [Uzy [dirUzy seUzy]].
    apply find_descendants_correct in Hx. destruct Hx as [Hx | Hx].
    - apply find_descendants_correct. right. exists Uzy. split. apply dirUzy. rewrite <- Hx. apply seUzy.
    - destruct Hx as [Uyx [dirUyx seUyx]].
      destruct Uzy as [[uz uy] lzy]. destruct Uyx as [[vy vx] lyx].
      apply path_start_end_equal in seUyx. destruct seUyx as [Hy Hx]. rewrite Hy in dirUyx. rewrite Hx in dirUyx.
      apply path_start_end_equal in seUzy. destruct seUzy as [Hz Hy2]. rewrite Hy2 in dirUzy. rewrite Hz in dirUzy.
      apply find_descendants_correct. right. exists (concat z y x lzy lyx). split.
      * apply concat_directed_paths. split.
        + apply dirUzy.
        + apply dirUyx.
      * unfold concat. unfold path_start_and_end. simpl. rewrite eqb_refl. simpl. apply eqb_refl. }
Qed.



(* here we focus specifically on parent nodes. The parents of a node X are
   all nodes with an edge directly to X *)
Fixpoint find_parents_from_edges (X: node) (E: edges) : nodes :=
  match E with
  | [] => []
  | h :: t => match h with
              | (u, v) => if (v =? X) then u :: (find_parents_from_edges X t)
                          else find_parents_from_edges X t
              end
  end.

Definition find_parents (X: node) (G: graph) : nodes :=
  match G with
  | (V, E) => find_parents_from_edges X E
  end.

Theorem edge_from_parent_to_child: forall (X P: node) (G: graph),
  In P (find_parents X G) <-> edge_in_graph (P, X) G = true.
Proof.
  intros X P [V E]. split.
  { intros Hmem. simpl. simpl in Hmem.
  induction E as [| h t IH].
  - simpl in Hmem. exfalso. apply Hmem.
  - destruct h as [u v]. destruct (v =? X) as [|] eqn:HvX.
    + simpl in Hmem. rewrite HvX in Hmem. simpl in Hmem.
      destruct Hmem as [HuIsP | HInd].
      * simpl. rewrite HvX. apply eqb_eq in HuIsP. rewrite HuIsP. simpl. reflexivity.
      * simpl. destruct ((u =? P) && (v =? X)) as [|] eqn:H.
        -- reflexivity.
        -- apply IH. apply HInd.
    + simpl in Hmem. rewrite HvX in Hmem. simpl. rewrite HvX.
      destruct (u =? P) as [|] eqn:HuP.
      * simpl. apply IH. apply Hmem.
      * simpl. apply IH. apply Hmem. }
  { intros H. simpl. induction E as [| h t IH].
  - simpl in H. discriminate H.
  - destruct h as [a b]. simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + apply split_and_true in H. destruct H as [H1 H2]. simpl.
      destruct (b =? X) as [|] eqn:Hbv.
      * simpl. left. apply eqb_eq. apply H1.
      * discriminate H2.
    + simpl. destruct (b =? X) as [|] eqn:Hbv.
      * simpl. right. apply IH. simpl. apply H.
      * apply IH. simpl. apply H. }
Qed.

(* in well-formed graphs, parents must also be nodes in the graph *)
Lemma parents_in_graph: forall (G: graph) (u p: node),
  G_well_formed G = true
  -> In p (find_parents u G)
  -> node_in_graph p G = true.
Proof.
  intros G u p. intros HG Hp.
  apply edge_from_parent_to_child in Hp.
  assert (Hnode: node_in_graph p G = true /\ node_in_graph u G = true).
  { apply edge_corresponds_to_nodes_in_well_formed. split. apply HG. apply Hp. }
  apply Hnode.
Qed.

Lemma each_parent_appears_once: forall (u p: node) (G: graph),
  G_well_formed G = true -> In p (find_parents u G) -> count p (find_parents u G) = 1.
Proof.
  intros u p G HG Hp.
  unfold G_well_formed in HG. destruct G as [V E]. apply split_and_true in HG. destruct HG as [_ HG].
  apply forallb_true with (x := (p, u)) in HG.
  - apply eqb_eq in HG. simpl. clear Hp.
    assert (count_edge (p, u) E = count p (find_parents_from_edges u E)).
    { clear HG. induction E as [| h t IH].
      + simpl. reflexivity.
      + simpl. destruct h as [h1 h2]. destruct (h2 =? u) as [|] eqn:Hu.
        * simpl. destruct (h1 =? p) as [|] eqn:Hp.
          -- simpl. rewrite Hu. f_equal. apply IH.
          -- simpl. apply IH.
        * simpl. rewrite Hu. rewrite andb_comm. simpl. apply IH. }
    rewrite <- H. apply HG.
  - apply edge_from_parent_to_child in Hp. simpl in Hp. apply member_edge_In_equiv. apply Hp.
Qed.