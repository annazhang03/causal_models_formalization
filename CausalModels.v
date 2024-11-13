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
Require Import Classical.



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
      | h :: t => (eqbedge h e) || (member_edge e t)
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

Lemma member_edge_In_equiv_false : 
  forall (l : edges) (x: edge), member_edge x l = false <-> ~(In x l).
Proof.
  intros l x.
  split.
  - intros Hmem HIn. apply member_edge_In_equiv in HIn. rewrite Hmem in HIn. discriminate HIn.
  - intros HIn. unfold not in HIn. destruct (member_edge x l) as [|] eqn:Hmem.
    + exfalso. apply HIn. apply member_edge_In_equiv. apply Hmem.
    + reflexivity.
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

Definition path_start_and_end (U: path) (A B: node) : bool :=
  ((path_start U) =? A) && ((path_end U) =? B).

Theorem path_start_end_refl: forall u v: node, forall l: nodes,
  path_start_and_end (u, v, l) u v = true.
Proof.
  intros u v l.
  unfold path_start_and_end. simpl. rewrite eqb_refl. simpl. apply eqb_refl.
Qed.

Theorem path_start_end_equal: forall u v A B: node, forall l: nodes,
  path_start_and_end (u, v, l) A B = true -> u = A /\ v = B.
Proof.
  intros u v A B l.
  intros H. unfold path_start_and_end in H. apply split_and_true in H. destruct H.
  simpl in H. apply eqb_eq in H.
  simpl in H0. apply eqb_eq in H0.
  split. apply H. apply H0.
Qed.

Definition path_contains_node (U: path) (X: node) : bool :=
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

Definition G_well_formed (G: graph) : bool :=
  match G with
  | (V, E) => forallb (fun e => match e with
                                | (u, v) => member u V && member v V end) E
  end.

Definition node_in_graph (u: node) (G: graph) : bool :=
  match G with
  | (V, E) => member u V
  end.

Definition max_node_in_graph (G: graph) : node :=
  match G with
  | (V, E) => max_list V
  end.

Definition edge_in_graph (e: edge) (G: graph) : bool :=
  match G with
  | (V, E) => member_edge e E
  end.

Theorem edge_corresponds_to_nodes_in_well_formed: forall (G: graph) (u v: node),
  G_well_formed G = true /\ edge_in_graph (u, v) G = true
  -> node_in_graph u G = true /\ node_in_graph v G = true.
Proof.
  intros [V E] u v [HG Hedge].
  unfold G_well_formed in HG. apply forallb_true with (x:=(u,v)) in HG.
  - apply split_and_true in HG. destruct HG as [Hu Hv]. simpl.
    rewrite Hu. rewrite Hv. split. reflexivity. reflexivity.
  - simpl in Hedge. apply member_edge_In_equiv. apply Hedge.
Qed.



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

Lemma concat_directed_paths_helper: forall l1 l2: nodes, forall G: graph,
  (is_dir_path_in_graph_helper l1 G = true) /\ (is_dir_path_in_graph_helper l2 G = true)
  /\ first_and_last_elts_same l1 l2 = true
  -> is_dir_path_in_graph_helper (l1 ++ (tl l2)) G = true.
Proof.
  intros l1 l2 G [H1 [H2 H12]].
  induction l1 as [| h t IH].
  - simpl in H12. destruct l2 as [| h2 t2]. discriminate H12. discriminate H12. 
  - destruct t as [| h' t'].
    + simpl. destruct l2 as [| h2 t2] eqn:Hl2.
      * simpl. reflexivity.
      * simpl. simpl in H12. apply eqb_eq in H12.
        simpl in H2. rewrite <- H12 in H2. apply H2.
    + simpl in H12. destruct l2 as [| al2 bl2].
      * discriminate H12.
      * simpl. simpl in H1. apply split_and_true in H1. 
        destruct H1 as [Hedge Hrec]. rewrite Hedge. simpl.
        destruct t' as [| at' bt'].
        -- simpl in IH. apply IH. reflexivity. apply H12.
        -- apply IH. 
           ++ apply Hrec.
           ++ apply H12.
Qed.

Definition is_directed_path_in_graph (p: path) (G: graph) : bool :=
  match p with
  | (u, v, l) => is_dir_path_in_graph_helper ((u :: l) ++ [v]) G
  end.

Example dir_path_in_graph: is_directed_path_in_graph (3, 2, [1]) G = true.
Proof. reflexivity. Qed.

Example dir_path_not_in_graph: is_directed_path_in_graph (2, 4, [1]) G = false.
Proof. reflexivity. Qed.

Theorem directed_path_is_path: forall (p: path) (G: graph),
  is_directed_path_in_graph p G = true -> is_path_in_graph p G = true.
Proof.
  intros [[u v] l] [V E] Hdir.
  unfold is_directed_path_in_graph in Hdir.
  unfold is_path_in_graph.
  induction ((u :: l) ++ [v]) as [| h t IH].
  - simpl. reflexivity.
  - destruct t as [| h1 t1].
    + simpl. reflexivity.
    + simpl. simpl in Hdir. apply split_and_true in Hdir. destruct Hdir as [Hedge Hind].
      rewrite Hedge. simpl.
      apply IH. apply Hind.
Qed.

Theorem concat_directed_paths: forall u1 mid v2: node, forall l1 l2: nodes, forall G: graph,
  is_directed_path_in_graph (u1, mid, l1) G = true /\ is_directed_path_in_graph (mid, v2, l2) G = true
  -> is_directed_path_in_graph (concat u1 mid v2 l1 l2) G = true.
Proof.
  intros u1 mid v2 l1 l2 G.
  intros [U1 U2].
  unfold concat. unfold is_directed_path_in_graph.
  unfold is_directed_path_in_graph in U1.
  unfold is_directed_path_in_graph in U2.
  assert (Hfl: first_and_last_elts_same ((u1 :: l1) ++ [mid]) ((mid :: l2) ++ [v2]) = true).
  { apply first_and_last_same. }
  remember ((u1 :: l1) ++ [mid]) as ls1.
  remember ((mid :: l2) ++ [v2]) as ls2.
  assert (H: is_dir_path_in_graph_helper (ls1 ++ (tl ls2)) G = true).
  { apply concat_directed_paths_helper. split. apply U1. split. apply U2.
    destruct ls1 as [| h t].
    - discriminate Heqls1.
    - induction l1 as [| h1 t1 IH].
      + simpl. destruct ls2 as [| h2 t2].
        * discriminate Heqls2.
        * inversion Heqls1. simpl. inversion Heqls2. apply eqb_refl.
      + apply Hfl. }
  rewrite Heqls2 in H. simpl in H. rewrite Heqls1 in H.
  assert (Hformat: ((u1 :: l1) ++ [mid]) ++ l2 = u1 :: l1 ++ mid :: l2).
  { simpl. apply f_equal. apply append_vs_concat. }
  assert (Hformat2: ((u1 :: l1) ++ [mid]) ++ l2 ++ [v2] = ((u1 :: l1 ++ mid :: l2) ++ [v2])).
  { rewrite <- Hformat. simpl. rewrite app_assoc. reflexivity. }
  rewrite <- Hformat2. apply H.
Qed.

Program Fixpoint is_path_in_graph_2 (p: path) (G: graph) {measure (measure_path p)} : bool :=
  match G with
  | (V, E) => match p with
              | (u, v, []) => is_edge (u, v) G || is_edge (v, u) G
              | (u, v, h :: t) => ((is_edge (u, h) G) || (is_edge (h, u) G)) && is_path_in_graph_2 (h, v, t) G
              end
  end.

Theorem one_paths_2_correct : forall G: graph, forall u v: node,
  is_path_in_graph_2 (u, v, []) G = true <-> is_edge (u, v) G = true \/ is_edge (v, u) G = true.
Proof.
  intros G u v.
  split.
  - intros Hpath.
    cbn in Hpath.
    destruct (is_edge (u, v) G) as [|] eqn:Huv.
    + left. reflexivity.
    + right. simpl in Hpath. destruct (is_edge (v, u) G) as [|] eqn:Hvu.
      * reflexivity.
      * destruct G as [V E]. apply Hpath. 
  - intros Hedge. destruct Hedge as [Huv | Hvu].
    + cbn. rewrite Huv. simpl. destruct G as [V E]. reflexivity.
    + cbn. rewrite Hvu. rewrite (orb_comm (is_edge (u, v) G) true). simpl. destruct G as [V E]. 
      reflexivity.
Qed.

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
    + simpl. rewrite Huv. simpl. destruct G as [V E]. reflexivity.
    + simpl. rewrite Hvu. rewrite (orb_comm (is_edge (u, v) G) true). simpl. destruct G as [V E].
      reflexivity.
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

(* a path outputted in the find_all_paths_from_start_to_end function is a valid path in G *)
Theorem paths_start_to_end_valid : forall u v: node, forall l: nodes, forall G: graph,
  In (u, v, l) (find_all_paths_from_start_to_end u v G) -> is_path_in_graph (u, v, l) G = true.
Proof.
Admitted.

(* a path outputted in the find_all_paths_from_start_to_end function is acyclic *)
Theorem paths_start_to_end_acyclic : forall u v: node, forall l: nodes, forall G: graph,
  In (u, v, l) (find_all_paths_from_start_to_end u v G) -> acyclic_path_2 (u, v, l).
Proof.
Admitted.

(* an acyclic path from u to v is in G iff it is outputted in the find_all_paths_from_start_to_end function *)
Theorem paths_start_to_end_correct : forall p: path, forall u v: node, forall G: graph,
      (is_path_in_graph p G = true) /\ (path_start_and_end p u v = true) /\ acyclic_path_2 p
  <-> In p (find_all_paths_from_start_to_end u v G).
Proof.
Admitted.

Theorem intermediate_node_not_endpoint: forall u v x: node, forall l: nodes,
  In x l /\ acyclic_path_2 (u, v, l) -> (x <> u /\ x <> v).
Proof.
  intros u v x l. intros [Hmem Hacyc].
  unfold acyclic_path_2 in Hacyc. destruct Hacyc as [_ [Hxu [Hxv _]]].
  split.
  - destruct (x =? u) as [|] eqn:Hxueq.
    + apply eqb_eq in Hxueq. rewrite Hxueq in Hmem. unfold not in Hxu. apply Hxu in Hmem. exfalso. apply Hmem.
    + apply eqb_neq. apply Hxueq.
  - destruct (x =? v) as [|] eqn:Hxveq.
    + apply eqb_eq in Hxveq. rewrite Hxveq in Hmem. unfold not in Hxv. apply Hxv in Hmem. exfalso. apply Hmem.
    + apply eqb_neq. apply Hxveq.
Qed.

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

Theorem contains_cycle_true_correct : forall G: graph, forall p: path,
  (is_path_in_graph p G = true) /\ ~(acyclic_path_2 p) <-> 
  contains_cycle G = true.
Proof. 
Admitted.

Theorem contains_cycle_false_correct : forall G: graph, forall p: path,
  contains_cycle G = false -> ((is_path_in_graph p G = true) -> acyclic_path_2 p).
Proof.
  intros G p.
  pose proof contains_cycle_true_correct as cycle_true.
  specialize (cycle_true G p).
  intros acyc path.
  rewrite path in cycle_true. 
  destruct (classic (acyclic_path_2 p)) as [HnC | HC].
  - apply HnC.
  - assert (H: true = true /\ ~ acyclic_path_2 p). { split. reflexivity. apply HC. }
    apply cycle_true in H. rewrite H in acyc. discriminate acyc.
Qed.


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

Lemma node_is_descendant_of_itself: forall s: node, forall G: graph,
  In s (find_descendants s G).
Proof.
  intros s G. unfold find_descendants. simpl. left. reflexivity.
Qed.

Theorem find_descendants_correct: forall G: graph, forall u v: node,
  In v (find_descendants u G) <-> 
  exists U: path, is_directed_path_in_graph U G = true /\ path_start_and_end U u v = true.
Proof.
Admitted.

Lemma find_descendants_all_nodes: forall G: graph, forall u v: node,
  In v (find_descendants u G) -> node_in_graph u G = true /\ node_in_graph v G = true.
Proof.
Admitted.

Fixpoint find_ancestors_in_nodes (e: node) (V: nodes) (G: graph) : nodes :=
  match V with
  | [] => []
  | h :: t => if (member e (find_descendants h G)) then h :: find_ancestors_in_nodes e t G
              else find_ancestors_in_nodes e t G
  end.

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
  (In u (find_descendants v G) <-> In v (find_ancestors u G)).
Proof.
  intros [V E] u v.
  split.
  - intros H. 
    assert (Huv: node_in_graph u (V, E) = true /\ node_in_graph v (V, E) = true).
    { apply find_descendants_all_nodes in H. rewrite and_comm. apply H. }
    destruct Huv as [Hu Hv].
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
  apply find_descendants_correct in Hy. destruct Hy as [Uzy [dirUzy seUzy]].
  apply find_descendants_correct in Hx. destruct Hx as [Uyx [dirUyx seUyx]].
  destruct Uzy as [[uz uy] lzy]. destruct Uyx as [[vy vx] lyx].
  apply path_start_end_equal in seUyx. destruct seUyx as [Hy Hx]. rewrite Hy in dirUyx. rewrite Hx in dirUyx.
  apply path_start_end_equal in seUzy. destruct seUzy as [Hz Hy2]. rewrite Hy2 in dirUzy. rewrite Hz in dirUzy.
  apply find_descendants_correct. exists (concat z y x lzy lyx). split.
  - apply concat_directed_paths. split.
    + apply dirUzy.
    + apply dirUyx.
  - unfold concat. unfold path_start_and_end. simpl. rewrite eqb_refl. simpl. apply eqb_refl.
Qed.

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
  In P (find_parents X G) -> edge_in_graph (P, X) G = true.
Proof.
  intros X P [V E].
  intros Hmem. simpl. simpl in Hmem.
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
      * simpl. apply IH. apply Hmem.
Qed.


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

(* find all mediators, such as B in A -> B -> C. *)
Definition find_mediators (u v: node) (V: nodes) (E: edges) : nodes :=
  if (member u V && member v V) 
  then filter (fun x => (member_edge (u, x) E && member_edge (x, v) E)) V
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

Definition is_mediator_bool (u v med: node) (G: graph) : bool :=
  is_edge (u, med) G && is_edge (med, v) G.

Theorem is_mediator_Prop_vs_bool: forall u v med: node, forall G: graph, 
  is_mediator_bool u v med G = true <-> is_mediator u v med G.
Proof.
  intros u v med G.
  split.
  - intros H. unfold is_mediator. unfold is_mediator_bool in H. 
    rewrite H. apply I.
  - intros H. unfold is_mediator_bool. unfold is_mediator in H.
    destruct (is_edge (u, med) G && is_edge (med, v) G) as [|] eqn:H1.
    + reflexivity.
    + exfalso. apply H.
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
      apply filter_true. split.
      * apply member_In_equiv. apply Hb.
      * rewrite Hab. rewrite Hbc. reflexivity.
    + exfalso. apply Hmed.
  - intros Hmed. unfold find_mediators in Hmed. destruct (member a V && member c V) as [|] eqn:Hac.
    + apply filter_true in Hmed. destruct Hmed as [Hmem Hedges].
      unfold is_mediator. unfold is_edge.
      apply split_and_true in Hac. destruct Hac as [Ha Hc].
      apply split_and_true in Hedges. destruct Hedges as [Hab Hbc].
      rewrite Ha. rewrite Hc. rewrite Hab. rewrite Hbc.
      apply member_In_equiv in Hmem. rewrite Hmem. simpl. apply I.
    + simpl in Hmed. exfalso. apply Hmed.
Qed.

(* find all confounders, such as B in A <- B -> C. *)
Definition find_confounders (u v: node) (V: nodes) (E: edges) : nodes :=
  if (member u V && member v V) 
  then filter (fun x => (member_edge (x, u) E && member_edge (x, v) E)) V
  else [].


Definition is_confounder (u v con: node) (G: graph) : Prop :=
  match G with
  | (V, E) => if (is_edge (con, u) G && is_edge (con, v) G) then True else False
  end.

Definition is_confounder_bool (u v con: node) (G: graph) : bool :=
  is_edge (con, u) G && is_edge (con, v) G.

Theorem is_confounder_Prop_vs_bool: forall u v con: node, forall G: graph, 
  is_confounder_bool u v con G = true <-> is_confounder u v con G.
Proof.
  intros u v con G.
  split.
  - intros H. unfold is_confounder. unfold is_confounder_bool in H. 
    rewrite H. destruct G as [V E]. apply I.
  - intros H. unfold is_confounder_bool. unfold is_confounder in H.
    destruct (is_edge (con, u) G && is_edge (con, v) G) as [|] eqn:H1.
    + reflexivity.
    + exfalso. destruct G as [V E]. apply H.
Qed.

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
      apply filter_true. split.
      * apply member_In_equiv. apply Hb.
      * rewrite Hba. rewrite Hbc. reflexivity.
    + exfalso. apply Hcon.
  - intros Hcon. unfold find_confounders in Hcon. destruct (member a V && member c V) as [|] eqn:Hac.
    + apply filter_true in Hcon. destruct Hcon as [Hmem Hedges].
      unfold is_confounder. unfold is_edge.
      apply split_and_true in Hac. destruct Hac as [Ha Hc].
      apply split_and_true in Hedges. destruct Hedges as [Hba Hbc].
      rewrite Ha. rewrite Hc. rewrite Hba. rewrite Hbc.
      apply member_In_equiv in Hmem. rewrite Hmem. simpl. apply I.
    + simpl in Hcon. exfalso. apply Hcon.
Qed.


(* find all colliders, such as B in A -> B <- C. *)
Definition find_colliders (u v: node) (V: nodes) (E: edges) : nodes :=
  if (member u V && member v V) 
  then filter (fun x => (member_edge (u, x) E && member_edge (v, x) E)) V
  else [].

Definition is_collider (u v col: node) (G: graph) : Prop :=
  match G with
  | (V, E) => if (is_edge (u, col) G && is_edge (v, col) G) then True else False
  end.

Definition is_collider_bool (u v col: node) (G: graph) : bool :=
  is_edge (u, col) G && is_edge (v, col) G.

Theorem is_collider_Prop_vs_bool: forall u v col: node, forall G: graph, 
  is_collider_bool u v col G = true <-> is_collider u v col G.
Proof.
  intros u v col G.
  split.
  - intros H. unfold is_collider. unfold is_collider_bool in H. 
    rewrite H. destruct G as [V E]. apply I.
  - intros H. unfold is_collider_bool. unfold is_collider in H.
    destruct (is_edge (u, col) G && is_edge (v, col) G) as [|] eqn:H1.
    + reflexivity.
    + exfalso. destruct G as [V E]. apply H.
Qed.

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
      apply filter_true. split.
      * apply member_In_equiv. apply Hb.
      * rewrite Hab. rewrite Hcb. reflexivity.
    + exfalso. apply Hcol.
  - intros Hcol. unfold find_colliders in Hcol. destruct (member a V && member c V) as [|] eqn:Hac.
    + apply filter_true in Hcol. destruct Hcol as [Hmem Hedges].
      unfold is_collider. unfold is_edge.
      apply split_and_true in Hac. destruct Hac as [Ha Hc].
      apply split_and_true in Hedges. destruct Hedges as [Hab Hcb].
      rewrite Ha. rewrite Hc. rewrite Hab. rewrite Hcb.
      apply member_In_equiv in Hmem. rewrite Hmem. simpl. apply I.
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
Definition path_out_of_start (p: path) (G: graph) : bool :=
  match p with 
  | (u, v, l) => match l with
                | [] => is_edge (u, v) G
                | h :: t => is_edge (u, h) G
               end
  end.
  
Definition path_into_start (p: path) (G: graph) : bool :=
  match p with 
  | (u, v, l) => match l with
                | [] => is_edge (v, u) G
                | h :: t => is_edge (h, u) G
               end
  end.

Definition find_backdoor_paths_from_start_to_end (X Y: node) (G: graph) : paths :=
  filter (fun p: path => path_into_start p G) (find_all_paths_from_start_to_end X Y G).

Theorem path_must_have_direction: forall p: path, forall G: graph,
  is_path_in_graph p G = true -> path_into_start p G = false -> path_out_of_start p G = true.
Proof.
  intros p G.
  intros p_in_G p_not_in.
  destruct p as [[u v] l].
  simpl. destruct l as [| h t].
  - simpl in p_not_in. simpl in p_in_G. destruct G as [V E].
    rewrite p_not_in in p_in_G. rewrite orb_false_r in p_in_G. apply andb_true_elim2 in p_in_G. apply p_in_G.
  - simpl in p_not_in. simpl in p_in_G. destruct G as [V E]. apply andb_true_elim2 in p_in_G.
    rewrite p_not_in in p_in_G. rewrite orb_false_r in p_in_G. apply p_in_G.
Qed.



(* Conditional independence *)

(* output nodes which are mediators in the sequence given by l *)
Fixpoint find_mediators_in_nodes (l: nodes) (G: graph) : nodes :=
  match l with
  | [] => []
  | h :: t => match t with
              | [] => []
              | h1 :: [] => []
              | h1 :: (h2 :: t2) => if (is_mediator_bool h h2 h1 G) then h1 :: (find_mediators_in_nodes t G)
                                    else find_mediators_in_nodes t G
              end
  end.

(* output nodes which are mediators in the path given by p *)
Definition find_mediators_in_path (p: path) (G: graph) : nodes :=
  match p with
  | (u, v, l) => find_mediators_in_nodes (u :: (l ++ [v])) G
  end.

Theorem mediators_vs_edges_in_path: forall (l: nodes) (G: graph) (x: node),
  In x (find_mediators_in_nodes l G)
    <-> exists y z: node, sublist [y; x; z] l = true /\ is_edge (y, x) G = true /\ is_edge (x, z) G = true.
Proof.
  intros l G x. split.
  { intros Hmed. induction l as [| h t IH].
  - simpl in Hmed. exfalso. apply Hmed.
  - destruct t as [| h' t'].
    + simpl in Hmed. exfalso. apply Hmed.
    + destruct t' as [| h'' t''].
      * simpl in Hmed. exfalso. apply Hmed.
      * destruct (is_mediator_bool h h'' h' G) as [|] eqn:Hmed2.
        -- simpl in Hmed. rewrite Hmed2 in Hmed. simpl in Hmed. destruct Hmed as [Hhx | Hind].
           { exists h. exists h''. split.
             - rewrite <- Hhx. simpl.
               rewrite eqb_refl. simpl. rewrite eqb_refl. simpl. rewrite eqb_refl. reflexivity.
             - unfold is_mediator_bool in Hmed2. apply split_and_true in Hmed2.
               rewrite <- Hhx. apply Hmed2. }
           { apply IH in Hind. destruct Hind as [y Hind]. destruct Hind as [z Hind].
             exists y. exists z. split.
             - destruct Hind as [Hsub _]. simpl. apply split_orb_true. right. apply Hsub.
             - destruct Hind as [_ Hedge]. apply Hedge. }
        -- simpl in Hmed. rewrite Hmed2 in Hmed. simpl in Hmed. apply IH in Hmed.
           destruct Hmed as [y [z Hmed]]. exists y. exists z.
           split.
           { destruct Hmed as [Hsub _]. simpl. apply split_orb_true. right. apply Hsub. }
           { destruct Hmed as [_ Hedge]. apply Hedge. } }
  { intros [y [z [Hsub Hedge]]]. induction l as [| h t IH].
  - simpl in Hsub. discriminate Hsub.
  - destruct t as [| h' t'].
    + simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [contra | contra].
      * rewrite andb_comm in contra. apply andb_true_elim2 in contra. discriminate contra.
      * discriminate contra.
    + destruct t' as [| h'' t''].
      * simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [contra | contra].
        -- rewrite andb_comm in contra. apply andb_true_elim2 in contra.
           rewrite andb_comm in contra. apply andb_true_elim2 in contra. discriminate contra.
        -- apply split_orb_true in contra. destruct contra as [contra | contra].
           { rewrite andb_comm in contra. apply andb_true_elim2 in contra. discriminate contra. }
           { discriminate contra. }
      * simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [Hyxz | Hind].
        -- apply split_and_true in Hyxz. destruct Hyxz as [Hy Hxz].
           apply split_and_true in Hxz. destruct Hxz as [Hx Hz].
           rewrite andb_comm in Hz. simpl in Hz.
           assert (Hmed: (is_mediator_bool h h'' h' G) = true).
           { unfold is_mediator_bool.
             rewrite eqb_eq in Hy. rewrite <- Hy.
             rewrite eqb_eq in Hx. rewrite <- Hx.
             rewrite eqb_eq in Hz. rewrite <- Hz.
             destruct Hedge as [Hyx Hxz]. rewrite Hyx. rewrite Hxz. reflexivity. }
           simpl. rewrite Hmed. simpl. left. rewrite eqb_eq in Hx. rewrite Hx. reflexivity.
        -- apply IH in Hind. destruct (is_mediator_bool h h'' h' G) as [|] eqn:Hmed.
           { simpl. rewrite Hmed. simpl. right. apply Hind. }
           { simpl. rewrite Hmed. apply Hind. } }
Qed.

(* p contains chain A -> B -> C, where B in Z (the conditioning set) *)
Definition is_blocked_by_mediator_2 (p: path) (G: graph) (Z: nodes) : bool :=
  overlap Z (find_mediators_in_path p G). 

Example mediator_in_conditioning_set_2: 
  is_blocked_by_mediator_2 (1, 3, [2]) ([1; 2; 3], [(1, 2); (2, 3)]) [2] = true.
Proof. reflexivity. Qed.

Example mediator_not_in_conditioning_set_2: 
  is_blocked_by_mediator_2 (1, 3, [2]) ([1; 2; 3], [(1, 2); (2, 3)]) [] = false.
Proof. reflexivity. Qed.

Example mediator_in_longer_path_2:
  is_blocked_by_mediator_2 (1, 4, [2; 3]) ([1; 2; 3; 4], [(2, 1); (2, 3); (3, 4)]) [3] = true.
Proof. reflexivity. Qed.

(* output nodes which are confounders in the sequence given by l *)
Fixpoint find_confounders_in_nodes (l: nodes) (G: graph) : nodes :=
  match l with
  | [] => []
  | h :: t => match t with
              | [] => []
              | h1 :: [] => []
              | h1 :: (h2 :: t2) => if (is_confounder_bool h h2 h1 G) then h1 :: (find_confounders_in_nodes t G)
                                    else find_confounders_in_nodes t G
              end
  end.

(* output nodes which are confounders in the path given by p *)
Definition find_confounders_in_path (p: path) (G: graph) : nodes :=
  match p with
  | (u, v, l) => find_confounders_in_nodes (u :: (l ++ [v])) G
  end.

Theorem confounders_vs_edges_in_path: forall (l: nodes) (G: graph) (x: node),
  In x (find_confounders_in_nodes l G)
    <-> exists y z: node, sublist [y; x; z] l = true /\ is_edge (x, y) G = true /\ is_edge (x, z) G = true.
Proof.
  intros l G x. split.
  { intros Hconf. induction l as [| h t IH].
  - simpl in Hconf. exfalso. apply Hconf.
  - destruct t as [| h' t'].
    + simpl in Hconf. exfalso. apply Hconf.
    + destruct t' as [| h'' t''].
      * simpl in Hconf. exfalso. apply Hconf.
      * destruct (is_confounder_bool h h'' h' G) as [|] eqn:Hconf2.
        -- simpl in Hconf. rewrite Hconf2 in Hconf. simpl in Hconf. destruct Hconf as [Hhx | Hind].
           { exists h. exists h''. split.
             - rewrite <- Hhx. simpl.
               rewrite eqb_refl. simpl. rewrite eqb_refl. simpl. rewrite eqb_refl. reflexivity.
             - unfold is_confounder_bool in Hconf2. apply split_and_true in Hconf2.
               rewrite <- Hhx. apply Hconf2. }
           { apply IH in Hind. destruct Hind as [y Hind]. destruct Hind as [z Hind].
             exists y. exists z. split.
             - destruct Hind as [Hsub _]. simpl. apply split_orb_true. right. apply Hsub.
             - destruct Hind as [_ Hedge]. apply Hedge. }
        -- simpl in Hconf. rewrite Hconf2 in Hconf. simpl in Hconf. apply IH in Hconf.
           destruct Hconf as [y [z Hconf]]. exists y. exists z.
           split.
           { destruct Hconf as [Hsub _]. simpl. apply split_orb_true. right. apply Hsub. }
           { destruct Hconf as [_ Hedge]. apply Hedge. } }
  { intros [y [z [Hsub Hedge]]]. induction l as [| h t IH].
  - simpl in Hsub. discriminate Hsub.
  - destruct t as [| h' t'].
    + simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [contra | contra].
      * rewrite andb_comm in contra. apply andb_true_elim2 in contra. discriminate contra.
      * discriminate contra.
    + destruct t' as [| h'' t''].
      * simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [contra | contra].
        -- rewrite andb_comm in contra. apply andb_true_elim2 in contra.
           rewrite andb_comm in contra. apply andb_true_elim2 in contra. discriminate contra.
        -- apply split_orb_true in contra. destruct contra as [contra | contra].
           { rewrite andb_comm in contra. apply andb_true_elim2 in contra. discriminate contra. }
           { discriminate contra. }
      * simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [Hyxz | Hind].
        -- apply split_and_true in Hyxz. destruct Hyxz as [Hy Hxz].
           apply split_and_true in Hxz. destruct Hxz as [Hx Hz].
           rewrite andb_comm in Hz. simpl in Hz.
           assert (Hconf: (is_confounder_bool h h'' h' G) = true).
           { unfold is_confounder_bool.
             rewrite eqb_eq in Hy. rewrite <- Hy.
             rewrite eqb_eq in Hx. rewrite <- Hx.
             rewrite eqb_eq in Hz. rewrite <- Hz.
             destruct Hedge as [Hyx Hxz]. rewrite Hyx. rewrite Hxz. reflexivity. }
           simpl. rewrite Hconf. simpl. left. rewrite eqb_eq in Hx. rewrite Hx. reflexivity.
        -- apply IH in Hind. destruct (is_confounder_bool h h'' h' G) as [|] eqn:Hconf.
           { simpl. rewrite Hconf. simpl. right. apply Hind. }
           { simpl. rewrite Hconf. apply Hind. } }
Qed.

(* p contains fork A <- B -> C, where B in Z (the conditioning set) *)
Definition is_blocked_by_confounder_2 (p: path) (G: graph) (Z: nodes) : bool :=
  overlap Z (find_confounders_in_path p G). 

Example confounder_in_conditioning_set_2: 
  is_blocked_by_confounder_2 (1, 3, [2]) ([1; 2; 3], [(2, 1); (2, 3)]) [2] = true.
Proof. reflexivity. Qed.

Example confounder_not_in_conditioning_set_2: 
  is_blocked_by_confounder_2 (1, 3, [2]) ([1; 2; 3], [(2, 1); (2, 3)]) [] = false.
Proof. reflexivity. Qed.

Example confounder_in_longer_path_2: 
  is_blocked_by_confounder_2 (1, 4, [2; 3]) ([1; 2; 3; 4], [(2, 1); (2, 3); (3, 4)]) [2] = true.
Proof. reflexivity. Qed.

Fixpoint descendants_not_in_Z (d: nodes) (Z: nodes) : Prop :=
  match d with
  | [] => True
  | h :: t => ~(In h Z) /\ descendants_not_in_Z t Z
  end.

Definition descendants_not_in_Z_bool (d: nodes) (Z: nodes) : bool :=
  forallb (fun x: node => negb (member x Z)) d.

Definition some_descendant_in_Z_bool (d: nodes) (Z: nodes) : bool :=
  overlap d Z.

Theorem descendants_in_or_not_in: forall d: nodes, forall Z: nodes, 
  descendants_not_in_Z_bool d Z = false <-> some_descendant_in_Z_bool d Z = true.
Proof.
  intros d Z. split.
  - intros H. induction d as [| h t IH].
    + simpl in H. discriminate H.
    + simpl. simpl in H. destruct (member h Z) as [|] eqn:HhZ.
      * reflexivity.
      * simpl in H. apply IH in H. apply H.
  - intros H. induction d as [| h t IH].
    + simpl in H. discriminate H.
    + simpl. simpl in H. destruct (member h Z) as [|] eqn:HhZ.
      * simpl. reflexivity.
      * simpl. apply IH in H. apply H.
Qed.


(* output nodes which are colliders in the sequence given by l *)
Fixpoint find_colliders_in_nodes (l: nodes) (G: graph) : nodes :=
  match l with
  | [] => []
  | h :: t => match t with
              | [] => []
              | h1 :: [] => []
              | h1 :: (h2 :: t2) => if (is_collider_bool h h2 h1 G) then h1 :: (find_colliders_in_nodes t G)
                                    else find_colliders_in_nodes t G
              end
  end.

(* output nodes which are colliders in the path given by p *)
Definition find_colliders_in_path (p: path) (G: graph) : nodes :=
  match p with
  | (u, v, l) => find_colliders_in_nodes (u :: (l ++ [v])) G
  end.

(* there is some collider such that none of its descendants are in Z *)
Definition collider_descendants_not_conditioned (cols: nodes) (G: graph) (Z: nodes) : bool :=  
  existsb (fun c => descendants_not_in_Z_bool (find_descendants c G) Z) cols.

(* p contains collision A -> B <- C, where B and descendants are not in Z (the conditioning set) *)
Definition is_blocked_by_collider_2 (p: path) (G: graph) (Z: nodes) : bool :=
  collider_descendants_not_conditioned (find_colliders_in_path p G) G Z.

Fixpoint is_collider_in_path_helper (col: node) (l: nodes) (G: graph) : Prop :=
  match l with
  | [] => False
  | h :: t => match t with
              | [] => False
              | h1 :: [] => False
              | h1 :: (h2 :: t2) => if (h1 =? col) then is_collider h h2 h1 G
                                          else is_collider_in_path_helper col t G
              end
  end.

Definition is_collider_in_path (col: node) (p: path) (G: graph): Prop :=
  match p with
  | (u, v, l) => is_collider_in_path_helper col ((u :: l) ++ [v]) G
  end.

Fixpoint is_collider_in_path_helper_bool (col: node) (l: nodes) (G: graph) : bool :=
  match l with
  | [] => false
  | h :: t => match t with
              | [] => false
              | h1 :: [] => false
              | h1 :: (h2 :: t2) => if (h1 =? col) then is_collider_bool h h2 h1 G
                                    else is_collider_in_path_helper_bool col t G
              end
  end.

Definition is_collider_in_path_bool (col: node) (p: path) (G: graph): bool :=
  match p with
  | (u, v, l) => is_collider_in_path_helper_bool col ((u :: l) ++ [v]) G
  end.

Theorem is_collider_in_path_Prop_vs_bool: forall col: node, forall p: path, forall G: graph, 
  is_collider_in_path_bool col p G = true <-> is_collider_in_path col p G.
Proof.
  intros col [[u v] l] G.
  split.
  - intros H. unfold is_collider_in_path. unfold is_collider_in_path_bool in H.
    induction ((u :: l) ++ [v]) as [| h t IH].
    + simpl in H. discriminate H.
    + destruct t as [| h1 t1].
      * simpl in H. discriminate H.
      * destruct t1 as [| h2 t2].
        -- simpl in H. discriminate H.
        -- destruct (h1 =? col) as [|] eqn:Hhcol.
           ++ simpl in H. rewrite Hhcol in H.
              simpl. rewrite Hhcol. apply is_collider_Prop_vs_bool. apply H.
           ++ simpl in H. rewrite Hhcol in H.
              simpl. rewrite Hhcol.
              simpl in IH. apply IH in H. apply H.
  - intros H. unfold is_collider_in_path_bool. unfold is_collider_in_path in H.
    induction ((u :: l) ++ [v]) as [| h t IH].
    + simpl in H. exfalso. apply H.
    + destruct t as [| h1 t1].
      * simpl in H. exfalso. apply H.
      * destruct t1 as [| h2 t2].
        -- simpl in H. exfalso. apply H.
        -- destruct (h1 =? col) as [|] eqn:Hhcol.
           ++ simpl in H. rewrite Hhcol in H.
              simpl. rewrite Hhcol. apply is_collider_Prop_vs_bool. apply H.
           ++ simpl in H. rewrite Hhcol in H.
              simpl. rewrite Hhcol.
              simpl in IH. apply IH in H. apply H.
Qed.

Definition path_has_no_colliders (p: path) (G: graph): bool :=
  match p with
  | (u, v, l) => forallb (fun x: node => negb (is_collider_in_path_bool x p G)) l
  end.

Lemma colliders_in_path_helper: forall l: nodes, forall G: graph, forall C: node,
  In C (find_colliders_in_nodes l G) <-> is_collider_in_path_helper C l G.
Proof.
  intros l G C. split.
  - intros H. induction l as [| h t IH].
    + simpl in H. exfalso. apply H.
    + destruct t as [| h1 t1].
      * simpl in H. apply H.
      * destruct t1 as [| h2 t2].
        -- simpl. simpl in H. apply H.
        -- simpl. destruct (h1 =? C) as [|] eqn:Hh1C.
           ++ simpl in H.  (* TODO need V to have no duplicate nodes *)
Admitted.

Theorem colliders_in_path: forall p: path, forall G: graph, forall C: node,
  In C (find_colliders_in_path p G) <-> is_collider_in_path C p G.
Proof.
  intros p G C. split.
  - intros H. destruct p as [[u v] l].
    induction l as [| h t IH].
    + simpl in H. exfalso. apply H.
    + simpl.
Admitted.

Theorem intermediate_node_in_path: forall G: graph, forall u v x: node, forall l: nodes,
  is_path_in_graph (u, v, l) G = true -> 
  (In x l <-> 
  (In x (find_mediators_in_path (u, v, l) G)) \/ (In x (find_confounders_in_path (u, v, l) G)) \/
  (In x (find_colliders_in_path (u, v, l) G))).
Proof. (* TODO should me much more doable with sublist definition *)
  intros G u v x l.
  intros Hpath. split.
  - intros Hmem.
  unfold is_path_in_graph in Hpath. simpl in Hpath.
Admitted.

Example collider_in_conditioning_set_2: 
  is_blocked_by_collider_2 (1, 3, [2]) ([1; 2; 3], [(1, 2); (3, 2)]) [2] = false.
Proof. reflexivity. Qed.

Example collider_not_in_conditioning_set_2: 
  is_blocked_by_collider_2 (1, 3, [2]) ([1; 2; 3], [(1, 2); (3, 2)]) [] = true.
Proof. reflexivity. Qed.

Example descendant_in_conditioning_set_2: 
  is_blocked_by_collider_2 (1, 3, [2]) ([1; 2; 3; 4], [(1, 2); (3, 2); (2, 4)]) [4] = false.
Proof. reflexivity. Qed.

Example collider_in_longer_path_2: 
  is_blocked_by_collider_2 (1, 4, [2; 3]) ([1; 2; 3; 4], [(1, 2); (3, 2); (3, 4)]) [] = true.
Proof. reflexivity. Qed.

Definition path_is_blocked_bool (G: graph) (Z: nodes) (p: path) : bool :=
  is_blocked_by_mediator_2 p G Z || is_blocked_by_confounder_2 p G Z || is_blocked_by_collider_2 p G Z.

Example collider_no_conditioning_needed_2: path_is_blocked_bool G_d [] (5, 8, [6; 7]) = true.
Proof. reflexivity. Qed.

(* conditioning on W unblocks the path from Z to Y *)
Example condition_on_collider_2: 
  path_is_blocked_bool G_d [6] (5, 8, [6; 7]) = false.
Proof. reflexivity. Qed.

(* conditioning on U (a descendant of W) unblocks the path from Z to Y *)
Example condition_on_descendant_collider_2:
  path_is_blocked_bool G_d [10] (5, 8, [6; 7]) = false.
Proof. reflexivity. Qed.

(* conditioning on X blocks the path from Z to Y, even if W unblocks it *)
Example condition_on_collider_and_mediator_2: 
  path_is_blocked_bool G_d [6; 7] (5, 8, [6; 7]) = true.
Proof. reflexivity. Qed.

(* determine whether u and v are independent in G conditional on the nodes in Z *)
Definition d_separated_bool (u v: node) (G: graph) (Z: nodes) : bool :=
  forallb (path_is_blocked_bool G Z) (find_all_paths_from_start_to_end u v G).


(* Z to Y are unconditionally independent due to collider at W *)
Example unconditionally_independent_2: d_separated_bool 5 8 G_d [] = true.
Proof. reflexivity. Qed.

(* conditioning on W unblocks the path from Z to Y *)
Example conditionally_dependent_2: d_separated_bool 5 8 G_d [6] = false.
Proof. reflexivity. Qed.

(* based on figure 2.8 of primer *)
(* conditioning on nothing leaves the path Z <- T -> Y open *)
Example unconditionally_dependent_2:
  d_separated_bool 5 8 G_d_modified [] = false.
Proof. reflexivity. Qed.

(* conditioning on T blocks the second path from Z to Y *)
Example conditionally_independent_2: 
  d_separated_bool 5 8 (V_d ++ [11; 12], E_d ++ [(11, 5); (11, 8); (12, 11)]) [11] = true.
Proof. reflexivity. Qed.

(* conditioning on T and W unblocks the path Z -> W <- X -> Y *)
Example condition_on_T_W_2 : 
  d_separated_bool 5 8 (V_d ++ [11; 12], E_d ++ [(11, 5); (11, 8); (12, 11)]) [11; 6] = false.
Proof. reflexivity. Qed.

(* conditioning on X closes the path Z -> W <- X -> Y *)
Example condition_on_T_W_X_2 : 
  d_separated_bool 5 8 (V_d ++ [11; 12], E_d ++ [(11, 5); (11, 8); (12, 11)]) [11; 6; 7] = true.
Proof. reflexivity. Qed.

Definition all_colliders_have_descendant_conditioned_on (col: nodes) (G: graph) (Z: nodes) : bool :=
  forallb (fun c => (some_descendant_in_Z_bool (find_descendants c G) Z)) col.

Definition d_connected_2 (p: path) (G: graph) (Z: nodes) : Prop :=
  overlap Z (find_mediators_in_path p G) = false /\
  overlap Z (find_confounders_in_path p G) = false /\
  all_colliders_have_descendant_conditioned_on (find_colliders_in_path p G) G Z = true.


(* u and v are d-separated given Z in G iff no path d-connects u and v given Z *)
Theorem d_separated_vs_connected: forall u v: node, forall G: graph, forall Z: nodes, 
  d_separated_bool u v G Z = false <-> 
  exists l: nodes, (acyclic_path_2 (u, v, l)) /\ (is_path_in_graph (u, v, l) G = true)
                                              /\ d_connected_2 (u, v, l) G Z.
Proof.
  intros u v G Z.
  split.
  - intros d_sep.
    unfold d_separated_bool in d_sep.
    apply demorgan_many_bool in d_sep.
    destruct d_sep as [p [HIn Hblock]].
    apply paths_start_to_end_correct in HIn. destruct HIn as [Hpath [Hse Hcyc]].
    destruct p as [[s e] l].
    apply path_start_end_equal in Hse. destruct Hse as [Hsu Hev].
    rewrite <- Hsu. rewrite <- Hev.
    exists l.
    split. apply Hcyc. split. apply Hpath.
    unfold path_is_blocked_bool in Hblock.
    apply demorgan_bool in Hblock. destruct Hblock as [Hblock Hcol].
    apply demorgan_bool in Hblock. destruct Hblock as [Hmed Hcon].
    unfold d_connected_2. split.
    (* no mediators are in Z *)
    + unfold is_blocked_by_mediator_2 in Hmed. apply Hmed.
    + split.
      (* no confounders are in Z *)
      * unfold is_blocked_by_confounder_2 in Hcon. apply Hcon.
      (* every collider has a descendant in Z *)
      * unfold is_blocked_by_collider_2 in Hcol.
        induction (find_colliders_in_path (s, e, l) G) as [| h t IH].
        -- simpl. reflexivity.
        -- simpl. simpl in Hcol.
           destruct (member h Z) as [|] eqn:HhZ.
           ++ simpl in Hcol. simpl. apply IH in Hcol. apply Hcol.
           ++ simpl in Hcol. simpl.
              destruct (descendants_not_in_Z_bool (get_endpoints (find_directed_paths_from_start h G)) Z) as [|] eqn:Hdesc.
              ** discriminate Hcol.
              ** apply IH in Hcol. rewrite Hcol.
                 apply descendants_in_or_not_in in Hdesc. rewrite Hdesc. reflexivity.
  - intros [l [cyc [path conn]]].
    unfold d_separated_bool. apply demorgan_many_bool. 
    exists (u, v, l). split.
    + apply paths_start_to_end_correct. split. apply path. split.
      * unfold path_start_and_end. simpl. rewrite eqb_refl. simpl. apply eqb_refl.
      * apply cyc.
    + unfold path_is_blocked_bool. unfold d_connected_2 in conn. destruct conn as [med [con col]].
      apply demorgan_bool. split.
      * apply demorgan_bool. split.
        (* path is not blocked by any mediator *)
        -- unfold is_blocked_by_mediator_2. apply med.
        (* path is not blocked by any confounder *)
        -- unfold is_blocked_by_confounder_2. apply con.
      (* path is not blocked by any collider *)
      * unfold is_blocked_by_collider_2. 
        induction (find_colliders_in_path (u, v, l) G) as [| h t IH].
        -- simpl. reflexivity.
        -- simpl. simpl in col. destruct (member h Z) as [|] eqn:HhZ.
           ++ simpl. simpl in col. apply IH in col. apply col.
           ++ simpl. simpl in col.
              destruct (descendants_not_in_Z_bool (get_endpoints (find_directed_paths_from_start h G)) Z) as [|] eqn:Hdesc.
              ** apply split_and_true in col. destruct col as [desc col].
                 apply descendants_in_or_not_in in desc. rewrite desc in Hdesc. discriminate Hdesc.
              ** apply split_and_true in col. destruct col as [desc col].
                 apply IH in col. apply col.
Qed.

(* interventions *)
Definition remove_edges_into (X: node) (E: edges) : edges :=
  filter (fun edg => negb (snd edg =? X)) E.

Definition do (X: node) (G: graph) : graph :=
  match G with
  | (V, E) => (V, remove_edges_into X E)
  end.

Example do_X_ice_cream: do 4 G_temp = (V_temp, [(2, 5); (3, 6); (5, 6)]).
Proof. reflexivity. Qed.

Lemma do_preserves_nodes: forall (X Y: node) (G: graph),
  (node_in_graph Y G = true) -> (node_in_graph Y (do X G) = true).
Proof.
  intros X Y [V E].
  simpl. intros H. apply H.
Qed.

Lemma do_preserves_edges_not_into_X: forall (X: node) (e: edge) (G: graph), 
  (edge_in_graph e G = true) -> (snd e =? X) = false
  -> edge_in_graph e (do X G) = true.
Proof.
  intros X e [V E]. intros He. intros HeX.
  unfold do. simpl. simpl in He.
  apply member_edge_In_equiv. apply filter_true. split.
  - apply member_edge_In_equiv in He. apply He.
  - replace (true) with (negb false).
    + f_equal. apply HeX.
    + reflexivity.
Qed.

Lemma do_removes_edges_into_X: forall (X: node) (e: edge) (G: graph), 
  (snd e =? X) = true -> edge_in_graph e (do X G) = false.
Proof.
  intros X e [V E]. intros HeX.
  unfold do. simpl.
  unfold remove_edges_into.
  apply member_edge_In_equiv_false. intros HIn.
  apply filter_In in HIn as [_ contra].
  apply negb_both_sides in contra. simpl in contra.
  unfold node in *.
  rewrite HeX in contra.
  discriminate contra.
Qed.

Theorem do_removes_paths_to_X: forall (X: node) (G: graph), 
  find_all_paths_to_end X (find_all_paths (do X G)) = [].
Proof.
Admitted.

Definition satisfies_backdoor_criterion (X Y: node) (G: graph) (Z: nodes) : Prop :=
  (* no node in Z is a descendant of X *)
  overlap Z (find_descendants X G) = false /\
  (* Z blocks every path between X and Y that contains an arrow into X *)
  forallb (fun p: path => path_is_blocked_bool G Z p) 
          (find_backdoor_paths_from_start_to_end X Y G) = true.

(* Figure 3.6 of primer *)
Example weight_fits_backdoor_criterion: satisfies_backdoor_criterion 1 2 G_drug [3].
Proof.
  compute. split. reflexivity. reflexivity.
Qed.

(* Figure 2.8 *)
Example no_backdoor_paths: satisfies_backdoor_criterion 7 8 G_d_modified [].
Proof.
  compute. split. reflexivity. reflexivity.
Qed.

Example dont_adjust_for_collider: ~(satisfies_backdoor_criterion 7 8 G_d_modified [6]).
Proof.
  compute. intros [contra _]. discriminate.
Qed.


Theorem parent_satisfy_backdoor_criterion: forall (X Y: node) (G: graph),
  G_well_formed G = true -> 
  (contains_cycle G = false) -> satisfies_backdoor_criterion X Y G (find_parents X G).
Proof.
  intros X Y G HG Hacyc.
  unfold satisfies_backdoor_criterion. split.
  - (* If there was overlap, then a parent P would be a descendant of X.
       Then there is a dipath from X to P, so concatenating that with edge (P, X)
       forms a cycle, contradicting Hacyc. *)
    apply no_overlap_non_member. intros P Hdesc Hparent.
    apply find_descendants_correct in Hdesc as [U [Hdir HUse]].
    apply edge_from_parent_to_child in Hparent as Hedge.
    assert (HedgePath: is_directed_path_in_graph (P, X, []) G = true).
    { simpl. rewrite andb_comm. simpl. unfold is_edge. destruct G as [V E].
      simpl in Hedge. rewrite Hedge. rewrite andb_comm. simpl.
      assert (H: node_in_graph P (V, E) = true /\ node_in_graph X (V, E) = true).
      { apply edge_corresponds_to_nodes_in_well_formed. split. apply HG.
        simpl. apply Hedge. }
      simpl in H. destruct H as [HP HV]. rewrite HP. rewrite HV. reflexivity. }
    destruct U as [[u v] l]. apply path_start_end_equal in HUse as [HuX HvP].
    assert (HnewPath: is_directed_path_in_graph (concat X P X l []) G = true).
    { apply concat_directed_paths. split.
      - rewrite HuX in Hdir. rewrite HvP in Hdir. apply Hdir.
      - apply HedgePath. }
    assert (contra: acyclic_path_2 (concat X P X l [])).
    { apply contains_cycle_false_correct with (p:=(concat X P X l [])) in Hacyc. apply Hacyc.
      apply directed_path_is_path. apply HnewPath. }
    simpl in contra. destruct contra as [contra _].
    apply eqb_neq in contra. rewrite eqb_refl in contra. discriminate contra.
  - (* For each path, the second node is a parent P (since the path is backdoor).
       The path is blocked: if P is a mediator or confounder, then it blocks 
       the path. If P is a collider, contradiction (cycle (X, P), (P, X)) *)
    apply forallb_forall. intros U Hbackdoor.
    unfold find_backdoor_paths_from_start_to_end in Hbackdoor.
    apply filter_true in Hbackdoor as [HUpath HintoX].
    apply paths_start_to_end_correct in HUpath as [HUpath [HUse HUacyc]].
    destruct U as [[u v] l]. apply path_start_end_equal in HUse as [HuX HvY].
    destruct l as [| h t].
    + unfold path_is_blocked_bool.
      assert (Hcol: is_blocked_by_collider_2 (u, v, []) G (find_parents X G) = true).
      { unfold is_blocked_by_collider_2.
        simpl.
Admitted.



(* counterfactuals *)
Definition assignment : Type := node * nat.
Definition assignments : Type := list assignment.

Definition no_repeat_nodes (V: nodes) : bool :=
  forallb (fun x: node => count x V =? 1) V.

Definition find_new_node (V: nodes) : node :=
  (max_list V) + 1.

Example add_new_node_1: find_new_node [1;2;3;4] = 5.
Proof. reflexivity. Qed.

Example add_new_node_2: find_new_node [1;2;4] = 5.
Proof. reflexivity. Qed.

Example add_new_node_3: find_new_node [2;1;4] = 5.
Proof. reflexivity. Qed.

Example add_new_node_4: find_new_node [2;4] = 5.
Proof. reflexivity. Qed.

Lemma new_node_non_member: forall V: nodes,
  member (find_new_node V) V = false.
Proof.
  intros V.
  unfold find_new_node.
  destruct (member (max_list V + 1) V) as [|] eqn:Hmem.
  - apply member_In_equiv in Hmem. apply max_correct in Hmem.
    apply leb_le in Hmem. 
    lia.
  - reflexivity.
Qed.

Theorem add_new_node_no_repeats: forall V: nodes,
  no_repeat_nodes V = true -> no_repeat_nodes ((find_new_node V) :: V) = true.
Proof.
  intros V H.
  apply forallb_true_iff. simpl. split.
  - (* find new node has no repeats *)
    rewrite eqb_refl. simpl.
    apply eqb_eq. apply not_member_count_0.
    apply new_node_non_member.
  - (* V has no repeats (H) *)
    apply forallb_true_iff.
    unfold no_repeat_nodes in H.
    apply forallb_forall. intros x Hmem.
    destruct (find_new_node V =? x) as [|] eqn:contra.
    + apply eqb_eq in contra. rewrite <- contra in Hmem. apply member_In_equiv in Hmem.
      assert (Hnomem: member (find_new_node V) V = false). { apply new_node_non_member. }
      rewrite Hmem in Hnomem. discriminate Hnomem.
    + apply forallb_true with (test := (fun x : node => count x V =? 1)) in Hmem.
      * apply Hmem.
      * apply H.
Qed.

(* shifting is used to translate a set of nodes by an offset
   when duplicating a graph for the twin network, the offset is the max node number *)
Fixpoint shift_nodes_by_offset (Z: nodes) (o: nat) :=
  match Z with
  | [] => []
  | h :: t => (h + o) :: (shift_nodes_by_offset t o)
  end.

Lemma shift_greater_than_offset: forall l: nodes, forall o: nat, forall x: node,
  In x (shift_nodes_by_offset l o) -> o <= x.
Proof.
  intros l o x.
  induction l as [| h t IH].
  - intros H. simpl in H. exfalso. apply H.
  - simpl. intros H. destruct H as [H | H].
    + lia.
    + apply IH. apply H.
Qed.

Lemma shift_member: forall l: nodes, forall x: node, forall o: nat,
  In x (shift_nodes_by_offset l o) <-> In (x - o) l /\ o <= x.
Proof.
  intros l x o. split.
  { intros Hmem.
  induction l as [| h t IH].
  - simpl in Hmem. exfalso. apply Hmem.
  - simpl. simpl in Hmem. destruct Hmem as [Heq | Hind].
    + lia.
    + split.
      * right. apply IH. apply Hind.
      * apply shift_greater_than_offset in Hind. apply Hind. }
  { intros [Hmem Hox].
  induction l as [| h t IH].
  - simpl in Hmem. exfalso. apply Hmem.
  - simpl. simpl in Hmem. destruct Hmem as [Heq | Hind].
    + left. lia.
    + right. apply IH. apply Hind. }
Qed.

Lemma shift_maintains_overlap: forall (l1 l2: nodes) (o: nat),
  overlap l1 l2 = false -> overlap (shift_nodes_by_offset l1 o) (shift_nodes_by_offset l2 o) = false.
Proof.
  intros l1 l2 o H.
  apply no_overlap_non_member. intros x Hmem2 Hmem1.
  apply shift_member in Hmem1. destruct Hmem1 as [Hmem1 _].
  apply shift_member in Hmem2. destruct Hmem2 as [Hmem2 _].
  apply no_overlap_non_member with (x := x - o) in H.
  - unfold not in H. apply H. apply Hmem1.
  - apply Hmem2.
Qed.

Lemma shift_maintains_prefix: forall (l1 l2: nodes) (o: nat),
  prefix l1 l2 = true <-> prefix (shift_nodes_by_offset l1 o) (shift_nodes_by_offset l2 o) = true.
Proof.
  induction l1 as [| h1 t1 IH].
  - intros l2 o. split.
    { simpl. reflexivity. }
    { simpl. reflexivity. }
  - intros l2 o. split.
    { intros Hpref. destruct l2 as [| h2 t2].
    + simpl in Hpref. discriminate Hpref.
    + simpl in Hpref. apply split_and_true in Hpref. destruct Hpref as [H12 Hind].
      simpl. apply eqb_eq in H12. rewrite H12. rewrite eqb_refl. simpl.
      apply IH with (l2 := t2). apply Hind. }
    { intros Hpref. destruct l2 as [| h2 t2].
    + simpl in Hpref. discriminate Hpref.
    + simpl in Hpref. apply split_and_true in Hpref. destruct Hpref as [H12o Hind].
      simpl. apply eqb_eq in H12o.
      assert (H12: h1 = h2). { lia. }
      rewrite H12. rewrite eqb_refl. simpl.
      apply IH with (l2 := t2) (o := o). apply Hind. }
Qed.

Lemma shift_maintains_subset: forall (l1 l2: nodes) (o: nat),
  sublist l1 l2 = true <-> sublist (shift_nodes_by_offset l1 o) (shift_nodes_by_offset l2 o) = true.
Proof.
  intros l1 l2 o. split.
  { intros Hsub. induction l2 as [| h2 t2 IH].
  - destruct l1 as [| h1 t1].
    + simpl. reflexivity.
    + simpl in Hsub. discriminate Hsub.
  - simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [Hpre | Hind].
    + simpl. apply shift_maintains_prefix with (o := o) in Hpre.
      simpl in Hpre. rewrite Hpre. simpl. reflexivity.
    + apply IH in Hind. simpl. rewrite Hind. rewrite orb_comm. simpl. reflexivity. }
  { intros Hsub. induction l2 as [| h2 t2 IH].
  - destruct l1 as [| h1 t1]. 
    + simpl. reflexivity.
    + simpl in Hsub. discriminate Hsub.
  - simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [Hpre | Hind].
    + simpl.
      replace (h2 + o :: shift_nodes_by_offset t2 o) with (shift_nodes_by_offset (h2 :: t2) o) in Hpre.
      * apply shift_maintains_prefix in Hpre. rewrite Hpre. simpl. reflexivity.
      * simpl. reflexivity.
    + apply IH  in Hind. simpl. rewrite Hind. rewrite orb_comm. simpl. reflexivity. }
Qed.

Lemma shift_maintains_append: forall (l1 l2: nodes) (o: nat),
  (shift_nodes_by_offset l1 o) ++ (shift_nodes_by_offset l2 o) = shift_nodes_by_offset (l1 ++ l2) o.
Proof.
  intros l1 l2 o. induction l1 as [| h1 t1 IH].
  - simpl. reflexivity.
  - simpl. apply f_equal. apply IH.
Qed.

(*
Twin Network

BEFORE PREPROCESSING:

for each v in V:
  create new v' in V'
  create new u in U
  add edges (u, v), (u, v')

for each edge (x, y) in E:
  add edge (x', y')

for each v in obs:
  apply do operator for v

for each v in cf:
  apply do operator for v' based on corr

for each u in U:
  if u has <2 edges out, delete edges and node

return (V + V' + U, edges)
*)

Fixpoint get_twin_nodes (V: nodes) (o: nat) : nodes :=
  match V with
  | [] => []
  | h :: t => (h + o) :: (get_twin_nodes t o)
  end.

Lemma twin_nodes_duplicated: forall V, forall o: nat, forall u: node,
  member u V = true <-> member (u + o) (get_twin_nodes V o) = true.
Proof.
  intros V.
  induction V as [| h t IH].
  - intros o u. split.
    { intros Hmem. simpl in Hmem. discriminate Hmem. }
    { intros Hmem. simpl in Hmem. discriminate Hmem. }
  - intros o u. split.
    { intros Hmem. simpl in Hmem. destruct (h + o =? u + o) as [|] eqn:Hhu.
    + simpl. rewrite Hhu. reflexivity.
    + simpl. rewrite Hhu. 
      apply IH. destruct (h =? u) as [|] eqn:Hhu1.
      * rewrite eqb_eq in Hhu1. rewrite Hhu1 in Hhu.
        rewrite eqb_refl in Hhu. discriminate Hhu.
      * apply Hmem. }
    { intros Hmem. simpl in Hmem. simpl. destruct (h =? u) as [|] eqn:Hhu.
    + reflexivity.
    + destruct (h + o =? u + o) as [|] eqn:Hhu1.
      * rewrite eqb_eq in Hhu1. assert (H: h = u). { lia. }
        rewrite H in Hhu.
        rewrite eqb_refl in Hhu. discriminate Hhu.
      * apply IH in Hmem. apply Hmem. }
Qed.

Fixpoint get_twin_edges (E: edges) (o: nat) : edges :=
  match E with
  | [] => []
  | h :: t => match h with
              | (u, v) => (u + o, v + o) :: (get_twin_edges t o)
              end
  end.

Lemma twin_edges_duplicated: forall E: edges, forall o: nat, forall e: edge,
  member_edge e E = true <-> member_edge (fst e + o, snd e + o) (get_twin_edges E o) = true.
Proof.
  intros E o e. split.
  { intros Hmem.
  induction E as [| h t IH].
  - simpl in Hmem. discriminate Hmem.
  - simpl in Hmem. apply split_orb_true in Hmem. destruct Hmem as [Heq | Hmem].
    + destruct h as [u v]. simpl. destruct e as [u' v'].
      unfold eqbedge in Heq. apply split_and_true in Heq. destruct Heq as [Hu Hv].
      simpl. apply eqb_eq in Hu. apply eqb_eq in Hv. rewrite Hu. rewrite eqb_refl. simpl.
      rewrite Hv. rewrite eqb_refl. simpl. reflexivity.
    + apply IH in Hmem. destruct h as [u' v']. simpl. rewrite Hmem.
      rewrite orb_comm. simpl. reflexivity. }
  { intros Hmem.
  induction E as [| h t IH].
  - simpl in Hmem. discriminate Hmem.
  - destruct e as [u v]. destruct h as [u' v']. simpl in Hmem. simpl.
    apply split_orb_true in Hmem. destruct Hmem as [Heq | Hind].
    + apply split_and_true in Heq. destruct Heq as [Hu Hv].
      rewrite eqb_eq in Hu. assert (Hu1: u' = u). { lia. }
      rewrite eqb_eq in Hv. assert (Hv1: v' = v). { lia. }
      rewrite Hu1. rewrite Hv1. rewrite eqb_refl. simpl. rewrite eqb_refl. simpl.
      reflexivity.
    + simpl in IH. apply IH in Hind. rewrite Hind. rewrite orb_comm. simpl.
      reflexivity. }
Qed.

Definition duplicate_graph (G: graph) : graph :=
  match G with
  | (V, E) => (get_twin_nodes V (max_list V), get_twin_edges E (max_list V))
  end.

Lemma duplicate_graph_maintains_edges: forall (u v: node) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  is_edge (u, v) G = true <-> is_edge (u + o, v + o) (duplicate_graph G) = true.
Proof.
  intros y x G o Ho. split.
  - intros Hedge. destruct G as [V E]. simpl. simpl in Ho.
    unfold is_edge in Hedge. apply split_and_true in Hedge. destruct Hedge as [Hmem Hedge].
    apply split_and_true in Hmem. destruct Hmem as [Hy Hx].
    assert (Hmemy: member (y + o) (get_twin_nodes V (max_list V)) = true).
    { apply twin_nodes_duplicated with (o := o) in Hy.
      rewrite <- Ho. apply Hy. }
    rewrite Hmemy. simpl.
    assert (Hmemx: member (x + o) (get_twin_nodes V (max_list V)) = true).
    { apply twin_nodes_duplicated with (o := o) in Hx.
      rewrite <- Ho. apply Hx. }
    rewrite Hmemx. simpl.
    apply twin_edges_duplicated with (o := o) in Hedge. simpl in Hedge.
    rewrite <- Ho. apply Hedge.
  - intros Hedge. destruct G as [V E]. simpl. simpl in Ho.
    unfold is_edge in Hedge. apply split_and_true in Hedge. destruct Hedge as [Hmem Hedge].
    apply split_and_true in Hmem. destruct Hmem as [Hy Hx].
    rewrite <- Ho in Hy. apply twin_nodes_duplicated in Hy.
    rewrite Hy.
    rewrite <- Ho in Hx. apply twin_nodes_duplicated in Hx.
    rewrite Hx.
    rewrite <- Ho in Hedge. apply twin_edges_duplicated with (e := (y,x)) in Hedge.
    rewrite Hedge. simpl. reflexivity.
Qed.

Lemma duplicate_graph_maintains_mediators: forall (u v: node) (l: nodes) (G: graph) (o: nat) (x: node),
  o = max_node_in_graph G -> In x (find_mediators_in_path (u, v, l) G) <->
  In (x + o) (find_mediators_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G)).
Proof.
  intros u v l G o x.
  unfold find_mediators_in_path. intros Ho. split.
  { intros Hmem.
  apply mediators_vs_edges_in_path in Hmem. destruct Hmem as [y [z Hmem]].
  destruct Hmem as [Hsub Hedge].
  apply mediators_vs_edges_in_path. exists (y + o). exists (z + o). split.
  - apply shift_maintains_subset with (o := o) in Hsub.
    replace (shift_nodes_by_offset [y; x; z] o) with ([y + o; x + o; z + o]) in Hsub.
    replace (shift_nodes_by_offset (u :: l ++ [v]) o) with (u + o :: (shift_nodes_by_offset l o) ++ [v + o]) in Hsub.
    + apply Hsub.
    + simpl. replace (shift_nodes_by_offset (l ++ [v]) o) with (shift_nodes_by_offset l o ++ [v + o]).
      * reflexivity.
      * apply shift_maintains_append with (l2 := [v]).
    + simpl. reflexivity.
  - destruct G as [V E]. simpl in Ho. split.
    + destruct Hedge as [Hyx _]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hyx.
    + destruct Hedge as [_ Hxz]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hxz. }
  { intros Hmem.
    apply mediators_vs_edges_in_path in Hmem. destruct Hmem as [y' [z' Hmem]].
    destruct Hmem as [Hsub Hedge].
    apply mediators_vs_edges_in_path.
    assert (Hshift: (@cons node (add u o)
               (@app node (shift_nodes_by_offset l o)
                  (@cons node (add v o) (@nil node)))) = (shift_nodes_by_offset (u :: l ++ [v]) o)).
      { simpl. rewrite <- shift_maintains_append. simpl. reflexivity. }
    rewrite Hshift in Hsub.
    assert (Hz: exists z, z + o = z').
      { exists (z' - o). assert (Hz': In z' (shift_nodes_by_offset (u :: l ++ [v]) o)).
        { apply sublist_member with (l1 := [y'; x + o; z']). split.
          - simpl. right. right. left. reflexivity.
          - apply Hsub. }
        apply shift_greater_than_offset in Hz'. lia. }
    assert (Hy: exists y, y + o = y').
    { exists (y' - o). assert (Hy': In y' (shift_nodes_by_offset (u :: l ++ [v]) o)).
      { apply sublist_member with (l1 := [y'; x + o; z']). split.
        - simpl. left. reflexivity.
        - apply Hsub. }
      apply shift_greater_than_offset in Hy'. lia. }
    destruct Hz as [z Hz]. destruct Hy as [y Hy].
    exists y. exists z. rewrite <- Hz in Hsub. rewrite <- Hy in Hsub.
    split.
    - replace ((@cons node (add y o)
               (@cons node (add x o) (@cons node (add z o) (@nil node))))) with (shift_nodes_by_offset [y; x; z] o) in Hsub.
      + apply shift_maintains_subset in Hsub. apply Hsub.
      + simpl. reflexivity.
    - split.
      + destruct Hedge as [Hedge _]. apply duplicate_graph_maintains_edges with (o := o).
        * apply Ho.
        * rewrite <- Hy in Hedge. apply Hedge.
      + destruct Hedge as [_ Hedge]. apply duplicate_graph_maintains_edges with (o := o).
        * apply Ho.
        * rewrite <- Hz in Hedge. apply Hedge. }
Qed.

Lemma duplicate_graph_maintains_confounders: forall (u v: node) (l: nodes) (G: graph) (o: nat) (x: node),
  o = max_node_in_graph G ->
  In x (find_confounders_in_path (u, v, l) G) <->
  In (x + o) (find_confounders_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G)).
Proof.
  intros u v l G o x.
  unfold find_confounders_in_path. intros Ho. split.
  { intros Hmem.
  apply confounders_vs_edges_in_path in Hmem. destruct Hmem as [y [z Hmem]].
  destruct Hmem as [Hsub Hedge].
  apply confounders_vs_edges_in_path. exists (y + o). exists (z + o). split.
  - apply shift_maintains_subset with (o := o) in Hsub.
    replace (shift_nodes_by_offset [y; x; z] o) with ([y + o; x + o; z + o]) in Hsub.
    replace (shift_nodes_by_offset (u :: l ++ [v]) o) with (u + o :: (shift_nodes_by_offset l o) ++ [v + o]) in Hsub.
    + apply Hsub.
    + simpl. replace (shift_nodes_by_offset (l ++ [v]) o) with (shift_nodes_by_offset l o ++ [v + o]).
      * reflexivity.
      * apply shift_maintains_append with (l2 := [v]).
    + simpl. reflexivity.
  - destruct G as [V E]. simpl in Ho. split.
    + destruct Hedge as [Hxy _]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hxy.
    + destruct Hedge as [_ Hxz]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hxz. }
  { intros Hmem.
  apply confounders_vs_edges_in_path in Hmem. destruct Hmem as [y' [z' Hmem]].
  destruct Hmem as [Hsub Hedge].
  apply confounders_vs_edges_in_path.
  assert (Hshift: (@cons node (add u o)
             (@app node (shift_nodes_by_offset l o)
                (@cons node (add v o) (@nil node)))) = (shift_nodes_by_offset (u :: l ++ [v]) o)).
    { simpl. rewrite <- shift_maintains_append. simpl. reflexivity. }
  rewrite Hshift in Hsub.
  assert (Hz: exists z, z + o = z').
    { exists (z' - o). assert (Hz': In z' (shift_nodes_by_offset (u :: l ++ [v]) o)).
      { apply sublist_member with (l1 := [y'; x + o; z']). split.
        - simpl. right. right. left. reflexivity.
        - apply Hsub. }
      apply shift_greater_than_offset in Hz'. lia. }
  assert (Hy: exists y, y + o = y').
  { exists (y' - o). assert (Hy': In y' (shift_nodes_by_offset (u :: l ++ [v]) o)).
    { apply sublist_member with (l1 := [y'; x + o; z']). split.
      - simpl. left. reflexivity.
      - apply Hsub. }
    apply shift_greater_than_offset in Hy'. lia. }
  destruct Hz as [z Hz]. destruct Hy as [y Hy].
  exists y. exists z. rewrite <- Hz in Hsub. rewrite <- Hy in Hsub.
  split.
  - replace ((@cons node (add y o)
             (@cons node (add x o) (@cons node (add z o) (@nil node))))) with (shift_nodes_by_offset [y; x; z] o) in Hsub.
    + apply shift_maintains_subset in Hsub. apply Hsub.
    + simpl. reflexivity.
  - split.
    + destruct Hedge as [Hedge _]. apply duplicate_graph_maintains_edges with (o := o).
      * apply Ho.
      * rewrite <- Hy in Hedge. apply Hedge.
    + destruct Hedge as [_ Hedge]. apply duplicate_graph_maintains_edges with (o := o).
      * apply Ho.
      * rewrite <- Hz in Hedge. apply Hedge. }
Qed.

Lemma duplicate_graph_maintains_single_collider: forall (u v c: node) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  is_collider_bool u v c G = true <-> 
  is_collider_bool (u + o) (v + o) (c + o) (duplicate_graph G) = true.
Proof.
  intros u v c G o Ho. split.
  - unfold is_collider_bool. intros H. apply split_and_true in H.
    destruct H as [Huc Hvc]. destruct G as [V E].
    apply duplicate_graph_maintains_edges with (o := o) in Huc.
    apply duplicate_graph_maintains_edges with (o := o) in Hvc.
    + unfold node. rewrite Huc. rewrite Hvc. reflexivity.
    + apply Ho.
    + apply Ho.
  - unfold is_collider_bool. intros H. apply split_and_true in H.
    destruct H as [Huc Hvc]. destruct G as [V E].
    apply duplicate_graph_maintains_edges with (o := o) in Huc.
    apply duplicate_graph_maintains_edges with (o := o) in Hvc.
    + rewrite Huc. rewrite Hvc. reflexivity.
    + apply Ho.
    + apply Ho.
Qed.

Lemma duplicate_graph_maintains_single_collider_f: forall (u v c: node) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  is_collider_bool u v c G = false <-> 
  is_collider_bool (u + o) (v + o) (c + o) (duplicate_graph G) = false.
Proof.
  intros u v c G o Ho. split.
  - intros H.
    destruct (is_collider_bool (u + o) (v + o) (c + o) (duplicate_graph G)) as [|] eqn:Hcol.
    + apply duplicate_graph_maintains_single_collider in Hcol.
      rewrite Hcol in H. discriminate H. apply Ho.
    + reflexivity.
  - intros H.
    destruct (is_collider_bool u v c G) as [|] eqn:Hcol.
    + apply duplicate_graph_maintains_single_collider with (o := o) in Hcol.
      rewrite Hcol in H. discriminate H. apply Ho.
    + reflexivity.
Qed.

Lemma duplicate_graph_maintains_colliders: forall (u v: node) (l: nodes) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  find_colliders_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G)
  = shift_nodes_by_offset (find_colliders_in_path (u, v, l) G) o.
Proof.
  intros u v l G o. intros Ho.
  generalize dependent v. generalize dependent u.
  unfold find_colliders_in_path.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - intros u v. destruct t as [| h' t'].
    + simpl. destruct (is_collider_bool u v h G) as [|] eqn:Hcol.
      * simpl. apply duplicate_graph_maintains_single_collider with (o := o) in Hcol.
        -- rewrite Hcol. reflexivity.
        -- apply Ho.
      * apply duplicate_graph_maintains_single_collider_f with (o := o) in Hcol.
        rewrite Hcol. simpl. reflexivity. apply Ho.
    + destruct t' as [| h'' t''].
      * simpl. destruct (is_collider_bool u h' h G) as [|] eqn:Hcol.
        -- apply duplicate_graph_maintains_single_collider with (o := o) in Hcol.
           rewrite Hcol. simpl. f_equal.
           destruct (is_collider_bool h v h' G) as [|] eqn:Hcol2.
           ++ apply duplicate_graph_maintains_single_collider with (o := o) in Hcol2.
              rewrite Hcol2. simpl. reflexivity. apply Ho.
           ++ apply duplicate_graph_maintains_single_collider_f with (o := o) in Hcol2.
              rewrite Hcol2. simpl. reflexivity. apply Ho.
           ++ apply Ho.
        -- apply duplicate_graph_maintains_single_collider_f with (o := o) in Hcol.
           rewrite Hcol. destruct (is_collider_bool h v h' G) as [|] eqn:Hcol2.
           ++ apply duplicate_graph_maintains_single_collider with (o := o) in Hcol2.
              rewrite Hcol2. simpl. reflexivity. apply Ho.
           ++ apply duplicate_graph_maintains_single_collider_f with (o := o) in Hcol2.
              rewrite Hcol2. simpl. reflexivity. apply Ho.
           ++ apply Ho.
      * destruct (is_collider_bool u h' h G) as [|] eqn:Hcol.
        -- simpl. rewrite Hcol.
           apply duplicate_graph_maintains_single_collider with (o := o) in Hcol.
           rewrite Hcol. simpl. f_equal. specialize (IH h v). apply IH. apply Ho.
        -- simpl. rewrite Hcol.
           apply duplicate_graph_maintains_single_collider_f with (o := o) in Hcol.
           rewrite Hcol. simpl. specialize (IH h v). apply IH. apply Ho.
Qed.

Lemma duplicate_graph_maintains_descendants: forall (u: node) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  find_descendants (u + o) (duplicate_graph G)
  = shift_nodes_by_offset (find_descendants u G) o.
Proof.
Admitted.

Theorem duplicate_graph_maintains_independence: forall G: graph, forall u v o: node, forall Z: nodes,
  o = max_node_in_graph G ->
  (exists p: path, path_start_and_end p u v = true
                  /\ node_in_graph u G = true /\ node_in_graph v G = true 
                  /\ d_connected_2 p G Z)
  <->
  (exists p': path, path_start_and_end p' (u + o) (v + o) = true /\ (exists int: nodes, path_int p' = shift_nodes_by_offset int o)
                  /\ node_in_graph (u + o) (duplicate_graph G) = true /\ node_in_graph (v + o) (duplicate_graph G) = true
                  /\ d_connected_2 p' (duplicate_graph G) (shift_nodes_by_offset Z o)).
Proof.
  intros G u v o Z. intros Ho. split.
  - intros [p [Hp [Hu [Hv Hconn]]]]. destruct p as [[u' v'] l]. apply path_start_end_equal in Hp. destruct Hp as [Hu' Hv'].
    rewrite Hu' in Hconn. rewrite Hv' in Hconn.
    exists (u + o, v + o, shift_nodes_by_offset l o).
    unfold d_connected_2. unfold d_connected_2 in Hconn. destruct Hconn as [Hmed [Hconf Hcol]]. repeat split.
    + apply path_start_end_refl.
    + exists l. simpl. reflexivity.
    + destruct G as [V E]. simpl. simpl in Hu. simpl in Ho. rewrite <- Ho.
      apply twin_nodes_duplicated. apply Hu.
    + destruct G as [V E]. simpl. simpl in Hv. simpl in Ho. rewrite <- Ho.
      apply twin_nodes_duplicated. apply Hv.
    + (* mediators *)
      apply shift_maintains_overlap with (o := o) in Hmed.
      apply no_overlap_non_member.
      intros x Hxmed HxZ.
      assert (Hol: forall x: node,
                   In x (shift_nodes_by_offset (find_mediators_in_path (u, v, l) G) o) -> ~(In x (shift_nodes_by_offset Z o))).
      { apply no_overlap_non_member. apply Hmed. }
      specialize (Hol x). apply Hol.
      { remember (x - o) as y.
        assert (Hox: o <= x). { apply shift_greater_than_offset in HxZ. apply HxZ. }
      replace x with (y + o) in Hxmed.
      * apply duplicate_graph_maintains_mediators with (x := y) in Hxmed.
        -- rewrite Heqy in Hxmed. apply shift_member. split. apply Hxmed. apply Hox.
        -- apply Ho.
      * rewrite Heqy. lia. }
      apply HxZ.
    + (* confounders *)
      apply shift_maintains_overlap with (o := o) in Hconf.
      apply no_overlap_non_member.
      intros x Hxconf HxZ.
      assert (Hol: forall x: node,
                   In x (shift_nodes_by_offset (find_confounders_in_path (u, v, l) G) o) -> ~(In x (shift_nodes_by_offset Z o))).
      { apply no_overlap_non_member. apply Hconf. }
      specialize (Hol x). apply Hol.
      { remember (x - o) as y.
        assert (Hox: o <= x). { apply shift_greater_than_offset in HxZ. apply HxZ. }
      replace x with (y + o) in Hxconf.
      * apply duplicate_graph_maintains_confounders with (x := y) in Hxconf.
        -- rewrite Heqy in Hxconf. apply shift_member. split. apply Hxconf. apply Hox.
        -- apply Ho.
      * rewrite Heqy. lia. }
      apply HxZ.
    + (* colliders *)
      unfold all_colliders_have_descendant_conditioned_on. apply forallb_forall.
      intros c' Hmem. unfold some_descendant_in_Z_bool.
      unfold all_colliders_have_descendant_conditioned_on in Hcol.
      replace (find_colliders_in_path (u + o, v + o, shift_nodes_by_offset l o)
          (duplicate_graph G)) with (shift_nodes_by_offset (find_colliders_in_path (u, v, l) G) o) in Hmem.
      apply shift_member in Hmem.
      destruct Hmem as [Hmem Hoc].
      assert (Hc': exists c, c' = c + o).
      { exists (c' - o). lia. }
      destruct Hc' as [c Hc'].
      assert (Hc: c = c' - o). { lia. } rewrite <- Hc in Hmem.
      assert (Hdesc: some_descendant_in_Z_bool (find_descendants c G) Z = true).
      { apply forallb_true with (l := (find_colliders_in_path (u, v, l) G))
              (test := (fun c: node => some_descendant_in_Z_bool (find_descendants c G) Z)).
        - apply Hmem.
        - apply Hcol. }
      unfold some_descendant_in_Z_bool in Hdesc.
      apply overlap_has_member_in_common in Hdesc. destruct Hdesc as [d [Hdesc HdZ]].
      remember (d + o) as d'.
      assert (Hdesc': In d' (find_descendants c' (duplicate_graph G))).
      { rewrite Hc'. rewrite duplicate_graph_maintains_descendants.
        rewrite Heqd'. apply shift_member. split.
        - assert (Hd': d' - o = d). { lia. } rewrite <- Hd' in Hdesc.
          rewrite Heqd' in Hdesc. apply Hdesc.
        - lia.
        - apply Ho. }
      assert (HdZ': In d' (shift_nodes_by_offset Z o)).
      { apply shift_member. split.
        - assert (Hd': d' - o = d). { lia. } rewrite <- Hd' in HdZ. apply HdZ.
        - lia. }
      apply overlap_has_member_in_common. exists d'. split.
      * apply Hdesc'.
      * apply HdZ'.
      * symmetry. apply duplicate_graph_maintains_colliders. apply Ho.
  - intros [p' [Hp [[l Hi] [Hu [Hv Hconn]]]]]. destruct p' as [[u' v'] l']. simpl in Hi.
    apply path_start_end_equal in Hp. destruct Hp as [Hu' Hv'].
    rewrite Hu' in Hconn. rewrite Hv' in Hconn.
    exists (u, v, l).
    unfold d_connected_2. unfold d_connected_2 in Hconn. destruct Hconn as [Hmed [Hconf Hcol]]. repeat split.
    + apply path_start_end_refl.
    + destruct G as [V E]. simpl. simpl in Hu. simpl in Ho. rewrite <- Ho in Hu.
      apply twin_nodes_duplicated in Hu. apply Hu.
    + destruct G as [V E]. simpl. simpl in Hv. simpl in Ho. rewrite <- Ho in Hv.
      apply twin_nodes_duplicated in Hv. apply Hv.
    + (* mediators *)
      apply no_overlap_non_member. intros m Hm HmZ.
      assert (Hm': In (m + o) (find_mediators_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G))).
      { apply duplicate_graph_maintains_mediators. apply Ho. apply Hm. }
      rewrite <- Hi in Hm'.
      assert (HmZ': In (m + o) (shift_nodes_by_offset Z o)).
      { remember (m + o) as m'. apply shift_member. split.
        - replace (m' - o) with m. apply HmZ. lia.
        - lia. }
      assert (contra: overlap (shift_nodes_by_offset Z o)
         (find_mediators_in_path (u + o, v + o, l') (duplicate_graph G)) = true).
      { apply overlap_has_member_in_common. exists (m + o). split.
        - apply HmZ'.
        - apply Hm'. }
      unfold node in Hmed. rewrite Hmed in contra. discriminate contra.
    + (* confounders *)
      apply no_overlap_non_member. intros c Hc HcZ.
      assert (Hc': In (c + o) (find_confounders_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G))).
      { apply duplicate_graph_maintains_confounders. apply Ho. apply Hc. }
      rewrite <- Hi in Hc'.
      assert (HcZ': In (c + o) (shift_nodes_by_offset Z o)).
      { remember (c + o) as c'. apply shift_member. split.
        - replace (c' - o) with c. apply HcZ. lia.
        - lia. }
      assert (contra: overlap (shift_nodes_by_offset Z o)
         (find_confounders_in_path (u + o, v + o, l') (duplicate_graph G)) = true).
      { apply overlap_has_member_in_common. exists (c + o). split.
        - apply HcZ'.
        - apply Hc'. }
      unfold node in Hconf. rewrite Hconf in contra. discriminate contra.
    + (* colliders *)
      unfold all_colliders_have_descendant_conditioned_on. apply forallb_forall.
      intros c Hmem. unfold some_descendant_in_Z_bool.
      unfold all_colliders_have_descendant_conditioned_on in Hcol.
      remember (c + o) as c'.
      assert (Hc': In c' (shift_nodes_by_offset (find_colliders_in_path (u, v, l) G) o)).
      { apply shift_member. split.
        - assert (Hc: c = c' - o). { lia. }
          rewrite <- Hc. apply Hmem.
        - lia. }
      replace (shift_nodes_by_offset (find_colliders_in_path (u, v, l) G) o) with
          (find_colliders_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G)) in Hc'.
      * assert (Hdesc: some_descendant_in_Z_bool (find_descendants c' (duplicate_graph G))
            (shift_nodes_by_offset Z o) = true).
        { apply forallb_true with (l := (find_colliders_in_path (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G)))
              (test := (fun c: node => some_descendant_in_Z_bool (find_descendants c (duplicate_graph G))
                (shift_nodes_by_offset Z o))) (x := c').
          - apply Hc'.
          - rewrite <- Hi. apply Hcol. }
        unfold some_descendant_in_Z_bool in Hdesc.
        apply overlap_has_member_in_common in Hdesc. destruct Hdesc as [d' [Hdesc' HdZ']].
        remember (d' - o) as d.
        assert (Hdesc: In d (find_descendants c G)).
        { rewrite Heqc' in Hdesc'. rewrite duplicate_graph_maintains_descendants in Hdesc'.
          apply shift_member in Hdesc'. destruct Hdesc' as [Hdesc' Hod'].
          rewrite <- Heqd in Hdesc'. apply Hdesc'. apply Ho. }
        assert (HdZ: In d Z).
        { apply shift_member in HdZ'. destruct HdZ' as [HdZ' Hod'].
          rewrite <- Heqd in HdZ'. apply HdZ'. }
        apply overlap_has_member_in_common. exists d. split.
        -- apply Hdesc.
        -- apply HdZ.
      * apply duplicate_graph_maintains_colliders. apply Ho.
Qed.

(* add unobserved confounders of each pair of corresponding nodes *)
Fixpoint get_unobserved_nodes_and_edges
  (V: nodes) (E: edges) (new_nodes: nodes) (new_edges: edges) (o: nat): graph :=
  match V with
  | [] => (new_nodes, new_edges)
  | h :: t => get_unobserved_nodes_and_edges t E ((h + o + o) :: new_nodes) ((h + o + o, h) :: (h + o + o, h + o) :: new_edges) o
  end.

(* create graph that duplicates original graph and adds unobserved nodes/edges *)
Definition create_duplicate_network (G: graph): graph :=
  match G with
  | (V, E) => let unobs := get_unobserved_nodes_and_edges V E [] [] (max_list V) in
              let dup := duplicate_graph G in
              (V ++ (fst dup) ++ (fst unobs), E ++ (snd dup) ++ (snd unobs))
  end.

Example duplicate_network_1: create_duplicate_network ([1; 2; 3], [(1, 2); (3, 2)])
  = ([1;2;3;4;5;6;9;8;7], [(1,2); (3,2); (4,5); (6,5); (9,3); (9,6); (8,2); (8,5); (7,1); (7,4)]).
Proof. reflexivity. Qed.

Fixpoint do_several (G: graph) (fixed: nodes): graph :=
  match fixed with
  | [] => G
  | h :: t => do_several (do h G) t
  end.

Fixpoint remove_unobserved (original_V: nodes) (new_nodes: nodes) (new_edges: edges) (o: nat) : graph :=
  match original_V with
  | [] => (new_nodes, new_edges)
  | h :: t => if (member_edge (h + o + o, h) new_edges && member_edge (h + o + o, h + o) new_edges) then remove_unobserved t new_nodes new_edges o
              else remove_unobserved t (filter (fun x => negb (x  =? h + o + o)) new_nodes) (filter (fun x => negb (fst x =? h + o + o)) new_edges) o
  end.

Definition create_initial_twin_network (G: graph) (obs: assignments) (cf: assignments): graph :=
  match G with
  | (V, E) => let duplicate_G := create_duplicate_network G in
              (do_several (do_several duplicate_G (fsts obs)) (shift_list (fsts cf) (max_list V)))
  end.

Example twin_1: create_initial_twin_network ([1;2;3], [(1, 2); (3, 2)]) [] [(1, 70)]
  = ([1;2;3;4;5;6;9;8;7], [(1,2); (3,2); (4,5); (6,5); (9,3); (9,6); (8,2); (8,5); (7,1)]).
Proof. reflexivity. Qed.

Definition create_twin_network_before_preprocess (G: graph) (obs: assignments) (cf: assignments): graph :=
  let init := create_initial_twin_network G obs cf in
  match G with
  | (V, E) => remove_unobserved V (fst init) (snd init) (max_list V)
  end.

Definition sequential_V: nodes := [1; 2; 3; 4; 5]. (* [A, H, B, Z, Y] *)
Definition sequential_E: edges := [(1, 4); (2, 4); (2, 3); (4, 3); (4, 5); (3, 5)].
Definition sequential_G: graph := (sequential_V, sequential_E).

Definition sequential_twin: graph := create_twin_network_before_preprocess sequential_G [] [(1, 1); (3, 2)].
Example sequential_twin_network: sequential_twin (* fix counterfactuals a=1, b=2 *)
  = ([1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 14; 12], sequential_E ++ [(6, 9); (7, 9); (9, 10); (8, 10)] ++ [(15, 5); (15, 10); (14, 4); (14, 9); (12, 2); (12, 7)]).
Proof. reflexivity. Qed.

Example sequential_twin_network_error: d_separated_bool 10 3 sequential_twin [4;1] = false.
Proof.
  apply d_separated_vs_connected.
  exists [9; 7; 12; 2].
  split.
  - simpl. split. easy. split.
    + intros H. destruct H as [H | [H | [H | [H | H]]]]. discriminate H. discriminate H. discriminate H. discriminate H. apply H.
    + split. intros H. destruct H as [H | [H | [H | [H | H]]]]. discriminate H. discriminate H. discriminate H. discriminate H. apply H. reflexivity.
  - split.
    + simpl. reflexivity.
    + unfold d_connected_2. split.
      * simpl. reflexivity.
      * split.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
Qed.


(*
PREPROCESSING:

compute topological ordering of original graph

for each node v in topo order:
  if for v and v', 1) parents are the same; 2) not both assigned a different value:
    merge v and v' into single node
    remove u if necessary
*)




