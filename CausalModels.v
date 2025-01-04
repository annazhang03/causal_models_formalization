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
              && forallb (fun v => count v V =? 1) V
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

Definition edge_in_graph (e: edge) (G: graph) : bool :=
  match G with
  | (V, E) => member_edge e E
  end.

Definition remove_associated_edges (u: node) (E: edges) : edges :=
  filter (fun edg => negb (snd edg =? u) && negb (fst edg =? u)) E.

Definition remove_node (u: node) (V: nodes) : nodes :=
  filter (fun v => negb (v =? u) ) V.

Lemma remove_node_from_well_formed: forall (V: nodes) (E: edges) (u: node),
  node_in_graph u (V, E) = true /\ G_well_formed (V, E) = true -> length V = S (length (remove_node u V)).
Proof.
Admitted.

Definition remove_node_from_graph (G: graph) (u: node) : graph :=
  match G with
  | (V, E) => (remove_node u V, remove_associated_edges u E)
  end.

Lemma remove_node_preserves_well_formed: forall (G: graph) (u: node),
  G_well_formed G = true -> G_well_formed (remove_node_from_graph G u) = true.
Proof.
  intros [V E] u H.
  unfold G_well_formed. simpl.
  unfold G_well_formed in H. apply split_and_true in H. destruct H as [He Hv].
  assert (He': forallb
    (fun e : nat * nat =>
     let (u0, v) := e in
     member u0 (remove_node u V) && member v (remove_node u V))
    (remove_associated_edges u E) = true).
  { apply forallb_true_iff_mem. intros [e1 e2]. intros Hmem.
    unfold remove_associated_edges in Hmem. apply filter_true in Hmem.
    destruct Hmem as [Hmem Heq].
    simpl in Heq. apply split_and_true in Heq. destruct Heq as [He2 He1].
    unfold remove_node.
    assert (HVmem: forall x: nat * nat, In x E -> (let (u, v) := x in member u V && member v V) = true).
    { apply forallb_true_iff_mem. apply He. }
    specialize HVmem with (x := (e1, e2)). apply HVmem in Hmem.
    apply split_and_true in Hmem. destruct Hmem as [He1V He2V].
    assert (He1mem: In e1 (filter (fun v : nat => negb (v =? u)) V)).
    { apply filter_true. split.
      - apply member_In_equiv. apply He1V.
      - apply He1. }
    assert (He2mem: In e2 (filter (fun v : nat => negb (v =? u)) V)).
    { apply filter_true. split.
      - apply member_In_equiv. apply He2V.
      - apply He2. }
    apply member_In_equiv in He1mem. apply member_In_equiv in He2mem.
    rewrite He1mem. rewrite He2mem. reflexivity. }
  rewrite He'. simpl.
  apply forallb_true_iff_mem. intros x Hmem.
  unfold remove_node in Hmem. apply filter_true in Hmem. destruct Hmem as [Hmem Hxu].
  unfold remove_node.
  assert (H: count x V = count x (filter (fun v : nat => negb (v =? u)) V)).
  { apply count_filter. apply Hxu. }
  rewrite <- H.
  assert (HVc: forall x: nat, In x V -> (count x V =? 1) = true).
  { apply forallb_true_iff_mem. apply Hv. }
  specialize HVc with (x := x). apply HVc in Hmem. apply Hmem.
Qed.

Definition num_nodes (G: graph) : nat :=
  match G with
  | (V, E) => length V
  end.

Theorem edge_corresponds_to_nodes_in_well_formed: forall (G: graph) (u v: node),
  G_well_formed G = true /\ edge_in_graph (u, v) G = true
  -> node_in_graph u G = true /\ node_in_graph v G = true.
Proof.
  intros [V E] u v [HG Hedge].
  unfold G_well_formed in HG. apply split_and_true in HG. destruct HG as [HG _].
  apply forallb_true with (x:=(u,v)) in HG.
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

Lemma first_node_in_path_in_graph: forall (G: graph) (l: nodes) (s e: node),
  is_path_in_graph_helper ((s :: l) ++ [e]) G = true -> node_in_graph s G = true.
Proof.
  intros G l s e Hpath.
  destruct G as [V E].
  simpl in Hpath. destruct (l ++ [e]) as [| h t] eqn:Hl.
  * destruct l as [| h' t']. 
    -- simpl in Hl. discriminate Hl.
    -- simpl in Hl. discriminate Hl.
  * apply split_and_true in Hpath. destruct Hpath as [Hpath _].
    apply split_orb_true in Hpath as [Hpath | Hpath].
    -- apply split_and_true in Hpath. destruct Hpath as [Hpath _].
       apply split_and_true in Hpath. destruct Hpath as [Hpath _].
       simpl. apply Hpath.
    -- apply split_and_true in Hpath. destruct Hpath as [Hpath _].
       apply split_and_true in Hpath. destruct Hpath as [_ Hpath].
       simpl. apply Hpath.
Qed.

Lemma last_node_in_path_in_graph: forall (G: graph) (l: nodes) (s e: node),
  (length ((s :: l) ++ [e]) > 1) /\ is_path_in_graph_helper ((s :: l) ++ [e]) G = true -> node_in_graph e G = true.
Proof.
  intros G l s e [Hlen Hpath].
  induction (s :: l) as [| h t IH].
  - simpl in Hlen. lia.
  - destruct t as [| h' t'].
    + simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [H _].
      apply split_orb_true in H. destruct H as [H | H].
      * unfold is_edge in H. apply split_and_true in H. destruct H as [H _].
        apply split_and_true in H. destruct H as [_ H]. simpl. apply H.
      * unfold is_edge in H. apply split_and_true in H. destruct H as [H _].
        apply split_and_true in H. destruct H as [H _]. simpl. apply H.
    + apply IH.
      * simpl. rewrite app_length. simpl. lia.
      * simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ H]. apply H.
Qed.

Lemma middle_node_in_path_in_graph: forall (G: graph) (l: nodes) (s x e: node),
  In x (s :: l) -> (length ((s :: l) ++ [e]) > 1) /\ is_path_in_graph_helper ((s :: l) ++ [e]) G = true -> node_in_graph x G = true.
Proof.
  intros G l s x e Hmem [Hlen Hpath].
  induction (s :: l) as [| h t IH].
  - simpl in Hlen. lia.
  - simpl in Hmem. destruct Hmem as [Hhx | Hmem].
    + rewrite <- Hhx. apply first_node_in_path_in_graph with (s := h) (l := t) (e := e). apply Hpath.
    + destruct t as [| h1 t1].
      * simpl in Hmem. exfalso. apply Hmem.
      * apply IH.
        -- apply Hmem.
        -- simpl. rewrite app_length. simpl. lia.
        -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ H].
           apply H.
Qed.

Definition is_path_in_graph (p: path) (G: graph) : bool :=
  match p with
  | (u, v, l) => is_path_in_graph_helper ((u :: l) ++ [v]) G
  end.

Lemma nodes_in_graph_in_V: forall (G: graph) (p: path) (u: node),
  node_in_path u p = true /\ is_path_in_graph p G = true -> node_in_graph u G = true.
Proof.
  intros G [[s e] l] u. intros [Hnode Hpath].
  unfold node_in_path in Hnode. apply split_orb_true in Hnode. destruct Hnode as [Hse | Hint].
  - apply split_orb_true in Hse. destruct Hse as [Hs | He].
    + simpl in Hs. unfold is_path_in_graph in Hpath. destruct G as [V E].
      apply eqb_eq in Hs. rewrite Hs.
      apply first_node_in_path_in_graph with (l := l) (e := e). apply Hpath.
    + simpl in He. unfold is_path_in_graph in Hpath. destruct G as [V E].
      apply eqb_eq in He. rewrite He.
      apply last_node_in_path_in_graph with (s := s) (l := l). split.
      * simpl. rewrite app_length. simpl. lia.
      * apply Hpath.
  - simpl in Hint. unfold is_path_in_graph in Hpath. destruct G as [V E].
    apply middle_node_in_path_in_graph with (x := u) (s := s) (l := l) (e := e).
    + simpl. right. apply member_In_equiv. apply Hint.
    + split.
      * simpl. rewrite app_length. simpl. lia.
      * apply Hpath.
Qed.

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
  match G with
  | (V, E) => filter (fun p => v =? path_end p)
          (extend_paths_from_start_iter E (edges_as_paths_from_start u E) (length V))
  end.

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

Lemma remove_node_preserves_acyclic: forall (G: graph) (u: node),
  contains_cycle G = false -> contains_cycle (remove_node_from_graph G u) = false.
Proof.
Admitted.

Theorem contains_cycle_true_correct : forall G: graph,
  (exists p: path, is_path_in_graph p G = true /\ ~(acyclic_path_2 p))
  <-> contains_cycle G = true.
Proof.
Admitted.

Theorem contains_cycle_false_correct : forall G: graph, forall p: path,
  contains_cycle G = false -> ((is_path_in_graph p G = true) -> acyclic_path_2 p).
Proof.
  intros G p.
  pose proof contains_cycle_true_correct as cycle_true.
  specialize (cycle_true G).
  intros Hcyc Hpath.
  destruct (classic (acyclic_path_2 p)) as [HnC | HC].
  - apply HnC.
  - assert (H: (exists p' : path, is_path_in_graph p' G = true /\ ~ acyclic_path_2 p')).
    { exists p. split. apply Hpath. apply HC. }
    apply cycle_true in H. rewrite H in Hcyc. discriminate Hcyc.
Qed.

Lemma acyclic_no_self_loop: forall (G: graph) (u: node),
  contains_cycle G = false -> is_edge (u, u) G = false.
Proof.
  intros G u Hcyc.
  destruct (is_edge (u, u) G) as [|] eqn:Hedge.
  - apply contains_cycle_false_correct with (p := (u, u, [])) in Hcyc.
    + simpl in Hcyc. destruct Hcyc as [Hcyc _]. unfold not in Hcyc.
        exfalso. apply Hcyc. reflexivity.
    + destruct G as [V E]. simpl. unfold is_edge in Hedge. rewrite Hedge. simpl. reflexivity.
  - reflexivity.
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


(* Topological sort *)

Definition get_indegree (u: node) (G: graph): nat :=
  length (find_parents u G).

Definition get_indegree_zero (G: graph): nodes :=
  match G with
  | (V, E) => filter (fun v => (get_indegree v G) =? 0) V
  end.

Fixpoint construct_path (G: graph) (p: path) (iters: nat) : path :=
  match iters with
  | 0 => p
  | S iters' => match p with
                | (u, v, l) => match (find_parents u G) with
                               | [] => p
                               | h :: t => (construct_path G (h, v, u :: l) iters')
                               end
                end
  end.

Definition contains_any_node (G: graph): bool :=
  match G with
  | (V, E) => negb (eqblist V [])
  end.

Theorem constructed_path_in_graph: forall (G: graph) (p: path) (iters: nat),
  G_well_formed G = true -> is_path_in_graph p G = true -> is_path_in_graph (construct_path G p iters) G = true.
Proof.
  intros G p iters Hwf H.
  generalize dependent p. induction iters as [| iters' IH].
  - intros p H. simpl. apply H.
  - intros p H. destruct p as [[u v] l]. simpl. destruct (find_parents u G) as [| h t] eqn:HP.
    + apply H.
    + specialize IH with (p := (h, v, u :: l)). apply IH.
      destruct G as [V E]. simpl in H. simpl. rewrite H.
      assert (Hedge: edge_in_graph (h, u) (V, E) = true).
      { apply edge_from_parent_to_child. rewrite HP. simpl. left. reflexivity. }
      simpl in Hedge. rewrite Hedge.
      assert (Hnode: node_in_graph h (V, E) = true /\ node_in_graph u (V, E) = true).
      { apply edge_corresponds_to_nodes_in_well_formed. split.
        - apply Hwf.
        - simpl. apply Hedge. }
      simpl in Hnode. destruct Hnode as [Hh Hu]. rewrite Hh. rewrite Hu. simpl. reflexivity.
Qed.

Theorem constructed_path_adds_length_iters: forall (G: graph) (p: path) (iters: nat),
  G_well_formed G = true /\ is_path_in_graph p G = true /\ get_indegree_zero G = []
  -> measure_path (construct_path G p iters) = (measure_path p) + iters.
Proof.
  intros G p iters [Hwf [Hpath Hindeg]].
  generalize dependent p. induction iters as [| iters' IH].
  - intros p Hpath. simpl. rewrite add_0_r. reflexivity.
  - intros p Hpath. destruct p as [[u v] l]. simpl. destruct (find_parents u G) as [| h t] eqn:HP.
    + (* contradiction: u should be in get_indegree_zero G = [] *)
      assert (contra: In u (get_indegree_zero G)).
      { destruct G as [V E]. unfold get_indegree_zero.
        apply filter_true. split.
        - assert (Hu: node_in_graph u (V, E) = true).
          { apply first_node_in_path_in_graph with (e := v) (l := l). unfold is_path_in_graph in Hpath. apply Hpath. }
          simpl in Hu. apply member_In_equiv. apply Hu.
        - unfold get_indegree. rewrite HP. simpl. reflexivity. }
      rewrite Hindeg in contra. exfalso. simpl in contra. apply contra.
    + specialize IH with (p := (h, v, u :: l)). rewrite IH.
      * simpl. lia.
      * destruct G as [V E]. simpl. unfold is_path_in_graph in Hpath. simpl in Hpath.
        rewrite Hpath.
        assert (Hhu: edge_in_graph (h, u) (V, E) = true).
        { apply edge_from_parent_to_child. rewrite HP. simpl. left. reflexivity. }
        simpl in Hhu. rewrite Hhu.
        assert (Hnode: node_in_graph h (V, E) = true /\ node_in_graph u (V, E) = true).
        { apply edge_corresponds_to_nodes_in_well_formed. split.
          - apply Hwf.
          - simpl. apply Hhu. }
        simpl in Hnode. destruct Hnode as [Hh Hu]. rewrite Hh. rewrite Hu. simpl. reflexivity.
Qed.

Theorem pigeonhole: forall (V: nodes) (V': nodes),
  (forall (u: node), In u V' -> In u V) /\ (length V < length V') -> exists (v: node), (count v V' > 1).
Proof.
  intros V V'. intros [Hu Hlen].
  generalize dependent V. induction V' as [| h' t' IH].
  - intros V Hu Hlen. simpl in Hlen. lia.
  - intros V Hu Hlen. destruct (member h' t') as [|] eqn:Hmem.
    + exists h'. simpl. rewrite eqb_refl.
      assert (Hc: count h' t' >= 1).
      { apply member_count_at_least_1. apply member_In_equiv. apply Hmem. }
      lia.
    + specialize IH with (V := (filter (fun v : nat => negb (v =? h')) V)).
      assert (H: exists v : node, count v t' > 1).
      { apply IH.
        - intros u Hmem2. apply filter_true. split.
          + apply Hu with (u := u). simpl. right. apply Hmem2.
          + destruct (u =? h') as [|] eqn:H.
            * apply eqb_eq in H. rewrite H in Hmem2. apply member_In_equiv in Hmem2. rewrite Hmem2 in Hmem. discriminate Hmem.
            * simpl. reflexivity.
        - assert (Hlen': S (length (filter (fun v : nat => negb (v =? h')) V)) <= length V).
          { apply filter_length_membership. apply Hu with (u := h'). simpl. left. reflexivity. }
          simpl in Hlen. apply succ_lt_mono. apply le_lt_trans with (m := (length V)).
          + apply Hlen'.
          + apply Hlen. }
      destruct H as [v H]. exists v. simpl. destruct (h' =? v) as [|] eqn:Hhv.
      -- lia.
      -- apply H.
Qed.

Theorem acyclic_has_indegree_zero: forall (G: graph),
  G_well_formed G = true /\ contains_any_node G = true /\ contains_cycle G = false
  -> exists u, ((node_in_graph u G) && (get_indegree u G =? 0)) = true.
Proof.
  intros G [HGwf [Hnode Hcyc]].
  destruct G as [V E] eqn: HG.
  destruct (get_indegree_zero (V, E)) as [| h t] eqn:Hindeg.
  - (* assume there are 0 nodes with indegree 0. Show a contradiction by showing that G is cyclic. *)
    destruct V as [| v V'] eqn:HV.
    + simpl in Hnode. discriminate Hnode.
    + destruct (get_indegree v G) as [| n'] eqn:Hvindeg.
      * exists v. simpl. rewrite eqb_refl. rewrite <- HG. rewrite Hvindeg. rewrite eqb_refl. reflexivity.
      * unfold get_indegree in Hvindeg. apply length_member in Hvindeg. destruct Hvindeg as [p Hp].
        apply edge_from_parent_to_child in Hp.
        assert (HpV: node_in_graph p G = true /\ node_in_graph v G = true).
        { apply edge_corresponds_to_nodes_in_well_formed. split. rewrite HG. apply HGwf. apply Hp. }
        destruct HpV as [HpV _].
        remember (construct_path G (p, v, []) (length V)) as cycle. (* extend (p, v) backwards |V| times *)
        assert (Hpath: is_path_in_graph cycle G = true).
        { rewrite Heqcycle. apply constructed_path_in_graph. rewrite HG. apply HGwf. rewrite HG. simpl.
          rewrite HG in HpV. simpl in HpV. rewrite HpV. rewrite eqb_refl.
          rewrite HG in Hp. simpl in Hp. rewrite Hp. simpl. reflexivity. }
        assert (Hrepeat: exists (r: node), (count r ([path_start cycle; path_end cycle] ++ (path_int cycle)) > 1)).
        { apply pigeonhole with (V := V). split.
          - intros x Hx.
            assert (Heq: node_in_graph x G = true).
            { apply nodes_in_graph_in_V with (p := cycle). split.
              - unfold node_in_path. simpl in Hx.
                destruct Hx as [Hs | [He | Hint]].
                + rewrite Hs. rewrite eqb_refl. simpl. reflexivity.
                + rewrite He. rewrite eqb_refl. simpl.
                  apply split_orb_true. left. apply split_orb_true. right. reflexivity.
                + apply member_In_equiv in Hint. rewrite Hint. apply split_orb_true. right. reflexivity.
              - apply Hpath. }
            rewrite HG in Heq. rewrite <- HV in Heq. simpl in Heq. apply member_In_equiv. apply Heq.
          - assert (Hlen: measure_path cycle = 2 + (length V)).
            { rewrite Heqcycle. apply constructed_path_adds_length_iters. repeat split.
              - rewrite HG. apply HGwf.
              - rewrite HG. simpl. rewrite eqb_refl.
                assert (Hmemp: node_in_graph p G = true /\ node_in_graph v G = true).
                { apply edge_corresponds_to_nodes_in_well_formed. split.
                  - rewrite HG. apply HGwf.
                  - apply Hp. } destruct Hmemp as [Hmemp _].
                rewrite HG in Hmemp. simpl in Hmemp. rewrite Hmemp. rewrite HG in Hp. simpl in Hp. rewrite Hp.
                simpl. reflexivity.
              - rewrite HG. apply Hindeg. }
            destruct cycle as [[s e] l]. unfold measure_path in Hlen. simpl.
            apply add_cancel_l in Hlen. rewrite Hlen. lia. }
        assert (Hcycle: ~(acyclic_path_2 cycle)).
        { unfold not. intros H. apply acyclic_path_correct in H. destruct Hrepeat as [r Hrepeat].
          apply acyclic_path_intermediate_nodes with (x := r) in H. destruct H as [H0 | H1].
          - rewrite H0 in Hrepeat. lia.
          - rewrite H1 in Hrepeat. lia. }
        assert (contra: contains_cycle G = true).
        { apply contains_cycle_true_correct. exists cycle. split.
          - apply Hpath.
          - apply Hcycle. }
        rewrite HG in contra. rewrite Hcyc in contra. discriminate contra.
  - exists h.
    unfold get_indegree_zero in Hindeg.
    assert (Hh: In h (filter
           (fun v : node =>
            get_indegree v (V, E) =? 0) V)). { rewrite Hindeg. simpl. left. reflexivity. }
    apply filter_true in Hh. unfold node_in_graph. rewrite <- member_In_equiv in Hh.
    destruct Hh as [HhV Hhdeg]. rewrite HhV. rewrite Hhdeg. reflexivity.
Qed.

Fixpoint topological_sort_helper (G: graph) (iters: nat) : option nodes :=
  match iters with
  | 0 => Some []
  | S iters' => let ind := get_indegree_zero G in
                match ind with
                | [] => None (* G contains cycle *)
                | h :: t => let rec := topological_sort_helper (remove_node_from_graph G h) iters' in
                            match rec with
                            | None => None
                            | Some r => Some (h :: r)
                            end
                end
  end.

Definition topological_sort (G: graph) : option nodes :=
  match G with
  | (V, E) => topological_sort_helper G (length V)
  end.

Definition V_topo: nodes := [3; 1; 2; 0; 4; 5].
Definition E_topo: edges := [(5, 0); (5, 2); (2, 3); (3, 1); (4, 0); (4, 1)].

Example toposort_1: topological_sort (V_topo, E_topo) = Some [4; 5; 2; 3; 1; 0].
Proof. reflexivity. Qed.

Lemma topo_sort_subgraph: forall (G: graph) (u: node) (ts: nodes),
  G_well_formed G = true /\ node_in_graph u G = true
  -> topological_sort G = Some (u :: ts) -> topological_sort (remove_node_from_graph G u) = Some ts.
Proof.
  intros [V E] u ts [Hwf Hu] H.
  unfold topological_sort in H.
  destruct (length V) as [| l'] eqn:Hlen.
  - simpl in H. inversion H.
  - simpl in H. destruct (get_indegree_zero (V, E)) as [| h t] eqn:Hind.
    + unfold get_indegree_zero in Hind. rewrite Hind in H. discriminate H.
    + unfold get_indegree_zero in Hind. rewrite Hind in H. 
      destruct (topological_sort_helper (remove_node h V, remove_associated_edges h E) l') as [r|] eqn:Hr.
      * inversion H. unfold topological_sort. simpl. rewrite <- H1.
        assert (Hlen': length V = S (length (remove_node h V))).
        { apply remove_node_from_well_formed with (E := E). split.
          - rewrite H1. apply Hu.
          - apply Hwf. }
        rewrite Hlen in Hlen'. inversion Hlen'. rewrite <- H3. rewrite <- H2. apply Hr.
      * discriminate H.
Qed.

Lemma topo_sort_exists_for_acyclic_helper: forall (G: graph) (iters: nat),
  G_well_formed G = true /\ contains_any_node G = true /\ iters <= num_nodes G ->
  contains_cycle G = false
  -> exists sorted: nodes, topological_sort_helper G iters = Some sorted.
Proof.
  intros G iters. intros [Hwf [Hnode Hiters]].
  intros Hcyc.
  generalize dependent G. induction iters as [| iters' IH].
  + intros G Hwf Hnode Hiters Hcyc. simpl. exists []. reflexivity.
  + intros [V E] Hwf Hnode Hiters Hcyc. simpl. destruct (filter (fun v : node => get_indegree v (V, E) =? 0) V) as [| h t] eqn:Hind.
    * assert (contra: exists u, ((node_in_graph u (V, E)) && (get_indegree u (V, E) =? 0)) = true).
      { apply acyclic_has_indegree_zero. repeat split.
        - apply Hwf.
        - apply Hnode.
        - apply Hcyc. }
      destruct contra as [u contra].
      assert (contra': In u (filter (fun v : node => get_indegree v (V, E) =? 0) V)).
      { apply filter_true. apply split_and_true in contra. simpl in contra. rewrite <- member_In_equiv. apply contra. }
      rewrite Hind in contra'. exfalso. simpl in contra'. apply contra'.
    * destruct iters' as [| iters''] eqn:Hiters'.
      -- simpl. exists [h]. reflexivity.
      -- specialize IH with (G := (remove_node h V, remove_associated_edges h E)).
         assert (Hlen: length V = S (length (remove_node h V))).
          { apply remove_node_from_well_formed with (E := E). split.
            - simpl. assert (H: In h (filter (fun v : node => get_indegree v (V, E) =? 0) V)).
              { rewrite Hind. simpl. left. reflexivity. }
              apply filter_true in H. destruct H as [H _]. apply member_In_equiv. apply H.
            - apply Hwf. }
      assert (H: exists sorted : nodes,
          topological_sort_helper (remove_node_from_graph (V, E) h) iters' = Some sorted).
      { rewrite Hiters'. apply IH.
        - apply remove_node_preserves_well_formed with (u := h) in Hwf. simpl in Hwf. apply Hwf.
        - simpl. simpl in Hiters.
          rewrite Hlen in Hiters. destruct (remove_node h V) as [| h' t'].
          + simpl in Hiters. lia.
          + simpl. reflexivity.
        - simpl. simpl in Hiters. lia.
        - apply remove_node_preserves_acyclic with (u := h) in Hcyc. apply Hcyc. }
      destruct H as [r H]. simpl in H. rewrite Hiters' in H. rewrite H. exists (h :: r). reflexivity.
Qed.

Lemma topo_sort_exists_for_acyclic: forall (G: graph),
  G_well_formed G = true /\ contains_cycle G = false -> exists sorted: nodes, topological_sort G = Some sorted.
Proof.
  intros [V E].
  intros [Hwf Hcyc].
  unfold topological_sort. destruct (length V) as [| l'] eqn:Hlen.
  + simpl. exists []. reflexivity.
  + apply topo_sort_exists_for_acyclic_helper.
    * repeat split.
      -- apply Hwf.
      -- simpl. destruct V as [| h t].
         ++ simpl in Hlen. discriminate Hlen.
         ++ simpl. reflexivity.
      -- simpl. rewrite Hlen. lia.
    * apply Hcyc.
Qed.

Lemma topo_sort_length_correct_helper: forall (G: graph) (iters: nat) (sorted: nodes),
  topological_sort_helper G iters = Some sorted -> length sorted = iters.
Proof.
  intros G iters sorted H.
  generalize dependent G. generalize dependent sorted. induction iters as [| iters' IH].
  - intros sorted G H. simpl in H. inversion H. simpl. reflexivity.
  - intros sorted G H. simpl in H. destruct (get_indegree_zero G) as [| h t].
    + discriminate H.
    + destruct (topological_sort_helper (remove_node_from_graph G h) iters') as [r|] eqn:Hr.
      * specialize IH with (sorted := r) (G := (remove_node_from_graph G h)).
        apply IH in Hr. inversion H. simpl. rewrite Hr. reflexivity.
      * discriminate H.
Qed.

Lemma topo_sort_length_correct: forall (G: graph) (sorted: nodes),
  topological_sort G = Some sorted -> length sorted = num_nodes G.
Proof.
  intros G sorted H.
  unfold topological_sort in H. destruct G as [V E].
  apply topo_sort_length_correct_helper in H. simpl. apply H.
Qed.

Lemma topo_sort_contains_nodes_helper: forall (G: graph) (iters: nat) (sorted: nodes),
  iters >= num_nodes G /\ topological_sort_helper G iters = Some sorted ->
  forall (u: node), (In u sorted <-> node_in_graph u G = true).
Proof.
  intros G iters sorted [Hiters Hts].
  intros u. split.
  - intros Hmem. generalize dependent G. generalize dependent sorted.
    induction iters as [| iters' IH].
    + intros sorted Hmem G Hiters Hts. simpl in Hts. inversion Hts. rewrite <- H0 in Hmem. simpl in Hmem.
      exfalso. apply Hmem.
    + intros sorted Hmem G Hiters Hts. simpl in Hts. destruct (get_indegree_zero G) as [| h t] eqn:Hd.
      * discriminate Hts.
      * destruct (topological_sort_helper (remove_node_from_graph G h) iters') as [r|] eqn:Hr.
        -- inversion Hts. rewrite <- H0 in Hmem. simpl in Hmem.
           assert (Hmemh: node_in_graph h G = true).
           { unfold get_indegree_zero in Hd. destruct G as [V E].
              assert (H: In h (filter (fun v : node => get_indegree v (V, E) =? 0) V)).
              { rewrite Hd. simpl. left. reflexivity. }
              apply filter_true in H. destruct H as [H _]. simpl.
              apply member_In_equiv. apply H. }
           destruct Hmem as [Hhu | Hind].
           ++ unfold get_indegree_zero in Hd. rewrite Hhu in Hmemh. apply Hmemh.
           ++ specialize IH with (sorted := r) (G := (remove_node_from_graph G h)).
              apply IH in Hind. destruct G as [V E].
              ** simpl in Hind. unfold remove_node in Hind.
                 apply member_In_equiv in Hind. apply filter_true in Hind. destruct Hind as [Hind _].
                 simpl. apply member_In_equiv. apply Hind.
              ** destruct G as [V E]. simpl in Hiters. simpl.
                 assert (H: S (length (remove_node h V)) <= length V).
                 { unfold remove_node. apply filter_length_membership. simpl in Hmemh. apply member_In_equiv. apply Hmemh. }
                 lia.
              ** apply Hr.
        -- discriminate Hts.
  - intros Hnode. generalize dependent G. generalize dependent sorted.
    induction iters as [| iters' IH].
    + intros sorted G Hiters Hts Hnode.
      destruct G as [V E]. simpl in Hiters. simpl in Hnode.
      destruct (length V) as [| l] eqn:Hl.
      * destruct V as [| h t] eqn:HV.
        -- simpl in Hnode. discriminate Hnode.
        -- simpl in Hl. discriminate Hl.
      * lia.
    + intros sorted G Hiters Hts Hnode. simpl in Hts.
      destruct (get_indegree_zero G) as [| h t] eqn:Hd.
      * discriminate Hts.
      * destruct (topological_sort_helper (remove_node_from_graph G h) iters') as [r|] eqn:Hr.
        -- inversion Hts. destruct G as [V E]. simpl in Hnode.
           destruct (u =? h) as [|] eqn:Huh.
           ++ apply eqb_eq in Huh. rewrite Huh. simpl. left. reflexivity.
           ++ assert (Hmem: node_in_graph u (remove_node_from_graph (V, E) h) = true).
              { simpl. unfold remove_node. apply member_In_equiv.
                apply filter_true. split.
                - apply member_In_equiv. apply Hnode.
                - rewrite Huh. simpl. reflexivity. }
              specialize IH with (sorted := r) (G := (remove_node_from_graph (V, E) h)).
              simpl. right. apply IH.
              ** simpl in Hiters. simpl.
                 assert (Hmemh: node_in_graph h (V, E) = true).
                 { unfold get_indegree_zero in Hd.
                    assert (H: In h (filter (fun v : node => get_indegree v (V, E) =? 0) V)).
                    { rewrite Hd. simpl. left. reflexivity. }
                    apply filter_true in H. destruct H as [H _]. simpl.
                    apply member_In_equiv. apply H. }
                 assert (H: S (length (remove_node h V)) <= length V).
                 { unfold remove_node. apply filter_length_membership. simpl in Hmemh. apply member_In_equiv. apply Hmemh. }
                 lia.
              ** apply Hr.
              ** apply Hmem.
        -- discriminate Hts.
Qed.

Lemma topo_sort_contains_nodes: forall (G: graph) (sorted: nodes),
  topological_sort G = Some sorted ->
  forall (u: node), (In u sorted <-> node_in_graph u G = true).
Proof.
  intros G sorted Hts.
  intros u.
  apply topo_sort_contains_nodes_helper with (iters := (num_nodes G)).
  split.
  - apply le_n.
  - destruct G as [V E]. unfold topological_sort in Hts. simpl. apply Hts.
Qed.

Lemma topo_sort_contains_nodes_exactly_once: forall (G: graph) (sorted: nodes),
  G_well_formed G = true /\ topological_sort G = Some sorted -> 
  forall (u: node), node_in_graph u G = true -> count u sorted = 1.
Proof.
  intros G ts [Hwf Hts].
  assert (HV: forall (u: node), In u (nodes_in_graph G) -> count u (nodes_in_graph G) = 1).
  { intros u Hmem. destruct G as [V E].
    unfold G_well_formed in Hwf. apply split_and_true in Hwf. destruct Hwf as [_ Hwf].
    apply forallb_true_iff_mem with (x := u) in Hwf.
    - simpl. apply eqb_eq in Hwf. apply Hwf.
    - simpl in Hmem. apply Hmem. }
  assert (HVts: forall (u: node), count u (nodes_in_graph G) = count u ts).
  { intros u.
    apply topo_sort_length_correct in Hts as Hlen.
    generalize dependent G. induction ts as [| h t IH].
    - intros G Hwf Hts Hu Hlen. simpl. simpl in Hlen. destruct G as [V E]. destruct V as [| h1 t1].
      + simpl. reflexivity.
      + discriminate Hlen.
    - intros G Hwf Hts Hnode Hlen. simpl.
      specialize IH with (G := remove_node_from_graph G h).
      assert (H: count u (nodes_in_graph (remove_node_from_graph G h)) = count u t).
      { apply IH.
        - apply remove_node_preserves_well_formed. apply Hwf.
        - apply topo_sort_subgraph.
          + split. apply Hwf.
            apply topo_sort_contains_nodes with (u := h) in Hts. apply Hts. simpl. left. reflexivity.
          + apply Hts.
        - intros u1 Hmem. destruct G as [V E]. simpl in Hmem. simpl.
          unfold remove_node in Hmem. apply filter_true in Hmem. destruct Hmem as [Hmem Huu1].
          simpl in Hnode. specialize Hnode with (u := u1). apply Hnode in Hmem.
          unfold remove_node. 
          assert (H1: count u1 V = count u1 (filter (fun v : nat => negb (v =? h)) V)).
          { apply count_filter. apply Huu1. }
          rewrite <- H1. apply Hmem.
        - destruct G as [V E]. simpl. simpl in Hnode.
          specialize Hnode with (u := h). simpl in Hlen.
          assert (H1: length V = S (length (filter (fun v : nat => negb (v =? h)) V))).
          { apply count_length. apply Hnode.
            apply topo_sort_contains_nodes with (u := h) in Hts. simpl in Hts.
            apply member_In_equiv. apply Hts. left. reflexivity. }
          rewrite H1 in Hlen. inversion Hlen. unfold remove_node. apply H0. }
      destruct (h =? u) as [|] eqn:Hhu.
      + destruct G as [V E]. simpl. simpl in H. simpl in Hnode.
        assert (HcV: count u V = 1).
        { apply topo_sort_contains_nodes with (u := h) in Hts. simpl in Hts.
          specialize Hnode with (u := u). apply Hnode.
          apply member_In_equiv. apply eqb_eq in Hhu. rewrite <- Hhu. apply Hts. left. reflexivity. }
        assert (Hct: count u t = 0).
        { rewrite <- H. unfold remove_node. apply eqb_eq in Hhu. rewrite Hhu. apply count_remove_element. }
        rewrite HcV. rewrite Hct. reflexivity.
      + destruct G as [V E]. simpl. simpl in H. unfold remove_node in H.
        rewrite <- H. apply count_filter. rewrite eqb_sym. rewrite Hhu. simpl. reflexivity. }
  intros u H.
  specialize HVts with (u := u). rewrite <- HVts.
  specialize HV with (u := u). apply HV. destruct G as [V E].
  simpl in H. simpl. apply member_In_equiv. apply H.
Qed.

Theorem topo_sort_correct: forall (G: graph) (u v: node) (sorted: nodes),
  G_well_formed G = true /\ topological_sort G = Some sorted /\ edge_in_graph (u, v) G = true
  -> exists (i j: nat), Some i = index sorted u /\ Some j = index sorted v /\ i < j.
Proof.
Admitted.

Corollary topo_sort_parents: forall (G: graph) (c p: node) (sorted: nodes),
  G_well_formed G = true /\ topological_sort G = Some sorted
  -> In p (find_parents c G)
  -> exists (i j: nat), Some i = index sorted p /\ Some j = index sorted c /\ i < j.
Proof. 
  intros G c p sorted. intros [Hwf Hts].
  intros Hmem. apply edge_from_parent_to_child in Hmem.
  apply topo_sort_correct with (G := G) (u := p) (v := c) (sorted := sorted).
  repeat split.
  - apply Hwf.
  - apply Hts.
  - apply Hmem.
Qed.

Lemma topo_sort_first_node_no_parents: forall (G: graph) (u: node) (ts: nodes),
  G_well_formed G = true /\ topological_sort G = Some (u :: ts) -> find_parents u G = [].
Proof.
  intros G u ts [Hwf Hts].
  destruct (find_parents u G) as [| h t] eqn:HP.
  - reflexivity.
  - (* contradiction: u is first in topological sort *)
    assert (Hcontra: exists (i j: nat), Some i = index (u :: ts) h /\ Some j = index (u :: ts) u /\ i < j).
    { apply topo_sort_parents with (G := G).
      - split. apply Hwf. apply Hts.
      - rewrite HP. simpl. left. reflexivity. }
    destruct Hcontra as [i [j [Hi [Hj Hij]]]].
    simpl in Hj. rewrite eqb_refl in Hj. inversion Hj. rewrite H0 in Hij. lia.
Qed.

Lemma topo_sort_parents_before: forall (G: graph) (h: node) (tsp t: nodes),
  G_well_formed G = true /\ topological_sort G = Some (tsp ++ h :: t)
  -> forall (v: node), In v (find_parents h G) -> In v tsp.
Proof.
  intros G h tsp t [Hwf Hts] p Hp.
  apply topo_sort_parents with (sorted := (tsp ++ h :: t)) in Hp.
  - (* i < j, so p must appear in tsp *)
    destruct Hp as [i [j [Hi [Hj Hij]]]].
    assert (Hmem: ~(In h tsp)).
    { intros Hhtsp.
      (* contradict that h appears only once in the topological sort of G *)
      assert (Hc: count h (tsp ++ h :: t) >= 2).
      { apply member_count_at_least_1 in Hhtsp.
        rewrite count_app. simpl. rewrite eqb_refl. lia. }
      assert (Hc2: count h (tsp ++ h :: t) = 1).
      { apply topo_sort_contains_nodes_exactly_once with (G := G).
        - split. apply Hwf. apply Hts.
        - apply topo_sort_contains_nodes with (u := h) in Hts. apply Hts.
          apply membership_append_r. simpl. left. reflexivity. }
      lia. }
    assert (Hj2: index (tsp ++ h :: t) h = Some (length tsp + 0)).
    { apply index_append with (l1 := tsp) (l2 := h :: t) (i := 0). split.
      - apply Hmem.
      - simpl. rewrite eqb_refl. reflexivity. }
    rewrite Hj2 in Hj. inversion Hj. rewrite add_0_r in H0. rewrite H0 in Hij.
    assert (Hptsp: index tsp p = Some i).
    { apply index_append_2 with (l2 := h :: t). split.
      - symmetry. apply Hi.
      - apply Hij. }
    apply index_exists. exists i. symmetry. apply Hptsp.
  - split.
    + apply Hwf.
    + apply Hts.
Qed.



(* semantics *)
Definition nodefun (X: Type) : Type := X * (list X) -> X. (* takes in unobserved term and values for each parent *)
Definition graphfun {X: Type} : Type := node -> nodefun X. (* takes in node and returns function for that node *)

Definition assignment (X : Type) : Type := node * X.
Definition assignments (X : Type) : Type := list (assignment X).

Fixpoint is_assigned {X: Type} (A: assignments X) (u: node) : bool :=
  match A with
  | [] => false
  | h :: t => (u =? (fst h)) || is_assigned t u
  end.

Lemma is_assigned_app: forall X (A1 A2: assignments X) (u: node),
  is_assigned A1 u = true -> is_assigned (A1 ++ A2) u = true.
Proof.
  intros X A1 A2 u H. induction A1 as [| h t IH].
  - simpl in H. discriminate H.
  - simpl. simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + rewrite H. simpl. reflexivity.
    + apply IH in H. rewrite H. rewrite orb_comm. simpl. reflexivity.
Qed.

Lemma is_assigned_app2: forall X (A1 A2: assignments X) (u: node),
  is_assigned A2 u = true -> is_assigned (A1 ++ A2) u = true.
Proof.
  intros X A1 A2 u H. induction A1 as [| h t IH].
  - simpl. apply H.
  - simpl. rewrite IH. rewrite orb_comm. simpl. reflexivity.
Qed.

Fixpoint get_assigned_value {X: Type} (A: assignments X) (u: node) : option X :=
  match A with
  | [] => None
  | h :: t => if ((fst h) =? u) then Some (snd h) else (get_assigned_value t u)
  end.

Lemma get_assigned_app_None: forall X (A1 A2: assignments X) (u: node),
  get_assigned_value A1 u = None -> get_assigned_value (A1 ++ A2) u = get_assigned_value A2 u.
Proof.
  intros X A1 A2 u H. induction A1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. simpl in H. destruct (fst h =? u) as [|] eqn:Hhu.
    + discriminate H.
    + apply IH. apply H.
Qed.

Lemma get_assigned_app_Some: forall X (A1 A2: assignments X) (u: node) (x: X),
  get_assigned_value A1 u = Some x -> get_assigned_value (A1 ++ A2) u = Some x.
Proof.
  intros X A1 A2 u x H. induction A1 as [| h t IH].
  - simpl in H. discriminate H.
  - simpl. simpl in H. destruct (fst h =? u) as [|] eqn:Hhu.
    + apply H.
    + apply IH. apply H.
Qed.

Lemma get_assigned_app2: forall X (A1 A1' A2 A2': assignments X) (u: node),
  get_assigned_value A1 u = get_assigned_value A2 u
    /\ get_assigned_value A1' u = get_assigned_value A2' u
  -> get_assigned_value (A1 ++ A1') u = get_assigned_value (A2 ++ A2') u.
Proof.
  intros X A1 A1' A2 A2' u.
  intros [H H'].
  induction A1 as [| h t IH].
  - simpl in H. simpl. symmetry in H. apply get_assigned_app_None with (A1 := A2) (A2 := A2') in H.
    rewrite H. apply H'.
  - simpl in H. simpl. destruct (fst h =? u) as [|] eqn:Hhu.
    + symmetry in H. apply get_assigned_app_Some with (A1 := A2) (A2 := A2') in H.
      rewrite H. reflexivity.
    + apply IH. apply H.
Qed.

Definition is_assignment_for {X: Type} (A: assignments X) (Z: nodes) : bool :=
  (forallb (fun x: node => is_assigned A x) Z).

Lemma is_assignment_for_cat: forall X (A: assignments X) (u: node) (x: X) (V: nodes),
  is_assignment_for A V = true -> is_assignment_for ((u, x) :: A) V = true.
Proof.
  intros X A u x V H. induction V as [| h t IH].
  - simpl. reflexivity.
  - simpl in H. apply split_and_true in H. destruct H as [H1 H2].
    simpl. rewrite H1. rewrite orb_comm. simpl. apply IH. apply H2.
Qed.

Lemma assigned_has_value: forall X (A: assignments X) (u: node) (L: nodes),
  In u L /\ is_assignment_for A L = true -> exists x: X, get_assigned_value A u = Some x.
Proof.
  intros X A u L [Hmem HA].
  unfold is_assignment_for in HA. apply forallb_true_iff_mem with (X := node) (x := u) in HA.
  - induction A as [| h t IH].
    + simpl in HA. discriminate HA.
    + simpl in HA. apply split_orb_true in HA. destruct HA as [Hu | Hind].
      * destruct h as [u1 x1]. exists x1. simpl in Hu. simpl.
        apply eqb_eq in Hu. rewrite Hu. rewrite eqb_refl. reflexivity.
      * apply IH in Hind. destruct Hind as [x Hind].
        simpl. destruct (fst h =? u) as [|] eqn:Hhu.
        -- exists (snd h). reflexivity.
        -- exists x. apply Hind.
  - apply Hmem.
Qed.

Lemma assigned_is_true: forall X (A: assignments X) (u: node),
  (exists x: X, get_assigned_value A u = Some x) -> is_assigned A u = true.
Proof.
  intros X A u [x H].
  induction A as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. destruct (fst h =? u) as [|] eqn:Hhu.
    + simpl. apply eqb_eq in Hhu. rewrite Hhu. rewrite eqb_refl. simpl. reflexivity.
    + simpl. apply IH in H. rewrite H. rewrite orb_comm. simpl. reflexivity.
Qed.

Lemma assigned_is_false: forall X (A: assignments X) (u: node),
  is_assigned A u = false -> get_assigned_value A u = None.
Proof.
  intros X A u H.
  induction A as [| h t IH].
  - simpl. reflexivity.
  - simpl in H. destruct (u =? fst h) as [|] eqn:Huh.
    + simpl in H. discriminate H.
    + simpl. rewrite eqb_sym. rewrite Huh. apply IH.
      simpl in H. apply H.
Qed.

(* returns None if some parent hasn't been assigned a value, else returns list of assignments *)
Fixpoint get_parent_assignments {X: Type} (A: assignments X) (P: nodes) : option (list X) :=
  match P with
  | [] => Some []
  | h :: t => match (get_assigned_value A h) with
              | Some x => match (get_parent_assignments A t) with
                          | Some l => Some (x :: l)
                          | None => None
                          end
              | None => None
              end
  end.

Lemma parent_assignments_exist: forall X (A: assignments X) (P: nodes),
  is_assignment_for A P = true -> exists L: list X, Some L = get_parent_assignments A P.
Proof.
  intros X A P H.
  induction P as [| h t IH].
  - simpl. exists []. reflexivity.
  - simpl in H. apply split_and_true in H. destruct H as [Hh Hind].
    assert (Hhx: exists x: X, get_assigned_value A h = Some x).
    { apply assigned_has_value with (L := h :: t). split.
      - simpl. left. reflexivity.
      - simpl. rewrite Hh. rewrite Hind. reflexivity. }
    destruct Hhx as [x Hhx].
    simpl. rewrite Hhx.
    apply IH in Hind. destruct Hind as [L Hind].
    exists (x :: L). rewrite <- Hind. reflexivity.
Qed.

Lemma parent_assignments_preserves_index: forall X (P: assignments X) (V: nodes) (p: list X) 
                                              (i: nat) (x: X) (m: node),
  (get_parent_assignments P V = Some p /\ index V m = Some i /\ get_assigned_value P m = Some x)
  -> nth_error p i = Some x.
Proof.
  intros X P V p i x m [Hp [Hi Hm]].
  generalize dependent p. generalize dependent i. induction V as [| h t IH].
  - intros i Hi p Hp. simpl in Hi. discriminate Hi.
  - intros i Hi p Hp. simpl in Hi. destruct (h =? m) as [|] eqn:Hhm.
    + inversion Hi. simpl in Hp. apply eqb_eq in Hhm. rewrite Hhm in Hp. rewrite Hm in Hp.
      destruct (get_parent_assignments P t) as [l|].
      * inversion Hp. simpl. reflexivity.
      * discriminate Hp.
    + destruct (index t m) as [i'|].
      * inversion Hi. simpl in Hp. destruct (get_assigned_value P h) as [vh|].
        -- destruct (get_parent_assignments P t) as [l|].
           ++ inversion Hp. simpl. specialize IH with (i := i') (p := l).
              apply IH. reflexivity. reflexivity.
           ++ discriminate Hp.
        -- discriminate Hp.
      * discriminate Hi.
Qed.

Definition add_assignment {X: Type} (A: assignments X) (u: node) (x: X) : assignments X :=
  A ++ [(u, x)].

(* A = assigned assignments, A_eval = evaluated assignments *)
Definition get_value_of_node {X: Type} (u: node) (G: graph) (g: graphfun) (U A A_eval: assignments X) : option X :=
  match (get_assigned_value A u) with
  | Some x => (* value already assigned *) Some x
  | None => (* find value of parents and use node function *)
            match (get_assigned_value U u) with
            | Some unobs => match (get_parent_assignments A_eval (find_parents u G)) with
                            | Some p => Some ((g u) (unobs, p))
                            | None => None (* won't reach this, contradicts topo correctness *)
                            end
            | None => None (* error, U needs to have unobserved value of all nodes *)
            end
  end.

Lemma value_exists_if_parents_are_assigned: forall X (u: node) (G: graph) (g: graphfun) (U A A_eval: assignments X),
  is_assignment_for A_eval (find_parents u G) = true /\ is_assignment_for U (nodes_in_graph G) = true
  /\ node_in_graph u G = true
  -> exists x: X, get_value_of_node u G g U A A_eval = Some x.
Proof.
  intros X u [V E] g U A A_eval [Hsf [HU Hu]].
  unfold get_value_of_node. destruct (get_assigned_value A u) as [x|] eqn:HA.
  - exists x. reflexivity.
  - assert (HUu: exists hu: X, get_assigned_value U u = Some hu).
    { apply assigned_has_value with (L := V). split.
      - simpl in Hu. apply member_In_equiv. apply Hu.
      - simpl in HU. apply HU. }
    destruct HUu as [hu HUu]. rewrite HUu.
    assert (HP: exists p, Some p = get_parent_assignments A_eval (find_parents u (V, E))).
    { apply parent_assignments_exist. apply Hsf. }
    destruct HP as [p HP].
    rewrite <- HP. exists (g u (hu, p)). reflexivity.
Qed.

Lemma value_same_if_parents_are_same:
  forall X (u: node) (G: graph) (g: graphfun) (U1 U2 A1 A2 V1 V2: assignments X),
  is_assignment_for V1 (find_parents u G) = true /\ is_assignment_for V2 (find_parents u G) = true
  /\ is_assignment_for U1 (nodes_in_graph G) = true /\ is_assignment_for U2 (nodes_in_graph G) = true
  /\ get_assigned_value U1 u = get_assigned_value U2 u
  /\ get_assigned_value A1 u = get_assigned_value A2 u
  /\ (forall (v: node), In v (find_parents u G) -> get_assigned_value V1 v = get_assigned_value V2 v)
  /\ node_in_graph u G = true
  -> get_value_of_node u G g U1 A1 V1 = get_value_of_node u G g U2 A2 V2.
Proof.
  intros X u [V E] g U1 U2 A1 A2 V1 V2.
  intros [HV1 [HV2 [HU1 [HU2 [HU [HA [Hv Hu]]]]]]].
  unfold get_value_of_node. rewrite <- HA.
  destruct (get_assigned_value A1 u) as [x|] eqn:HA1.
  - reflexivity.
  - rewrite <- HU. assert (HUu: exists hu: X, get_assigned_value U1 u = Some hu).
    { apply assigned_has_value with (L := V). split.
      - simpl in Hu. apply member_In_equiv. apply Hu.
      - simpl in HU1. apply HU1. }
    destruct HUu as [hu HUu]. rewrite HUu.
    assert (HP: exists p, Some p = get_parent_assignments V1 (find_parents u (V, E))).
    { apply parent_assignments_exist. apply HV1. }
    destruct HP as [p HP].
    assert (HP2: get_parent_assignments V2 (find_parents u (V, E)) = Some p).
    { generalize dependent p. induction (find_parents u (V, E)) as [| h t IH].
      - intros p HP. simpl. simpl in HP. inversion HP. reflexivity.
      - intros p HP. simpl in HP. destruct (get_assigned_value V1 h) as [a|] eqn:Hh.
        + simpl. assert (Hh2: get_assigned_value V2 h = Some a).
          { rewrite <- Hh. symmetry. specialize Hv with (v := h). apply Hv. simpl. left. reflexivity. }
          rewrite Hh2. destruct (get_parent_assignments V1 t) as [l|] eqn:Hl.
          * specialize IH with (p := l).
            assert (Hl2: get_parent_assignments V2 t = Some l).
            { apply IH.
              - simpl in HV1. apply split_and_true in HV1. destruct HV1 as [_ HV1]. apply HV1.
              - simpl in HV2. apply split_and_true in HV2. destruct HV2 as [_ HV2]. apply HV2.
              - intros v Hmem. apply Hv. simpl. right. apply Hmem.
              - reflexivity. }
            rewrite Hl2. symmetry. apply HP.
          * discriminate HP.
        + discriminate HP. }
    rewrite <- HP. rewrite HP2. reflexivity.
Qed.

Fixpoint get_values_from_topo_sort {X: Type} (ts: nodes) (G: graph) (g: graphfun) (U: assignments X)
                                   (A: assignments X) (A_eval: assignments X) : option (assignments X) :=
  match ts with
  | [] => Some A_eval
  | u :: ts' => match (get_value_of_node u G g U A A_eval) with
                | Some x => get_values_from_topo_sort ts' G g U A (add_assignment A_eval u x)
                | None => None
                end
  end.

Definition get_values {X: Type} (G: graph) (g: graphfun) (U A: assignments X) : option (assignments X) :=
  match (topological_sort G) with
  | Some ts => get_values_from_topo_sort ts G g U A []
  | None => None (* graph is cyclic *)
  end.

Lemma assigned_if_in_A_eval: forall X (ts: nodes) (G: graph) (g: graphfun) (U A A_eval values: assignments X) (u: node),
  get_values_from_topo_sort ts G g U A A_eval = Some values /\ is_assigned A_eval u = true ->
  is_assigned values u = true.
Proof.
  intros X ts G g U A A_eval values u.
  intros [H1 H2].
  generalize dependent A_eval. induction ts as [| h t IH].
  - intros A_eval H1 H2. simpl in H1. inversion H1. rewrite <- H0. apply H2.
  - intros A_eval H1 H2. simpl in H1. unfold get_value_of_node in H1.
    destruct (get_assigned_value A h) as [x|] eqn:HA.
    + specialize IH with (A_eval := (add_assignment A_eval h x)).
      apply IH.
      * apply H1.
      * unfold add_assignment. apply is_assigned_app. apply H2.
    + destruct (get_assigned_value U h) as [unobs|] eqn:HU.
      * destruct (get_parent_assignments A_eval (find_parents h G)) as [p|] eqn:HP.
        -- specialize IH with (A_eval := (add_assignment A_eval h (g h (unobs, p)))).
           apply IH.
           ++ apply H1.
           ++ unfold add_assignment. apply is_assigned_app. apply H2.
        -- discriminate H1.
      * discriminate H1.
Qed.

Lemma get_assigned_if_in_A_eval:
  forall X (ts: nodes) (G: graph) (g: graphfun) (U A A_eval values: assignments X) (u: node) (x: X),
  get_values_from_topo_sort ts G g U A A_eval = Some values /\ get_assigned_value A_eval u = Some x ->
  get_assigned_value values u = Some x.
Proof.
  intros X ts G g U A A' values u x.
  intros [Hts HA'].
  generalize dependent A'. induction ts as [| h t IH].
  - intros A' Hts HA'. simpl in Hts. inversion Hts. rewrite <- H0. apply HA'.
  - intros A' Hts HA'. simpl in Hts. destruct (get_value_of_node h G g U A A') as [hv|] eqn:Hhv.
    + specialize IH with (A' := (add_assignment A' h hv)). apply IH.
      * apply Hts.
      * unfold add_assignment. apply get_assigned_app_Some with (A2 := [(h, hv)]) in HA'.
        apply HA'.
    + discriminate Hts.
Qed.

Lemma get_values_exists_then_all_nodes_assigned_helper: forall X (ts: nodes) (G: graph) (g: graphfun)
  (U A A_eval values: assignments X),
  topological_sort G = Some ts /\ get_values_from_topo_sort ts G g U A A_eval = Some values
  -> is_assignment_for values (nodes_in_graph G) = true.
Proof.
  intros X ts G g U A A_eval values [Hts H].
  unfold is_assignment_for. apply forallb_true_iff_mem. intros u Hmem.
  assert (Huts: In u ts).
  { apply topo_sort_contains_nodes with (u := u) in Hts as Hu.
    apply Hu. destruct G as [V E]. simpl. simpl in Hmem. apply member_In_equiv. apply Hmem. }
  clear Hts.
  generalize dependent values. generalize dependent A_eval. induction ts as [| h t IH].
  + exfalso. apply Huts.
  + intros A_eval values H. simpl in Huts. destruct Huts as [Huh | Hut].
    * simpl in H. unfold get_value_of_node in H. destruct (get_assigned_value A u) as [x|] eqn:Hassigned.
      -- rewrite <- Huh in Hassigned. rewrite Hassigned in H. unfold add_assignment in H.
         apply assigned_if_in_A_eval with (ts := t) (G := G) (g := g) (U := U) (A := A) (A_eval := A_eval ++ [(h, x)]).
         split.
         ++ apply H.
         ++ rewrite <- Huh. apply is_assigned_app2. simpl. rewrite eqb_refl. simpl. reflexivity.
      -- rewrite <- Huh in Hassigned. rewrite Hassigned in H.
         destruct (get_assigned_value U h) as [unobs|] eqn:HU.
         ++ destruct (get_parent_assignments A_eval (find_parents h G)) as [p|] eqn:HP.
            ** unfold add_assignment in H.
               apply assigned_if_in_A_eval with (ts := t) (G := G) (g := g) (U := U) (A := A) (A_eval := A_eval ++ [(h, g h (unobs, p))]).
               split.
              { apply H. } { rewrite <- Huh. apply is_assigned_app2. simpl. rewrite eqb_refl. simpl. reflexivity. }
            ** discriminate H.
         ++ discriminate H.
    * simpl in H. unfold get_value_of_node in H. destruct (get_assigned_value A h) as [x|] eqn:HA.
      -- unfold add_assignment in H. specialize IH with (A_eval := (A_eval ++ [(h, x)])) (values := values).
         apply IH. apply Hut. apply H.
      -- destruct (get_assigned_value U h) as [Uh|] eqn:HU.
         ++ destruct (get_parent_assignments A_eval (find_parents h G)) as [p|] eqn:HP.
            ** specialize IH with (A_eval := (add_assignment A_eval h (g h (Uh, p)))) (values := values).
               apply IH. apply Hut. apply H.
            ** discriminate H.
         ++ discriminate H.
Qed.

Theorem get_values_exists_then_all_nodes_assigned: forall X (G: graph) (g: graphfun) (U A values: assignments X),
  get_values G g U A = Some values -> is_assignment_for values (nodes_in_graph G) = true.
Proof.
  intros X G g U A values H. destruct (topological_sort G) as [ts|] eqn:Hts.
  - apply get_values_exists_then_all_nodes_assigned_helper with (ts := ts) (g := g) (U := U) (A := A) (A_eval := []).
    split. apply Hts. unfold get_values in H. rewrite Hts in H. apply H. 
  - unfold get_values in H. rewrite Hts in H. discriminate H.
Qed.

Lemma get_values_only_dependent_on_parents_helper:
  forall X (G: graph) (ts_pre ts_suff: nodes) (u: node) (g: graphfun)
           (U1 U2 A1 A2 A1' A2' V1 V2: assignments X),
  G_well_formed G = true /\ topological_sort G = Some (ts_pre ++ ts_suff) /\ node_in_graph u G = true ->
  get_values_from_topo_sort ts_suff G g U1 A1 A1' = Some V1
  /\ get_values_from_topo_sort ts_suff G g U2 A2 A2' = Some V2
  /\ is_assignment_for A1' ts_pre = true /\ is_assignment_for A2' ts_pre = true
  /\ get_assigned_value A1' u = get_assigned_value A2' u /\ True
  /\ get_assigned_value U1 u = get_assigned_value U2 u
  /\ is_assignment_for U1 (nodes_in_graph G) = true /\ is_assignment_for U2 (nodes_in_graph G) = true
  /\ get_assigned_value A1 u = get_assigned_value A2 u
  /\ (forall (v: node), In v (find_parents u G)
          -> get_assigned_value V1 v = get_assigned_value V2 v) ->
  get_assigned_value V1 u = get_assigned_value V2 u.
Proof.
  intros X G tsp tss u g U1 U2 A1 A2 A1' A2' V1 V2.
  intros [Hwf [Hts Hu]] [HV1 [HV2 [HA1' [HA2' [HA1u [HA2u [HU [HU1 [HU2 [HA HP]]]]]]]]]].
  generalize dependent V1. generalize dependent V2. generalize dependent tsp.
  generalize dependent A1'. generalize dependent A2'.
  induction tss as [| h t IH].
  - intros A2' A1' HA1u. intros tsp Hts HA1' HA2' V2 HV2 V1 HV1 Hv.
    simpl in HV1. inversion HV1. rewrite <- H0.
    simpl in HV2. inversion HV2. rewrite <- H1.
    apply HA1u.
  - intros A2' A1' HA1u. intros tsp Hts HA1' HA2' V2 HV2 V1 HV1 Hv.
    simpl in HV1. simpl in HV2.
    destruct (get_value_of_node h G g U1 A1 A1') as [hv1|] eqn:Hhv1.
    + destruct (get_value_of_node h G g U2 A2 A2') as [hv2|] eqn:Hhv2.
      * unfold add_assignment in HV1. unfold add_assignment in HV2.
        specialize IH with (A2' := (A2' ++ [(h, hv2)])) (A1' := (A1' ++ [(h, hv1)])).
        specialize IH with (tsp := tsp ++ [h]) (V2 := V2) (V1 := V1).
        apply IH.
        -- destruct (get_assigned_value A1' u) as [x|] eqn:Hx.
           ++ apply get_assigned_app_Some with (A2 := [(h, hv1)]) in Hx. rewrite Hx.
              symmetry in HA1u. apply get_assigned_app_Some with (A2 := [(h, hv2)]) in HA1u. rewrite HA1u.
              reflexivity.
           ++ apply get_assigned_app_None with (A2 := [(h, hv1)]) in Hx. rewrite Hx.
              symmetry in HA1u. apply get_assigned_app_None with (A2 := [(h, hv2)]) in HA1u. rewrite HA1u.
              (* if h=u, then hv1=hv2. *)
              destruct (h =? u) as [|] eqn:Hhu.
              ** assert (Hp: forall v: node, In v (find_parents u G) -> In v tsp).
                 { apply topo_sort_parents_before with (t := t). split. apply Hwf.
                   apply eqb_eq in Hhu. rewrite Hhu in Hts. apply Hts. }
                 unfold get_assigned_value. simpl. rewrite Hhu. apply eqb_eq in Hhu. 
                 assert (H: get_value_of_node u G g U1 A1 A1' = get_value_of_node u G g U2 A2 A2').
                 { apply value_same_if_parents_are_same. repeat split.
                 - unfold is_assignment_for. apply forallb_true_iff_mem. intros p Hmem.
                   specialize Hp with (v := p). apply Hp in Hmem.
                   apply assigned_is_true. apply assigned_has_value with (L := tsp). split.
                   + apply Hmem.
                   + apply HA1'.
                 - unfold is_assignment_for. apply forallb_true_iff_mem. intros p Hmem.
                   specialize Hp with (v := p). apply Hp in Hmem.
                   apply assigned_is_true. apply assigned_has_value with (L := tsp). split.
                   + apply Hmem.
                   + apply HA2'.
                 - apply HU1.
                 - apply HU2.
                 - apply HU.
                 - apply HA.
                 - intros p Hpmem. specialize Hv with (v := p).
                   assert (HA1p: exists x: X, get_assigned_value A1' p = Some x).
                   { apply assigned_has_value with (L := tsp). split.
                     - specialize Hp with (v := p). apply Hp. apply Hpmem.
                     - apply HA1'. }
                   destruct HA1p as [x1 HA1p]. rewrite HA1p.
                   assert (HV1p: get_assigned_value V1 p = Some x1).
                   { apply get_assigned_if_in_A_eval with (ts := t) (G := G) (g := g) (U := U1)
                                                          (A := A1) (A_eval := (A1' ++ [(h, hv1)])).
                     split. apply HV1. apply get_assigned_app_Some with (A2 := [(h, hv1)]) in HA1p.
                     apply HA1p. }
                   assert (HA2p: exists x: X, get_assigned_value A2' p = Some x).
                   { apply assigned_has_value with (L := tsp). split.
                     - specialize Hp with (v := p). apply Hp. apply Hpmem.
                     - apply HA2'. }
                   destruct HA2p as [x2 HA2p]. rewrite HA2p.
                   assert (HV2p: get_assigned_value V2 p = Some x2).
                   { apply get_assigned_if_in_A_eval with (ts := t) (G := G) (g := g) (U := U2)
                                                          (A := A2) (A_eval := (A2' ++ [(h, hv2)])).
                     split. apply HV2. apply get_assigned_app_Some with (A2 := [(h, hv2)]) in HA2p.
                     apply HA2p. }
                   apply Hv in Hpmem. rewrite HV1p in Hpmem. rewrite HV2p in Hpmem. apply Hpmem.
                 - apply Hu. }
                 rewrite <- Hhu in H. rewrite Hhv1 in H. rewrite Hhv2 in H.
                 apply H.
              ** simpl. rewrite Hhu. reflexivity.
        -- rewrite append_vs_concat. apply Hts.
        -- unfold is_assignment_for. apply forallb_true_iff_mem. intros x Hmem.
           apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
           ++ apply is_assigned_app. apply assigned_is_true. apply assigned_has_value with (L := tsp).
              split. apply Hmem. apply HA1'.
           ++ apply is_assigned_app2. apply assigned_is_true. apply assigned_has_value with (L := [h]).
              split. apply Hmem. simpl. rewrite eqb_refl. simpl. reflexivity.
        -- unfold is_assignment_for. apply forallb_true_iff_mem. intros x Hmem.
           apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
           ++ apply is_assigned_app. apply assigned_is_true. apply assigned_has_value with (L := tsp).
              split. apply Hmem. apply HA2'.
           ++ apply is_assigned_app2. apply assigned_is_true. apply assigned_has_value with (L := [h]).
              split. apply Hmem. simpl. rewrite eqb_refl. simpl. reflexivity.
        -- apply HV2.
        -- apply HV1.
        -- apply Hv.
      * discriminate HV2.
    + discriminate HV1.
Qed.

(* as long as u has the same error term,
   its parents have the same values,
   and it has either not been assigned or been assigned the same value,
   then it will have the same find_value *)
Theorem get_values_only_dependent_on_parents:
  forall X (G: graph) (u: node) (g: graphfun) (U1 U2 A1 A2 V1 V2: assignments X),
  G_well_formed G = true /\ node_in_graph u G = true ->
  get_values G g U1 A1 = Some V1 /\ get_values G g U2 A2 = Some V2 ->
  (forall (v: node), In v (find_parents u G) 
          -> get_assigned_value V1 v = get_assigned_value V2 v)
  /\ get_assigned_value U1 u = get_assigned_value U2 u
  /\ is_assignment_for U1 (nodes_in_graph G) = true /\ is_assignment_for U2 (nodes_in_graph G) = true
  /\ get_assigned_value A1 u = get_assigned_value A2 u ->
  get_assigned_value V1 u = get_assigned_value V2 u.
Proof.
  intros X G u g U1 U2 A1 A2 V1 V2.
  intros [Hwf Hu] [HV1 HV2] [Hp [HU [HU1 [HU2 HA]]]].
  unfold get_values in HV1. destruct (topological_sort G) as [ts|] eqn:Hts.
  - unfold get_values in HV2. rewrite Hts in HV2.
    apply get_values_only_dependent_on_parents_helper with (G := G) (ts_pre := []) (ts_suff := ts)
                    (g := g) (U1 := U1) (U2 := U2) (A1 := A1) (A2 := A2) (A1' := []) (A2' := []).
    + repeat split.
      * apply Hwf.
      * simpl. apply Hts.
      * apply Hu.
    + repeat split.
      * apply HV1.
      * apply HV2.
      * apply HU.
      * apply HU1.
      * apply HU2.
      * apply HA.
      * apply Hp.
  - discriminate HV1.
Qed.

Lemma get_values_existence_helper: forall X (ts_pre ts_suff: nodes) (G: graph) (g: graphfun) (U A A_eval: assignments X),
  G_well_formed G = true ->
  topological_sort G = Some (ts_pre ++ ts_suff) /\ is_assignment_for A_eval ts_pre = true /\
  is_assignment_for U (nodes_in_graph G) = true
  -> exists (values: assignments X), get_values_from_topo_sort ts_suff G g U A A_eval = Some values.
Proof.
  intros X tsp tss G g U A A_eval.
  intros Hwf [Hts [Hsf HU]].
  generalize dependent tsp. generalize dependent A_eval. induction tss as [| h t IH].
  - intros A_eval tsp Hts Hsf. simpl. exists A_eval. reflexivity.
  - intros A_eval tsp Hts Hsf. simpl.
    assert (Hh: exists x: X, get_value_of_node h G g U A A_eval = Some x).
    { apply value_exists_if_parents_are_assigned. repeat split.
      - assert (Hp: forall (p: node), In p (find_parents h G) -> In p tsp).
        { apply topo_sort_parents_before with (t := t). split. apply Hwf. apply Hts. }
        unfold is_assignment_for. apply forallb_true_iff_mem. intros p Hmem.
        specialize Hp with (p := p). apply Hp in Hmem.
        apply assigned_is_true. apply assigned_has_value with (L := tsp). split.
        + apply Hmem.
        + apply Hsf.
      - apply HU.
      - apply topo_sort_contains_nodes with (u := h) in Hts. apply Hts.
        apply membership_append_r. simpl. left. reflexivity. }
    destruct Hh as [x Hh]. rewrite Hh.
    specialize IH with (A_eval := (add_assignment A_eval h x)) (tsp := tsp ++ [h]).
    apply IH.
    + rewrite Hts. f_equal. rewrite append_vs_concat. reflexivity.
    + unfold add_assignment. unfold is_assignment_for.
      apply forallb_true_iff_mem. intros v Hmem.
      apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
      * apply is_assigned_app. apply assigned_is_true. apply assigned_has_value with (L := tsp). split.
        -- apply Hmem.
        -- apply Hsf.
      * apply is_assigned_app2. apply assigned_is_true. apply assigned_has_value with (L := [h]). split.
        -- apply Hmem.
        -- simpl. rewrite eqb_refl. simpl. reflexivity.
Qed.

Theorem get_values_existence: forall X (G: graph) (g: graphfun) (U A: assignments X),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true ->
  exists (values: assignments X), get_values G g U A = Some values.
Proof.
  intros X G g U A. destruct G as [V E] eqn:HG.
  intros [Hwf Hcyc]. intros HU. simpl in HU. simpl.
  assert (Hts: exists ts: nodes, topological_sort G = Some ts).
  { apply topo_sort_exists_for_acyclic. split.
    - rewrite HG. apply Hwf.
    - rewrite HG. apply Hcyc. }
  destruct Hts as [ts Hts].
  unfold get_values. rewrite HG in Hts. rewrite Hts.
  apply get_values_existence_helper with (ts_pre := []).
  - apply Hwf.
  - repeat split.
    + rewrite Hts. simpl. reflexivity.
    + simpl. apply HU.
Qed.

Definition find_value {X: Type} (G: graph) (g: graphfun) (u: node) (U A: assignments X): option X :=
  match (get_values G g U A) with
  | Some values => get_assigned_value values u
  | None => None
  end.

Fixpoint find_values {X: Type} (G: graph) (g: graphfun) (P: nodes) (U A: assignments X): option (assignments X) :=
  match P with
  | [] => Some []
  | h :: t => match (find_value G g h U A) with
              | Some x => match (find_values G g t U A) with
                          | Some r => Some ((h, x) :: r)
                          | None => None
                          end
              | None => None
              end
  end.

Lemma find_values_assignment: forall X (G: graph) (g: graphfun) (P: nodes) (U A values: assignments X),
  find_values G g P U A = Some values -> is_assignment_for values P = true.
Proof.
  intros X G g P U A.
  induction P as [| h t IH].
  - intros values H. simpl. reflexivity.
  - intros values H. simpl. simpl in H. destruct (find_value G g h U A) as [x|].
    + destruct (find_values G g t U A) as [r|].
      * inversion H. simpl. rewrite eqb_refl. simpl. specialize IH with (values := r).
        apply is_assignment_for_cat. apply IH. reflexivity.
      * discriminate H.
    + discriminate H.
Qed.

Lemma find_values_get_assigned: forall X (G: graph) (g: graphfun) (P: nodes) (U A values: assignments X)
                                       (x: X) (m: node),
  find_values G g P U A = Some values /\ In m P /\ find_value G g m U A = Some x
  -> get_assigned_value values m = Some x.
Proof.
  intros X G g P U A values x m.
  intros [Hv [Hm Hx]].
  generalize dependent values. induction P as [| h t IH].
  - intros values Hv. simpl in Hm. exfalso. apply Hm.
  - intros values Hv. simpl in Hm. destruct Hm as [Hhm | Hmem].
    + simpl in Hv. rewrite Hhm in Hv. rewrite Hx in Hv.
      destruct (find_values G g t U A) as [r|].
      * inversion Hv. simpl. rewrite eqb_refl. reflexivity.
      * discriminate Hv.
    + simpl in Hv. destruct (find_value G g h U A) as [x'|] eqn:Hh.
      * destruct (find_values G g t U A) as [r|].
        -- inversion Hv. simpl. destruct (h =? m) as [|] eqn:Hhm.
           ++ apply eqb_eq in Hhm. rewrite Hhm in Hh. rewrite <- Hh. apply Hx.
           ++ apply IH with (values := r).
              ** apply Hmem.
              ** reflexivity.
        -- discriminate Hv.
      * discriminate Hv.
Qed.

Theorem find_value_existence: forall X (G: graph) (g: graphfun) (U A: assignments X) (u: node),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph u G = true ->
  exists (x: X), find_value G g u U A = Some x.
Proof.
  intros X G g U A u. intros [Hwf Hcyc]. intros [HU Hu].
  assert (Hval: exists (values: assignments X), get_values G g U A = Some values).
  { apply get_values_existence.
    - split.
      + apply Hwf.
      + apply Hcyc.
    - apply HU. }
  unfold find_value. destruct Hval as [values Hval].
  rewrite Hval. apply get_values_exists_then_all_nodes_assigned in Hval.
  apply assigned_has_value with (L := (nodes_in_graph G)). split.
  - destruct G as [V E]. simpl. simpl in Hu. apply member_In_equiv. apply Hu.
  - apply Hval.
Qed.

Corollary find_values_existence: forall X (G: graph) (g: graphfun) (U A: assignments X) (u: node),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph u G = true ->
  exists (P: assignments X), find_values G g (find_parents u G) U A = Some P.
Proof.
  intros X G g U A u. intros [Hwf Hcyc]. intros [HU hu].
  remember (find_parents u G).
  assert (H: forall h: node, In h n -> In h (find_parents u G)).
  { intros h Hmem. rewrite <- Heqn. apply Hmem. }
  clear Heqn.
  induction n as [| h t IH].
  - exists []. reflexivity.
  - simpl. assert (Hv: exists v, find_value G g h U A = Some v).
    { apply find_value_existence.
      - split. apply Hwf. apply Hcyc.
      - split. apply HU.
        assert (He: edge_in_graph (h, u) G = true).
        { apply edge_from_parent_to_child. specialize H with (h := h).
          apply H. simpl. left. reflexivity. }
        assert (Hh: node_in_graph h G = true /\ node_in_graph u G = true).
        { apply edge_corresponds_to_nodes_in_well_formed. split.
          apply Hwf. apply He. }
        destruct Hh as [Hh _]. apply Hh. }
    destruct Hv as [v Hv]. rewrite Hv.
    assert (H': forall h: node, In h t -> In h (find_parents u G)).
    { intros h' Hmem. apply H. simpl. right. apply Hmem. }
    apply IH in H'. destruct H' as [P' H']. rewrite H'. exists ((h, v) :: P'). reflexivity.
Qed.

Theorem find_values_preserves_index: forall X (G: graph) (g: graphfun) (U A values: assignments X)
                                            (P: nodes) (u: node) (i: nat),
  G_well_formed G = true /\ contains_cycle G = false
  -> is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph u G = true
  -> (forall (v: node), In v P -> node_in_graph v G = true)
  -> find_values G g P U A = Some values /\ index P u = Some i
  -> exists x: X, find_value G g u U A = Some x /\ nth_error values i = Some (u, x).
Proof.
  intros X G g U A values P u i [Hwf Hcyc] [HU Hu] HP [Hfv Hi].
  assert (Hx: exists x: X, find_value G g u U A = Some x).
  { apply find_value_existence. split.
    - apply Hwf.
    - apply Hcyc.
    - split. apply HU. apply Hu. }
  destruct Hx as [x Hx]. exists x. split.
  - apply Hx.
  - generalize dependent values. generalize dependent i. induction P as [| h t IH].
    + intros i Hi values H. simpl in Hi. discriminate Hi.
    + intros i Hi values H. assert (Hx': exists x': X, find_value G g h U A = Some x').
      { apply find_value_existence. split.
        - apply Hwf.
        - apply Hcyc.
        - split. apply HU. specialize HP with (v := h). apply HP. simpl. left. reflexivity. }
      destruct Hx' as [x' Hx'].
      simpl in H. rewrite Hx' in H. simpl in Hi.
      destruct (h =? u) as [|] eqn:Hhu.
      * inversion Hi. destruct (find_values G g t U A) as [r|].
        -- inversion H. simpl. apply eqb_eq in Hhu. rewrite Hhu.
           assert (Hxx': x = x').
           { rewrite Hhu in Hx'. rewrite Hx in Hx'. inversion Hx'. reflexivity. }
           rewrite Hxx'. reflexivity.
        -- discriminate H.
      * destruct (index t u) as [i'|].
        -- inversion Hi. destruct (find_values G g t U A) as [r|].
           ++ inversion H. specialize IH with (i := i') (values := r).
              simpl. apply IH.
              ** intros v Hmem. apply HP. simpl. right. apply Hmem.
              ** reflexivity.
              ** reflexivity.
           ++ discriminate H.
        -- discriminate Hi.
Qed.

Theorem find_value_gives_value_of_node: forall X (G: graph) (g: graphfun) (U A: assignments X) (u: node),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph u G = true ->
  exists (P: assignments X), find_values G g (find_parents u G) U A = Some P
                              /\ find_value G g u U A = get_value_of_node u G g U A P.
Proof.
  intros X G g U A u. intros [Hwf Hcyc]. intros [HU Hu].
  assert (H: exists (P: assignments X), find_values G g (find_parents u G) U A = Some P).
  { apply find_values_existence. split.
    - apply Hwf.
    - apply Hcyc.
    - split. apply HU. apply Hu. }
  destruct H as [P H]. exists P. split.
  - apply H.
  - admit.
Admitted.


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

Definition find_values_independent_2 {X: Type} (G: graph) (u v: node) (Z: nodes)
                                     (A: assignments X) (U: assignments X): Prop :=
  forall (g: graphfun) (a b x: X),
  (find_value G g v U A = Some a -> find_value G g u U A = Some x)
  -> (find_value G g v U A = Some b -> find_value G g u U A = Some x).

Definition f1 {X: Type} (x: X * (list X)): X :=
  match (snd x) with
  | [] => fst x
  | h :: t => h
  end.

Definition g1 {X: Type} (u: node): nodefun X := f1.

Definition f2 (X: Type) (i: nat) (x: X * (list X)): X :=
  nth_default (fst x) (snd x) i.
Definition g3 (X: Type) (u v: node) (i j: nat) := fun x: node => if (x =? u) then f2 X i else f2 X j.
Definition h1 (X: Type) (u v: node) (i j: nat): graphfun := g3 X u v i j.

Definition get_assignment_for {X: Type} (V: nodes) (a: X): assignments X :=
  map (fun u: node => (u, a)) V.

Lemma node_maps_to_assigned: forall X (V: nodes) (u: node) (a: X),
  In u V -> is_assigned (get_assignment_for V a) u = true.
Proof.
  intros X V u a H.
  induction V as [| h t IH].
  - simpl in H. exfalso. apply H.
  - simpl in H. destruct H as [H | H].
    + simpl. rewrite H. rewrite eqb_refl. simpl. reflexivity.
    + simpl. apply IH in H. rewrite H. rewrite orb_comm. simpl. reflexivity.
Qed.

Lemma node_maps_to_unassigned: forall X (V: nodes) (u: node) (a: X),
  ~(In u V) -> is_assigned (get_assignment_for V a) u = false.
Proof.
  intros X V u a H. unfold not in H.
  induction V as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (u =? h) as [|] eqn:Huh.
    + simpl in H. exfalso. apply H. left. apply eqb_eq in Huh. symmetry. apply Huh.
    + simpl in H. simpl. apply IH. intros Hmem.
      apply H. right. apply Hmem.
Qed.

Lemma nodes_map_to_assignment: forall X (V: nodes) (a: X),
  is_assignment_for (get_assignment_for V a) V = true.
Proof.
  intros X V a.
  induction V as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite eqb_refl. simpl.
    unfold is_assignment_for. unfold is_assignment_for in IH.
    apply forallb_true_iff_mem. intros x Hmem.
    assert (H: is_assigned (get_assignment_for t a) x = true).
    { apply forallb_true with (x := x) in IH.
      - apply IH.
      - apply Hmem. }
    simpl. rewrite H. rewrite orb_comm. simpl. reflexivity.
Qed.

Theorem mediator_independence: forall X (G: graph) (u v m: node),
  (exists (x: X), True) /\ G_well_formed G = true /\ contains_cycle G = false
    /\ (find_all_paths_from_start_to_end u v G = [(u, v, [m])] /\ is_mediator_bool u v m G = true) ->
  forall (Z: nodes), (* TODO need that Z is a subset? *) d_separated_bool u v G Z = true <->
  forall (A: assignments X) (U: assignments X),
    is_assignment_for A Z = true /\ is_assignment_for U (nodes_in_graph G) = true ->
    find_values_independent_2 G v u Z A U.
Proof.
  intros X G u v m. intros [[xX _] [Hwf [Hcyc [Hpath Hmed]]]].
  intros Z. split.
  { intros Hdsep. intros A U. intros [HA HU].
    assert (HmZ: In m Z). { admit. }
    assert (HmA: is_assigned A m = true). { admit. }
    assert (HP: find_parents v G = [m]). { admit. }
    unfold find_values_independent_2. intros g a b x Ha Hb.
    assert (Hval: find_value G g v U A = get_assigned_value A m). { admit. }
    (* TODO ideally, could show that since fv(u)=a -> fv(v)=x and fv(v) does not have
       anything to do with fv(u), the hypothesis doesn't matter, so the result is always
       true. But how to explain this in coq? *)
    admit. }
  { intros H.
    destruct (member v Z) as [|] eqn:HvZ.
    { (* TODO if v is in Z, are u and v automatically d-separated? This would require a change
         in the definition of d-separation, which currently only depends on mediators, confounders,
         and colliders. *) admit. }
    {
    (* WTS: m is in Z. Show by contradiction: if m is not in Z, then m not assigned in A.
       Define g(v) := g(m), and g(m) := g(u). Then fv(u)=a -> fv(v)=a, and fv(u)=b -> fv(v)=b.
       Specialize with a not equal to b (how?), then discriminate H. *)
    assert (Hmem: In m Z).
    { destruct (member m Z) as [|] eqn:Hmem.
      - apply member_In_equiv. apply Hmem.
      - remember (get_assignment_for Z xX) as A. remember (get_assignment_for (nodes_in_graph G) xX) as U.
        specialize H with (A := A) (U := U).
        unfold find_values_independent_2 in H.
        assert (Hnode: node_in_graph u G = true /\ node_in_graph m G = true /\ node_in_graph v G = true).
        { unfold is_mediator_bool in Hmed. destruct G as [V E]. simpl in Hmed.
          apply split_and_true in Hmed. destruct Hmed as [Hum Hmv].
          apply split_and_true in Hum. destruct Hum as [Hum _]. apply split_and_true in Hum.
          simpl. destruct Hum as [Hu Hm]. repeat split.
          - apply Hu.
          - apply Hm.
          - apply split_and_true in Hmv. destruct Hmv as [Hmv _].
            apply split_and_true in Hmv. destruct Hmv as [_ Hv]. apply Hv. }
        assert (Hi: exists i: nat, index (find_parents v G) m = Some i).
        { assert (Hm: In m (find_parents v G)).
          { apply edge_from_parent_to_child. destruct G as [V E]. simpl.
            unfold is_mediator_bool in Hmed. simpl in Hmed.
            apply split_and_true in Hmed. destruct Hmed as [_ Hmed].
            apply split_and_true in Hmed. destruct Hmed as [_ Hmed]. apply Hmed. }
          apply index_exists in Hm. destruct Hm as [i Hi]. exists i. rewrite Hi. reflexivity. }
        destruct Hi as [i Hi].
        assert (Hj: exists j: nat, index (find_parents m G) u = Some j).
        { assert (Hm: In u (find_parents m G)).
          { apply edge_from_parent_to_child. destruct G as [V E]. simpl.
            unfold is_mediator_bool in Hmed. simpl in Hmed.
            apply split_and_true in Hmed. destruct Hmed as [Hmed _].
            apply split_and_true in Hmed. destruct Hmed as [_ Hmed]. apply Hmed. }
          apply index_exists in Hm. destruct Hm as [j Hj]. exists j. rewrite Hj. reflexivity. }
        destruct Hj as [j Hj].
        remember (h1 X v m i j) as g1.
        specialize H with (g := g1).
        assert (Hf: exists (value: X), find_value G g1 u U A = Some value).
        { apply find_value_existence. repeat split.
          - apply Hwf.
          - apply Hcyc.
          - split.
            + rewrite HeqU. apply nodes_map_to_assignment.
            + destruct Hnode as [Hnode _]. apply Hnode. }
        destruct Hf as [value Hf].
        assert (Hvalv: exists (P: assignments X), find_values G g1 (find_parents v G) U A = Some P
                              /\ find_value G g1 v U A = get_value_of_node v G g1 U A P).
        { apply find_value_gives_value_of_node. split.
          - apply Hwf.
          - apply Hcyc.
          - split.
            + rewrite HeqU. apply nodes_map_to_assignment.
            + destruct Hnode as [_ [_ Hnode]]. apply Hnode. }
        destruct Hvalv as [P [HP Hv]].
        assert (Hvalm: exists (P: assignments X), find_values G g1 (find_parents m G) U A = Some P
                              /\ find_value G g1 m U A = get_value_of_node m G g1 U A P).
        { apply find_value_gives_value_of_node. split.
          - apply Hwf.
          - apply Hcyc.
          - split.
            + rewrite HeqU. apply nodes_map_to_assignment.
            + destruct Hnode as [_ [Hnode _]]. apply Hnode. }
        destruct Hvalm as [Pm [HPm Hm]].
        assert (Hv': find_value G g1 v U A = find_value G g1 m U A).
        { unfold get_value_of_node in Hv. assert (Hnone: get_assigned_value A v = None).
          { apply assigned_is_false. rewrite HeqA. apply node_maps_to_unassigned.
            unfold not. intros contra. apply member_In_equiv in contra. rewrite contra in HvZ. discriminate HvZ. }
          rewrite Hnone in Hv. assert (Hunobs: exists unobs, get_assigned_value U v = Some unobs).
          { apply assigned_has_value with (L := nodes_in_graph G). split.
            - destruct Hnode as [_ [_ Hnode]]. destruct G as [V E]. simpl. simpl in Hnode.
              apply member_In_equiv. apply Hnode.
            - rewrite HeqU. apply nodes_map_to_assignment. }
          destruct Hunobs as [unobs Hunobs]. rewrite Hunobs in Hv.
          apply find_values_assignment in HP as HP'.
          assert (Hpar: exists p, Some p = get_parent_assignments P (find_parents v G)).
          { apply parent_assignments_exist. apply HP'. } destruct Hpar as [p Hpar].
          rewrite <- Hpar in Hv.
          assert (Hx: exists x: X, find_value G g1 m U A = Some x /\ nth_error P i = Some (m, x)).
          { apply find_values_preserves_index with (P := find_parents v G).
            - split. apply Hwf. apply Hcyc.
            - split. rewrite HeqU. apply nodes_map_to_assignment.
              destruct Hnode as [_ [Hnode _]]. apply Hnode.
            - intros v' Hfp. apply edge_from_parent_to_child in Hfp.
              assert (Hvv: node_in_graph v' G = true /\ node_in_graph v G = true).
              { apply edge_corresponds_to_nodes_in_well_formed. split. apply Hwf. apply Hfp. }
              destruct Hvv as [Hvv _]. apply Hvv.
            - split. apply HP. apply Hi. }
          destruct Hx as [x [Hm' Hi']].
          assert (Hg1: g1 v (unobs, p) = x).
          { rewrite Heqg1. unfold h1. unfold g3. rewrite eqb_refl. unfold f2. simpl.
            assert (Hn: nth_error p i = Some x).
            { apply parent_assignments_preserves_index with (P := P) (V := find_parents v G) (m := m).
              repeat split.
              - symmetry. apply Hpar.
              - apply Hi.
              - apply find_values_get_assigned with (G := G) (g := g1) (P := find_parents v G) (U := U) (A := A). repeat split.
                + apply HP.
                + apply index_exists. exists i. symmetry. apply Hi.
                + apply Hm'. }
            unfold nth_default. rewrite Hn. reflexivity. }
          rewrite Hv. rewrite Hg1. rewrite Hm'. reflexivity. }
        assert (Hm': find_value G g1 m U A = find_value G g1 u U A).
        { unfold get_value_of_node in Hm. assert (Hnone: get_assigned_value A m = None).
          { apply assigned_is_false. rewrite HeqA. apply node_maps_to_unassigned.
            unfold not. intros contra. apply member_In_equiv in contra. rewrite contra in Hmem. discriminate Hmem. }
          rewrite Hnone in Hm. assert (Hunobs: exists unobs, get_assigned_value U m = Some unobs).
          { apply assigned_has_value with (L := nodes_in_graph G). split.
            - destruct Hnode as [_ [Hnode _]]. destruct G as [V E]. simpl. simpl in Hnode.
              apply member_In_equiv. apply Hnode.
            - rewrite HeqU. apply nodes_map_to_assignment. }
          destruct Hunobs as [unobs Hunobs]. rewrite Hunobs in Hm.
          apply find_values_assignment in HPm as HP'.
          assert (Hpar: exists p, Some p = get_parent_assignments Pm (find_parents m G)).
          { apply parent_assignments_exist. apply HP'. } destruct Hpar as [p Hpar].
          rewrite <- Hpar in Hm.
          assert (Hx: exists x: X, find_value G g1 u U A = Some x /\ nth_error Pm j = Some (u, x)).
          { apply find_values_preserves_index with (P := find_parents m G).
            - split. apply Hwf. apply Hcyc.
            - split. rewrite HeqU. apply nodes_map_to_assignment.
              destruct Hnode as [Hnode _]. apply Hnode.
            - intros u' Hfp. apply edge_from_parent_to_child in Hfp.
              assert (Hvv: node_in_graph u' G = true /\ node_in_graph m G = true).
              { apply edge_corresponds_to_nodes_in_well_formed. split. apply Hwf. apply Hfp. }
              destruct Hvv as [Hvv _]. apply Hvv.
            - split. apply HPm. apply Hj. }
          destruct Hx as [x [Hm' Hi']].
          assert (Hmv: m =? v = false).
          { destruct (m =? v) as [|] eqn:Hmv.
            - unfold is_mediator_bool in Hmed. apply split_and_true in Hmed. destruct Hmed as [_ Hmed].
              apply acyclic_no_self_loop with (u := v) in Hcyc. apply eqb_eq in Hmv. rewrite Hmv in Hmed.
              rewrite Hmed in Hcyc. discriminate Hcyc.
            - reflexivity. }
          assert (Hg1: g1 m (unobs, p) = x).
          { rewrite Heqg1. unfold h1. unfold g3. rewrite Hmv. unfold f2. simpl.
            assert (Hn: nth_error p j = Some x).
            { apply parent_assignments_preserves_index with (P := Pm) (V := find_parents m G) (m := u).
              repeat split.
              - symmetry. apply Hpar.
              - apply Hj.
              - apply find_values_get_assigned with (G := G) (g := g1) (P := find_parents m G) (U := U) (A := A). repeat split.
                + apply HPm.
                + apply index_exists. exists j. symmetry. apply Hj.
                + apply Hm'. }
            unfold nth_default. rewrite Hn. reflexivity. }
          rewrite Hm. rewrite Hg1. rewrite Hm'. reflexivity. }
        assert (Ha: forall (a: X), find_value G g1 u U A = Some a -> find_value G g1 v U A = Some a).
        { intros a Hu. rewrite Hv'. rewrite Hm'. apply Hu. }
        assert (Hb: exists (b: X), b <> value).
        { admit. }
        destruct Hb as [b Hb].
        specialize Ha with (a := b) as Hb'. specialize H with (a := b) (b := value) (x := b).
        apply H in Hb'.
        + specialize Ha with (a := value). apply Ha in Hf. rewrite Hf in Hb'.
          inversion Hb'. rewrite H1 in Hb. unfold not in Hb. exfalso. apply Hb. reflexivity.
        + split.
          * rewrite HeqA. apply nodes_map_to_assignment.
          * rewrite HeqU. apply nodes_map_to_assignment.
        + apply Hf. }
    unfold d_separated_bool. rewrite Hpath. simpl.
    unfold path_is_blocked_bool.
    assert (Hmedb: is_blocked_by_mediator_2 (u, v, [m]) G Z = true).
    { unfold is_blocked_by_mediator_2. unfold find_mediators_in_path. simpl. rewrite Hmed.
      apply overlap_has_member_in_common. exists m. split.
      - apply Hmem.
      - simpl. left. reflexivity. }
    rewrite Hmedb. simpl. reflexivity.
Admitted.

Theorem conditional_independence_semantics: forall X (G: graph) (u v: node),
  (exists (x: X), True) /\ G_well_formed G = true /\ contains_cycle G = false ->
  forall (Z: nodes), (* TODO need that Z is a subset? *) d_separated_bool u v G Z = true <->
  forall (A: assignments X) (U: assignments X),
    is_assignment_for A Z = true /\ is_assignment_for U (nodes_in_graph G) = true ->
    find_values_independent_2 G v u Z A U.
Proof.
  intros X G u v. intros [Hx [Hwf Hcyc]] Z. split.
  - intros Hsep A U [HA HU]. unfold find_values_independent_2. intros g a b x Ha Hb.
    admit.
  - intros H. unfold d_separated_bool.
    admit.
Admitted.

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

Lemma twin_nodes_greater_than_offset: forall V: nodes, forall o: nat, forall x: node,
  In x (get_twin_nodes V o) -> o <= x.
Proof.
  intros V o x.
  induction V as [| h t IH].
  - intros H. simpl in H. exfalso. apply H.
  - simpl. intros H. destruct H as [H | H].
    + lia.
    + apply IH. apply H.
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

Lemma duplicate_graph_maintains_dir_paths: forall (u v: node) (l: nodes) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  is_directed_path_in_graph (u, v, l) G = true <->
  is_directed_path_in_graph (u + o, v + o, shift_nodes_by_offset l o) (duplicate_graph G) = true.
Proof.
  intros u v l G o Ho.
  unfold is_directed_path_in_graph.
  generalize dependent v. generalize dependent u.
  induction l as [| h t IH].
  - intros u v. simpl. split.
    + intros H. rewrite andb_comm in H. simpl in H.
      apply duplicate_graph_maintains_edges with (o := o) in H.
      unfold node in *. rewrite H. reflexivity. apply Ho.
    + intros H. rewrite andb_comm in H. simpl in H.
      apply duplicate_graph_maintains_edges in H. rewrite H. reflexivity. apply Ho.
  - intros u v. split.
    + simpl. intros Hdir. destruct (is_edge (u, h) G) as [|] eqn:Hedge.
      * simpl in Hdir. apply duplicate_graph_maintains_edges with (o := o) in Hedge.
        unfold node in *. rewrite Hedge. simpl. specialize (IH h v). apply IH. apply Hdir. apply Ho.
      * simpl in Hdir. discriminate Hdir.
    + simpl. intros Hdir. destruct (is_edge (u + o, h + o) (duplicate_graph G)) as [|] eqn:Hedge.
      * unfold node in *. rewrite Hedge in Hdir. simpl in Hdir. apply duplicate_graph_maintains_edges in Hedge.
        unfold node in *. rewrite Hedge. simpl. specialize (IH h v). apply IH. apply Hdir. apply Ho.
      * unfold node in *. rewrite Hedge in Hdir. simpl in Hdir. discriminate Hdir.
Qed.

Lemma duplicate_graph_shifts_dir_paths: forall (u' v': node) (l': nodes) (G: graph) (o: nat),
  o = max_node_in_graph G ->
  is_directed_path_in_graph (u', v', l') (duplicate_graph G) = true ->
  exists u v l, u' = u + o /\ v' = v + o /\ l' = shift_nodes_by_offset l o.
Proof.
  intros u' v' l' G o Ho Hdir.
  generalize dependent v'. generalize dependent u'.
  induction l' as [| h t IH].
  - intros u' v' Hdir. simpl in Hdir. rewrite andb_comm in Hdir. simpl in Hdir.
    exists (u' - o). exists (v' - o). exists [].
    unfold is_edge in Hdir. destruct G as [V E]. simpl in Hdir.
    apply split_and_true in Hdir. destruct Hdir as [Hmem Hedge].
    apply split_and_true in Hmem. destruct Hmem as [Hu' Hv']. simpl in Ho.
    repeat split.
    + rewrite <- Ho in Hu'. apply member_In_equiv in Hu'.
      apply twin_nodes_greater_than_offset in Hu'. lia.
    + rewrite <- Ho in Hv'. apply member_In_equiv in Hv'.
      apply twin_nodes_greater_than_offset in Hv'. lia.
  - intros u' v' Hdir. simpl in Hdir.
    destruct (is_edge (u', h) (duplicate_graph G)) as [|] eqn:Hedge.
    + unfold is_edge in Hedge. destruct G as [V E]. simpl in Hedge.
      apply split_and_true in Hedge. destruct Hedge as [Hmem Hedge].
      apply split_and_true in Hmem. destruct Hmem as [Hu' Hh']. simpl in Ho.
      simpl in Hdir. specialize (IH h v'). apply IH in Hdir.
      destruct Hdir as [h1 [v [t' [Hh [Hv Ht]]]]].
      exists (u' - o), v, ((h - o) :: t'). repeat split.
      * rewrite <- Ho in Hu'. apply member_In_equiv in Hu'.
        apply twin_nodes_greater_than_offset in Hu'. lia.
      * apply Hv.
      * simpl. assert (Hho: h = h - o + o).
        { rewrite <- Ho in Hh'. apply member_In_equiv in Hh'.
          apply twin_nodes_greater_than_offset in Hh'. lia. }
        rewrite <- Hho. f_equal. apply Ht.
    + simpl in Hdir. discriminate Hdir.
Qed.

Lemma duplicate_graph_maintains_descendants: forall (u: node) (G: graph) (o: nat) (d: node),
  o = max_node_in_graph G ->
  In d (find_descendants u G) <->
  In (d + o) (find_descendants (u + o) (duplicate_graph G)).
Proof.
  intros u G o d Ho. split.
  - intros Hd. apply find_descendants_correct in Hd.
    destruct Hd as [p [Hdir Hse]].
    destruct p as [[u' d'] l]. apply path_start_end_equal in Hse. destruct Hse as [Hu Hd].
    apply find_descendants_correct.
    exists (u + o, d + o, shift_nodes_by_offset l o). split.
    + rewrite Hu in Hdir. rewrite Hd in Hdir.
      apply duplicate_graph_maintains_dir_paths with (o := o) in Hdir. apply Hdir. apply Ho.
    + apply path_start_end_refl.
  - intros Hd. apply find_descendants_correct in Hd.
    destruct Hd as [p' [Hdir Hse]].
    destruct p' as [[u' d'] l'].
    apply duplicate_graph_shifts_dir_paths with (o := o) in Hdir as Huvl.
    destruct Huvl as [u1 [d1 [l [Hu1 [Hd1 Hl]]]]].
    apply path_start_end_equal in Hse. destruct Hse as [Hu Hd].
    + apply find_descendants_correct. exists (u, d, l). split.
      * rewrite Hu in Hdir. rewrite Hd in Hdir. rewrite Hl in Hdir.
        apply duplicate_graph_maintains_dir_paths in Hdir. apply Hdir. apply Ho.
      * apply path_start_end_refl.
    + apply Ho.
Qed.

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
      { rewrite Hc'. rewrite Heqd'. apply duplicate_graph_maintains_descendants.
        - apply Ho.
        - apply Hdesc. }
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
        { apply duplicate_graph_maintains_descendants with (o := o).
          - apply Ho.
          - rewrite <- Heqc'.
            assert (Hd': d' = d + o).
            { assert (Hdo': o <= d'). { apply shift_greater_than_offset in HdZ'. apply HdZ'. }
              lia. }
            rewrite <- Hd'. apply Hdesc'. }
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

Definition create_initial_twin_network {X: Type} (G: graph) (obs: assignments X) (cf: assignments X): graph :=
  match G with
  | (V, E) => let duplicate_G := create_duplicate_network G in
              (do_several (do_several duplicate_G (fsts obs)) (shift_list (fsts cf) (max_list V)))
  end.

Example twin_1: create_initial_twin_network ([1;2;3], [(1, 2); (3, 2)]) [] [(1, 70)]
  = ([1;2;3;4;5;6;9;8;7], [(1,2); (3,2); (4,5); (6,5); (9,3); (9,6); (8,2); (8,5); (7,1)]).
Proof. reflexivity. Qed.

Definition create_twin_network_before_preprocess {X: Type} (G: graph) (obs cf: assignments X): graph :=
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




