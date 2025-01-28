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
  forall (p : nodes), (acyclic_path p = true) <-> forall (x: node), (count x p = 0) \/ (count x p = 1).
Proof.
  intros p. split.
  { intros Hcyc x.
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
      * apply Hcyc. }
  { intros Hx. induction p as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (member h t) as [|] eqn:Hmem.
    + apply member_In_equiv in Hmem. apply member_count_at_least_1 in Hmem.
      assert (Hc: count h (h :: t) >= 2). { simpl. rewrite eqb_refl. lia. }
      specialize Hx with (x := h). destruct Hx as [Hx | Hx]. rewrite Hx in Hc. lia. rewrite Hx in Hc. lia.
    + simpl. apply IH. intros x. specialize Hx with (x := x). destruct Hx as [Hx | Hx].
      * left. simpl in Hx. destruct (h =? x) as [|] eqn:Hhx. lia. apply Hx.
      * simpl in Hx. destruct (h =? x) as [|] eqn:Hhx.
        -- inversion Hx. left. reflexivity.
        -- right. apply Hx. }
Qed.

Lemma acyclic_path_reverse: forall (p: nodes),
  acyclic_path p = true -> acyclic_path (rev p) = true.
Proof.
  intros p H.
  destruct p as [| h t].
  - simpl. reflexivity.
  - simpl. simpl in H. apply acyclic_path_intermediate_nodes. intros x. apply acyclic_path_intermediate_nodes with (p := h :: t) (x := x) in H.
    destruct H as [H | H].
    + simpl in H. destruct (h =? x) as [|] eqn:Hhx.
      * lia.
      * left. rewrite count_app. rewrite <- count_reverse. simpl. rewrite Hhx. rewrite H. reflexivity.
    + simpl in H. destruct (h =? x) as [|] eqn:Hhx.
      * inversion H. right. rewrite H1. rewrite count_app. rewrite <- count_reverse. rewrite H1. simpl. rewrite Hhx. reflexivity.
      * right. rewrite count_app. rewrite <- count_reverse. simpl. rewrite Hhx. rewrite H. reflexivity.
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

Theorem acyclic_path_correct_2 : 
  forall (p : path), 
    (acyclic_path_2 p) -> acyclic_path ((path_start p) :: (path_int p) ++ [path_end p]) = true. 
Proof.
  intros [[u v] l]. generalize dependent v. generalize dependent u. induction l as [| h t IH].
  - intros u v H. simpl. destruct (v =? u) as [|] eqn:Hvu.
    + simpl in H. destruct H as [H].
      apply eqb_neq in H. apply eqb_eq in Hvu. rewrite Hvu in H. 
      rewrite -> eqb_refl in H. discriminate H.
    + reflexivity.
  - intros u v H. simpl. destruct (h =? u) as [|] eqn:Hhu.
    + simpl in H. destruct H as [_ [H _]]. exfalso. apply H. left. apply eqb_eq. apply Hhu.
    + destruct (member u (t ++ [v])) as [|] eqn:Hmem.
      * apply member_In_equiv in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
        -- simpl in H. destruct H as [_ [H _]]. exfalso. apply H. right. apply Hmem.
        -- simpl in Hmem. destruct Hmem as [Hmem | F].
           ++ simpl in H. destruct H as [H _]. exfalso. apply H. rewrite Hmem. reflexivity.
           ++ exfalso. apply F.
      * simpl. apply IH. simpl in H. unfold acyclic_path_2. repeat split.
        -- destruct H as [_ [_ [H _]]]. intros Hhv. apply H. left. apply Hhv.
        -- destruct H as [_ [_ [_ H]]]. apply split_and_true in H. destruct H as [H _]. intros F. apply member_In_equiv in F. rewrite F in H. discriminate H.
        -- destruct H as [_ [_ [H _]]]. intros Hhv. apply H. right. apply Hhv.
        -- destruct H as [_ [_ [_ H]]]. apply split_and_true in H. destruct H as [_ H]. destruct t as [| h0 t0]. apply I. apply H.
Qed.

Theorem reverse_path_still_acyclic: forall (u v: node) (l: nodes),
  acyclic_path_2 (u, v, l) -> acyclic_path_2 (v, u, rev l).
Proof.
  intros u v l H. generalize dependent u. destruct l as [| h t].
  - intros u H. simpl in H. destruct H as [H _]. simpl. repeat split.
    + intros Hvu. apply H. symmetry. apply Hvu.
    + intros F. apply F.
    + intros F. apply F.
  - intros u H. simpl. repeat split.
    + simpl in H. destruct H as [H _]. intros Hvu. apply H. symmetry. apply Hvu.
    + simpl in H. intros Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
      * apply membership_rev in Hmem. rewrite <- reverse_list_twice in Hmem.
        destruct H as [_ [_ [H _]]]. apply H. right. apply Hmem.
      * destruct H as [_ [_ [H _]]]. apply H. left. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. apply Hmem. exfalso. apply Hmem.
    + simpl in H. intros Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
      * destruct H as [_ [H _]]. rewrite membership_rev in Hmem. apply H. right. apply Hmem.
      * destruct H as [_ [H _]]. apply H. left. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. apply Hmem. exfalso. apply Hmem.
    + simpl in H. destruct H as [_ [_ [_ H]]].
      assert (acyclic_path (h :: t) = true). { simpl. apply H. } apply acyclic_path_reverse in H0. simpl in H0.
      destruct (rev t ++ [h]) as [| h0 t0].
      * apply I.
      * simpl in H0. apply H0.
Qed.

Lemma subpath_still_acyclic: forall (w u v: node) (l1 l2 l3: nodes),
  l1 ++ [u] ++ l2 = l3 /\ acyclic_path_2 (w, v, l3)
  -> acyclic_path_2 (u, v, l2).
Proof.
  intros w u v l1 l2 l3. intros [Hl Hcyc].

  generalize dependent u. generalize dependent l1. induction l2 as [| h t IH].
  - intros l1 u Hl. simpl. repeat split.
    + intros Huv. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [_ Hcyc].
      apply acyclic_path_intermediate_nodes with (x := v) in Hcyc. destruct Hcyc as [Hc | Hc].
      * rewrite <- Hl in Hc. simpl in Hc. rewrite <- Huv in Hc. rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia.
      * rewrite <- Hl in Hc. simpl in Hc. rewrite <- Huv in Hc. repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia.
    + easy.
    + easy.
  - intros l1 u Hl. simpl.
    assert (H: forall (z: node), In z ([u] ++ h :: t) -> (z = u /\ In z (h :: t)) \/ z = v -> False).
    { intros z Hz Hzv. destruct Hzv as [Hzv | Hzv].
      { destruct Hzv as [Hzu Hzl2]. apply membership_splits_list in Hzl2. destruct Hzl2 as [lz1 [lz2 Hzl2]]. rewrite <- Hzl2 in Hl.
      apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [_ Hcyc].
      apply acyclic_path_intermediate_nodes with (x := z) in Hcyc. destruct Hcyc as [Hc | Hc].
      * rewrite <- Hl in Hc. simpl in Hc. rewrite <- Hzu in Hc. repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia.
      * rewrite <- Hl in Hc. simpl in Hc. rewrite <- Hzu in Hc. repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc.
        rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia. }
      { apply membership_splits_list in Hz. destruct Hz as [lz1 [lz2 Hz]]. rewrite <- Hz in Hl.
      apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [_ Hcyc].
      apply acyclic_path_intermediate_nodes with (x := v) in Hcyc. destruct Hcyc as [Hc | Hc].
      * rewrite <- Hl in Hc. simpl in Hc. rewrite <- Hzv in Hc. rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia.
      * rewrite <- Hl in Hc. simpl in Hc. rewrite <- Hzv in Hc. repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia. } }

    repeat split.
    + intros Huv. apply H with (z := u). left. reflexivity. right. apply Huv.
    + intros Hh. destruct Hh as [Hh | Hh].
      * apply H with (z := h).
        -- right. left. reflexivity.
        -- left. split. apply Hh. left. reflexivity.
      * apply H with (z := u).
        -- left. reflexivity.
        -- left. split. reflexivity. right. apply Hh.
    + intros Hh. destruct Hh as [Hh | Hh].
      * apply H with (z := h).
        -- right. left. reflexivity.
        -- right. apply Hh.
      * apply H with (z := v).
        -- right. right. apply Hh.
        -- right. reflexivity.
    + specialize IH with (l1 := l1 ++ [u]) (u := h). unfold acyclic_path_2 in IH. simpl in IH.
      rewrite app_assoc in Hl. apply IH in Hl. destruct t as [| h' t'].
      * simpl. reflexivity.
      * simpl. destruct Hl as [_ [Hh [_ Hl]]]. rewrite Hl.
        destruct (h' =? h) as [|] eqn:Hh'.
        -- exfalso. apply Hh. left. apply eqb_eq. apply Hh'.
        -- destruct (member h t') as [|] eqn:Hmem.
           ++ exfalso. apply Hh. right. apply member_In_equiv. apply Hmem.
           ++ reflexivity.
Qed.

Lemma concat_paths_acyclic: forall (w u v: node) (l1 l2: nodes),
  u <> v /\ acyclic_path_2 (u, w, l1) /\ acyclic_path_2 (w, v, l2)
  -> ~(In u l2) /\ ~(In v l1)
  -> overlap l1 l2 = false
  -> acyclic_path_2 (concat u w v l1 l2).
Proof.
  intros w u v l1 l2. intros [Huv [Hcycu Hcycv]]. intros [Hul2 Hvl1]. intros Hover. unfold concat.
  unfold acyclic_path_2. repeat split.
  * apply Huv.
  * intros Hu. apply membership_append_or in Hu. destruct Hu as [Hu | Hu].
    { unfold acyclic_path_2 in Hcycu.
      destruct Hcycu as [_ [Hcycu _]]. apply Hcycu. apply Hu. }
    { destruct Hu as [Hu | Hu].
    -- unfold acyclic_path_2 in Hcycu. destruct Hcycu as [Hcycu _]. apply Hcycu. rewrite Hu. reflexivity.
    -- apply Hul2. apply Hu. }
  * unfold acyclic_path_2 in Hcycv. intros Hv. apply membership_append_or in Hv. destruct Hv as [Hv | Hv].
    { exfalso. apply Hvl1. apply Hv. }
    { destruct Hv as [Hv | Hv].
    -- destruct Hcycv as [Hcycv _]. apply Hcycv. apply Hv.
    -- destruct Hcycv as [_ [_ [Hcycv _]]]. apply Hcycv. apply Hv. }
  * generalize dependent u. induction l1 as [| h1 t1 IH].
    -- intros u Huv Hcycu Hul2. simpl. unfold acyclic_path_2 in Hcycv. destruct Hcycv as [_ [Hwl2 [_ Hcycv]]].
       destruct (member w l2) as [|] eqn:Hwl2'.
       ++ exfalso. apply Hwl2. apply member_In_equiv. apply Hwl2'.
       ++ simpl. destruct l2 as [| h2 t2]. simpl. reflexivity. apply Hcycv.
    -- intros u Huv Hcycu Hul2. simpl. destruct (member h1 (t1 ++ w :: l2)) as [|] eqn:Hmem.
       ++ apply member_In_equiv in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
          ** simpl in Hcycu. destruct Hcycu as [_ [_ [_ Hcycu]]]. apply split_and_true in Hcycu. destruct Hcycu as [Hcycu _].
             apply member_In_equiv in Hmem. rewrite Hmem in Hcycu. discriminate Hcycu.
          ** destruct Hmem as [Hmem | Hmem].
             --- simpl in Hcycu. destruct Hcycu as [_ [_ [Hcycu _]]]. exfalso. apply Hcycu. left. rewrite Hmem. reflexivity.
             --- apply no_overlap_non_member with (x := h1) in Hover.
                 +++ exfalso. apply Hover. left. reflexivity.
                 +++ apply Hmem.
       ++ simpl. destruct (t1 ++ w :: l2) as [| h' t'].
          ** simpl. reflexivity.
          ** apply IH with (u := h1).
             --- intros H. apply Hvl1. right. apply H.
             --- simpl in Hover. destruct (member h1 l2). discriminate Hover. apply Hover.
             --- intros H. apply Hvl1. left. apply H.
             --- apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h1 :: t1). split.
                 simpl. reflexivity. apply Hcycu.
             --- intros H. apply no_overlap_non_member with (x := h1) in Hover.
                 +++ apply Hover. left. reflexivity.
                 +++ apply H.
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

Lemma reverse_path_in_graph: forall (G: graph) (u v: node) (l: nodes),
  is_path_in_graph (u, v, l) G = true -> is_path_in_graph (v, u, rev l) G = true.
Proof.
  intros [V E] u v l H.
  generalize dependent v. generalize dependent u. induction l as [| h t IH].
  - intros u v H. simpl in H. rewrite andb_comm in H. simpl in H. simpl.
    rewrite orb_comm in H. rewrite H. reflexivity.
  - intros u v H. specialize IH with (u := h) (v := v). simpl in H. apply split_and_true in H.
    destruct H as [H1 H2]. apply IH in H2. replace (rev (h :: t)) with ((rev t) ++ [h]).
    + simpl. simpl in H2. admit.
Admitted.

Theorem concat_paths_still_a_path: forall u1 mid v2: node, forall l1 l2: nodes, forall G: graph,
  is_path_in_graph (u1, mid, l1) G = true /\ is_path_in_graph (mid, v2, l2) G = true
  -> is_path_in_graph (concat u1 mid v2 l1 l2) G = true.
Proof.
Admitted.

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

Theorem directed_path_has_directed_edge: forall (u v: node) (l: nodes) (G: graph),
  is_directed_path_in_graph (u, v, l) G = true
  -> exists (x: node), node_in_path x (u, v, l) = true /\ is_edge (x, v) G = true.
Proof.
  intros u v l G H.
  generalize dependent v. generalize dependent u. induction l as [| h t IH].
  - intros u v H. simpl in H. exists u. split.
    + unfold node_in_path. simpl. rewrite eqb_refl. simpl. reflexivity.
    + rewrite andb_comm in H. simpl in H. apply H.
  - intros u v H. specialize IH with (u := h) (v := v). simpl in H. apply split_and_true in H. destruct H as [_ H].
    apply IH in H. destruct H as [x [H1 H2]]. exists x. split.
    + unfold node_in_path. simpl. unfold node_in_path in H1. simpl in H1. destruct (h =? x) as [|] eqn:Hhx.
      * rewrite orb_comm. reflexivity.
      * rewrite eqb_sym in Hhx. rewrite Hhx in H1. simpl in H1. rewrite split_orb_true in H1. destruct H1 as [H1 | H1].
        -- rewrite H1. rewrite orb_comm. rewrite orb_assoc. rewrite orb_comm. reflexivity.
        -- rewrite H1. rewrite orb_comm. reflexivity.
    + apply H2.
Qed.

Theorem directed_path_has_directed_edge_end: forall (u v: node) (l: nodes) (G: graph),
  is_directed_path_in_graph (u, v, l) G = true
  -> l = [] \/ exists (l': nodes) (x: node), l = l' ++ [x] /\ is_edge (x, v) G = true.
Proof.
  intros u v l G H.
  generalize dependent v. generalize dependent u. induction l as [| h t IH].
  - intros u v H. left. reflexivity.
  - intros u v H. right. specialize IH with (u := h) (v := v). simpl in H. apply split_and_true in H. destruct H as [Hedge H].
    apply IH in H as H'. destruct H' as [H' | H'].
    + rewrite H'. exists []. exists h. split.
      * simpl. reflexivity.
      * rewrite H' in H. simpl in H. rewrite andb_comm in H. simpl in H. apply H.
    + destruct H' as [l' [x [Ht Hx]]].
      * exists (h :: l'). exists x. split.
        -- simpl. rewrite <- Ht. reflexivity.
        -- apply Hx.
Qed.

Theorem directed_path_has_directed_edge_start: forall (u v: node) (l: nodes) (G: graph),
  is_directed_path_in_graph (u, v, l) G = true
  -> exists (x: node), node_in_path x (u, v, l) = true /\ is_edge (u, x) G = true.
Proof.
  intros u v l G H.
  destruct l as [| h t].
  - exists v. split.
    + unfold node_in_path. simpl. rewrite orb_comm. rewrite orb_assoc. rewrite orb_comm. rewrite eqb_refl. reflexivity.
    + simpl in H. rewrite andb_comm in H. simpl in H. apply H.
  - exists h. split.
    + unfold node_in_path. simpl. rewrite eqb_refl. rewrite orb_comm. reflexivity.
    + simpl in H. apply split_and_true in H. destruct H as [H _]. apply H.
Qed.

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

Theorem subpath_still_directed: forall (w u v: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ is_directed_path_in_graph (w, v, l3) G = true
  -> is_directed_path_in_graph (u, v, l2) G = true.
Proof.
  intros w u v l1 l2 l3 G. intros [Hl Hdir].
  generalize dependent l3. generalize dependent w. induction l1 as [| h t IH].
  - intros w l3 Hl Hdir. simpl in Hl. rewrite <- Hl in Hdir. simpl in Hdir. apply split_and_true in Hdir. destruct Hdir as [_ Hdir].
    apply Hdir.
  - intros w l3 Hl Hdir. specialize IH with (w := h) (l3 := (t ++ [u] ++ l2)). apply IH.
    + reflexivity.
    + simpl in Hl. rewrite <- Hl in Hdir. simpl in Hdir. apply split_and_true in Hdir. destruct Hdir as [_ Hdir]. apply Hdir.
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

Fixpoint add_nodes_no_repeats (S: nodes) (V: nodes) : nodes :=
  match S with
  | [] => V
  | h :: t => if (member h V) then add_nodes_no_repeats t V else add_nodes_no_repeats t (h :: V)
  end.

Example test_add_nodes_1: add_nodes_no_repeats [1; 2; 3] [1; 2; 3] = [1; 2; 3].
Proof. reflexivity. Qed.

Example test_add_nodes_2: add_nodes_no_repeats [1; 2; 3] [1; 3] = [2; 1; 3].
Proof. reflexivity. Qed.

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

Lemma acyclic_no_two_cycle: forall (G: graph) (u v: node),
  contains_cycle G = false -> is_edge (u, v) G = true -> is_edge (v, u) G = false.
Proof.
  intros G u v Hcyc He.
  destruct (is_edge (v, u) G) as [|] eqn:Hvu.
  - apply contains_cycle_false_correct with (p := (u, u, [v])) in Hcyc.
    + simpl in Hcyc. destruct Hcyc as [F _]. exfalso. apply F. reflexivity.
    + simpl. rewrite He. rewrite Hvu. simpl. destruct G as [V E]. reflexivity.
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

Definition find_directed_paths_to_end (t: node) (G: graph): paths :=
  filter (fun (p: path) => path_end p =? t)
         (snd (dfs_extend_by_edges_iter (edges_in_graph G) (directed_edges_as_paths (edges_in_graph G)) (num_nodes G))).


Example directed_paths_from_1: find_directed_paths_from_start 1 G = [(1, 2, [])].
Proof. reflexivity. Qed.

Example directed_paths_from_3: find_directed_paths_from_start 3 G = [(3, 2, []); (3, 1, []); (3, 2, [1])].
Proof. reflexivity. Qed.

Example directed_paths_to_1: find_directed_paths_to_end 4 G = [].
Proof. reflexivity. Qed.

Example directed_paths_to_2: find_directed_paths_to_end 2 G = [(1, 2, []); (3, 2, []); (4, 2, [1]); (3, 2, [1])].
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
Proof. (* TODO this does not work for u = v!!! *)
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

Lemma not_assigned_app: forall X (A1 A2: assignments X) (w: node),
  is_assigned A1 w = false /\ is_assigned A2 w = false -> is_assigned (A1 ++ A2) w = false.
Proof.
  intros X A1 A2 w [H1 H2].
  induction A1 as [| h t IH].
  - simpl. apply H2.
  - simpl. simpl in H1. apply split_orb_false in H1. destruct H1 as [Hwh H1].
    rewrite Hwh. simpl. apply IH. apply H1.
Qed.

Lemma is_assigned_membership: forall X (A: assignments X) (w: node),
  is_assigned A w = true <-> exists (x: X), In (w, x) A.
Proof.
  intros X A w. split.
  { intros H.
  induction A as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + simpl. destruct h as [h1 h2]. exists h2. left. simpl in H. apply eqb_eq in H. rewrite H. reflexivity.
    + apply IH in H. destruct H as [x H]. exists x. right. apply H. }
  { intros [x H].
  induction A as [| h t IH].
  - exfalso. apply H.
  - simpl in H. destruct H as [H | H].
    + simpl. rewrite H. simpl. rewrite eqb_refl. reflexivity.
    + apply IH in H. simpl. rewrite orb_comm. rewrite H. reflexivity. }
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

Lemma is_assignment_for_app: forall X (A B: assignments X) (V: nodes),
  is_assignment_for A V = true -> is_assignment_for (A ++ B) V = true.
Proof.
  intros X A B V H. unfold is_assignment_for in H. unfold is_assignment_for.
  apply forallb_true_iff_mem. intros x Hmem.
  apply forallb_true with (x := x) in H.
  - apply is_assigned_app. apply H.
  - apply Hmem.
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
  (exists x: X, get_assigned_value A u = Some x) <-> is_assigned A u = true.
Proof.
  intros X A u. split.
  { intros [x H].
  induction A as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. destruct (fst h =? u) as [|] eqn:Hhu.
    + simpl. apply eqb_eq in Hhu. rewrite Hhu. rewrite eqb_refl. simpl. reflexivity.
    + simpl. apply IH in H. rewrite H. rewrite orb_comm. simpl. reflexivity. }
  { intros H. induction A as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. destruct (u =? fst h) as [|] eqn:Hhu.
    + simpl. apply eqb_eq in Hhu. rewrite Hhu. rewrite eqb_refl. exists (snd h). reflexivity.
    + simpl in H. apply IH in H. simpl. rewrite eqb_sym. rewrite Hhu. apply H. }
Qed.

Lemma assigned_is_false: forall X (A: assignments X) (u: node),
  is_assigned A u = false <-> get_assigned_value A u = None.
Proof.
  intros X A u. split.
  { intros H. induction A as [| h t IH].
  - simpl. reflexivity.
  - simpl in H. destruct (u =? fst h) as [|] eqn:Huh.
    + simpl in H. discriminate H.
    + simpl. rewrite eqb_sym. rewrite Huh. apply IH.
      simpl in H. apply H. }
  { intros H. induction A as [| h t IH].
  - simpl. reflexivity.
  - simpl. simpl in H. destruct (fst h =? u) as [|] eqn:Hhu.
    + discriminate H.
    + rewrite eqb_sym. rewrite Hhu. simpl. apply IH. apply H. }
Qed.

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

Definition is_exact_assignment_for {X: Type} (A: assignments X) (Z: nodes) : Prop :=
  is_assignment_for A Z = true /\ forall (u: node), member u Z = false -> is_assigned A u = false.

Lemma assigned_true_then_in_list: forall X (A: assignments X) (u: node) (L: nodes),
  is_assigned A u = true /\ is_exact_assignment_for A L -> In u L.
Proof.
  intros X A u L [Hu [HA Hf]].
  destruct (member u L) as [|] eqn:Hmem.
  - apply member_In_equiv. apply Hmem.
  - specialize Hf with (u := u). apply Hf in Hmem. rewrite Hmem in Hu. discriminate Hu.
Qed.

Lemma nodes_map_to_exact_assignment: forall X (V: nodes) (a: X),
  is_exact_assignment_for (get_assignment_for V a) V.
Proof.
  intros X V a.
  unfold is_exact_assignment_for. split.
  - apply nodes_map_to_assignment.
  - induction V as [| h t IH].
    + simpl. reflexivity.
    + simpl. intros u H. destruct (h =? u) as [|] eqn:Hhu.
      * discriminate H.
      * rewrite eqb_sym. rewrite Hhu. simpl. specialize IH with (u := u). apply IH. apply H.
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

Lemma find_value_evaluates_to_g {X: Type}: forall (G: graph) (g: graphfun) (U: assignments X) (u: node),
  (G_well_formed G = true /\ contains_cycle G = false) /\ is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph u G = true
  -> exists (P: assignments X), find_values G g (find_parents u G) U [] = Some P
  /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents u G)
  /\ exists (unobs: X), get_assigned_value U u = Some unobs
  /\ find_value G g u U [] = Some (g u (unobs, pa)).
Proof.
  intros G g U u. intros [HG [HU HuG]].
  assert (HP: exists (P: assignments X), find_values G g (find_parents u G) U [] = Some P
              /\ find_value G g u U [] = get_value_of_node u G g U [] P).
  { apply find_value_gives_value_of_node with (A := []).
    - apply HG.
    - split. apply HU. apply HuG. }
  destruct HP as [P [HP Hu]]. exists P. split.
  - apply HP.
  - unfold get_value_of_node in Hu. simpl in Hu.
    apply find_values_assignment in HP as HP'.
    assert (Hpar: exists p, Some p = get_parent_assignments P (find_parents u G)).
    { apply parent_assignments_exist. apply HP'. }
    destruct Hpar as [pa Hpar]. exists pa. split.
    + apply Hpar.
    + rewrite <- Hpar in Hu.
      assert (HuU: exists (unobs: X), get_assigned_value U u = Some unobs).
      { apply assigned_has_value with (L := nodes_in_graph G). split.
        - destruct G as [V E]. simpl. simpl in HuG. apply member_In_equiv. apply HuG.
        - apply HU. }
      destruct HuU as [unobs HuU]. exists unobs. split.
      * apply HuU.
      * rewrite HuU in Hu. apply Hu.
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

Lemma path_must_have_direction: forall p: path, forall G: graph,
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

Lemma path_must_have_direction_2: forall p: path, forall G: graph,
  is_path_in_graph p G = true -> path_out_of_start p G = false -> path_into_start p G = true.
Proof.
  intros p G.
  intros p_in_G p_not_out.
  destruct p as [[u v] l].
  simpl. destruct l as [| h t].
  - simpl in p_not_out. simpl in p_in_G. destruct G as [V E].
    rewrite p_not_out in p_in_G. simpl in p_in_G. apply andb_true_elim2 in p_in_G. apply p_in_G.
  - simpl in p_not_out. simpl in p_in_G. destruct G as [V E]. apply andb_true_elim2 in p_in_G.
    rewrite p_not_out in p_in_G. simpl in p_in_G. apply p_in_G.
Qed.

Theorem acyclic_path_one_direction: forall (p: path) (G: graph),
  is_path_in_graph p G = true /\ contains_cycle G = false
  -> path_into_start p G = false <-> path_out_of_start p G = true.
Proof.
  intros p G [HpG Hcyc]. split.
  - apply path_must_have_direction. apply HpG.
  - destruct p as [[u v] l]. destruct l as [| h t].
    + simpl. intros Hout. apply acyclic_no_two_cycle.
      * apply Hcyc.
      * apply Hout.
    + simpl. intros Hout. apply acyclic_no_two_cycle.
      * apply Hcyc.
      * apply Hout.
Qed.

Theorem acyclic_path_one_direction_2: forall (p: path) (G: graph),
  is_path_in_graph p G = true /\ contains_cycle G = false
  -> path_into_start p G = true <-> path_out_of_start p G = false.
Proof.
  intros p G [HpG Hcyc]. split.
  - destruct p as [[u v] l]. destruct l as [| h t].
    + simpl. intros Hin. apply acyclic_no_two_cycle.
      * apply Hcyc.
      * apply Hin.
    + simpl. intros Hin. apply acyclic_no_two_cycle.
      * apply Hcyc.
      * apply Hin.
  - apply path_must_have_direction_2. apply HpG.
Qed.

Fixpoint path_into_end_nodes (p: nodes) (G: graph): option bool :=
  match p with
  | [] => None
  | h :: [] => None
  | h :: h' :: [] => Some (is_edge (h, h') G)
  | h :: t => path_into_end_nodes t G
  end.

Definition path_into_end (p: path) (G: graph): option bool :=
  match p with
  | (u, v, l) => path_into_end_nodes (u :: l ++ [v]) G
  end.

Fixpoint path_out_of_end_nodes (p: nodes) (G: graph): option bool :=
  match p with
  | [] => None
  | h :: [] => None
  | h :: h' :: [] => Some (is_edge (h', h) G)
  | h :: t => path_out_of_end_nodes t G
  end.

Definition path_out_of_end (p: path) (G: graph): option bool :=
  match p with
  | (u, v, l) => path_out_of_end_nodes (u :: l ++ [v]) G
  end.

Example path_out_of_end_1: path_out_of_end (2, 4, [1]) G = Some true /\ path_into_end (2, 4, [1]) G = Some false.
Proof. split. reflexivity. reflexivity. Qed.

Example path_out_of_end_2: path_out_of_end (2, 1, [3]) G = Some false /\ path_into_end (2, 1, [3]) G = Some true.
Proof. split. reflexivity. reflexivity. Qed.


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

Theorem directed_path_all_mediators: forall (u v m: node) (l: nodes) (G: graph),
  is_directed_path_in_graph (u, v, l) G = true /\ In m l -> In m (find_mediators_in_path (u, v, l) G).
Proof.
Admitted.

Theorem mediators_same_in_reverse_path: forall (u v m: node) (l: nodes) (G: graph),
  In m (find_mediators_in_path (u, v, l) G) -> In m (find_mediators_in_path (v, u, rev l) G).
Proof. (* TODO need to change defn of mediators to include this *)
Admitted.

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

Theorem confounders_same_in_reverse_path: forall (u v m: node) (l: nodes) (G: graph),
  In m (find_confounders_in_path (u, v, l) G) -> In m (find_confounders_in_path (v, u, rev l) G).
Proof.
(* TODO use sublist theorem *)
Admitted.

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

Theorem colliders_vs_edges_in_path: forall (l: nodes) (G: graph) (x: node),
  In x (find_colliders_in_nodes l G)
    <-> exists y z: node, sublist [y; x; z] l = true /\ is_edge (y, x) G = true /\ is_edge (z, x) G = true.
Proof.
  intros l G x. split.
  { intros Hcol. induction l as [| h t IH].
  - simpl in Hcol. exfalso. apply Hcol.
  - destruct t as [| h' t'].
    + simpl in Hcol. exfalso. apply Hcol.
    + destruct t' as [| h'' t''].
      * simpl in Hcol. exfalso. apply Hcol.
      * destruct (is_collider_bool h h'' h' G) as [|] eqn:Hcol2.
        -- simpl in Hcol. rewrite Hcol2 in Hcol. simpl in Hcol. destruct Hcol as [Hhx | Hind].
           { exists h. exists h''. split.
             - rewrite <- Hhx. simpl.
               rewrite eqb_refl. simpl. rewrite eqb_refl. simpl. rewrite eqb_refl. reflexivity.
             - unfold is_collider_bool in Hcol2. apply split_and_true in Hcol2.
               rewrite <- Hhx. apply Hcol2. }
           { apply IH in Hind. destruct Hind as [y Hind]. destruct Hind as [z Hind].
             exists y. exists z. split.
             - destruct Hind as [Hsub _]. simpl. apply split_orb_true. right. apply Hsub.
             - destruct Hind as [_ Hedge]. apply Hedge. }
        -- simpl in Hcol. rewrite Hcol2 in Hcol. simpl in Hcol. apply IH in Hcol.
           destruct Hcol as [y [z Hcol]]. exists y. exists z.
           split.
           { destruct Hcol as [Hsub _]. simpl. apply split_orb_true. right. apply Hsub. }
           { destruct Hcol as [_ Hedge]. apply Hedge. } }
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
           assert (Hcol: (is_collider_bool h h'' h' G) = true).
           { unfold is_collider_bool.
             rewrite eqb_eq in Hy. rewrite <- Hy.
             rewrite eqb_eq in Hx. rewrite <- Hx.
             rewrite eqb_eq in Hz. rewrite <- Hz.
             destruct Hedge as [Hyx Hxz]. rewrite Hyx. rewrite Hxz. reflexivity. }
           simpl. rewrite Hcol. simpl. left. rewrite eqb_eq in Hx. rewrite Hx. reflexivity.
        -- apply IH in Hind. destruct (is_collider_bool h h'' h' G) as [|] eqn:Hcol.
           { simpl. rewrite Hcol. simpl. right. apply Hind. }
           { simpl. rewrite Hcol. apply Hind. } }
Qed.

Theorem colliders_same_in_reverse_path: forall (u v m: node) (l: nodes) (G: graph),
  In m (find_colliders_in_path (u, v, l) G) -> In m (find_colliders_in_path (v, u, rev l) G).
Proof.
(* TODO use sublist theorem *)
Admitted.



Lemma concat_preserves_colliders: forall (G: graph) (u m v c: node) (l1 l2: nodes),
  In c (find_colliders_in_path (u, m, l1) G) -> In c (find_colliders_in_path (concat u m v l1 l2) G).
Proof.
  intros G u m v c l1 l2 H.
  apply colliders_vs_edges_in_path in H. destruct H as [y [z [Hsub Hedge]]].
  unfold concat. unfold find_colliders_in_path. apply colliders_vs_edges_in_path. exists y. exists z.
  split.
  - rewrite app_comm_cons. replace (m :: l2) with ([m] ++ l2). 
    + apply sublist_breaks_down_list in Hsub. destruct Hsub as [sl1 [sl2 Hl]].
      apply sublist_breaks_down_list. exists sl1. exists (sl2 ++ l2 ++ [v]). rewrite app_assoc. rewrite app_assoc in Hl.
      rewrite app_assoc. rewrite Hl. simpl. rewrite append_vs_concat. unfold node. f_equal. apply rearrange_list_concat_app.
    + simpl. reflexivity.
  - apply Hedge.
Qed.

Lemma concat_preserves_mediators_r: forall (G: graph) (u mid v m: node) (l1 l2: nodes),
  In m (find_mediators_in_path (mid, v, l2) G) -> In m (find_mediators_in_path (concat u mid v l1 l2) G).
Proof.
  intros G u mid v m l1 l2 H.
  apply mediators_vs_edges_in_path in H. destruct H as [y [z [Hsub Hedge]]].
  unfold concat. unfold find_mediators_in_path. apply mediators_vs_edges_in_path. exists y. exists z.
  split.
  - apply sublist_breaks_down_list in Hsub. destruct Hsub as [l3 [l4 Hsub]].
    rewrite <- app_assoc. apply sublist_breaks_down_list. exists (u :: l1 ++ l3). exists l4.
    simpl. rewrite <- Hsub. simpl. rewrite <- app_assoc. reflexivity.
  - apply Hedge.
Qed.

Lemma prefix_of_long_list: forall (l1 l2 p: list nat),
  prefix p (l1 ++ l2) = true
  -> prefix p l1 = true \/ (exists (p': list nat), prefix p' l2 = true /\ l1 ++ p' = p).
Proof.
  intros l1 l2 p H.
  generalize dependent l1. induction p as [| h t IH].
  - intros l1 H. left. simpl. reflexivity.
  - intros l1 H. destruct l1 as [| h1 t1].
    + right. exists (h :: t). split. apply H. reflexivity.
    + simpl in H. apply split_and_true in H. destruct H as [H1 H2].
      specialize IH with (l1 := t1). apply IH in H2. destruct H2 as [H2 | H2].
      * left. simpl. rewrite H1. rewrite H2. reflexivity.
      * right. destruct H2 as [p' [H2 H3]]. exists p'. split. apply H2. simpl. rewrite H3. apply eqb_eq in H1. rewrite H1. reflexivity.
Qed.

Lemma sublist_of_long_list: forall (l1 l2 sl: list nat),
  sublist sl (l1 ++ l2) = true
  -> sublist sl l1 = true \/ (exists (sl1 sl2: list nat), sublist sl1 l1 = true /\ sublist sl2 l2 = true /\ sl1 ++ sl2 = sl) \/ sublist sl l2 = true.
Proof.
  intros l1 l2 sl H.
  induction l1 as [| h t IH].
  - simpl in H. right. right. apply H.
  - simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + apply prefix_of_long_list with (l1 := h :: t) in H. destruct H as [H | H].
      * left. simpl. rewrite H. reflexivity.
      * destruct H as [p' [H1 H2]]. right. left. exists (h :: t). exists p'. split.
        -- simpl. rewrite eqb_refl. assert (prefix t (t ++ []) = true). { apply prefix_identity. }
           rewrite append_identity in H. rewrite H. reflexivity.
        -- split.
           ++ apply prefix_implies_sublist. apply H1.
           ++ apply H2.
    + apply IH in H. destruct H as [H | [H | H]].
      * left. simpl. rewrite H. rewrite orb_comm. reflexivity.
      * destruct H as [sl1 [sl2 H]]. right. left. exists sl1. exists sl2. split.
        -- simpl. destruct H as [H _]. rewrite H. rewrite orb_comm. reflexivity.
        -- destruct H as [_ H]. apply H.
      * right. right. apply H.
Qed.

Lemma length_0_list_empty: forall X (l: list X),
  length l = 0 <-> l = [].
Proof.
  intros X l. split.
  { intros H.
  destruct l as [| h t].
  - reflexivity.
  - simpl in H. discriminate H. }
  { intros H. rewrite H. reflexivity. }
Qed.


Lemma concat_preserves_colliders_2: forall (G: graph) (u m v c: node) (l1 l2: nodes),
  acyclic_path_2 (concat u m v l1 l2) /\ In c (find_colliders_in_path (concat u m v l1 l2) G) /\ In c l1 -> In c (find_colliders_in_path (u, m, l1) G).
Proof.
  intros G u m v c l1 l2. intros [Hcyc [Hcol Hl1]].
  apply colliders_vs_edges_in_path in Hcol. destruct Hcol as [y [z [Hsub Hedge]]].
  apply colliders_vs_edges_in_path. exists y. exists z. 
  assert (~(In c l2)). { admit. (* acyclic, and c is in l1, so cannot also be in l2 *) }
  assert (Hcm: c =? m = false). { admit. (* acyclic, same reasoning *) }
  split.
  - replace (u :: (l1 ++ m :: l2) ++ [v]) with ((u :: l1 ++ [m]) ++ (l2 ++ [v])) in Hsub.
    + apply sublist_of_long_list with (l1 := (u :: l1 ++ [m])) (l2 := l2 ++ [v]) in Hsub.
      destruct Hsub as [Hsub | [Hsub | Hsub]].
      * apply Hsub.
      * destruct Hsub as [sl1 [sl2 Hsub]].
        destruct sl1 as [| h t].
        -- destruct Hsub as [_ [H1 H2]]. simpl in H2. apply sublist_of_long_list in H1.
           destruct H1 as [H1 | [H1 | H1]].
           ++ assert (In c l2).
              { apply sublist_member with (l1 := sl2). split.
                - rewrite H2. simpl. right. left. reflexivity.
                - apply H1. }
              exfalso. apply H. apply H0.
           ++ destruct H1 as [sl1 [sl3 [H11 [H12 H13]]]].
              assert (In c sl1).
              { destruct sl3 as [| h t].
                - rewrite append_identity in H13. rewrite H13 in H11.
                  rewrite H13. rewrite H2. simpl. right. left. reflexivity.
                - simpl in H12. apply split_orb_true in H12. destruct H12 as [H12 | H12].
                  + apply split_and_true in H12. destruct H12 as [H12 H12'].
                    destruct t as [| h' t'].
                    * assert (forall (l t: list nat) (a d: nat), l ++ [a] = t ++ [d] -> l = t).
                      { intros l t a d Ha. generalize dependent t. induction l as [| hl tl IHl].
                        - intros t Ha. simpl in Ha. destruct t as [| ht tt]. reflexivity. simpl in Ha. destruct tt as [| htt ttt]. discriminate Ha. discriminate Ha.
                        - intros t Ha. destruct t as [| ht tt].
                          + simpl in Ha. destruct tl as [| ht1 ht2]. discriminate Ha. discriminate Ha.
                          + specialize IHl with (t := tt). simpl in Ha. inversion Ha. apply IHl in H3. rewrite H3. reflexivity. }
                      specialize H0 with (l := sl1) (t := [y; c]) (a := h) (d := z). rewrite <- H13 in H2. simpl in H0. apply H0 in H2.
                      rewrite H2. simpl. right. left. reflexivity.
                    * simpl in H12'. discriminate H12'.
                  + discriminate H12. }
              assert (In c l2).
              { apply sublist_member with (l1 := sl1). split.
                - apply H0.
                - apply H11. }
              exfalso. apply H. apply H1. 
           ++ rewrite H2 in H1. simpl in H1. rewrite andb_comm in H1. simpl in H1. discriminate H1.
           (* TODO not sure why this is so hard rn, the idea is that because of how sublists work, either c in l1, c = m, or c in l2.
              because of acyclic, c in l1. that should prove the theorem *)
        -- admit.
      * (* contradiction, c is in l2 *) admit.
    + simpl. f_equal. rewrite append_vs_concat. apply rearrange_list_concat_app.
  - apply Hedge.
Admitted.

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

Theorem if_mediator_then_not_confounder: forall (G: graph) (u v x: node),
  contains_cycle G = false -> is_mediator_bool u v x G = true
  -> is_confounder_bool u v x G = false /\ is_collider_bool u v x G = false.
Proof.
  intros G u v x Hcyc Hmed.
  unfold is_mediator_bool in Hmed. apply split_and_true in Hmed. destruct Hmed as [H1 H2].
  split.
  { destruct (is_confounder_bool u v x G) as [|] eqn:Hcon.
  - unfold is_confounder_bool in Hcon. apply split_and_true in Hcon. destruct Hcon as [H3 H4].
    assert (Hpath: is_path_in_graph (u, u, [x]) G = true).
    { destruct G as [V E]. simpl. unfold is_edge in *. rewrite H1. rewrite H3. simpl. reflexivity. }
    apply contains_cycle_false_correct in Hpath.
    + simpl in Hpath. destruct Hpath as [contra _]. unfold not in contra.
      exfalso. apply contra. reflexivity.
    + apply Hcyc.
  - reflexivity. }
  { destruct (is_collider_bool u v x G) as [|] eqn:Hcol.
  - unfold is_collider_bool in Hcol. apply split_and_true in Hcol. destruct Hcol as [H3 H4].
    assert (Hpath: is_path_in_graph (v, v, [x]) G = true).
    { destruct G as [V E]. simpl. unfold is_edge in *. rewrite H2. rewrite H4. simpl. reflexivity. }
    apply contains_cycle_false_correct in Hpath.
    + simpl in Hpath. destruct Hpath as [contra _]. unfold not in contra.
      exfalso. apply contra. reflexivity.
    + apply Hcyc.
  - reflexivity. }
Qed.

Theorem if_mediator_then_not_confounder_path: forall (G: graph) (u: node) (p: path),
  contains_cycle G = false -> In u (find_mediators_in_path p G)
  -> ~(In u (find_confounders_in_path p G)) /\ ~(In u (find_colliders_in_path p G)).
Proof.
Admitted.

Theorem if_confounder_then_not_mediator_path: forall (G: graph) (u: node) (p: path),
  contains_cycle G = false -> In u (find_confounders_in_path p G)
  -> ~(In u (find_mediators_in_path p G)) /\ ~(In u (find_colliders_in_path p G)).
Proof.
Admitted.

Lemma med_con_col_are_nodes_in_graph: forall (G: graph) (u v w: node),
  is_mediator_bool u v w G = true \/ is_confounder_bool u v w G = true \/ is_collider_bool u v w G = true
  -> node_in_graph u G = true /\ node_in_graph w G = true /\ node_in_graph v G = true.
Proof.
  intros G u v w H.
  destruct H as [Hmed | [Hcon | Hcol]].
  - unfold is_mediator_bool in Hmed. destruct G as [V E]. simpl in Hmed.
    apply split_and_true in Hmed. destruct Hmed as [Hum Hmv].
    apply split_and_true in Hum. destruct Hum as [Hum _]. apply split_and_true in Hum.
    simpl. destruct Hum as [Hu Hm]. repeat split.
    + apply Hu.
    + apply Hm.
    + apply split_and_true in Hmv. destruct Hmv as [Hmv _].
      apply split_and_true in Hmv. destruct Hmv as [_ Hv]. apply Hv.
  - unfold is_confounder_bool in Hcon. destruct G as [V E]. simpl in Hcon.
    apply split_and_true in Hcon. destruct Hcon as [Hcu Hcv].
    apply split_and_true in Hcu. destruct Hcu as [Hcu _]. apply split_and_true in Hcu.
    simpl. destruct Hcu as [Hc Hu]. repeat split.
    + apply Hu.
    + apply Hc.
    + apply split_and_true in Hcv. destruct Hcv as [Hcv _].
      apply split_and_true in Hcv. destruct Hcv as [_ Hv]. apply Hv.
  - unfold is_collider_bool in Hcol. destruct G as [V E]. simpl in Hcol.
    apply split_and_true in Hcol. destruct Hcol as [Hcu Hcv].
    apply split_and_true in Hcu. destruct Hcu as [Hcu _]. apply split_and_true in Hcu.
    simpl. destruct Hcu as [Hc Hu]. repeat split.
    + apply Hc.
    + apply Hu.
    + apply split_and_true in Hcv. destruct Hcv as [Hcv _].
      apply split_and_true in Hcv. destruct Hcv as [Hv _]. apply Hv.
Qed.

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


Theorem reverse_d_connected_paths: forall (u v: node) (l: nodes) (G: graph) (Z: nodes),
  d_connected_2 (u, v, l) G Z -> d_connected_2 (v, u, rev l) G Z.
Proof.
  intros u v l G Z H. unfold d_connected_2 in *. repeat split.
  - destruct (overlap Z (find_mediators_in_path (v, u, rev l) G)) as [|] eqn:Hmed.
    + apply overlap_has_member_in_common in Hmed. destruct Hmed as [m [HmZ Hmed]].
      apply mediators_same_in_reverse_path in Hmed. destruct H as [H _]. apply no_overlap_non_member_rev with (x := m) in H.
      * exfalso. apply H. rewrite <- reverse_list_twice in Hmed. apply Hmed.
      * apply HmZ.
    + reflexivity.
  - destruct (overlap Z (find_confounders_in_path (v, u, rev l) G)) as [|] eqn:Hcon.
    + apply overlap_has_member_in_common in Hcon. destruct Hcon as [m [HmZ Hcon]].
      apply confounders_same_in_reverse_path in Hcon. destruct H as [_ [H _]]. apply no_overlap_non_member_rev with (x := m) in H.
      * exfalso. apply H. rewrite <- reverse_list_twice in Hcon. apply Hcon.
      * apply HmZ.
    + reflexivity.
  - unfold all_colliders_have_descendant_conditioned_on in *. apply forallb_true_iff_mem. intros m Hcol.
    apply colliders_same_in_reverse_path in Hcol. rewrite <- reverse_list_twice in Hcol. destruct H as [_ [_ H]]. apply forallb_true_iff_mem with (x := m) in H.
    + apply H.
    + apply Hcol.
Qed.

Lemma d_connected_path_not_d_separated: forall (u v: node) (l: nodes) (G: graph) (Z: nodes),
  d_connected_2 (u, v, l) G Z
  -> is_path_in_graph (u, v, l) G = true /\ acyclic_path_2 (u, v, l)
  -> d_separated_bool u v G Z = true -> False.
Proof.
  intros u v l G Z. intros Hconn [Hpath Hcyc] Hsep.
  assert (Hconn': exists (l: nodes), (acyclic_path_2 (u, v, l)) /\ (is_path_in_graph (u, v, l) G = true)
                                      /\ d_connected_2 (u, v, l) G Z).
  { exists l. split.
    - apply Hcyc.
    - split.
      + apply Hpath.
      + apply Hconn. }
  apply d_separated_vs_connected in Hconn'. rewrite Hconn' in Hsep. discriminate Hsep.
Qed.

Definition generic_graph_and_type_properties_hold (X: Type) (G: graph): Prop :=
  (exists (x y: X), x <> y) /\ G_well_formed G = true /\ contains_cycle G = false.

(* p represents a path backwards. return nodes in path before any node in Z is reached *)
Fixpoint find_unblocked_members_of_nodes (p: nodes) (Z: nodes): nodes :=
  match p with
  | [] => []
  | h :: t => if (member h Z) then [] else h :: (find_unblocked_members_of_nodes t Z)
  end.

Lemma unblocked_member_means_in_path: forall (p: nodes) (Z: nodes) (a: node),
  In a (find_unblocked_members_of_nodes p Z) -> In a p /\ ~(In a Z).
Proof.
Admitted.

(* does NOT include the end node (the node that all other nodes are ancestors of) *)
Fixpoint find_unblocked_ancestors_given_paths (P: paths) (Z: nodes): nodes :=
  match P with
  | [] => []
  | p :: P' => match p with
               | (u, v, l) => add_nodes_no_repeats (find_unblocked_members_of_nodes ((rev l) ++ [u]) Z) (find_unblocked_ancestors_given_paths P' Z)
               end
  end.

Lemma in_unblocked_ancestors_of_some_path: forall (P: paths) (Z: nodes) (a: node),
  In a (find_unblocked_ancestors_given_paths P Z) -> exists (p: path), In p P /\ In a (find_unblocked_members_of_nodes ((rev (path_int p)) ++ [path_start p]) Z).
Proof.
Admitted.

(* return all ancestors of u with an unblocked directed path to u TODO prove this is correct *)
Definition find_unblocked_ancestors (G: graph) (v: node) (Z: nodes): nodes :=
  v :: (find_unblocked_ancestors_given_paths (find_directed_paths_to_end v G) Z).


Lemma acyclic_path_equate_sublists: forall (l1 l2 l3 l4: nodes) (m: node),
  acyclic_path (l1 ++ [m] ++ l2) = true /\ l1 ++ [m] ++ l2 = l3 ++ [m] ++ l4 -> l1 = l3 /\ l2 = l4.
Proof.
  intros l1 l2 l3 l4 m [Hcyc Hl].
  generalize dependent l3. induction l1 as [| h t IH].
  - intros l3 Hl. simpl in Hl. destruct l3 as [| h3 t3].
    + simpl in Hl. inversion Hl. split. reflexivity. reflexivity.
    + simpl in Hl. inversion Hl. rewrite <- H0 in H1. rewrite H1 in Hcyc. simpl in Hcyc.
      apply split_and_true in Hcyc. destruct Hcyc as [Hcyc _]. destruct (member m (t3 ++ m :: l4)) as [|] eqn:F.
      * simpl in Hcyc. discriminate Hcyc.
      * assert (In m (t3 ++ (m :: l4))). { apply membership_append_r. left. reflexivity. }
        apply member_In_equiv in H. rewrite H in F. discriminate F.
  - intros l3 Hl. simpl in Hl. destruct l3 as [| h3 t3].
    + simpl in Hl. inversion Hl. rewrite H0 in Hcyc. simpl in Hcyc.
      apply split_and_true in Hcyc. destruct Hcyc as [Hcyc _]. destruct (member m (t ++ m :: l2)) as [|] eqn:F.
      * simpl in Hcyc. discriminate Hcyc.
      * assert (In m (t ++ (m :: l2))). { apply membership_append_r. left. reflexivity. }
        apply member_In_equiv in H. rewrite H in F. discriminate F.
    + inversion Hl. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [_ Hcyc].
      specialize IH with (l3 := t3). simpl in IH. apply IH in Hcyc.
      * split.
        -- f_equal. destruct Hcyc as [Hcyc _]. apply Hcyc.
        -- destruct Hcyc as [_ Hcyc]. apply Hcyc.
      * apply H1.
Qed.

Theorem concat_d_connected_paths: forall (u v mid: node) (l1 l2: nodes) (G: graph) (Z: nodes),
  contains_cycle G = false -> is_path_in_graph (concat u mid v l1 l2) G = true
  -> d_connected_2 (u, mid, l1) G Z /\ d_connected_2 (mid, v, l2) G Z /\ acyclic_path_2 (concat u mid v l1 l2)
  -> (In mid (find_mediators_in_path (concat u mid v l1 l2) G) /\ ~ In mid Z)
     \/ (In mid (find_confounders_in_path (concat u mid v l1 l2) G) /\ ~ In mid Z)
     \/ (In mid (find_colliders_in_path (concat u mid v l1 l2) G) /\ (some_descendant_in_Z_bool (find_descendants mid G) Z = true))
  -> d_connected_2 (concat u mid v l1 l2) G Z.
Proof.
  intros u v mid l1 l2 G Z. intros HGcyc Hpath [H1 [H2 Hcyc]]. intros H.
  unfold d_connected_2 in *. repeat split.
  + destruct (overlap Z (find_mediators_in_path (concat u mid v l1 l2) G)) as [|] eqn:Hmeds.
    * apply overlap_has_member_in_common in Hmeds. destruct Hmeds as [m [HmZ Hmedm]].
      assert (Hmem: In m (l1 ++ mid :: l2)). { apply intermediate_node_in_path with (x := m) in Hpath. apply Hpath. left. apply Hmedm. }
      apply membership_append_or in Hmem. destruct Hmem as [Hm1 | Hm2].
      -- (* m must be a mediator of l1 *)
         assert (Hmedm1: In m (find_mediators_in_path (u, mid, l1) G)).
         { apply mediators_vs_edges_in_path in Hmedm. destruct Hmedm as [y [z [Hsub Hedge]]].
           apply sublist_breaks_down_list in Hsub.
           apply mediators_vs_edges_in_path. exists y. exists z. split.
           - apply membership_splits_list in Hm1. destruct Hm1 as [l1s [l1e Hl1]].
             destruct Hsub as [ps [pe Hp]]. simpl in Hp. pose proof Hp as Hp'. rewrite <- Hl1 in Hp. simpl in Hp.
             assert (Hvar: (ps ++ [y]) ++ [m] ++ z :: pe = (u :: l1s) ++ [m] ++ l1e ++ mid :: l2 ++ [v]).
             { simpl. rewrite <- app_assoc. simpl. unfold node. rewrite Hp. f_equal. simpl. rewrite <- app_assoc. simpl.
               rewrite <- app_assoc. simpl. reflexivity. }
             assert (Hvar': (u :: l1s) ++ [m] ++ l1e ++ mid :: l2 ++ [v] = u :: (l1 ++ mid :: l2) ++ [v]).
             { rewrite <- Hl1. simpl. f_equal. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
             assert (Hsubl: ps ++ [y] = u :: l1s /\ z :: pe = l1e ++ mid :: l2 ++ [v]).
             { apply acyclic_path_equate_sublists with (m := m). split.
               - unfold node in *. rewrite Hvar. rewrite Hvar'. unfold concat in Hcyc. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply Hcyc.
               - apply Hvar. }
             destruct Hsubl as [Hps Hpe]. 
             apply sublist_breaks_down_list. exists ps.
             destruct l1e as [| h1 t1].
             + simpl in Hpe. exists []. simpl. inversion Hpe. rewrite <- Hl1. simpl. rewrite <- app_assoc.
               unfold node in *. rewrite <- append_vs_concat. rewrite Hps. simpl. reflexivity.
             + inversion Hpe. exists (t1 ++ [mid]). simpl. rewrite <- Hl1. simpl.
               unfold node in *. rewrite <- append_vs_concat. rewrite Hps. simpl. f_equal.
               rewrite <- app_assoc. reflexivity.
           - apply Hedge. }
         destruct H1 as [H1 _]. apply no_overlap_non_member with (x := m) in H1.
         ++ exfalso. apply H1. apply HmZ.
         ++ apply Hmedm1.
      -- simpl in Hm2. destruct Hm2 as [Hmmid | Hm2].
         ++ destruct H as [Hmidmed | [Hmidcon | Hmidcol]].
            ** destruct Hmidmed as [Hmid HmidZ]. exfalso. apply HmidZ. rewrite Hmmid. apply HmZ.
            ** destruct Hmidcon as [Hmid HmidZ]. exfalso. apply HmidZ. rewrite Hmmid. apply HmZ.
            ** destruct Hmidcol as [Hmid HmidZ]. apply if_mediator_then_not_confounder_path in Hmedm.
               --- destruct Hmedm as [_ Hmedm]. exfalso. apply Hmedm. rewrite <- Hmmid. apply Hmid.
               --- apply HGcyc.
         ++ (* m must be a mediator of l2 *)
            assert (Hmedm2: In m (find_mediators_in_path (mid, v, l2) G)).
            { apply mediators_vs_edges_in_path in Hmedm. destruct Hmedm as [y [z [Hsub Hedge]]].
              apply sublist_breaks_down_list in Hsub.
              apply mediators_vs_edges_in_path. exists y. exists z. split.
              - apply membership_splits_list in Hm2. destruct Hm2 as [l2s [l2e Hl2]].
                destruct Hsub as [ps [pe Hp]]. simpl in Hp. pose proof Hp as Hp'. rewrite <- Hl2 in Hp. simpl in Hp.
                 assert (Hvar: (ps ++ [y]) ++ [m] ++ z :: pe = (u :: l1 ++ mid :: l2s) ++ [m] ++ l2e ++ [v]).
                 { simpl. rewrite <- app_assoc. simpl. unfold node. rewrite Hp. f_equal. simpl. rewrite <- app_assoc. simpl.
                    rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
                 assert (Hvar': (u :: l1 ++ mid :: l2s) ++ [m] ++ l2e ++ [v] = u :: (l1 ++ mid :: l2) ++ [v]).
                 { rewrite <- Hl2. simpl. f_equal. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
                assert (Hsubl: ps ++ [y] = u :: l1 ++ mid :: l2s /\ z :: pe = l2e ++ [v]).
                { apply acyclic_path_equate_sublists with (m := m). split.
                  - unfold node in *. rewrite Hvar. rewrite Hvar'. unfold concat in Hcyc. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply Hcyc.
                  - apply Hvar. }
                destruct Hsubl as [Hps Hpe].
                apply sublist_breaks_down_list.
                assert (Hlast: l2s = [] \/ exists (l: list nat), l2s = l ++ [y]).
                { apply last_elts_of_equal_lists_2 with (l1 := ps) (l2 := u :: l1 ++ [mid]). simpl. rewrite <- app_assoc. simpl. apply Hps. }
                destruct Hlast as [Hl2s | Hl2s].
                + exists []. exists pe. simpl. simpl in Hp. simpl in Hl2. rewrite <- Hl2. unfold node in *. rewrite Hpe.
                  rewrite Hl2s in Hps. apply last_elts_of_equal_lists with (l2 := u :: l1) in Hps. rewrite Hps. f_equal. rewrite Hl2s. simpl. reflexivity.
                + destruct Hl2s as [l2s' Hl2s]. exists (mid :: l2s'). exists pe. simpl. rewrite <- Hl2. rewrite Hl2s. unfold node in *. rewrite Hpe.
                  f_equal. simpl. rewrite <- app_assoc. simpl. rewrite append_vs_concat. reflexivity.
              - apply Hedge. }
            destruct H2 as [H2 _]. apply no_overlap_non_member with (x := m) in H2.
            ** exfalso. apply H2. apply HmZ.
            ** apply Hmedm2.
    * reflexivity.
  + destruct (overlap Z (find_confounders_in_path (concat u mid v l1 l2) G)) as [|] eqn:Hcons.
    * apply overlap_has_member_in_common in Hcons. destruct Hcons as [m [HmZ Hconm]].
      assert (Hmem: In m (l1 ++ mid :: l2)). { apply intermediate_node_in_path with (x := m) in Hpath. apply Hpath. right. left. apply Hconm. }
      apply membership_append_or in Hmem. destruct Hmem as [Hm1 | Hm2].
      -- (* m must be a confounder of l1 *)
         assert (Hconm1: In m (find_confounders_in_path (u, mid, l1) G)).
         { apply confounders_vs_edges_in_path in Hconm. destruct Hconm as [y [z [Hsub Hedge]]].
           apply sublist_breaks_down_list in Hsub.
           apply confounders_vs_edges_in_path. exists y. exists z. split.
           - apply membership_splits_list in Hm1. destruct Hm1 as [l1s [l1e Hl1]].
             destruct Hsub as [ps [pe Hp]]. simpl in Hp. pose proof Hp as Hp'. rewrite <- Hl1 in Hp. simpl in Hp.
             assert (Hvar: (ps ++ [y]) ++ [m] ++ z :: pe = (u :: l1s) ++ [m] ++ l1e ++ mid :: l2 ++ [v]).
             { simpl. rewrite <- app_assoc. simpl. unfold node. rewrite Hp. f_equal. simpl. rewrite <- app_assoc. simpl.
               rewrite <- app_assoc. simpl. reflexivity. }
             assert (Hvar': (u :: l1s) ++ [m] ++ l1e ++ mid :: l2 ++ [v] = u :: (l1 ++ mid :: l2) ++ [v]).
             { rewrite <- Hl1. simpl. f_equal. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
             assert (Hsubl: ps ++ [y] = u :: l1s /\ z :: pe = l1e ++ mid :: l2 ++ [v]).
             { apply acyclic_path_equate_sublists with (m := m). split.
               - unfold node in *. rewrite Hvar. rewrite Hvar'. unfold concat in Hcyc. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply Hcyc.
               - apply Hvar. }
             destruct Hsubl as [Hps Hpe]. 
             apply sublist_breaks_down_list. exists ps.
             destruct l1e as [| h1 t1].
             + simpl in Hpe. exists []. simpl. inversion Hpe. rewrite <- Hl1. simpl. rewrite <- app_assoc.
               unfold node in *. rewrite <- append_vs_concat. rewrite Hps. simpl. reflexivity.
             + inversion Hpe. exists (t1 ++ [mid]). simpl. rewrite <- Hl1. simpl.
               unfold node in *. rewrite <- append_vs_concat. rewrite Hps. simpl. f_equal.
               rewrite <- app_assoc. reflexivity.
           - apply Hedge. }
         destruct H1 as [_ [H1 _]]. apply no_overlap_non_member with (x := m) in H1.
         ++ exfalso. apply H1. apply HmZ.
         ++ apply Hconm1.
      -- simpl in Hm2. destruct Hm2 as [Hmmid | Hm2].
         ++ destruct H as [Hmidmed | [Hmidcon | Hmidcol]].
            ** destruct Hmidmed as [Hmid HmidZ]. exfalso. apply HmidZ. rewrite Hmmid. apply HmZ.
            ** destruct Hmidcon as [Hmid HmidZ]. exfalso. apply HmidZ. rewrite Hmmid. apply HmZ.
            ** destruct Hmidcol as [Hmid HmidZ]. apply if_confounder_then_not_mediator_path in Hconm.
               --- destruct Hconm as [_ Hconm]. exfalso. apply Hconm. rewrite <- Hmmid. apply Hmid.
               --- apply HGcyc.
         ++ (* m must be a confounder of l2 *)
            assert (Hconm2: In m (find_confounders_in_path (mid, v, l2) G)).
            { apply confounders_vs_edges_in_path in Hconm. destruct Hconm as [y [z [Hsub Hedge]]].
              apply sublist_breaks_down_list in Hsub.
              apply confounders_vs_edges_in_path. exists y. exists z. split.
              - apply membership_splits_list in Hm2. destruct Hm2 as [l2s [l2e Hl2]].
                destruct Hsub as [ps [pe Hp]]. simpl in Hp. pose proof Hp as Hp'. rewrite <- Hl2 in Hp. simpl in Hp.
                 assert (Hvar: (ps ++ [y]) ++ [m] ++ z :: pe = (u :: l1 ++ mid :: l2s) ++ [m] ++ l2e ++ [v]).
                 { simpl. rewrite <- app_assoc. simpl. unfold node. rewrite Hp. f_equal. simpl. rewrite <- app_assoc. simpl.
                    rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
                 assert (Hvar': (u :: l1 ++ mid :: l2s) ++ [m] ++ l2e ++ [v] = u :: (l1 ++ mid :: l2) ++ [v]).
                 { rewrite <- Hl2. simpl. f_equal. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
                assert (Hsubl: ps ++ [y] = u :: l1 ++ mid :: l2s /\ z :: pe = l2e ++ [v]).
                { apply acyclic_path_equate_sublists with (m := m). split.
                  - unfold node in *. rewrite Hvar. rewrite Hvar'. unfold concat in Hcyc. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply Hcyc.
                  - apply Hvar. }
                destruct Hsubl as [Hps Hpe].
                apply sublist_breaks_down_list.
                assert (Hlast: l2s = [] \/ exists (l: list nat), l2s = l ++ [y]).
                { apply last_elts_of_equal_lists_2 with (l1 := ps) (l2 := u :: l1 ++ [mid]). simpl. rewrite <- app_assoc. simpl. apply Hps. }
                destruct Hlast as [Hl2s | Hl2s].
                + exists []. exists pe. simpl. simpl in Hp. simpl in Hl2. rewrite <- Hl2. unfold node in *. rewrite Hpe.
                  rewrite Hl2s in Hps. apply last_elts_of_equal_lists with (l2 := u :: l1) in Hps. rewrite Hps. f_equal. rewrite Hl2s. simpl. reflexivity.
                + destruct Hl2s as [l2s' Hl2s]. exists (mid :: l2s'). exists pe. simpl. rewrite <- Hl2. rewrite Hl2s. unfold node in *. rewrite Hpe.
                  f_equal. simpl. rewrite <- app_assoc. simpl. rewrite append_vs_concat. reflexivity.
              - apply Hedge. }
            destruct H2 as [_ [H2 _]]. apply no_overlap_non_member with (x := m) in H2.
            ** exfalso. apply H2. apply HmZ.
            ** apply Hconm2.
    * reflexivity.
  + unfold all_colliders_have_descendant_conditioned_on. apply forallb_true_iff_mem. intros m Hcolm.
    assert (Hmem: In m (l1 ++ mid :: l2)). { apply intermediate_node_in_path with (x := m) in Hpath. apply Hpath. right. right. apply Hcolm. }
    apply membership_append_or in Hmem. destruct Hmem as [Hm1 | Hm2].
    * destruct H1 as [_ [_ H1]]. unfold all_colliders_have_descendant_conditioned_on in H1. apply forallb_true with (x := m) in H1.
      - apply H1.
      - apply colliders_vs_edges_in_path in Hcolm. destruct Hcolm as [y [z [Hsub Hedge]]].
        apply sublist_breaks_down_list in Hsub.
        apply colliders_vs_edges_in_path. exists y. exists z. split.
        -- apply membership_splits_list in Hm1. destruct Hm1 as [l1s [l1e Hl1]].
           destruct Hsub as [ps [pe Hp]]. simpl in Hp. pose proof Hp as Hp'. rewrite <- Hl1 in Hp. simpl in Hp.
           assert (Hvar: (ps ++ [y]) ++ [m] ++ z :: pe = (u :: l1s) ++ [m] ++ l1e ++ mid :: l2 ++ [v]).
           { simpl. rewrite <- app_assoc. simpl. unfold node. rewrite Hp. f_equal. simpl. rewrite <- app_assoc. simpl.
             rewrite <- app_assoc. simpl. reflexivity. }
           assert (Hvar': (u :: l1s) ++ [m] ++ l1e ++ mid :: l2 ++ [v] = u :: (l1 ++ mid :: l2) ++ [v]).
           { rewrite <- Hl1. simpl. f_equal. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
           assert (Hsubl: ps ++ [y] = u :: l1s /\ z :: pe = l1e ++ mid :: l2 ++ [v]).
           { apply acyclic_path_equate_sublists with (m := m). split.
             - unfold node in *. rewrite Hvar. rewrite Hvar'. unfold concat in Hcyc. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply Hcyc.
             - apply Hvar. }
           destruct Hsubl as [Hps Hpe]. 
           apply sublist_breaks_down_list. exists ps.
           destruct l1e as [| h1 t1].
           ++ simpl in Hpe. exists []. simpl. inversion Hpe. rewrite <- Hl1. simpl. rewrite <- app_assoc.
              unfold node in *. rewrite <- append_vs_concat. rewrite Hps. simpl. reflexivity.
           ++ inversion Hpe. exists (t1 ++ [mid]). simpl. rewrite <- Hl1. simpl.
              unfold node in *. rewrite <- append_vs_concat. rewrite Hps. simpl. f_equal.
              rewrite <- app_assoc. reflexivity.
         -- apply Hedge.
    * simpl in Hm2. destruct Hm2 as [Hmmid | Hm2].
      - destruct H as [Hmidmed | [Hmidcon | Hmidcol]].
        ** destruct Hmidmed as [Hmid HmidZ]. apply if_mediator_then_not_confounder_path in Hmid.
           --- destruct Hmid as [_ Hmid]. exfalso. apply Hmid. rewrite Hmmid in *. apply Hcolm.
           --- apply HGcyc.
        ** destruct Hmidcon as [Hmid HmidZ]. apply if_confounder_then_not_mediator_path in Hmid.
           --- destruct Hmid as [_ Hmid]. exfalso. apply Hmid. rewrite Hmmid in *. apply Hcolm.
           --- apply HGcyc.
        ** destruct Hmidcol as [Hmid HmidZ]. rewrite <- Hmmid. apply HmidZ.
      - destruct H2 as [_ [_ H2]]. unfold all_colliders_have_descendant_conditioned_on in H2. apply forallb_true with (x := m) in H2.
        { apply H2. }
        { apply colliders_vs_edges_in_path in Hcolm. destruct Hcolm as [y [z [Hsub Hedge]]].
          apply sublist_breaks_down_list in Hsub.
          apply colliders_vs_edges_in_path. exists y. exists z. split.
          - apply membership_splits_list in Hm2. destruct Hm2 as [l2s [l2e Hl2]].
            destruct Hsub as [ps [pe Hp]]. simpl in Hp. pose proof Hp as Hp'. rewrite <- Hl2 in Hp. simpl in Hp.
            assert (Hvar: (ps ++ [y]) ++ [m] ++ z :: pe = (u :: l1 ++ mid :: l2s) ++ [m] ++ l2e ++ [v]).
            { simpl. rewrite <- app_assoc. simpl. unfold node. rewrite Hp. f_equal. simpl. rewrite <- app_assoc. simpl.
              rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
            assert (Hvar': (u :: l1 ++ mid :: l2s) ++ [m] ++ l2e ++ [v] = u :: (l1 ++ mid :: l2) ++ [v]).
            { rewrite <- Hl2. simpl. f_equal. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. }
            assert (Hsubl: ps ++ [y] = u :: l1 ++ mid :: l2s /\ z :: pe = l2e ++ [v]).
            { apply acyclic_path_equate_sublists with (m := m). split.
              - unfold node in *. rewrite Hvar. rewrite Hvar'. unfold concat in Hcyc. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply Hcyc.
              - apply Hvar. }
            destruct Hsubl as [Hps Hpe].
            apply sublist_breaks_down_list.
            assert (Hlast: l2s = [] \/ exists (l: list nat), l2s = l ++ [y]).
            { apply last_elts_of_equal_lists_2 with (l1 := ps) (l2 := u :: l1 ++ [mid]). simpl. rewrite <- app_assoc. simpl. apply Hps. }
            destruct Hlast as [Hl2s | Hl2s].
            + exists []. exists pe. simpl. simpl in Hp. simpl in Hl2. rewrite <- Hl2. unfold node in *. rewrite Hpe.
              rewrite Hl2s in Hps. apply last_elts_of_equal_lists with (l2 := u :: l1) in Hps. rewrite Hps. f_equal. rewrite Hl2s. simpl. reflexivity.
            + destruct Hl2s as [l2s' Hl2s]. exists (mid :: l2s'). exists pe. simpl. rewrite <- Hl2. rewrite Hl2s. unfold node in *. rewrite Hpe.
              f_equal. simpl. rewrite <- app_assoc. simpl. rewrite append_vs_concat. reflexivity.
          - apply Hedge. }
Qed.

Theorem unblocked_ancestors_have_unblocked_directed_path: forall (G: graph) (v a: node) (Z: nodes),
  In a (find_unblocked_ancestors G v Z)
  <-> (a = v) \/ (exists (l: nodes), is_directed_path_in_graph (a, v, l) G = true /\ acyclic_path_2 (a, v, l) /\ forall (w: node), (w = a \/ In w l) -> ~(In w Z)).
Proof.
  (* path can be acyclic because if there is a directed path, can remove cycle *)
  intros G v a Z. split.
  - intros H. unfold find_unblocked_ancestors in H. simpl in H. destruct H as [H | H].
    + left. rewrite H. reflexivity.
    + right. apply in_unblocked_ancestors_of_some_path in H. destruct H as [p [Hp Ha]].
      destruct p as [[u v'] l]. apply unblocked_member_means_in_path in Ha as Ha'. destruct Ha' as [Ha' HaZ]. simpl in Ha'.
      apply membership_append_or in Ha'. destruct Ha' as [Ha' | Ha'].
      * admit.
      * simpl in Ha'. exists l. split.
        -- admit.
        -- split.
           ++ admit.
           ++ intros w Hw HZ. admit. (* show w in find_unblocked...nodes, then use lemma *)
  - intros [H | H].
    + unfold find_unblocked_ancestors. simpl. left. rewrite H. reflexivity.
    + destruct H as [l [Hp Hw]]. admit.
Admitted.

Theorem acyclic_path_if_common_ancestor: forall (u v anc: node) (lv lu: nodes) (Z: nodes) (G: graph) (len: nat),
  u <> v /\ ~(In u (find_unblocked_ancestors G v Z)) /\ ~(In v (find_unblocked_ancestors G u Z))
  -> length lu < len
  -> is_directed_path_in_graph (anc, v, lv) G = true /\ acyclic_path_2 (anc, v, lv) /\ (forall w : node, w = anc \/ In w lv -> ~ In w Z)
  -> is_directed_path_in_graph (anc, u, lu) G = true /\ acyclic_path_2 (anc, u, lu) /\ (forall w : node, w = anc \/ In w lu -> ~ In w Z)
  -> exists (anc': node) (lu' lv': nodes), is_directed_path_in_graph (anc', u, lu') G = true /\ is_directed_path_in_graph (anc', v, lv') G = true
      /\ (forall w : node, w = anc' \/ In w lu' \/ In w lv' -> ~ In w Z) /\ acyclic_path_2 (u, v, (rev lu') ++ (anc' :: lv')).
Proof.
  intros u v anc lv lu Z G len. intros [Huv [HuvZ HvuZ]] Hlen [Hdirv [Hcycv HlvZ]]. intros [Hdiru [Hcycu HluZ]].
  (* u <- ..lu.. <- anc -> ..lv.. -> v *)
  generalize dependent anc. generalize dependent lv. generalize dependent lu. induction len as [| len' IH].
  - intros lu Hlen lv anc Hdirv Hcycv HlvZ Hdiru Hcycu HluZ. lia. (* Hlen *)
  - intros lu Hlen lv anc Hdirv Hcycv HlvZ Hdiru Hcycu HluZ.
    (* u <- ..lu.. <- anc -> ..lv.. -> v *)
    destruct (overlap lu lv) as [|] eqn:Hover.
    { apply overlap_has_member_in_common in Hover. destruct Hover as [x [Hxlu Hxlv]].
      apply membership_splits_list in Hxlu. destruct Hxlu as [lu1 [lu2 Hxlu]].
      apply membership_splits_list in Hxlv. destruct Hxlv as [lv1 [lv2 Hxlv]].
      (* u <- ..lu2.. <- x -> ..lv2.. -> v *)
      specialize IH with (lu := lu2) (lv := lv2) (anc := x). apply IH.
      - apply sublist_length_less with (l1 := (lu1 ++ [x])) (l3 := lu). repeat split.
        + apply Hlen.
        + rewrite <- app_assoc. apply Hxlu.
        + destruct lu1 as [| hlu1 tlu1]. intros F. discriminate F. intros F. discriminate F.
      - apply subpath_still_directed with (w := anc) (l1 := lv1) (l3 := lv). split. apply Hxlv. apply Hdirv.
      - apply subpath_still_acyclic with (w := anc) (l1 := lv1) (l3 := lv). split. apply Hxlv. apply Hcycv.
      - intros w Hw. apply HlvZ. right. destruct Hw as [Hw | Hw].
        + apply membership_splits_list. rewrite Hw. exists lv1. exists lv2. apply Hxlv.
        + apply sublist_member with (l1 := lv2). split. apply Hw. apply sublist_breaks_down_list. exists (lv1 ++ [x]). exists [].
          rewrite append_identity. rewrite <- app_assoc. apply Hxlv.
      - apply subpath_still_directed with (w := anc) (l1 := lu1) (l3 := lu). split. apply Hxlu. apply Hdiru.
      - apply subpath_still_acyclic with (w := anc) (l1 := lu1) (l3 := lu). split. apply Hxlu. apply Hcycu.
      - intros w Hw. apply HluZ. right. destruct Hw as [Hw | Hw].
        + apply membership_splits_list. rewrite Hw. exists lu1. exists lu2. apply Hxlu.
        + apply sublist_member with (l1 := lu2). split. apply Hw. apply sublist_breaks_down_list. exists (lu1 ++ [x]). exists [].
          rewrite append_identity. rewrite <- app_assoc. apply Hxlu. }
    { (* no overlap, so already acyclic - use original paths. *)
      exists anc. exists lu. exists lv. split. apply Hdiru. split. apply Hdirv. split.
      + intros w [Hw | [Hw | Hw]].
        * apply HluZ. left. apply Hw.
        * apply HluZ. right. apply Hw.
        * apply HlvZ. right. apply Hw.
      + apply concat_paths_acyclic. split. apply Huv. split.
        * apply reverse_path_still_acyclic. apply Hcycu.
        * apply Hcycv.
        * split. (* u and v cannot be unblocked ancestors of each other *)
          { intros Hu. apply HuvZ. apply unblocked_ancestors_have_unblocked_directed_path. right.
            pose proof Hu as Hu'. apply membership_splits_list in Hu. destruct Hu as [l1 [l2 Hu]]. exists l2. split.
            ++ apply subpath_still_directed with (w := anc) (l1 := l1) (l3 := lv). split. apply Hu. apply Hdirv.
            ++ split.
               ** apply subpath_still_acyclic with (w := anc) (l1 := l1) (l3 := lv). split. apply Hu. apply Hcycv.
                ** intros w Hw. destruct Hw as [Hw | Hw].
                  --- apply HlvZ. right. rewrite Hw. apply Hu'.
                  --- apply HlvZ. right. apply sublist_member with (l1 := l2). split. apply Hw. apply sublist_breaks_down_list.
                      exists (l1 ++ [u]). exists []. rewrite append_identity. rewrite <- app_assoc. apply Hu. }
          { intros Hv. apply membership_rev in Hv. rewrite <- reverse_list_twice in Hv.
            apply HvuZ. apply unblocked_ancestors_have_unblocked_directed_path. right.
            pose proof Hv as Hv'. apply membership_splits_list in Hv. destruct Hv as [l1 [l2 Hv]]. exists l2. split.
            ++ apply subpath_still_directed with (w := anc) (l1 := l1) (l3 := lu). split. apply Hv. apply Hdiru.
            ++ split.
               ** apply subpath_still_acyclic with (w := anc) (l1 := l1) (l3 := lu). split. apply Hv. apply Hcycu.
               ** intros w Hw. destruct Hw as [Hw | Hw].
                  --- apply HluZ. right. rewrite Hw. apply Hv'.
                  --- apply HluZ. right. apply sublist_member with (l1 := l2). split. apply Hw. apply sublist_breaks_down_list.
                      exists (l1 ++ [v]). exists []. rewrite append_identity. rewrite <- app_assoc. apply Hv. }
        * destruct (overlap (rev lu) lv) as [|] eqn:Hover'.
          -- apply overlap_has_member_in_common in Hover'. destruct Hover' as [x [Hx1 Hx2]].
             apply no_overlap_non_member_rev with (x := x) in Hover.
             ++ exfalso. apply Hover. apply Hx2.
             ++ apply membership_rev. apply Hx1.
          -- reflexivity. }
Qed.


Definition G_anc: graph := ([1; 2; 3; 4; 5; 6], [(2, 1); (2, 3); (4, 1); (6, 4); (5, 6); (5, 3)]).

Example unblocked_ancestors_1: find_unblocked_ancestors G_anc 1 [2;4] = [1].
Proof. reflexivity. Qed.

(* U and U' assign the same nodes, and only the assignments for nodes in S can change *)
Definition assignments_change_only_for_subset {X: Type} (U U': assignments X) (S: nodes): Prop :=
  forall (x: node), (is_assigned U x = true <-> is_assigned U' x = true)
  /\ (~(In x S) -> get_assigned_value U x = get_assigned_value U' x).

Class EqType (X : Type) := {
  eqb : X -> X -> bool;
  eqb_refl' : forall x, eqb x x = true;
  eqb_sym' : forall x y, eqb x y = eqb y x;
  eqb_eq' : forall x y, eqb x y = true <-> x = y
}.

(* find all unblocked ancestors of nodes in Z that are not properly conditioned in A' *)
Fixpoint find_unblocked_ancestors_in_Z {X: Type} `{EqType X} (G: graph) (Z: nodes) (AZ A': assignments X): nodes :=
  match AZ with
  | [] => []
  | (u, x) :: AZ' => match (get_assigned_value A' u) with
                     | Some y => if (eqb x y) then find_unblocked_ancestors_in_Z G Z AZ' A'
                                             else (find_unblocked_ancestors G u Z) ++ (find_unblocked_ancestors_in_Z G Z AZ' A')
                     | None => find_unblocked_ancestors_in_Z G Z AZ' A'
                     end
  end.

Definition each_node_assigned_once {X: Type} (A: assignments X): Prop :=
  forall (u: node), is_assigned A u = true -> length (filter (fun (x: node * X) => (fst x) =? u) A) = 1.

Definition each_node_appears_once (Z: nodes): Prop :=
  forall (u: node), In u Z -> count u Z = 1.

Lemma first_node_appears_once: forall (Z: nodes) (u v: node),
  each_node_appears_once (u :: Z) /\ In v Z -> (u =? v) = false.
Proof.
  intros Z u v [Hu Hv].
  unfold each_node_appears_once in Hu.
  destruct (u =? v) as [|] eqn:Huv.
  - specialize Hu with (u := v). simpl in Hu. rewrite Huv in Hu.
    assert (S (count v Z) = 1). { apply Hu. right. apply Hv. } inversion H. clear H.
    apply member_count_at_least_1 in Hv. rewrite H1 in Hv. lia.
  - reflexivity.
Qed.

Lemma exact_assignment_assigns_once {X: Type}: forall (Z: nodes) (x: X),
  each_node_appears_once Z -> each_node_assigned_once (get_assignment_for Z x).
Proof.
  intros Z x HZ.
  induction Z as [| h t IH].
  - simpl. unfold each_node_assigned_once. intros u F. simpl in F. discriminate F.
  - unfold each_node_assigned_once. intros u Hu. simpl.
    destruct (h =? u) as [|] eqn:Hhu.
    + unfold each_node_appears_once in HZ. specialize HZ with (u := h). simpl in HZ. rewrite eqb_refl in HZ.
      assert (S (count h t) = 1). { apply HZ. left. reflexivity. } inversion H.
      simpl. f_equal. rewrite H1.
      destruct (member h t) as [|] eqn:Hmem.
      * apply member_In_equiv in Hmem. apply member_count_at_least_1 in Hmem. rewrite H1 in Hmem. lia.
      * rewrite length_0_list_empty.
        assert (Hmem': ~(In h t)). { intros Hmem'. apply member_In_equiv in Hmem'. rewrite Hmem in Hmem'. discriminate Hmem'. }
        apply node_maps_to_unassigned with (X := X) (a := x) in Hmem'.
        destruct (filter (fun x0 : node * X => fst x0 =? u) (get_assignment_for t x)) as [| [h' x'] t'] eqn:Hfil.
        -- reflexivity.
        -- assert (Hh: is_assigned (get_assignment_for t x) h = true).
           { apply is_assigned_membership. exists x'.
             assert (In (h', x') (filter (fun x0 : node * X => fst x0 =? u) (get_assignment_for t x))). { rewrite Hfil. left. reflexivity. }
             apply filter_In in H0. destruct H0 as [H0 H2]. simpl in H2. apply eqb_eq in H2. apply eqb_eq in Hhu. rewrite <- Hhu in H2.
             rewrite H2 in H0. apply H0. }
           rewrite Hh in Hmem'. discriminate Hmem'.
    + pose proof HZ as HZ'. unfold each_node_appears_once in HZ. specialize HZ with (u := u). simpl in HZ. rewrite Hhu in HZ.
      apply IH.
      * unfold each_node_appears_once. intros v Hv. assert (h =? v = false). { apply first_node_appears_once with (Z := t). split. apply HZ'. apply Hv. }
        unfold each_node_appears_once in HZ'. specialize HZ' with (u := v). simpl in HZ'. rewrite H in HZ'. apply HZ'. right. apply Hv.
      * simpl in Hu. rewrite eqb_sym in Hu. rewrite Hhu in Hu. simpl in Hu. apply Hu.
Qed.

Theorem unblocked_ancestor_of_node_in_Z {X: Type} `{EqType X}: forall (G: graph) (Z: nodes) (AZ Ab Ub: assignments X) (anc: node) (g: graphfun),
  In anc (find_unblocked_ancestors_in_Z G Z AZ Ab) /\ get_values G g Ub [] = Some Ab /\ each_node_assigned_once AZ
  -> exists (z: node), In anc (find_unblocked_ancestors G z Z) /\ is_assigned AZ z = true
                       /\ find_value G g z Ub [] <> get_assigned_value AZ z.
Proof.
  intros G Z AZ Ab Ub anc g. intros [Hanc [HAb HAZ]].
  induction AZ as [| [z1 x1] t IH].
  - simpl in Hanc. exfalso. apply Hanc.
  - simpl in Hanc.
    assert (forall (z: node), (z1 =? z) = true -> is_assigned t z = false).
    { intros z Hz1z.
      unfold each_node_assigned_once in HAZ. specialize HAZ with (u := z1). simpl in HAZ. rewrite eqb_refl in HAZ. simpl in HAZ.
      assert (S (length (filter (fun x : node * X => fst x =? z1) t)) = 1). { apply HAZ. reflexivity. }
      inversion H0. (* contradiction, H2 -> z1 is not assigned in t, contradicts Ht. might not need HZ. *)
      assert ((filter (fun x : node * X => fst x =? z1) t) = []). { apply length_0_list_empty. apply H2. }
      destruct (is_assigned t z) as [|] eqn:Ha.
      - assert (exists (x: X), In (z, x) t). { apply is_assigned_membership. apply Ha. }
        destruct H3 as [x Hx].
        assert (In (z, x) (filter (fun x : node * X => fst x =? z1) t)).
        { apply filter_In. split. 
          - apply Hx.
          - simpl. rewrite eqb_sym. apply Hz1z. }
        rewrite H1 in H3. exfalso. apply H3.
      - reflexivity. }

    destruct (get_assigned_value Ab z1) as [y|] eqn:HAbz1.
    + destruct (eqb x1 y) as [|] eqn:Hx1y.
      * apply IH in Hanc. destruct Hanc as [z [Hancz [Ht Hz]]]. exists z. repeat split.
        -- apply Hancz.
        -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
        -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
           ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
           ++ apply Hz.
        -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
           destruct (z1 =? u) as [|] eqn:Huz1.
           ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
           ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity.
      * apply membership_append_or with (l1 := z1 :: find_unblocked_ancestors_given_paths (find_directed_paths_to_end z1 G) Z) in Hanc.
        destruct Hanc as [Hanc | Hanc].
        { exists z1. repeat split.
        -- apply Hanc.
        -- simpl. rewrite eqb_refl. reflexivity.
        -- simpl. rewrite eqb_refl. unfold find_value. rewrite HAb. rewrite HAbz1. intros Hx1y'. inversion Hx1y'. rewrite H2 in Hx1y. rewrite eqb_refl' in Hx1y. discriminate Hx1y. }
        { apply IH in Hanc. destruct Hanc as [z [Hancz [Ht Hz]]]. exists z. repeat split.
        -- apply Hancz.
        -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
        -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
           ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
           ++ apply Hz.
        -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
           destruct (z1 =? u) as [|] eqn:Huz1.
           ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
           ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity. }
    + apply IH in Hanc. destruct Hanc as [z [Hancz [Ht Hz]]]. exists z. repeat split.
        -- apply Hancz.
        -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
        -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
           ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
           ++ apply Hz.
        -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
           destruct (z1 =? u) as [|] eqn:Huz1.
           ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
           ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity.
Qed.

(* assumes A corresponds to get_values with U *)
Definition unobs_valid_given_u {X: Type} (G: graph) (U A: assignments X) (u: node) (a: X): Prop :=
  is_assignment_for U (nodes_in_graph G) = true /\ get_assigned_value A u = Some a.

Definition unobs_conditions_on_Z {X: Type} (G: graph) (g: graphfun) (U AZ: assignments X) (Z: nodes): Prop :=
  forall (w: node), In w Z -> find_value G g w U [] = get_assigned_value AZ w.

Definition conditionally_independent (X: Type) `{EqType X} (G: graph) (u v: node) (Z: nodes): Prop :=
  forall (AZ: assignments X), is_exact_assignment_for AZ Z /\ each_node_assigned_once AZ
  (* properly conditioned, consistent assignments where f(u)=a *)
  -> forall (g: graphfun) (a: X) (Ua Aa: assignments X),
      get_values G g Ua [] = Some Aa /\ unobs_valid_given_u G Ua Aa u a /\ unobs_conditions_on_Z G g Ua AZ Z
  (* assignments after setting f(u)=b and propagating *)
  -> forall (b: X) (Ub Ab: assignments X),
      (assignments_change_only_for_subset Ua Ub (find_unblocked_ancestors G u Z))
      /\ get_values G g Ub [] = Some Ab /\ (unobs_valid_given_u G Ub Ab u b)
  (* assignments after resetting changed conditioned variables and propagating *)
  -> forall (Ub' Ab': assignments X),
      (assignments_change_only_for_subset Ub Ub' (find_unblocked_ancestors_in_Z G Z AZ Ab))
      /\ get_values G g Ub' [] = Some Ab' /\ (unobs_valid_given_u G Ub' Ab' u b) /\ (unobs_conditions_on_Z G g Ub' AZ Z)
  (* value of v must stay constant *)
  -> get_assigned_value Aa v = get_assigned_value Ab' v.

(* return value of i-th parent, where val is (unobs, pa) *)
Definition f_parent_i (X: Type) (i: nat) (val: X * (list X)): X :=
  nth_default (fst val) (snd val) i.

Lemma find_value_child_equals_parent {X: Type}: forall (G: graph) (g: graphfun) (u v: node) (U: assignments X) (i: nat),
  (G_well_formed G = true /\ contains_cycle G = false) /\ is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph v G = true /\ node_in_graph u G = true
  -> index (find_parents v G) u = Some i /\ g v = f_parent_i X i
  -> find_value G g v U [] = find_value G g u U [].
Proof.
  intros G g u v U i [HG [HU [Hv Hu]]] [Hi Hg].
  assert (Hgv: exists (P: assignments X), find_values G g (find_parents v G) U [] = Some P
                  /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents v G)
                  /\ exists (unobs: X), get_assigned_value U v = Some unobs
                  /\ find_value G g v U [] = Some (g v (unobs, pa))).
  { apply find_value_evaluates_to_g. split.
    - apply HG.
    - split.
      + apply HU.
      + apply Hv. }
  destruct Hgv as [Pv [HPv [PAv [HPAv [unobsv [HUv Hgv]]]]]].
  assert (Hgu: exists x: X, find_value G g u U [] = Some x /\ nth_error Pv i = Some (u, x)).
  { apply find_values_preserves_index with (P := find_parents v G).
    - apply HG.
    - split.
      + apply HU.
      + apply Hu.
    - intros u' Hfp. apply edge_from_parent_to_child in Hfp.
      assert (Huv': node_in_graph u' G = true /\ node_in_graph v G = true).
      { apply edge_corresponds_to_nodes_in_well_formed. split. apply HG. apply Hfp. }
      destruct Huv' as [Huv' _]. apply Huv'.
    - split. apply HPv. apply Hi. }
  destruct Hgu as [x [Hgu Hi']].
  assert (Hvx: g v (unobsv, PAv) = x).
  { rewrite Hg. unfold f_parent_i. simpl.
    assert (Hn: nth_error PAv i = Some x).
    { apply parent_assignments_preserves_index with (P := Pv) (V := find_parents v G) (m := u).
      repeat split.
      - symmetry. apply HPAv.
      - apply Hi.
      - apply find_values_get_assigned with (G := G) (g := g) (P := find_parents v G) (U := U) (A := []). repeat split.
        + apply HPv.
        + apply index_exists. exists i. symmetry. apply Hi.
        + apply Hgu. }
    unfold nth_default. rewrite Hn. reflexivity. }
  rewrite Hgu. rewrite <- Hvx. apply Hgv.
Qed.


(* return x if values of i-th and j-th parents are equal, else y, where val is (unobs, pa) *)
Definition f_equate_ij (X: Type) `{EqType X} (i j: nat) (x y: X) (val: X * (list X)): X :=
  if (eqb (nth_default (fst val) (snd val) i) (nth_default (fst val) (snd val) j)) then x else y.

Definition f_constant (X: Type) (res: X) (val: X * (list X)): X := res.

Definition get_constant_nodefun_assignments {X: Type} (AZ: assignments X): assignments (nodefun X) :=
  map (fun (x: (node * X)) => (fst x, f_constant X (snd x))) AZ.

Lemma assigned_node_has_constant_nodefun {X: Type}: forall (AZ: assignments X) (z: node) (x: X),
  get_assigned_value AZ z = Some x -> get_assigned_value (get_constant_nodefun_assignments AZ) z = Some (f_constant X x).
Proof.
  intros AZ z x H.
  induction AZ as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. destruct (fst h =? z) as [|] eqn:Hhz.
    + simpl. rewrite Hhz. inversion H. reflexivity.
    + simpl. rewrite Hhz. apply IH. apply H.
Qed.

Definition g_path (X: Type) `{EqType X} (A1: assignments nat) (A2: assignments (nat * nat * X * X)) (A3: assignments (nodefun X)) (def: nodefun X) (u: node): nodefun X :=
  match (get_assigned_value A1 u) with
  | Some i => f_parent_i X i
  | None => match (get_assigned_value A2 u) with
            | Some (i, j, x, y) => f_equate_ij X i j x y
            | None => match (get_assigned_value A3 u) with
                      | Some f => f
                      | None => def
                      end
            end
  end.

(* mediators, u if u is a child, and v if v is a child *)
Definition get_A1_binded_nodes_in_g_path (G: graph) (p: path): nodes :=
  match p with
  | (u, v, l) =>
    match path_out_of_end p G with
    | Some b => if b then (if path_into_start p G then u :: (find_mediators_in_path p G) else find_mediators_in_path p G)
                     else (if path_into_start p G then u :: (find_mediators_in_path p G) ++ [v] else (find_mediators_in_path p G) ++ [v])
    | None => [] (* since p has at least two nodes, will not reach this *)
    end
  end.

Lemma path_out_of_end_same: forall (G: graph) (u h v: node) (t: nodes),
  path_out_of_end (u, v, h :: t) G = path_out_of_end (h, v, t) G.
Proof.
  intros G u h v t.
  destruct t as [| h' t'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Definition path_out_of_h (G: graph) (u v h: node) (t: nodes): bool :=
  match t with
  | [] => is_edge (h, v) G
  | h' :: t' => is_edge (h, h') G
  end.

Lemma path_out_of_h_same: forall (G: graph) (u h v: node) (t: nodes),
  path_out_of_h G u v h t = path_out_of_start (h, v, t) G.
Proof.
  intros G u h v t.
  destruct t as [| h' t'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma path_out_of_end_Some: forall (G: graph) (l: nodes) (u v: node),
  path_out_of_end (u, v, l) G = None -> False.
Proof.
  intros G l. induction l as [| h t IH].
  - intros u v. simpl. intros F. discriminate F.
  - intros u v. simpl. destruct t as [| h' t'].
    + simpl. intros F. discriminate F.
    + specialize IH with (u := h) (v := v). apply IH.
Qed.

Lemma is_path_in_graph_induction: forall (G: graph) (u h v: node) (t: nodes),
  is_path_in_graph (u, v, h :: t) G = true -> is_path_in_graph (h, v, t) G = true.
Proof.
  intros G u h v t Hp.
  simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. apply Hp.
Qed.

Lemma A1_induction_case: forall (G: graph) (u h v: node) (t: nodes),
  is_path_in_graph (u, v, h :: t) G = true /\ contains_cycle G = false
  -> path_into_start (u, v, h :: t) G = true /\ path_out_of_h G u v h t = true -> get_A1_binded_nodes_in_g_path G (u, v, h :: t) = u :: (get_A1_binded_nodes_in_g_path G (h, v, t)).
Proof.
  intros G u h v t [Hp Hcyc] [Hin Houth].
  unfold get_A1_binded_nodes_in_g_path.
  destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction in Houth.
    + rewrite Houth. f_equal. simpl. destruct t as [| h' t'].
      * simpl. assert (Hmed: is_mediator_bool u v h G = false).
        { unfold is_mediator_bool. simpl in Hin. apply acyclic_no_two_cycle in Hin.
          - rewrite Hin. reflexivity.
          - apply Hcyc. }
        rewrite Hmed. reflexivity.
      * assert (Hmed: is_mediator_bool u h' h G = false).
        { unfold is_mediator_bool. simpl in Hin. apply acyclic_no_two_cycle in Hin.
          - rewrite Hin. reflexivity.
          - apply Hcyc. }
        simpl. rewrite Hmed. reflexivity.
    + split.
      * simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. apply Hp.
      * apply Hcyc.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction in Houth.
    + rewrite Houth. f_equal. simpl. destruct t as [| h' t'].
      * simpl. assert (Hmed: is_mediator_bool u v h G = false).
        { unfold is_mediator_bool. simpl in Hin. apply acyclic_no_two_cycle in Hin.
          - rewrite Hin. reflexivity.
          - apply Hcyc. }
        rewrite Hmed. reflexivity.
      * assert (Hmed: is_mediator_bool u h' h G = false).
        { unfold is_mediator_bool. simpl in Hin. apply acyclic_no_two_cycle in Hin.
          - rewrite Hin. reflexivity.
          - apply Hcyc. }
        simpl. rewrite Hmed. reflexivity.
    + split.
      * apply is_path_in_graph_induction with (u := u). apply Hp.
      * apply Hcyc.
  -  apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Definition get_A2_binded_nodes_in_g_path (G: graph) (p: path): nodes :=
  find_colliders_in_path p G. (* TODO and descendants as necessary *)

Lemma A2_induction_case: forall (G: graph) (u h v: node) (t: nodes),
  contains_cycle G = false
  -> path_into_start (u, v, h :: t) G = true -> get_A2_binded_nodes_in_g_path G (u, v, h :: t) = get_A2_binded_nodes_in_g_path G (h, v, t).
Proof.
  intros G u h v t Hcyc Hin.
  unfold get_A2_binded_nodes_in_g_path.
  simpl. destruct (t ++ [v]) as [| h' t'].
  - reflexivity.
  - assert (is_collider_bool u h' h G = false).
    { unfold is_collider_bool. simpl in Hin. apply acyclic_no_two_cycle in Hin.
      - rewrite Hin. simpl. reflexivity.
      - apply Hcyc. }
    rewrite H. reflexivity.
Qed.

Lemma A2_nodes_not_in_A1: forall (G: graph) (u: node) (p: path),
  In u (get_A2_binded_nodes_in_g_path G p) -> ~(In u (get_A1_binded_nodes_in_g_path G p)).
Proof.
  (* when A2 includes descendants, not always true. *)
Admitted.


(* using g_path and specific values for A1, A2, and A3, for a d-connected path betw u and v, provide a graphfun
   that requires all non-collider node values along the path (and importantly, f(v) and f(u)), to be equal *)
Lemma path_d_connected_then_can_equate_values {X : Type} `{EqType X}: forall (G: graph) (u v: node) (p: path),
  generic_graph_and_type_properties_hold X G /\ In p (find_all_paths_from_start_to_end u v G) ->
  forall (Z: nodes), ~(In u Z) -> d_connected_2 p G Z
  -> forall (AZ: assignments X), is_assignment_for AZ Z = true
  -> exists (A1: assignments nat) (A2: assignments (nat * nat * X * X)),
     is_exact_assignment_for A1 (get_A1_binded_nodes_in_g_path G p) /\ is_exact_assignment_for A2 (get_A2_binded_nodes_in_g_path G p)
     /\ forall (A3: assignments (nodefun X)) (default: nodefun X) (U: assignments X),
        is_assignment_for U (nodes_in_graph G) = true ->
        (* the colliders that are given a nodefun, but will still evaluate to conditioned value *)
        (forall (w: node), In w Z /\ is_assigned A2 w = true -> find_value G (g_path X A1 A2 A3 default) w U [] = get_assigned_value AZ w)
        /\ (unobs_conditions_on_Z G (g_path X A1 A2 A3 default) U AZ Z
           -> exists (x: X), forall (w: node), node_in_path w p = true /\ ~(In w (find_colliders_in_path p G))
              -> find_value G (g_path X A1 A2 A3 default) w U [] = Some x).
Proof.
  intros G u v p [HG Hp]. intros Z HuZ Hconn. intros AZ HAZ.
  assert (Hpath: exists (l: nodes), p = (u, v, l)).
  { destruct p as [[u' v'] l]. apply paths_start_to_end_correct in Hp. destruct Hp as [_ [Hp _]].
    apply path_start_end_equal in Hp. destruct Hp as [Huu' Hvv']. exists l. rewrite Huu'. rewrite Hvv'. reflexivity. }
  destruct Hpath as [l Hpath]. rewrite Hpath in *. clear Hpath.
  generalize dependent v. generalize dependent u. induction l as [| h t IH].
  - intros u HuZ v Hp Hconn. destruct (path_out_of_start (u, v, []) G) as [|] eqn:Hout.
    + (* u -> v: A1 = {v: i}, where i is the index of u in pa(v). A2 = {} *)
      assert (Hin: path_into_start (u, v, []) G = false).
      { apply acyclic_path_one_direction in Hout.
        -- apply Hout.
        -- split. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
           unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [_ HG]]. apply HG. }
      assert (Hi: exists i: nat, index (find_parents v G) u = Some i).
      { assert (Hu: In u (find_parents v G)).
        { apply edge_from_parent_to_child. simpl in Hout. destruct G as [V E]. simpl. simpl in Hout. apply split_and_true in Hout.
          destruct Hout as [_ Hout]. apply Hout. }
        apply index_exists in Hu. destruct Hu as [i Hi]. exists i. rewrite Hi. reflexivity. }
      destruct Hi as [i Hi].
      exists [(v, i)]. exists []. repeat split.
      * simpl. simpl in Hin. rewrite Hin. simpl. rewrite eqb_refl. simpl. reflexivity.
      * intros w Hmem. simpl in Hmem. simpl in Hin. rewrite Hin in Hmem. simpl in Hmem.
        simpl. destruct (v =? w) as [|] eqn:Hvw.
        -- discriminate Hmem.
        -- rewrite eqb_sym. rewrite Hvw. reflexivity.
      * intros w Hw. simpl in Hw. destruct Hw as [_ F]. discriminate F.
      * pose proof H0 as HU. clear H0. intros Hcond. remember (g_path X [(v, i)] [] A3 default) as g.
        (* u and v are the only two nodes in the path, and both will have value f(u) *)
        assert (Hgu: exists (x: X), find_value G g u U [] = Some x).
        { apply find_value_existence. 
          - destruct HG as [_ HG]. apply HG.
          - split.
            + apply HU.
            + apply nodes_in_graph_in_V with (p := (u, v, [])). split.
              * unfold node_in_path. simpl. rewrite eqb_refl. simpl. reflexivity.
              * apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp. }
        destruct Hgu as [x Hgu].
        exists x. intros w [Hwuv Hcol].
        unfold node_in_path in Hwuv. apply split_orb_true in Hwuv. destruct Hwuv as [Hwuv | F].
        ** simpl in Hwuv. apply split_orb_true in Hwuv. destruct Hwuv as [Hwu | Hwv].
           +++ apply eqb_eq in Hwu. rewrite Hwu. apply Hgu.
           +++ (* by definition of g_path and i, f(v) = f(u) *)
               apply eqb_eq in Hwv. rewrite Hwv.
               assert (Huv: find_value G g v U [] = find_value G g u U []).
               { apply find_value_child_equals_parent with (i := i). split.
                 - destruct HG as [_ HG]. apply HG.
                 - apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. repeat split.
                   + apply HU.
                   + apply nodes_in_graph_in_V with (p := (u, v, [])). split.
                     * unfold node_in_path. simpl. rewrite eqb_refl. rewrite orb_comm. simpl. rewrite orb_comm. reflexivity.
                     * apply Hp.
                   + apply nodes_in_graph_in_V with (p := (u, v, [])). split.
                     * unfold node_in_path. simpl. rewrite eqb_refl. reflexivity.
                     * apply Hp.
                 - split.
                   + apply Hi.
                   + rewrite Heqg. unfold g_path. simpl. rewrite eqb_refl. reflexivity. }
               rewrite Huv. apply Hgu.
          ** simpl in F. discriminate F.
    + (* u <- v: A1 = {u: i}, where i is the index of v in pa(u). A2 = {} *)
      assert (Hin: path_into_start (u, v, []) G = true).
      { apply acyclic_path_one_direction_2 in Hout.
        -- apply Hout.
        -- split. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
           unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [_ HG]]. apply HG. }
      assert (Hi: exists i: nat, index (find_parents u G) v = Some i).
      { assert (Hu: In v (find_parents u G)).
        { apply edge_from_parent_to_child. simpl in Hout. destruct G as [V E]. simpl. simpl in Hin. apply split_and_true in Hin.
          destruct Hin as [_ Hin]. apply Hin. }
      apply index_exists in Hu. destruct Hu as [i Hi]. exists i. rewrite Hi. reflexivity. }
      destruct Hi as [i Hi].
      exists [(u, i)]. exists []. repeat split.
      * simpl. simpl in Hin. rewrite Hin. simpl. rewrite eqb_refl. simpl. reflexivity.
      * intros w Hmem. simpl in Hmem. simpl in Hin. rewrite Hin in Hmem. simpl in Hmem.
        simpl. destruct (u =? w) as [|] eqn:Huw.
        -- discriminate Hmem.
        -- rewrite eqb_sym. rewrite Huw. reflexivity.
      * intros w Hw. simpl in Hw. destruct Hw as [_ F]. discriminate F.
      * pose proof H0 as HU. clear H0. intros Hcond. remember (g_path X [(u, i)] [] A3 default) as g.
        assert (Hgv: exists (x: X), find_value G g v U []  = Some x).
        { apply find_value_existence. 
          - destruct HG as [_ HG]. apply HG.
          - split.
            + apply HU.
            + apply nodes_in_graph_in_V with (p := (u, v, [])). split.
              * unfold node_in_path. simpl. rewrite eqb_refl. rewrite orb_comm. simpl. rewrite orb_comm. reflexivity.
              * apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp. }
        destruct Hgv as [x Hgv].
        exists x. intros w [Hwuv Hcol].
        unfold node_in_path in Hwuv. apply split_orb_true in Hwuv. destruct Hwuv as [Hwuv | F].
        -- simpl in Hwuv. apply split_orb_true in Hwuv. destruct Hwuv as [Hwu | Hwv].
           +++ (* by definition of g_path and i, f(u) = f(v) *)
               assert (Huv: find_value G g u U [] = find_value G g v U []).
               { apply find_value_child_equals_parent with (i := i). split.
                 - destruct HG as [_ HG]. apply HG.
                 - apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. repeat split.
                   + apply HU.
                   + apply nodes_in_graph_in_V with (p := (u, v, [])). split.
                     * unfold node_in_path. simpl. rewrite eqb_refl. reflexivity.
                     * apply Hp.
                   + apply nodes_in_graph_in_V with (p := (u, v, [])). split.
                     * unfold node_in_path. simpl. rewrite eqb_refl. rewrite orb_comm. simpl. rewrite orb_comm. reflexivity.
                     * apply Hp.
                 - split.
                   + apply Hi.
                   + rewrite Heqg. unfold g_path. simpl. rewrite eqb_refl. reflexivity. }
               apply eqb_eq in Hwu. rewrite Hwu. rewrite Huv. apply Hgv.
           +++ apply eqb_eq in Hwv. rewrite Hwv. apply Hgv.
        -- simpl in F. discriminate F.
  - intros u HuZ v Hp Hconn.
    destruct (path_out_of_h G u v h t) as [|] eqn:Houth.
    { (* out of h: u <-> h -> ... v *)
      specialize IH with (u := h) (v := v).
      assert (Hp': In (h, v, t) (find_all_paths_from_start_to_end h v G)).
      { apply paths_start_to_end_correct in Hp. apply paths_start_to_end_correct. admit. }
      apply IH in Hp'. clear IH.
      + destruct Hp' as [A1' [A2' HA12]]. destruct HA12 as [HA1' [HA2' HA12]].
        (* u <-> h <-> ... <-> v *)
        destruct (path_into_start (u, v, h :: t) G) as [|] eqn:Hin.
        * (* u <- h -> ... *)
          assert (Hi: exists i: nat, index (find_parents u G) h = Some i).
          { assert (Hh: In h (find_parents u G)).
            { apply edge_from_parent_to_child. simpl in Hin. destruct G as [V E]. simpl. simpl in Hin. apply split_and_true in Hin.
              destruct Hin as [_ Hin]. apply Hin. }
            apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
          destruct Hi as [i Hi].
          exists ((u, i) :: A1'). exists A2'.
          assert (HA1ind: get_A1_binded_nodes_in_g_path G (u, v, h :: t) = u :: get_A1_binded_nodes_in_g_path G (h, v, t)).
          { apply A1_induction_case.
            - split.
              ** apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
              ** destruct HG as [_ [_ HG]]. apply HG.
            - split.
              ** apply Hin.
              ** apply Houth. }
          assert (HA2ind: get_A2_binded_nodes_in_g_path G (u, v, h :: t) = get_A2_binded_nodes_in_g_path G (h, v, t)).
          { apply A2_induction_case.
            - destruct HG as [_ [_ HG]]. apply HG.
            - apply Hin. }
          repeat split.
          -- (* since arrow into u, u is in A1 *)
             unfold nodes. rewrite HA1ind. simpl. rewrite eqb_refl. simpl. apply is_assignment_for_cat.
             unfold is_exact_assignment_for in HA1'. destruct HA1' as [HA1' _]. apply HA1'.
          -- intros u' Hmemu'. unfold is_exact_assignment_for in HA1'. destruct HA1' as [_ HA1']. simpl.
             assert (Hmemu: In u (get_A1_binded_nodes_in_g_path G (u, v, h :: t))).
             { rewrite HA1ind. left. reflexivity. }
             destruct (u' =? u) as [|] eqn:Huu'.
             ++ apply eqb_eq in Huu'. apply member_In_equiv in Hmemu. rewrite Huu' in Hmemu'. unfold nodes in Hmemu'. rewrite Hmemu in Hmemu'. discriminate Hmemu'.
             ++ simpl. apply HA1'. unfold nodes in Hmemu'. rewrite HA1ind in Hmemu'. unfold member in Hmemu'. rewrite eqb_sym in Hmemu'. rewrite Huu' in Hmemu'. apply Hmemu'.
          -- unfold nodes. rewrite HA2ind. unfold is_exact_assignment_for in HA2'. destruct HA2' as [HA2' _]. apply HA2'.
          -- (* since h is not a collider, nothing changes from induction case *)
             unfold nodes. rewrite HA2ind. unfold is_exact_assignment_for in HA2'. destruct HA2' as [_ HA2']. apply HA2'.
          -- (* only change from induction is u, but since w is in A2', it is not in A1, so w != u *)
             specialize HA12 with (A3 := A3) (default := default) (U := U). pose proof H0 as HU. apply HA12 in H0. destruct H0 as [H0 _].
             intros w Hw. remember (g_path X ((u, i) :: A1') A2' A3 default) as g.
             assert (Hw': exists (P: assignments X), find_values G g (find_parents w G) U [] = Some P
                  /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                  /\ exists (unobs: X), get_assigned_value U w = Some unobs
                  /\ find_value G g w U [] = Some (g w (unobs, pa))).
             { apply find_value_evaluates_to_g. split.
               - destruct HG as [_ HG]. apply HG.
               - split. apply HU.
                 (* w is assigned in A2, so it must be in the graph *)
                 admit. }
             destruct Hw' as [P [HP [pa [Hpar [unobs [HwU Hw']]]]]].
             rewrite Hw'. rewrite Heqg. unfold g_path.
             assert (HA1w: get_assigned_value ((u, i) :: A1') w = None).
             { destruct Hw as [_ Hw]. assert (HA2w: In w (get_A2_binded_nodes_in_g_path G (h, v, t))).
               { apply assigned_true_then_in_list with (A := A2'). split. apply Hw. apply HA2'. }
               simpl. rewrite <- HA2ind in HA2w.
               apply A2_nodes_not_in_A1 in HA2w. rewrite HA1ind in HA2w. destruct (u =? w) as [|] eqn:Huw.
               - exfalso. apply HA2w. left. apply eqb_eq in Huw. apply Huw.
               - destruct HA1' as [_ HA1']. apply assigned_is_false. specialize HA1' with (u := w). apply HA1'.
                 destruct (member w (get_A1_binded_nodes_in_g_path G (h, v, t))) as [|] eqn:Hmem.
                 + exfalso. apply HA2w. right. apply member_In_equiv. apply Hmem.
                 + apply Hmem. }
             rewrite HA1w. specialize H0 with (w := w). apply H0 in Hw as HAZw. clear H0.
             destruct Hw as [_ Hw]. apply assigned_is_true in Hw. destruct Hw as [[[[iw jw] xw] yw] Hvalw]. rewrite Hvalw.
             rewrite <- HAZw. remember (g_path X A1' A2' A3 default) as g'.
             (* show that the induction case evaluates to the same thing *)
             assert (Hw'': exists (P: assignments X), find_values G g' (find_parents w G) U [] = Some P
                  /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                  /\ exists (unobs: X), get_assigned_value U w = Some unobs
                  /\ find_value G g' w U [] = Some (g' w (unobs, pa))).
             { apply find_value_evaluates_to_g. split.
               - destruct HG as [_ HG]. apply HG.
               - split. apply HU.
                 (* w is assigned in A2, so it must be in the graph *)
                 admit. }
             destruct Hw'' as [P' [HP' [pa' [Hpar' [unobs' [HwU' Hw'']]]]]].
             rewrite Hw''. rewrite Heqg'. unfold g_path. simpl in HA1w. destruct (u =? w). discriminate HA1w.
             rewrite HA1w. rewrite Hvalw.
             unfold f_equate_ij. simpl.
             rewrite HwU in HwU'. inversion HwU'.
             admit.
(* - show that for A3 nodes, find_value stays the same (constant)
   - for A1 nodes, also stays the same (each chain of mediators ends at a confounder in A3)
   - for A2 nodes, also stays the same (depends on values of mediators/confounders) *)
          -- intros Hcond. specialize HA12 with (A3 := A3) (default := default) (U := U). apply HA12 in H0. clear HA12. destruct H0 as [_ HA12].
             assert (Hcond': unobs_conditions_on_Z G (g_path X A1' A2' A3 default) U AZ Z).
             { unfold unobs_conditions_on_Z. unfold unobs_conditions_on_Z in Hcond. admit. (* since u not in Z, w != u *) }
             apply HA12 in Hcond'. destruct Hcond' as [x Hcond']. exists x. intros w [Hwp Hwcol].
             specialize Hcond' with (w := w). (* show for all nodes in path != u (same as before), then for u (= f(h)) *)
             admit.
        * (* u -> h *) admit.
      + admit. (* since arrow out of h is ->, h cannot be a collider, so h not in Z *)
      + unfold d_connected_2 in Hconn. unfold d_connected_2. admit. }
    (* into h: u <-> h <- ...v 
       destruct based on u <-> h arrow. if u <- h, then h is a mediator, so h not in Z. same as above case
                                       if u -> h, then h is a collider, have to include h in A2.
                                         destruct t: if [], manually? else, use induction step with path not incl u and h *)
    { (* into h: u <-> h <- ...v *)
      destruct (path_into_start (u, v, h :: t) G) as [|] eqn:Hin.
      - (* u <- h <- ... *)
        specialize IH with (u := h) (v := v).
        assert (Hp': In (h, v, t) (find_all_paths_from_start_to_end h v G)).
        { apply paths_start_to_end_correct in Hp. apply paths_start_to_end_correct. admit. }
        apply IH in Hp'. clear IH.
        + destruct Hp' as [A1' [A2' HA12]]. destruct HA12 as [HA1' [HA2' HA12]].
          assert (Hi: exists i: nat, index (find_parents u G) h = Some i).
          { assert (Hh: In h (find_parents u G)).
            { apply edge_from_parent_to_child. simpl in Hin. destruct G as [V E]. simpl. simpl in Hin. apply split_and_true in Hin.
              destruct Hin as [_ Hin]. apply Hin. }
            apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
          destruct Hi as [i Hi].
          exists ((u, i) :: A1'). exists A2'. repeat split.
          -- admit. (* have to destruct based on next arrow h <->... *)
          -- admit.
          -- admit. (* show that this is the same as without u, since h is not a collider *)
          -- admit.
          -- admit. (* not in A1' and not = u, so same as IH *)
          -- intros Hcond. specialize HA12 with (A3 := A3) (default := default) (U := U).
             assert (Hcond': unobs_conditions_on_Z G (g_path X A1' A2' A3 default) U AZ Z).
             { unfold unobs_conditions_on_Z. unfold unobs_conditions_on_Z in Hcond. admit. (* since u not in Z, w != u *) }
             admit.
        + admit. (* h cannot be a collider, so h not in Z *)
        + unfold d_connected_2 in Hconn. unfold d_connected_2. admit.
      - (* u -> h <- ... h is a collider, have to include h in A2.
                                         destruct t: if [], manually? else, use induction step with path not incl u and h *)
        admit. }
Admitted.

Lemma exists_node_not_defined_in_path {X : Type} `{EqType X}: forall (G: graph) (u v: node) (p: path) (Z: nodes) (A1: assignments nat) (A2: assignments (nat * nat * X * X)),
  generic_graph_and_type_properties_hold X G /\ In p (find_all_paths_from_start_to_end u v G)
  -> d_connected_2 p G Z
  -> (forall (w: node), member w (get_A1_binded_nodes_in_g_path G p) = false -> is_assigned A1 w = false)
     /\ (forall (w: node), member w (get_A2_binded_nodes_in_g_path G p) = false -> is_assigned A2 w = false)
  -> exists (w: node), is_assigned A1 w = false /\ is_assigned A2 w = false /\ ~(In w Z) /\ In w (find_unblocked_ancestors G u Z) /\ node_in_path w p = true.
Proof.
(* if path is out of u (u -> ...), then w = u.
   else, if there is any out arrow, the first out arrow's parent is w (u <- ... <- w -> ...)
   else, the last node is w (u <- ... <- w) *)
  intros G u v p Z A1 A2. intros [HG Hp] Hconn [HA1 HA2].
  destruct p as [[u' v'] l]. apply paths_start_to_end_correct in Hp as Huv. destruct Huv as [_ [Huv _]]. apply path_start_end_equal in Huv.
  destruct Huv as [Hu Hv]. rewrite Hu in *. rewrite Hv in *. clear Hu. clear Hv.
  generalize dependent v. generalize dependent u. induction l as [| h t IH].
  - intros u v HGp Hconn HA1 HA2. destruct (path_out_of_start (u, v, []) G) as [|] eqn:Hout.
    + exists u. repeat split.
      * simpl in Hout. assert (Hedge: is_edge (v, u) G = false).
        { destruct (member_edge (v, u) (edges_in_graph G)) as [|] eqn:He.
          - admit. (* TODO cycle u' -> v' -> u' *)
          - unfold is_edge. destruct G as [V E]. simpl in He. rewrite He. rewrite andb_comm. simpl. reflexivity. }
        simpl in HA1. rewrite Hedge in HA1. specialize HA1 with (w := u). apply HA1. simpl.
        assert (Hvu: v =? u = false). { admit. (* TODO cycl u' -> u' *) } rewrite Hvu. reflexivity.
      * simpl in HA2. specialize HA2 with (w := u). apply HA2. simpl. reflexivity.
      * admit. (* use Hconn / have to assume that endpoints not in Z (shouldn't affect induction) *)
      * simpl in Hout. apply unblocked_ancestors_have_unblocked_directed_path. left. reflexivity.
      * unfold node_in_path. simpl. rewrite eqb_refl. simpl. reflexivity.
    + exists v. admit.
  - (* u -> h ... v, then u. u <- h ... w ... v, then w. *)
    intros u v HGp Hconn HA1 HA2. destruct (path_out_of_start (u, v, h :: t) G) as [|] eqn:Hout.
    + exists u. admit. (* use path_into vs. out_of proof? similar to above. *)
    + specialize IH with (u := h) (v := v).
      assert (exists w : node,
       is_assigned A1 w = false /\
       is_assigned A2 w = false /\
       ~ In w Z /\
       In w (find_unblocked_ancestors G h Z) /\
       node_in_path w (h, v, t) = true).
      { apply IH.
        - admit.
        - admit.
        - intros w Hmem. specialize HA1 with (w := w). admit. (* only difference could be u, but u is not in it, since u -> *)
        - intros w Hmem. specialize HA2 with (w := w). apply HA2. admit. (* can we simplify the assumption? wait don't need because will always be on path and first -> by construction, so not collider *) }
      destruct H0 as [w Hw]. exists w. repeat split.
      * destruct Hw as [Hw _]. apply Hw.
      * destruct Hw as [_ [Hw _]]. apply Hw.
      * destruct Hw as [_ [_ [Hw _]]]. apply Hw.
      * destruct Hw as [_ [_ [_ [Hw _]]]]. apply unblocked_ancestors_have_unblocked_directed_path in Hw.
        destruct Hw as [Hwh | Hhl].
        -- apply unblocked_ancestors_have_unblocked_directed_path. right. exists []. split.
           ++ simpl. (* Hout gives that (h, u) is an edge *) admit.
           ++ split. admit. unfold node_in_path. simpl. admit.
        -- apply unblocked_ancestors_have_unblocked_directed_path. right. destruct Hhl as [l Hhl]. exists (l ++ [h]). split.
           ++ simpl. (* might be annoying *) admit.
           ++ admit.
      * unfold node_in_path. simpl. destruct Hw as [_ [_ [_ [_ Hw]]]]. unfold node_in_path in Hw. simpl in Hw. admit. (* use Hw *)
Admitted.

(* show that using the g from generic_graph_and_type_properties_hold to equate values along the path, the
   conditionally_independent proposition cannot hold *)
Lemma path_d_connected_then_not_independent {X : Type} `{EqType X}: forall (G: graph) (u v: node) (p: path),
  generic_graph_and_type_properties_hold X G /\ In p (find_all_paths_from_start_to_end u v G) ->
  forall (Z: nodes), subset Z (nodes_in_graph G) = true /\ each_node_appears_once Z /\ member u Z = false /\ member v Z = false
  -> d_connected_2 p G Z -> ~(conditionally_independent X G u v Z).
Proof.
  intros G u v p HGp. intros Z [HZ [HZnode [HuZ HvZ]]] Hconn. intros Hcond. unfold conditionally_independent in Hcond.
  pose proof HGp as Hxy. unfold generic_graph_and_type_properties_hold in Hxy. destruct Hxy as [[Hxy _] _]. destruct Hxy as [x [y Hxy]].
  assert (Hpath: exists (l: nodes), p = (u, v, l)).
  { destruct p as [[u' v'] l]. destruct HGp as [_ Hp]. apply paths_start_to_end_correct in Hp. destruct Hp as [_ [Hp _]].
    apply path_start_end_equal in Hp. destruct Hp as [Huu' Hvv']. exists l. rewrite Huu'. rewrite Hvv'. reflexivity. }
  destruct Hpath as [l Hpath].
  remember (get_assignment_for Z x) as AZ. (* use arbitrary assignment of nodes in Z *)
  pose proof path_d_connected_then_can_equate_values as Heq. specialize Heq with (G := G) (u := u) (v := v) (p := p) (Z := Z) (AZ := AZ).
  apply Heq in HGp as HA12. destruct HA12 as [A1 [A2 HA12]]. clear Heq. destruct HA12 as [HA1 [HA2 Hg]].
  - (* show contradiction with Hcond by showing that v's value changes with u's *)
    (* find node w to bind to either a or b (not in A1 or A2 or Z) *)
    assert (Hanc: exists (w: node), is_assigned A1 w = false /\ is_assigned A2 w = false /\ ~(In w Z) /\ In w (find_unblocked_ancestors G u Z) /\ node_in_path w p = true).
    { apply exists_node_not_defined_in_path with (v := v). split.
      - destruct HGp as [HG _]. apply HG.
      - destruct HGp as [_ Hp]. apply Hp.
      - apply Hconn.
      - split. unfold is_exact_assignment_for in *. destruct HA1 as [_ HA1]. apply HA1. destruct HA2 as [_ HA2]. apply HA2. }
    destruct Hanc as [w Hw].
    remember (get_constant_nodefun_assignments AZ) as AZf. remember ((w, fun (x: (X * (list X))) => fst x) :: AZf) as A3.
    specialize Hg with (A3 := A3) (default := f_constant X x).
    remember ((w, x) :: (get_assignment_for (nodes_in_graph G) x)) as Ux. remember ((w, y) :: (get_assignment_for (nodes_in_graph G) x)) as Uy.
    assert (HUxG: is_assignment_for Ux (nodes_in_graph G) = true).
    { rewrite HeqUx. apply is_assignment_for_cat. apply nodes_map_to_assignment. }
    assert (HUyG: is_assignment_for Uy (nodes_in_graph G) = true).
    { rewrite HeqUy. apply is_assignment_for_cat. apply nodes_map_to_assignment. }
    remember (g_path X A1 A2 A3 (f_constant X x)) as g.
    (* show that this choice of g always correctly conditions on Z *)
    assert (HU: forall (U: assignments X), is_assignment_for U (nodes_in_graph G) = true
                -> unobs_conditions_on_Z G g U AZ Z).
    { intros U HU. unfold unobs_conditions_on_Z. intros z HzZ.
      assert (HzG: node_in_graph z G = true).
      { destruct G as [V E]. simpl. apply member_In_equiv. apply subset_larger_set_membership with (l1 := Z).
        split. apply HZ. apply HzZ. }
      (* express f(z) in terms of g *)
      assert (Hz: exists (P: assignments X), find_values G g (find_parents z G) U [] = Some P
                  /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents z G)
                  /\ exists (unobs: X), get_assigned_value U z = Some unobs
                  /\ find_value G g z U [] = Some (g z (unobs, pa))).
      { apply find_value_evaluates_to_g. split.
        - destruct HGp as [HG _]. apply HG.
        - split. apply HU. apply HzG. }
      destruct Hz as [P [HP [pa [Hpar [unobs [HzU Hz]]]]]].
      (* since z is in Z, either z is not in the path or z is a collider *)
      (* first, show z is either in A2 (collider) and evaluates to correct value, or not assigned in A2 *)
      destruct (is_assigned A2 z) as [|] eqn:HzA2.
      - specialize Hg with (U := U). apply Hg in HU as Hg'. clear Hg. pose proof Hg' as Hg.
        destruct Hg as [Hg _]. specialize Hg with (w := z). apply Hg.
        split. apply HzZ. apply HzA2.
      - rewrite Hz. rewrite Heqg. unfold g_path.
        (* show that since z in Z and path is d-connected, z is not assigned in A1 *)
        assert (HzA1: ~(In z (get_A1_binded_nodes_in_g_path G p))).
        { intros HzA1. unfold get_A1_binded_nodes_in_g_path in HzA1.
          destruct (path_out_of_end p G) as [[|]|].
          - destruct (path_into_start p G) as [|].
            + rewrite Hpath in *. simpl in HzA1. destruct HzA1 as [Hzu | Hzmed].
              * (* by assumption (HuZ), u is not in Z *)
                apply member_In_equiv in HzZ. rewrite Hzu in HuZ. rewrite HzZ in HuZ. discriminate HuZ.
              * (* z cannot be a mediator, or else p would not be d-connected *)
                unfold d_connected_2 in Hconn. destruct Hconn as [Hconn _]. apply no_overlap_non_member with (x := z) in Hconn.
                -- exfalso. apply Hconn. apply HzZ.
                -- apply Hzmed.
            + unfold d_connected_2 in Hconn. destruct Hconn as [Hconn _]. apply no_overlap_non_member with (x := z) in Hconn.
                -- exfalso. apply Hconn. apply HzZ.
                -- rewrite Hpath in *. apply HzA1.
          - destruct (path_into_start p G) as [|].
            + rewrite Hpath in *. simpl in HzA1. destruct HzA1 as [Hzu | Hzmedv].
              * apply member_In_equiv in HzZ. rewrite Hzu in HuZ. rewrite HzZ in HuZ. discriminate HuZ.
              * apply membership_append_or in Hzmedv. destruct Hzmedv as [Hzmed | Hzv].
                -- unfold d_connected_2 in Hconn. destruct Hconn as [Hconn _]. apply no_overlap_non_member with (x := z) in Hconn.
                   ++ exfalso. apply Hconn. apply HzZ.
                   ++ apply Hzmed.
                -- simpl in Hzv. destruct Hzv as [Hzv | F].
                   ++ apply member_In_equiv in HzZ. rewrite Hzv in HvZ. rewrite HzZ in HvZ. discriminate HvZ.
                   ++ apply F.
            + rewrite Hpath in *. apply membership_append_or in HzA1. destruct HzA1 as [Hzmed | Hzv].
              * unfold d_connected_2 in Hconn. destruct Hconn as [Hconn _]. apply no_overlap_non_member with (x := z) in Hconn.
                   ++ exfalso. apply Hconn. apply HzZ.
                   ++ apply Hzmed.
              * simpl in Hzv. destruct Hzv as [Hzv | F].
                   ++ apply member_In_equiv in HzZ. rewrite Hzv in HvZ. rewrite HzZ in HvZ. discriminate HvZ.
                   ++ apply F.
          - rewrite Hpath in HzA1. simpl in HzA1. apply HzA1. }
        unfold is_exact_assignment_for in HA1. destruct HA1 as [_ HA1]. specialize HA1 with (u := z).
        assert (HzA1': member z (get_A1_binded_nodes_in_g_path G p) = false).
        { destruct (member z (get_A1_binded_nodes_in_g_path G p)) eqn:Hmem.
          - exfalso. apply HzA1. apply member_In_equiv. apply Hmem.
          - reflexivity. }
        clear HzA1. apply HA1 in HzA1'. apply assigned_is_false in HzA1'. rewrite HzA1'.
        (* z is not assigned in A2 *)
        apply assigned_is_false in HzA2. rewrite HzA2.
        (* z is assigned in A3 to be its value in AZf (since z != w since w not in Z)
           its value in AZf is the function that returns AZ(z) for all inputs *)
        assert (HzAZ: exists (val_z: X), get_assigned_value AZ z = Some val_z).
        { apply assigned_is_true. rewrite HeqAZ. apply node_maps_to_assigned. apply HzZ. }
        destruct HzAZ as [valz HzAZ].
        assert (HzA3: get_assigned_value A3 z = Some (f_constant X valz)).
        { rewrite HeqA3. simpl. destruct (w =? z) as [|] eqn:Hwz.
          - destruct Hw as [_ [_ [Hw _]]]. apply eqb_eq in Hwz. rewrite <- Hwz in HzZ. exfalso. apply Hw. apply HzZ.
          - apply assigned_node_has_constant_nodefun in HzAZ. rewrite HeqAZf. apply HzAZ. }
        unfold nodefun. rewrite HzA3. unfold f_constant. rewrite HzAZ. reflexivity. }
    (* set Ua = Ux, Ub = Uy, and Ub' = Uy in Hcond *)
    assert (HAx: exists (Ax: assignments X), get_values G g Ux [] = Some Ax).
    { apply get_values_existence. destruct HGp as [[_ HG] _]. apply HG. apply HUxG. }
    assert (HAy: exists (Ay: assignments X), get_values G g Uy [] = Some Ay).
    { apply get_values_existence. destruct HGp as [[_ HG] _]. apply HG. apply HUyG. }
    destruct HAx as [Ax HAx]. destruct HAy as [Ay HAy].

    (* show that f(any non-collider node in path) is equal to the binding of w *)
    assert (HwU: forall (U A: assignments X) (c: X),
                 is_assignment_for U (nodes_in_graph G) = true
                 /\ U = (w, c) :: get_assignment_for (nodes_in_graph G) x
                 /\ get_values G g U [] = Some A
                 -> forall w : node, node_in_path w p = true /\ ~ In w (find_colliders_in_path p G) ->
                    find_value G g w U [] = Some c).
    { (* show that f(w) = c (due to binding in U) *)
      intros U A c [HUG [HeqU HA]].
      assert (Hwc: exists (P: assignments X), find_values G g (find_parents w G) U [] = Some P
                  /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                  /\ exists (unobs: X), get_assigned_value U w = Some unobs
                  /\ find_value G g w U [] = Some (g w (unobs, pa))).
      { apply find_value_evaluates_to_g. split.
        - destruct HGp as [HG _]. apply HG.
        - split.
          + apply HUG.
          + apply nodes_in_graph_in_V with (p := p). split.
            * destruct Hw as [_ [_ [_ [_ Hw]]]]. apply Hw.
            * destruct HGp as [_ Hp]. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp. }
      destruct Hwc as [Pwc [HPwc [pawc [Hparwc [unobswc [HwU Hwc]]]]]].
      assert (Hgwc: g w (unobswc, pawc) = c).
      { rewrite Heqg. unfold g_path. destruct Hw as [Hw1 [Hw2 _]]. apply assigned_is_false in Hw1. rewrite Hw1.
        apply assigned_is_false in Hw2. rewrite Hw2. rewrite HeqA3. simpl. rewrite eqb_refl. simpl.
        rewrite HeqU in HwU. simpl in HwU. rewrite eqb_refl in HwU. inversion HwU. reflexivity. }
      (* show that all non-collider nodes equal c (due to Hg and f(w) = c) *)
      specialize Hg with (U := U). apply Hg in HUG as Hg'. clear Hg. pose proof Hg' as Hg. clear Hg'.
      destruct Hg as [_ Hg]. apply HU in HUG as Hnodex. apply Hg in Hnodex. clear Hg.
      destruct Hnodex as [x' Hnodex].
      assert (Hcx': c = x').
      { assert (Hwx': find_value G g w U [] = Some x').
        { apply Hnodex. split.
          - destruct Hw as [_ [_ [_ [_ Hw]]]]. apply Hw.
          - destruct Hw as [_ [Hw _]]. unfold get_A2_binded_nodes_in_g_path in HA2. unfold is_exact_assignment_for in HA2.
            destruct HA2 as [HA2 _]. intros Hmemw.
            assert (F: is_assigned A2 w = true).
            { apply assigned_is_true. apply assigned_has_value with (L := find_colliders_in_path p G). split. apply Hmemw. apply HA2. }
            rewrite Hw in F. discriminate F. }
        rewrite Hgwc in Hwc. rewrite Hwx' in Hwc. inversion Hwc. reflexivity. }
      rewrite <- Hcx' in Hnodex. apply Hnodex. }

    (* show that v is equal to the binding of w *)
    assert (HvU: forall (U A: assignments X) (c: X),
                 is_assignment_for U (nodes_in_graph G) = true
                 /\ U = (w, c) :: get_assignment_for (nodes_in_graph G) x
                 /\ get_values G g U [] = Some A
                 -> get_assigned_value A v = Some c).
    { (* show that f(w) = c (due to binding in U) *)
      intros U A c [HUG [HeqU HA]].
      assert (Hnodex: forall w : node, node_in_path w p = true /\ ~ In w (find_colliders_in_path p G) ->
                    find_value G g w U [] = Some c).
      { apply HwU with (A := A). repeat split. apply HUG. apply HeqU. apply HA. }
      (* show that f(v) = c *)
      specialize Hnodex with (w := v). unfold find_value in Hnodex. rewrite HA in Hnodex.
      apply Hnodex. split.
      - rewrite Hpath. unfold node_in_path. simpl. rewrite eqb_refl. rewrite orb_true_r. reflexivity.
      - intros Hmemx. rewrite Hpath in Hmemx. unfold find_colliders_in_path in Hmemx. apply colliders_vs_edges_in_path in Hmemx.
        destruct Hmemx as [v1 [v2 [Hsub Hedge]]].
        (* v must appear twice in the list, since v1 <-> v <-> v2 appears as a subpath in p *)
        destruct HGp as [_ Hp]. apply paths_start_to_end_correct in Hp. destruct Hp as [_ [_ Hp]].
        apply middle_elt_of_sublist_not_last_elt with (l := u :: l) in Hsub. destruct Hsub as [Hsub | Hsub].
        + (* u cannot equal v, or cyclic *)
          unfold acyclic_path_2 in Hp. rewrite Hpath in Hp. destruct Hp as [Hp _]. apply Hp. apply Hsub.
        + (* v appears in l, also contradicts acyclic *)
          unfold acyclic_path_2 in Hp. rewrite Hpath in Hp. destruct Hp as [_ [_ [Hp _]]]. apply Hp. apply Hsub. }
    (* show that for U = Ux, f(v) = f(w) = x *)
    assert (HvUx: get_assigned_value Ax v = Some x).
    { apply HvU with (U := Ux). repeat split.
      - apply HUxG.
      - apply HeqUx.
      - apply HAx. }
    assert (HvUy: get_assigned_value Ay v = Some y).
    { apply HvU with (U := Uy). repeat split.
      - apply HUyG.
      - apply HeqUy.
      - apply HAy. }

    (* show that u is equal to the binding of w *)
    assert (HuU: forall (U A: assignments X) (c: X),
                 is_assignment_for U (nodes_in_graph G) = true
                 /\ U = (w, c) :: get_assignment_for (nodes_in_graph G) x
                 /\ get_values G g U [] = Some A
                 -> get_assigned_value A u = Some c).
    { (* show that f(w) = c (due to binding in U) *)
      intros U A c [HUG [HeqU HA]].
      assert (Hnodex: forall w : node, node_in_path w p = true /\ ~ In w (find_colliders_in_path p G) ->
                    find_value G g w U [] = Some c).
      { apply HwU with (A := A). repeat split. apply HUG. apply HeqU. apply HA. }
      (* show that f(v) = c *)
      specialize Hnodex with (w := u). unfold find_value in Hnodex. rewrite HA in Hnodex.
      apply Hnodex. split.
      - rewrite Hpath. unfold node_in_path. simpl. rewrite eqb_refl. reflexivity.
      - intros Hmemx. rewrite Hpath in Hmemx. unfold find_colliders_in_path in Hmemx. apply colliders_vs_edges_in_path in Hmemx.
        destruct Hmemx as [v1 [v2 [Hsub Hedge]]].
        (* v must appear twice in the list, since v1 <-> v <-> v2 appears as a subpath in p *)
        destruct HGp as [_ Hp]. apply paths_start_to_end_correct in Hp. destruct Hp as [_ [_ Hp]].
        apply middle_elt_of_sublist_not_first_elt with (l := l ++ [v]) in Hsub. apply membership_append_or in Hsub. destruct Hsub as [Hsub | Hsub].
        + (* u appears in l, contradicts acyclic *)
          unfold acyclic_path_2 in Hp. rewrite Hpath in Hp. destruct Hp as [_ [Hp _]]. apply Hp. apply Hsub.
        + (* u cannot equal v, or cyclic *)
          simpl in Hsub. destruct Hsub as [Hsub | F].
          * unfold acyclic_path_2 in Hp. rewrite Hpath in Hp. destruct Hp as [Hp _]. apply Hp. rewrite Hsub. reflexivity.
          * apply F. }

    (* using the assumption of conditional independence (Hcond), derive contradiction (Ax(v) = Ay(v)) *)
    specialize Hcond with (AZ := AZ) (g := g) (a := x) (Ua := Ux) (Aa := Ax)
                          (b := y) (Ub := Uy) (Ab := Ay) (Ub' := Uy) (Ab' := Ay).
    assert (HvAxAy: get_assigned_value Ax v = get_assigned_value Ay v).
    { apply Hcond.
      - rewrite HeqAZ. split. apply nodes_map_to_exact_assignment. apply exact_assignment_assigns_once. apply HZnode.
      - repeat split.
        + apply HAx.
        + apply HUxG.
        + apply HuU with (U := Ux). repeat split.
          * apply HUxG.
          * apply HeqUx.
          * apply HAx.
        + specialize HU with (U := Ux). apply HU. apply HUxG.
      - repeat split.
        + intros Hx0. rewrite HeqUx in Hx0. simpl in Hx0. rewrite HeqUy. simpl. apply Hx0.
        + intros Hx0. rewrite HeqUy in Hx0. simpl in Hx0. rewrite HeqUx. simpl. apply Hx0.
        + intros Hx0. rewrite HeqUx. rewrite HeqUy. simpl. destruct (w =? x0) as [|] eqn:Hwx0.
          * exfalso. apply Hx0. apply eqb_eq in Hwx0. rewrite <- Hwx0. destruct Hw as [_ [_ [_ [Hw _]]]]. apply Hw.
          * reflexivity.
        + apply HAy.
        + apply HUyG.
        + apply HuU with (U := Uy). repeat split.
          * apply HUyG.
          * apply HeqUy.
          * apply HAy.
      - repeat split.
        + easy.
        + easy.
        + apply HAy.
        + apply HUyG.
        + apply HuU with (U := Uy). repeat split.
          * apply HUyG.
          * apply HeqUy.
          * apply HAy.
        + specialize HU with (U := Uy). apply HU. apply HUyG. }
    rewrite HvUx in HvAxAy. rewrite HvUy in HvAxAy. inversion HvAxAy.
    apply Hxy. apply H1.
  - intros HuZ'. apply member_In_equiv in HuZ'. rewrite HuZ' in HuZ. discriminate HuZ.
  - apply Hconn.
  - rewrite HeqAZ. apply nodes_map_to_assignment.
Qed.

Lemma nodefun_value_only_affected_by_unblocked_ancestors {X: Type}: forall (G: graph) (u: node) (Z: nodes) (U1 U2: assignments X) (g: graphfun),
  find_value G g u U1 [] <> find_value G g u U2 []
  -> exists (a: node), In a (find_unblocked_ancestors G u Z)
      /\ get_assigned_value U1 a <> get_assigned_value U2 a
      /\ find_value G g a U1 [] <> find_value G g a U2 [].
Proof.
Admitted.

Theorem conditional_independence_d_separation {X : Type} `{EqType X}: forall (G: graph) (u v: node),
  u <> v /\ generic_graph_and_type_properties_hold X G
  -> forall (Z: nodes), subset Z (nodes_in_graph G) = true /\ each_node_appears_once Z /\ member u Z = false /\ member v Z = false
  -> d_separated_bool u v G Z = true <-> conditionally_independent X G u v Z.
Proof.
  intros G u' v'. intros [Huveq HG] Z HZ. split.
  { intros Hdsep. unfold conditionally_independent.
    intros AZ HAZ g a Ua Aa [HAa [HUa HZUa]]. intros b Ub Ab [HUab [HAb HUb]]. intros Ub' Ab' [HUbb' [HAb' [HUb' HZUb']]].

  assert (Hdconn1: forall (anc u: node) (l: nodes), is_directed_path_in_graph (anc, u, l) G = true /\
          (forall w : node, w = anc \/ In w l -> ~ In w Z) -> d_connected_2 (anc, u, l) G Z).
  { intros anc u l [Hdir HlZ]. apply directed_path_is_path in Hdir as Hpath.
    unfold d_connected_2. repeat split.
    - destruct (overlap Z (find_mediators_in_path (anc, u, l) G)) as [|] eqn:Hmed.
      + apply overlap_has_member_in_common in Hmed. destruct Hmed as [m [HmZ Hmmed]].
        assert (Hml: In m l).
        { apply intermediate_node_in_path with (x := m) in Hpath. apply Hpath. left. apply Hmmed. }
        specialize HlZ with (w := m). assert (F: ~(In m Z)). { apply HlZ. right. apply Hml. } exfalso. apply F. apply HmZ.
      + reflexivity.
    - destruct (overlap Z (find_confounders_in_path (anc, u, l) G)) as [|] eqn:Hcon.
      + apply overlap_has_member_in_common in Hcon. destruct Hcon as [c [HcZ Hccon]].
        assert (Hcl: In c l).
        { apply intermediate_node_in_path with (x := c) in Hpath. apply Hpath. right. left. apply Hccon. }
        specialize HlZ with (w := c). assert (F: ~(In c Z)). { apply HlZ. right. apply Hcl. } exfalso. apply F. apply HcZ.
      + reflexivity.
    - destruct (collider_descendants_not_conditioned (find_colliders_in_path (anc, u, l) G) G Z) as [|] eqn:Hcol.
      + destruct (find_colliders_in_path (anc, u, l) G) as [| h t] eqn:Hcol'.
        ** simpl in Hcol. discriminate Hcol.
        ** (* h is a collider, so h in l. But the path v...l...u is directed, contradiction *)
           assert (Hmemh: In h l).
           { apply intermediate_node_in_path with (x := h) in Hpath. apply Hpath. right. right. rewrite Hcol'. left. reflexivity. }
           assert (Hmedh: In h (find_mediators_in_path (anc, u, l) G)).
           { apply directed_path_all_mediators with (m := h). split. apply Hdir. apply Hmemh. }
           apply if_mediator_then_not_confounder_path in Hmedh. destruct Hmedh as [_ Hhcol]. exfalso. apply Hhcol. rewrite Hcol'. left. reflexivity.
           destruct HG as [_ [_ HG]]. apply HG.
      + unfold all_colliders_have_descendant_conditioned_on. unfold collider_descendants_not_conditioned in Hcol. apply forallb_true_iff_mem.
        intros col Hcol'. apply descendants_in_or_not_in. apply example_usage with (x := col) in Hcol.
        ** apply Hcol.
        ** apply Hcol'. }

  assert (Hdconn2: forall (anc u v: node) (lu lv: nodes), is_directed_path_in_graph (anc, u, lu) G = true /\ (forall w : node, w = anc \/ In w lu -> ~ In w Z)
                                                       /\ is_directed_path_in_graph (anc, v, lv) G = true /\ (forall w : node, w = anc \/ In w lv -> ~ In w Z)
                   -> is_path_in_graph (u, v, (rev lu) ++ (anc :: lv)) G = true /\ acyclic_path_2 (u, v, (rev lu) ++ (anc :: lv)) -> d_connected_2 (u, v, (rev lu) ++ anc :: lv) G Z).
  { intros anc u v lu lv [Hdiru [HluZ [Hdirv HlvZ]]] [Hpath Hcyc].
    assert (Hconnu: d_connected_2 (anc, u, lu) G Z). { apply Hdconn1. split. apply Hdiru. apply HluZ. }
    assert (Hconnv: d_connected_2 (anc, v, lv) G Z). { apply Hdconn1. split. apply Hdirv. apply HlvZ. }
    apply concat_d_connected_paths.
    - destruct HG as [_ [_ HG]]. apply HG.
    - apply Hpath.
    - split. apply reverse_d_connected_paths. apply Hconnu. split. apply Hconnv. apply Hcyc.
    - right. left. split.
      + apply confounders_vs_edges_in_path. destruct lu as [| hlu tlu].
        * destruct lv as [| hlv tlv].
          -- exists u. exists v. split.
             ++ simpl. repeat rewrite eqb_refl. reflexivity.
             ++ simpl in Hdiru. rewrite andb_comm in Hdiru. simpl in Hdiru. split. apply Hdiru.
                simpl in Hdirv. rewrite andb_comm in Hdirv. simpl in Hdirv. apply Hdirv.
          -- exists u. exists hlv. split.
             ++ apply sublist_breaks_down_list. exists []. exists (tlv ++ [v]). simpl. reflexivity.
             ++ simpl in Hdiru. rewrite andb_comm in Hdiru. simpl in Hdiru. split. apply Hdiru.
                simpl in Hdirv. apply split_and_true in Hdirv. destruct Hdirv as [Hdirv _]. apply Hdirv.
        * destruct lv as [| hlv tlv].
          -- exists hlu. exists v. split.
             ++ apply sublist_breaks_down_list. exists (u :: rev tlu). exists []. simpl. repeat rewrite <- app_assoc; simpl. reflexivity.
             ++ simpl in Hdiru. apply split_and_true in Hdiru. destruct Hdiru as [Hdiru _]. split. apply Hdiru.
                simpl in Hdirv. apply split_and_true in Hdirv. destruct Hdirv as [Hdirv _]. apply Hdirv.
          -- exists hlu. exists hlv. split.
             ++ apply sublist_breaks_down_list. exists (u :: rev tlu). exists (tlv ++ [v]). simpl. repeat rewrite <- app_assoc; simpl. reflexivity.
             ++ simpl in Hdiru. apply split_and_true in Hdiru. destruct Hdiru as [Hdiru _]. split. apply Hdiru.
                simpl in Hdirv. apply split_and_true in Hdirv. destruct Hdirv as [Hdirv _]. apply Hdirv.
      + specialize HluZ with (w := anc). apply HluZ. left. reflexivity. }

    assert (Hdconn: forall (anc: node) (u v: node), u <> v -> In anc (find_unblocked_ancestors G v Z) /\ In anc (find_unblocked_ancestors G u Z)
                    -> d_separated_bool u v G Z = true -> False).
    { intros anc u v Huv [Hancv Hancu] Hsep.
      destruct (member v (find_unblocked_ancestors G u Z)) as [|] eqn:Heqancv.
      - apply member_In_equiv in Heqancv. destruct (member u (find_unblocked_ancestors G v Z)) as [|] eqn:Heqancu.
        + (* cycle, contradiction *) apply member_In_equiv in Heqancu. apply unblocked_ancestors_have_unblocked_directed_path in Heqancv.
          apply unblocked_ancestors_have_unblocked_directed_path in Heqancu.
          destruct Heqancu as [Heqancu | Heqancu]. apply Huv. apply Heqancu.
          destruct Heqancv as [Heqancv | Heqancv]. apply Huv. rewrite Heqancv. reflexivity.
          destruct Heqancu as [lu [Hlu _]]. destruct Heqancv as [lv [Hlv _]].
          assert (Hcycle: is_directed_path_in_graph (concat u v u lu lv) G = true).
          { apply concat_directed_paths. split. apply Hlu. apply Hlv. }
          destruct HG as [_ [_ HG]]. apply contains_cycle_false_correct with (p := (concat u v u lu lv)) in HG.
          * unfold concat in HG. unfold acyclic_path_2 in HG. destruct HG as [HG _]. apply HG. reflexivity.
          * apply directed_path_is_path. apply Hcycle.
        + (* v -> ...l... -> u is d-connected path *) clear Hancu. clear Hancv.
          apply unblocked_ancestors_have_unblocked_directed_path in Heqancv. destruct Heqancv as [Hancu | Hancu]. apply Huv. rewrite Hancu. reflexivity.
          destruct Hancu as [l [Hdir [Hcycu HlZ]]].
          assert (Hdir': d_connected_2 (v, u, l) G Z). { apply Hdconn1. split. apply Hdir. apply HlZ. }
          apply d_connected_path_not_d_separated with (l := rev l) in Hsep.
          * apply Hsep.
          * apply reverse_d_connected_paths. apply Hdir'.
          * split. apply reverse_path_in_graph. apply directed_path_is_path. apply Hdir. apply reverse_path_still_acyclic. apply Hcycu.
      - pose proof Hancv as Hancv'. apply unblocked_ancestors_have_unblocked_directed_path in Hancv. destruct Hancv as [Hancv | Hancv].
        (* v is not an unblocked ancestor of u *) rewrite Hancv in Hancu. apply member_In_equiv in Hancu. rewrite Hancu in Heqancv. discriminate Heqancv.
        destruct (member u (find_unblocked_ancestors G v Z)) as [|] eqn:Heqancu.
        + (* u -> ...lv... -> v is a d-connected path *) clear Hancu. clear Hancv. apply member_In_equiv in Heqancu.
          apply unblocked_ancestors_have_unblocked_directed_path in Heqancu. destruct Heqancu as [Hancv | Hancv]. apply Huv. apply Hancv.
          destruct Hancv as [l [Hdir [Hcycv HlZ]]].
          assert (Hdir': d_connected_2 (u, v, l) G Z). { apply Hdconn1. split. apply Hdir. apply HlZ. }
          apply d_connected_path_not_d_separated with (l := l) in Hsep.
          * apply Hsep.
          * apply Hdir'.
          * split. apply directed_path_is_path. apply Hdir. apply Hcycv.
        + (* u <- ...lu... <- anc -> ...lv... -> v  is a d-connected path *)
          apply unblocked_ancestors_have_unblocked_directed_path in Hancu. destruct Hancu as [Hancu | Hancu]. rewrite Hancu in Hancv'. apply member_In_equiv in Hancv'. rewrite Hancv' in Heqancu. discriminate Heqancu.
          assert (Hanc': exists (anc': node) (lu lv: nodes), is_directed_path_in_graph (anc', u, lu) G = true /\ is_directed_path_in_graph (anc', v, lv) G = true
                         /\ (forall w : node, w = anc' \/ In w lu \/ In w lv -> ~ In w Z) /\ acyclic_path_2 (u, v, (rev lu) ++ (anc' :: lv))).
          { destruct Hancv as [lv' Hv']. destruct Hancu as [lu' Hu']. apply acyclic_path_if_common_ancestor with (anc := anc) (lu := lu') (lv := lv') (len := S (length lu')).
            - split. apply Huv. split. intros Hmem. apply member_In_equiv in Hmem. rewrite Hmem in Heqancu. discriminate Heqancu.
              intros Hmem. apply member_In_equiv in Hmem. rewrite Hmem in Heqancv. discriminate Heqancv.
            - lia.
            - apply Hv'.
            - apply Hu'. }
          destruct Hanc' as [anc' [lu [lv [Hdiru [Hdirv [HlulvZ Hcycuv]]]]]].
          assert (Hpath: is_path_in_graph (u, v, (rev lu) ++ (anc' :: lv)) G = true).
          { apply concat_paths_still_a_path. split. apply reverse_path_in_graph. apply directed_path_is_path. apply Hdiru.
            apply directed_path_is_path. apply Hdirv. }
          assert (Hconn: d_connected_2 (u, v, (rev lu) ++ anc' :: lv) G Z).
          { apply Hdconn2. repeat split.
            - apply Hdiru.
            - intros w Hw. apply HlulvZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. left. apply Hw.
            - apply Hdirv.
            - intros w Hw. apply HlulvZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. right. apply Hw.
            - split. apply Hpath. apply Hcycuv. }
          apply d_connected_path_not_d_separated with (u := u) (v := v) (l := (rev lu) ++ (anc' :: lv)) (G := G) (Z := Z).
          -- apply Hconn.
          -- split. apply Hpath. apply Hcycuv.
          -- apply Hsep. }

    remember u' as u. remember v' as v.
    assert (HvUa: exists (va: X), find_value G g v Ua [] = Some va).
    { apply find_value_existence.
      - destruct HG as [_ HG]. apply HG.
      - split. destruct HUa as [HUa _]. apply HUa. admit. }
    assert (HvUb: exists (vb: X), find_value G g v Ub [] = Some vb).
    { apply find_value_existence.
      - destruct HG as [_ HG]. apply HG.
      - split. destruct HUb as [HUb _]. apply HUb. admit. }
    destruct HvUa as [va HvUa]. destruct HvUb as [vb HvUb].
    assert (Hv: find_value G g v Ua [] = find_value G g v Ub []).
    { destruct (eqb va vb) as [|] eqn:Hvavb.
      - apply eqb_eq' in Hvavb. rewrite Hvavb in HvUa. rewrite HvUa. rewrite HvUb. reflexivity.
      - (* contradiction: this would mean u and v share an unblocked ancestor, and thus a d-connected path *)
        assert (Hfvavb: find_value G g v Ua [] <> find_value G g v Ub []).
        { rewrite HvUa. rewrite HvUb. intros F. inversion F. rewrite H1 in Hvavb. rewrite eqb_refl' in Hvavb. discriminate Hvavb. }
        apply nodefun_value_only_affected_by_unblocked_ancestors with (Z := Z) in Hfvavb. destruct Hfvavb as [anc [Hancv [HancU Hancf]]].
        unfold assignments_change_only_for_subset in HUab. specialize HUab with (x := anc).
        assert (Hancu: In anc (find_unblocked_ancestors G u Z)).
        { destruct (member anc (find_unblocked_ancestors G u Z)) as [|] eqn:Hancu'.
          - apply member_In_equiv. apply Hancu'.
          - destruct HUab as [_ HUab]. assert (Hancu: ~ In anc (find_unblocked_ancestors G u Z)).
            { intros F. apply member_In_equiv in F. rewrite Hancu' in F. discriminate F. }
            clear Hancu'. apply HUab in Hancu. rewrite Hancu in HancU. exfalso. apply HancU. reflexivity. }   
        specialize Hdconn with (anc := anc) (u := u) (v := v). exfalso. apply Hdconn. repeat split.
        + apply Huveq.
        + split. apply Hancv. apply Hancu.
        + apply Hdsep. }
    (* Hv shows that f(v, Ua) = f(v, Ub). Now show f(v, Ub) = f(v, Ub') *)
    assert (HvUb': exists (vb': X), find_value G g v Ub' [] = Some vb').
    { apply find_value_existence.
      - destruct HG as [_ HG]. apply HG.
      - split. destruct HUb' as [HUb' _]. apply HUb'. admit. }
    destruct HvUb' as [vb' HvUb'].
    assert (Hv': find_value G g v Ub [] = find_value G g v Ub' []).
    { destruct (eqb vb vb') as [|] eqn:Hvbvb'.
      - apply eqb_eq' in Hvbvb'. rewrite Hvbvb' in HvUb. rewrite HvUb. rewrite HvUb'. reflexivity.
      - (* contradiction: this would mean that there is a node z in Z that shares unblocked ancestors with u and v, which forms a d-connected path *)
        assert (Hfvbvb': find_value G g v Ub [] <> find_value G g v Ub' []).
        { rewrite HvUb. rewrite HvUb'. intros F. inversion F. rewrite H1 in Hvbvb'. rewrite eqb_refl' in Hvbvb'. discriminate Hvbvb'. }
        apply nodefun_value_only_affected_by_unblocked_ancestors with (Z := Z) in Hfvbvb'. destruct Hfvbvb' as [ancv [Hancv [HancvU Hancvf]]].
        unfold assignments_change_only_for_subset in HUbb'. specialize HUbb' with (x := ancv).
        assert (Hz: exists (z: node), In ancv (find_unblocked_ancestors G z Z) /\ is_assigned AZ z = true
                       /\ find_value G g z Ub [] <> get_assigned_value AZ z).
        { apply unblocked_ancestor_of_node_in_Z with (Ab := Ab). repeat split.
          - destruct (member ancv (find_unblocked_ancestors_in_Z G Z AZ Ab)) as [|] eqn:HmemZ.
            + apply member_In_equiv in HmemZ. apply HmemZ.
            + assert (F: get_assigned_value Ub ancv = get_assigned_value Ub' ancv).
              { destruct HUbb' as [_ HUbb']. apply HUbb'. intros F. apply member_In_equiv in F. rewrite F in HmemZ. discriminate HmemZ. }
              exfalso. apply HancvU. apply F.
          - apply HAb.
          - destruct HAZ as [_ HAZ]. apply HAZ. }
        destruct Hz as [z [Hancvz [HAZz HUbz]]].
        (* now show that z shares and unblocked ancestor with u due to HUab *)
        assert (HzZ: In z Z).
        { destruct (member z Z) as [|] eqn:HzZ.
          - apply member_In_equiv in HzZ. apply HzZ.
          - unfold is_exact_assignment_for in HAZ. destruct HAZ as [[_ HAZ] _]. specialize HAZ with (u := z).
            apply HAZ in HzZ. rewrite HzZ in HAZz. discriminate HAZz. }
        assert (Hfzazb: find_value G g z Ua [] <> find_value G g z Ub []).
        { (* show that f(z, Ua) = AZ(z) using HZUa *)
          unfold unobs_conditions_on_Z in HZUa. specialize HZUa with (w := z). apply HZUa in HzZ. rewrite HzZ. intros F. rewrite F in HUbz. apply HUbz. reflexivity. }
        apply nodefun_value_only_affected_by_unblocked_ancestors with (Z := Z) in Hfzazb. destruct Hfzazb as [ancu [Hancuz [HancuU Hancuf]]].
        unfold assignments_change_only_for_subset in HUab. specialize HUab with (x := ancu).
        assert (Hancu: In ancu (find_unblocked_ancestors G u Z)).
        { destruct (member ancu (find_unblocked_ancestors G u Z)) as [|] eqn:Hancu'.
          - apply member_In_equiv. apply Hancu'.
          - destruct HUab as [_ HUab]. assert (Hancu: ~ In ancu (find_unblocked_ancestors G u Z)).
            { intros F. apply member_In_equiv in F. rewrite Hancu' in F. discriminate F. }
            clear Hancu'. apply HUab in Hancu. rewrite Hancu in HancuU. exfalso. apply HancuU. reflexivity. }
        (* u <- ... <- ancu -> ... -> z <- ... <- ancv -> ... -> v is a d-connected path *)
        destruct (overlap (find_unblocked_ancestors G u Z) (find_unblocked_ancestors G v Z)) as [|] eqn:Hover.
        { apply overlap_has_member_in_common in Hover. clear Hancu. clear Hancv. destruct Hover as [anc [Hancu Hancv]].
          apply Hdconn with (anc := anc) in Hdsep.
          * exfalso. apply Hdsep.
          * apply Huveq.
          * split. apply Hancv. apply Hancu. }
        { apply unblocked_ancestors_have_unblocked_directed_path in Hancv. destruct Hancv as [Hancv | Hancv].
          + (* u <- ... <- ancu -> ... -> z <- ... <- v *)
            pose proof Hancvz as Hancvz'. apply unblocked_ancestors_have_unblocked_directed_path in Hancvz. destruct Hancvz as [Hancvz | Hancvz].
            * (* z = v: then ancu is a common ancestor of u and v, so can use prev case Hdconn *)
              specialize Hdconn with (anc := ancu) (u := u) (v := v). exfalso. apply Hdconn.
              -- apply Huveq.
              -- split. rewrite <- Hancvz in Hancuz. rewrite Hancv in Hancuz. apply Hancuz. apply Hancu.
              -- apply Hdsep.
            * (* u <- ... <- ancu -> ... -> z <- ..lv.. <- v *)
              destruct Hancvz as [lv [Hdirv HlvZ]].
              pose proof Hancu as Hancu'. apply unblocked_ancestors_have_unblocked_directed_path in Hancu. destruct Hancu as [Hancu | Hancu].
              -- (* u -> ... -> z <- ..lv.. <- v *)
                 apply unblocked_ancestors_have_unblocked_directed_path in Hancuz. destruct Hancuz as [Hancuz | Hancuz].
                 ++ (* u <- ..lv.. <- v: v is common ancestor of u and v, Hdconn *)
                    specialize Hdconn with (anc := v) (u := u) (v := v). exfalso. apply Hdconn.
                    ** apply Huveq.
                    ** split. { unfold find_unblocked_ancestors. left. reflexivity. } { rewrite Hancv in Hancvz'. rewrite <- Hancuz in Hancvz'. rewrite Hancu in Hancvz'. apply Hancvz'. }
                    ** apply Hdsep.
                 ++ (* u -> ..lu.. -> z <- ..lv.. <- v *)
                    destruct Hancuz as [lu [Hdiru HluZ]].
                    assert (Hpath: is_path_in_graph (concat u z v lu (rev lv)) G = true).
                    { apply concat_paths_still_a_path. split.
                      + rewrite Hancu in Hdiru. apply directed_path_is_path in Hdiru. apply Hdiru.
                      + apply reverse_path_in_graph. rewrite Hancv in Hdirv. apply directed_path_is_path in Hdirv. apply Hdirv. }
                    assert (Hconn: d_connected_2 (concat u z v lu (rev lv)) G Z).
                    { apply concat_d_connected_paths.
                      - destruct HG as [_ [_ HG]]. apply HG.
                      - apply Hpath.
                      - split.
                        + specialize Hdconn1 with (anc := u) (u := z) (l := lu). apply Hdconn1. split.
                          * rewrite Hancu in Hdiru. apply Hdiru.
                          * rewrite Hancu in HluZ. apply HluZ.
                        + split.
                        { apply reverse_d_connected_paths. apply Hdconn1. split. rewrite Hancv in Hdirv. apply Hdirv. rewrite Hancv in HlvZ. apply HlvZ. }
                        { admit. }
                      - right. right. split.
                        + apply colliders_vs_edges_in_path. rewrite Hancu in Hdiru. rewrite Hancv in Hdirv.
                          apply directed_path_has_directed_edge_end in Hdiru as Hdiru'. destruct Hdiru' as [Hdiru' | Hdiru'].
                          * apply directed_path_has_directed_edge_end in Hdirv as Hdirv'. destruct Hdirv' as [Hdirv' | Hdirv'].
                            exists u. exists v. split.
                            -- rewrite Hdirv'. rewrite Hdiru'. apply sublist_breaks_down_list. exists []. exists []. simpl. reflexivity.
                            -- split. rewrite Hdiru' in Hdiru. simpl in Hdiru. rewrite andb_comm in Hdiru. simpl in Hdiru. apply Hdiru.
                               rewrite Hdirv' in Hdirv. simpl in Hdirv. rewrite andb_comm in Hdirv. simpl in Hdirv. apply Hdirv.
                            -- destruct Hdirv' as [l' [x Hdirv']]. exists u. exists x. split.
                               ++ apply sublist_breaks_down_list. exists []. exists (rev l' ++ [v]).
                                  simpl. rewrite Hdiru'. destruct Hdirv' as [Hdirv' Hxz]. rewrite Hdirv'. rewrite reverse_list_append.
                                  simpl. reflexivity.
                               ++ split. rewrite Hdiru' in Hdiru. simpl in Hdiru. rewrite andb_comm in Hdiru. simpl in Hdiru. apply Hdiru.
                                  destruct Hdirv' as [_ Hdirv']. apply Hdirv'.
                          * destruct Hdiru' as [lu' [x1 [Hlu' Hx1z]]].
                            apply directed_path_has_directed_edge_end in Hdirv as Hdirv'. destruct Hdirv' as [Hdirv' | Hdirv'].
                            { exists x1. exists v. split.
                              -- rewrite Hdirv'. apply sublist_breaks_down_list. rewrite Hlu'. exists (u :: lu'). exists []. simpl. unfold node.
                                 f_equal. repeat rewrite <- app_assoc; simpl. reflexivity.
                              -- split. apply Hx1z. rewrite Hdirv' in Hdirv. simpl in Hdirv. rewrite andb_comm in Hdirv. simpl in Hdirv. apply Hdirv. }
                            { destruct Hdirv' as [lv' [x2 [Hlv' Hx2z]]]. exists x1. exists x2. split.
                              -- apply sublist_breaks_down_list. exists (u :: lu'). exists (rev lv' ++ [v]).
                                 simpl. rewrite Hlv'. rewrite reverse_list_append.
                                 simpl. rewrite Hlu'. simpl. unfold node. f_equal. repeat rewrite <- app_assoc; simpl. reflexivity.
                              -- split. apply Hx1z. apply Hx2z. }
                        + unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists z.
                          split.
                          * unfold find_descendants. left. reflexivity.
                          * apply HzZ. }
                        (* TODO need to address case of the two paths meeting prior to z, in which case z is the descendant of a collider *)
                    exfalso. apply d_connected_path_not_d_separated with (u := u) (v := v) (l := (lu ++ z :: rev lv)) (G := G) (Z := Z).
                    ** apply Hconn.
                    ** split. apply Hpath. admit.
                    ** apply Hdsep.
              -- destruct Hancu as [lu'' [Hdiru' [Hcycu HluZ']]].
                 apply unblocked_ancestors_have_unblocked_directed_path in Hancuz. destruct Hancuz as [Hancuz | Hancuz].
                 ++ (* ancu = z: contradiction, z is in Z, but ancu is not *)
                    specialize HluZ' with (w := z). exfalso. apply HluZ'. left. symmetry. apply Hancuz. apply HzZ.
                 ++ (* u <- ..rev(lu).. <- ancu -> ..lu2.. -> z <- ..rev(lv).. <- v *)
                    assert (Hancu: exists (anc': node) (lu lu': nodes), is_directed_path_in_graph (anc', u, lu) G = true /\ is_directed_path_in_graph (anc', z, lu') G = true
                           /\ (forall w : node, w = anc' \/ In w lu \/ In w lu' -> ~ In w Z) /\ acyclic_path_2 (u, z, (rev lu) ++ (anc' :: lu'))).
                    { destruct Hancuz as [lu' Hz']. apply acyclic_path_if_common_ancestor with (anc := ancu) (lu := lu'') (lv := lu') (len := S (length lu'')).
                      - admit.
                      - lia.
                      - apply Hz'.
                      - split. apply Hdiru'. split. apply Hcycu. apply HluZ'. }
                    destruct Hancu as [ancu' [lu [lu' [Hdiru [Hdiruz [HluZ Hcycuz]]]]]]. clear Hdiru'. clear HluZ'. clear Hcycu. clear Hancuz.
                    assert (Hpath: is_path_in_graph (concat u ancu' z (rev lu) lu') G = true).
                    { apply concat_paths_still_a_path. split.
                      + apply reverse_path_in_graph. apply directed_path_is_path in Hdiru. apply Hdiru.
                      + apply directed_path_is_path in Hdiruz. apply Hdiruz. }
                    assert (Hconn1: d_connected_2 (u, z, rev lu ++ ancu' :: lu') G Z).
                    { apply Hdconn2.
                      - repeat split.
                        + apply Hdiru.
                        + intros w Hw. apply HluZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. left. apply Hw.
                        + apply Hdiruz.
                        + intros w Hw. apply HluZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. right. apply Hw.
                      - split. apply Hpath. apply Hcycuz. }
                    assert (Hconn2: d_connected_2 (z, v, rev lv) G Z).
                    { apply reverse_d_connected_paths. apply Hdconn1. split. rewrite Hancv in Hdirv. apply Hdirv. rewrite Hancv in HlvZ. apply HlvZ. }
                    assert (Hpath': is_path_in_graph (concat u z v (rev lu ++ ancu' :: lu') (rev lv)) G = true).
                    { apply concat_paths_still_a_path. split.
                      + apply Hpath.
                      + apply reverse_path_in_graph. apply directed_path_is_path in Hdirv. rewrite Hancv in Hdirv. apply Hdirv. }
                    assert (Hconn3: d_connected_2 (concat u z v (rev lu ++ ancu' :: lu') (rev lv)) G Z).
                    { apply concat_d_connected_paths.
                      - destruct HG as [_ [_ HG]]. apply HG.
                      - apply Hpath'.
                      - split. apply Hconn1. split. apply Hconn2.
                        admit.
                      - right. right. split.
                        + apply colliders_vs_edges_in_path.
                          apply directed_path_has_directed_edge_end in Hdiruz as Hdiruz'. destruct Hdiruz' as [Hdiruz' | Hdiruz'].
                          * apply directed_path_has_directed_edge_end in Hdirv as Hdirv'. destruct Hdirv' as [Hdirv' | Hdirv'].
                            exists ancu'. exists v. split.
                            -- rewrite Hdirv'. rewrite Hdiruz'. apply sublist_breaks_down_list. exists (u :: (rev lu)). exists []. simpl.
                               rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity.
                            -- split. rewrite Hdiruz' in Hdiruz. simpl in Hdiruz. rewrite andb_comm in Hdiruz. simpl in Hdiruz. apply Hdiruz.
                               rewrite Hdirv' in Hdirv. simpl in Hdirv. rewrite andb_comm in Hdirv. simpl in Hdirv. rewrite Hancv in Hdirv. apply Hdirv.
                            -- destruct Hdirv' as [l' [x Hdirv']]. exists ancu'. exists x. split.
                               ++ apply sublist_breaks_down_list. exists (u :: (rev lu)). exists (rev l' ++ [v]).
                                  simpl. rewrite Hdiruz'. destruct Hdirv' as [Hdirv' Hxz]. rewrite Hdirv'. rewrite reverse_list_append.
                                  simpl. rewrite <- app_assoc. rewrite <- append_vs_concat. simpl. reflexivity.
                               ++ split. rewrite Hdiruz' in Hdiruz. simpl in Hdiruz. rewrite andb_comm in Hdiruz. simpl in Hdiruz. apply Hdiruz.
                                  destruct Hdirv' as [_ Hdirv']. apply Hdirv'.
                          * destruct Hdiruz' as [lu2' [x1 [Hlu2 Hxz]]].
                            apply directed_path_has_directed_edge_end in Hdirv as Hdirv'. destruct Hdirv' as [Hdirv' | Hdirv'].
                            exists x1. exists v. split.
                            -- rewrite Hdirv'. apply sublist_breaks_down_list. rewrite Hlu2. exists (u :: (rev lu) ++ ancu' :: lu2'). exists []. simpl. unfold node.
                               f_equal. repeat rewrite <- app_assoc; simpl. rewrite <- app_assoc. reflexivity.
                            -- split. apply Hxz. rewrite Hdirv' in Hdirv. simpl in Hdirv. rewrite andb_comm in Hdirv. simpl in Hdirv. rewrite Hancv in Hdirv. apply Hdirv.
                            -- destruct Hdirv' as [lv' [x2 Hdirv']]. exists x1. exists x2. split.
                               ++ apply sublist_breaks_down_list. exists (u :: (rev lu) ++ ancu' :: lu2'). exists (rev lv' ++ [v]).
                                  simpl. destruct Hdirv' as [Hlv' Hx2z]. rewrite Hlv'. rewrite reverse_list_append.
                                  simpl. rewrite Hlu2. simpl. unfold node. f_equal. repeat rewrite <- app_assoc; simpl. rewrite <- app_assoc. reflexivity.
                               ++ split. apply Hxz. destruct Hdirv' as [_ Hdirv']. apply Hdirv'.
                        + unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists z. split.
                          * unfold find_descendants. left. reflexivity.
                          * apply HzZ. }
                    unfold concat in Hconn3. apply d_connected_path_not_d_separated with (l := (rev lu ++ ancu' :: lu') ++ z :: rev lv) in Hdsep.
                    ** exfalso. apply Hdsep.
                    ** apply Hconn3.
                    ** split. apply Hpath'. admit.
          + (* u <- ... <- ancu -> ... -> z <- ... <- ancv -> ... -> v *)
            destruct Hancv as [lv [Hdirv [Hcycv HlvZ]]].
            pose proof Hancvz as Hancvz'. apply unblocked_ancestors_have_unblocked_directed_path in Hancvz. destruct Hancvz as [Hancvz | Hancvz].
            * (* ancv = z: contradiction, z is in Z, but ancv is not *)
              specialize HlvZ with (w := z). exfalso. apply HlvZ. left. symmetry. apply Hancvz. apply HzZ.
            * destruct Hancvz as [lv' [Hdirv' HlvZ']]. (* u <- ... <- ancu -> ... -> z <- ..rev(lv').. <- ancv -> lv -> v *)
              apply unblocked_ancestors_have_unblocked_directed_path in Hancu. destruct Hancu as [Hancu | Hancu].
              -- (* u -> ... -> z <- ..rev(lv').. <- ancv -> lv -> v *) admit.
              -- destruct Hancu as [lu [Hancu [Hcycu HluZ]]].
                 apply unblocked_ancestors_have_unblocked_directed_path in Hancuz. destruct Hancuz as [Hancuz | Hancuz].
                 ++ (* ancu = z: contradiction, z is in Z, but ancu is not *)
                    specialize HluZ with (w := z). exfalso. apply HluZ. left. symmetry. apply Hancuz. apply HzZ.
                 ++ destruct Hancuz as [lu' [Hancuz HluZ']].
                    (* u <- ..rev(lu).. <- ancu -> ..lu'.. -> z <- ..rev(lv').. <- ancv -> ..lv.. -> v *)
                    assert (Hpath: is_path_in_graph (u, z, (rev lu) ++ ancu :: lu') G = true).
                    { apply concat_paths_still_a_path. split.
                      + apply reverse_path_in_graph. apply directed_path_is_path in Hancu. apply Hancu.
                      + apply directed_path_is_path in Hancuz. apply Hancuz. }
                    assert (Hconn1: d_connected_2 (u, z, (rev lu) ++ ancu :: lu') G Z).
                    { apply Hdconn2. repeat split.
                      apply Hancu. apply HluZ. apply Hancuz. apply HluZ'. split. apply Hpath.
                      apply concat_paths_acyclic.
                      - split.
                        + intros Huz. destruct HZ as [_ [_ [Huz' _]]]. apply member_In_equiv in HzZ. rewrite <- Huz in HzZ. rewrite HzZ in Huz'. discriminate Huz'.
                        + split. apply reverse_path_still_acyclic. apply Hcycu. destruct HluZ' as [Hcycz _]. apply Hcycz.
                      - admit.
                      - admit. } (* TODO make this more like the proof of Hdconn and reuse for below version *)
                    assert (Hpath': is_path_in_graph (z, v, (rev lv') ++ ancv :: lv) G = true).
                    { apply concat_paths_still_a_path. split.
                      + apply reverse_path_in_graph. apply directed_path_is_path in Hdirv'. apply Hdirv'.
                      + apply directed_path_is_path in Hdirv. apply Hdirv. }
                    assert (Hconn2: d_connected_2 (z, v, (rev lv') ++ ancv :: lv) G Z).
                    { apply Hdconn2. repeat split.
                      apply Hdirv'. apply HlvZ'. apply Hdirv. apply HlvZ. split. apply Hpath'. admit. }
                    assert (Hconn3: d_connected_2 (concat u z v ((rev lu) ++ ancu :: lu') ((rev lv') ++ ancv :: lv)) G Z).
                    { apply concat_d_connected_paths.
                      - destruct HG as [_ [_ HG]]. apply HG.
                      - apply concat_paths_still_a_path. split.
                        + apply Hpath.
                        + apply Hpath'.
                      - split. apply Hconn1. split. apply Hconn2. admit.
                      - right. right. split.
                        + apply colliders_vs_edges_in_path.
                          apply directed_path_has_directed_edge_end in Hancuz as Hancuz'. destruct Hancuz' as [Hancuz' | Hancuz'].
                          * apply directed_path_has_directed_edge_end in Hdirv' as Hdirv''. destruct Hdirv'' as [Hdirv'' | Hdirv''].
                            exists ancu. exists ancv. split.
                            -- rewrite Hdirv''. rewrite Hancuz'. apply sublist_breaks_down_list. exists (u :: (rev lu)). exists (lv ++ [v]). simpl.
                               repeat rewrite <- app_assoc; simpl. reflexivity.
                            -- split. rewrite Hancuz' in Hancuz. simpl in Hancuz. rewrite andb_comm in Hancuz. simpl in Hancuz. apply Hancuz.
                               rewrite Hdirv'' in Hdirv'. simpl in Hdirv'. rewrite andb_comm in Hdirv'. simpl in Hdirv'. apply Hdirv'.
                            -- destruct Hdirv'' as [lv'' [x1 Hdirv'']]. exists ancu. exists x1. split.
                               ++ apply sublist_breaks_down_list. exists (u :: (rev lu)). exists (rev lv'' ++ ancv :: lv ++ [v]). rewrite Hancuz'.
                                  destruct Hdirv'' as [Hdirv'' Hx1z]. rewrite Hdirv''. rewrite reverse_list_append.
                                  repeat simpl; rewrite <- app_assoc. simpl. rewrite append_vs_concat. rewrite <- app_assoc. simpl. reflexivity.
                               ++ split. rewrite Hancuz' in Hancuz. simpl in Hancuz. rewrite andb_comm in Hancuz. simpl in Hancuz. apply Hancuz.
                                  destruct Hdirv'' as [_ Hdirv'']. apply Hdirv''.
                          * destruct Hancuz' as [lu'' [x1 [Hlu'' Hx1z]]].
                            apply directed_path_has_directed_edge_end in Hdirv' as Hdirv''. destruct Hdirv'' as [Hdirv'' | Hdirv''].
                            exists x1. exists ancv. split.
                            -- rewrite Hdirv''. apply sublist_breaks_down_list. rewrite Hlu''. exists (u :: (rev lu) ++ ancu :: lu''). exists (lv ++ [v]). simpl. unfold node.
                               f_equal. repeat rewrite <- app_assoc; simpl. rewrite <- app_assoc. reflexivity.
                            -- split. apply Hx1z. rewrite Hdirv'' in Hdirv'. simpl in Hdirv'. rewrite andb_comm in Hdirv'. simpl in Hdirv'. apply Hdirv'.
                            -- destruct Hdirv'' as [lv'' [x2 Hdirv'']]. exists x1. exists x2. split.
                               ++ apply sublist_breaks_down_list. exists (u :: (rev lu) ++ ancu :: lu''). exists (rev lv'' ++ ancv :: lv ++ [v]).
                                  simpl. destruct Hdirv'' as [Hlv' Hx2z]. rewrite Hlv'. rewrite Hlu''. rewrite reverse_list_append.
                                  simpl. unfold node. f_equal. repeat rewrite <- app_assoc; simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity.
                               ++ split. apply Hx1z. destruct Hdirv'' as [_ Hdirv'']. apply Hdirv''.
                        + unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists z. split.
                          * unfold find_descendants. left. reflexivity.
                          * apply HzZ. }
                    unfold concat in Hconn3. apply d_connected_path_not_d_separated with (l := (rev lu ++ ancu :: lu') ++ z :: rev lv' ++ ancv :: lv) in Hdsep.
                    ** exfalso. apply Hdsep.
                    ** apply Hconn3.
                    ** split. apply concat_paths_still_a_path. split. apply Hpath. apply Hpath'. admit. } }
    unfold find_value in Hv. rewrite HAa in Hv. rewrite HAb in Hv. rewrite Hv. unfold find_value in Hv'. rewrite HAb in Hv'. rewrite HAb' in Hv'. rewrite Hv'.
    reflexivity. }
  { intros Hcond. remember u' as u. remember v' as v. (* show that if NOT d-separated, then there is a contradiction. *)
    destruct (d_separated_bool u v G Z) as [|] eqn:Hsep.
    - reflexivity.
    - apply d_separated_vs_connected in Hsep. destruct Hsep as [l Hp].
      assert (contra: ~(conditionally_independent X G u v Z)).
      { apply path_d_connected_then_not_independent with (p := (u, v, l)).
        - split. apply HG.
          apply paths_start_to_end_correct. split.
          + destruct Hp as [_ [Hp _]]. apply Hp.
          + split.
            * apply path_start_end_refl.
            * destruct Hp as [Hp _]. apply Hp.
        - apply HZ.
        - destruct Hp as [_ [_ Hp]]. apply Hp. }
      contradiction. }
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




