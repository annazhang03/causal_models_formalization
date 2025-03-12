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
Require Import Coq.Logic.FunctionalExtensionality.



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

Lemma node_in_path_cat: forall (u v h w: node) (t: nodes),
  (w =? u) = false
  -> node_in_path w (h, v, t) = node_in_path w (u, v, h :: t).
Proof.
  intros u v h w t H.
  unfold node_in_path. simpl. rewrite H. simpl. destruct (w =? h) as [|] eqn:Hwh.
  - simpl. rewrite eqb_sym in Hwh. rewrite Hwh. rewrite orb_comm. reflexivity.
  - simpl. rewrite eqb_sym in Hwh. rewrite Hwh. reflexivity.
Qed.

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
    (acyclic_path_2 p) <-> acyclic_path ((path_start p) :: (path_int p) ++ [path_end p]) = true. 
Proof.
  intros [[u v] l]. split.
  { generalize dependent v. generalize dependent u. induction l as [| h t IH].
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
        -- destruct H as [_ [_ [_ H]]]. apply split_and_true in H. destruct H as [_ H]. destruct t as [| h0 t0]. apply I. apply H. }
  { generalize dependent v. generalize dependent u. induction l as [| h t IH].
  - intros u v H. simpl. destruct (v =? u) as [|] eqn:Hvu.
    + simpl in H. rewrite Hvu in H. discriminate H.
    + simpl in H. repeat split. intros Huv. rewrite Huv in Hvu. rewrite eqb_refl in Hvu. discriminate Hvu. repeat intros F; apply F. intros F; apply F.
  - intros u v H. simpl in H. destruct (h =? u) as [|] eqn:Hhu.
    + simpl in H. discriminate H.
    + destruct (member u (t ++ [v])) as [|] eqn:Hmem.
      * simpl in H. discriminate H.
      * simpl in H. apply IH in H. simpl. repeat split.
        -- intros Huv. apply member_In_equiv_F in Hmem. apply Hmem. apply membership_append_r. left. symmetry. apply Huv.
        -- intros [Hu | Hu]. rewrite Hu in Hhu. rewrite eqb_refl in Hhu. discriminate Hhu.
           apply member_In_equiv_F in Hmem. apply Hmem. apply membership_append. apply Hu.
        -- simpl in H. intros [Hv | Hv]. destruct H as [H]. apply H. apply Hv. destruct H as [_ [_ [H]]]. apply H. apply Hv.
        -- simpl in H. apply split_and_true. split. rewrite negb_true_iff. apply member_In_equiv_F. apply H.
           destruct t as [| h' t']. simpl. reflexivity. simpl. apply H. }
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

Lemma subpath_still_acyclic_2: forall (w u v: node) (l1 l2 l3: nodes),
  l1 ++ [u] ++ l2 = l3 /\ acyclic_path_2 (w, v, l3)
  -> acyclic_path_2 (w, u, l1).
Proof.
  intros w u v l1 l2 l3. intros [Hl Hcyc].
  destruct l1 as [| h t].
  - simpl in Hl. rewrite <- Hl in Hcyc. simpl. repeat split.
    + intros Hwu. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [Hcyc _]. apply eqb_eq in Hwu.
      rewrite eqb_sym in Hwu. rewrite Hwu in Hcyc. discriminate Hcyc.
    + easy.
    + easy.
  - simpl. repeat split.
    + intros Hwu. apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [Hcyc _].
      rewrite <- Hl in Hcyc. simpl in Hcyc. destruct (h =? w) as [|] eqn:Hhw.
      * discriminate Hcyc.
      * assert (Hmem: member w (t ++ u :: l2) = true). { apply member_In_equiv. apply membership_append_r. rewrite Hwu. left. reflexivity. }
        apply member_In_equiv in Hmem. apply membership_append with (l2 := [v]) in Hmem. apply member_In_equiv in Hmem. rewrite Hmem in Hcyc. discriminate Hcyc.
    + intros [Hw | Hw].
      * unfold acyclic_path_2 in Hcyc. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. rewrite <- Hl. rewrite <- Hw. simpl. left. reflexivity.
      * unfold acyclic_path_2 in Hcyc. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. rewrite <- Hl. simpl. right. apply membership_append. apply Hw.
    + intros [Hu | Hu].
      * apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [_ Hcyc].
        apply acyclic_path_intermediate_nodes with (x := h) in Hcyc. destruct Hcyc as [Hc | Hc].
        -- rewrite <- Hl in Hc. simpl in Hc. rewrite <- Hu in Hc. repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia.
        -- rewrite <- Hl in Hc. simpl in Hc. rewrite <- Hu in Hc. repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. lia.
      * apply acyclic_path_correct_2 in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [_ Hcyc].
        apply acyclic_path_intermediate_nodes with (x := u) in Hcyc. destruct Hcyc as [Hc | Hc].
        -- rewrite <- Hl in Hc. simpl in Hc. destruct (h =? u) as [|] eqn:Hhu.
           ++ repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. apply member_count_at_least_1 in Hu. lia.
           ++ repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. apply member_count_at_least_1 in Hu. lia.
        -- rewrite <- Hl in Hc. simpl in Hc. destruct (h =? u) as [|] eqn:Hhu.
           ++ repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. apply member_count_at_least_1 in Hu. lia.
           ++ repeat rewrite count_app in Hc. simpl in Hc. rewrite eqb_refl in Hc. apply member_count_at_least_1 in Hu. lia.
    + rewrite <- Hl in Hcyc. simpl in Hcyc. apply acyclic_path_intermediate_nodes with (p := h :: t).
      intros x. simpl.
      destruct Hcyc as [_ [_ [_ Hcyc]]]. apply split_and_true in Hcyc. destruct Hcyc as [Hcyc1 Hcyc2].
      destruct (h =? x) as [|] eqn:Hhx.
      * right. f_equal. apply not_member_count_0. apply eqb_eq in Hhx. rewrite <- Hhx.
        destruct (member h t) as [|] eqn:Hmem.
        -- apply member_In_equiv in Hmem. apply membership_append with (l2 := u :: l2) in Hmem. apply member_In_equiv in Hmem. rewrite Hmem in Hcyc1. discriminate Hcyc1.
        -- reflexivity.
      * apply acyclic_path_intermediate_nodes with (x := x) in Hcyc2. destruct Hcyc2 as [Hcyc2 | Hcyc2].
        -- left. rewrite count_app in Hcyc2. lia.
        -- rewrite count_app in Hcyc2. lia.
Qed.

Lemma acyclic_path_cat: forall (u v h: node) (t: nodes),
  acyclic_path_2 (u, v, h :: t)
  -> acyclic_path_2 (h, v, t).
Proof.
  intros u v h t H.
  unfold acyclic_path_2 in *.
  repeat split.
  - destruct H as [_ [_ [H _]]]. intros Hhv. apply H. left. apply Hhv.
  - destruct H as [_ [_ [_ H]]]. intros Hht. simpl in H. apply split_and_true in H. destruct H as [H _].
    apply negb_true_iff in H. apply member_In_equiv_F in H. apply H. apply Hht.
  - destruct H as [_ [_ [H _]]]. intros Hvt. apply H. right. apply Hvt.
  - destruct H as [_ [_ [_ H]]]. simpl in H. apply split_and_true in H. destruct H as [_ H]. destruct t as [| h' t'].
    + apply I.
    + apply H.
Qed.

Lemma acyclic_path_cat_2: forall (u v h: node) (t: nodes),
  acyclic_path_2 (h, v, t)
  -> ~In u (h :: t ++ [v])
  -> acyclic_path_2 (u, v, h :: t).
Proof.
  intros u v h t H1 H2.
  apply acyclic_path_correct_2. simpl. apply split_and_true. split.
  - apply member_In_equiv_F in H2. simpl in H2. rewrite H2. reflexivity.
  - apply acyclic_path_correct_2 in H1. simpl in H1. apply H1.
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


Lemma acyclic_path_count: forall (u v x: node) (l: nodes),
  In x (u :: l ++ [v])
  -> acyclic_path_2 (u, v, l)
  -> count x (u :: l ++ [v]) = 1.
Proof.
  intros u v x l Hmem Hcyc.
  generalize dependent u. induction l as [| h t IH].
  - intros u Hmem Hcyc. simpl in Hmem. destruct Hmem as [Hux | [Hvx | F]].
    + simpl. rewrite Hux. rewrite eqb_refl. f_equal. unfold acyclic_path_2 in Hcyc. destruct Hcyc as [Hcyc _].
      rewrite Hux in Hcyc. apply eqb_neq in Hcyc. rewrite eqb_sym. rewrite Hcyc. reflexivity.
    + simpl. rewrite Hvx. rewrite eqb_refl. unfold acyclic_path_2 in Hcyc. destruct Hcyc as [Hcyc _].
      rewrite Hvx in Hcyc. apply eqb_neq in Hcyc. rewrite Hcyc. reflexivity.
    + exfalso. apply F.
  - intros u Hmem Hcyc. destruct (u =? x) as [|] eqn:Hux.
    + apply eqb_eq in Hux. rewrite Hux in *. simpl. rewrite eqb_refl. f_equal. unfold acyclic_path_2 in Hcyc.
      destruct Hcyc as [Hxv [Hcyc _]]. simpl in Hcyc.
      destruct (h =? x) as [|] eqn:Hhx.
      * exfalso. apply Hcyc. left. apply eqb_eq. apply Hhx.
      * apply not_member_count_0. apply member_In_equiv_F. intros F. apply membership_append_or in F. destruct F as [F | F].
        -- apply Hcyc. right. apply F.
        -- destruct F as [F | F]. apply Hxv. rewrite F. reflexivity. apply F.
    + simpl in Hmem. destruct Hmem as [Hmem | Hmem].
      * rewrite Hmem in Hux. rewrite eqb_refl in Hux. discriminate Hux.
      * simpl. rewrite Hux. apply IH.
        -- apply Hmem.
        -- apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split.
           ++ simpl. reflexivity.
           ++ apply Hcyc.
Qed.

Lemma node_in_subpath_not_acyclic: forall (u h v: node) (t: nodes),
  node_in_path u (h, v, t) = true
  -> acyclic_path_2 (u, v, h :: t)
  -> False.
Proof.
  intros u h v t H1 H2.
  unfold node_in_path in H1. unfold acyclic_path_2 in H2. simpl in H1.
  apply split_orb_true in H1. destruct H1 as [H1 | H1].
  - apply split_orb_true in H1. destruct H1 as [H1 | H1].
    + destruct H2 as [_ [H2 _]]. apply H2. left. apply eqb_eq in H1. rewrite H1. reflexivity.
    + destruct H2 as [H2 _]. apply H2. apply eqb_eq. apply H1.
  - destruct H2 as [_ [H2 _]]. apply H2. right. apply member_In_equiv. apply H1.
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


Theorem is_edge_then_node_in_graph: forall (G: graph) (u v: node),
  is_edge (u, v) G = true \/ is_edge (v, u) G = true
  -> node_in_graph u G = true.
Proof.
  intros G u v [Huv | Hvu].
  - destruct G as [V E]. unfold is_edge in Huv. apply split_and_true in Huv. destruct Huv as [Huv _].
    apply split_and_true in Huv. destruct Huv as [Huv _]. simpl. apply Huv.
  - destruct G as [V E]. unfold is_edge in Hvu. apply split_and_true in Hvu. destruct Hvu as [Huv _].
    apply split_and_true in Huv. destruct Huv as [_ Huv]. simpl. apply Huv.
Qed.

Theorem edge_in_graph_then_is_edge: forall (G: graph) (u v: node),
  G_well_formed G = true
  -> edge_in_graph (u, v) G = true
  -> is_edge (u, v) G = true.
Proof.
  intros G u v HG Huv.
  unfold is_edge.
  assert (Hnode: node_in_graph u G = true /\ node_in_graph v G = true).
  { apply edge_corresponds_to_nodes_in_well_formed. split. apply HG. apply Huv. }
  destruct G as [V E].
  simpl in Huv. rewrite Huv.
  simpl in Hnode. destruct Hnode as [H1 H2]. rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem edge_in_graph_equiv: forall (G: graph) (u v: node),
  G_well_formed G = true
  -> is_edge (u, v) G = edge_in_graph (u, v) G.
Proof.
  intros G u v HG.
  destruct (edge_in_graph (u, v) G) as [|] eqn:Huv.
  - apply edge_in_graph_then_is_edge in Huv. apply Huv. apply HG.
  - unfold is_edge. destruct G as [V E]. simpl in Huv. rewrite Huv. rewrite andb_comm. simpl. reflexivity.
Qed.


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

Theorem subpath_still_path: forall (w u v: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ is_path_in_graph (w, v, l3) G = true
  -> is_path_in_graph (u, v, l2) G = true.
Proof.
  intros w u v l1 l2 l3 G. intros [Hl Hdir].
  generalize dependent l3. generalize dependent w. induction l1 as [| h t IH].
  - intros w l3 Hl Hdir. simpl in Hl. rewrite <- Hl in Hdir. simpl in Hdir. destruct G as [V E]. apply split_and_true in Hdir. destruct Hdir as [_ Hdir].
    apply Hdir.
  - intros w l3 Hl Hdir. specialize IH with (w := h) (l3 := (t ++ [u] ++ l2)). apply IH.
    + reflexivity.
    + simpl in Hl. rewrite <- Hl in Hdir. simpl in Hdir. destruct G as [V E]. apply split_and_true in Hdir. destruct Hdir as [_ Hdir]. apply Hdir.
Qed.

Theorem subpath_still_directed_2: forall (w u v: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ is_directed_path_in_graph (w, v, l3) G = true
  -> is_directed_path_in_graph (w, u, l1) G = true.
Proof.
  intros w u v l1 l2 l3 G. intros [Hl Hdir].
  generalize dependent l3. generalize dependent w. induction l1 as [| h t IH].
  - intros w l3 Hl Hdir. simpl in Hl. rewrite <- Hl in Hdir. simpl in Hdir. apply split_and_true in Hdir. destruct Hdir as [Hdir _].
    simpl. rewrite Hdir. reflexivity.
  - intros w l3 Hl Hdir. specialize IH with (w := h) (l3 := (t ++ [u] ++ l2)). simpl.
    rewrite <- Hl in Hdir. simpl in Hdir. apply split_and_true in Hdir. destruct Hdir as [Hdir1 Hdir2]. rewrite Hdir1. simpl. apply IH.
    + reflexivity.
    + apply Hdir2.
Qed.

Theorem subpath_still_path_2: forall (w u v: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ is_path_in_graph (w, v, l3) G = true
  -> is_path_in_graph (w, u, l1) G = true.
Proof.
  intros w u v l1 l2 l3 G. intros [Hl Hdir].
  generalize dependent l3. generalize dependent w. induction l1 as [| h t IH].
  - intros w l3 Hl Hdir. simpl in Hl. rewrite <- Hl in Hdir. simpl in Hdir. destruct G as [V E]. apply split_and_true in Hdir. destruct Hdir as [Hdir _].
    simpl. simpl in Hdir. rewrite Hdir. reflexivity.
  - intros w l3 Hl Hdir. specialize IH with (w := h) (l3 := (t ++ [u] ++ l2)). simpl.
    rewrite <- Hl in Hdir. simpl in Hdir. destruct G as [V E]. apply split_and_true in Hdir. destruct Hdir as [Hdir1 Hdir2]. rewrite Hdir1. simpl. apply IH.
    + reflexivity.
    + apply Hdir2.
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
(* TODO think this should be is_directed_path_in_graph... *)

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
(* TODO add the condition that each edge appears only once in G_well_formed *)
Admitted.

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

Lemma get_assigned_In: forall X (A: assignments X) (u: node) (x: X),
  get_assigned_value A u = Some x -> In (u, x) A.
Proof.
  intros X A u x H. induction A as [| h t IH].
  - simpl in H. discriminate H.
  - simpl. simpl in H. destruct (fst h =? u) as [|] eqn:Hu.
    + left. destruct h as [h1 h2]. simpl in Hu. apply eqb_eq in Hu. rewrite Hu. simpl in H. inversion H. reflexivity.
    + right. apply IH. apply H.
Qed.

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

Lemma is_assignment_for_app_r: forall X (A B: assignments X) (V: nodes),
  is_assignment_for B V = true -> is_assignment_for (A ++ B) V = true.
Proof.
  intros X A B V H. unfold is_assignment_for in H. unfold is_assignment_for.
  apply forallb_true_iff_mem. intros x Hmem.
  apply forallb_true with (x := x) in H.
  - apply is_assigned_app2. apply H.
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

Definition remove_assignment_for {X: Type} (A: assignments X) (v: node): assignments X :=
  filter (fun x => negb (fst x =? v)) A.

Lemma exact_assignment_append {X: Type}: forall (A: assignments X) (Z: nodes) (v: node),
  is_exact_assignment_for A (Z ++ [v])
  -> ~(In v Z)
  -> is_exact_assignment_for (remove_assignment_for A v) Z.
Proof.
  intros A Z v H. unfold is_exact_assignment_for in H. destruct H as [HA Hu].
  unfold is_exact_assignment_for. split.
  - unfold is_assignment_for. apply forallb_true_iff_mem. intros x HxZ. unfold remove_assignment_for.
    unfold is_assignment_for in HA. apply forallb_true_iff_mem with (x := x) in HA.
    + apply assigned_is_true in HA. destruct HA as [a HA]. apply get_assigned_In in HA.
      apply is_assigned_membership. exists a. apply filter_true. split.
      * apply HA.
      * simpl. destruct (x =? v) as [|] eqn:Hxv.
        -- exfalso. apply H. apply eqb_eq in Hxv. rewrite Hxv in HxZ. apply HxZ.
        -- reflexivity.
    + apply membership_append. apply HxZ.
  - intros u HuZ.
    unfold remove_assignment_for. destruct (u =? v) as [|] eqn:Huv.
    + destruct (is_assigned (filter (fun x : nat * X => negb (fst x =? v)) A) u) as [|] eqn:Ha.
      * apply is_assigned_membership in Ha. destruct Ha as [a Ha]. apply filter_true in Ha. destruct Ha as [_ Ha]. simpl in Ha. rewrite Huv in Ha. discriminate Ha.
      * reflexivity.
    + assert (is_assigned A u = false). { apply Hu. destruct (member u (Z ++ [v])) as [|] eqn:Hmem.
      - apply member_In_equiv in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
        + apply member_In_equiv in Hmem. rewrite Hmem in HuZ. discriminate HuZ.
        + destruct Hmem as [Hmem | Hmem].
          * rewrite Hmem in Huv. rewrite eqb_refl in Huv. discriminate Huv.
          * exfalso. apply Hmem.
      - reflexivity. }
      destruct (is_assigned (filter (fun x : nat * X => negb (fst x =? v)) A) u) as [|] eqn:Ha.
      * apply is_assigned_membership in Ha. destruct Ha as [a Ha]. apply filter_true in Ha. destruct Ha as [Ha _].
        assert (is_assigned A u = true). { apply is_assigned_membership. exists a. apply Ha. } rewrite H1 in H0. discriminate H0.
      * reflexivity.
Qed.

Lemma remove_assignment_None {X: Type}: forall (A: assignments X) (u: node),
  get_assigned_value (remove_assignment_for A u) u = None.
Proof.
  intros A u.
  induction A as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (fst h =? u) as [|] eqn:Hhu.
    + unfold node in *. rewrite Hhu. simpl. apply IH.
    + unfold node in *. rewrite Hhu. simpl. unfold node in *. rewrite Hhu. apply IH.
Qed.

Lemma remove_assignment_preserves_other_nodes {X: Type}: forall (A: assignments X) (u x: node),
  u =? x = false
  -> get_assigned_value (remove_assignment_for A u) x = get_assigned_value A x.
Proof.
  intros A u x H.
  induction A as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (fst h =? u) as [|] eqn:Hhu.
    + unfold node in *. rewrite Hhu. simpl. destruct (fst h =? x) as [|] eqn:Hhx.
      * apply eqb_eq in Hhu. apply eqb_eq in Hhx. unfold node in *. rewrite Hhx in Hhu. rewrite Hhu in H. rewrite eqb_refl in H. discriminate H.
      * unfold node in *. rewrite Hhx. apply IH.
    + unfold node in *. rewrite Hhu. simpl. destruct (fst h =? x) as [|] eqn:Hhx.
      * unfold node in *. rewrite Hhx. reflexivity.
      * unfold node in *. rewrite Hhx. apply IH.
Qed.

Lemma remove_assignment_is_assignment_cat {X: Type}: forall (A: assignments X) (h u: node) (A': nodes) (c: X),
  is_assignment_for A (u :: A') = true
  -> ~(In u A')
  -> is_assignment_for ((h, c) :: remove_assignment_for A u) (h :: A') = true.
Proof.
  intros A h u A' c HA Hmem.
  simpl. rewrite eqb_refl. simpl. simpl in HA. apply split_and_true in HA. destruct HA as [_ HA].
  induction A' as [| ha ta IH].
  - simpl. reflexivity.
  - simpl. destruct (ha =? h) as [|] eqn:Hhah.
    + simpl. apply IH.
      * simpl in HA. apply split_and_true in HA. apply HA.
      * intros F. apply Hmem. right. apply F.
    + simpl. apply split_and_true. split.
      * apply assigned_is_true. rewrite remove_assignment_preserves_other_nodes.
        -- apply assigned_is_true. simpl in HA. apply split_and_true in HA. apply HA.
        -- destruct (u =? ha) as [|] eqn:Huha. exfalso. apply Hmem. left. apply eqb_eq in Huha. symmetry. apply Huha. reflexivity.
      * apply IH.
        -- simpl in HA. apply split_and_true in HA. apply HA.
        -- intros F. apply Hmem. right. apply F.
Qed.

Lemma remove_assignment_non_member_cat {X: Type}: forall (A: assignments X) (h u: node) (A': nodes) (c: X),
  (forall u0 : node, member u0 (u :: A') = false -> is_assigned A u0 = false)
  -> ~ In u A'
  -> forall u0 : node,
      member u0 (h :: A') = false ->
      is_assigned ((h, c) :: remove_assignment_for A u) u0 = false.
Proof.
  intros A h u A' c HA Hmem.
  intros v Hv. simpl in Hv. destruct (h =? v) as [|] eqn:Hhv.
  - discriminate Hv.
  - simpl. rewrite eqb_sym in Hhv. rewrite Hhv. simpl.
    destruct (v =? u) as [|] eqn:Hvu.
    + apply assigned_is_false. apply eqb_eq in Hvu. rewrite Hvu. apply remove_assignment_None.
    + apply assigned_is_false. rewrite remove_assignment_preserves_other_nodes.
      * apply assigned_is_false. apply HA. simpl. rewrite eqb_sym in Hvu. rewrite Hvu. apply Hv.
      * rewrite eqb_sym. apply Hvu.
Qed.


Lemma remove_assignment_exact_cat {X: Type}: forall (A: assignments X) (h u: node) (A': nodes) (c: X),
  is_exact_assignment_for A (u :: A')
  -> ~(In u A')
  -> is_exact_assignment_for ((h, c) :: remove_assignment_for A u) (h :: A').
Proof.
  intros A h u A' c H Hmem.
  unfold is_exact_assignment_for in *. destruct H as [H1 H2]. split.
  - apply remove_assignment_is_assignment_cat. apply H1. apply Hmem.
  - apply remove_assignment_non_member_cat. apply H2. apply Hmem.
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

Fixpoint get_values_from_topo_sort_2 {X: Type} (ts: nodes) (G: graph) (g: graphfun) (U: assignments X)
                                     (A_eval: assignments X) : option (assignments X) :=
  match ts with
  | [] => Some []
  | u :: ts' => match (get_value_of_node u G g U [] A_eval) with
                | Some x => match (get_values_from_topo_sort_2 ts' G g U (add_assignment A_eval u x)) with
                            | Some r => Some ((u, x) :: r)
                            | None => None
                            end
                | None => None
                end
  end.

Lemma get_values_ts_2_preserves_length {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U Ae V: assignments X),
  get_values_from_topo_sort_2 ts G g U Ae = Some V
  -> length V = length ts.
Proof.
  intros ts G g U Ae V HV.
  generalize dependent Ae. generalize dependent ts. induction V as [| h t IH].
  - intros ts Ae HV. destruct ts as [| hts tts].
    + reflexivity.
    + simpl in HV. destruct (get_value_of_node hts G g U [] Ae) as [x|] eqn:Hx.
      * destruct (get_values_from_topo_sort_2 tts G g U (add_assignment Ae hts x)) as [r|] eqn:Hr.
        -- inversion HV.
        -- discriminate HV.
      * discriminate HV.
  - intros ts Ae HV. destruct ts as [| hts tts].
    + simpl in HV. inversion HV.
    + simpl in HV. destruct (get_value_of_node hts G g U [] Ae) as [x|].
      * destruct (get_values_from_topo_sort_2 tts G g U (add_assignment Ae hts x)) as [r|] eqn:Hr.
        -- inversion HV. simpl. f_equal.
           specialize IH with (ts := tts) (Ae := (add_assignment Ae hts x)). apply IH. rewrite <- H1. apply Hr.
        -- discriminate HV.
      * discriminate HV.
Qed.

Lemma get_values_ts_2_preserves_index {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U Ae: assignments X) (u: node),
  forall (i: nat) (V: assignments X), nth_error ts i = Some u
  -> get_values_from_topo_sort_2 ts G g U Ae = Some V
  -> exists (x: X), nth_error V i = Some (u, x).
Proof.
  intros ts G g U Ae u i V Hi HV.
  generalize dependent ts. generalize dependent V. generalize dependent Ae. induction i as [| i' IH].
  - intros Ae V ts Hi HV. destruct ts as [| h t].
    + simpl in Hi. discriminate Hi.
    + simpl in Hi. inversion Hi. rewrite H0 in *. simpl in HV.
      destruct (get_value_of_node u G g U [] Ae) as [x|].
      * destruct (get_values_from_topo_sort_2 t G g U (add_assignment Ae u x)) as [r|].
        -- inversion HV. exists x. simpl. reflexivity.
        -- discriminate HV.
      * discriminate HV.
  - intros Ae V ts Hi HV. destruct ts as [| h t].
    + simpl in Hi. discriminate Hi.
    + simpl in Hi. simpl in HV. destruct (get_value_of_node h G g U [] Ae) as [xh|].
      * destruct (get_values_from_topo_sort_2 t G g U (add_assignment Ae h xh)) as [r|] eqn:Hr.
        -- specialize IH with (V := r) (ts := t) (Ae := add_assignment Ae h xh).
           assert (Hind: exists x : X, nth_error r i' = Some (u, x)).
           { apply IH. apply Hi. apply Hr. }
           destruct Hind as [x Hux]. exists x.
           inversion HV. simpl. apply Hux.
        -- discriminate HV.
      * discriminate HV.
Qed.

Lemma get_values_ts_2_preserves_index_rev {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U Ae: assignments X) (u: node),
  forall (i: nat) (V: assignments X) (x: X),
  get_values_from_topo_sort_2 ts G g U Ae = Some V /\ nth_error V i = Some (u, x)
  -> nth_error ts i = Some u.
Proof.
  intros ts G g U Ae u i V x [HV Hi].
  generalize dependent ts. generalize dependent V. generalize dependent Ae. induction i as [| i' IH].
  - intros Ae V Hi ts HV. destruct V as [| h t].
    + simpl in Hi. discriminate Hi.
    + simpl in Hi. inversion Hi. rewrite H0 in *. destruct ts as [| hts tts].
      * simpl in HV. inversion HV.
      * simpl in HV. destruct (get_value_of_node hts G g U [] Ae) as [htsx|].
        -- destruct (get_values_from_topo_sort_2 tts G g U (add_assignment Ae hts htsx)) as [r|].
           ++ inversion HV. simpl. reflexivity.
           ++ discriminate HV.
        -- discriminate HV.
  - intros Ae V Hi ts HV. destruct V as [| h t].
    + simpl in Hi. discriminate Hi.
    + simpl in Hi. destruct ts as [| hts tts].
      * simpl in HV. inversion HV.
      * simpl in HV. destruct (get_value_of_node hts G g U [] Ae) as [htsx|].
        -- destruct (get_values_from_topo_sort_2 tts G g U (add_assignment Ae hts htsx)) as [r|] eqn:Hr.
           ++ inversion HV. simpl. specialize IH with (ts := tts) (Ae := add_assignment Ae hts htsx) (V := r).
              apply IH. rewrite H1. apply Hi. easy.
           ++ discriminate HV.
        -- discriminate HV.
Qed.

Fixpoint first_n {X: Type} (l: list X) (n: nat): option (list X) :=
  match n with
  | 0 => Some []
  | S n' => match l with
            | [] => None
            | h :: t => match (first_n t n') with
                        | Some r => Some (h :: r)
                        | None => None
                        end
            end
  end.

Lemma first_n_exists {X: Type}: forall (V: assignments X) (i: nat),
  i < length V
  -> exists V' : assignments X, first_n V i = Some V'.
Proof.
  intros V i H.
  generalize dependent i. induction V as [| h t IH].
  - intros i H. destruct i as [| i'].
    + simpl in H. lia.
    + simpl in H. lia.
  - intros i H. destruct i as [| i'].
    + simpl. exists []. reflexivity.
    + assert (Hind: exists V' : assignments X, first_n t i' = Some V').
      { apply IH. simpl in H. lia. }
      destruct Hind as [V' Hind]. exists (h :: V'). simpl. rewrite Hind. reflexivity.
Qed.

Lemma get_values_ts_2_get_value_node {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U Ae: assignments X) (u: node),
  forall (i: nat) (V: assignments X), nth_error ts i = Some u
  -> get_values_from_topo_sort_2 ts G g U Ae = Some V
  -> exists (x: X) (V': assignments X),
       get_value_of_node u G g U [] (Ae ++ V') = Some x
       /\ first_n V i = Some V'
       /\ nth_error V i = Some (u, x).
Proof.
  intros ts G g U Ae u i V Hi HV.
  generalize dependent ts. generalize dependent V. generalize dependent Ae. induction i as [| i' IH].
  - intros Ae V ts Hi HV. destruct ts as [| h t].
    + simpl in Hi. discriminate Hi.
    + simpl in Hi. inversion Hi. rewrite H0 in *. simpl in HV.
      destruct (get_value_of_node u G g U [] Ae) as [x|] eqn:Hx.
      * destruct (get_values_from_topo_sort_2 t G g U (add_assignment Ae u x)) as [r|].
        -- inversion HV. exists x. exists []. repeat split. rewrite append_identity. apply Hx.
        -- discriminate HV.
      * discriminate HV.
  - intros Ae V ts Hi HV. destruct ts as [| h t].
    + simpl in Hi. discriminate Hi.
    + simpl in Hi. simpl in HV. destruct (get_value_of_node h G g U [] Ae) as [xh|] eqn:Hxh.
      * destruct (get_values_from_topo_sort_2 t G g U (add_assignment Ae h xh)) as [r|] eqn:Hr.
        -- specialize IH with (V := r) (ts := t) (Ae := add_assignment Ae h xh).
           assert (Hind: exists (x : X) (V' : assignments X),
                         get_value_of_node u G g U [] (add_assignment Ae h xh ++ V') = Some x /\
                         first_n r i' = Some V' /\ nth_error r i' = Some (u, x)).
           { apply IH. apply Hi. apply Hr. }
           destruct Hind as [x [V' [Hx [Hi' Hux]]]].
           exists x. exists ((h, xh) :: V'). repeat split.
           ++ unfold add_assignment in Hx. rewrite append_vs_concat_X in Hx. apply Hx.
           ++ inversion HV. simpl. rewrite Hi'. reflexivity.
           ++ inversion HV. simpl. apply Hux.
        -- discriminate HV.
      * discriminate HV.
Qed.

Lemma get_values_from_topo_sort_equiv_helper {X: Type}: forall (G: graph) (g: graphfun) (tsp tss: nodes) (U A_eval V1: assignments X),
  topological_sort G = Some (tsp ++ tss)
  -> get_values_from_topo_sort (tss) G g U [] A_eval = Some V1
  -> exists (V2: assignments X), get_values_from_topo_sort_2 (tss) G g U A_eval = Some V2
  /\ V1 = A_eval ++ V2.
Proof.
  intros G g tsp tss U Ae V1 Hts HV1.
  generalize dependent tsp. generalize dependent Ae. induction tss as [| h t IH].
  - intros Ae HV1 tsp Hts. simpl in HV1. exists []. simpl. split. reflexivity. inversion HV1. symmetry. apply append_identity.
  - intros Ae HV1 tsp Hts. simpl in HV1. simpl.
    destruct (get_value_of_node h G g U [] Ae) as [x|] eqn:Hh.
    + specialize IH with (Ae := add_assignment Ae h x) (tsp := tsp ++ [h]).
      assert (Hind: exists V2 : assignments X,
         get_values_from_topo_sort_2 t G g U (add_assignment Ae h x) = Some V2 /\
         V1 = add_assignment Ae h x ++ V2).
      { apply IH.
        - apply HV1.
        - rewrite append_vs_concat_X. apply Hts. }
      destruct Hind as [r [Hr Hind]].
      exists ((h, x) :: r). rewrite Hr. split. reflexivity.
      unfold add_assignment in Hind. rewrite append_vs_concat_X in Hind. apply Hind.
    + discriminate HV1.
Qed.


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

Theorem get_values_from_topo_sort_equiv {X: Type}: forall (G: graph) (g: graphfun) (ts: nodes) (U: assignments X),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true ->
  topological_sort G = Some ts
  -> get_values G g U [] = get_values_from_topo_sort_2 ts G g U [].
Proof.
  intros G g ts U HG HU Hts.
  assert (HV: exists (V: assignments X), get_values G g U [] = Some V).
  { apply get_values_existence. easy. easy. }
  destruct HV as [V HV].
  assert (Hlem: exists (V2: assignments X), get_values_from_topo_sort_2 ts G g U [] = Some V2 /\ V = [] ++ V2).
  { apply get_values_from_topo_sort_equiv_helper with (tsp := []).
    - simpl. apply Hts.
    - unfold get_values in HV. rewrite Hts in HV. apply HV. }
  destruct Hlem as [V2 [HV2 HV']]. rewrite HV. simpl in HV'. rewrite HV2. f_equal. apply HV'.
Qed.


Definition find_value {X: Type} (G: graph) (g: graphfun) (u: node) (U A: assignments X): option X :=
  match (get_values G g U A) with
  | Some values => get_assigned_value values u
  | None => None
  end.

Lemma get_values_preserves_index {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U V: assignments X) (u: node) (i: nat),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true
  -> topological_sort G = Some ts /\ nth_error ts i = Some u
  -> get_values G g U [] = Some V
  -> exists (x: X), nth_error V i = Some (u, x).
Proof.
  intros ts G g U V u i. intros HG HU [Hts Hi] HV.
  assert (Hgvts: get_values G g U [] = get_values_from_topo_sort_2 ts G g U []).
  { apply get_values_from_topo_sort_equiv. easy. easy. easy. }
  rewrite Hgvts in HV.
  assert (HVi: exists (x: X) (V': assignments X),
               get_value_of_node u G g U [] ([] ++ V') = Some x
               /\ first_n V i = Some V'
               /\ nth_error V i = Some (u, x)).
  { apply get_values_ts_2_get_value_node with (ts := ts).
    - apply Hi.
    - apply HV. }
  destruct HVi as [x [V' [HV' [Hi' Hux]]]].
  exists x. apply Hux.
Qed.

Lemma filter_preserves_relative_index {X: Type}: forall (test: (node * X) -> bool) (V: assignments X) (h: node * X) (i: nat),
  nth_error (filter test V) i = Some h -> exists (j: nat), nth_error V j = Some h /\ j >= i.
Proof.
  intros test V h i. intros Hi.
  generalize dependent i. induction V as [| hv tv IH].
  - intros i Hi. simpl in Hi. destruct i as [| i']. simpl in Hi. discriminate Hi. simpl in Hi. discriminate Hi.
  - intros i Hi. simpl in Hi. destruct (test hv) as [|] eqn:Hhv.
    + destruct i as [| i'].
      * simpl in Hi. exists 0. simpl. split. apply Hi. lia.
      * simpl in Hi. apply IH in Hi. destruct Hi as [j [Hj Hji]]. exists (S j).
        split.
        -- simpl. apply Hj.
        -- lia.
    + apply IH in Hi. destruct Hi as [j [Hj Hji]]. exists (S j). split.
      * simpl. apply Hj.
      * lia.
Qed.

Lemma filter_preserves_relative_index_2 {X: Type}: forall (test: (node * X) -> bool) (V t': assignments X) (h h': node * X),
  filter test V = h :: h' :: t' -> exists (i j: nat), nth_error V i = Some h /\ nth_error V j = Some h' /\ i =? j = false.
Proof.
  intros test V t' h h'. intros Hf.
  generalize dependent h. generalize dependent h'. generalize dependent t'. induction V as [| hv tv IH].
  - intros t' h' h Hf. simpl in Hf. discriminate Hf.
  - intros t' h' h Hf. simpl in Hf. destruct (test hv) as [|] eqn:Htest.
    + inversion Hf. exists 0.
      destruct t' as [| ht tt].
      * assert (In h' (filter test tv)). { rewrite H1. left. reflexivity. }
        apply In_nth_error in H. destruct H as [j Hj]. apply filter_preserves_relative_index in Hj. destruct Hj as [j' [Hj' Hjj]].
        exists (S j'). repeat split. simpl. apply Hj'.
      * specialize IH with (t' :=  tt) (h' := ht) (h := h'). apply IH in H1.
        destruct H1 as [j [k [Hj [Hk Hjk]]]].
        exists (S j). repeat split. simpl. apply Hj.
    + apply IH in Hf. destruct Hf as [i [j [Hi [Hj Hij]]]]. exists (S i). exists (S j). repeat split.
      * simpl. apply Hi.
      * simpl. apply Hj.
      * destruct (S i =? S j) as [|] eqn:HSij.
        -- apply eqb_eq in HSij. inversion HSij. rewrite H0 in Hij. rewrite eqb_refl in Hij. discriminate Hij.
        -- reflexivity.
Qed.

Lemma nth_error_count: forall (l: list nat) (u: nat) (j k: nat),
  nth_error l j = Some u /\ nth_error l k = Some u
  -> j =? k = false
  -> count u l > 1.
Proof.
  intros l u j k [Hj Hk] Hjk.
  generalize dependent j. generalize dependent k. induction l as [| h t IH].
  - intros k Hk j Hj Hjk. destruct j as [| j']. simpl in Hj. discriminate Hj. simpl in Hj. discriminate Hj.
  - intros k Hk j Hj Hjk. destruct j as [| j'].
    + simpl in Hj. inversion Hj. simpl. rewrite eqb_refl.
      destruct k as [| k']. rewrite eqb_refl in Hjk. discriminate Hjk.
      simpl in Hk. apply nth_error_In in Hk. apply member_count_at_least_1 in Hk. lia.
    + simpl in Hj. destruct k as [| k'].
      * simpl in Hk. inversion Hk. simpl. rewrite eqb_refl.
        apply nth_error_In in Hj. apply member_count_at_least_1 in Hj. lia.
      * simpl in Hk. assert (Hc: count u t > 1).
        { apply IH with (k := k') (j := j'). easy. easy. destruct (j' =? k') as [|] eqn:F.
          - apply eqb_eq in F. rewrite F in Hjk. rewrite eqb_refl in Hjk. discriminate Hjk.
          - reflexivity. }
        simpl. destruct (h =? u) as [|]. lia. lia.
Qed.

Lemma nth_error_get_assigned_value {X: Type}: forall (V: assignments X) (u: node) (x: X) (i: nat),
  nth_error V i = Some (u, x) /\ length (filter (fun x : nat * X => fst x =? u) V) = 1
  -> get_assigned_value V u = Some x.
Proof.
  intros V u x i. intros [Hi Hl].
  generalize dependent i. induction V as [| h t IH].
  - intros i Hi. destruct i as [| i']. simpl in Hi. discriminate Hi. simpl in Hi. discriminate Hi.
  - intros i Hi. destruct i as [| i']. 
    + simpl in Hi. inversion Hi. simpl. rewrite eqb_refl. reflexivity.
    + simpl in Hi. simpl in Hl. destruct (fst h =? u) as [|] eqn:Hhu.
      * unfold node in *. rewrite Hhu in Hl. simpl in Hl. inversion Hl.
        assert (F: In (u, x) (filter (fun x : nat * X => fst x =? u) t)).
        { apply filter_true. split.
          - apply nth_error_In in Hi. apply Hi.
          - simpl. apply eqb_refl. }
        destruct (filter (fun x : nat * X => fst x =? u) t) as [| hf tf]. exfalso. apply F. simpl in H0. lia.
      * unfold node in *. rewrite Hhu in Hl. simpl. unfold node in *. rewrite Hhu. apply IH with (i := i').
        -- apply Hl.
        -- apply Hi.
Qed.

Lemma length_filter_1 {X: Type}: forall (u: node) (U V: assignments X) (i: nat) (x: X) (ts: nodes) (G: graph) (g: graphfun),
  G_well_formed G = true /\ topological_sort G = Some ts
  -> nth_error V i = Some (u, x)
  -> get_values_from_topo_sort_2 ts G g U [] = Some V
  -> length (filter (fun x => fst x =? u) V) = 1.
Proof.
  intros u U V i x ts G g [HG Hts] Hx Hgvts.
  destruct (length (filter (fun x0 : nat * X => fst x0 =? u) V)) as [|l] eqn:Hl.
  - apply nth_error_In in Hx.
    assert (Hfilt: In (u, x) (filter (fun x0 : nat * X => fst x0 =? u) V)).
    { apply filter_true. split. apply Hx. simpl. apply eqb_refl. }
    destruct (filter (fun x0 : nat * X => fst x0 =? u) V) as [| h t].
    + exfalso. apply Hfilt.
    + simpl in Hl. lia.
  - destruct l as [|l'] eqn:Hl'.
    + reflexivity.
    + destruct (filter (fun x0 : nat * X => fst x0 =? u) V) as [| h t] eqn:Hfilt.
      * simpl in Hl. lia.
      * simpl in Hl. inversion Hl. destruct t as [|h' t'] eqn:Ht.
        -- simpl in H0. lia.
        -- apply filter_preserves_relative_index_2 in Hfilt as Hfilt'. destruct Hfilt' as [j [k [Hj [Hk Hjk]]]].
           simpl in H0. inversion H0.
           assert (Hh: In h V /\ fst h =? u = true).
           { assert (In h (filter (fun x0 : nat * X => fst x0 =? u) V)). { rewrite Hfilt. left. reflexivity. }
             apply filter_true in H. apply H. }
           assert (Hh': In h' V /\ fst h' =? u = true).
           { assert (In h' (filter (fun x0 : nat * X => fst x0 =? u) V)). { rewrite Hfilt. right. left. reflexivity. }
             apply filter_true in H. apply H. }
           destruct Hh as [HhV Hh]. destruct h as [h1 h2]. destruct h' as [h1' h2'].
           simpl in Hh. apply eqb_eq in Hh. rewrite Hh in *. clear Hh. destruct Hh' as [HhV' Hh].
           simpl in Hh. apply eqb_eq in Hh. rewrite Hh in *. clear Hh.
           assert (Hhts: nth_error ts j = Some u).
           { apply get_values_ts_2_preserves_index_rev with (G := G) (g := g) (Ae := []) (U := U) (V := V) (x := h2).
             split. apply Hgvts. apply Hj. }
           assert (Hhts': nth_error ts k = Some u).
           { apply get_values_ts_2_preserves_index_rev with (G := G) (g := g) (Ae := []) (U := U) (V := V) (x := h2').
             split. apply Hgvts. apply Hk. }
           assert (Hc: count u ts = 1).
           { apply topo_sort_contains_nodes_exactly_once with (G := G). easy.
             apply topo_sort_contains_nodes with (u := u) in Hts. apply Hts. apply nth_error_In with (n := j). apply Hhts. }
           assert (Hc': count u ts > 1). { apply nth_error_count with (j := j) (k := k). easy. easy. }
           lia.
Qed.

Lemma find_value_preserves_index {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U V: assignments X) (u: node) (i: nat),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true
  -> topological_sort G = Some ts /\ nth_error ts i = Some u
  -> get_values G g U [] = Some V
  -> exists (x: X), nth_error V i = Some (u, x) /\ find_value G g u U [] = Some x.
Proof.
  intros ts G g U V u i. intros HG HU [Hts Hi] HV.
  assert (Hx: exists (x: X), nth_error V i = Some (u, x)).
  { apply get_values_preserves_index with (ts := ts) (G := G) (g := g) (U := U) (u := u). easy. easy. easy. easy. }
  destruct Hx as [x Hx]. exists x. split. easy.
  unfold find_value. rewrite HV.

  assert (Hgvts: get_values_from_topo_sort_2 ts G g U [] = Some V).
  { symmetry. rewrite <- HV. apply get_values_from_topo_sort_equiv. easy. easy. easy. }

  assert (Hc: length (filter (fun x => fst x =? u) V) = 1).
  { apply length_filter_1 with (U := U) (ts := ts) (i := i) (x := x) (G := G) (g := g). easy. apply Hx. apply Hgvts. }
  apply nth_error_get_assigned_value with (i := i). easy.
Qed.

Lemma first_n_preserves_index {X: Type}: forall (V V': assignments X) (i j: nat) (p: node) (x: X),
  first_n V i = Some V'
  -> nth_error V j = Some (p, x)
  -> j < i
  -> nth_error V' j = Some (p, x).
Proof.
  intros V V' i j p x. intros HV' Hj Hji.
  generalize dependent V. generalize dependent j. generalize dependent V'. induction i as [| i' IH].
  - lia.
  - intros V' j Hji V HV' Hj. destruct V as [| h t].
    + simpl in HV'. discriminate HV'.
    + simpl in HV'. destruct (first_n t i') as [r|] eqn:Hr.
      * destruct j as [| j'].
        -- inversion HV'. simpl. simpl in Hj. apply Hj.
        -- specialize IH with (j := j') (V := t) (V' := r). inversion HV'. simpl. apply IH.
           ++ lia.
           ++ apply Hr.
           ++ simpl in Hj. apply Hj.
      * discriminate HV'.
Qed.

Lemma first_n_filter_length {X: Type}: forall (V V': assignments X) (test: node * X -> bool) (i: nat),
  first_n V i = Some V'
  -> length (filter test V) >= length (filter test V').
Proof.
  intros V V' test i. intros Hi.
  generalize dependent V'. generalize dependent i. induction V as [| h t IH].
  - intros i V' Hi. simpl in Hi. destruct i as [|i'].
    + inversion Hi. simpl. lia.
    + discriminate Hi.
  - intros i V' Hi. simpl. destruct (test h) as [|] eqn:Htest.
    + simpl in Hi. destruct i as [| i'].
      * inversion Hi. simpl. lia.
      * destruct (first_n t i') as [r|] eqn:Hr.
        -- specialize IH with (i := i') (V' := r). apply IH in Hr. inversion Hi. simpl. rewrite Htest. simpl. lia.
        -- discriminate Hi.
    + simpl in Hi. destruct i as [| i'].
      * inversion Hi. simpl. lia.
      * destruct (first_n t i') as [r|] eqn:Hr.
        -- inversion Hi. simpl. rewrite Htest. apply IH with (i := i') (V' := r). apply Hr.
        -- discriminate Hi.
Qed.

Lemma find_value_parent_first_n {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U V V': assignments X) (u: node) (i: nat),
  G_well_formed G = true /\ contains_cycle G = false
  -> is_assignment_for U (nodes_in_graph G) = true
  -> topological_sort G = Some ts /\ nth_error ts i = Some u
  -> get_values_from_topo_sort_2 ts G g U [] = Some V
  -> first_n V i = Some V'
  -> forall (p: node), In p (find_parents u G)
     -> find_value G g p U [] = get_assigned_value V' p.
Proof.
  intros ts G g U V V' u i.
  intros HG HU [Hts Hi] HV HV' p Hp.
  assert (Hj: exists (j: nat), nth_error ts j = Some p /\ j < i).
  { assert (Hpar: exists (j i: nat), Some j = index ts p /\ Some i = index ts u /\ j < i).
    { apply topo_sort_parents with (G := G). easy. easy. }
    destruct Hpar as [j [i' [Hj [Hi' Hji]]]].
    exists j. split.
    - apply index_correct. apply Hj.
    - apply index_correct_appears_once in Hi.
      + rewrite <- Hi in Hi'. inversion Hi'. rewrite <- H0. apply Hji.
      + apply topo_sort_contains_nodes_exactly_once with (G := G). easy. apply topo_sort_contains_nodes with (u := u) in Hts.
        apply Hts. apply index_exists. exists i'. apply Hi'. }
  destruct Hj as [j Hj].
  assert (Hlem: exists (x: X), nth_error V j = Some (p, x) /\ find_value G g p U [] = Some x).
  { apply find_value_preserves_index with (ts := ts). easy. easy. easy. 
    rewrite <- HV. apply get_values_from_topo_sort_equiv. easy. easy. easy. }
  destruct Hlem as [x [Hpx Hx]].
  rewrite Hx. symmetry.
  assert (Hc: length (filter (fun x => fst x =? p) V) = 1).
  { apply length_filter_1 with (U := U) (i := j) (x := x) (G := G) (g := g) (ts := ts). easy. apply Hpx. apply HV. }
  assert (Hj': nth_error V' j = Some (p, x)).
  { apply first_n_preserves_index with (V := V) (i := i). apply HV'. apply Hpx. apply Hj. }
  apply nth_error_get_assigned_value with (i := j). split.
  - apply Hj'.
  - assert (Hgeq1: length (filter (fun x0 : nat * X => fst x0 =? p) V') >= 1).
    { assert (Hmem: In (p, x) V'). { apply nth_error_In with (n := j). apply Hj'. }
      assert (Hmem': In (p, x) (filter (fun x0 : nat * X => fst x0 =? p) V')).
      { apply filter_true. split. apply Hmem. simpl. apply eqb_refl. }
      destruct (filter (fun x0 : nat * X => fst x0 =? p) V') as [| h t] eqn: Hl.
      - exfalso. apply Hmem'.
      - simpl. lia. }
    assert (Hleq1: 1 >= length (filter (fun x0 : nat * X => fst x0 =? p) V')).
    { rewrite <- Hc. apply first_n_filter_length with (i := i). apply HV'. }
    lia.
Qed.

Lemma find_value_get_value_node {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U: assignments X) (u: node),
  forall (i: nat) (V V': assignments X), 
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true
  -> topological_sort G = Some ts /\ nth_error ts i = Some u
  -> get_values G g U [] = Some V
  -> first_n V i = Some V'
  -> find_value G g u U [] = get_value_of_node u G g U [] V'.
Proof.
  intros ts G g U u i V V'. intros HG HU [Hts Hi] HV HV'.
  assert (Hgvts: get_values_from_topo_sort_2 ts G g U [] = Some V).
  { symmetry. rewrite <- HV. apply get_values_from_topo_sort_equiv. easy. easy. easy. }

  assert (Hx: exists (x: X), nth_error V i = Some (u, x) /\ find_value G g u U [] = Some x).
  { apply find_value_preserves_index with (ts := ts). easy. easy. easy. easy. }
  destruct Hx as [x [Hux Hx]].
  assert (Hx': exists (x: X) (V': assignments X),
       get_value_of_node u G g U [] ([] ++ V') = Some x
       /\ first_n V i = Some V'
       /\ nth_error V i = Some (u, x)).
  { apply get_values_ts_2_get_value_node with (ts := ts). easy. apply Hgvts. }
  destruct Hx' as [x' [V'' [Hx' [HV'' Hux']]]].
  rewrite Hx. simpl in Hx'. rewrite HV' in HV''. inversion HV''. rewrite Hx'. rewrite Hux in Hux'. inversion Hux'. reflexivity.
Qed.

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

Lemma find_values_not_assigned {X: Type}: forall (G: graph) (g: graphfun) (P: nodes) (U A values: assignments X) (u: node),
  find_values G g P U A = Some values /\ ~(In u P) -> is_assigned values u = false.
Proof.
  intros G g P U A values u. intros [Hv Hu].
  generalize dependent values. induction P as [| h t IH].
  - intros values Hv. simpl in Hv. inversion Hv. simpl. reflexivity.
  - intros values Hv. simpl in Hu. simpl in Hv. destruct (find_value G g h U A) as [x|].
    + destruct (find_values G g t U A) as [r|].
      * inversion Hv. specialize IH with (values := r). simpl.
        assert (u =? h = false). { destruct (u =? h) as [|] eqn:Hhu. exfalso. apply Hu. left. apply eqb_eq. rewrite eqb_sym. apply Hhu. reflexivity. }
        rewrite H. simpl. apply IH.
        -- intros F. apply Hu. right. apply F. 
        -- reflexivity.
      * discriminate Hv.
    + discriminate Hv.
Qed.

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

Lemma find_values_same_if_parents_same {X: Type}: forall (G: graph) (g g': graphfun) (w: node) (U: assignments X),
  (forall (p: node), In p (find_parents w G) -> find_value G g p U [] = find_value G g' p U [])
  -> find_values G g' (find_parents w G) U [] = find_values G g (find_parents w G) U [].
Proof.
  intros G g g' w U H.
  induction (find_parents w G) as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    assert (Hh: find_value G g h U [] = find_value G g' h U []).
    { apply H. left. reflexivity. }
    rewrite Hh.
    destruct (find_value G g' h U []) as [x|] eqn:Hx.
    + assert (Ht: find_values G g' t U [] = find_values G g t U []).
      { apply IH. intros p Hp. apply H. right. apply Hp. }
      rewrite Ht. reflexivity.
    + reflexivity.
Qed.

Lemma get_value_of_node_equal {X: Type}: forall (ts: nodes) (G: graph) (g: graphfun) (U: assignments X) (u: node) (i: nat) (V V' P: assignments X),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true
  -> topological_sort G = Some ts /\ nth_error ts i = Some u
  -> get_values G g U [] = Some V
  -> first_n V i = Some V'
  -> find_values G g (find_parents u G) U [] = Some P
  -> get_value_of_node u G g U [] V' = get_value_of_node u G g U [] P.
Proof.
  intros ts G g U u i V V' P. intros HG HU [Hts Hi] HV HV' HP.
  unfold get_value_of_node. simpl. destruct (get_assigned_value U u) as [unobs|].
  - assert (Hpar: get_parent_assignments V' (find_parents u G) = get_parent_assignments P (find_parents u G)).
    { assert (Hedge: forall (p: node), In p (find_parents u G) -> edge_in_graph (p, u) G = true).
      { intros p Hp. apply edge_from_parent_to_child. apply Hp. }
      assert (Hcount: forall (p: node), In p (find_parents u G) -> count p (find_parents u G) = 1).
      { intros p Hp. apply each_parent_appears_once. easy. apply Hp. }
      generalize dependent P. induction (find_parents u G) as [| h t IH].
      - intros P HP. simpl. reflexivity.
      - intros P HP. simpl. simpl in HP.
        destruct (find_value G g h U []) as [x|] eqn:Hx.
        + assert (HPh: get_assigned_value P h = Some x).
          { apply find_values_get_assigned with (G := G) (g := g) (U := U) (A := []) (P := h :: t).
            repeat split.
            - simpl. rewrite Hx. apply HP.
            - left. reflexivity.
            - apply Hx. }
          assert (HVh': get_assigned_value V' h = Some x).
          { symmetry. rewrite <- Hx. apply find_value_parent_first_n with (ts := ts) (V := V) (U := U) (i := i) (u := u).
            - easy.
            - easy.
            - easy.
            - rewrite <- HV. symmetry. apply get_values_from_topo_sort_equiv. easy. easy. easy.
            - apply HV'.
            - apply edge_from_parent_to_child. apply Hedge. left. reflexivity. }
          rewrite HPh. rewrite HVh'. destruct (find_values G g t U []) as [r|] eqn:Hr.
          * specialize IH with (P := r).
            assert (Hpar: get_parent_assignments P t = get_parent_assignments r t).
            { inversion HP. clear IH. clear Hr. clear Hedge. induction t as [| ht tt IH].
              - simpl. reflexivity.
              - simpl.
                destruct (h =? ht) as [|] eqn:Hhht.
                + apply eqb_eq in Hhht. rewrite Hhht in Hcount. specialize Hcount with (p := ht).
                  assert (F: count ht (ht :: ht :: tt) = 1). { apply Hcount. left. reflexivity. }
                  simpl in F. rewrite eqb_refl in F. lia.
                + assert (Hind: get_parent_assignments ((h, x) :: r) tt = get_parent_assignments r tt).
                  { apply IH. intros p Hmem. destruct Hmem as [Hmem | Hmem].
                    - rewrite Hmem in *. simpl. rewrite eqb_refl. f_equal.
                      assert (Hc: count p (p :: ht :: tt) = 1). { apply Hcount. left. reflexivity. }
                      simpl in Hc. rewrite eqb_refl in Hc. inversion Hc. destruct (ht =? p) as [|] eqn:F.
                      + lia.
                      + reflexivity.
                    - simpl. destruct (h =? p) as [|] eqn:F.
                      + apply eqb_eq in F. rewrite F in *. assert (Hc: count p (p :: ht :: tt) = 1). { apply Hcount. left. reflexivity. }
                        simpl in Hc. rewrite eqb_refl in Hc. rewrite eqb_sym in Hhht. rewrite Hhht in Hc. inversion Hc.
                        apply member_count_at_least_1 in Hmem. lia.
                      + assert (Hc: count p (h :: ht :: tt) = 1). { apply Hcount. right. right. apply Hmem. }
                        simpl in Hc. rewrite F in Hc. destruct (ht =? p) as [|] eqn:F'.
                        * inversion Hc. apply member_count_at_least_1 in Hmem. lia.
                        * apply Hc. }
                  rewrite Hind. reflexivity. }
            rewrite Hpar.
            assert (Hind: get_parent_assignments V' t = get_parent_assignments r t).
            { apply IH.
              - intros p Hmem. apply Hedge. right. apply Hmem.
              - intros p Hmem. destruct (h =? p) as [|] eqn:Hhp.
                + apply eqb_eq in Hhp. rewrite Hhp in Hcount. specialize Hcount with (p := p).
                  assert (F: count p (p :: t) = 1). { apply Hcount. left. reflexivity. }
                  simpl in F. rewrite eqb_refl in F. inversion F. apply member_count_at_least_1 in Hmem. lia.
                + assert (Hc: count p (h :: t) = 1). { apply Hcount. right. apply Hmem. }
                  simpl in Hc. rewrite Hhp in Hc. apply Hc.
              - reflexivity. }
            rewrite Hind. reflexivity.
          * discriminate HP.
        + discriminate HP. }
    rewrite Hpar. reflexivity.
  - reflexivity.
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

Corollary find_values_existence_gen: forall X (G: graph) (g: graphfun) (U A: assignments X) (l: nodes),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true ->
  (forall (u: node), In u l -> node_in_graph u G = true) ->
  exists (P: assignments X), find_values G g l U A = Some P.
Proof.
  intros X G g U A l. intros [Hwf Hcyc]. intros HU Hu.
  induction l as [| h t IH].
  - exists []. reflexivity.
  - simpl. assert (Hv: exists v, find_value G g h U A = Some v).
    { apply find_value_existence.
      - split. apply Hwf. apply Hcyc.
      - split. apply HU. apply Hu. left. reflexivity. }
    destruct Hv as [v Hv]. rewrite Hv.
    assert (H': forall u: node, In u t -> node_in_graph u G = true).
    { intros h' Hmem. apply Hu. simpl. right. apply Hmem. }
    apply IH in H'. destruct H' as [P' H']. rewrite H'. exists ((h, v) :: P'). reflexivity.
Qed.


Theorem find_value_gives_value_of_node {X: Type}: forall (G: graph) (g: graphfun) (U: assignments X) (u: node),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true /\ node_in_graph u G = true ->
  exists (P: assignments X), find_values G g (find_parents u G) U [] = Some P
                              /\ find_value G g u U [] = get_value_of_node u G g U [] P.
Proof.
  intros G g U u. intros HG [HU Hu].
  assert (HP: exists (P: assignments X), find_values G g (find_parents u G) U [] = Some P).
  { apply find_values_existence. easy. easy. }
  destruct HP as [P HP]. exists P. split. apply HP.
  assert (HV: exists (V: assignments X), get_values G g U [] = Some V).
  { apply get_values_existence. easy. easy. }
  destruct HV as [V HV].
  assert (Hts: exists (ts: nodes), topological_sort G = Some ts).
  { apply topo_sort_exists_for_acyclic. easy. }
  destruct Hts as [ts Hts].
  assert (Hi: exists (i: nat), nth_error ts i = Some u).
  { apply In_nth_error. apply topo_sort_contains_nodes with (u := u) in Hts. apply Hts. apply Hu. }
  destruct Hi as [i Hi].
  assert (HV': exists (V': assignments X), first_n V i = Some V').
  { apply first_n_exists. apply index_correct_appears_once in Hi.
    - apply index_in_range in Hi.
      assert (Hlen: length V = length ts).
      { apply get_values_ts_2_preserves_length with (G := G) (g := g) (U := U) (Ae := []). symmetry. rewrite <- HV.
        apply get_values_from_topo_sort_equiv. easy. easy. easy. }
      rewrite Hlen. apply Hi.
    - apply topo_sort_contains_nodes_exactly_once with (G := G). easy. easy. }
  destruct HV' as [V' HV'].
  assert (H1: find_value G g u U [] = get_value_of_node u G g U [] V').
  { apply find_value_get_value_node with (ts := ts) (i := i) (V := V).
    - apply HG.
    - apply HU.
    - split. apply Hts. apply Hi.
    - apply HV.
    - apply HV'. }
  rewrite H1.
  apply get_value_of_node_equal with (ts := ts) (i := i) (V := V).
  - apply HG.
  - apply HU.
  - split. apply Hts. apply Hi.
  - apply HV.
  - apply HV'.
  - apply HP.
Qed.

Lemma find_values_append {X: Type}: forall (G: graph) (g: graphfun) (l: nodes) (U A: assignments X) (u: node),
  G_well_formed G = true /\ contains_cycle G = false ->
  is_assignment_for U (nodes_in_graph G) = true ->
  (forall (u: node), In u l -> node_in_graph u G = true) ->
  node_in_graph u G = true ->
  exists (x: X) (V: assignments X), find_value G g u U A = Some x
      /\ find_values G g l U A = Some V /\ find_values G g (l ++ [u]) U A = Some (V ++ [(u, x)]).
Proof.
  intros G g l U A u HG HU Hl Hu.
  assert (Hx: exists (x: X), find_value G g u U A = Some x).
  { apply find_value_existence.
    - apply HG.
    - split. apply HU. apply Hu. }
  destruct Hx as [x Hx].
  induction l as [| h t IH].
  - simpl. exists x. exists []. repeat split.
    + apply Hx.
    + rewrite Hx. simpl. reflexivity.
  - assert (Hxh: exists (xh: X), find_value G g h U A = Some xh).
    { apply find_value_existence.
      - apply HG.
      - split. apply HU. apply Hl. left. reflexivity. }
    destruct Hxh as [xh Hxh].
    assert (Hind: forall u : node, In u t -> node_in_graph u G = true).
    { intros v Hmem. apply Hl. right. apply Hmem. }
    apply IH in Hind. destruct Hind as [x' [V [Hx' [HV HVx]]]].
    exists x'. exists ((h, xh) :: V). repeat split.
    + apply Hx'.
    + simpl. rewrite Hxh. rewrite HV. reflexivity.
    + simpl. rewrite Hxh. rewrite HVx. reflexivity.
Qed.

Lemma get_parent_assignments_append {X: Type}: forall (G: graph) (g: graphfun) (l: nodes) (U Ae Ae': assignments X) (u: node),
  G_well_formed G = true /\ contains_cycle G = false /\ is_assignment_for U (nodes_in_graph G) = true
  -> (forall (v: node), In v l -> node_in_graph v G = true) /\ node_in_graph u G = true
  -> subset (find_parents u G) l = true /\ find_values G g l U [] = Some Ae
  -> get_parent_assignments Ae (find_parents u G) = get_parent_assignments (Ae ++ Ae') (find_parents u G).
Proof.
  intros G g l U Ae Ae' u. intros [HG [Hcyc HU]] [Hul Hu] [Hl HAe].
  induction (find_parents u G) as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    assert (Hlmem: In h l).
    { apply member_In_equiv. apply split_and_true in Hl. apply Hl. }

    assert (Hh: exists (x: X), find_value G g h U [] = Some x).
    { apply find_value_existence. easy. split. apply HU. apply Hul. simpl in Hl. apply Hlmem. }
    destruct Hh as [x Hh].

    assert (HAeh: get_assigned_value Ae h = Some x).
    { apply find_values_get_assigned with (G := G) (g := g) (P := l) (U := U) (A := []). easy. }

    rewrite HAeh. assert (HAeh': get_assigned_value (Ae ++ Ae') h = Some x).
    { apply get_assigned_app_Some. apply HAeh. }
    rewrite HAeh'.

    simpl in Hl. apply split_and_true in Hl. destruct Hl as [_ Hl]. apply IH in Hl.
    rewrite Hl. reflexivity.
Qed.


Lemma find_values_get_assigned_2: forall X (G: graph) (g: graphfun) (P: nodes) (U A values: assignments X)
                                       (x: X) (m: node),
  G_well_formed G = true /\ contains_cycle G = false /\ is_assignment_for U (nodes_in_graph G) = true
  -> find_values G g P U A = Some values /\ In m P /\ (forall (u: node), In u P -> node_in_graph u G = true)
  -> get_assigned_value values m = Some x -> find_value G g m U A = Some x.
Proof.
  intros X G g P U A values x m.
  intros HG [Hv [Hm Hu]] Hx. generalize dependent values. induction P as [| h t IH].
  - exfalso. apply Hm.
  - intros values Hv Hx.
    assert (Hh: exists (xh: X), find_value G g h U A = Some xh).
    { apply find_value_existence. easy. split. easy. apply Hu. left. reflexivity. }
    destruct Hh as [xh Hxh].
    destruct (h =? m) as [|] eqn:Hhm.
    + simpl in Hv. apply eqb_eq in Hhm.
      rewrite Hxh in Hv.
      destruct (find_values G g t U A) as [r|].
      * inversion Hv. rewrite <- H0 in Hx. simpl in Hx. rewrite Hhm in Hx. rewrite eqb_refl in Hx. inversion Hx.
        rewrite <- H1. rewrite <- Hhm. apply Hxh.
      * discriminate Hv.
    + destruct Hm as [Hm | Hm]. rewrite Hm in Hhm. rewrite eqb_refl in Hhm. discriminate Hhm.
      simpl in Hv. rewrite Hxh in Hv. destruct (find_values G g t U A) as [r|].
      * inversion Hv. apply IH with (values := r).
        -- apply Hm.
        -- intros u Hu'. apply Hu. right. apply Hu'.
        -- reflexivity.
        -- rewrite <- H0 in Hx. simpl in Hx. rewrite Hhm in Hx. apply Hx.
      * discriminate Hv.
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
  { apply find_value_gives_value_of_node.
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
              | h1 :: (h2 :: t2) => if (is_mediator_bool h h2 h1 G || is_mediator_bool h2 h h1 G) then h1 :: (find_mediators_in_nodes t G)
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
    <-> exists y z: node, sublist [y; x; z] l = true
        /\ ((is_edge (y, x) G = true /\ is_edge (x, z) G = true)
            \/ (is_edge (x, y) G = true /\ is_edge (z, x) G = true)).
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
             - left. unfold is_mediator_bool in Hmed2. apply split_and_true in Hmed2.
               rewrite <- Hhx. apply Hmed2. }
           { apply IH in Hind. destruct Hind as [y Hind]. destruct Hind as [z Hind].
             exists y. exists z. split.
             - destruct Hind as [Hsub _]. simpl. apply split_orb_true. right. apply Hsub.
             - destruct Hind as [_ Hedge]. apply Hedge. }
        -- simpl in Hmed. rewrite Hmed2 in Hmed. simpl in Hmed. destruct (is_mediator_bool h'' h h') as [|] eqn:Hmed3.
           ++ simpl in Hmed. destruct Hmed as [Hhx | Hind].
              { exists h. exists h''. split.
                - rewrite <- Hhx. simpl.
                  rewrite eqb_refl. simpl. rewrite eqb_refl. simpl. rewrite eqb_refl. reflexivity.
                - right. unfold is_mediator_bool in Hmed3. apply split_and_true in Hmed3.
                  rewrite <- Hhx. apply and_comm. apply Hmed3. }
              { apply IH in Hind. destruct Hind as [y Hind]. destruct Hind as [z Hind].
                exists y. exists z. split.
                - destruct Hind as [Hsub _]. simpl. apply split_orb_true. right. apply Hsub.
                - destruct Hind as [_ Hedge]. apply Hedge. }
           ++ simpl in Hmed. apply IH in Hmed.
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
           rewrite andb_comm in Hz. simpl in Hz. simpl.
           assert (Hmed: (is_mediator_bool h h'' h' G || is_mediator_bool h'' h h' G) = true).
           { unfold is_mediator_bool.
             rewrite eqb_eq in Hy. rewrite <- Hy.
             rewrite eqb_eq in Hx. rewrite <- Hx.
             rewrite eqb_eq in Hz. rewrite <- Hz. apply split_orb_true. rewrite split_and_true. rewrite split_and_true.
             destruct Hedge as [Hedge | Hedge]. left. apply Hedge. right. rewrite and_comm. apply Hedge. }
           simpl. rewrite Hmed. simpl. left. rewrite eqb_eq in Hx. rewrite Hx. reflexivity.
        -- apply IH in Hind. destruct (is_mediator_bool h h'' h' G) as [|] eqn:Hmed.
           { simpl. rewrite Hmed. simpl. right. apply Hind. }
           { simpl. rewrite Hmed. simpl. destruct (is_mediator_bool h'' h h' G) as [|] eqn:Hmed'.
             - simpl. right. apply Hind.
             - apply Hind. } }
Qed.

Theorem directed_path_all_mediators: forall (u v m: node) (l: nodes) (G: graph),
  is_directed_path_in_graph (u, v, l) G = true /\ In m l -> In m (find_mediators_in_path (u, v, l) G).
Proof.
  intros u v m l G [Hp Hm].
  generalize dependent u. induction l as [| h t IH].
  - intros u H. exfalso. apply Hm.
  - intros u Hp. destruct Hm as [Hm | Hm].
    + simpl. destruct t as [| h' t'].
      * simpl. simpl in Hp. unfold is_mediator_bool. apply split_and_true in Hp. rewrite split_and_true in Hp. destruct Hp as [Huh [Hhv _]].
        rewrite Huh. rewrite Hhv. simpl. left. apply Hm.
      * simpl. simpl in Hp. unfold is_mediator_bool. apply split_and_true in Hp. rewrite split_and_true in Hp. destruct Hp as [Huh [Hhv _]].
        rewrite Huh. rewrite Hhv. simpl. left. apply Hm.
    + simpl. destruct t as [| h' t'].
      * exfalso. apply Hm.
      * simpl. destruct (is_mediator_bool u h' h G || is_mediator_bool h' u h G) as [|] eqn:H'.
        -- simpl. right. apply IH.
           ++ apply Hm.
           ++ simpl in Hp. apply split_and_true in Hp. destruct Hp as [_ Hp]. apply Hp.
        -- simpl. apply IH.
           ++ apply Hm.
           ++ simpl in Hp. apply split_and_true in Hp. destruct Hp as [_ Hp]. apply Hp.
Qed.

Theorem mediators_same_in_reverse_path: forall (u v m: node) (l: nodes) (G: graph),
  In m (find_mediators_in_path (u, v, l) G) -> In m (find_mediators_in_path (v, u, rev l) G).
Proof.
  intros u v m l G H.
  apply mediators_vs_edges_in_path. apply mediators_vs_edges_in_path in H. destruct H as [y [z [Hsub Hedge]]].
  exists z. exists y. split.
  - apply sublist_rev in Hsub. simpl in Hsub. rewrite reverse_list_append in Hsub. simpl in Hsub. apply Hsub.
  - destruct Hedge as [Hedge | Hedge].
    + right. rewrite and_comm. apply Hedge.
    + left. rewrite and_comm. apply Hedge.
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

Theorem confounders_same_in_reverse_path: forall (u v m: node) (l: nodes) (G: graph),
  In m (find_confounders_in_path (u, v, l) G) -> In m (find_confounders_in_path (v, u, rev l) G).
Proof.
  intros u v m l G H.
  apply confounders_vs_edges_in_path. apply confounders_vs_edges_in_path in H. destruct H as [y [z [Hsub Hedge]]].
  exists z. exists y. split.
  - apply sublist_rev in Hsub. simpl in Hsub. rewrite reverse_list_append in Hsub. simpl in Hsub. apply Hsub.
  - rewrite and_comm. apply Hedge.
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
  intros u v m l G H.
  apply colliders_vs_edges_in_path. apply colliders_vs_edges_in_path in H. destruct H as [y [z [Hsub Hedge]]].
  exists z. exists y. split.
  - apply sublist_rev in Hsub. simpl in Hsub. rewrite reverse_list_append in Hsub. simpl in Hsub. apply Hsub.
  - rewrite and_comm. apply Hedge.
Qed.



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

Lemma concat_preserves_confounders_r: forall (G: graph) (u mid v m: node) (l1 l2: nodes),
  In m (find_confounders_in_path (mid, v, l2) G) -> In m (find_confounders_in_path (concat u mid v l1 l2) G).
Proof.
  intros G u mid v m l1 l2 H.
  apply confounders_vs_edges_in_path in H. destruct H as [y [z [Hsub Hedge]]].
  unfold concat. unfold find_confounders_in_path. apply confounders_vs_edges_in_path. exists y. exists z.
  split.
  - apply sublist_breaks_down_list in Hsub. destruct Hsub as [l3 [l4 Hsub]].
    rewrite <- app_assoc. apply sublist_breaks_down_list. exists (u :: l1 ++ l3). exists l4.
    simpl. rewrite <- Hsub. simpl. rewrite <- app_assoc. reflexivity.
  - apply Hedge.
Qed.

Lemma add_node_preserves_confounders: forall (G: graph) (u h v m: node) (t: nodes),
  In m (find_confounders_in_path (h, v, t) G) -> In m (find_confounders_in_path (u, v, h :: t) G).
Proof.
  intros G u h v m t H.
  apply confounders_vs_edges_in_path in H. destruct H as [y [z [Hsub Hedge]]].
  apply confounders_vs_edges_in_path. exists y. exists z.
  split.
  - apply sublist_breaks_down_list in Hsub. destruct Hsub as [l3 [l4 Hsub]].
    apply sublist_breaks_down_list. exists (u :: l3). exists l4.
    simpl. rewrite <- Hsub. simpl. reflexivity.
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
Proof.
  intros G u v x l.
  intros Hpath. split.
  - intros Hmem. generalize dependent u. induction l as [| h t IH].
    + exfalso. apply Hmem.
    + intros u Hu. destruct Hmem as [Hmem | Hmem].
      * rewrite <- Hmem. simpl in Hu. destruct G as [V E]. apply split_and_true in Hu. destruct Hu as [Hhu Hu].
        destruct t as [| h' t'].
        -- simpl in Hu. rewrite andb_comm in Hu. simpl in Hu. apply split_orb_true in Hu. apply split_orb_true in Hhu.
           destruct Hhu as [Huh | Hhu]. destruct Hu as [Hhv | Hvh].
           ++ left. apply mediators_vs_edges_in_path. exists u. exists v. split.
              simpl. repeat rewrite eqb_refl. reflexivity. left. rewrite Huh. split. reflexivity. apply Hhv.
           ++ right. right. apply colliders_vs_edges_in_path. exists u. exists v. split. simpl. repeat rewrite eqb_refl. reflexivity.
              split. apply Huh. apply Hvh.
           ++ destruct Hu as [Hhv | Hvh].
              ** right. left. apply confounders_vs_edges_in_path. exists u. exists v. split.
                 simpl. repeat rewrite eqb_refl. reflexivity. split. apply Hhu. apply Hhv.
              ** left. apply mediators_vs_edges_in_path. exists u. exists v. split.
                 simpl. repeat rewrite eqb_refl. reflexivity. right. split. apply Hhu. apply Hvh.
        -- simpl in Hu. apply split_and_true in Hu. destruct Hu as [Hu _]. apply split_orb_true in Hu. apply split_orb_true in Hhu.
           destruct Hhu as [Huh | Hhu]. destruct Hu as [Hhv | Hvh].
           ++ left. apply mediators_vs_edges_in_path. exists u. exists h'. split.
              simpl. repeat rewrite eqb_refl. reflexivity. left. rewrite Huh. split. reflexivity. apply Hhv.
           ++ right. right. apply colliders_vs_edges_in_path. exists u. exists h'. split. simpl. repeat rewrite eqb_refl. reflexivity.
              split. apply Huh. apply Hvh.
           ++ destruct Hu as [Hhv | Hvh].
              ** right. left. apply confounders_vs_edges_in_path. exists u. exists h'. split.
                 simpl. repeat rewrite eqb_refl. reflexivity. split. apply Hhu. apply Hhv.
              ** left. apply mediators_vs_edges_in_path. exists u. exists h'. split.
                 simpl. repeat rewrite eqb_refl. reflexivity. right. split. apply Hhu. apply Hvh.
      * specialize IH with (u := h). apply IH in Hmem.
        2: { simpl in Hu. destruct G as [V E]. apply split_and_true in Hu. apply Hu. }
        destruct Hmem as [H | [H | H]].
        -- left. simpl. destruct t as [| h' t'].
           ++ simpl. simpl in H. exfalso. apply H.
           ++ simpl. destruct (is_mediator_bool u h' h G || is_mediator_bool h' u h G) as [|]. right. apply H. apply H.
        -- right. left. destruct t as [| h' t'].
           ++ simpl. simpl in H. exfalso. apply H.
           ++ simpl. destruct (is_confounder_bool u h' h G) as [|]. right. apply H. apply H.
        -- right. right. destruct t as [| h' t'].
           ++ simpl. simpl in H. exfalso. apply H.
           ++ simpl. destruct (is_collider_bool u h' h G) as [|]. right. apply H. apply H.
  - intros Hx. destruct Hx as [Hx | [Hx | Hx]].
    + apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [Hsub Hedg]]].
      apply end_of_sublist_still_sublist_gen in Hsub. apply first_elt_of_sublist_not_last_elt_gen in Hsub. apply Hsub.
    + apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hsub Hedg]]].
      apply end_of_sublist_still_sublist_gen in Hsub. apply first_elt_of_sublist_not_last_elt_gen in Hsub. apply Hsub.
    + apply colliders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hsub Hedg]]].
      apply end_of_sublist_still_sublist_gen in Hsub. apply first_elt_of_sublist_not_last_elt_gen in Hsub. apply Hsub.
Qed.

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
  intros G u p Hcyc Hu. (* TODO think the condition needs to be that the path is acyclic...but shouldn't change things with proofs *)
Admitted.

Theorem if_confounder_then_not_mediator_path: forall (G: graph) (u: node) (p: path),
  contains_cycle G = false -> In u (find_confounders_in_path p G)
  -> ~(In u (find_mediators_in_path p G)) /\ ~(In u (find_colliders_in_path p G)).
Proof.
Admitted.

Theorem if_collider_then_not_mediator_path: forall (G: graph) (u: node) (p: path),
  contains_cycle G = false -> In u (find_colliders_in_path p G)
  -> ~(In u (find_mediators_in_path p G)) /\ ~(In u (find_confounders_in_path p G)).
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

Theorem d_separated_symmetry: forall (u v: node) (G: graph) (Z: nodes),
  d_separated_bool u v G Z = true -> d_separated_bool v u G Z = true.
Proof.
  intros u v G Z H.
  destruct (d_separated_bool v u G Z) as [|] eqn:Hd.
  - reflexivity.
  - apply d_separated_vs_connected in Hd. destruct Hd as [l Hl].
    assert (Hl': exists l: nodes, (acyclic_path_2 (u, v, l)) /\ (is_path_in_graph (u, v, l) G = true)
                                              /\ d_connected_2 (u, v, l) G Z).
    { exists (rev l). split.
      - apply reverse_path_still_acyclic. apply Hl.
      - split. apply reverse_path_in_graph. apply Hl. apply reverse_d_connected_paths. apply Hl. }
    apply d_separated_vs_connected in Hl'. rewrite Hl' in H. discriminate H.
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

Theorem d_connected_cat: forall (u v h: node) (t: nodes) (G: graph) (Z: nodes),
  contains_cycle G = false
  -> d_connected_2 (h, v, t) G Z
  -> (In h (find_mediators_in_path (u, v, h :: t) G) /\ ~ In h Z)
     \/ (In h (find_confounders_in_path (u, v, h :: t) G) /\ ~ In h Z)
     \/ (In h (find_colliders_in_path (u, v, h :: t) G) /\ (some_descendant_in_Z_bool (find_descendants h G) Z = true))
  -> d_connected_2 (u, v, h :: t) G Z.
Proof.
  intros u v h t G Z. intros HGcyc H1. intros H.
  unfold d_connected_2 in *. repeat split.
  + apply no_overlap_non_member. intros m Hm Hm'.
    simpl in Hm. destruct t as [| h' t'].
    * simpl in Hm. destruct (is_mediator_bool u v h G || is_mediator_bool v u h G) as [|] eqn:Hmed.
      - assert (In h (find_mediators_in_path (u, v, [h]) G)). { simpl. rewrite Hmed. left. reflexivity. }
        apply if_mediator_then_not_confounder_path in H0. 2: { apply HGcyc. }
        destruct H as [H | [H | H]].
        -- destruct H as [_ H]. destruct Hm as [Hm | Hm]. apply H. rewrite Hm. apply Hm'. apply Hm.
        -- destruct H0 as [H0 _]. apply H0. apply H.
        -- destruct H0 as [_ H0]. apply H0. apply H.
      - apply Hm.
    * simpl in Hm. destruct (is_mediator_bool u h' h G || is_mediator_bool h' u h G) as [|] eqn:Hmed.
      - assert (In h (find_mediators_in_path (u, v, h :: h' :: t') G)). { simpl. rewrite Hmed. left. reflexivity. }
        apply if_mediator_then_not_confounder_path in H0. 2: { apply HGcyc. }
        destruct H as [H | [H | H]].
        -- destruct Hm as [Hm | Hm].
           ++ destruct H as [_ H]. apply H. rewrite Hm. apply Hm'.
           ++ destruct H1 as [H1 _]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
        -- destruct Hm as [Hm | Hm].
           ++ destruct H0 as [H0 _]. apply H0. apply H.
           ++ destruct H1 as [H1 _]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
        -- destruct Hm as [Hm | Hm].
           ++ destruct H0 as [_ H0]. apply H0. apply H.
           ++ destruct H1 as [H1 _]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
      - destruct H1 as [H1 _]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
  + apply no_overlap_non_member. intros m Hm Hm'.
    simpl in Hm. destruct t as [| h' t'].
    * simpl in Hm. destruct (is_confounder_bool u v h G) as [|] eqn:Hmed.
      - assert (In h (find_confounders_in_path (u, v, [h]) G)). { simpl. rewrite Hmed. left. reflexivity. }
        apply if_confounder_then_not_mediator_path in H0. 2: { apply HGcyc. }
        destruct H as [H | [H | H]].
        -- destruct H0 as [H0 _]. apply H0. apply H.
        -- destruct H as [_ H]. destruct Hm as [Hm | Hm]. apply H. rewrite Hm. apply Hm'. apply Hm.
        -- destruct H0 as [_ H0]. apply H0. apply H.
      - apply Hm.
    * simpl in Hm. destruct (is_confounder_bool u h' h G) as [|] eqn:Hmed.
      - assert (In h (find_confounders_in_path (u, v, h :: h' :: t') G)). { simpl. rewrite Hmed. left. reflexivity. }
        apply if_confounder_then_not_mediator_path in H0. 2: { apply HGcyc. }
        destruct H as [H | [H | H]].
        -- destruct Hm as [Hm | Hm].
           ++ destruct H0 as [H0 _]. apply H0. apply H.
           ++ destruct H1 as [_ [H1 _]]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
        -- destruct Hm as [Hm | Hm].
           ++ destruct H as [_ H]. apply H. rewrite Hm. apply Hm'.
           ++ destruct H1 as [_ [H1 _]]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
        -- destruct Hm as [Hm | Hm].
           ++ destruct H0 as [_ H0]. apply H0. apply H.
           ++ destruct H1 as [_ [H1 _]]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
      - destruct H1 as [_ [H1 _]]. apply no_overlap_non_member with (x := m) in H1. apply H1. apply Hm'. apply Hm.
  + unfold all_colliders_have_descendant_conditioned_on. apply forallb_true_iff_mem. intros m Hcolm.
    pose proof Hcolm as H0. apply if_collider_then_not_mediator_path in H0.
    simpl in Hcolm. destruct t as [| h' t'].
    * simpl in Hcolm. destruct (is_collider_bool u v h G) as [|] eqn:Hcol.
      - destruct Hcolm as [Hcolm | Hcolm]. rewrite Hcolm in *. destruct H as [H | [H | H]].
        -- exfalso. destruct H0 as [H0 _]. apply H0. apply H.
        -- destruct H0 as [_ H0]. exfalso. apply H0. apply H.
        -- destruct H as [_ H]. apply H.
        -- exfalso. apply Hcolm.
      - exfalso. apply Hcolm.
    * simpl in Hcolm. destruct (is_collider_bool u h' h G) as [|] eqn:Hcol.
      - destruct Hcolm as [Hcolm | Hcolm].
        -- rewrite Hcolm in *. destruct H as [H | [H | H]].
           ++ exfalso. destruct H0 as [H0 _]. apply H0. apply H.
           ++ destruct H0 as [_ H0]. exfalso. apply H0. apply H.
           ++ destruct H as [_ H]. apply H.
        -- destruct H1 as [_ [_ H1]]. apply forallb_true with (x := m) in H1. apply H1. apply Hcolm.
      - destruct H1 as [_ [_ H1]]. apply forallb_true with (x := m) in H1. apply H1. apply Hcolm.
    * apply HGcyc.
Qed.

Lemma subpath_preserves_mediators: forall (w u v m: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ (In m (find_mediators_in_path (u, v, l2) G) \/ In m (find_mediators_in_path (w, u, l1) G))
  -> In m (find_mediators_in_path (w, v, l3) G).
Proof.
  intros w u v m l1 l2 l3 G. intros [Hl3 H].
  destruct H as [H | H].
  { apply mediators_vs_edges_in_path. apply mediators_vs_edges_in_path in H. destruct H as [y [z [Hyz [[Hyx Hxz] | [Hxy Hzx]]]]].
    { exists y. exists z. repeat split.
      -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l21 [l22 Hl2]].
         exists (w :: l1 ++ l21). exists l22. simpl. rewrite <- Hl3. simpl. rewrite <- app_assoc. rewrite <- app_assoc. simpl. simpl in Hl2. rewrite <- Hl2. reflexivity.
      -- left. split. apply Hyx. apply Hxz. }
    { exists y. exists z. repeat split.
      -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l21 [l22 Hl2]].
         exists (w :: l1 ++ l21). exists l22. simpl. rewrite <- Hl3. simpl. rewrite <- app_assoc. rewrite <- app_assoc. simpl. simpl in Hl2. rewrite <- Hl2. reflexivity.
      -- right. split. apply Hxy. apply Hzx. } }
  { apply mediators_vs_edges_in_path. apply mediators_vs_edges_in_path in H. destruct H as [y [z [Hyz [[Hyx Hxz] | [Hxy Hzx]]]]].
    { exists y. exists z. repeat split.
      -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l21 [l22 Hl2]].
         exists l21. exists (l22 ++ l2 ++ [v]). rewrite app_assoc with (l := l21). rewrite app_assoc. rewrite <- app_assoc with (l := l21). rewrite Hl2. simpl. rewrite <- app_assoc. rewrite <- Hl3. simpl. rewrite <- app_assoc. simpl. reflexivity.
      -- left. split. apply Hyx. apply Hxz. }
    { exists y. exists z. repeat split.
      -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l21 [l22 Hl2]].
         exists l21. exists (l22 ++ l2 ++ [v]). rewrite app_assoc with (l := l21). rewrite app_assoc. rewrite <- app_assoc with (l := l21). rewrite Hl2. simpl. rewrite <- app_assoc. rewrite <- Hl3. simpl. rewrite <- app_assoc. simpl. reflexivity.
      -- right. split. apply Hxy. apply Hzx. } }
Qed.

Lemma subpath_preserves_confounders: forall (w u v m: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ In m (find_confounders_in_path (u, v, l2) G)
  -> In m (find_confounders_in_path (w, v, l3) G).
Proof.
  intros w u v m l1 l2 l3 G. intros [Hl3 H].
  apply confounders_vs_edges_in_path. apply confounders_vs_edges_in_path in H. destruct H as [y [z [Hyz [Hyx Hxz]]]].
  exists y. exists z. repeat split.
  -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l21 [l22 Hl2]].
     exists (w :: l1 ++ l21). exists l22. simpl. rewrite <- Hl3. simpl. rewrite <- app_assoc. rewrite <- app_assoc. simpl. simpl in Hl2. rewrite <- Hl2. reflexivity.
  -- apply Hyx.
  -- apply Hxz.
Qed.

Lemma subpath_preserves_colliders: forall (w u v m: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ (In m (find_colliders_in_path (u, v, l2) G) \/ In m (find_colliders_in_path (w, u, l1) G))
  -> In m (find_colliders_in_path (w, v, l3) G).
Proof.
  intros w u v m l1 l2 l3 G. intros [Hl3 Hx].
  destruct Hx as [Hx | Hx].
  { apply colliders_vs_edges_in_path. apply colliders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hyz [Hyx Hxz]]]].
    exists y. exists z. repeat split.
    -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l21 [l22 Hl2]].
       exists (w :: l1 ++ l21). exists l22. simpl. rewrite <- Hl3. simpl. rewrite <- app_assoc. rewrite <- app_assoc. simpl. simpl in Hl2. rewrite <- Hl2. reflexivity.
    -- apply Hyx.
    -- apply Hxz. }
  { apply colliders_vs_edges_in_path. apply colliders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hyz [Hyx Hxz]]]].
    exists y. exists z. repeat split.
    -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l21 [l22 Hl2]].
       exists l21. exists (l22 ++ l2 ++ [v]). simpl. rewrite <- Hl3. simpl. rewrite <- app_assoc. simpl.
       rewrite <- append_vs_concat. rewrite <- append_vs_concat. rewrite <- append_vs_concat. rewrite app_assoc.
       simpl in Hl2. rewrite <- append_vs_concat in Hl2. rewrite <- append_vs_concat in Hl2. rewrite <- append_vs_concat in Hl2.
       rewrite Hl2. simpl. rewrite append_vs_concat. reflexivity.
    -- apply Hyx.
    -- apply Hxz. }
Qed.

Lemma subpath_preserves_colliders_2: forall (w u v: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3
  -> find_colliders_in_path (w, v, l3) G = (find_colliders_in_path (w, u, l1) G) ++ [u] ++ (find_colliders_in_path (u, v, l2) G)
     \/ find_colliders_in_path (w, v, l3) G = (find_colliders_in_path (w, u, l1) G) ++ (find_colliders_in_path (u, v, l2) G).
Proof.
  intros w u v l1 l2 l3 G. intros H.
  generalize dependent w. generalize dependent l3. induction l1 as [| h t IH].
  - intros l3 H w. simpl in H. rewrite <- H. simpl. destruct l2 as [| h2 t2].
    + simpl. destruct (is_collider_bool w v u G) as [|]. left. reflexivity. right. reflexivity.
    + simpl. destruct (is_collider_bool w h2 u G) as [|]. left. reflexivity. right. reflexivity.
  - intros l3 H w. simpl. destruct l3 as [| h3 t3].
    + simpl. discriminate H.
    + specialize IH with (l3 := t3) (w := h3). simpl in H. inversion H. rewrite <- H1 in *. apply IH in H2 as Hind.
      simpl. rewrite H2. simpl in Hind. destruct t3 as [| h' t'].
      * destruct t as [| ht tt]. discriminate H. discriminate H.
      * simpl. simpl in Hind. destruct (is_collider_bool w h' h G) as [|] eqn:Hcol.
        -- destruct Hind as [Hind | Hind].
           ++ left. destruct t as [| ht tt].  simpl. simpl in Hind. simpl in H2. inversion H2. rewrite H3 in *. rewrite H4 in *. rewrite Hcol. simpl. f_equal. apply Hind.
              simpl. simpl in Hind. simpl in H2. inversion H2. rewrite H3 in *. rewrite H4 in *. rewrite Hcol. simpl. f_equal. apply Hind.
           ++ right. destruct t as [| ht tt].  simpl. simpl in Hind. simpl in H2. inversion H2. rewrite H3 in *. rewrite H4 in *. rewrite Hcol. simpl. f_equal. apply Hind.
              simpl. simpl in Hind. simpl in H2. inversion H2. rewrite H3 in *. rewrite H4 in *. rewrite Hcol. simpl. f_equal. apply Hind.
        -- destruct Hind as [Hind | Hind].
           ++ left. destruct t as [| ht tt].  simpl. simpl in Hind. simpl in H2. inversion H2. rewrite H3 in *. rewrite H4 in *. rewrite Hcol. simpl. f_equal. apply Hind.
              simpl. simpl in Hind. simpl in H2. inversion H2. rewrite H3 in *. rewrite H4 in *. rewrite Hcol. simpl. f_equal. apply Hind.
           ++ right. destruct t as [| ht tt].  simpl. simpl in Hind. simpl in H2. inversion H2. rewrite H3 in *. rewrite H4 in *. rewrite Hcol. simpl. f_equal. apply Hind.
              simpl. simpl in Hind. simpl in H2. inversion H2. rewrite H3 in *. rewrite H4 in *. rewrite Hcol. simpl. f_equal. apply Hind.
Qed.

Lemma collider_means_edge_in: forall (c x v hl2: node) (l1 tl2: nodes) (G: graph),
  acyclic_path_2 (x, v, l1 ++ [c] ++ hl2 :: tl2)
  -> In c (find_colliders_in_path (x, v, l1 ++ [c] ++ hl2 :: tl2) G)
  -> is_edge (hl2, c) G = true.
Proof.
  intros c x v h l t G Hcyc H.
  apply colliders_vs_edges_in_path in H. destruct H as [y [z [Hsub Hedge]]].
  apply end_of_sublist_still_sublist_2 in Hsub as Hsub'.
  assert (z = h). { apply two_sublists_the_same with (l := (x :: l ++ [c] ++ h :: t) ++ [v]) (a := c). apply Hsub'.
                    apply sublist_breaks_down_list. exists (x :: l). exists (t ++ [v]). simpl. rewrite <- app_assoc. simpl. reflexivity.
                    apply acyclic_path_count with (x := c) in Hcyc. apply Hcyc. right. apply membership_append. apply membership_append_r. left. reflexivity. }
  rewrite H in Hedge. apply Hedge.
Qed.

Lemma collider_means_edge_in_end: forall (c x v: node) (l1: nodes) (G: graph),
  acyclic_path_2 (x, v, l1 ++ [c])
  -> In c (find_colliders_in_path (x, v, l1 ++ [c]) G)
  -> is_edge (v, c) G = true.
Proof.
  intros c x v l G Hcyc H.
  apply colliders_vs_edges_in_path in H. destruct H as [y [z [Hsub Hedge]]].
  apply end_of_sublist_still_sublist_2 in Hsub as Hsub'.
  assert (z = v). { apply two_sublists_the_same with (l := (x :: l ++ [c]) ++ [v]) (a := c). apply Hsub'.
                    apply sublist_breaks_down_list. exists (x :: l). exists []. simpl. rewrite <- app_assoc. simpl. reflexivity.
                    apply acyclic_path_count with (x := c) in Hcyc. apply Hcyc. right. apply membership_append. apply membership_append_r. left. reflexivity. }
  rewrite H in Hedge. apply Hedge.
Qed.

Lemma mediator_means_edge_out: forall (c dy y: node) (ly1 ly2 py: nodes) (G: graph),
  py ++ [dy] = ly1 ++ [y] ++ ly2
  -> is_directed_path_in_graph (c, dy, py) G = true
  -> (ly1 = [] -> is_edge (c, y) G = true) /\
     (forall (hly1: node) (tly1: nodes), ly1 = hly1 :: tly1 -> is_edge (c, hly1) G = true).
Proof.
  intros cy dy y ly1 ly2 py G Hpdy Hdir.
  split.
  ** intros Hly1. rewrite Hly1 in *.
     destruct py as [| hpy tpy]. simpl in Hpdy. inversion Hpdy. rewrite H0 in Hdir.
     simpl in Hdir. apply split_and_true in Hdir. apply Hdir.
     simpl in Hpdy. inversion Hpdy. rewrite H0 in Hdir.
     simpl in Hdir. apply split_and_true in Hdir. apply Hdir.
  ** intros hly1 tly1 Hly1. rewrite Hly1 in *.
     destruct py as [| hpy tpy]. simpl in Hpdy. inversion Hpdy. rewrite H0 in Hdir.
     simpl in Hdir. apply split_and_true in Hdir. apply Hdir.
     simpl in Hpdy. inversion Hpdy. rewrite H0 in Hdir.
     simpl in Hdir. apply split_and_true in Hdir. apply Hdir.
Qed.


Lemma path_breaks_down_midpoint_vs_endpoint: forall (l1 l2 l3: nodes) (a b: node),
  l1 ++ [a] ++ l2 = l3 ++ [b]
  -> (rev l2 = [] -> a = b /\ l1 = l3) /\ (forall (hl2: node) (tl2: nodes), rev l2 = hl2 :: tl2 -> b = hl2 /\ l3 = l1 ++ [a] ++ rev tl2).
Proof.
  intros l1' l2' l3 a b H. split.
  { intros Hlp2.
    assert (Hlem: rev (l1' ++ [a]) = rev (l3 ++ [b])).
    { rewrite <- H. rewrite reverse_list_append. rewrite reverse_list_append. rewrite reverse_list_append. unfold nodes in *. unfold node in *. rewrite Hlp2.
      simpl. reflexivity. }
    rewrite reverse_list_append in Hlem. rewrite reverse_list_append in Hlem. simpl in Hlem.
    inversion Hlem. split. reflexivity. rewrite reverse_list_twice with (l := l1'). rewrite H2. rewrite <- reverse_list_twice.
    reflexivity. }
  { intros hlp2' tlp2' Hlp2'. assert (Hlem: rev (l1' ++ [a] ++ l2') = rev (l3 ++ [b])).
    { rewrite <- H. reflexivity. }
    rewrite reverse_list_append in Hlem. rewrite reverse_list_append in Hlem. unfold nodes in *. unfold node in *. rewrite Hlp2' in Hlem. simpl in Hlem. rewrite reverse_list_append in Hlem.
    simpl in Hlem. inversion Hlem. split. reflexivity. rewrite reverse_list_twice with (l := l3).
    rewrite <- H2. repeat rewrite reverse_list_append. rewrite <- reverse_list_twice. simpl. reflexivity. }
Qed.


Lemma mediator_end_means_edge_in: forall (c dy y: node) (ly1 ly2 py: nodes) (G: graph),
  py ++ [dy] = ly1 ++ [y] ++ ly2
  -> is_directed_path_in_graph (c, dy, py) G = true
  -> (ly1 = [] -> is_edge (c, y) G = true) /\
     (forall (hly1: node) (tly1: nodes), rev ly1 = hly1 :: tly1 -> is_edge (hly1, y) G = true).
Proof.
  intros cy dy y ly1 ly2 py G Hpdy Hdir.
  split.
  ** pose proof mediator_means_edge_out. specialize H with (c := cy) (dy := dy) (py := py) (ly1 := ly1) (ly2 := ly2) (y := y) (G := G).
     apply H. apply Hpdy. apply Hdir.
  ** intros hly1 tly1 Hly1. assert (Hly1': ly1 = rev tly1 ++ [hly1]). { rewrite reverse_list_twice with (l := ly1). unfold node in *. rewrite Hly1. reflexivity. }
     rewrite Hly1' in *. symmetry in Hpdy. apply path_breaks_down_midpoint_vs_endpoint in Hpdy.
     destruct (rev ly2) as [| hly2 tly2] eqn:Hly2.
     - assert (H: y = dy /\ rev tly1 ++ [hly1] = py). { apply Hpdy. reflexivity. } destruct H as [H1 H2]. rewrite <- H1 in Hdir.
       assert (Hdir': is_directed_path_in_graph (hly1, y, []) G = true). { apply subpath_still_directed with (w := cy) (l1 := rev tly1) (l3 := py). split. apply H2. apply Hdir. }
       simpl in Hdir'. apply split_and_true in Hdir'. apply Hdir'.
     - assert (H: dy = hly2 /\ py = (rev tly1 ++ [hly1]) ++ [y] ++ rev tly2). { apply Hpdy. reflexivity. }
       destruct H as [H1 H2].
       assert (Hdir': is_directed_path_in_graph (hly1, dy, y :: rev tly2) G = true). { apply subpath_still_directed with (w := cy) (l1 := rev tly1) (l3 := py). split. rewrite <- app_assoc in H2. symmetry. apply H2. apply Hdir. }
       simpl in Hdir'. apply split_and_true in Hdir'. apply Hdir'.
Qed.

Lemma collider_becomes_mediator_when_concat_directed: forall (c x v y dy: node) (txv lv1 lv2 py ly1 ly2: nodes) (G: graph),
  In c (find_colliders_in_path (x, v, txv) G)
  -> lv1 ++ [c] ++ lv2 = txv
  -> acyclic_path_2 (x, v, txv)
  -> py ++ [dy] = ly1 ++ [y] ++ ly2
  -> is_directed_path_in_graph (c, dy, py) G = true
  -> In c (find_mediators_in_path (concat y c v (rev ly1) lv2) G).
Proof.
  intros cy x v y dy txv lv1 lv2 py ly1 ly2 G Hcol Htxv Hcyc Hpdy Hdir. apply mediator_means_edge_out with (c := cy) (G := G) in Hpdy.
  unfold concat. apply mediators_vs_edges_in_path. destruct ly1 as [| hlyd1 tlyd1] eqn:Hlyd1.
  ** exists y. destruct lv2 as [| hcy2 tcy2] eqn:Hlcyv2.
     --- exists v. split. simpl. repeat rewrite eqb_refl. reflexivity. right. split.
         +++ destruct Hpdy as [Hpdy _]. apply Hpdy. reflexivity.
         +++ apply collider_means_edge_in_end with (x := x) (v := v) (l1 := lv1). rewrite <- Htxv in Hcyc. apply Hcyc.
             rewrite <- Htxv in Hcol. apply Hcol.
     --- exists hcy2. split. apply sublist_breaks_down_list. exists []. exists (tcy2 ++ [v]). simpl. reflexivity. right. split.
         +++ destruct Hpdy as [Hpdy _]. apply Hpdy. reflexivity.
         +++ apply collider_means_edge_in with (x := x) (v := v) (l1 := lv1) (hl2 := hcy2) (tl2 := tcy2).
             rewrite <- Htxv in Hcyc. apply Hcyc.
             rewrite <- Htxv in Hcol. apply Hcol.
  ** exists hlyd1. destruct lv2 as [| hcy2 tcy2] eqn:Hlcyv2.
     --- exists v. split. apply sublist_breaks_down_list. exists (y :: rev tlyd1). exists []. simpl. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. right. split.
         +++ destruct Hpdy as [_ Hpdy]. apply Hpdy with (tly1 := tlyd1). reflexivity.
         +++ apply collider_means_edge_in_end with (x := x) (v := v) (l1 := lv1). rewrite <- Htxv in Hcyc. apply Hcyc.
             rewrite <- Htxv in Hcol. apply Hcol.
     --- exists hcy2. split. apply sublist_breaks_down_list. exists (y :: rev tlyd1). exists (tcy2 ++ [v]). simpl. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. right. split.
         +++ destruct Hpdy as [_ Hpdy]. apply Hpdy with (tly1 := tlyd1). reflexivity.
         +++ apply collider_means_edge_in with (x := x) (v := v) (l1 := lv1) (hl2 := hcy2) (tl2 := tcy2).
             rewrite <- Htxv in Hcyc. apply Hcyc.
             rewrite <- Htxv in Hcol. apply Hcol.
  ** apply Hdir.
Qed.


Lemma intersection_of_directed_paths_is_collider: forall (y c1 c2 d1 d2: node) (l1 l2 l1' l1'' l2' l2'': nodes) (G: graph),
  is_directed_path_in_graph (c1, d1, l1) G = true
  -> is_directed_path_in_graph (c2, d2, l2) G = true
  -> l1 ++ [d1] = l1' ++ [y] ++ l1''
  -> l2 ++ [d2] = l2' ++ [y] ++ l2''
  -> In y (find_colliders_in_path (c1, c2, l1' ++ [y] ++ rev l2') G).
Proof.
  intros y c1 c2 d1 d2 l1 l2 l1' l1'' l2' l2'' G Hd1 Hd2 Hl1 Hl2. symmetry in Hl1. symmetry in Hl2.
  apply colliders_vs_edges_in_path. apply path_breaks_down_midpoint_vs_endpoint in Hl1. apply path_breaks_down_midpoint_vs_endpoint in Hl2.
  assert (Hcy2: l2' = [] -> is_edge (c2, y) G = true).
  { intros Hl20. destruct (rev l2'') as [| hl2' tl2'] eqn:Hl2''.
    - assert (Hy: y = d2 /\ l2' = l2). { apply Hl2. reflexivity. } destruct Hy as [Hy1 Hy2]. rewrite <- Hy1 in Hd2. rewrite <- Hy2 in Hd2. rewrite Hl20 in Hd2.
      simpl in Hd2. apply split_and_true in Hd2. apply Hd2.
    - assert (Hy: d2 = hl2' /\ l2 = l2' ++ [y] ++ rev tl2'). { apply Hl2. reflexivity. } destruct Hy as [Hy1 Hy2]. rewrite Hy1 in Hd2. rewrite Hy2 in Hd2. rewrite Hl20 in Hd2.
      simpl in Hd2. apply split_and_true in Hd2. apply Hd2. }

  assert (Hcy2': forall (hl2: node) (tl2: nodes), l2' = rev tl2 ++ [hl2] -> is_edge (hl2, y) G = true).
  { intros hl2 tl2 Hl20. destruct (rev l2'') as [| hl2' tl2'] eqn:Hl2''.
    - assert (Hy: y = d2 /\ l2' = l2). { apply Hl2. reflexivity. } destruct Hy as [Hy1 Hy2]. rewrite <- Hy1 in Hd2. rewrite <- Hy2 in Hd2. rewrite Hl20 in Hd2.
      assert (Hd': is_directed_path_in_graph (hl2, y, []) G = true). { apply subpath_still_directed with (w := c2) (l1 := rev tl2) (l3 := rev tl2 ++ [hl2]). split. rewrite append_identity. reflexivity. apply Hd2. }
      simpl in Hd'. apply split_and_true in Hd'. apply Hd'.
    - assert (Hy: d2 = hl2' /\ l2 = l2' ++ [y] ++ rev tl2'). { apply Hl2. reflexivity. } destruct Hy as [Hy1 Hy2]. rewrite Hy2 in Hd2. rewrite Hl20 in Hd2.
      assert (Hd': is_directed_path_in_graph (hl2, d2, y :: rev tl2') G = true). { apply subpath_still_directed with (w := c2) (l1 := rev tl2) (l3 := rev tl2 ++ [hl2] ++ [y] ++ rev tl2'). split. reflexivity. rewrite app_assoc. apply Hd2. }
      simpl in Hd'. apply split_and_true in Hd'. apply Hd'. }

  destruct (rev l1') as [| hl1 tl1] eqn:Hl1'.
  - exists c1. assert (Hl10: l1' = []). { rewrite reverse_list_twice with (l := l1'). unfold node in *. rewrite Hl1'. reflexivity. }
    assert (Hcy1: is_edge (c1, y) G = true).
    { destruct (rev l1'') as [| hl1' tl1'] eqn:Hl1''.
      - assert (Hy: y = d1 /\ l1' = l1). { apply Hl1. reflexivity. } destruct Hy as [Hy1 Hy2]. rewrite <- Hy1 in Hd1. rewrite <- Hy2 in Hd1. rewrite Hl10 in Hd1.
        simpl in Hd1. apply split_and_true in Hd1. apply Hd1.
      - assert (Hy: d1 = hl1' /\ l1 = l1' ++ [y] ++ rev tl1'). { apply Hl1. reflexivity. } destruct Hy as [Hy1 Hy2]. rewrite Hy1 in Hd1. rewrite Hy2 in Hd1. rewrite Hl10 in Hd1.
        simpl in Hd1. apply split_and_true in Hd1. apply Hd1. } rewrite Hl10 in *.

    destruct (rev l2') as [| hl2 tl2] eqn:Hl2'.
    + exists c2. assert (Hl20: l2' = []). { rewrite reverse_list_twice with (l := l2'). unfold node in *. rewrite Hl2'. reflexivity. }
      split. simpl. repeat rewrite eqb_refl. reflexivity. split.
      * apply Hcy1.
      * apply Hcy2. apply Hl20.
    + exists hl2. split. simpl. repeat rewrite eqb_refl. reflexivity. split.
      * apply Hcy1.
      * apply Hcy2' with (tl2 := tl2). rewrite reverse_list_twice with (l := l2'). unfold node in *. rewrite Hl2'. simpl. reflexivity.
  - exists hl1.
    assert (Hl10: l1' = rev tl1 ++ [hl1]). { rewrite reverse_list_twice with (l := l1'). unfold node in *. rewrite Hl1'. simpl. reflexivity. }
    assert (Hcy1: is_edge (hl1, y) G = true).
    { destruct (rev l1'') as [| hl1' tl1'] eqn:Hl1''.
      - assert (Hy: y = d1 /\ l1' = l1). { apply Hl1. reflexivity. } destruct Hy as [Hy1 Hy2]. rewrite <- Hy1 in Hd1. rewrite <- Hy2 in Hd1. rewrite Hl10 in Hd1.
        assert (Hd': is_directed_path_in_graph (hl1, y, []) G = true). { apply subpath_still_directed with (w := c1) (l1 := rev tl1) (l3 := rev tl1 ++ [hl1]). split. rewrite append_identity. reflexivity. apply Hd1. }
        simpl in Hd'. apply split_and_true in Hd'. apply Hd'.
      - assert (Hy: d1 = hl1' /\ l1 = l1' ++ [y] ++ rev tl1'). { apply Hl1. reflexivity. } destruct Hy as [Hy1 Hy2]. rewrite Hy2 in Hd1. rewrite Hl10 in Hd1.
        assert (Hd': is_directed_path_in_graph (hl1, d1, y :: rev tl1') G = true). { apply subpath_still_directed with (w := c1) (l1 := rev tl1) (l3 := rev tl1 ++ [hl1] ++ [y] ++ rev tl1'). split. reflexivity. rewrite app_assoc. apply Hd1. }
        simpl in Hd'. apply split_and_true in Hd'. apply Hd'. }
    rewrite Hl10 in *.

    destruct (rev l2') as [| hl2 tl2] eqn:Hl2'.
    + exists c2. assert (Hl20: l2' = []). { rewrite reverse_list_twice with (l := l2'). unfold node in *. rewrite Hl2'. reflexivity. }
      split. apply sublist_breaks_down_list. exists (c1 :: rev tl1). exists []. rewrite <- app_assoc. rewrite <- app_assoc. simpl. reflexivity. split.
      * apply Hcy1.
      * apply Hcy2. apply Hl20.
    + exists hl2. split. apply sublist_breaks_down_list. exists (c1 :: rev tl1). exists (tl2 ++ [c2]). rewrite <- app_assoc. rewrite <- app_assoc. rewrite <- app_assoc. simpl. reflexivity.
      split.
      * apply Hcy1.
      * apply Hcy2' with (tl2 := tl2). rewrite reverse_list_twice with (l := l2'). unfold node in *. rewrite Hl2'. simpl. reflexivity.
Qed.


Theorem subpath_still_d_connected_gen: forall (w u v: node) (l1 l2 l3 Z: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3 /\ d_connected_2 (w, v, l3) G Z
  -> d_connected_2 (u, v, l2) G Z.
Proof.
  intros w u v l1 l2 l3 Z G. intros [Hl3 H].
  unfold d_connected_2 in *. repeat split.
  - destruct H as [H _].
    destruct (overlap Z (find_mediators_in_path (u, v, l2) G)) as [|] eqn:Hover.
    + apply overlap_has_member_in_common in Hover. destruct Hover as [x [HxZ Hx]].
      apply no_overlap_non_member with (x := x) in H.
      * exfalso. apply H. apply HxZ.
      * apply subpath_preserves_mediators with (u := u) (l1 := l1) (l2 := l2). split. apply Hl3. left. apply Hx.
    + reflexivity.
  - destruct H as [_ [H _]].
    destruct (overlap Z (find_confounders_in_path (u, v, l2) G)) as [|] eqn:Hover.
    + apply overlap_has_member_in_common in Hover. destruct Hover as [x [HxZ Hx]].
      apply no_overlap_non_member with (x := x) in H.
      * exfalso. apply H. apply HxZ.
      * apply subpath_preserves_confounders with (u := u) (l1 := l1) (l2 := l2). split. apply Hl3. apply Hx.
    + reflexivity.
  - unfold all_colliders_have_descendant_conditioned_on in *. apply forallb_true_iff_mem. intros x Hx.
    destruct H as [_ [_ H]]. apply forallb_true with (x := x) in H.
    + apply H.
    + apply subpath_preserves_colliders with (u := u) (l1 := l1) (l2 := l2). split. apply Hl3. left. apply Hx.
Qed.


Lemma subpath_still_d_connected: forall (G: graph) (u v h: node) (t Z: nodes),
  d_connected_2 (u, v, h :: t) G Z
  -> d_connected_2 (h, v, t) G Z.
Proof.
  intros G u v h t Z H.
  unfold d_connected_2 in *. repeat split.
  - destruct H as [H _].
    destruct (overlap Z (find_mediators_in_path (h, v, t) G)) as [|] eqn:Hover.
    + apply overlap_has_member_in_common in Hover. destruct Hover as [x [HxZ Hx]].
      apply no_overlap_non_member with (x := x) in H.
      * exfalso. apply H. apply HxZ.
      * apply mediators_vs_edges_in_path. apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [Hyz [[Hyx Hxz] | [Hxy Hzx]]]]].
        { exists y. exists z. repeat split.
          -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l2 [l3 Hl23]].
             exists (u :: l2). exists l3. simpl. rewrite <- Hl23. simpl. reflexivity.
          -- left. split. apply Hyx. apply Hxz. }
        { exists y. exists z. repeat split.
          -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l2 [l3 Hl23]].
             exists (u :: l2). exists l3. simpl. rewrite <- Hl23. simpl. reflexivity.
          -- right. split. apply Hxy. apply Hzx. }
    + reflexivity.
  - destruct H as [_ [H _]].
    destruct (overlap Z (find_confounders_in_path (h, v, t) G)) as [|] eqn:Hover.
    + apply overlap_has_member_in_common in Hover. destruct Hover as [x [HxZ Hx]].
      apply no_overlap_non_member with (x := x) in H.
      * exfalso. apply H. apply HxZ.
      * apply confounders_vs_edges_in_path. apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hyz [Hyx Hxz]]]].
        exists y. exists z. repeat split.
        -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l2 [l3 Hl23]].
           exists (u :: l2). exists l3. simpl. rewrite <- Hl23. simpl. reflexivity.
        -- apply Hyx.
        -- apply Hxz.
    + reflexivity.
  - unfold all_colliders_have_descendant_conditioned_on in *. apply forallb_true_iff_mem. intros x Hx.
    destruct H as [_ [_ H]]. apply forallb_true with (x := x) in H.
    + apply H.
    + apply colliders_vs_edges_in_path. apply colliders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hyz [Hyx Hxz]]]].
        exists y. exists z. repeat split.
        -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l2 [l3 Hl23]].
           exists (u :: l2). exists l3. simpl. rewrite <- Hl23. simpl. reflexivity.
        -- apply Hyx.
        -- apply Hxz.
Qed.

Lemma directed_path_can_be_acyclic: forall (G: graph) (u v: node) (l: nodes),
  is_directed_path_in_graph (u, v, l) G = true
  -> exists (l': nodes), is_directed_path_in_graph (u, v, l') G = true /\ acyclic_path_2 (u, v, l')
      /\ subset l' l = true.
Proof.
  intros G u v l H.
Admitted.

Lemma colliders_have_unblocked_path_to_descendant: forall (G: graph) (Z: nodes) (c: node) (p: path),
  In c (find_colliders_in_path p G)
  -> d_connected_2 p G Z
  -> In c Z \/ (~In c Z /\ exists (z: node) (dp: nodes), is_directed_path_in_graph (c, z, dp) G = true /\ acyclic_path_2 (c, z, dp) /\ overlap dp Z = false /\ In z Z).
Proof.
  intros G Z c p Hc Hp.
  unfold d_connected_2 in Hp. destruct Hp as [_ [_ Hp]]. unfold all_colliders_have_descendant_conditioned_on in Hp.
  apply forallb_true_iff_mem with (x := c) in Hp.
  - unfold some_descendant_in_Z_bool in Hp. apply overlap_has_member_in_common in Hp. destruct Hp as [d [Hd HdZ]].
    apply find_descendants_correct in Hd. destruct Hd as [Hcd | Hd].
    + left. rewrite Hcd. apply HdZ.
    + destruct Hd as [dp [Hdp Hcd]]. destruct dp as [[c' d'] dp]. apply path_start_end_equal in Hcd. destruct Hcd as [Hc' Hd'].
      rewrite Hc' in *. rewrite Hd' in *. clear Hc'. clear Hd'.

      remember (length dp) as n.
      assert (Hn: exists (n': nat), n' = length dp /\ n' <= n). { exists n. split. apply Heqn. lia. }
      clear Heqn.

      generalize dependent d. generalize dependent dp. induction n as [| n' IH].
      * intros dp Hn d Hdp HdZ. destruct Hn as [n' [Hn' H0]]. assert (Hn0: n' = 0). { lia. }
        assert (Hl: dp = []). { destruct dp as [| hdp tdp]. reflexivity. rewrite Hn0 in Hn'. simpl in Hn'. discriminate Hn'. }
        destruct (member c Z) as [|] eqn:HcZ.
        -- left. apply member_In_equiv. apply HcZ.
        -- right. split. apply member_In_equiv_F. apply HcZ. exists d. exists []. split. rewrite Hl in Hdp. apply Hdp. repeat split.
           ++ intros Hcd. rewrite Hcd in HcZ. apply member_In_equiv_F in HcZ. apply HcZ. apply HdZ.
           ++ intros F. apply F.
           ++ intros F. apply F.
           ++ apply HdZ.
      * intros dp Hn d Hdp HdZ. destruct (overlap dp Z) as [|] eqn:Hover.
        -- apply overlap_has_member_in_common in Hover. destruct Hover as [z [Hz HzZ]]. apply membership_splits_list in Hz.
           destruct Hz as [dp1 [dp2 Hdp12]].
           specialize IH with (dp := dp1) (d := z). apply IH.
           ++ exists (length dp1). split. reflexivity. destruct Hn as [n [Hndp Hnn']].
              assert (Hlen: length (dp1 ++ [z] ++ dp2) = n). { rewrite Hdp12. symmetry. apply Hndp. }
              rewrite app_length in Hlen. simpl in Hlen. lia.
           ++ apply subpath_still_directed_2 with (v := d) (l2 := dp2) (l3 := dp). split. apply Hdp12. apply Hdp.
           ++ apply HzZ.
        -- destruct (member c Z) as [|] eqn:HcZ.
           ++ left. apply member_In_equiv. apply HcZ.
           ++ right. split. apply member_In_equiv_F. apply HcZ.
              apply directed_path_can_be_acyclic in Hdp. destruct Hdp as [dp' Hdp].
              exists d. exists dp'. split. apply Hdp. split. apply Hdp. split.
              ** apply no_overlap_non_member. intros x Hx1 Hx2. apply no_overlap_non_member with (x := x) in Hover.
                 apply Hover. apply subset_larger_set_membership with (l1 := dp'). split. apply Hdp. apply Hx2. apply Hx1.
              ** apply HdZ.
  - apply Hc.
Qed.

(* does not include the collider *)
Fixpoint get_collider_descendants_from_assignments (D: assignments (nodes * node)) (col: nodes): option nodes :=
  match col with
  | [] => Some []
  | h :: t => match (get_assigned_value D h) with
              | Some x => match (get_collider_descendants_from_assignments D t) with
                          | Some r => if (snd x =? h) then Some r else Some ((fst x) ++ (snd x) :: r)
                          | None => None
                          end
              | None => None
              end
  end.

Lemma collider_descendants_from_assignments_existence: forall (D: assignments (nodes * node)) (G: graph) (p: path),
  (forall (c: node), In c (find_colliders_in_path p G)
    -> get_assigned_value D c = Some ([], c)
       \/
       exists (p: nodes) (d: node), get_assigned_value D c = Some (p, d))
  -> exists (L: nodes), get_collider_descendants_from_assignments D (find_colliders_in_path p G) = Some L.
Proof.
  intros D G p H.
  induction (find_colliders_in_path p G) as [| h t IH].
  - simpl. exists []. reflexivity.
  - simpl.
    assert (Hh: In h (h :: t)). { left. reflexivity. } apply H in Hh.
    assert (Hind: exists L : nodes, get_collider_descendants_from_assignments D t = Some L).
    { apply IH. intros c Hc. apply H. right. apply Hc. }
    destruct Hind as [L HL].
    destruct Hh as [Hh | Hh].
    + rewrite Hh. simpl. rewrite eqb_refl.
      exists L. rewrite HL. reflexivity.
    + destruct Hh as [pa [d Hpd]]. rewrite Hpd. rewrite HL. simpl. destruct (d =? h) as [|]. exists L. reflexivity.
      exists (pa ++ d :: L). reflexivity.
Qed.

Fixpoint get_collider_descendants_for_subpath (D: assignments (nodes * node)) (col: nodes): option (assignments (nodes * node)) :=
  match col with
  | [] => Some []
  | h :: t => match (get_assigned_value D h) with
              | Some x => match (get_collider_descendants_for_subpath D t) with
                          | Some r => Some ((h, x) :: r)
                          | None => None
                          end
              | None => None
              end
  end.

Lemma collider_descendants_is_assignment_for: forall (D: assignments (nodes * node)) (col L: nodes),
  get_collider_descendants_from_assignments D col = Some L
  -> is_assignment_for D col = true.
Proof.
  intros D col L H.
  generalize dependent L. induction col as [| h t IH].
  - intros L H. simpl. reflexivity.
  - intros L H. simpl. simpl in H. destruct (get_assigned_value D h) as [x|] eqn:Hx.
    + apply split_and_true. split.
      * apply assigned_is_true. exists x. apply Hx.
      * destruct (get_collider_descendants_from_assignments D t) as [r|] eqn:Hr.
        -- destruct (snd x =? h) as [|].
           ++ inversion H. apply IH with (L := r). reflexivity.
           ++ apply IH with (L := r). reflexivity.
        -- discriminate H.
    + discriminate H.
Qed.

Lemma collider_subpath_is_exact_assignment: forall (D D': assignments (nodes * node)) (col: nodes),
  get_collider_descendants_for_subpath D col = Some D'
  -> is_exact_assignment_for D' col.
Proof.
  intros D D' col H.
  unfold is_exact_assignment_for. split.
  - generalize dependent D'. induction col as [| h t IH].
    + simpl. reflexivity.
    + intros D' H. simpl. simpl in H. destruct (get_assigned_value D h) as [x|] eqn:Hx.
      * destruct (get_collider_descendants_for_subpath D t) as [r|] eqn:Hr.
        -- apply split_and_true. split.
           ++ inversion H. simpl. rewrite eqb_refl. reflexivity.
           ++ inversion H. apply is_assignment_for_cat. apply IH. reflexivity.
        -- discriminate H.
      * discriminate H.
  - intros u Hu. generalize dependent D'. induction col as [| h t IH].
    + intros D' H. simpl in H. inversion H. simpl. reflexivity.
    + intros D' H. simpl in H. destruct (get_assigned_value D h) as [x|] eqn:Hx.
      * destruct (get_collider_descendants_for_subpath D t) as [r|] eqn:Hr.
        -- inversion H. simpl. simpl in Hu. destruct (h =? u) as [|] eqn:Hhu. discriminate Hu. rewrite eqb_sym in Hhu. rewrite Hhu. simpl.
           apply IH. apply Hu. reflexivity.
        -- discriminate H.
      * discriminate H.
Qed.

Lemma collider_descendants_for_subpath_existence: forall (D: assignments (nodes * node)) (G: graph) (u v m: node) (l1 l2 L: nodes),
  get_collider_descendants_from_assignments D (find_colliders_in_path (concat u m v l1 l2) G) = Some L
  -> exists (D': assignments (nodes * node)), get_collider_descendants_for_subpath D (find_colliders_in_path (u, m, l1) G) = Some D'.
Proof.
  intros D G u v m l1 l2 L H.
  assert (Hc: forall (c: node), In c (find_colliders_in_path (u, m, l1) G) -> In c (find_colliders_in_path (concat u m v l1 l2) G)).
  { intros c Hc. apply subpath_preserves_colliders with (u := m) (l1 := l1) (l2 := l2). split. reflexivity. right. apply Hc. }

  induction (find_colliders_in_path (u, m, l1) G) as [| h t IH].
  - simpl. exists []. reflexivity.
  - simpl.
    assert (Hind: exists D' : assignments (nodes * node), get_collider_descendants_for_subpath D t = Some D').
    { apply IH. intros c Hc'. apply Hc. right. apply Hc'. }
    destruct Hind as [D' HD'].
    assert (Hh: exists x, get_assigned_value D h = Some x).
    { apply assigned_has_value with (L := (find_colliders_in_path (concat u m v l1 l2) G)). split.
      - apply Hc. left. reflexivity.
      - apply collider_descendants_is_assignment_for with (L := L). apply H. }
    destruct Hh as [x Hh]. rewrite Hh. exists ((h, x) :: D'). rewrite HD'. reflexivity.
Qed.

Lemma collider_descendants_for_subpath_existence_2: forall (D: assignments (nodes * node)) (G: graph) (u v m: node) (l1 l2 L: nodes),
  get_collider_descendants_from_assignments D (find_colliders_in_path (concat u m v l1 l2) G) = Some L
  -> exists (D': assignments (nodes * node)), get_collider_descendants_for_subpath D (find_colliders_in_path (m, v, l2) G) = Some D'.
Proof.
  intros D G u v m l1 l2 L H.
  assert (Hc: forall (c: node), In c (find_colliders_in_path (m, v, l2) G) -> In c (find_colliders_in_path (concat u m v l1 l2) G)).
  { intros c Hc. apply subpath_preserves_colliders with (u := m) (l1 := l1) (l2 := l2). split. reflexivity. left. apply Hc. }

  induction (find_colliders_in_path (m, v, l2) G) as [| h t IH].
  - simpl. exists []. reflexivity.
  - simpl.
    assert (Hind: exists D' : assignments (nodes * node), get_collider_descendants_for_subpath D t = Some D').
    { apply IH. intros c Hc'. apply Hc. right. apply Hc'. }
    destruct Hind as [D' HD'].
    assert (Hh: exists x, get_assigned_value D h = Some x).
    { apply assigned_has_value with (L := (find_colliders_in_path (concat u m v l1 l2) G)). split.
      - apply Hc. left. reflexivity.
      - apply collider_descendants_is_assignment_for with (L := L). apply H. }
    destruct Hh as [x Hh]. rewrite Hh. exists ((h, x) :: D'). rewrite HD'. reflexivity.
Qed.

Lemma collider_descendants_preserved_for_subpath: forall (D D': assignments (nodes * node)) (col p: nodes) (c d: node),
  get_collider_descendants_for_subpath D col = Some D'
  -> get_assigned_value D' c = Some (p, d)
  -> get_assigned_value D c = Some (p, d).
Proof.
  intros D D' col p c d H1 H2.
  generalize dependent D'. induction col as [| h t IH].
  - intros D' H1 H2. simpl in H1. inversion H1. rewrite <- H0 in H2. simpl in H2. discriminate H2.
  - intros D' H1 H2. simpl in H1. destruct (get_assigned_value D h) as [x|] eqn:Hx.
    + destruct (get_collider_descendants_for_subpath D t) as [r|] eqn:Hr.
      * inversion H1. rewrite <- H0 in H2. simpl in H2. destruct (h =? c) as [|] eqn:Hhc.
        -- apply eqb_eq in Hhc. rewrite <- Hhc. inversion H2. rewrite <- H3. apply Hx.
        -- apply IH with (D' := r). reflexivity. apply H2.
      * discriminate H1.
    + discriminate H1.
Qed.

Lemma collider_descendants_preserved_for_subpath_2: forall (D D': assignments (nodes * node)) (col p: nodes) (c d: node),
  get_collider_descendants_for_subpath D col = Some D'
  -> get_assigned_value D c = Some (p, d)
  -> In c col
  -> get_assigned_value D' c = Some (p, d).
Proof.
  intros D D' col p c d H1 H2 H3.
  generalize dependent D'. induction col as [| h t IH].
  - intros D' H1. exfalso. apply H3.
  - intros D' H1. simpl in H1. destruct (get_assigned_value D h) as [x|] eqn:Hx.
    + destruct (get_collider_descendants_for_subpath D t) as [r|] eqn:Hr.
      * inversion H1. simpl. destruct (h =? c) as [|] eqn:Hhc.
        -- apply eqb_eq in Hhc. rewrite Hhc in Hx. rewrite H2 in Hx. symmetry. apply Hx.
        -- apply IH with (D' := r). simpl in H3. destruct H3 as [H3 | H3]. rewrite H3 in Hhc. rewrite eqb_refl in Hhc. discriminate Hhc.
           apply H3. reflexivity.
      * discriminate H1.
    + discriminate H1.
Qed.


Lemma collider_descendants_from_assignments_mem: forall (D: assignments (nodes * node)) (G: graph) (p': path) (L p: nodes) (c d: node),
  In c (find_colliders_in_path p' G)
  -> get_assigned_value D c = Some (p, d) /\ d =? c = false
  -> get_collider_descendants_from_assignments D (find_colliders_in_path p' G) = Some L
  -> forall (u: node), In u (p ++ [d]) -> In u L.
Proof.
  intros D G p' L p c d. intros Hc [Hpd Hdc] HL. intros u Hu.
  generalize dependent L. induction (find_colliders_in_path p' G) as [| h t IH].
  - intros L HL. exfalso. apply Hc.
  - intros L HL. destruct Hc as [Hc | Hc].
    + simpl in HL. rewrite <- Hc in *. rewrite Hpd in HL. simpl in HL. rewrite Hdc in HL.
      destruct (get_collider_descendants_from_assignments D t) as [r|].
      * inversion HL. apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]]. apply membership_append. apply Hu.
        apply membership_append_r. left. apply Hu. exfalso. apply Hu.
      * discriminate HL.
    + simpl in HL. destruct (get_assigned_value D h) as [x|].
      * destruct (get_collider_descendants_from_assignments D t) as [r|] eqn:Hr.
        -- specialize IH with (L := r). apply IH in Hc. destruct (snd x =? h) as [|].
           ++ inversion HL. rewrite <- H0. apply Hc.
           ++ inversion HL. apply membership_append_r. right. apply Hc.
           ++ reflexivity.
        -- discriminate HL.
      * discriminate HL.
Qed.

Lemma collider_descendants_from_assignments_belong_to_collider: forall (D: assignments (nodes * node)) (G: graph) (p': path) (L: nodes) (u: node),
  get_collider_descendants_from_assignments D (find_colliders_in_path p' G) = Some L
  -> In u L
  -> exists (c d: node) (p: nodes), In c (find_colliders_in_path p' G)
      /\ get_assigned_value D c = Some (p, d) /\ d =? c = false
      /\ In u (p ++ [d]).
Proof.
  intros D G p' L u. intros HL Hu.
  generalize dependent L. induction (find_colliders_in_path p' G) as [| h t IH].
  - intros L HL Hu. exfalso. simpl in HL. inversion HL. rewrite <- H0 in Hu. apply Hu.
  - intros L HL Hu. simpl in HL. destruct (get_assigned_value D h) as [x|] eqn:Hx.
    + destruct (get_collider_descendants_from_assignments D t) as [r|] eqn:Hr.
      * destruct (snd x =? h) as [|] eqn:Hhx.
        -- inversion HL. apply IH in Hu.
           ++ destruct Hu as [c [d [p Hu]]]. exists c. exists d. exists p. split. right. apply Hu. apply Hu.
           ++ f_equal. apply H0.
        -- inversion HL. rewrite <- H0 in Hu. apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]].
           ++ exists h. exists (snd x). exists (fst x). split. left. reflexivity. split. destruct x as [x1 x2]. simpl. apply Hx.
              split. apply Hhx. apply membership_append. apply Hu.
           ++ exists h. exists (snd x). exists (fst x). split. left. reflexivity. split. destruct x as [x1 x2]. simpl. apply Hx.
              split. apply Hhx. apply membership_append_r. left. apply Hu.
           ++ apply IH in Hu. destruct Hu as [c [d [p Hu]]]. exists c. exists d. exists p. split. right. apply Hu. apply Hu.
              reflexivity.
      * discriminate HL.
    + discriminate HL.
Qed.

Fixpoint path_out_of_node_nodes (p: nodes) (u: node) (G: graph): option bool :=
  match p with
  | [] => None
  | h :: t => match t with
              | [] => None
              | h' :: t' => if (h =? u) then (if (edge_in_graph (h, h') G) then Some true else Some false)
                            else path_out_of_node_nodes t u G
              end
  end.

Lemma path_out_of_node_mem: forall (p: nodes) (u: node) (G: graph) (b: bool),
  path_out_of_node_nodes p u G = Some b
  -> In u p.
Proof.
  intros p u G b H.
  induction p as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. destruct t as [| h' t'].
    + discriminate H.
    + destruct (h =? u) as [|] eqn:Hhu.
      * left. apply eqb_eq. apply Hhu.
      * right. apply IH. apply H.
Qed.

Definition path_out_of_node (u: node) (p: path) (G: graph) : option bool :=
  path_out_of_node_nodes ((path_start p) :: (path_int p) ++ [path_end p]) u G.

Lemma path_out_of_node_cat: forall (u v h w: node) (t: nodes) (G: graph),
  (w =? u) = false
  -> path_out_of_node w (u, v, h :: t) G = path_out_of_node w (h, v, t) G.
Proof.
  intros u v h w t G H. unfold path_out_of_node. simpl. rewrite eqb_sym in H. rewrite H. reflexivity.
Qed.

Lemma path_out_of_node_mem_2: forall (u v w: node) (l: nodes) (G: graph),
  In w (u :: l)
  -> exists (b: bool), path_out_of_node w (u, v, l) G = Some b.
Proof.
  intros u v w l G H.
  unfold path_out_of_node. simpl.
  destruct (w =? u) as [|] eqn:Hwu.
  - apply eqb_eq in Hwu. destruct l as [| h t].
    + simpl. rewrite <- Hwu. rewrite eqb_refl. exists (edge_in_graph (w, v) G). destruct (edge_in_graph (w, v) G). reflexivity. reflexivity.
    + simpl. rewrite <- Hwu. rewrite eqb_refl. exists (edge_in_graph (w, h) G). destruct (edge_in_graph (w, h) G). reflexivity. reflexivity.
  - destruct H as [H | H]. rewrite H in Hwu. rewrite eqb_refl in Hwu. discriminate Hwu.
    generalize dependent u. induction l as [| h t IH].
    * exfalso. apply H.
    * intros u Hwu. simpl. rewrite eqb_sym in Hwu. rewrite Hwu. destruct (w =? h) as [|] eqn:Hwh.
      + apply eqb_eq in Hwh. destruct t as [| h' t'].
        ** simpl. rewrite <- Hwh. rewrite eqb_refl. exists (edge_in_graph (w, v) G). destruct (edge_in_graph (w, v) G). reflexivity. reflexivity.
        ** simpl. rewrite <- Hwh. rewrite eqb_refl. exists (edge_in_graph (w, h') G). destruct (edge_in_graph (w, h') G). reflexivity. reflexivity.
      + apply IH.
        ** destruct H as [H | H]. rewrite H in Hwh. rewrite eqb_refl in Hwh. discriminate Hwh. apply H.
        ** apply Hwh.
Qed.

Theorem superpath_preserves_path_out_of_node: forall (w u v a: node) (l1 l2 l3: nodes) (G: graph) (b: bool),
  l1 ++ [u] ++ l2 = l3
  -> path_out_of_node a (w, v, l3) G = Some b
  -> acyclic_path_2 (w, v, l3)
  -> In a (u :: l2)
  -> path_out_of_node a (u, v, l2) G = Some b.
Proof.
  intros w u v a l1 l2 l3 G b. intros Hl Ha Hcyc Hmem. unfold path_out_of_node in *.
  assert (Hwa: (w =? a) = false).
  { destruct (w =? a) as [|] eqn:Hwa.
    - apply eqb_eq in Hwa. exfalso. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. rewrite <- Hl. apply membership_append_r. rewrite Hwa. apply Hmem.
    - reflexivity. }

  generalize dependent l3. generalize dependent w. induction l1 as [| h1 t1 IH].
  - intros w Hwa l3 Hl Hb Hcyc. simpl in Hl. simpl in Hb. simpl. rewrite <- Hl in Hb. simpl in Hb.
    rewrite Hwa in Hb. apply Hb.
  - intros w Hwa l3 Hl Hb Hcyc. rewrite <- Hl in Hb. simpl in Hb. simpl. rewrite Hwa in Hb. apply IH with (w := h1) (l3 := t1 ++ [u] ++ l2).
    + destruct (h1 =? a) as [|] eqn:Hh1a.
      * apply eqb_eq in Hh1a. apply acyclic_path_count with (x := a) in Hcyc. rewrite <- Hl in Hcyc. rewrite Hh1a in Hcyc.
        simpl in Hcyc. rewrite eqb_refl in Hcyc. rewrite Hwa in Hcyc. rewrite count_app in Hcyc. rewrite count_app in Hcyc.
        apply member_count_at_least_1 in Hmem. lia.
        right. rewrite <- Hl. left. apply Hh1a.
      * reflexivity.
    + reflexivity.
    + apply Hb.
    + rewrite <- Hl in Hcyc. apply acyclic_path_cat with (u := w). apply Hcyc.
Qed.

Theorem subpath_preserves_path_out_of_node: forall (w u v a: node) (l1 l2 l3: nodes) (G: graph) (b: bool),
  l1 ++ [u] ++ l2 = l3 /\ path_out_of_node a (u, v, l2) G = Some b
  -> acyclic_path_2 (w, v, l3)
  -> path_out_of_node a (w, v, l3) G = Some b.
Proof.
  intros w u v a l1 l2 l3 G b. intros [Hl Hb] Hcyc. unfold path_out_of_node in *.
  assert (Hwa: (w =? a) = false).
  { destruct (w =? a) as [|] eqn:Hwa.
    - apply eqb_eq in Hwa. apply path_out_of_node_mem in Hb. unfold acyclic_path_2 in Hcyc. rewrite app_comm_cons in Hb.
      apply membership_append_or in Hb. destruct Hb as [Hb | Hb].
      + destruct Hcyc as [_ [Hcyc _]]. exfalso. apply Hcyc. rewrite <- Hl. simpl in Hb. apply membership_append_r.
        destruct Hb as [Hb | Hb]. left. rewrite Hwa. apply Hb. right. simpl. rewrite Hwa. apply Hb.
      + exfalso. simpl in Hb. destruct Hcyc as [Hcyc _]. apply Hcyc. destruct Hb as [Hb | Hb]. rewrite Hb. apply Hwa. exfalso. apply Hb.
    - reflexivity. }

  generalize dependent l3. generalize dependent w. induction l1 as [| h1 t1 IH].
  - intros w Hwa l3 Hl Hcyc. simpl in Hl. simpl in Hb. simpl. rewrite <- Hl. simpl.
    rewrite Hwa. apply Hb.
  - intros w Hwa l3 Hl Hcyc. rewrite <- Hl. simpl. rewrite Hwa. apply IH with (w := h1) (l3 := t1 ++ [u] ++ l2).
    + destruct (h1 =? a) as [|] eqn:Hh1a.
      * apply eqb_eq in Hh1a. apply path_out_of_node_mem in Hb. unfold acyclic_path_2 in Hcyc. rewrite app_comm_cons in Hb.
        apply membership_append_or in Hb. destruct Hb as [Hb | Hb].
        -- destruct Hcyc as [_ [_ [_ Hcyc]]]. rewrite <- Hl in Hcyc. simpl in Hcyc. apply split_and_true in Hcyc. destruct Hcyc as [Hcyc _].
           apply negb_true_iff in Hcyc. apply member_In_equiv_F in Hcyc. exfalso. apply Hcyc. destruct Hb as [Hb | Hb].
           ++ simpl in Hb. apply membership_append_r. left. rewrite Hh1a. apply Hb.
           ++ simpl in Hb. apply membership_append_r. right. rewrite Hh1a. apply Hb.
        -- destruct Hcyc as [_ [_ [Hcyc _]]]. rewrite <- Hl in Hcyc. simpl in Hcyc. exfalso. apply Hcyc. left. simpl in Hb.
           destruct Hb as [Hb | Hb]. rewrite Hb. apply Hh1a. exfalso. apply Hb.
      * reflexivity.
    + reflexivity.
    + rewrite <- Hl in Hcyc. apply acyclic_path_cat with (u := w). apply Hcyc.
Qed.

Lemma path_out_not_collider: forall (x u v: node) (l: nodes) (G: graph),
  path_out_of_node x (u, v, l) G = Some true
  -> G_well_formed G = true /\ contains_cycle G = false
  -> acyclic_path_2 (u, v, l)
  -> ~ In x (find_colliders_in_path (u, v, l) G).
Proof.
  intros x u v l G Hout HG Hcyc Hmem.
  generalize dependent u. induction l as [| h t IH].
  - intros u Hout Hcyc Hmem. simpl in Hmem. apply Hmem.
  - intros u Hout Hcyc Hmem. unfold path_out_of_node in Hout. simpl in Hout. destruct (u =? x) as [|] eqn:Hux.
    + assert (Hmemx: In x (h :: t)).
      { apply colliders_vs_edges_in_path in Hmem. destruct Hmem as [y [z [Hsub Hedge]]]. apply end_of_sublist_still_sublist in Hsub.
        apply first_elt_of_sublist_not_last_elt_gen in Hsub. apply Hsub. }
      unfold acyclic_path_2 in Hcyc. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. apply eqb_eq in Hux. rewrite Hux. apply Hmemx.
    + simpl in Hmem. destruct t as [| ht tt].
      * simpl in Hmem. destruct (is_collider_bool u v h G) as [|] eqn:Hcol.
        -- destruct Hmem as [Hxh | F]. simpl in Hout. rewrite Hxh in Hout. rewrite eqb_refl in Hout. destruct (edge_in_graph (x, v) G) as [|] eqn:Hhv.
           ++ unfold is_collider_bool in Hcol. apply split_and_true in Hcol. destruct Hcol as [_ Hcol]. rewrite Hxh in Hcol.
              apply acyclic_no_two_cycle in Hcol. rewrite edge_in_graph_equiv in Hcol. rewrite Hcol in Hhv. discriminate Hhv. apply HG. apply HG.
           ++ discriminate Hout.
           ++ apply F.
        -- apply Hmem.
      * simpl in Hmem. destruct (is_collider_bool u ht h G) as [|] eqn:Hcol.
        -- destruct (h =? x) as [|] eqn:Hxh.
           { apply eqb_eq in Hxh.
             simpl in Hout. destruct (edge_in_graph (h, ht) G) as [|] eqn:Hhv.
             ++ unfold is_collider_bool in Hcol. apply split_and_true in Hcol. destruct Hcol as [_ Hcol].
                apply acyclic_no_two_cycle in Hcol. rewrite edge_in_graph_equiv in Hcol. rewrite Hcol in Hhv. discriminate Hhv. apply HG. apply HG.
             ++ discriminate Hout. }
           { destruct Hmem as [F | Hmem]. rewrite F in Hxh. rewrite eqb_refl in Hxh. discriminate Hxh.
             apply IH with (u := h).
             * unfold path_out_of_node. simpl. rewrite Hxh. apply Hout.
             * apply acyclic_path_cat with (u := u). apply Hcyc.
             * apply Hmem. }
        -- apply IH with (u := h).
           ++ apply Hout.
           ++ apply acyclic_path_cat with (u := u). apply Hcyc.
           ++ apply Hmem.
Qed.

Definition descendant_paths_disjoint (D: assignments (nodes * node)) (u v: node) (l': nodes) (G: graph) (Z: nodes): Prop :=
  is_exact_assignment_for D (find_colliders_in_path (u, v, l') G) /\
  forall (c: node), In c (find_colliders_in_path (u, v, l') G)
      -> get_assigned_value D c = Some ([], c) /\ In c Z (* c is conditioned on, don't need path *)
         \/
         exists (p: nodes) (d: node), get_assigned_value D c = Some (p, d)
           /\ In d Z /\ is_directed_path_in_graph (c, d, p) G = true (* c has path p to conditioned descendant d *)
                     /\ acyclic_path_2 (c, d, p) (* directed path is acyclic, not a huge constraint *)
           /\ overlap (c :: p) Z = false (* d is the first node in the path that is conditioned on *)
           /\ overlap (p ++ [d]) (u :: l' ++ [v]) = false (* the descendant does not intersect the u-v path *)
           /\ forall (c' d': node) (p': nodes), (c =? c' = false) /\ get_assigned_value D c' = Some (p', d')
              -> overlap (c :: p ++ [d]) (c' :: p' ++ [d']) = false. (* the descendant path does not intersect any other descendant path *)


Theorem exists_d_connected_path_with_collider_descendants_disjoint: forall (G: graph) (Z l: nodes) (u v: node),
  G_well_formed G = true /\ contains_cycle G = false
  -> acyclic_path_2 (u, v, l)
  -> d_connected_2 (u, v, l) G Z
  -> is_path_in_graph (u, v, l) G = true
  -> exists (l': nodes),
     acyclic_path_2 (u, v, l') /\ d_connected_2 (u, v, l') G Z /\ is_path_in_graph (u, v, l') G = true
     /\
     (forall (w: node), (node_in_path w (u, v, l') = true /\ node_in_path w (u, v, l) = false) \/
                        (exists (b: bool), path_out_of_node w (u, v, l) G = Some b /\ path_out_of_node w (u, v, l') G = Some (negb b))
      -> ((exists (du: node) (pu: nodes), is_directed_path_in_graph (w, du, pu) G = true /\ In du Z /\ ~In w Z)
          \/ path_out_of_node w (u, v, l') G <> Some true /\ In w Z)
           (* if path changed direction into u, then it's due to a descendant path *)
         /\ (path_out_of_node w (u, v, l') G = Some true -> ~(In w Z)))
     /\
     exists (D: assignments (nodes * node)), descendant_paths_disjoint D u v l' G Z.
Proof.
  intros G Z l u v HG. unfold descendant_paths_disjoint.

  generalize dependent u. induction l as [| h t IH].
  - intros u Hcyc Hconn Hpath.
    exists []. split. apply Hcyc. split. apply Hconn. split. apply Hpath. split.
    + intros w Hw. destruct Hw as [[Hw1 Hw2] | Hw].
      * rewrite Hw1 in Hw2. discriminate Hw2.
      * destruct Hw as [b [Hw1 Hw2]]. rewrite Hw1 in Hw2. inversion Hw2. destruct b as [|]. discriminate H0. discriminate H0.
    + exists []. split.
      * unfold is_exact_assignment_for. simpl. split. reflexivity. reflexivity.
      * intros c Hc. simpl in Hc. exfalso. apply Hc.
  - intros u Hcyc Hconn Hpath.
    specialize IH with (u := h).
    assert (Hcyc': acyclic_path_2 (h, v, t)). { apply acyclic_path_cat with (u := u). apply Hcyc. }
    apply IH in Hcyc'. clear IH.
    + destruct Hcyc' as [lhv Hlhv]. rewrite <- and_assoc in Hlhv. rewrite <- and_assoc in Hlhv. destruct Hlhv as [Hlhv [Hout [Dh HDh]]].
      assert (HLh: exists (Lh: nodes), get_collider_descendants_from_assignments Dh (find_colliders_in_path (h, v, lhv) G) = Some Lh).
      { apply collider_descendants_from_assignments_existence. intros c Hc. apply HDh in Hc. destruct Hc as [Hc | Hc].
        - left. apply Hc.
        - destruct Hc as [p [d Hc]]. right. exists p. exists d. apply Hc. }
      destruct HLh as [L HLh].

      assert (Hpath': is_path_in_graph (u, v, h :: lhv) G = true).
      { simpl. destruct G as [V E]. apply split_and_true. split.
        - simpl in Hpath. apply split_and_true in Hpath. apply Hpath.
        - apply Hlhv. }

      assert (Hl2: forall (l1 l2 l3: nodes) (a b: node), l1 ++ [a] ++ l2 = l3 ++ [b] ->
                        (rev l2 = [] -> a = b /\ l1 = l3) /\ (forall (hl2: node) (tl2: nodes), rev l2 = hl2 :: tl2 -> b = hl2 /\ l3 = l1 ++ [a] ++ rev tl2)).
      { intros l1' l2' l3 a b H. split.
        { intros Hlp2.
          assert (Hlem: rev (l1' ++ [a]) = rev (l3 ++ [b])).
          { rewrite <- H. rewrite reverse_list_append. rewrite reverse_list_append. rewrite reverse_list_append. unfold nodes in *. unfold node in *. rewrite Hlp2.
            simpl. reflexivity. }
          rewrite reverse_list_append in Hlem. rewrite reverse_list_append in Hlem. simpl in Hlem.
          inversion Hlem. split. reflexivity. rewrite reverse_list_twice with (l := l1'). rewrite H2. rewrite <- reverse_list_twice.
          reflexivity. }
        { intros hlp2' tlp2' Hlp2'. assert (Hlem: rev (l1' ++ [a] ++ l2') = rev (l3 ++ [b])).
          { rewrite <- H. reflexivity. }
          rewrite reverse_list_append in Hlem. rewrite reverse_list_append in Hlem. unfold nodes in *. unfold node in *. rewrite Hlp2' in Hlem. simpl in Hlem. rewrite reverse_list_append in Hlem.
          simpl in Hlem. inversion Hlem. split. reflexivity. rewrite reverse_list_twice with (l := l3).
          rewrite <- H2. repeat rewrite reverse_list_append. rewrite <- reverse_list_twice. simpl. reflexivity. } }

      assert (Hhu: (h =? u) = false).
      { destruct (h =? u) as [|] eqn:Hhu.
        - apply eqb_eq in Hhu. destruct Hcyc as [_ [Hcyc _]]. exfalso. apply Hcyc. left. apply Hhu.
        - reflexivity. }

      destruct (member u lhv) as [|] eqn:Hulhv.
      * (* CASE 1: if u intersects lhv, then use path along lhv starting from v *)
        apply member_In_equiv in Hulhv. apply membership_splits_list in Hulhv. destruct Hulhv as [lhv1 [lhv2 Hulhv]].
        exists lhv2. split.
        { apply subpath_still_acyclic with (w := h) (l1 := lhv1) (l3 := lhv). split. apply Hulhv. apply Hlhv. } split.
        { apply subpath_still_d_connected_gen with (w := h) (l1 := lhv1) (l3 := lhv). split. apply Hulhv. apply Hlhv. } split.
        { apply subpath_still_path with (w := h) (l1 := lhv1) (l3 := lhv). split. apply Hulhv. apply Hlhv. } split.

        { intros w Hw.
          assert (Houtw: path_out_of_node w (u, v, lhv2) G = path_out_of_node w (h, v, lhv) G).
          { assert (Houtw: exists (b: bool), path_out_of_node w (u, v, lhv2) G = Some b).
            { destruct Hw as [Hw | Hw].
              - apply path_out_of_node_mem_2. unfold node_in_path in Hw. simpl in Hw. destruct (w =? u) as [|] eqn:Hwu.
                + left. apply eqb_eq in Hwu. rewrite Hwu. reflexivity.
                + simpl in Hw. destruct (w =? v) as [|] eqn:Hwv.
                  * simpl in Hw. destruct Hw as [_ Hw]. discriminate Hw.
                  * simpl in Hw. right. apply member_In_equiv. apply Hw.
              - destruct Hw as [b Hw]. exists (negb b). apply Hw. }
            destruct Houtw as [b Houtw]. rewrite Houtw. symmetry. apply subpath_preserves_path_out_of_node with (u := u) (l1 := lhv1) (l2 := lhv2).
            split. apply Hulhv. apply Houtw. apply Hlhv. }

          unfold nodes in *. unfold node in *. rewrite Houtw. apply Hout.
          destruct Hw as [Hw | Hw].
           - (* all nodes in (u, v, lhv2) but not (u, v, h :: t) must also be in (h, v, lhv), so Hout applies *)
            unfold node_in_path in Hw. simpl in Hw. destruct (w =? u) as [|] eqn:Hwu. simpl in Hw. destruct Hw as [_ Hw]. discriminate Hw.
            simpl in Hw. destruct (w =? v) as [|] eqn:Hwv. simpl in Hw. destruct Hw as [_ Hw]. discriminate Hw. simpl in Hw.
            left. unfold node_in_path. simpl. split.
            + apply split_orb_true. right. apply member_In_equiv. rewrite <- Hulhv. apply membership_append_r. right. apply member_In_equiv. apply Hw.
            + rewrite Hwv. destruct (h =? w) as [|] eqn:Hhw. destruct Hw as [_ Hw]. discriminate Hw. rewrite eqb_sym in Hhw. rewrite Hhw.
              simpl. apply Hw.
          - destruct Hw as [b Hw]. destruct (w =? u) as [|] eqn:Hwu.
            + left. split.
              * unfold node_in_path. simpl. rewrite orb_comm. apply split_orb_true. left. apply member_In_equiv. rewrite <- Hulhv.
                apply membership_append_r. left. apply eqb_eq in Hwu. rewrite Hwu. reflexivity.
              * apply eqb_eq in Hwu. rewrite Hwu. apply acyclic_path_correct in Hcyc. simpl in Hcyc.
                unfold node_in_path. simpl. destruct (v =? u) as [|] eqn:Hvu. simpl in Hcyc. discriminate Hcyc. rewrite eqb_sym in Hvu. rewrite Hvu.
                rewrite eqb_sym in Hhu. rewrite Hhu. simpl.
                apply split_and_true in Hcyc. destruct Hcyc as [Hcyc _]. destruct (member u t) as [|] eqn:Hut. rewrite eqb_sym in Hhu. rewrite Hhu in Hcyc. discriminate Hcyc. reflexivity.
            + right. exists b. split.
              * rewrite <- path_out_of_node_cat with (u := u). apply Hw. apply Hwu.
              * rewrite <- Houtw. apply Hw. }

        assert (HD: exists (D: assignments (nodes * node)), get_collider_descendants_for_subpath Dh (find_colliders_in_path (u, v, lhv2) G) = Some D).
        { apply collider_descendants_for_subpath_existence_2 with (u := h) (l1 := lhv1) (L := L).
          unfold concat. simpl in Hulhv. unfold nodes in *. unfold node in *. rewrite Hulhv. apply HLh. }
        destruct HD as [D HD]. exists D. split. apply collider_subpath_is_exact_assignment with (D := Dh). apply HD.

        intros c Hc.
        assert (Hc': In c (find_colliders_in_path (h, v, lhv) G)).
        { apply subpath_preserves_colliders with (u := u) (l1 := lhv1) (l2 := lhv2). split. apply Hulhv. left. apply Hc. }
        apply HDh in Hc'. clear HDh. destruct Hc' as [Hc' | Hc'].
        -- left. split. apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (u, v, lhv2) G). apply HD. apply Hc'. apply Hc. apply Hc'.
        -- right. destruct Hc' as [p [d HDh]]. exists p. exists d. split.
           apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (u, v, lhv2) G). apply HD. apply HDh. apply Hc.

           rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc.
           split. repeat split; apply HDh. split.

           apply no_overlap_non_member. intros x Hx Hx'.
           destruct HDh as [_ [_ [_ [_ [_ [HDh _]]]]]]. apply no_overlap_non_member with (x := x) in HDh. apply HDh. apply Hx'.
           rewrite app_comm_cons in Hx. right. rewrite <- Hulhv. apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
           ++ apply membership_append. apply membership_append_r. apply Hx.
           ++ apply membership_append_r. apply Hx.
           ++ intros c' d' p' Hcdp. destruct HDh as [_ [_ [_ [_ [_ HDh]]]]]. apply HDh. split. apply Hcdp.
              apply collider_descendants_preserved_for_subpath with (D' := D) (col := find_colliders_in_path (u, v, lhv2) G). apply HD. apply Hcdp.

      * (* CASE 2: u does not intersect lhv. check if u intersects any descendant paths of Dh *)
        destruct (member u L) as [|] eqn:HuL.
        ** (* CASE 2A *)
           apply member_In_equiv in HuL. apply membership_splits_list in HuL. destruct HuL as [l1 [l2 HuL]].

           assert (Hu: exists (c d: node) (p: nodes), In c (find_colliders_in_path (h, v, lhv) G)
                        /\ get_assigned_value Dh c = Some (p, d) /\ d =? c = false
                        /\ In u (p ++ [d])).
           { apply collider_descendants_from_assignments_belong_to_collider with (L := L). apply HLh. rewrite <- HuL. apply membership_append_r. left. reflexivity. }
           destruct Hu as [c [d [p [Hcolc [HDc [Hdc Hu]]]]]]. apply membership_splits_list in Hu. destruct Hu as [lp1 [lp2 Hlp]].

           assert (Hclhv: In c lhv).
           { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := c) in Hlhv. apply Hlhv. right. right. apply Hcolc. } 
           apply membership_splits_list in Hclhv. destruct Hclhv as [lc1 [lc2 Hlhvc]].

           pose proof Hcolc as Hcolc'. apply HDh in Hcolc. destruct Hcolc as [[F _] | Hcolc]. rewrite HDc in F. inversion F. rewrite H1 in Hdc. rewrite eqb_refl in Hdc. discriminate Hdc.
           destruct Hcolc as [p' [d' [Hpd'' Hpd']]]. rewrite HDc in Hpd''. inversion Hpd''. clear Hpd''. rewrite <- H0 in *. rewrite <- H1 in *. clear H0. clear H1.

           assert (Hlp2: rev lp2 = [] -> u = d /\ lp1 = p).
           { apply Hl2. apply Hlp. }
           assert (Hlp2': forall (hlp2: node) (tlp2: nodes), rev lp2 = hlp2 :: tlp2 -> d = hlp2 /\ p = lp1 ++ [u] ++ (rev tlp2)).
           { apply Hl2. apply Hlp. }

           assert (Hcyc': acyclic_path_2 (u, v, rev lp1 ++ [c] ++ lc2)).
           { apply concat_paths_acyclic.
             - split.
               --- destruct Hpd' as [_ [_ [_ [_ [Hpd' _]]]]]. intros Hyv. apply no_overlap_non_member with (x := u) in Hpd'.
                   + apply Hpd'. rewrite <- Hlp. apply membership_append_r. left. reflexivity.
                   + rewrite Hyv. right. apply membership_append_r. left. reflexivity.
               --- split.
                   + destruct (rev lp2) as [| hlp2 tlp2].
                     * assert (Hyd: u = d /\ lp1 = p). { apply Hlp2. reflexivity. } destruct Hyd as [Hyd Hlp1]. rewrite Hyd.
                       apply reverse_path_still_acyclic. rewrite Hlp1. apply Hpd'.
                     * assert (Hd: d = hlp2 /\ p = lp1 ++ [u] ++ (rev tlp2)). { apply Hlp2'. reflexivity. }
                       apply reverse_path_still_acyclic. apply subpath_still_acyclic_2 with (v := d) (l2 := rev tlp2) (l3 := p). split. symmetry. apply Hd.
                       apply Hpd'.
                   + apply subpath_still_acyclic with (w := h) (l1 := lc1) (l3 := lhv). split. apply Hlhvc. apply Hlhv.
             - apply demorgan. intros Hmem. (* y cannot overlap with lhv path, v cannot overlap desc path (both Hpd') *)
               destruct Hpd' as [_ [_ [_ [_ [Hpd' _]]]]]. destruct Hmem as [Hmem | Hmem].
               + apply no_overlap_non_member with (x := u) in Hpd'.
                 * apply Hpd'. rewrite <- Hlp. apply membership_append_r. left. reflexivity.
                 * rewrite <- Hlhvc. right. apply membership_append. apply membership_append_r. apply membership_append_r. apply Hmem.
               + apply no_overlap_non_member with (x := v) in Hpd'.
                 * apply Hpd'. rewrite <- Hlp. apply membership_append. apply membership_rev. apply Hmem.
                 * right. apply membership_append_r. left. reflexivity.
             - apply no_overlap_non_member. intros x' Hmem Hmem2. destruct Hpd' as [_ [_ [_ [_ [Hpd' _]]]]].
               apply no_overlap_non_member with (x := x') in Hpd'.
               + apply Hpd'. rewrite <- Hlp. apply membership_append. apply membership_rev. apply Hmem2.
               + right. apply membership_append. rewrite <- Hlhvc. apply membership_append_r. apply membership_append_r. apply Hmem. }

           assert (Hpath'': is_path_in_graph (u, v, rev lp1 ++ [c] ++ lc2) G = true).
           { apply concat_paths_still_a_path. split.
             - destruct (rev lp2) as [| hlp2 tlp2].
               + (* Hlp -> u = d, use HD to show that in fact, path is directed *)
                 assert (Hyd: u = d /\ lp1 = p). { apply Hlp2. reflexivity. }
                 apply reverse_path_in_graph. destruct Hyd as [Hyd Hlp1]. rewrite Hyd. rewrite Hlp1.
                 apply directed_path_is_path. apply Hpd'.
               + (* Hlp -> d = hlp2, so use subpath with l2 := tlp2, then use HD *)
                 assert (Hd: d = hlp2 /\ p = lp1 ++ [u] ++ (rev tlp2)). { apply Hlp2'. reflexivity. }
                 apply reverse_path_in_graph. apply subpath_still_path_2 with (v := d) (l2 := rev tlp2) (l3 := p). split. symmetry. apply Hd.
                 apply directed_path_is_path. apply Hpd'.

             - apply subpath_still_path with (w := h) (l1 := lc1) (l3 := lhv). split.
               + apply Hlhvc.
               + apply Hlhv. }


           exists (rev lp1 ++ [c] ++ lc2).

           assert (Hpath''': is_path_in_graph (c, v, lc2) G = true). { apply subpath_still_path with (w := h) (l1 := lc1) (l3 := lhv). split. apply Hlhvc. apply Hlhv. }
           assert (Hdir: is_directed_path_in_graph (c, u, lp1) G = true).
           { destruct (rev lp2) as [| hlp2 tlp2].
             + assert (Hyd: u = d /\ lp1 = p). { apply Hlp2. reflexivity. } destruct Hyd as [Hyd Hlp1]. rewrite Hyd. rewrite Hlp1.
               apply Hpd'.
             + assert (Hyd: d = hlp2 /\ p = lp1 ++ [u] ++ rev tlp2). { apply Hlp2'. reflexivity. }
               apply subpath_still_directed_2 with (v := d) (l2 := rev tlp2) (l3 := p). split. symmetry. apply Hyd. apply Hpd'. }

           assert (Hc: In c (find_mediators_in_path (concat u c v (rev lp1) lc2) G)).
           { destruct lc2 as [| hlc2 tlc2].
             + simpl in Hpath'''. destruct G as [V E]. rewrite andb_comm in Hpath'''. simpl in Hpath'''. apply split_orb_true in Hpath'''. destruct Hpath''' as [Hcv | Hvc].
               * (* Hcolc' -> (v, c) is an edge, makes cycle with Hcv *)
                 apply colliders_vs_edges_in_path in Hcolc'. destruct Hcolc' as [y [z [Hsub Hcolc']]]. apply end_of_sublist_still_sublist in Hsub.
                 assert (Hz: z = v).
                 { apply two_sublists_the_same with (l := lhv ++ [v]) (a := c). apply Hsub.
                   apply sublist_breaks_down_list. exists lc1. exists []. simpl. rewrite <- Hlhvc. simpl. rewrite <- app_assoc. reflexivity.
                   destruct Hlhv as [[Hlhv _] _]. apply acyclic_path_count with (x := c) in Hlhv. simpl in Hlhv. destruct (h =? c) as [|] eqn:Hhc.
                   - inversion Hlhv. rewrite <- Hlhvc in H0. rewrite count_app in H0. rewrite count_app in H0. simpl in H0. rewrite eqb_refl in H0. lia.
                   - apply Hlhv.
                   - right. rewrite <- Hlhvc. apply membership_append. apply membership_append_r. left. reflexivity. }
                 rewrite Hz in Hcolc'. destruct Hcolc' as [_ Hcolc'].
                 destruct HG as [_ HG]. apply contains_cycle_false_correct with (p := (v, v, [c])) in HG. exfalso. destruct HG as [HG _]. apply HG. reflexivity.
                 simpl. simpl in Hcv. rewrite Hcv. simpl in Hcolc'. rewrite Hcolc'. reflexivity.
               * destruct lp1 as [| hlp1 tlp1].
                 ++ apply mediators_vs_edges_in_path. exists u. exists v. split. simpl. repeat rewrite eqb_refl. reflexivity. right.
                    split. simpl in Hdir. apply split_and_true in Hdir. apply Hdir. apply Hvc.
                 ++ apply mediators_vs_edges_in_path. exists hlp1. exists v. split.
                    ** apply sublist_breaks_down_list. exists (u :: rev tlp1). exists []. simpl. repeat rewrite <- app_assoc. simpl. reflexivity.
                    ** right. split. simpl in Hdir. apply split_and_true in Hdir. apply Hdir. apply Hvc.

             + simpl in Hpath'''. destruct G as [V E]. apply split_and_true in Hpath'''. destruct Hpath''' as [Hpath''' _]. apply split_orb_true in Hpath'''. destruct Hpath''' as [Hcv | Hvc].
               * (* Hcolc' -> (hlc2, c) is an edge, makes cycle with Hcv *)
                 apply colliders_vs_edges_in_path in Hcolc'. destruct Hcolc' as [y [z [Hsub Hcolc']]]. apply end_of_sublist_still_sublist in Hsub.
                 assert (Hz: z = hlc2).
                 { apply two_sublists_the_same with (l := lhv ++ [v]) (a := c). apply Hsub.
                   apply sublist_breaks_down_list. exists lc1. exists (tlc2 ++ [v]). simpl. rewrite <- Hlhvc. simpl. rewrite <- app_assoc. reflexivity.
                   destruct Hlhv as [[Hlhv _] _]. apply acyclic_path_count with (x := c) in Hlhv. simpl in Hlhv. destruct (h =? c) as [|] eqn:Hhc.
                   - inversion Hlhv. rewrite <- Hlhvc in H0. rewrite count_app in H0. rewrite count_app in H0. simpl in H0. rewrite eqb_refl in H0. lia.
                   - apply Hlhv.
                   - right. rewrite <- Hlhvc. apply membership_append. apply membership_append_r. left. reflexivity. }
                 rewrite Hz in Hcolc'. destruct Hcolc' as [_ Hcolc'].
                 destruct HG as [_ HG]. apply contains_cycle_false_correct with (p := (hlc2, hlc2, [c])) in HG. exfalso. destruct HG as [HG _]. apply HG. reflexivity.
                 simpl. simpl in Hcv. rewrite Hcv. simpl in Hcolc'. rewrite Hcolc'. reflexivity.
               * destruct lp1 as [| hlp1 tlp1].
                 ++ apply mediators_vs_edges_in_path. exists u. exists hlc2. split. simpl. repeat rewrite eqb_refl. reflexivity. right.
                    split. simpl in Hdir. apply split_and_true in Hdir. apply Hdir. apply Hvc.
                 ++ apply mediators_vs_edges_in_path. exists hlp1. exists hlc2. split.
                    ** apply sublist_breaks_down_list. exists (u :: rev tlp1). exists (tlc2 ++ [v]). simpl. repeat rewrite <- app_assoc. simpl. reflexivity.
                    ** right. split. simpl in Hdir. apply split_and_true in Hdir. apply Hdir. apply Hvc. }

           assert (Hccol: ~ In c (find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G)).
           { apply if_mediator_then_not_confounder_path in Hc. 2: { apply HG. } apply Hc. }

           assert (Hx': forall (x': node),
                          In x' (find_mediators_in_path (u, c, rev lp1) G) \/
                          In x' (find_confounders_in_path (u, c, rev lp1) G) \/
                          In x' (find_colliders_in_path (u, c, rev lp1) G) -> In x' (rev lp1)).
           { intros x'. assert (Hpath'''': is_path_in_graph (u, c, rev lp1) G = true).
             { apply subpath_still_path_2 with (v := v) (l2 := lc2) (l3 := rev lp1 ++ [c] ++ lc2). split. reflexivity. apply Hpath''. }
             apply intermediate_node_in_path with (x := x') in Hpath''''. apply Hpath''''. }

           assert (Hx'': forall (x': node), In x' (rev lp1) -> In x' (find_mediators_in_path (u, c, rev lp1) G)).
           { intros x' Hmem. apply mediators_same_in_reverse_path. apply directed_path_all_mediators. split.
             - apply Hdir.
             - apply membership_rev. apply Hmem. }

           split. apply Hcyc'. split.
           { apply concat_d_connected_paths. apply HG. apply Hpath''.
             - rewrite <- and_assoc. rewrite and_comm. split. apply Hcyc'. split.
               + (* directed path, so all mediators. none are in Z (except possible y if y = d) *)
                 unfold d_connected_2. 
                 repeat split.
                 * (* mediators in lp1, so in p, so not in Z by Hpd' *)
                   apply no_overlap_non_member. intros x' Hmem Hmem2.
                   assert (Hmem3: In x' (rev lp1)). { apply Hx'. left. apply Hmem. }
                   apply membership_rev in Hmem3. rewrite <- reverse_list_twice in Hmem3.
                   assert (Hmem4: In x' p).
                   { destruct (rev lp2) as [| hlp2 tlp2].
                     - assert (Hlem: lp1 = p). { apply Hlp2. reflexivity. } rewrite <- Hlem. apply Hmem3.
                     - assert (Hlem: p = lp1 ++ [u] ++ rev tlp2). { apply Hlp2' with (hlp2 := hlp2). reflexivity. }
                       rewrite Hlem. apply membership_append. apply Hmem3. }
                   destruct Hpd' as [_ [_ [_ [Hpd' _]]]]. apply no_overlap_non_member with (x := x') in Hpd'.
                   -- apply Hpd'. right. apply Hmem4.
                   -- apply Hmem2.
                * (* no confounders, since directed path *)
                  apply no_overlap_non_member. intros x' Hmem _.
                  assert (Hcon: In x' (find_mediators_in_path (u, c, rev lp1) G)).
                  { apply Hx''. apply Hx'. right. left. apply Hmem. }
                  apply if_mediator_then_not_confounder_path in Hcon. destruct Hcon as [Hcon _]. apply Hcon. apply Hmem. apply HG.
                * unfold all_colliders_have_descendant_conditioned_on. apply forallb_true_iff_mem. intros x' Hmem.
                  assert (Hcon: In x' (find_mediators_in_path (u, c, rev lp1) G)).
                  { apply Hx''. apply Hx'. right. right. apply Hmem. }
                  apply if_mediator_then_not_confounder_path in Hcon. destruct Hcon as [_ Hcon]. exfalso. apply Hcon. apply Hmem. apply HG.
               + apply subpath_still_d_connected_gen with (w := h) (l1 := lc1) (l3 := lhv). split. apply Hlhvc. apply Hlhv.
             - (* since c starts descendant path, cannot be collider. not in Z by Hpd'. *)
               (* need to determine first edge c <-> ...lc2 *)
               assert (HcZ: ~ In c Z). { destruct Hpd' as [_ [_ [_ [Hpd' _]]]]. intros Hmem. apply no_overlap_non_member with (x := c) in Hpd'. exfalso. apply Hpd'. left. reflexivity. apply Hmem. }

               left. split. apply Hc. apply HcZ. } split. apply Hpath''. split.

           { intros w Hw.
             (* w is in (u, c, rev lp1): exists d, p. path_out_of_node = false *)
             assert (Hw': In w (u :: rev lp1) \/ In w (c :: lc2 ++ [v])). { admit. }
             destruct Hw' as [Hw' | Hw'].
             - split.
               + apply membership_splits_list in Hw'. destruct Hw' as [lw1 [lw2 Hw']].
                 destruct (rev lp2) as [| hlp2 tlp2] eqn:Hlp2eq.
                 * destruct lw1 as [| hlw1 tlw1].
                   -- (* u = w = d *) right. split.
                      ++ inversion Hw'. unfold path_out_of_node. simpl. rewrite eqb_refl. (* Hdir says c->..lp1..->u is directed *)
                         admit.
                      ++ inversion Hw'. assert (Hud: u = d). { apply Hlp2. reflexivity. } rewrite Hud. apply Hpd'.
                   -- left. exists d. exists (rev tlw1). split.
                      ++ apply subpath_still_directed with (w := c) (l1 := rev lw2) (l3 := p). split.
                         ** assert (Hp: lp1 = p). { apply Hlp2. reflexivity. } inversion Hw'. rewrite <- Hp. rewrite reverse_list_twice with (l := lp1).
                            rewrite <- H1. rewrite reverse_list_append. simpl. rewrite <- app_assoc. reflexivity.
                         ** apply Hpd'.
                      ++ split. apply Hpd'. destruct Hpd' as [_ [_ [_ [Hpd' _]]]]. intros HwZ. apply no_overlap_non_member with (x := w) in Hpd'.
                         apply Hpd'. right. inversion Hw'. assert (Hp: lp1 = p). { apply Hlp2. reflexivity. } rewrite <- Hp. rewrite reverse_list_twice with (l := lp1).
                         rewrite <- H1. rewrite reverse_list_append. apply membership_append. apply membership_rev. left. reflexivity.
                         apply HwZ.
                 * assert (Hd: d = hlp2 /\ p = lp1 ++ [u] ++ rev tlp2). { apply Hlp2'. reflexivity. }
                   destruct lw1 as [| hlw1 tlw1].
                   -- left. exists d. exists (rev tlp2). inversion Hw'. repeat split. apply subpath_still_directed with (w := c) (l1 := lp1) (l3 := p).
                      split. symmetry. apply Hd. apply Hpd'. apply Hpd'.
                      destruct Hpd' as [_ [_ [_ [Hpd' _]]]]. intros HwZ. apply no_overlap_non_member with (x := u) in Hpd'.
                      apply Hpd'. right. destruct Hd as [_ Hd]. rewrite Hd. apply membership_append_r. left. reflexivity.
                      apply HwZ.
                   -- left. exists d. exists (rev tlw1 ++ [u] ++ rev tlp2). inversion Hw'. repeat split.
                      ++ apply subpath_still_directed with (w := c) (l1 := rev lw2) (l3 := p). split.
                         destruct Hd as [_ Hd]. rewrite Hd. rewrite reverse_list_twice with (l := lp1). rewrite <- H1. rewrite reverse_list_append. simpl.
                         rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hpd'.
                      ++ apply Hpd'.
                      ++ destruct Hpd' as [_ [_ [_ [Hpd' _]]]]. intros HwZ. apply no_overlap_non_member with (x := w) in Hpd'.
                         apply Hpd'. right. destruct Hd as [_ Hd]. rewrite Hd. apply membership_append. apply membership_rev. rewrite <- H1. apply membership_append_r. left. reflexivity.
                         apply HwZ.
               + intros F. admit. (* reverse directed path *)

             (* w is in (c, v, lc2): use Hout *) 
             - admit. }



           assert (Hcol: find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G = find_colliders_in_path (c, v, lc2) G).
           { assert (Hcolyv: find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G = (find_colliders_in_path (u, c, rev lp1) G) ++ [c] ++ (find_colliders_in_path (c, v, lc2) G)
                           \/ find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G = (find_colliders_in_path (u, c, rev lp1) G) ++ (find_colliders_in_path (c, v, lc2) G)).
             { apply subpath_preserves_colliders_2. reflexivity. }
             assert (Hcolyv': find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G = (find_colliders_in_path (u, c, rev lp1) G) ++ (find_colliders_in_path (c, v, lc2) G)).
             { (* by Hc, c cannot be a collider *) destruct Hcolyv as [Hcolyv | Hcolyv].
               - exfalso. apply Hccol. rewrite Hcolyv. apply membership_append_r. left. reflexivity.
               - apply Hcolyv. } clear Hcolyv.
             destruct (find_colliders_in_path (u, c, rev lp1) G) as [| huc tuc] eqn:Hcoluc.
             - rewrite Hcolyv'. reflexivity.
             - assert (Hhuc: In huc (find_mediators_in_path (u, c, rev lp1) G)).
               { apply Hx''. apply Hx'. right. right. left. reflexivity. }
               apply if_mediator_then_not_confounder_path in Hhuc. exfalso. apply Hhuc. rewrite Hcoluc. left. reflexivity. apply HG. }

           assert (HD: exists (D: assignments (nodes * node)), get_collider_descendants_for_subpath Dh (find_colliders_in_path (c, v, lc2) G) = Some D).
           { apply collider_descendants_for_subpath_existence_2 with (u := h) (l1 := lc1) (L := L).
             unfold concat. simpl in Hlhvc. unfold nodes in *. unfold node in *. rewrite Hlhvc. apply HLh. }
           destruct HD as [D HD]. exists D. split.
           { apply collider_subpath_is_exact_assignment with (D := Dh).
             unfold nodes in *. unfold node in *. rewrite Hcol. apply HD. }

           (* use the same paths for remaining colliders, since from HD, they do not overlap y desc path *)
           intros c' Hc'.
           assert (Hcol': In c' (find_colliders_in_path (h, v, lhv) G)).
           { apply subpath_preserves_colliders with (u := c) (l1 := lc1) (l2 := lc2). split. apply Hlhvc. left.
             unfold nodes in *. unfold node in *. rewrite Hcol in Hc'. apply Hc'. }
           apply HDh in Hcol'. destruct Hcol' as [Hcol' | Hcol'].
           -- left. split. apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G). rewrite Hcol. apply HD. apply Hcol'. apply Hc'. apply Hcol'.
           -- right. destruct Hcol' as [pc [dc HDh']]. exists pc. exists dc. split.
              apply collider_descendants_preserved_for_subpath_2 with (D := Dh) (col := find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G). rewrite Hcol. apply HD. apply HDh'. apply Hc'.
 
              rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc.
              split. repeat split; apply HDh'. split.
 
              apply no_overlap_non_member. intros x Hx1 Hx2.
              ++ assert (Hx1': In x ((u :: rev lp1) ++ (c :: lc2 ++ [v]))).
                 { rewrite app_comm_cons. rewrite app_assoc. rewrite <- app_comm_cons. apply Hx1. }
                 clear Hx1. apply membership_append_or in Hx1'. destruct Hx1' as [Hx1 | Hx1].
                 --- destruct HDh' as [_ [_ [_ [_ [_ [_ HDh']]]]]]. specialize HDh' with (c' := c) (d' := d) (p' := p).
                     assert (Hover: overlap (c' :: pc ++ [dc]) (c :: p ++ [d]) = false).
                     { apply HDh'. rewrite and_comm. split. apply HDc. destruct (c' =? c) as [|] eqn:Hcc'.
                       - apply eqb_eq in Hcc'. exfalso. apply Hccol. rewrite <- Hcc' in *. apply Hc'.
                       - reflexivity. }
                     apply no_overlap_non_member with (x := x) in Hover. apply Hover. right. apply Hx2. right. rewrite <- Hlp.
                     destruct Hx1 as [Hx1 | Hx1]. apply membership_append_r. left. apply Hx1. apply membership_append. apply membership_rev. apply Hx1.
                 --- destruct HDh' as [_ [_ [_ [_ [_ [HDh' _]]]]]]. apply no_overlap_non_member with (x := x) in HDh'. apply HDh'. apply Hx2.
                     right. rewrite <- Hlhvc. rewrite <- app_assoc. apply membership_append_r. apply Hx1.
              ++ intros c'' d'' p'' Hcdp. destruct HDh' as [_ [_ [_ [_ [_ HDh']]]]]. apply HDh'. split. apply Hcdp.
                 apply collider_descendants_preserved_for_subpath with (D' := D) (col := find_colliders_in_path (u, v, rev lp1 ++ [c] ++ lc2) G). rewrite Hcol. apply HD. apply Hcdp.

        ** (* u does not intersect any part of (h, v, lhv). see if h is a mediator, confounder, or collider *)
           assert (Hh: In h (find_mediators_in_path (u, v, h :: lhv) G) \/
                       In h (find_confounders_in_path (u, v, h :: lhv) G) \/
                       In h (find_colliders_in_path (u, v, h :: lhv) G)).
           { assert (Hh: In h (h :: lhv)). { left. reflexivity. }
             apply intermediate_node_in_path with (x := h) in Hpath'. apply Hpath' in Hh. apply Hh. }

           rewrite <- or_assoc in Hh. destruct Hh as [Hh | Hh].
           --- (* CASE 2B: h is not a collider *)
               assert (HFcol: find_colliders_in_path (u, v, h :: lhv) G = find_colliders_in_path (h, v, lhv) G).
               { assert (HFcol: ~In h (find_colliders_in_path (u, v, h :: lhv) G)).
                 { destruct Hh as [Hh | Hh]. apply if_mediator_then_not_confounder_path in Hh. apply Hh. apply HG.
                   apply if_confounder_then_not_mediator_path in Hh. apply Hh. apply HG. }

                 simpl. destruct lhv as [| h' t'].
                 - simpl. destruct (is_collider_bool u v h G) as [|] eqn:Hcol.
                   + assert (Hcol': In h (find_colliders_in_path (u, v, [h]) G)). { simpl. rewrite Hcol. left. reflexivity. }
                     exfalso. apply HFcol. apply Hcol'.
                   + reflexivity.
                  - simpl. destruct (is_collider_bool u h' h G) as [|] eqn:Hcol.
                    + assert (Hcol': In h (find_colliders_in_path (u, v, h :: h' :: t') G)). { simpl. rewrite Hcol. left. reflexivity. }
                      exfalso. apply HFcol. apply Hcol'.
                    + reflexivity. }

               exists (h :: lhv). split. repeat split.
               { apply Hcyc. }
               { intros Hmem. destruct Hmem as [Hmem | Hmem].
                 - unfold acyclic_path_2 in Hcyc. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. left. apply Hmem.
                 - apply member_In_equiv_F in Hulhv. apply Hulhv. apply Hmem. }
               { unfold acyclic_path_2 in Hlhv. intros Hmem. destruct Hmem as [Hmem | Hmem].
                 - destruct Hlhv as [[[Hlhv _] _] _]. apply Hlhv. apply Hmem.
                 - destruct Hlhv as [[[_ [_ [Hlhv _]]] _] _]. apply Hlhv. apply Hmem. }
               { destruct Hlhv as [[Hlhv _] _]. apply acyclic_path_correct_2 in Hlhv. apply acyclic_path_reverse in Hlhv.
                 simpl in Hlhv. rewrite reverse_list_append in Hlhv. simpl in Hlhv. apply split_and_true in Hlhv. destruct Hlhv as [_ Hlhv].
                 apply acyclic_path_reverse in Hlhv. rewrite reverse_list_append in Hlhv. rewrite <- reverse_list_twice in Hlhv. apply Hlhv. } split.

               pose proof Hh as Hh'. clear Hh.
               assert (Hsub: forall (y z: node), sublist [y; h; z] (u :: (h :: lhv) ++ [v]) = true
                             -> (lhv = [] -> y = u /\ z = v) /\
                                (forall (hlhv: node) (tlhv: nodes), lhv = hlhv :: tlhv -> y = u /\ z = hlhv)).
               { intros y z Hh. split.
                 * intros Hht. rewrite Hht in Hh. simpl in Hh. repeat rewrite eqb_refl in Hh. simpl in Hh. rewrite andb_assoc in Hh. apply split_orb_true in Hh. rewrite andb_comm in Hh. simpl in Hh.
                   destruct Hh as [Hh | Hh]. apply split_and_true in Hh. repeat rewrite eqb_eq in Hh. apply Hh.
                   rewrite andb_assoc in Hh. rewrite andb_comm in Hh. simpl in Hh. rewrite andb_comm in Hh. simpl in Hh. discriminate Hh.
                 * intros hlhv tlhv Hht. rewrite Hht in Hh. unfold sublist in Hh. apply split_orb_true in Hh. destruct Hh as [Hh | Hh].
                   - simpl in Hh. repeat rewrite eqb_refl in Hh. simpl in Hh. rewrite andb_assoc in Hh. apply split_and_true in Hh. destruct Hh as [Hh _]. apply split_and_true in Hh. repeat rewrite eqb_eq in Hh. apply Hh.
                   - assert (Hu: In h ((hlhv :: tlhv) ++ [v])). { apply middle_elt_of_sublist_not_first_elt with (a := y) (c := z). apply Hh. }
                     destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv.
                     apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]].
                     + destruct Hlhv as [_ [Hlhv _]]. exfalso. apply Hlhv. rewrite Hht. apply Hu.
                     + destruct Hlhv as [Hlhv _]. exfalso. apply Hlhv. symmetry. apply Hu.
                     + exfalso. apply Hu. }

               pose proof Hh' as Hh. clear Hh'. repeat split.
               { destruct Hh as [Hh | Hh].
                 - (* if h is a mediator in the new path, then u->h->...lhv or u<-h<-...lhv
                      if arrow didn't change, then mediator in original path, so not in Z
                      if arrow changed, then in original path either u->h<- and not in Z, or u<-h-> (not in Z since d-conn) *)
                   apply mediators_vs_edges_in_path in Hh. destruct Hh as [y [z [Hh Hyz]]].
                   apply Hsub in Hh as Hsub'. destruct Hsub' as [Hlhv0 Hhlhv].

                   assert (Hyu: y = u). { destruct lhv as [| hlhv tlhv] eqn:Hl. apply Hlhv0. reflexivity. apply Hhlhv with (hlhv := hlhv) (tlhv := tlhv). reflexivity. }
                   rewrite Hyu in *. clear Hyu.

                   assert (HhZ: ~In h Z).
                   { destruct Hyz as [Hyz | Hyz].
                     + (* u->h->z *)
                       assert (Houth: path_out_of_node h (h, v, lhv) G = Some true).
                       { unfold path_out_of_node. simpl. rewrite eqb_refl. destruct lhv as [| hlhv tlhv].
                         - simpl. assert (Hz: z = v). { apply Hlhv0. reflexivity. }
                           rewrite Hz in Hyz. destruct Hyz as [_ Hyz]. unfold is_edge in Hyz.
                           destruct G as [V E]. apply split_and_true in Hyz. destruct Hyz as [_ Hyz]. simpl. rewrite Hyz. reflexivity.
                         - simpl. assert (Hz: z = hlhv). { apply Hhlhv with (tlhv := tlhv). reflexivity. }
                           rewrite Hz in *. destruct Hyz as [_ Hyz]. destruct G as [V E]. apply split_and_true in Hyz. destruct Hyz as [_ Hyz]. simpl. rewrite Hyz. reflexivity. }

                       destruct (path_out_of_node h (u, v, h :: t) G) as [[|]|] eqn:Houth'.
                       - assert (Hmed: In h (find_mediators_in_path (u, v, h :: t) G)).
                         { simpl. unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'.
                           destruct t as [| h' t'].
                           - simpl. simpl in Houth'. rewrite eqb_refl in Houth'. unfold is_mediator_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                             destruct (edge_in_graph (h, v) G) as [|] eqn:Hhv. apply edge_in_graph_then_is_edge in Hhv. rewrite Hhv. simpl. left. reflexivity. apply HG. discriminate Houth'.
                           - simpl. rewrite eqb_refl in Houth'. simpl in Houth'. unfold is_mediator_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                             destruct (edge_in_graph (h, h') G) as [|] eqn:Hhh'. apply edge_in_graph_then_is_edge in Hhh'. rewrite Hhh'. simpl. left. reflexivity. apply HG. discriminate Houth'. }

                         unfold d_connected_2 in Hconn. destruct Hconn as [Hconn _]. apply no_overlap_non_member with (x := h) in Hconn.
                         apply Hconn. apply Hmed.
                       - assert (Hlem: path_out_of_node h (h, v, lhv) G = Some true -> ~ In h Z).
                         { apply Hout. right. exists false. split.
                           - rewrite <- path_out_of_node_cat with (u := u). apply Houth'. apply Hhu.
                           - simpl. apply Houth. }
                         apply Hlem. apply Houth.
                       - unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'. rewrite eqb_refl in Houth'.
                         destruct t as [| h' t']. simpl in Houth'. destruct (edge_in_graph (h, v) G) as [|]. discriminate Houth'. discriminate Houth'.
                         simpl in Houth'. destruct (edge_in_graph (h, h') G) as [|]. discriminate Houth'. discriminate Houth'.

                     + (* u<-h<-z *)
                       assert (Houth: path_out_of_node h (h, v, lhv) G = Some false).
                       { unfold path_out_of_node. simpl. rewrite eqb_refl. destruct lhv as [| hlhv tlhv].
                         - simpl. assert (Hz: z = v). { apply Hlhv0. reflexivity. }
                           rewrite Hz in Hyz. destruct Hyz as [_ Hyz]. apply acyclic_no_two_cycle in Hyz as Hyz'. unfold is_edge in Hyz.
                           destruct G as [V E]. apply split_and_true in Hyz. unfold is_edge in Hyz'. destruct Hyz as [Hyz1 Hyz2]. rewrite andb_comm in Hyz1. rewrite Hyz1 in Hyz'.
                           simpl. simpl in Hyz'. rewrite Hyz'. reflexivity. apply HG.
                         - simpl. assert (Hz: z = hlhv). { apply Hhlhv with (tlhv := tlhv). reflexivity. }
                           rewrite Hz in *. destruct Hyz as [_ Hyz]. apply acyclic_no_two_cycle in Hyz as Hyz'. unfold is_edge in Hyz.
                           destruct G as [V E]. apply split_and_true in Hyz. unfold is_edge in Hyz'. destruct Hyz as [Hyz1 Hyz2]. rewrite andb_comm in Hyz1. rewrite Hyz1 in Hyz'.
                           simpl. simpl in Hyz'. rewrite Hyz'. reflexivity. apply HG. }

                       destruct (path_out_of_node h (u, v, h :: t) G) as [[|]|] eqn:Houth'.
                       - assert (Hmed: In h (find_confounders_in_path (u, v, h :: t) G)).
                         { simpl. unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'.
                           destruct t as [| h' t'].
                           - simpl. simpl in Houth'. rewrite eqb_refl in Houth'. unfold is_confounder_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                             destruct (edge_in_graph (h, v) G) as [|] eqn:Hhv. apply edge_in_graph_then_is_edge in Hhv. rewrite Hhv. simpl. left. reflexivity. apply HG. discriminate Houth'.
                           - simpl. rewrite eqb_refl in Houth'. simpl in Houth'. unfold is_confounder_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                             destruct (edge_in_graph (h, h') G) as [|] eqn:Hhh'. apply edge_in_graph_then_is_edge in Hhh'. rewrite Hhh'. simpl. left. reflexivity. apply HG. discriminate Houth'. }
                         unfold d_connected_2 in Hconn. destruct Hconn as [_ [Hconn _]]. apply no_overlap_non_member with (x := h) in Hconn.
                         apply Hconn. apply Hmed.
                       - assert (Hmed: In h (find_mediators_in_path (u, v, h :: t) G)).
                         { simpl. unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'.
                           destruct t as [| h' t'].
                           - simpl. simpl in Houth'. rewrite eqb_refl in Houth'. unfold is_mediator_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                             destruct (edge_in_graph (h, v) G) as [|] eqn:Hhv. discriminate Houth'. simpl in Hpath.
                             destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [Hpath _].
                             simpl in Hhv. simpl in Hpath. rewrite Hhv in Hpath. rewrite andb_comm in Hpath. simpl in Hpath. simpl. rewrite Hpath. rewrite orb_comm. simpl. left. reflexivity.
                           - simpl. simpl in Houth'. rewrite eqb_refl in Houth'. unfold is_mediator_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                             destruct (edge_in_graph (h, h') G) as [|] eqn:Hhv. discriminate Houth'. simpl in Hpath.
                             destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [Hpath _].
                             simpl in Hhv. simpl in Hpath. rewrite Hhv in Hpath. rewrite andb_comm in Hpath. simpl in Hpath. simpl. rewrite Hpath. rewrite orb_comm. simpl. left. reflexivity. }
                         unfold d_connected_2 in Hconn. destruct Hconn as [Hconn _]. apply no_overlap_non_member with (x := h) in Hconn.
                         apply Hconn. apply Hmed.
                       - unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'. rewrite eqb_refl in Houth'.
                         destruct t as [| h' t']. simpl in Houth'. destruct (edge_in_graph (h, v) G) as [|]. discriminate Houth'. discriminate Houth'.
                         simpl in Houth'. destruct (edge_in_graph (h, h') G) as [|]. discriminate Houth'. discriminate Houth'. }

                     simpl. destruct lhv as [| hlhv tlhv].
                     -- simpl. destruct (is_mediator_bool u v h G || is_mediator_bool v u h G) as [|].
                        ++ apply overlap_flip. simpl. apply member_In_equiv_F in HhZ. rewrite HhZ. reflexivity.
                        ++ apply overlap_with_empty.
                     -- simpl. destruct (is_mediator_bool u hlhv h G || is_mediator_bool hlhv u h G) as [|].
                        ++ apply overlap_flip. simpl. apply member_In_equiv_F in HhZ. rewrite HhZ. apply overlap_flip. apply Hlhv.
                        ++ apply Hlhv.
                 - (* h is a confounder, so not a mediator. then find_mediators(new path) = find_mediators(old path) *)
                   simpl. destruct lhv as [| hlhv tlhv].
                   + simpl. destruct (is_mediator_bool u v h G || is_mediator_bool v u h G) as [|] eqn:Hmed.
                     * assert (Hmedh: In h (find_mediators_in_path (u, v, [h]) G)). { simpl. rewrite Hmed. left. reflexivity. }
                       apply if_mediator_then_not_confounder_path in Hmedh. exfalso. destruct Hmedh as [Hmedh _]. apply Hmedh. apply Hh. apply HG.
                     * apply overlap_with_empty.
                   + simpl. destruct (is_mediator_bool u hlhv h G || is_mediator_bool hlhv u h G) as [|] eqn:Hmed.
                     * assert (Hmedh: In h (find_mediators_in_path (u, v, h :: hlhv :: tlhv) G)). { simpl. rewrite Hmed. left. reflexivity. }
                       apply if_mediator_then_not_confounder_path in Hmedh. exfalso. destruct Hmedh as [Hmedh _]. apply Hmedh. apply Hh. apply HG.
                     * apply Hlhv. }

               { destruct Hh as [Hh | Hh].
                 - (* h is a mediator, so not a confounder. then find_confounders(new path) = find_confounders(old path) *)
                   simpl. destruct lhv as [| hlhv tlhv].
                   + simpl. destruct (is_confounder_bool u v h G) as [|] eqn:Hmed.
                     * assert (Hmedh: In h (find_confounders_in_path (u, v, [h]) G)). { simpl. rewrite Hmed. left. reflexivity. }
                       apply if_mediator_then_not_confounder_path in Hh. exfalso. destruct Hh as [Hh _]. apply Hh. apply Hmedh. apply HG.
                     * apply overlap_with_empty.
                   + simpl. destruct (is_confounder_bool u hlhv h G) as [|] eqn:Hmed.
                     * assert (Hmedh: In h (find_confounders_in_path (u, v, h :: hlhv :: tlhv) G)). { simpl. rewrite Hmed. left. reflexivity. }
                       apply if_mediator_then_not_confounder_path in Hh. exfalso. destruct Hh as [Hh _]. apply Hh. apply Hmedh. apply HG.
                     * apply Hlhv.
                 - (* if h is a confounder in the new path, then u<-h->...lhv
                      if arrow didn't change, then confounder in original path, so not in Z
                      if arrow changed, then in original path u<-h<- (not in Z since d-conn) *)
                   apply confounders_vs_edges_in_path in Hh. destruct Hh as [y [z [Hh Hyz]]].

                   apply Hsub in Hh as Hsub'. destruct Hsub' as [Hlhv0 Hhlhv].

                   assert (Hyu: y = u). { destruct lhv as [| hlhv tlhv] eqn:Hl. apply Hlhv0. reflexivity. apply Hhlhv with (hlhv := hlhv) (tlhv := tlhv). reflexivity. }
                   rewrite Hyu in *. clear Hyu.

                   assert (HhZ: ~In h Z).
                   { assert (Houth: path_out_of_node h (h, v, lhv) G = Some true).
                     { unfold path_out_of_node. simpl. rewrite eqb_refl. destruct lhv as [| hlhv tlhv].
                       - simpl. assert (Hz: z = v). { apply Hlhv0. reflexivity. }
                         rewrite Hz in Hyz. destruct Hyz as [_ Hyz]. unfold is_edge in Hyz.
                         destruct G as [V E]. apply split_and_true in Hyz. destruct Hyz as [_ Hyz]. simpl. rewrite Hyz. reflexivity.
                       - simpl. assert (Hz: z = hlhv). { apply Hhlhv with (tlhv := tlhv). reflexivity. }
                         rewrite Hz in *. destruct Hyz as [_ Hyz]. destruct G as [V E]. apply split_and_true in Hyz. destruct Hyz as [_ Hyz]. simpl. rewrite Hyz. reflexivity. }

                     destruct (path_out_of_node h (u, v, h :: t) G) as [[|]|] eqn:Houth'.
                     - assert (Hmed: In h (find_confounders_in_path (u, v, h :: t) G)).
                       { simpl. unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'.
                         destruct t as [| h' t'].
                         - simpl. simpl in Houth'. rewrite eqb_refl in Houth'. unfold is_confounder_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                           destruct (edge_in_graph (h, v) G) as [|] eqn:Hhv. apply edge_in_graph_then_is_edge in Hhv. rewrite Hhv. simpl. left. reflexivity. apply HG. discriminate Houth'.
                         - simpl. rewrite eqb_refl in Houth'. simpl in Houth'. unfold is_confounder_bool. destruct Hyz as [Hyz1 Hyz2]. rewrite Hyz1.
                           destruct (edge_in_graph (h, h') G) as [|] eqn:Hhh'. apply edge_in_graph_then_is_edge in Hhh'. rewrite Hhh'. simpl. left. reflexivity. apply HG. discriminate Houth'. }

                       unfold d_connected_2 in Hconn. destruct Hconn as [_ [Hconn _]]. apply no_overlap_non_member with (x := h) in Hconn.
                       apply Hconn. apply Hmed.
                     - assert (Hlem: path_out_of_node h (h, v, lhv) G = Some true -> ~ In h Z).
                       { apply Hout. right. exists false. split.
                         - rewrite <- path_out_of_node_cat with (u := u). apply Houth'. apply Hhu.
                         - simpl. apply Houth. }
                       apply Hlem. apply Houth.
                     - unfold path_out_of_node in Houth'. simpl in Houth'. rewrite eqb_sym in Hhu. rewrite Hhu in Houth'. rewrite eqb_refl in Houth'.
                       destruct t as [| h' t']. simpl in Houth'. destruct (edge_in_graph (h, v) G) as [|]. discriminate Houth'. discriminate Houth'.
                       simpl in Houth'. destruct (edge_in_graph (h, h') G) as [|]. discriminate Houth'. discriminate Houth'. }

                     simpl. destruct lhv as [| hlhv tlhv].
                     -- simpl. destruct (is_confounder_bool u v h G) as [|].
                        ++ apply overlap_flip. simpl. apply member_In_equiv_F in HhZ. rewrite HhZ. reflexivity.
                        ++ apply overlap_with_empty.
                     -- simpl. destruct (is_confounder_bool u hlhv h G) as [|].
                        ++ apply overlap_flip. simpl. apply member_In_equiv_F in HhZ. rewrite HhZ. apply overlap_flip. apply Hlhv.
                        ++ apply Hlhv. }

               { unfold nodes in *. rewrite HFcol. apply Hlhv. } split.
               { apply Hpath'. } split.

               { intros w H. destruct (w =? u) as [|] eqn:Hwu.
                 - (* contradicts H, since would be the same *) apply eqb_eq in Hwu. rewrite Hwu in H. destruct H as [H | H].
                   + destruct H as [_ H]. unfold node_in_path in H. simpl in H. rewrite eqb_refl in H. simpl in H. discriminate H.
                   + unfold path_out_of_node in H. simpl in H. rewrite eqb_refl in H. destruct (edge_in_graph (u, h) G) as [|].
                     * destruct H as [b Hb]. destruct Hb as [Hb1 Hb2]. rewrite Hb1 in Hb2. inversion Hb2. destruct b as [|]. discriminate H0. discriminate H0.
                     * destruct H as [b Hb]. destruct Hb as [Hb1 Hb2]. rewrite Hb1 in Hb2. inversion Hb2. destruct b as [|]. discriminate H0. discriminate H0.
                 - assert (Houtw: path_out_of_node w (u, v, h :: lhv) G = path_out_of_node w (h, v, lhv) G).
                   { apply path_out_of_node_cat. apply Hwu. }
                   assert (Houtw': path_out_of_node w (u, v, h :: t) G = path_out_of_node w (h, v, t) G).
                   { apply path_out_of_node_cat. apply Hwu. }
                   unfold nodes in *. rewrite Houtw in H. rewrite Houtw' in H.
                   assert (Hnode: node_in_path w (u, v, h :: lhv) = node_in_path w (h, v, lhv)).
                   { symmetry. apply node_in_path_cat. apply Hwu. }
                   assert (Hnode': node_in_path w (u, v, h :: t) = node_in_path w (h, v, t)).
                   { symmetry. apply node_in_path_cat. apply Hwu. }
                   rewrite Hnode in H. rewrite Hnode' in H. apply Hout in H. rewrite Houtw. apply H. }

               exists Dh. split.
               { unfold nodes in *. rewrite HFcol. apply HDh. }
               intros c Hc. unfold nodes in *. rewrite HFcol in Hc. destruct HDh as [_ HDh]. pose proof Hc as Hc'. apply HDh in Hc. destruct Hc as [Hc | Hc].
               left. apply Hc.
               right. destruct Hc as [p [d Hc]]. exists p. exists d.
               rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite and_comm. rewrite <- and_assoc.
               split. repeat split; apply Hc.
               apply overlap_flip. simpl.
               assert (Hu: member u (p ++ [d]) = false).
               { destruct (member u (p ++ [d])) as [|] eqn:Hu.
                 - assert (HuL': In u L).
                   { apply collider_descendants_from_assignments_mem with (D := Dh) (G := G) (c := c) (p' := (h, v, lhv)) (p := p) (d := d).
                     apply Hc'. 2: { apply HLh. } 2: { apply member_In_equiv. apply Hu. }
                     split. apply Hc. destruct (d =? c) as [|] eqn:Hdc.
                     { destruct Hc as [_ [HdZ [_ [_ [HcZ _]]]]]. simpl in HcZ. destruct (member c Z) as [|] eqn:HcZ'. discriminate HcZ.
                       apply member_In_equiv_F in HcZ'. exfalso. apply HcZ'. apply eqb_eq in Hdc. rewrite <- Hdc. apply HdZ. }
                     { reflexivity. } }
                   apply member_In_equiv_F in HuL. exfalso. apply HuL. apply HuL'.
                 - reflexivity. }
               rewrite Hu. destruct Hc as [_ [_ [_ [_ [_ [Hc _]]]]]]. apply overlap_flip in Hc. apply Hc.

           --- (* CASE 2C *)
               assert (Huh: is_edge (u, h) G = true).
               { simpl in Hh. destruct lhv as [| hlhv tlhv].
                 - simpl in Hh. destruct (is_collider_bool u v h G) as [|] eqn:Huhv.
                   + unfold is_collider_bool in Huhv. apply split_and_true in Huhv. apply Huhv.
                   + exfalso. apply Hh.
                 - simpl in Hh. destruct (is_collider_bool u hlhv h G) as [|] eqn:Huhv.
                   + unfold is_collider_bool in Huhv. apply split_and_true in Huhv. apply Huhv.
                   + assert (Hmem: In h (hlhv :: tlhv)).
                     { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := h) in Hlhv. apply Hlhv. right. right. apply Hh. }
                     destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. exfalso. apply Hlhv. apply Hmem. }

               assert (Hhv: (lhv = [] -> is_edge (v, h) G = true) /\ (forall (hlhv: node) (tlhv: nodes), lhv = hlhv :: tlhv -> is_edge (hlhv, h) G = true)).
               { split.
                 - intros Hlhv0. rewrite Hlhv0 in Hh. simpl in Hh.
                   destruct (is_collider_bool u v h G) as [|] eqn:Huhv.
                   * unfold is_collider_bool in Huhv. apply split_and_true in Huhv. apply Huhv.
                   * exfalso. apply Hh.
                 - intros hlhv tlhv Hlhv0. rewrite Hlhv0 in *. simpl in Hh. destruct (is_collider_bool u hlhv h G) as [|] eqn:Huhv.
                   + unfold is_collider_bool in Huhv. apply split_and_true in Huhv. apply Huhv.
                   + assert (Hmem: In h (hlhv :: tlhv)).
                     { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := h) in Hlhv. apply Hlhv. right. right. apply Hh. }
                     destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. exfalso. apply Hlhv. apply Hmem. }

               assert (Hcol: find_colliders_in_path (u, v, h :: lhv) G = h :: find_colliders_in_path (h, v, lhv) G).
               { simpl. destruct lhv as [| hlhv tlhv].
                 - simpl. simpl in Hh. destruct (is_collider_bool u v h G) as [|]. reflexivity. exfalso. apply Hh.
                 - simpl. simpl in Hh. destruct (is_collider_bool u hlhv h G) as [|]. reflexivity.
                   assert (Hhmem: In h (hlhv :: tlhv)).
                   { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := h) in Hlhv. apply Hlhv. right. right. apply Hh. }
                   destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. exfalso. apply Hlhv. apply Hhmem. }

               assert (Hconn': d_connected_2 (u, v, h :: lhv) G Z).
               { apply d_connected_cat. apply HG. apply Hlhv. right. right. split. apply Hh.

                 pose proof Hconn as Hconn'. destruct Hconn as [_ [_ Hconn]]. simpl in Hconn. destruct t as [| ht tt].
                 + simpl in Hconn. destruct (is_collider_bool u v h G) as [|] eqn:Hcolht.
                   * apply forallb_true_iff_mem with (x := h) in Hconn. apply Hconn. left. reflexivity.
                   * (* h is not a collider in original path, so path_out = true in original, false in new *)
                     assert (Houth: ((exists (du : node) (pu : nodes),
                                         is_directed_path_in_graph (h, du, pu) G = true /\
                                         In du Z /\ ~ In h Z) \/
                                      path_out_of_node h (h, v, lhv) G <> Some true /\ In h Z) /\
                                     (path_out_of_node h (h, v, lhv) G = Some true -> ~ In h Z)).
                     { apply Hout. right. exists true. split.
                       - unfold path_out_of_node. simpl. rewrite eqb_refl. unfold is_collider_bool in Hcolht.
                         rewrite Huh in Hcolht. simpl in Hcolht. simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath.
                         destruct Hpath as [_ Hpath]. rewrite Hcolht in Hpath. rewrite andb_comm in Hpath. rewrite orb_comm in Hpath. simpl in Hpath.
                         simpl. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. rewrite Hpath. reflexivity.
                       - unfold path_out_of_node. simpl. rewrite eqb_refl. destruct lhv as [| hlhv tlhv] eqn:Hlhveq.
                         + simpl. assert (Huhv: is_edge (v, h) G = true). { apply Hhv. reflexivity. } apply acyclic_no_two_cycle in Huhv.
                           rewrite edge_in_graph_equiv in Huhv. rewrite Huhv. reflexivity. apply HG. apply HG.
                         + simpl. assert (Huhv: is_edge (hlhv, h) G = true). { apply Hhv with (hlhv := hlhv) (tlhv := tlhv). reflexivity. } apply acyclic_no_two_cycle in Huhv.
                           rewrite edge_in_graph_equiv in Huhv. rewrite Huhv. reflexivity. apply HG. apply HG. }

                     assert (HhZ: ~In h Z).
                     { apply intermediate_node_in_path with (x := h) in Hpath. assert (Hhh: In h [h]). { left. reflexivity. } apply Hpath in Hhh.
                       destruct Hhh as [Hhh | [Hhh | Hhh]].
                       - destruct Hconn' as [Hconn' _]. apply no_overlap_non_member with (x := h) in Hconn'. apply Hconn'. apply Hhh.
                       - destruct Hconn' as [_ [Hconn' _]]. apply no_overlap_non_member with (x := h) in Hconn'. apply Hconn'. apply Hhh.
                       - simpl in Hhh. rewrite Hcolht in Hhh. exfalso. apply Hhh. }

                     destruct Houth as [[[dh [ph Houth]] | Houth] _].
                     unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists dh. split.
                     apply find_descendants_correct. right. exists (h, dh, ph). split. apply Houth. apply path_start_end_refl. apply Houth.
                     exfalso. apply HhZ. apply Houth.

                 + simpl in Hconn. destruct (is_collider_bool u ht h G) as [|] eqn:Hcolht.
                   * apply forallb_true_iff_mem with (x := h) in Hconn. apply Hconn. left. reflexivity.
                   * (* h is not a collider in original path, so path_out = true in original, false in new *)
                     assert (Houth: ((exists (du : node) (pu : nodes),
                                         is_directed_path_in_graph (h, du, pu) G = true /\
                                         In du Z /\ ~ In h Z) \/
                                      path_out_of_node h (h, v, lhv) G <> Some true /\ In h Z) /\
                                     (path_out_of_node h (h, v, lhv) G = Some true -> ~ In h Z)).
                     { apply Hout. right. exists true. split.
                       - unfold path_out_of_node. simpl. rewrite eqb_refl. unfold is_collider_bool in Hcolht.
                         rewrite Huh in Hcolht. simpl in Hcolht. simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath.
                         destruct Hpath as [_ Hpath]. rewrite Hcolht in Hpath. rewrite andb_comm in Hpath. rewrite orb_comm in Hpath. simpl in Hpath.
                         simpl. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. rewrite Hpath. reflexivity.
                       - unfold path_out_of_node. simpl. rewrite eqb_refl. destruct lhv as [| hlhv tlhv] eqn:Hlhveq.
                         + simpl. assert (Huhv: is_edge (v, h) G = true). { apply Hhv. reflexivity. } apply acyclic_no_two_cycle in Huhv.
                           rewrite edge_in_graph_equiv in Huhv. rewrite Huhv. reflexivity. apply HG. apply HG.
                         + simpl. assert (Huhv: is_edge (hlhv, h) G = true). { apply Hhv with (hlhv := hlhv) (tlhv := tlhv). reflexivity. } apply acyclic_no_two_cycle in Huhv.
                           rewrite edge_in_graph_equiv in Huhv. rewrite Huhv. reflexivity. apply HG. apply HG. }
                     assert (HhZ: ~In h Z).
                     { pose proof Hpath as Hpathh. apply intermediate_node_in_path with (x := h) in Hpath. assert (Hhh: In h (h :: ht :: tt)). { left. reflexivity. } apply Hpath in Hhh.
                       destruct Hhh as [Hhh | [Hhh | Hhh]].
                       - destruct Hconn' as [Hconn' _]. apply no_overlap_non_member with (x := h) in Hconn'. apply Hconn'. apply Hhh.
                       - destruct Hconn' as [_ [Hconn' _]]. apply no_overlap_non_member with (x := h) in Hconn'. apply Hconn'. apply Hhh.
                       - simpl in Hhh. rewrite Hcolht in Hhh.
                         assert (Htt: In h (ht :: tt)).
                         { assert (Hpathh': is_path_in_graph (h, v, ht :: tt) G = true). { simpl in Hpathh. destruct G as [V E]. apply split_and_true in Hpathh. apply Hpathh. }
                         apply intermediate_node_in_path with (x := h) in Hpathh'. apply Hpathh'. right. right. apply Hhh. }
                         apply acyclic_path_cat in Hcyc. destruct Hcyc as [_ [Hcyc _]]. exfalso. apply Hcyc. apply Htt. }

                     destruct Houth as [[[dh [ph Houth]] | Houth] _].
                     unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists dh. split.
                     apply find_descendants_correct. right. exists (h, dh, ph). split. apply Houth. apply path_start_end_refl. apply Houth.
                     exfalso. apply HhZ. apply Houth. }

               assert (Hh': In h Z \/ (~In h Z /\ exists (z: node) (dp: nodes), is_directed_path_in_graph (h, z, dp) G = true /\ acyclic_path_2 (h, z, dp) /\ overlap dp Z = false /\ In z Z)).
               { apply colliders_have_unblocked_path_to_descendant with (p := (u, v, h :: lhv)). apply Hh. apply Hconn'. }

               destruct Hh' as [Hh' | Hh'].
               { (* CASE 2C.1 *) exists (h :: lhv). split. repeat split.
                 { apply Hcyc. }
                 { intros Hmem. destruct Hmem as [Hmem | Hmem].
                   - unfold acyclic_path_2 in Hcyc. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. left. apply Hmem.
                   - apply member_In_equiv_F in Hulhv. apply Hulhv. apply Hmem. }
                 { unfold acyclic_path_2 in Hlhv. intros Hmem. destruct Hmem as [Hmem | Hmem].
                   - destruct Hlhv as [[[Hlhv _] _] _]. apply Hlhv. apply Hmem.
                   - destruct Hlhv as [[[_ [_ [Hlhv _]]] _] _]. apply Hlhv. apply Hmem. }
                 { destruct Hlhv as [[Hlhv _] _]. apply acyclic_path_correct_2 in Hlhv. apply acyclic_path_reverse in Hlhv.
                   simpl in Hlhv. rewrite reverse_list_append in Hlhv. simpl in Hlhv. apply split_and_true in Hlhv. destruct Hlhv as [_ Hlhv].
                   apply acyclic_path_reverse in Hlhv. rewrite reverse_list_append in Hlhv. rewrite <- reverse_list_twice in Hlhv. apply Hlhv. } split.
                 apply Hconn'. split. apply Hpath'. split.
                 { intros w H. destruct (w =? u) as [|] eqn:Hwu.
                   - (* contradicts H, since would be the same *) apply eqb_eq in Hwu. rewrite Hwu in H. destruct H as [H | H].
                     + destruct H as [_ H]. unfold node_in_path in H. simpl in H. rewrite eqb_refl in H. simpl in H. discriminate H.
                     + unfold path_out_of_node in H. simpl in H. rewrite eqb_refl in H. destruct (edge_in_graph (u, h) G) as [|].
                       * destruct H as [b Hb]. destruct Hb as [Hb1 Hb2]. rewrite Hb1 in Hb2. inversion Hb2. destruct b as [|]. discriminate H0. discriminate H0.
                       * destruct H as [b Hb]. destruct Hb as [Hb1 Hb2]. rewrite Hb1 in Hb2. inversion Hb2. destruct b as [|]. discriminate H0. discriminate H0.
                   - assert (Houtw: path_out_of_node w (u, v, h :: lhv) G = path_out_of_node w (h, v, lhv) G).
                     { apply path_out_of_node_cat. apply Hwu. }
                     assert (Houtw': path_out_of_node w (u, v, h :: t) G = path_out_of_node w (h, v, t) G).
                     { apply path_out_of_node_cat. apply Hwu. }
                     unfold nodes in *. rewrite Houtw in H. rewrite Houtw' in H.
                     assert (Hnode: node_in_path w (u, v, h :: lhv) = node_in_path w (h, v, lhv)).
                     { symmetry. apply node_in_path_cat. apply Hwu. }
                     assert (Hnode': node_in_path w (u, v, h :: t) = node_in_path w (h, v, t)).
                     { symmetry. apply node_in_path_cat. apply Hwu. }
                     rewrite Hnode in H. rewrite Hnode' in H. apply Hout in H. rewrite Houtw. apply H. }

                 exists ((h, ([], h)) :: Dh). split. unfold nodes in *. rewrite Hcol. split.
                 - simpl. rewrite eqb_refl. simpl. apply is_assignment_for_cat. apply HDh.
                 - intros w Hw. simpl in Hw. simpl. destruct (h =? w) as [|] eqn:Hhw. discriminate Hw. rewrite eqb_sym in Hhw. rewrite Hhw.
                   simpl. destruct HDh as [[_ HDh] _]. apply HDh. apply Hw.
                 - intros c Hc. unfold nodes in *. rewrite Hcol in Hc. destruct Hc as [Hc | Hc].
                   + left. rewrite <- Hc in *. split. simpl. rewrite eqb_refl. reflexivity. apply Hh'.
                   + assert (HcDh: get_assigned_value ((h, ([], h)) :: Dh) c = get_assigned_value Dh c).
                     { simpl. destruct (h =? c) as [|] eqn:Hhc.
                       - apply eqb_eq in Hhc. rewrite <- Hhc in Hc.
                         assert (Hhmem: In h lhv).
                         { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := h) in Hlhv. apply Hlhv. right. right. apply Hc. }
                         destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. exfalso. apply Hlhv. apply Hhmem.
                       - reflexivity. }
                     rewrite HcDh. pose proof Hc as Hcolc.
                     destruct HDh as [_ HDh]. apply HDh in Hc. destruct Hc as [Hc | Hc]. left. apply Hc. right.
                     destruct Hc as [p [d Hc]]. exists p. exists d. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc.
                     split. repeat split; apply Hc. split.
                     apply overlap_flip. simpl. destruct (member u (p ++ [d])) as [|] eqn:Humem.
                     * exfalso. apply member_In_equiv_F in HuL. apply HuL. 
                       apply collider_descendants_from_assignments_mem with (D := Dh) (p' := (h, v, lhv)) (p := p) (d := d) (c := c) (G := G).
                       apply Hcolc. split. apply Hc. destruct (d =? c) as [|] eqn:Hdc. apply eqb_eq in Hdc. destruct Hc as [_ [HdZ [_ [_ [HcZ _]]]]].
                       exfalso. apply no_overlap_non_member with (x := c) in HcZ. apply HcZ. left. reflexivity. rewrite <- Hdc. apply HdZ. reflexivity.
                       apply HLh. apply member_In_equiv. apply Humem.
                     * destruct Hc as [_ [_ [_ [_ [_ [Hc _]]]]]]. apply overlap_flip in Hc. apply Hc.
                     * intros c' d' p' Hc'. simpl in Hc'. destruct (h =? c') as [|] eqn:Hhc'.
                       -- destruct Hc' as [Hcc' Hc']. inversion Hc'. rewrite <- H1. apply eqb_eq in Hhc'. rewrite <- Hhc'.
                          apply overlap_flip. simpl. rewrite <- Hhc' in Hcc'. rewrite Hcc'. destruct (member h (p ++ [d])) as [|] eqn:Hmem.
                          ++ destruct Hc as [_ [_ [_ [_ [_ [Hc _]]]]]]. apply no_overlap_non_member with (x := h) in Hc. exfalso. apply Hc. apply member_In_equiv. apply Hmem.
                             left. reflexivity.
                          ++ reflexivity.
                       -- apply Hc. apply Hc'. }

               { destruct Hh' as [HhZ [zh [ph Hh']]].
                 assert (Hacyc: forall (cy dy y: node) (l1 l2 l3: nodes), l1 ++ [y] ++ l2 = l3 ++ [dy] /\ acyclic_path_2 (cy, dy, l3)
                                   -> acyclic_path_2 (cy, y, l1)).
                 { intros cy dy y l1 l2 l3 [H1 H2].
                   destruct (rev l2) as [| hl2 tl2] eqn:Hl.
                   - assert (Hl': rev l2 = [] -> y = dy /\ l1 = l3). { apply Hl2. apply H1. } apply Hl' in Hl.
                     clear Hl'. destruct Hl as [Hl Hl']. rewrite Hl. rewrite Hl'. apply H2.
                   - assert (Hl': rev l2 = hl2 :: tl2 -> dy = hl2 /\ l3 = l1 ++ [y] ++ rev tl2). { apply Hl2. apply H1. } apply Hl' in Hl. clear Hl'.
                     destruct Hl as [Hl Hl']. apply subpath_still_acyclic_2 with (v := dy) (l2 := rev tl2) (l3 := l3).
                     split. symmetry. apply Hl'. apply H2. }

                 assert (Hcyccy': forall (cy dy y: node) (py lhcy1 lhcy2 lcyd1 lcyd2: nodes),
                                  (In dy Z /\
                                   is_directed_path_in_graph (cy, dy, py) G = true /\
                                   acyclic_path_2 (cy, dy, py) /\
                                   overlap (cy :: py) Z = false /\
                                   overlap (py ++ [dy]) (h :: lhv ++ [v]) = false /\
                                   (forall (c' d' : node) (p' : nodes),
                                    (cy =? c') = false /\
                                    get_assigned_value Dh c' = Some (p', d') ->
                                    overlap (cy :: py ++ [dy]) (c' :: p' ++ [d']) = false))
                                  -> lhcy1 ++ [cy] ++ lhcy2 = lhv
                                  -> py ++ [dy] = lcyd1 ++ [y] ++ lcyd2
                                  -> acyclic_path_2 (y, v, rev lcyd1 ++ [cy] ++ lhcy2)
                                     /\ ~In h (rev lcyd1 ++ [cy] ++ lhcy2)).
                 { intros cy dy y py lhcy1 lhcy2 lcyd1 lcyd2 Hpdy'' Hcy Hy'. split.
                   { apply concat_paths_acyclic. split.
                     -- intros Hyv. destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := y) in Hpdy''. apply Hpdy''.
                        rewrite Hy'. apply membership_append_r. left. reflexivity.
                        right. apply membership_append_r. left. symmetry. apply Hyv.
                     -- split.
                        ++ apply reverse_path_still_acyclic. apply Hacyc with (dy := dy) (l2 := lcyd2) (l3 := py). split. symmetry. apply Hy'.
                           apply Hpdy''.
                        ++ apply subpath_still_acyclic with (w := h) (l1 := lhcy1) (l3 := lhv). split. apply Hcy. apply Hlhv.
                     -- split.
                        ++ (* Hpdy'', cy's desc path cannot intersect lhv *)
                           intros Hmem. destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := y) in Hpdy''.
                           apply Hpdy''. rewrite Hy'. apply membership_append_r. left. reflexivity.
                           right. apply membership_append. rewrite <- Hcy. apply membership_append_r. apply membership_append_r. apply Hmem.

                        ++ (* Hpdy'', v cannot intersect cy's desc path *)
                           intros Hmem. destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := v) in Hpdy''.
                           apply Hpdy''. rewrite Hy'. apply membership_append. apply membership_rev. apply Hmem.
                           right. apply membership_append_r. left. reflexivity.

                     -- (* Hpdy'', cy's desc path cannot intersect lhv *)
                        apply no_overlap_non_member. intros w Hw Hw'. destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := w) in Hpdy''.
                        apply Hpdy''. rewrite Hy'. apply membership_append. apply membership_rev. apply Hw'.
                        right. apply membership_append. rewrite <- Hcy. apply membership_append_r. apply membership_append_r. apply Hw. }
                   { intros Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                     -- destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := h) in Hpdy''. apply Hpdy''.
                        rewrite Hy'. apply membership_append. apply membership_rev. apply Hmem. left. reflexivity.
                     -- destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. apply Hlhv.
                        rewrite <- Hcy. apply membership_append_r. apply Hmem. } }

                 assert (Hpathcy': forall (cy dy y: node) (py l1 l2: nodes),
                                  is_directed_path_in_graph (cy, dy, py) G = true
                                  -> py ++ [dy] = l1 ++ [y] ++ l2
                                  -> is_directed_path_in_graph (cy, y, l1) G = true).
                 { intros cy dy y py l1 l2 Hdir Hpdy. symmetry in Hpdy.
                   destruct (rev l2) as [| hl2 tl2] eqn:Hrevl2.
                   - apply Hl2 in Hpdy. apply Hpdy in Hrevl2. destruct Hrevl2 as [Hdy Hpy]. rewrite Hdy. rewrite Hpy. apply Hdir.
                   - apply Hl2 in Hpdy. apply Hpdy in Hrevl2. destruct Hrevl2 as [Hdy Hpy].
                     apply subpath_still_directed_2 with (v := dy) (l2 := rev tl2) (l3 := py). split. symmetry. apply Hpy. apply Hdir. }

                 assert (Hconncy: forall (p l1 l2: nodes) (d c x: node),
                                      p ++ [d] = l1 ++ [x] ++ l2
                                      -> is_directed_path_in_graph (c, d, p) G = true /\ overlap p Z = false
                                      -> d_connected_2 (c, x, l1) G Z).
                 { intros p l1 l2 d c x Hpd [Hdir Hover].
                   assert (Hpath'': is_directed_path_in_graph (c, x, l1) G = true).
                   { apply Hpathcy' with (dy := d) (py := p) (l2 := l2). apply Hdir. apply Hpd. }
                   repeat split.
                   + apply no_overlap_non_member. intros w Hw Hw'.
                     assert (Hw'': In w l1).
                     { apply directed_path_is_path in Hpath''. apply intermediate_node_in_path with (x := w) in Hpath''. apply Hpath''. left. apply Hw. }
                     apply no_overlap_non_member with (x := w) in Hover. apply Hover. symmetry in Hpd.
                     destruct (rev l2) as [| hl2 tl2] eqn:Hl2eq.
                     * apply Hl2 in Hpd. apply Hpd in Hl2eq. destruct Hl2eq as [_ Hl2eq]. rewrite <- Hl2eq. apply Hw''.
                     * apply Hl2 in Hpd. apply Hpd in Hl2eq. destruct Hl2eq as [_ Hl2eq]. rewrite Hl2eq. apply membership_append. apply Hw''.
                     * apply Hw'.
                   + apply no_overlap_non_member. intros w Hw Hw'.
                     assert (Hw'': In w l1).
                     { apply directed_path_is_path in Hpath''. apply intermediate_node_in_path with (x := w) in Hpath''. apply Hpath''. right. left. apply Hw. }
                     assert (Hmed: In w (find_mediators_in_path (c, x, l1) G)). { apply directed_path_all_mediators. split. apply Hpath''. apply Hw''. }
                     apply if_confounder_then_not_mediator_path in Hw. destruct Hw as [Hw _]. apply Hw. apply Hmed. apply HG.
                   + apply forallb_true_iff_mem. intros w Hw.
                     assert (Hw'': In w l1).
                     { apply directed_path_is_path in Hpath''. apply intermediate_node_in_path with (x := w) in Hpath''. apply Hpath''. right. right. apply Hw. }
                     assert (Hmed: In w (find_mediators_in_path (c, x, l1) G)). { apply directed_path_all_mediators. split. apply Hpath''. apply Hw''. }
                     apply if_collider_then_not_mediator_path in Hw. destruct Hw as [Hw _]. exfalso. apply Hw. apply Hmed. apply HG. }

                 assert (Huph: member u (ph ++ [zh]) = false).
                 { (* since u->h->...ph...->zh is a directed path and G is acyclic *)
                   destruct (member u (ph ++ [zh])) as [|] eqn:Hu.
                   - apply member_In_equiv in Hu.
                     (* cycle u -> h ->...ph..-> u *) apply membership_splits_list in Hu. destruct Hu as [lphu1 [lphu2 Hlphu]].
                     destruct HG as [_ HG]. apply contains_cycle_false_correct with (p := (u, u, h :: lphu1)) in HG.
                     + exfalso. destruct HG as [HG _]. apply HG. reflexivity.
                     + apply directed_path_is_path. destruct (rev lphu2) as [| hlphu2 tlphu2] eqn:Hlphu2.
                       -- assert (Huv: rev lphu2 = [] -> u = zh /\ lphu1 = ph). { apply Hl2. apply Hlphu. } apply Huv in Hlphu2. destruct Hlphu2 as [Hlphu2 Hlphu2'].
                          simpl. apply split_and_true. split. apply Huh. rewrite Hlphu2. rewrite Hlphu2'. apply Hh'.
                       -- apply subpath_still_directed_2 with (v := zh) (l2 := rev tlphu2) (l3 := h :: ph). split. simpl. f_equal.
                          assert (Hlphu1: rev lphu2 = hlphu2 :: tlphu2 -> zh = hlphu2 /\ ph = lphu1 ++ [u] ++ rev tlphu2).
                          { apply Hl2. apply Hlphu. } apply Hlphu1 in Hlphu2. clear Hlphu1. symmetry. apply Hlphu2. simpl. apply split_and_true. split. apply Huh. apply Hh'.
                   - reflexivity. }

                 destruct (overlap (ph ++ [zh]) (lhv ++ [v])) as [|] eqn:Hoverh.
                 - apply overlap_rev_true in Hoverh.
                   apply list_has_first_elt_in_common_with_other_list in Hoverh. destruct Hoverh as [ph1 [ph2 [lx1 [lx2 [x Hx]]]]]. rewrite reverse_list_append in Hx. simpl in Hx.

                   assert (Hcychx: acyclic_path_2 (h, x, ph1)).
                   { apply Hacyc with (dy := zh) (l2 := ph2) (l3 := ph). split. symmetry. apply Hx. apply Hh'. }

                   assert (Hdir: is_directed_path_in_graph (u, x, h :: ph1) G = true).
                   { simpl. apply split_and_true. split. apply Huh.
                     assert (Hdir: is_directed_path_in_graph (h,x, ph1) G = true).
                     { destruct (rev ph2) as [| hph2 tph2] eqn:Hph2.
                       - assert (Hph2': rev ph2 = [] -> x = zh /\ ph1 = ph). { apply Hl2. symmetry. apply Hx. } apply Hph2' in Hph2. clear Hph2'.
                         destruct Hph2 as [Hph2 Hph2']. rewrite Hph2'. rewrite Hph2. apply Hh'.
                       - apply subpath_still_directed_2 with (v := zh) (l2 := rev tph2) (l3 := ph). split.
                         assert (Hph2': rev ph2 = hph2 :: tph2 -> zh = hph2 /\ ph = ph1 ++ [x] ++ rev tph2). { apply Hl2. symmetry. apply Hx. }
                         apply Hph2' in Hph2. symmetry. apply Hph2. apply Hh'. }
                     apply Hdir. }

                   destruct lx1 as [| hlx1 tlx1].
                   + (* CASE 2C.2: x = v *)
                     destruct Hx as [Hx [Hx' _]]. inversion Hx'. rewrite H0 in *.
                     exists (h :: ph1). (* directed path u -> h -> ... -> v *)

                     split.
                     { apply acyclic_path_correct_2. simpl. apply split_and_true. split.
                       - (* u not in [h, ph1] bc cycle *)
                         apply negb_true_iff. rewrite Hhu. apply member_In_equiv_F. intros F. apply member_In_equiv_F in Huph. apply Huph.
                         rewrite Hx. rewrite <- append_vs_concat. apply membership_append. apply F.
                       - apply acyclic_path_correct_2 in Hcychx. apply Hcychx. }

                     split.
                     { apply d_connected_cat. apply HG.
                       - apply Hconncy with (p := ph) (l2 := ph2) (d := zh). apply Hx. split. apply Hh'. apply Hh'.
                       - left. split.
                         + apply directed_path_all_mediators. split. apply Hdir. left. reflexivity.
                         + apply HhZ. } split.
                     { apply directed_path_is_path. apply Hdir. } split.

                     { intros w Hw.
                       assert (Hwuh: w =? u = false). { admit. } split.
                       destruct (w =? x) as [|] eqn:Hwx.
                       - admit. (* destruct x = zh or not (ph1) *)
                       - left. exists zh. admit.
                       - admit. }

                     exists []. assert (Hcol': find_colliders_in_path (u, x, h :: ph1) G = []). { admit. }
                     unfold nodes in *. unfold node in *. rewrite Hcol'. split. unfold is_exact_assignment_for. split. simpl. reflexivity. simpl. reflexivity.
                     intros c F. exfalso. apply F.

                   + (* CASE 2C.3: v = hlx1 *)
                     destruct Hx as [Hx [Hx' Hx'']]. inversion Hx'. rewrite <- H0 in *.
                     assert (Hbout: exists (b: bool), path_out_of_node x (h, v, lhv) G = Some b).
                     { admit. }
                     destruct Hbout as [b Hbout].

                     assert (HDx: exists (D: assignments (nodes * node)), get_collider_descendants_for_subpath Dh (find_colliders_in_path (x, v, rev tlx1) G) = Some D).
                     { apply collider_descendants_for_subpath_existence_2 with (u := h) (l1 := rev lx2) (L := L).
                       unfold concat. admit. }
                     destruct HDx as [Dx HDx].
                     assert (HL: exists (L: nodes), get_collider_descendants_from_assignments Dx (find_colliders_in_path (x, v, rev tlx1) G) = Some L).
                     { apply collider_descendants_from_assignments_existence. admit. }
                     destruct HL as [Lx HLx].

                     assert (Hlhvrev: lhv = rev lx2 ++ [x] ++ rev tlx1).
                     { rewrite reverse_list_twice with (l := lhv).
                       rewrite H1. rewrite reverse_list_append. simpl. rewrite <- app_assoc. reflexivity. }

                     assert (Hcycxv: acyclic_path_2 (x, v, rev tlx1)).
                     { apply subpath_still_acyclic with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }

                     assert (Hcyccy: forall (cy dy y: node) (py lcyv1 lcyv2 lcyd1 lcyd2: nodes),
                                  (In dy Z /\
                                   is_directed_path_in_graph (cy, dy, py) G = true /\
                                   acyclic_path_2 (cy, dy, py) /\
                                   overlap (cy :: py) Z = false /\
                                   overlap (py ++ [dy]) (h :: lhv ++ [v]) = false /\
                                   (forall (c' d' : node) (p' : nodes),
                                    (cy =? c') = false /\
                                    get_assigned_value Dh c' = Some (p', d') ->
                                    overlap (cy :: py ++ [dy]) (c' :: p' ++ [d']) = false))
                                  -> lcyv1 ++ [cy] ++ lcyv2 = rev tlx1
                                  -> py ++ [dy] = lcyd1 ++ [y] ++ lcyd2
                                  -> acyclic_path_2 (y, v, rev lcyd1 ++ [cy] ++ lcyv2)
                                     /\ ~In h (rev lcyd1 ++ [cy] ++ lcyv2)).
                     { intros cy dy y py lcyv1 lcyv2 lcyd1 lcyd2 Hpdy'' Hcy Hy'. apply Hcyccy' with (dy := dy) (py := py) (lcyd2 := lcyd2) (lhcy1 := rev lx2 ++ [x] ++ lcyv1).
                       apply Hpdy''. rewrite <- app_assoc. rewrite <- app_assoc. unfold node in *. rewrite Hcy. symmetry. apply Hlhvrev. apply Hy'. }

                     assert (HLcy: forall (cy dy y' w: node) (py: nodes),
                                   In cy (find_colliders_in_path (x, v, rev tlx1) G) /\
                                   get_assigned_value Dx cy = Some (py, dy) /\
                                   (dy =? cy) = false /\ In y' (py ++ [dy])
                                   -> In w (py ++ [dy]) -> In w L).
                     { intros cy dy y' w py Hpdy Hmem.
                       apply collider_descendants_from_assignments_mem with (D := Dh) (p' := (h, v, lhv)) (p := py) (d := dy) (c := cy) (G := G).
                       -- apply subpath_preserves_colliders with (u := x) (l1 := rev lx2) (l2 := rev tlx1). split. symmetry. apply Hlhvrev.
                          left. apply Hpdy.
                       -- split. apply collider_descendants_preserved_for_subpath with (D' := Dx) (col := find_colliders_in_path (x, v, rev tlx1) G). apply HDx. apply Hpdy. apply Hpdy.
                       -- apply HLh.
                       -- apply Hmem. }

                     destruct (overlap ph1 Lx) as [|] eqn:Hoverph1.
                     { (* CASE 2C.3.i: take ph1 until intersect with desc path, then take that path to collider, then to v *)
                       apply overlap_rev_true in Hoverph1.
                       apply lists_have_first_elt_in_common in Hoverph1. destruct Hoverph1 as [ph11' [ph12' [Lx1 [Lx2 [y' Hy]]]]].
                       assert (Hy': exists (c d: node) (p: nodes), In c (find_colliders_in_path (x, v, rev tlx1) G)
                                   /\ get_assigned_value Dx c = Some (p, d) /\ d =? c = false
                                   /\ In y' (p ++ [d])).
                       { apply collider_descendants_from_assignments_belong_to_collider with (L := Lx). apply HLx. apply membership_rev.
                         destruct Hy as [_ [Hy _]]. rewrite Hy. apply membership_append_r. left. reflexivity. }
                       destruct Hy' as [cy [dy [py Hpdy]]].

                       assert (Hcolcy: In cy (find_colliders_in_path (h, v, lhv) G)).
                       { apply subpath_preserves_colliders with (u := x) (l1 := rev lx2) (l2 := rev tlx1). split. symmetry. apply Hlhvrev. left. apply Hpdy. }
                       destruct HDh as [HDh HDh']. apply HDh' in Hcolcy. clear HDh'.
                       pose proof Hpdy as Hpdy'. destruct Hpdy' as [_ [Hpdy' _]]. apply collider_descendants_preserved_for_subpath with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G) in Hpdy'.
                       2: { apply HDx. }
                       destruct Hcolcy as [Hcolcy | Hcolcy]. rewrite Hpdy' in Hcolcy. inversion Hcolcy. inversion H. rewrite H5 in Hpdy. destruct Hpdy as [_ [_ [Hpdy _]]]. rewrite eqb_refl in Hpdy. discriminate Hpdy.
                       destruct Hcolcy as [py' [dy' Hpdy'']]. destruct Hpdy'' as [Hpdy''' Hpdy'']. rewrite Hpdy' in Hpdy'''. inversion Hpdy'''. rewrite <- H2 in *. rewrite <- H3 in *. clear Hpdy'''. clear H2. clear H3.

                       assert (Hovery: overlap ph1 (py ++ [dy]) = true).
                       { apply overlap_has_member_in_common. exists y'. split.
                         - destruct Hy as [Hy _]. rewrite Hy. apply membership_append_r. left. reflexivity.
                         - apply Hpdy. }
                       apply list_has_first_elt_in_common_with_other_list in Hovery. destruct Hovery as [ph11 [ph12 [lyd1 [lyd2 [y Hy']]]]].

                       assert (Hcy: In cy (rev tlx1)).
                       { assert (Hpath'': is_path_in_graph (x, v, rev tlx1) G = true).
                         { apply subpath_still_path with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }
                         apply intermediate_node_in_path with (x := cy) in Hpath''. apply Hpath''. right. right. apply Hpdy. }
                       apply membership_splits_list in Hcy. destruct Hcy as [lcyv1 [lcyv2 Hcy]].

                       exists (h :: ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2).

                       assert (Hcychv: acyclic_path_2 (h, v, ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2)).
                       { apply concat_paths_acyclic. split. apply Hlhv. split.
                         - apply subpath_still_acyclic_2 with (v := x) (l2 := ph12) (l3 := ph1). split. symmetry. apply Hy'. apply Hcychx.
                         - apply Hcyccy with (dy := dy) (py := py) (lcyv1 := lcyv1) (lcyd2 := lyd2). apply Hpdy''. apply Hcy. apply Hy'.
                         - split.
                           + apply Hcyccy with (dy := dy) (py := py) (lcyv1 := lcyv1) (lcyd2 := lyd2) (y := y). apply Hpdy''. apply Hcy. apply Hy'.
                           + (* Hx'': ph1 does not intersect lhv after x *)
                             intros Hmem. apply no_overlap_non_member with (x := v) in Hx''. apply Hx''. rewrite Hx.
                             apply membership_append. destruct Hy' as [Hy' _]. rewrite Hy'. apply membership_append. apply Hmem.
                             left. reflexivity.
                         - (* lyd1: Hy'. [cy, lcyv2]: Hx'', ph1 does not intersect lhv after x *)
                           apply no_overlap_non_member. intros w Hw Hw'. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                           + destruct Hy' as [Hph1 [_ Hy']]. apply no_overlap_non_member with (x := w) in Hy'. apply Hy'. rewrite Hph1. apply membership_append. apply Hw'.
                             apply membership_rev. apply Hw.
                           + apply no_overlap_non_member with (x := w) in Hx''. apply Hx''. rewrite Hx. apply membership_append. destruct Hy' as [Hy' _]. rewrite Hy'. apply membership_append. apply Hw'.
                             right. apply membership_rev. rewrite <- Hcy. apply membership_append_r. apply Hw. }

                       split.
                       { apply acyclic_path_cat_2.
                         apply Hcychv.
                         { (* u not in [ph1,y] b/c cycle. u not in [rev lyd1] b/c HuL. u not in [cy, lcyv2] b/c Hulhv *)
                           intros Hmem. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. rewrite Hmem in Hhu. rewrite eqb_refl in Hhu. discriminate Hhu.
                           rewrite app_comm_cons in Hmem. rewrite app_assoc in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                           - apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                             + rewrite <- append_vs_concat in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                               * apply member_In_equiv_F in Huph. apply Huph. rewrite Hx. apply membership_append. destruct Hy' as [Hy' _]. rewrite Hy'.
                                 rewrite app_assoc. apply membership_append. apply Hmem.
                               * apply member_In_equiv_F in HuL. apply HuL. apply HLcy with (cy := cy) (dy := dy) (y' := y') (py := py). apply Hpdy.
                                 destruct Hy' as [_ [Hy' _]]. rewrite Hy'. rewrite app_assoc. apply membership_append. apply membership_rev. rewrite reverse_list_append. simpl. right. apply Hmem.
                             + apply member_In_equiv_F in Hulhv. apply Hulhv. rewrite Hlhvrev. apply membership_append_r. right. simpl. rewrite <- Hcy. apply membership_append_r. apply Hmem.
                           - destruct Hmem as [Hmem | Hmem]. destruct Hcyc as [Hcyc _]. apply Hcyc. symmetry. apply Hmem. apply Hmem. } }

                        assert (Hphv: is_path_in_graph (h, v, ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2) G = true).
                        { apply concat_paths_still_a_path. split.
                          - apply subpath_still_path_2 with (v := x) (l2 := ph12) (l3 := ph1). split. symmetry. apply Hy'.
                            apply directed_path_is_path. simpl in Hdir. apply split_and_true in Hdir. apply Hdir.
                          - apply concat_paths_still_a_path. split.
                            + apply reverse_path_in_graph. apply directed_path_is_path. apply Hpathcy' with (dy := dy) (py := py) (l2 := lyd2).
                              apply Hpdy''. apply Hy'.
                            + apply subpath_still_path with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. symmetry. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy. apply Hlhvrev.
                              apply Hlhv. }

                        split.
                        { (* h is a mediator and not in Z (HhZ). ph1 directed path. y collider with desc path to dy (already in Dx)
                             lyd1 directed path. cy now mediator, not in Z. everything else same as before *) 
                          apply d_connected_cat. apply HG.
                          - apply concat_d_connected_paths. apply HG. apply Hphv. split.
                            + apply Hconncy with (p := ph) (l2 := ph12 ++ [x] ++ ph2) (d := zh). destruct Hy' as [Hy' _]. rewrite Hx. rewrite Hy'. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
                              split. apply Hh'. apply Hh'.
                            + split.
                              * apply concat_d_connected_paths. apply HG.
                                unfold concat. apply subpath_still_path with (w := h) (l1 := ph11) (l3 := ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2). split. reflexivity. apply Hphv.
                                split.
                                -- apply reverse_d_connected_paths. apply Hconncy with (p := py) (l2 := lyd2) (d := dy). apply Hy'. split. apply Hpdy''.
                                   apply overlap_cat with (x := cy). apply Hpdy''.
                                -- split.
                                   ++ apply subpath_still_d_connected_gen with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. symmetry. rewrite <- app_assoc. rewrite <- app_assoc. unfold nodes in *. unfold node in *. rewrite Hcy. apply Hlhvrev.
                                      apply Hlhv.
                                   ++ unfold concat. apply subpath_still_acyclic with (w := h) (l1 := ph11) (l3 := ph11 ++ [y] ++ rev lyd1 ++ [cy] ++ lcyv2). split. reflexivity. apply Hcychv.
                                -- left. apply and_comm. split.
                                   ++ destruct Hpdy'' as [_ [_ [_ [Hpdy'' _]]]]. simpl in Hpdy''. destruct (member cy Z) as [|] eqn:HcyZ. discriminate Hpdy''. apply member_In_equiv_F. apply HcyZ.
                                   ++ apply collider_becomes_mediator_when_concat_directed with (x := x) (dy := dy) (txv := rev tlx1) (py := py) (lv1 := lcyv1) (ly2 := lyd2).
                                      apply Hpdy. apply Hcy.
                                      apply subpath_still_acyclic with (w := h) (l1 := rev lx2) (l3 := lhv). split. simpl in Hcy. symmetry. apply Hlhvrev. apply Hlhv.
                                      apply Hy'. apply Hpdy''.
                              * apply Hcychv.
                            + right. right. rewrite and_comm. split.
                              * unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists dy. rewrite and_comm. split. apply Hpdy''.
                                apply find_descendants_correct. destruct Hy' as [_ [Hy' _]]. symmetry in Hy'. destruct (rev lyd2) as [| hlyd2 tlyd2] eqn:Hlyd2.
                                -- apply Hl2 in Hy'. left. apply Hy'. apply Hlyd2.
                                -- apply Hl2 in Hy'. right. exists (y, dy, rev tlyd2). split. apply subpath_still_directed with (w := cy) (l1 := lyd1) (l3 := py). split. symmetry. apply Hy' with (hl2 := hlyd2) (tl2 := tlyd2). apply Hlyd2. apply Hpdy''.
                                   apply path_start_end_refl.
                              * apply subpath_preserves_colliders with (u := cy) (l1 := ph11 ++ [y] ++ rev lyd1) (l2 := lcyv2). split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. right.
                                apply intersection_of_directed_paths_is_collider with (d1 := zh) (d2 := dy) (l1 := ph) (l2 := py) (l1'' := ph12 ++ x :: ph2) (l2'' := lyd2). apply Hh'. apply Hpdy''.
                                destruct Hy' as [Hy' _]. rewrite app_assoc. rewrite app_assoc. unfold nodes in *. unfold node in *. rewrite <- app_assoc with (l := ph11). rewrite <- Hy'. apply Hx. apply Hy'.
                          - left. apply and_comm. split.
                            + apply HhZ.
                            + assert (Hph: ph ++ [zh] = ph11 ++ [y] ++ (ph12 ++ x :: ph2)). { destruct Hy' as [Hy' _]. rewrite Hx. rewrite Hy'. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. }
                              apply mediator_means_edge_out with (c := h) (G := G) in Hph.
                              destruct ph11 as [| hph11 tph11].
                              * apply mediators_vs_edges_in_path. exists u. exists y. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                                -- apply Huh.
                                -- destruct Hph as [Hph _]. apply Hph. reflexivity.
                              * apply mediators_vs_edges_in_path. exists u. exists hph11. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                                -- apply Huh.
                                -- destruct Hph as [_ Hph]. apply Hph with (tly1 := tph11). reflexivity.
                              * apply Hh'. }

                        split.
                        { simpl. destruct G as [V E]. rewrite Huh. simpl. apply Hphv. }

                        split. { intros w Hw. (* [h, y): pydy, not in Z. y: either = dy or not in Z. [lyd1]: path in, exists dy, py *) admit. }
                        assert (HDcy: exists (D: assignments (nodes * node)), get_collider_descendants_for_subpath Dh (find_colliders_in_path (cy, v, lcyv2) G) = Some D).
                        { apply collider_descendants_for_subpath_existence_2 with (u := h) (l1 := lcyv1) (L := L).
                          unfold concat. admit. }
                        destruct HDcy as [Dcy HDcy].
                        (* destruct on y = dy or not *) exists ((y, (py, dy)) :: Dcy). admit. }

                     destruct ((negb b) && (negb (eqblist ph2 [])) && overlap ph2 Lx) as [|] eqn:HbLx.
                     * (* CASE 2C.3.ii *) apply split_and_true in HbLx. destruct HbLx as [Hb Hoverx]. apply split_and_true in Hb. destruct Hb as [Hb Hph2'].
                       apply negb_true_iff in Hb. rewrite Hb in *. clear Hb. apply negb_true_iff in Hph2'. destruct (rev ph2) as [| hph2 tph2] eqn:Hph2.
                       rewrite reverse_list_twice with (l := ph2) in Hph2'. rewrite Hph2 in Hph2'. simpl in Hph2'. discriminate Hph2'. clear Hph2'.
                       pose proof Hx as Hx'''. symmetry in Hx'''. apply Hl2 in Hx'''. apply Hx''' in Hph2 as Hph2'. destruct Hph2' as [Hzh Hph]. rewrite <- Hzh in *. clear Hzh. clear Hx'''.
                       clear Hx'. assert (Hph2': ph2 = rev tph2 ++ [zh]). { rewrite reverse_list_twice with (l := ph2). rewrite Hph2. simpl. reflexivity. }

                       (* choose first overlap in path of last collider that overlaps *)
                       (* use first overlap of path + last overlap of Lx to find collider, then find first overlap in two paths *)
                       apply overlap_rev_true in Hoverx.
                       apply lists_have_first_elt_in_common in Hoverx. destruct Hoverx as [tzh1 [tzh2 [Lx1 [Lx2 [y' Hy]]]]].
                       assert (Hy': exists (c d: node) (p: nodes), In c (find_colliders_in_path (x, v, rev tlx1) G)
                                   /\ get_assigned_value Dx c = Some (p, d) /\ d =? c = false
                                   /\ In y' (p ++ [d])).
                       { apply collider_descendants_from_assignments_belong_to_collider with (L := Lx). apply HLx. apply membership_rev.
                         destruct Hy as [_ [Hy _]]. rewrite Hy. apply membership_append_r. left. reflexivity. }
                       destruct Hy' as [cy [dy [py Hpdy]]].

                       assert (Hovery: overlap ph2 (py ++ [dy]) = true).
                       { apply overlap_has_member_in_common. exists y'. split.
                         - destruct Hy as [Hy _]. rewrite Hy. apply membership_append_r. left. reflexivity.
                         - apply Hpdy. }
                       apply lists_have_first_elt_in_common in Hovery. destruct Hovery as [lxy1 [lxy2 [lcyd1 [lcyd2 [y Hy']]]]].

                       assert (Hlxy1y: forall (w: node), In w (lxy1 ++ [y]) -> In w (ph ++ [zh])).
                       { intros w Hmem. rewrite Hx. apply membership_append_r. right. destruct Hy' as [Hy' _]. rewrite Hy'. rewrite app_assoc. apply membership_append. apply Hmem. }

                       assert (Hlxy1: forall (w: node), In w lxy1 -> In w ph).
                       { intros w Hmem. rewrite reverse_list_twice with (l := ph2) in Hy'.
                         destruct Hy' as [Hy' _]. rewrite Hph2 in Hy'. simpl in Hy'. symmetry in Hy'. apply Hl2 in Hy'. rewrite Hph. apply membership_append_r. right.
                         destruct (rev lxy2) as [| hlxy2 tlxy2] eqn:Hlxy2.
                         apply Hy' in Hlxy2. destruct Hlxy2 as [_ Hlxy2]. simpl. unfold nodes in *. unfold node in *. rewrite <- Hlxy2. apply Hmem.
                         apply Hy' in Hlxy2. destruct Hlxy2 as [_ Hlxy2]. simpl. unfold nodes in *. unfold node in *. rewrite Hlxy2. apply membership_append. apply Hmem. }

                       assert (Hcolcy: In cy (find_colliders_in_path (h, v, lhv) G)).
                       { apply subpath_preserves_colliders with (u := x) (l1 := rev lx2) (l2 := rev tlx1). split. symmetry. apply Hlhvrev. left. apply Hpdy. }
                       destruct HDh as [HDh HDh']. apply HDh' in Hcolcy. clear HDh'.
                       pose proof Hpdy as Hpdy'. destruct Hpdy' as [_ [Hpdy' _]]. apply collider_descendants_preserved_for_subpath with (D := Dh) (col := find_colliders_in_path (x, v, rev tlx1) G) in Hpdy'.
                       2: { apply HDx. }
                       destruct Hcolcy as [Hcolcy | Hcolcy]. rewrite Hpdy' in Hcolcy. inversion Hcolcy. inversion H. rewrite H5 in Hpdy. destruct Hpdy as [_ [_ [Hpdy _]]]. rewrite eqb_refl in Hpdy. discriminate Hpdy.
                       destruct Hcolcy as [py' [dy' Hpdy'']]. destruct Hpdy'' as [Hpdy''' Hpdy'']. rewrite Hpdy' in Hpdy'''. inversion Hpdy'''. rewrite <- H2 in *. rewrite <- H3 in *. clear Hpdy'''. clear H2. clear H3.

                       assert (Hcy: In cy (rev tlx1)).
                       { assert (Hpath'': is_path_in_graph (x, v, rev tlx1) G = true). { admit. }
                         apply intermediate_node_in_path with (x := cy) in Hpath''. apply Hpath''. right. right. apply Hpdy. }
                       apply membership_splits_list in Hcy. destruct Hcy as [lcyv1 [lcyv2 Hcy]].

                       exists (h :: ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).

                       assert (Hcychv: acyclic_path_2 (concat h x v ph1 (lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2))).
                       { apply concat_paths_acyclic.
                         - split. apply Hlhv. split. apply Hcychx. apply concat_paths_acyclic.
                           + (* x->..tph2..->zh acyclic, this is a subpath. *) split.
                             destruct Hlhv as [[Hlhv _] _]. destruct Hlhv as [_ [_ [Hlhv _]]]. intros Hxv. apply Hlhv. apply membership_rev. rewrite H1.
                             apply membership_append_r. left. apply Hxv. split.
                             * apply Hacyc with (dy := zh) (l2 := lxy2) (l3 := rev tph2). split. symmetry. unfold nodes in *. unfold node in *. rewrite <- Hph2'. apply Hy'.
                               apply subpath_still_acyclic with (w := h) (l1 := ph1) (l3 := ph1 ++ [x] ++ rev tph2). split. reflexivity.
                               unfold node in *. rewrite <- Hph. apply Hh'.
                             * apply Hcyccy with (dy := dy) (py := py) (lcyd2 := lcyd2) (lcyv1 := lcyv1). apply Hpdy''. apply Hcy. apply Hy'.

                           + split.
                             * intros Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                               -- (* lcyd1: cy's desc path cannot intersect lhv *)
                                  destruct Hpdy'' as [_ [_ [_ [_ [Hpdy'' _]]]]]. apply no_overlap_non_member with (x := x) in Hpdy''.
                                  apply Hpdy''. destruct Hy' as [_ [Hy' _]]. rewrite Hy'. apply membership_append. apply membership_rev. apply Hmem.
                                  right. apply membership_append. rewrite Hlhvrev. apply membership_append_r. left. reflexivity.
                               -- (* [cy, lcyv1]: lhv acyclic *) unfold acyclic_path_2 in Hcycxv. destruct Hcycxv as [_ [Hcycxv _]]. apply Hcycxv.
                                  rewrite <- Hcy. apply membership_append_r. apply Hmem.

                             * (* Hx, v cannot intersect h's desc path *)
                               intros Hmem. apply no_overlap_non_member with (x := v) in Hx''. apply Hx''. apply Hlxy1 in Hmem. apply membership_append. apply Hmem.
                               left. reflexivity.

                           + (* lcyd1: Hy'. [cy, lcyv2]: Hx *)
                             apply no_overlap_non_member. intros w Hw Hw'. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                             * destruct Hy' as [_ [_ Hy']]. apply no_overlap_non_member with (x := w) in Hy'. apply Hy'. apply Hw'. apply membership_rev. apply Hw.
                             * apply no_overlap_non_member with (x := w) in Hx''. apply Hx''. apply Hlxy1 in Hw'. apply membership_append. apply Hw'.
                               right. apply membership_rev. rewrite <- Hcy. apply membership_append_r. apply Hw.

                         - split.
                           + (* [lxy1, y]: h's desc path acyclic. lcyd1: HDh: h doesn't not overlap with any desc path. [cy, lcyv1]: lhv acyclic *)
                             intros Hmem. rewrite app_assoc in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                             * destruct Hh' as [_ [Hh' _]]. unfold acyclic_path_2 in Hh'. apply Hlxy1y in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                               -- destruct Hh' as [_ [Hh' _]]. apply Hh'. apply Hmem.
                               -- destruct Hh' as [Hh' _]. apply Hh'. destruct Hmem as [Hmem | Hmem]. symmetry. apply Hmem. exfalso. apply Hmem.
                             * assert (F: ~In h (rev lcyd1 ++ [cy] ++ lcyv2)). { apply Hcyccy with (dy := dy) (py := py) (lcyv1 := lcyv1) (lcyd2 := lcyd2) (y := y). apply Hpdy''. apply Hcy. apply Hy'. }
                               apply F. apply Hmem.

                           + (* Hx *) intros Hmem. apply no_overlap_non_member with (x := v) in Hx''. apply Hx''. apply membership_append.
                             rewrite Hph. apply membership_append. apply Hmem.
                             left. reflexivity.
                         - (* lxy1, y: Hh' ph path acyclic. lcyd1: Hoverph1. [cy, lcyv2]: Hx'' *)
                           apply no_overlap_non_member. intros w Hw Hw'. rewrite app_assoc in Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                           + destruct Hh' as [_ [Hh' _]]. apply acyclic_path_correct_2 in Hh'.
                             assert (Hc: count w (h :: ph ++ [zh]) = 0 \/ count w (h :: ph ++ [zh]) = 1). { apply acyclic_path_intermediate_nodes. apply Hh'. }
                             assert (Hc': count w (h :: ph ++ [zh]) > 1).
                             { rewrite Hph. destruct Hy' as [Hy' _]. rewrite <- app_assoc. rewrite <- app_assoc. unfold node in *. rewrite <- Hph2'. rewrite Hy'.
                               simpl. rewrite count_app. apply member_count_at_least_1 in Hw'. simpl. rewrite <- append_vs_concat. rewrite count_app.
                               apply member_count_at_least_1 in Hw. destruct (h =? w). destruct (x =? w). lia. lia. destruct (x =? w). lia. lia. }
                             lia.
                           + apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                             * apply no_overlap_non_member with (x := w) in Hoverph1. apply Hoverph1. apply Hw'.
                               apply collider_descendants_from_assignments_mem with (D := Dx) (p' := (x, v, rev tlx1)) (p := py) (d := dy) (c := cy) (G := G).
                               apply Hpdy. split. apply Hpdy. apply Hpdy. apply HLx. destruct Hy' as [_ [Hy' _]]. rewrite Hy'. apply membership_append. apply membership_rev. apply Hw.
                             * apply no_overlap_non_member with (x := w) in Hx''. apply Hx''. apply membership_append. rewrite Hph. apply membership_append. apply Hw'.
                               right. apply membership_rev. rewrite <- Hcy. apply membership_append_r. apply Hw. }

                       split.
                       { apply acyclic_path_cat_2.
                         { apply Hcychv. }

                         (* u not in [ph1,x, lxy1] b/c cycle. u not in [y,lcyd1] b/c HuL. u not in [cy, lcyv2] b/c Hulhv *)
                         { intros Hmem. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. rewrite Hmem in Hhu. rewrite eqb_refl in Hhu. discriminate Hhu.
                           rewrite app_comm_cons in Hmem. rewrite app_assoc in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                           - apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                             + apply member_In_equiv_F in Huph. apply Huph. rewrite Hph. apply membership_append. rewrite <- append_vs_concat in Hmem. apply membership_append_or in Hmem.
                               destruct Hmem as [Hmem | Hmem]. rewrite app_assoc. apply membership_append. apply Hmem.
                               rewrite <- Hph. apply Hlxy1. apply Hmem.
                             + rewrite app_comm_cons in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                               * apply member_In_equiv_F in HuL. apply HuL. apply HLcy with (cy := cy) (dy := dy) (py := py) (y' := y'). apply Hpdy.
                                 destruct Hy' as [_ [Hy' _]]. rewrite Hy'. rewrite app_assoc. apply membership_append. apply membership_rev. rewrite reverse_list_append. simpl. apply Hmem.
                               * apply member_In_equiv_F in Hulhv. apply Hulhv. rewrite Hlhvrev. apply membership_append_r. right. simpl. rewrite <- Hcy. apply membership_append_r. apply Hmem.
                           - destruct Hmem as [Hmem | Hmem]. destruct Hcyc as [Hcyc _]. apply Hcyc. symmetry. apply Hmem. apply Hmem. } }

                       assert (Hphv: is_path_in_graph (concat h x v ph1 (lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2)) G = true).
                       { apply concat_paths_still_a_path. split.
                         - apply directed_path_is_path. apply Hpathcy' with (dy := zh) (py := ph) (l2 := ph2). apply Hh'. apply Hx.
                         - apply concat_paths_still_a_path. split.
                           + apply subpath_still_path with (w := h) (l1 := ph1) (l3 := ph1 ++ [x] ++ lxy1). split. reflexivity.
                             apply directed_path_is_path. apply Hpathcy' with (dy := zh) (py := ph) (l2 := lxy2). apply Hh'. rewrite <- app_assoc. rewrite <- app_assoc. rewrite Hx. destruct Hy' as [Hy' _]. rewrite Hy'. reflexivity.
                           + apply concat_paths_still_a_path. split.
                             * apply reverse_path_in_graph. apply directed_path_is_path. apply Hpathcy' with (dy := dy) (py := py) (l2 := lcyd2). apply Hpdy''. apply Hy'.
                             * apply subpath_still_path with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite Hlhvrev. rewrite <- Hcy. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hlhv. }

                       split.
                       { (* (u, h, ph1, x) all mediators. x is mediator (not in z, Hh'). [lxy1] mediators
                            y collider, either = zh = dy and in Z, or not in Z but has path to dy
                            [lcyd1 mediators, not in Z. cy mediator, not in Z. lcyv2 from lhv d-conn *) 
                         apply d_connected_cat. apply HG.
                         - apply concat_d_connected_paths. apply HG. apply Hphv. split.
                           + apply Hconncy with (p := ph) (l2 := ph2) (d := zh). apply Hx. split. apply Hh'. apply Hh'.
                           + split. apply concat_d_connected_paths. apply HG. unfold concat. apply subpath_still_path with (w := h) (l1 := ph1) (l3 := ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).
                             split. reflexivity. apply Hphv. split.
                             * apply subpath_still_d_connected_gen with (w := h) (l1 := ph1) (l3 := ph1 ++ [x] ++ lxy1). split. reflexivity.
                               apply Hconncy with (p := ph) (l2 := lxy2) (d := zh). rewrite <- app_assoc. rewrite <- app_assoc. rewrite Hx. destruct Hy' as [Hy' _]. rewrite Hy'. reflexivity.
                               split. apply Hh'. apply Hh'.
                             * split. apply concat_d_connected_paths. apply HG. apply subpath_still_path with (w := h) (l1 := ph1 ++ [x] ++ lxy1) (l3 := ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2).
                               rewrite <- app_assoc. rewrite <- app_assoc. split. reflexivity. apply Hphv. split.
                               -- apply reverse_d_connected_paths. apply Hconncy with (p := py) (l2 := lcyd2) (d := dy). apply Hy'. split. apply Hpdy''.
                                  apply overlap_cat with (x := cy). apply Hpdy''.
                               -- split. apply subpath_still_d_connected_gen with (w := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (l3 := lhv). split. rewrite Hlhvrev. rewrite <- Hcy. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hlhv.
                                  apply subpath_still_acyclic with (w := h) (l1 := ph1 ++ [x] ++ lxy1) (l3 := ph1 ++ [x] ++ lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2). split.
                                  rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. apply Hcychv.
                               -- left. apply and_comm. split.
                                  ++ destruct Hpdy'' as [_ [_ [_ [Hpdy'' _]]]]. simpl in Hpdy''. destruct (member cy Z) as [|] eqn:HcyZ. discriminate Hpdy''. apply member_In_equiv_F. apply HcyZ.
                                  ++ apply collider_becomes_mediator_when_concat_directed with (x := x) (dy := dy) (txv := rev tlx1) (py := py) (lv1 := lcyv1) (ly2 := lcyd2).
                                     apply Hpdy. apply Hcy.
                                     apply subpath_still_acyclic with (w := h) (l1 := rev lx2) (l3 := lhv). split. simpl in Hcy. symmetry. apply Hlhvrev. apply Hlhv.
                                     apply Hy'. apply Hpdy''.
                               -- apply subpath_still_acyclic with (w := h) (l1 := ph1) (l3 := ph1 ++ [x]  ++lxy1 ++ [y] ++ rev lcyd1 ++ [cy] ++ lcyv2). split. reflexivity. apply Hcychv.
                             * right. right. rewrite and_comm. split.
                               ++ unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists dy. rewrite and_comm. split. apply Hpdy''.
                                  apply find_descendants_correct. destruct Hy' as [_ [Hy' _]]. symmetry in Hy'. destruct (rev lcyd2) as [| hlyd2 tlyd2] eqn:Hlyd2.
                                  -- apply Hl2 in Hy'. left. apply Hy'. apply Hlyd2.
                                  -- apply Hl2 in Hy'. right. exists (y, dy, rev tlyd2). split. apply subpath_still_directed with (w := cy) (l1 := lcyd1) (l3 := py). split. symmetry. apply Hy' with (hl2 := hlyd2) (tl2 := tlyd2). apply Hlyd2. apply Hpdy''.
                                     apply path_start_end_refl.
                               ++ apply subpath_preserves_colliders with (u := cy) (l1 := lxy1 ++ [y] ++ rev lcyd1) (l2 := lcyv2). split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. right.
                                  apply intersection_of_directed_paths_is_collider with (d1 := zh) (d2 := dy) (l1 := rev tph2) (l2 := py) (l1'' := lxy2) (l2'' := lcyd2).
                                  apply subpath_still_directed with (w := h) (l1 := ph1) (l3 := ph). split. symmetry. apply Hph. apply Hh'. apply Hpdy''.
                                  destruct Hy' as [Hy' _]. unfold nodes in *. unfold node in *. rewrite <- Hy'. symmetry. apply Hph2'. apply Hy'.
                             * apply Hcychv.
                           + left. apply and_comm. split.
                             * destruct Hh' as [_ [_ [Hh' _]]]. intros HxZ. apply no_overlap_non_member with (x := x) in Hh'. apply Hh'.
                               rewrite Hph. apply membership_append_r. left. reflexivity. apply HxZ.
                             * unfold concat. apply subpath_preserves_mediators with (u := y) (l1 := ph1 ++ x :: lxy1) (l2 := rev lcyd1 ++ [cy] ++ lcyv2). split. rewrite <- app_assoc. reflexivity.
                               right. apply directed_path_all_mediators. split.
                               -- apply Hpathcy' with (dy := zh) (py := ph) (l2 := lxy2). apply Hh'. rewrite Hx. destruct Hy' as [Hy' _]. rewrite Hy'. rewrite <- app_assoc. reflexivity.
                               -- apply membership_append_r. left. reflexivity.
                         - left. apply and_comm. split.
                            + apply HhZ.
                            + apply mediator_means_edge_out with (c := h) (G := G) in Hx.
                              destruct ph1 as [| hph11 tph11].
                              * apply mediators_vs_edges_in_path. exists u. exists x. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                                -- apply Huh.
                                -- destruct Hx as [Hx _]. apply Hx. reflexivity.
                              * apply mediators_vs_edges_in_path. exists u. exists hph11. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                                -- apply Huh.
                                -- destruct Hx as [_ Hx]. apply Hx with (tly1 := tph11). reflexivity.
                              * apply Hh'. }
                       split.
                       { simpl. rewrite Huh. simpl. destruct G as [V E]. apply Hphv. }
                       split.
                       { (* w = h: exists zh, ph, h not in Z. w in ph1: all not in Z, exists zh, ph. w = x: exists zh, ph, not in Z (Hh')
                            w in lxy1: exists zh, ph, not in Z. w = y: exists dy, lcdy2 (or =dy), path in. w in lcyd1: exists dy, lcdy2, path in
                            w = cy: exists dy, lcdy2, path in. w in lcyv2: use Hout *) admit. }
                       assert (HDy: exists (D: assignments (nodes * node)), get_collider_descendants_for_subpath Dh (find_colliders_in_path (cy, v, lcyv2) G) = Some D).
                       { apply collider_descendants_for_subpath_existence_2 with (u := h) (l1 := rev lx2 ++ [x] ++ lcyv1) (L := L).
                         unfold concat. admit. }
                       destruct HDy as [Dy HDy].
                       assert (HL: exists (L: nodes), get_collider_descendants_from_assignments Dy (find_colliders_in_path (cy, v, lcyv2) G) = Some L).
                       { apply collider_descendants_from_assignments_existence. admit. }
                       destruct HL as [Ly HLy].

                       (* TODO destruct if y = zh = dy or not. *) exists ((y, (lcyd2, dy)) :: Dy). admit.

                     * (* CASE 2C.3.iii: either b = true, so x is not a collider (Hbout) (and not in Z since lhv d-conn)
                          or (ph2 ++ [zh]) doesn't overlap Lx, so using ph2++[z] as x's desc path works *)

                       exists (h :: ph1 ++ [x] ++ rev tlx1).

                       assert (Hcyc': acyclic_path_2 (h, v, ph1 ++ [x] ++ rev tlx1)).
                       { apply concat_paths_acyclic. split. apply Hlhv. split. apply Hcychx.
                         - apply subpath_still_acyclic with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv.
                         - split.
                           + intros Hht. destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. apply Hlhv.
                             apply membership_rev. rewrite H1. apply membership_append. apply membership_rev. apply Hht.
                           + intros Hvph1. apply no_overlap_non_member with (x := v) in Hx''. apply Hx''. rewrite Hx. apply membership_append. apply Hvph1.
                             left. reflexivity.
                         - apply no_overlap_non_member. intros w Hw Hw'. apply no_overlap_non_member with (x := w) in Hx''. apply Hx''. rewrite Hx. apply membership_append. apply Hw'.
                           right. apply membership_rev. apply Hw. }

                       assert (Hpath'': is_path_in_graph (h, v, ph1 ++ [x] ++ rev tlx1) G = true).
                       { apply concat_paths_still_a_path. split.
                         - apply directed_path_is_path. simpl in Hdir. apply split_and_true in Hdir. apply Hdir.
                         - apply subpath_still_path with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv. }

                       split.
                       { apply acyclic_path_correct_2. simpl. rewrite Hhu.
                         apply split_and_true. split.
                         - rewrite <- app_assoc. simpl. rewrite <- append_vs_concat. apply negb_true_iff. apply member_In_equiv_F. intros Hu. apply membership_append_or in Hu.
                           destruct Hu as [Hu | Hu]. (* ph1 ++ [x] because cycle, rev tlx1 ++ [v] because Hulhv *)
                           + apply member_In_equiv_F in Huph. apply Huph. rewrite Hx. rewrite <- append_vs_concat. apply membership_append. apply Hu.
                           + apply membership_append_or in Hu. destruct Hu as [Hu | Hu].
                             * apply member_In_equiv_F in Hulhv. apply Hulhv. apply membership_rev. rewrite H1. apply membership_append. apply membership_rev. apply Hu.
                             * destruct Hcyc as [Hcyc _]. apply Hcyc. destruct Hu as [Hu | Hu]. symmetry. apply Hu. exfalso. apply Hu.
                         - apply acyclic_path_correct_2 in Hcyc'. simpl in Hcyc'. rewrite <- app_assoc in Hcyc'. simpl in Hcyc'. rewrite <- app_assoc. simpl. apply Hcyc'. }

                       split.
                       { apply d_connected_cat. apply HG. apply concat_d_connected_paths. apply HG. apply Hpath''. split.
                         - apply Hconncy with (p := ph) (d := zh) (l2 := ph2). apply Hx. split. apply Hh'. apply Hh'.
                         - split. apply subpath_still_d_connected_gen with (w := h) (l1 := rev lx2) (l3 := lhv). split. symmetry. apply Hlhvrev. apply Hlhv.
                           apply Hcyc'.
                         - destruct b as [|] eqn:Hb. (* HbLx: either x is not a collider (Houtx), so not in Z, or collider with ph2++[zh] desc path. *)
                           + left. apply and_comm. split.
                             * destruct Hlhv as [[Hcyclhv Hconnlhv] Hlhv]. apply intermediate_node_in_path with (x := x) in Hlhv. assert (Hxlhv: In x lhv). { rewrite Hlhvrev. apply membership_append_r. left. reflexivity. } apply Hlhv in Hxlhv.
                               destruct Hxlhv as [Hhh | [Hhh | Hhh]].
                               -- destruct Hconnlhv as [Hconnlhv _]. apply no_overlap_non_member with (x := x) in Hconnlhv. apply Hconnlhv. apply Hhh.
                               -- destruct Hconnlhv as [_ [Hconnlhv _]]. apply no_overlap_non_member with (x := x) in Hconnlhv. apply Hconnlhv. apply Hhh.
                               -- (* Hhh contradicts Hbout *) apply path_out_not_collider in Hbout. intros F. apply Hbout. apply Hhh. apply HG. apply Hcyclhv.
                             * apply mediator_end_means_edge_in with (c := h) (G := G) in Hx.
                               assert (Hbout': path_out_of_node x (x, v, rev tlx1) G = Some true).
                               { apply superpath_preserves_path_out_of_node with (w := h) (l1 := rev lx2) (l3 := lhv). symmetry. apply Hlhvrev.
                                 apply Hbout. apply Hlhv. left. reflexivity. }
                               destruct (rev ph1) as [| hph11 tph11] eqn:Hph1.
                               ++ assert (Hph1': ph1 = []). { rewrite reverse_list_twice with (l := ph1). rewrite Hph1. reflexivity. } rewrite Hph1' in *.
                                  apply mediators_vs_edges_in_path. exists h.
                                  destruct (rev tlx1) as [| hx1 tx1] eqn:Htlx1.
                                  ** exists v. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                                     -- apply Hx. reflexivity.
                                     -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, v) G) as [|] eqn:Hedge.
                                        apply edge_in_graph_then_is_edge. apply HG. apply Hedge. unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'.
                                  ** exists hx1. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                                     -- apply Hx. reflexivity.
                                     -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, hx1) G) as [|] eqn:Hedge.
                                        apply edge_in_graph_then_is_edge. apply HG. apply Hedge. unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'.
                               ++ assert (Hph1': ph1 = rev tph11 ++ [hph11]). { rewrite reverse_list_twice with (l := ph1). rewrite Hph1. reflexivity. } rewrite Hph1' in *.
                                  apply mediators_vs_edges_in_path. exists hph11.
                                  destruct (rev tlx1) as [| hx1 tx1] eqn:Htlx1.
                                  ** exists v. split. apply sublist_breaks_down_list. exists (h :: rev tph11). exists []. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. left. split.
                                     -- apply Hx with (hly1 := hph11) (tly1 := tph11). rewrite reverse_list_append. rewrite <- reverse_list_twice. reflexivity.
                                     -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, v) G) as [|] eqn:Hedge.
                                        apply edge_in_graph_then_is_edge. apply HG. apply Hedge. unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'.
                                  ** exists hx1. split. apply sublist_breaks_down_list. exists (h :: rev tph11). exists (tx1 ++ [v]). rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. left. split.
                                     -- apply Hx with (hly1 := hph11) (tly1 := tph11). rewrite reverse_list_append. rewrite <- reverse_list_twice. reflexivity.
                                     -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, hx1) G) as [|] eqn:Hedge.
                                        apply edge_in_graph_then_is_edge. apply HG. apply Hedge. unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'.
                               ++ apply Hh'.
                           + right. right. apply and_comm. split.
                             * apply overlap_has_member_in_common. exists zh. symmetry in Hx. apply Hl2 in Hx. destruct (rev ph2) as [| hph2 tph2] eqn:Hph2.
                               -- assert (Hxzh: x = zh /\ ph1 = ph). { apply Hx. apply Hph2. } destruct Hxzh as [Hxzh _]. split. rewrite Hxzh. unfold find_descendants. left. reflexivity.
                                  apply Hh'.
                               -- assert (Hxzh: zh = hph2 /\ ph = ph1 ++ [x] ++ rev tph2). { apply Hx. apply Hph2. } destruct Hxzh as [_ Hxzh]. split. apply find_descendants_correct.
                                  right. exists (x, zh, rev tph2). split. apply subpath_still_directed with (w := h) (l1 := ph1) (l3 := ph). split. symmetry. apply Hxzh. apply Hh'. apply path_start_end_refl. apply Hh'.
                             * apply mediator_end_means_edge_in with (c := h) (G := G) in Hx.
                               assert (Hbout': path_out_of_node x (x, v, rev tlx1) G = Some false).
                               { apply superpath_preserves_path_out_of_node with (w := h) (l1 := rev lx2) (l3 := lhv). symmetry. apply Hlhvrev.
                                 apply Hbout. apply Hlhv. left. reflexivity. }
                               destruct (rev ph1) as [| hph11 tph11] eqn:Hph1.
                               ++ assert (Hph1': ph1 = []). { rewrite reverse_list_twice with (l := ph1). rewrite Hph1. reflexivity. } rewrite Hph1' in *.
                                  apply colliders_vs_edges_in_path. exists h.
                                  destruct (rev tlx1) as [| hx1 tx1] eqn:Htlx1.
                                  ** exists v. split. simpl. repeat rewrite eqb_refl. reflexivity. split.
                                     -- apply Hx. reflexivity.
                                     -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, v) G) as [|] eqn:Hedge.
                                        unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'. simpl in Hpath''. destruct G as [V E]. apply split_and_true in Hpath''. destruct Hpath'' as [_ Hpath''].
                                        rewrite <- edge_in_graph_equiv in Hedge. rewrite Hedge in Hpath''. simpl in Hpath''. rewrite andb_comm in Hpath''. simpl in Hpath''. simpl. apply Hpath''. apply HG.
                                  ** exists hx1. split. simpl. repeat rewrite eqb_refl. reflexivity. split.
                                     -- apply Hx. reflexivity.
                                     -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, hx1) G) as [|] eqn:Hedge.
                                        unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'. simpl in Hpath''. destruct G as [V E]. apply split_and_true in Hpath''. destruct Hpath'' as [_ Hpath''].
                                        apply split_and_true in Hpath''. destruct Hpath'' as [Hpath'' _].
                                        rewrite <- edge_in_graph_equiv in Hedge. rewrite Hedge in Hpath''. simpl in Hpath''. simpl. apply Hpath''. apply HG.
                               ++ assert (Hph1': ph1 = rev tph11 ++ [hph11]). { rewrite reverse_list_twice with (l := ph1). rewrite Hph1. reflexivity. } rewrite Hph1' in *.
                                  apply colliders_vs_edges_in_path. exists hph11.
                                  destruct (rev tlx1) as [| hx1 tx1] eqn:Htlx1.
                                  ** exists v. split. apply sublist_breaks_down_list. exists (h :: rev tph11). exists []. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. split.
                                     -- apply Hx with (hly1 := hph11) (tly1 := tph11). rewrite reverse_list_append. rewrite <- reverse_list_twice. reflexivity.
                                     -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, v) G) as [|] eqn:Hedge.
                                        unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'.
                                        assert (Hpath''': is_path_in_graph (hph11, v, [x]) G = true). { apply subpath_still_path with (w := h) (l1 := rev tph11) (l3 := rev tph11 ++ [hph11] ++ [x]). split. reflexivity. rewrite <- app_assoc in Hpath''. apply Hpath''. }
                                        clear Hpath''. simpl in Hpath'''. destruct G as [V E]. apply split_and_true in Hpath'''. destruct Hpath''' as [_ Hpath''].
                                        rewrite <- edge_in_graph_equiv in Hedge. rewrite Hedge in Hpath''. simpl in Hpath''. rewrite andb_comm in Hpath''. simpl in Hpath''. simpl. apply Hpath''. apply HG.
                                  ** exists hx1. split. apply sublist_breaks_down_list. exists (h :: rev tph11). exists (tx1 ++ [v]). rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. split.
                                     -- apply Hx with (hly1 := hph11) (tly1 := tph11). rewrite reverse_list_append. rewrite <- reverse_list_twice. reflexivity.
                                     -- unfold path_out_of_node in Hbout'. simpl in Hbout'. rewrite eqb_refl in Hbout'. destruct (edge_in_graph (x, hx1) G) as [|] eqn:Hedge.
                                        unfold node in *. rewrite Hedge in Hbout'. discriminate Hbout'.
                                        assert (Hpath''': is_path_in_graph (hph11, v, [x] ++ hx1 :: tx1) G = true). { apply subpath_still_path with (w := h) (l1 := rev tph11) (l3 := rev tph11 ++ [hph11] ++ [x] ++ hx1 :: tx1). split. reflexivity. rewrite <- app_assoc in Hpath''. apply Hpath''. }
                                        clear Hpath''. simpl in Hpath'''. destruct G as [V E]. apply split_and_true in Hpath'''. destruct Hpath''' as [_ Hpath''].
                                        apply split_and_true in Hpath''. destruct Hpath'' as [Hpath'' _].
                                        rewrite <- edge_in_graph_equiv in Hedge. rewrite Hedge in Hpath''. simpl in Hpath''. simpl. apply Hpath''. apply HG.
                               ++ apply Hh'.
                         - left. apply and_comm. split.
                           + apply HhZ.
                           + apply mediator_means_edge_out with (c := h) (G := G) in Hx.
                             destruct ph1 as [| hph11 tph11].
                             * apply mediators_vs_edges_in_path. exists u. exists x. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                               -- apply Huh.
                               -- destruct Hx as [Hx _]. apply Hx. reflexivity.
                             * apply mediators_vs_edges_in_path. exists u. exists hph11. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                               -- apply Huh.
                               -- destruct Hx as [_ Hx]. apply Hx with (tly1 := tph11). reflexivity.
                             * apply Hh'. }

                       split.
                       { simpl. simpl in Hdir. apply split_and_true in Hdir. destruct Hdir as [Hdir _]. rewrite Hdir. simpl. destruct G as [V E]. apply Hpath''. } split.
                       { intros w Hw. (* [h, x): exists zh, ph, not in Z. x: did not change. tlx1: did not change *) admit. }

                       (* Dx for subpath of colliders after x (if x is not a collider). else, either x = zh, so Dx, or (tph2++zh) :: Dx *)
                       destruct b as [|] eqn:Hb.
                       -- (* x is not a collider *) exists Dx. admit.
                       -- simpl in HbLx. destruct ph2 as [| hph2 tph2] eqn:Hph2.
                          ++ (* x = zh *) exists ((x, ([], x)) :: Dx). admit.
                          ++ (* use desc path, since no overlap with Lx *) simpl in HbLx. exists ((x, (rev tph2, zh)) :: Dx). admit.

                 - destruct (overlap (ph ++ [zh]) L) as [|] eqn:HoverL.
                   + (* CASE 2C.4.i find the first point of overlap betw ph++[zh] and last collider that overlaps in L *)
                     apply overlap_rev_true in HoverL.
                     apply lists_have_first_elt_in_common in HoverL. destruct HoverL as [ph1 [ph2 [L1 [L2 [y' Hy]]]]].
                     assert (Hy': exists (c d: node) (p: nodes), In c (find_colliders_in_path (h, v, lhv) G)
                                 /\ get_assigned_value Dh c = Some (p, d) /\ d =? c = false
                                 /\ In y' (p ++ [d])).
                     { apply collider_descendants_from_assignments_belong_to_collider with (L := L). apply HLh. apply membership_rev.
                       destruct Hy as [_ [Hy _]]. rewrite Hy. apply membership_append_r. left. reflexivity. }
                     destruct Hy' as [cy [dy [py Hpdy]]].

                     assert (Hovery: overlap (ph ++ [zh]) (py ++ [dy]) = true). { apply overlap_has_member_in_common. exists y'. admit. }
                     apply lists_have_first_elt_in_common in Hovery. destruct Hovery as [lhy1 [lhy2 [lcy1 [lcy2 [y Hy']]]]].

                     assert (Hcy: In cy lhv).
                     { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := cy) in Hlhv. apply Hlhv. right. right. apply Hpdy. }
                     apply membership_splits_list in Hcy. destruct Hcy as [lhcy1 [lhcy2 Hcy]].
                     exists (h :: lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2).

                     destruct HDh as [HDh HDh']. destruct Hpdy as [Hcolcy Hpdy]. pose proof Hcolcy as Hcolcy'. apply HDh' in Hcolcy. clear HDh'.
                     pose proof Hpdy as Hpdy'. destruct Hpdy' as [Hpdy' _].
                     destruct Hcolcy as [Hcolcy | Hcolcy]. rewrite Hpdy' in Hcolcy. inversion Hcolcy. inversion H. rewrite H3 in Hpdy. destruct Hpdy as [_ [Hpdy _]]. rewrite eqb_refl in Hpdy. discriminate Hpdy.
                     destruct Hcolcy as [py' [dy' Hpdy'']]. destruct Hpdy'' as [Hpdy''' Hpdy'']. rewrite Hpdy' in Hpdy'''. inversion Hpdy'''. rewrite <- H0 in *. rewrite <- H1 in *. clear Hpdy'''. clear H0. clear H1.

                     assert (Hcychv: acyclic_path_2 (h, v, lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2)).
                     { apply concat_paths_acyclic. split. apply Hlhv. split.
                       - apply Hacyc with (dy := zh) (l2 := lhy2) (l3 := ph). split. symmetry. apply Hy'. apply Hh'.
                       - specialize Hcyccy' with (py := py) (dy := dy) (lhcy1 := lhcy1) (lcyd1 := lcy1) (cy := cy) (y := y) (lhcy2 := lhcy2) (lcyd2 := lcy2).
                         apply Hcyccy'. apply Hpdy''. apply Hcy. apply Hy'.
                       - split.
                         + specialize Hcyccy' with (py := py) (dy := dy) (lhcy1 := lhcy1) (lcyd1 := lcy1) (cy := cy) (y := y) (lhcy2 := lhcy2) (lcyd2 := lcy2).
                           apply Hcyccy'. apply Hpdy''. apply Hcy. apply Hy'.
                         + (* Hoverh: no overlap in ph++zh path and lhv path *)
                           intros Hmem. apply no_overlap_non_member with (x := v) in Hoverh. apply Hoverh. destruct Hy' as [Hy' _]. rewrite Hy'. apply membership_append. apply Hmem.
                           apply membership_append_r. left. reflexivity.
                       - (* lcy1: Hy'. [cy, lhcy2]: Hoverh *)
                         apply no_overlap_non_member. intros w Hw Hw'. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                         + destruct Hy' as [_ [_ Hy']]. apply no_overlap_non_member with (x := w) in Hy'. apply Hy'. apply Hw'. apply membership_rev. apply Hw.
                         + apply no_overlap_non_member with (x := w) in Hoverh. apply Hoverh. destruct Hy' as [Hy' _]. rewrite Hy'. apply membership_append. apply Hw'.
                          rewrite <- Hcy. apply membership_append. apply membership_append_r. apply Hw. }

                     split.
                     { apply acyclic_path_cat_2.
                       apply Hcychv.
                       { (* u not in [lhy1,y] b/c cycle. u not in [rev lcy1] b/c HuL. u not in [cy, lhcy2] b/c Hulhv *)
                         intros Hmem. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. rewrite Hmem in Hhu. rewrite eqb_refl in Hhu. discriminate Hhu.
                         rewrite app_comm_cons in Hmem. rewrite app_assoc in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                         - apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                           + rewrite <- append_vs_concat in Hmem. apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                             * apply member_In_equiv_F in Huph. apply Huph. destruct Hy' as [Hy' _]. rewrite Hy'.
                               rewrite app_assoc. apply membership_append. apply Hmem.
                             * apply member_In_equiv_F in HuL. apply HuL.
                               apply collider_descendants_from_assignments_mem with (D := Dh) (p' := (h, v, lhv)) (p := py) (d := dy) (c := cy) (G := G).
                               apply Hcolcy'. split. apply Hpdy'. apply Hpdy. apply HLh. destruct Hy' as [_ [Hy' _]]. rewrite Hy'. apply membership_append. apply membership_rev. apply Hmem.
                           + apply member_In_equiv_F in Hulhv. apply Hulhv. rewrite <- Hcy. apply membership_append_r. apply Hmem.
                         - destruct Hmem as [Hmem | Hmem]. destruct Hcyc as [Hcyc _]. apply Hcyc. symmetry. apply Hmem. apply Hmem. } }

                     assert (Hphv: is_path_in_graph (concat h y v lhy1 (rev lcy1 ++ [cy] ++ lhcy2)) G = true).
                     { apply concat_paths_still_a_path. split.
                       - apply directed_path_is_path. apply Hpathcy' with (dy := zh) (py := ph) (l2 := lhy2). apply Hh'. apply Hy'.
                       - apply concat_paths_still_a_path. split.
                         + apply reverse_path_in_graph. apply directed_path_is_path. apply Hpathcy' with (dy := dy) (py := py) (l2 := lcy2). apply Hpdy''. apply Hy'.
                         + apply subpath_still_path with (w := h) (l1 := lhcy1) (l3 := lhv). split. apply Hcy. apply Hlhv. }

                     split.
                     { apply d_connected_cat. apply HG. apply concat_d_connected_paths. apply HG.
                       apply Hphv. split.
                       - apply Hconncy with (p := ph) (l2 := lhy2) (d := zh). apply Hy'. split. apply Hh'. apply Hh'.
                       - split. apply concat_d_connected_paths. apply HG. apply subpath_still_path with (w := h) (l1 := lhy1) (l3 := lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2). split. reflexivity. apply Hphv. split.
                         + apply reverse_d_connected_paths. apply Hconncy with (p := py) (l2 := lcy2) (d := dy). apply Hy'. split. apply Hpdy''. apply overlap_cat with (x := cy). apply Hpdy''.
                         + split. apply subpath_still_d_connected_gen with (w := h) (l1 := lhcy1) (l3 := lhv). split. apply Hcy. apply Hlhv.
                           apply subpath_still_acyclic with (w := h) (l1 := lhy1) (l3 := lhy1 ++ [y] ++ rev lcy1 ++ [cy] ++ lhcy2). split. reflexivity. apply Hcychv.
                         + left. apply and_comm. split.
                           * destruct Hpdy'' as [_ [_ [_ [Hpdy'' _]]]]. simpl in Hpdy''. destruct (member cy Z) as [|] eqn:HcyZ. discriminate Hpdy''. apply member_In_equiv_F. apply HcyZ.
                           * apply collider_becomes_mediator_when_concat_directed with (x := h) (dy := dy) (txv := lhv) (py := py) (lv1 := lhcy1) (ly2 := lcy2).
                             apply Hcolcy'. apply Hcy. apply Hlhv. apply Hy'. apply Hpdy''.
                         + apply Hcychv.
                       - right. right. rewrite and_comm. split.
                         ++ unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists dy. rewrite and_comm. split. apply Hpdy''.
                            apply find_descendants_correct. destruct Hy' as [_ [Hy' _]]. symmetry in Hy'. destruct (rev lcy2) as [| hlyd2 tlyd2] eqn:Hlyd2.
                            -- apply Hl2 in Hy'. left. apply Hy'. apply Hlyd2.
                            -- apply Hl2 in Hy'. right. exists (y, dy, rev tlyd2). split. apply subpath_still_directed with (w := cy) (l1 := lcy1) (l3 := py). split. symmetry. apply Hy' with (hl2 := hlyd2) (tl2 := tlyd2). apply Hlyd2. apply Hpdy''.
                               apply path_start_end_refl.
                         ++ apply subpath_preserves_colliders with (u := cy) (l1 := lhy1 ++ [y] ++ rev lcy1) (l2 := lhcy2). split. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. right.
                            apply intersection_of_directed_paths_is_collider with (d1 := zh) (d2 := dy) (l1 := ph) (l2 := py) (l1'' := lhy2) (l2'' := lcy2).
                            apply Hh'. apply Hpdy''. apply Hy'. apply Hy'.
                       - left. apply and_comm. split.
                         + apply HhZ.
                         + destruct Hy' as [Hy' _]. apply mediator_means_edge_out with (c := h) (G := G) in Hy'.
                           destruct lhy1 as [| hph11 tph11].
                           * apply mediators_vs_edges_in_path. exists u. exists y. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                             -- apply Huh.
                             -- destruct Hy' as [Hx _]. apply Hx. reflexivity.
                           * apply mediators_vs_edges_in_path. exists u. exists hph11. split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                             -- apply Huh.
                             -- destruct Hy' as [_ Hx]. apply Hx with (tly1 := tph11). reflexivity.
                           * apply Hh'. }

                     split.
                     { simpl. rewrite Huh. simpl. destruct G as [V E]. apply Hphv. }
                     admit.

                   + (* CASE 2C.4.ii *) exists (h :: lhv).

                     split. repeat split.
                     { apply Hcyc. }
                     { intros Hmem. destruct Hmem as [Hmem | Hmem].
                       - unfold acyclic_path_2 in Hcyc. destruct Hcyc as [_ [Hcyc _]]. apply Hcyc. left. apply Hmem.
                       - apply member_In_equiv_F in Hulhv. apply Hulhv. apply Hmem. }
                     { unfold acyclic_path_2 in Hlhv. intros Hmem. destruct Hmem as [Hmem | Hmem].
                       - destruct Hlhv as [[[Hlhv _] _] _]. apply Hlhv. apply Hmem.
                       - destruct Hlhv as [[[_ [_ [Hlhv _]]] _] _]. apply Hlhv. apply Hmem. }
                     { destruct Hlhv as [[Hlhv _] _]. apply acyclic_path_correct_2 in Hlhv. apply acyclic_path_reverse in Hlhv.
                       simpl in Hlhv. rewrite reverse_list_append in Hlhv. simpl in Hlhv. apply split_and_true in Hlhv. destruct Hlhv as [_ Hlhv].
                       apply acyclic_path_reverse in Hlhv. rewrite reverse_list_append in Hlhv. rewrite <- reverse_list_twice in Hlhv. apply Hlhv. } split.
                     apply Hconn'. split. apply Hpath'. split.
                     { intros w H. destruct (w =? u) as [|] eqn:Hwu.
                       - (* contradicts H, since would be the same *) apply eqb_eq in Hwu. rewrite Hwu in H. destruct H as [H | H].
                         + destruct H as [_ H]. unfold node_in_path in H. simpl in H. rewrite eqb_refl in H. simpl in H. discriminate H.
                         + unfold path_out_of_node in H. simpl in H. rewrite eqb_refl in H. destruct (edge_in_graph (u, h) G) as [|].
                           * destruct H as [b Hb]. destruct Hb as [Hb1 Hb2]. rewrite Hb1 in Hb2. inversion Hb2. destruct b as [|]. discriminate H0. discriminate H0.
                           * destruct H as [b Hb]. destruct Hb as [Hb1 Hb2]. rewrite Hb1 in Hb2. inversion Hb2. destruct b as [|]. discriminate H0. discriminate H0.
                       - assert (Houtw: path_out_of_node w (u, v, h :: lhv) G = path_out_of_node w (h, v, lhv) G).
                         { apply path_out_of_node_cat. apply Hwu. }
                         assert (Houtw': path_out_of_node w (u, v, h :: t) G = path_out_of_node w (h, v, t) G).
                         { apply path_out_of_node_cat. apply Hwu. }
                         unfold nodes in *. rewrite Houtw in H. rewrite Houtw' in H.
                         assert (Hnode: node_in_path w (u, v, h :: lhv) = node_in_path w (h, v, lhv)).
                         { symmetry. apply node_in_path_cat. apply Hwu. }
                         assert (Hnode': node_in_path w (u, v, h :: t) = node_in_path w (h, v, t)).
                         { symmetry. apply node_in_path_cat. apply Hwu. }
                         rewrite Hnode in H. rewrite Hnode' in H. apply Hout in H. rewrite Houtw. apply H. } (* TODO generalize this *)

                     exists ((h, (ph, zh)) :: Dh). split. unfold nodes in *. rewrite Hcol. split.
                     { simpl. rewrite eqb_refl. simpl. apply is_assignment_for_cat. apply HDh. }
                     { intros w Hw. simpl in Hw. simpl. destruct (h =? w) as [|] eqn:Hhw. discriminate Hw. rewrite eqb_sym in Hhw. rewrite Hhw.
                       simpl. destruct HDh as [[_ HDh] _]. apply HDh. apply Hw. }
                     { intros c Hc. unfold nodes in *. rewrite Hcol in Hc.

                       assert (HpdL: forall (w: node) (c d: node) (p: nodes), 
                                     In c (find_colliders_in_path (h, v, lhv) G)
                                     -> In d Z
                                     -> overlap (c :: p) Z = false
                                     -> get_assigned_value Dh c = Some (p, d)
                                     -> In w (p ++ [d]) -> In w L).
                       { intros w c' d p Hccol HdZ HcZ Hc'.
                         apply collider_descendants_from_assignments_mem with (D := Dh) (p' := (h, v, lhv)) (p := p) (d := d) (c := c') (G := G).
                         apply Hccol. split. apply Hc'. destruct (d =? c') as [|] eqn:Hdc. apply eqb_eq in Hdc.
                         - exfalso. apply no_overlap_non_member with (x := d) in HcZ.
                           apply HcZ. left. symmetry. apply Hdc. apply HdZ.
                         - reflexivity.
                         - apply HLh. }

                       destruct Hc as [Hc | Hc].
                       + right. exists ph. exists zh. rewrite <- Hc in *. split.
                         * simpl. rewrite eqb_refl. reflexivity.
                         * rewrite <- and_assoc. rewrite <- and_assoc. split. repeat split; apply Hh'. repeat split.
                           -- simpl. apply member_In_equiv_F in HhZ. rewrite HhZ. apply Hh'.
                           -- apply overlap_flip. simpl. rewrite Huph. destruct Hh' as [_ [Hh' _]]. destruct (member h (ph ++ [zh])) as [|] eqn:Hmem.
                              ++ apply member_In_equiv in Hmem. apply membership_append_or in Hmem. exfalso. destruct Hmem as [Hmem | Hmem]. 
                                 destruct Hh' as [_ [Hh' _]]. apply Hh'. apply Hmem. destruct Hmem as [Hmem | Hmem]. destruct Hh' as [Hh' _]. apply Hh'. symmetry. apply Hmem. apply Hmem.
                              ++ apply overlap_flip. apply Hoverh.
                           -- intros c' d' p' Hc'. simpl in Hc'. destruct Hc' as [Hc' Hc'']. rewrite Hc' in Hc''. simpl. rewrite eqb_sym. rewrite Hc'.
                              assert (Hcolc': In c' (find_colliders_in_path (h, v, lhv) G)).
                              { apply assigned_true_then_in_list with (A := Dh). split. apply assigned_is_true. exists (p', d'). apply Hc''. apply HDh. }
                              destruct (member h (p' ++ [d'])) as [|] eqn:Hmem.
                              ++ destruct HDh as [_ HDh]. apply HDh in Hcolc'. destruct Hcolc' as [Hcolc' | Hcolc'].
                                 ** destruct Hcolc' as [Hcolc' _]. rewrite Hc'' in Hcolc'. inversion Hcolc'. rewrite H0 in Hmem. rewrite H1 in Hmem. simpl in Hmem. rewrite eqb_sym in Hc'.
                                    rewrite Hc' in Hmem. discriminate Hmem.
                                 ** destruct Hcolc' as [p'' [d'' Hcolc']]. destruct Hcolc' as [Hpd'' Hcolc']. rewrite Hc'' in Hpd''.
                                    inversion Hpd''. rewrite <- H0 in Hcolc'. rewrite <- H1 in Hcolc'. clear H0. clear H1. clear Hpd''.
                                    destruct Hcolc' as [_ [_ [_ [_ [Hcolc' _]]]]]. apply overlap_flip in Hcolc'. simpl in Hcolc'. rewrite Hmem in Hcolc'. discriminate Hcolc'.
                              ++ apply no_overlap_non_member. intros w Hw Hw'. destruct Hw as [Hw | Hw].
                                 ** apply no_overlap_non_member with (x := c') in Hoverh. apply Hoverh. rewrite Hw. apply Hw'. apply membership_append.
                                    destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := c') in Hlhv. apply Hlhv. right. right. apply Hcolc'.
                                 ** pose proof Hcolc' as Hcolc''. destruct HDh as [_ HDh]. apply HDh in Hcolc'. destruct Hcolc' as [Hcolc' | Hcolc'].
                                    --- destruct Hcolc' as [Hcolc' _]. rewrite Hc'' in Hcolc'. inversion Hcolc'. rewrite H0 in Hw. rewrite H1 in Hw. simpl in Hw. rewrite or_comm in Hw. destruct Hw as [Hw | Hw]. apply Hw.
                                        apply no_overlap_non_member with (x := c') in Hoverh. apply Hoverh. rewrite Hw. apply Hw'. apply membership_append.
                                        destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := c') in Hlhv. apply Hlhv. right. right. apply Hcolc''.
                                    --- apply no_overlap_non_member with (x := w) in HoverL. apply HoverL. apply Hw'.
                                        destruct Hcolc' as [p'' [d'' Hcolc']]. destruct Hcolc' as [Hpd'' Hcolc']. rewrite Hc'' in Hpd''.
                                        inversion Hpd''. rewrite <- H1 in Hcolc'. rewrite <- H2 in Hcolc'. clear H1. clear H2. clear Hpd''.
                                        apply HpdL with (c := c') (p := p') (d := d'). apply Hcolc''. apply Hcolc'. apply Hcolc'. apply Hc''.
                                        apply Hw.

                       + assert (HcDh: get_assigned_value ((h, (ph, zh)) :: Dh) c = get_assigned_value Dh c).
                         { simpl. destruct (h =? c) as [|] eqn:Hhc.
                           - apply eqb_eq in Hhc. rewrite <- Hhc in Hc.
                             assert (Hhmem: In h lhv).
                             { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := h) in Hlhv. apply Hlhv. right. right. apply Hc. }
                             destruct Hlhv as [[Hlhv _] _]. unfold acyclic_path_2 in Hlhv. destruct Hlhv as [_ [Hlhv _]]. exfalso. apply Hlhv. apply Hhmem.
                           - reflexivity. }
                         rewrite HcDh. pose proof Hc as Hcolc.
                         destruct HDh as [_ HDh]. apply HDh in Hc. destruct Hc as [Hc | Hc]. left. apply Hc. right.
                         destruct Hc as [p [d Hc]]. exists p. exists d. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc.
                         split. repeat split; apply Hc.

                         split.
                         apply overlap_flip. simpl. destruct (member u (p ++ [d])) as [|] eqn:Humem.
                         * apply member_In_equiv_F in HuL. exfalso. apply HuL. apply HpdL with (c := c) (p := p) (d := d). apply Hcolc. apply Hc. apply Hc. apply Hc. apply member_In_equiv. apply Humem.
                         * destruct Hc as [_ [_ [_ [_ [_ [Hc _]]]]]]. apply overlap_flip in Hc. apply Hc.
                         * intros c' d' p' Hc'. simpl in Hc'. destruct (h =? c') as [|] eqn:Hhc'.
                           -- destruct Hc' as [Hcc' Hc']. inversion Hc'. rewrite <- H1. rewrite <- H0. apply eqb_eq in Hhc'. rewrite <- Hhc'.
                              apply overlap_flip. simpl. rewrite <- Hhc' in Hcc'. rewrite Hcc'. destruct (member h (p ++ [d])) as [|] eqn:Hmem.
                              ++ destruct Hc as [_ [_ [_ [_ [_ [Hc _]]]]]]. apply no_overlap_non_member with (x := h) in Hc. exfalso. apply Hc. apply member_In_equiv. apply Hmem.
                                 left. reflexivity.
                              ++ apply no_overlap_non_member. intros w Hw Hw'. destruct Hw as [Hw | Hw].
                                 ** apply no_overlap_non_member with (x := w) in Hoverh. apply Hoverh. apply Hw'.
                                    assert (Hclhv: In c lhv).
                                    { destruct Hlhv as [_ Hlhv]. apply intermediate_node_in_path with (x := c) in Hlhv. apply Hlhv. right. right. apply Hcolc. }
                                    apply membership_splits_list in Hclhv. destruct Hclhv as [lhvc1 [lhvc2 Hclhv]].
                                    apply membership_append. rewrite <- Hclhv. apply membership_append_r. left. apply Hw.
                                 ** apply no_overlap_non_member with (x := w) in HoverL. apply HoverL. apply Hw'.
                                    apply HpdL with (c := c) (d := d) (p := p). apply Hcolc. apply Hc. apply Hc. apply Hc. apply Hw.
                           -- apply Hc. apply Hc'. } }
    + apply subpath_still_d_connected with (u := u). apply Hconn.
    + simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. apply Hpath.
Admitted.


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

Theorem acyclic_paths_intersect_if_common_endpoint: forall (anc1 anc2 z: node) (l1 l2: nodes) (Z: nodes) (G: graph),
  contains_cycle G = false
  -> is_directed_path_in_graph (anc1, z, l1) G = true /\ acyclic_path_2 (anc1, z, l1) /\ (forall w : node, w = anc1 \/ In w l1 -> ~ In w Z)
  -> is_directed_path_in_graph (anc2, z, l2) G = true /\ acyclic_path_2 (anc2, z, l2) /\ (forall w : node, w = anc2 \/ In w l2 -> ~ In w Z)
  -> overlap l1 l2 = false \/
     exists (l2': nodes), is_directed_path_in_graph (anc2, z, l2') G = true /\ acyclic_path_2 (anc2, z, l2')
      /\ (forall w : node, (w = anc2 \/ In w l2') -> ~ In w Z)
      /\ exists (l1'' l2'': nodes) (l3 l3': nodes) (x: node), l1 = l1'' ++ [x] ++ l3 /\ l2' = l2'' ++ [x] ++ l3 /\ l2 = l2'' ++ [x] ++ l3' /\ overlap l1'' l2'' = false.
Proof.
  intros anc1 anc2 z l1 l2 Z G. intros HG [Hdir1 [Hcyc1 HZ1]] [Hdir2 [Hcyc2 HZ2]].
  destruct (overlap l1 l2) as [|] eqn:Hover.
  - right.
    assert (H: exists (l1' l1'' l2' l2'': list nat) (x: nat), l1 = l1' ++ [x] ++ l1'' /\ l2 = l2' ++ [x] ++ l2'' /\ overlap l1' l2' = false).
    { apply lists_have_first_elt_in_common. apply Hover. }
    destruct H as [l1' [l1'' [l2' [l2'' [x [Hl1 [Hl2 Hover']]]]]]].
    exists (l2' ++ [x] ++ l1''). split.
    -- apply concat_directed_paths. split.
       ++ apply subpath_still_directed_2 with (v := z) (l2 := l2'') (l3 := l2). split. symmetry. apply Hl2. apply Hdir2.
       ++ apply subpath_still_directed with (w := anc1) (l1 := l1') (l3 := l1). split. symmetry. apply Hl1. apply Hdir1.
    -- split.
       ++ apply concat_paths_acyclic.
          ** split.
             --- unfold acyclic_path_2 in Hcyc2. destruct Hcyc2 as [Hcyc2 _]. apply Hcyc2.
             --- split.
                 +++ apply subpath_still_acyclic_2 with (v := z) (l2 := l2'') (l3 := l2). split. symmetry. apply Hl2. apply Hcyc2.
                 +++ apply subpath_still_acyclic with (w := anc1) (l1 := l1') (l3 := l1). split. symmetry. apply Hl1. apply Hcyc1.
          ** split.
             --- intros H. (* cycle anc2 -> ..l2'.. -> x -> ..l1''.. *) 
                 apply membership_splits_list in H. destruct H as [c1 [c2 Hc]].
                 assert (Hcyc: is_directed_path_in_graph (anc2, anc2, l2' ++ [x] ++ c1) G = true).
                 { apply concat_directed_paths. split.
                   - apply subpath_still_directed_2 with (v := z) (l2 := l2'') (l3 := l2). split. symmetry. apply Hl2. apply Hdir2.
                   - apply subpath_still_directed_2 with (v := z) (l2 := c2) (l3 := l1''). split. apply Hc.
                     apply subpath_still_directed with (w := anc1) (l1 := l1') (l3 := l1). split. symmetry. apply Hl1. apply Hdir1. }
                 apply contains_cycle_false_correct with (p := (anc2, anc2, l2' ++ [x] ++ c1)) in HG.
                 +++ unfold acyclic_path_2 in HG. destruct HG as [HG _]. apply HG. reflexivity.
                 +++ apply directed_path_is_path. apply Hcyc.
             --- intros H. unfold acyclic_path_2 in Hcyc2. destruct Hcyc2 as [_ [_ [Hcyc2 _]]]. apply Hcyc2. apply membership_append with (l2 := [x] ++ l2'') in H.
                 rewrite Hl2. apply H.
          ** destruct (overlap l2' l1'') as [|] eqn:F.
             apply overlap_has_member_in_common in F. destruct F as [x' [Hx2' Hx1']]. apply membership_splits_list in Hx2'. destruct Hx2' as [s1 [s2 Hs]].
             apply membership_splits_list in Hx1'. destruct Hx1' as [t1 [t2 Ht]].
             assert (Hcyc: is_directed_path_in_graph (x', x', s2 ++ [x] ++ t1) G = true).
             { apply concat_directed_paths. split.
               - apply subpath_still_directed with (w := anc2) (l1 := s1) (l3 := l2'). split. apply Hs.
                 apply subpath_still_directed_2 with (v := z) (l2 := l2'') (l3 := l2). split. symmetry. apply Hl2. apply Hdir2.
               - apply subpath_still_directed_2 with (v := z) (l2 := t2) (l3 := l1''). split. apply Ht.
                 apply subpath_still_directed with (w := anc1) (l1 := l1') (l3 := l1). split. symmetry. apply Hl1. apply Hdir1. }
             apply contains_cycle_false_correct with (p := (x', x', s2 ++ [x] ++ t1)) in HG.
             +++ unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
             +++ apply directed_path_is_path. apply Hcyc.
             +++ reflexivity.
       ++ split.
          ** intros w Hw. destruct Hw as [Hw | Hw].
             --- apply HZ2. left. apply Hw.
             --- apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                 +++ apply HZ2. right. apply membership_append with (l2 := [x] ++ l2'') in Hw. rewrite Hl2. apply Hw.
                 +++ apply HZ1. right. apply membership_append_r with (l1 := l1') in Hw. rewrite Hl1. apply Hw.
          ** exists l1'. exists l2'. exists l1''. exists l2''. exists x. repeat split.
             --- apply Hl1.
             --- apply Hl2.
             --- apply Hover'.
  - left. reflexivity.
Qed.

Lemma unblocked_ancestor_if_in_unblocked_directed_path: forall (anc u v: node) (l Z: nodes) (G: graph),
  is_directed_path_in_graph (anc, v, l) G = true /\ acyclic_path_2 (anc, v, l) /\ (forall w : node, w = anc \/ In w l -> ~ In w Z)
  -> In u l
  -> In u (find_unblocked_ancestors G v Z).
Proof.
  intros anc u v l Z G. intros [Hdir [Hcyc HlZ]]. intros Hu.
  apply unblocked_ancestors_have_unblocked_directed_path. right.
  - apply membership_splits_list in Hu. destruct Hu as [l1 [l2 Hl]].
    exists l2. split.
    + apply subpath_still_directed with (w := anc) (l1 := l1) (l3 := l). split. apply Hl. apply Hdir.
    + split.
      * apply subpath_still_acyclic with (w := anc) (l1 := l1) (l3 := l). split. apply Hl. apply Hcyc.
      * intros w Hw. apply HlZ. right. destruct Hw as [Hw | Hw].
        -- apply membership_splits_list. rewrite Hw. exists l1. exists l2. apply Hl.
        -- apply sublist_member with (l1 := l2). split. apply Hw. apply sublist_breaks_down_list. exists (l1 ++ [u]). exists [].
           rewrite append_identity. rewrite <- app_assoc. apply Hl.
Qed.

Lemma unblocked_ancestor_if_in_unblocked_directed_path_2: forall (anc u v: node) (l Z: nodes) (G: graph),
  is_directed_path_in_graph (anc, v, l) G = true /\ acyclic_path_2 (anc, v, l) /\ (forall w : node, w = anc \/ In w l -> ~ In w Z)
  -> In u l
  -> In anc (find_unblocked_ancestors G u Z).
Proof.
  intros anc u v l Z G. intros [Hdir [Hcyc HlZ]]. intros Hu.
  apply unblocked_ancestors_have_unblocked_directed_path. right.
  - apply membership_splits_list in Hu. destruct Hu as [l1 [l2 Hl]].
    exists l1. split.
    + apply subpath_still_directed_2 with (v := v) (l2 := l2) (l3 := l). split. apply Hl. apply Hdir.
    + split.
      * apply subpath_still_acyclic_2 with (v := v) (l2 := l2) (l3 := l). split. apply Hl. apply Hcyc.
      * intros w Hw. apply HlZ. destruct Hw as [Hw | Hw].
        -- left. apply Hw.
        -- right. apply membership_splits_list in Hw. destruct Hw as [l3 [l4 Hw]]. apply membership_splits_list. exists l3. exists (l4 ++ [u] ++ l2).
           rewrite app_assoc. rewrite app_assoc. rewrite app_assoc in Hw. rewrite Hw. apply Hl.
Qed.

Lemma unblocked_ancestors_transitive: forall (u ancu' ancu'': node) (G: graph) (Z: nodes),
  In ancu' (find_unblocked_ancestors G u Z)
  -> In ancu'' (find_unblocked_ancestors G ancu' Z)
  -> In ancu'' (find_unblocked_ancestors G u Z).
Proof.
  intros u ancu' ancu'' G Z Hu Hancu'. apply unblocked_ancestors_have_unblocked_directed_path in Hancu'.
  destruct Hancu' as [Hancu' | Hancu'].
  - rewrite Hancu'. apply Hu.
  - apply unblocked_ancestors_have_unblocked_directed_path in Hu. destruct Hu as [Hu | Hu].
    + rewrite <- Hu. apply unblocked_ancestors_have_unblocked_directed_path. right. apply Hancu'.
    + apply unblocked_ancestors_have_unblocked_directed_path. right. 
      destruct Hu as [l1 Hu]. destruct Hancu' as [l2 Hancu'].
      assert (Hdir: is_directed_path_in_graph (ancu'', u, l2 ++ [ancu'] ++ l1) G = true).
      { apply concat_directed_paths. split. apply Hancu'. apply Hu. }
      apply directed_path_can_be_acyclic in Hdir. destruct Hdir as [l Hl]. rewrite <- and_assoc in Hl. destruct Hl as [Hl Hsub].
      exists l. rewrite <- and_assoc. split. apply Hl.
      intros w [Hw | Hw].
      * destruct Hancu' as [_ [_ Hancu']]. apply Hancu'. left. apply Hw.
      * assert (Hmem: In w (l2 ++ [ancu'] ++ l1)).
        { apply subset_larger_set_membership with (l1 := l). split. apply Hsub. apply Hw. }
        apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
        ** destruct Hancu' as [_ [_ Hancu']]. apply Hancu'. right. apply Hmem.
        ** destruct Hu as [_ [_ Hu]]. apply Hu. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. left. symmetry. apply Hmem. right. apply Hmem.
Qed.


Lemma no_common_unblocked_ancestors_transitive: forall (u v ancu': node) (G: graph) (Z: nodes),
  overlap (find_unblocked_ancestors G u Z) (find_unblocked_ancestors G v Z) = false
  /\ In ancu' (find_unblocked_ancestors G u Z)
  -> overlap (find_unblocked_ancestors G ancu' Z) (find_unblocked_ancestors G v Z) = false.
Proof.
  intros u v ancu' G Z [Hover Hanc].
  apply unblocked_ancestors_have_unblocked_directed_path in Hanc. destruct Hanc as [Hanc | Hanc].
  { rewrite Hanc. apply Hover. }
  { destruct Hanc as [lu Hlu].
    destruct (overlap (find_unblocked_ancestors G ancu' Z) (find_unblocked_ancestors G v Z)) as [|] eqn:F.
    - apply overlap_has_member_in_common in F. destruct F as [x [Hxancu' Hxv]].
      apply no_overlap_non_member with (x := x) in Hover. apply unblocked_ancestors_transitive with (u := u) in Hxancu'.
      + exfalso. apply Hover. apply Hxancu'.
      + apply unblocked_ancestors_have_unblocked_directed_path. right. exists lu. apply Hlu.
      + apply Hxv.
    - reflexivity. }
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

(* find all unblocked ancestors of nodes in Z that are not properly conditioned in A' TODO added 2.16 *)
Fixpoint find_unblocked_ancestors_in_Z' {X: Type} `{EqType X} (G: graph) (Z: nodes) (AZ A': assignments X) (S: nodes): nodes :=
  match AZ with
  | [] => []
  | (u, x) :: AZ' => match (get_assigned_value A' u) with
                     | Some y => if (eqb x y) then find_unblocked_ancestors_in_Z' G Z AZ' A' S
                                              else if (overlap (find_unblocked_ancestors G u Z) S)
                                                   then (find_unblocked_ancestors G u Z) ++ (find_unblocked_ancestors_in_Z' G Z AZ' A' S)
                                                   else find_unblocked_ancestors_in_Z' G Z AZ' A' S
                     | None => find_unblocked_ancestors_in_Z' G Z AZ' A' S
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

(* TODO added 2.16 *)
Theorem unblocked_ancestor_of_node_in_Z' {X: Type} `{EqType X}: forall (G: graph) (Z S: nodes) (AZ Ab Ub: assignments X) (anc: node) (g: graphfun),
  In anc (find_unblocked_ancestors_in_Z' G Z AZ Ab S) /\ get_values G g Ub [] = Some Ab /\ each_node_assigned_once AZ
  -> exists (z: node), In anc (find_unblocked_ancestors G z Z) /\ overlap (find_unblocked_ancestors G z Z) S = true
     /\ is_assigned AZ z = true /\ find_value G g z Ub [] <> get_assigned_value AZ z.
Proof.
  intros G Z SS AZ Ab Ub anc g. intros [Hanc [HAb HAZ]].
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
      * apply IH in Hanc. destruct Hanc as [z [Hancz [Hover [Ht Hz]]]]. exists z. repeat split.
        -- apply Hancz.
        -- apply Hover.
        -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
        -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
           ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
           ++ apply Hz.
        -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
           destruct (z1 =? u) as [|] eqn:Huz1.
           ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
           ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity.
      * destruct (member z1 SS || overlap (find_unblocked_ancestors_given_paths (find_directed_paths_to_end z1 G) Z) SS) as [|] eqn:Hover.
        -- apply split_orb_true in Hover. destruct Hover as [Hover | Hover].
      { rewrite Hover in Hanc. apply membership_append_or with (l1 := z1 :: find_unblocked_ancestors_given_paths (find_directed_paths_to_end z1 G) Z) in Hanc.
        destruct Hanc as [Hanc | Hanc].
        { exists z1. repeat split.
        -- apply Hanc.
        -- apply overlap_has_member_in_common. exists z1. split.
           ++ unfold find_unblocked_ancestors. left. reflexivity.
           ++ apply member_In_equiv. apply Hover.
        -- simpl. rewrite eqb_refl. reflexivity.
        -- simpl. rewrite eqb_refl. unfold find_value. rewrite HAb. rewrite HAbz1. intros Hx1y'. inversion Hx1y'. rewrite H2 in Hx1y. rewrite eqb_refl' in Hx1y. discriminate Hx1y. }
        { apply IH in Hanc. destruct Hanc as [z [Hancz [Hover' [Ht Hz]]]]. exists z. repeat split.
        -- apply Hancz.
        -- apply Hover'.
        -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
        -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
           ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
           ++ apply Hz.
        -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
           destruct (z1 =? u) as [|] eqn:Huz1.
           ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
           ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity. } }
      { rewrite Hover in Hanc. destruct (member z1 SS) as [|] eqn:Hmem.
        { apply membership_append_or with (l1 := z1 :: find_unblocked_ancestors_given_paths (find_directed_paths_to_end z1 G) Z) in Hanc.
          destruct Hanc as [Hanc | Hanc].
          { exists z1. repeat split.
          -- apply Hanc.
          -- apply overlap_has_member_in_common. exists z1. split.
             ++ unfold find_unblocked_ancestors. left. reflexivity.
             ++ apply member_In_equiv. apply Hmem.
          -- simpl. rewrite eqb_refl. reflexivity.
          -- simpl. rewrite eqb_refl. unfold find_value. rewrite HAb. rewrite HAbz1. intros Hx1y'. inversion Hx1y'. rewrite H2 in Hx1y. rewrite eqb_refl' in Hx1y. discriminate Hx1y. }
          { apply IH in Hanc. destruct Hanc as [z [Hancz [Hover' [Ht Hz]]]]. exists z. repeat split.
          -- apply Hancz.
          -- apply Hover'.
          -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
          -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
             ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
             ++ apply Hz.
          -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
             destruct (z1 =? u) as [|] eqn:Huz1.
             ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
             ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity. } }
        { apply membership_append_or with (l1 := z1 :: find_unblocked_ancestors_given_paths (find_directed_paths_to_end z1 G) Z) in Hanc.
          destruct Hanc as [Hanc | Hanc].
          { exists z1. repeat split.
          -- apply Hanc.
          -- apply overlap_has_member_in_common in Hover. destruct Hover as [x [Hx1 Hx2]]. apply overlap_has_member_in_common. exists x. split.
             ++ unfold find_unblocked_ancestors. right. apply Hx1.
             ++ apply Hx2.
          -- simpl. rewrite eqb_refl. reflexivity.
          -- simpl. rewrite eqb_refl. unfold find_value. rewrite HAb. rewrite HAbz1. intros Hx1y'. inversion Hx1y'. rewrite H2 in Hx1y. rewrite eqb_refl' in Hx1y. discriminate Hx1y. }
          { apply IH in Hanc. destruct Hanc as [z [Hancz [Hover' [Ht Hz]]]]. exists z. repeat split.
          -- apply Hancz.
          -- apply Hover'.
          -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
          -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
             ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
             ++ apply Hz.
          -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
             destruct (z1 =? u) as [|] eqn:Huz1.
             ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
             ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity. } } }
        -- apply split_orb_false in Hover. destruct Hover as [Hover1 Hover2]. rewrite Hover1 in Hanc. rewrite Hover2 in Hanc.
           apply IH in Hanc. destruct Hanc as [z [Hancz [Hover [Ht Hz]]]]. exists z. repeat split.
           ++ apply Hancz.
           ++ apply Hover.
           ++ simpl. rewrite Ht. rewrite orb_comm. reflexivity.
           ++ simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
              ** specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
              ** apply Hz.
           ++ unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
              destruct (z1 =? u) as [|] eqn:Huz1.
              ** specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
              ** apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity.
     + apply IH in Hanc. destruct Hanc as [z [Hancz [Hover [Ht Hz]]]]. exists z. repeat split.
        -- apply Hancz.
        -- apply Hover.
        -- simpl. rewrite Ht. rewrite orb_comm. reflexivity.
        -- simpl. destruct (z1 =? z) as [|] eqn:Hz1z.
           ++ specialize H0 with (z := z). apply H0 in Hz1z. rewrite Hz1z in Ht. discriminate Ht.
           ++ apply Hz.
        -- unfold each_node_assigned_once. intros u Hu. unfold each_node_assigned_once in HAZ. specialize HAZ with (u := u). simpl in HAZ.
           destruct (z1 =? u) as [|] eqn:Huz1.
           ++ specialize H0 with (z := u). apply H0 in Huz1. rewrite Huz1 in Hu. discriminate Hu.
           ++ apply HAZ. rewrite Hu. rewrite orb_comm. reflexivity.
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
  forall (w: node), In w Z /\ node_in_graph w G = true -> find_value G g w U [] = get_assigned_value AZ w.

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

(* TODO added 2.16 *)
Fixpoint unblocked_ancestors_that_changed_A_to_B {X: Type} `{EqType X} (V: nodes) (Ua Ub: assignments X): nodes :=
  match V with
  | [] => []
  | h :: t => match (get_assigned_value Ua h) with
              | Some xa => match (get_assigned_value Ub h) with
                           | Some xb => if (eqb xa xb) then (unblocked_ancestors_that_changed_A_to_B t Ua Ub)
                                                       else h :: (unblocked_ancestors_that_changed_A_to_B t Ua Ub)
                           | None => (unblocked_ancestors_that_changed_A_to_B t Ua Ub)
                           end
              | None => (unblocked_ancestors_that_changed_A_to_B t Ua Ub)
              end
  end.

Lemma in_unblocked_that_changed {X: Type} `{EqType X}: forall (G: graph) (Ua Ub: assignments X) (x: node),
  In x (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub)
  -> get_assigned_value Ua x <> get_assigned_value Ub x.
Proof.
  intros G Ua Ub x Hmem.
  induction (nodes_in_graph G) as [| h t IH].
  - simpl in Hmem. exfalso. apply Hmem.
  - simpl in Hmem. destruct (get_assigned_value Ua h) as [xa|] eqn:Hxa.
    + destruct (get_assigned_value Ub h) as [xb|] eqn:Hxb.
      * destruct (eqb xa xb) as [|] eqn:Hxab.
        -- apply IH. apply Hmem.
        -- destruct Hmem as [Hmem | Hmem].
           ++ intros F. rewrite Hmem in *. rewrite Hxa in F. rewrite Hxb in F. inversion F. rewrite H1 in Hxab. rewrite eqb_refl' in Hxab. discriminate Hxab.
           ++ apply IH. apply Hmem.
      * apply IH. apply Hmem.
    + apply IH. apply Hmem.
Qed.

Definition conditionally_independent' (X: Type) `{EqType X} (G: graph) (u v: node) (Z: nodes): Prop :=
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
      (assignments_change_only_for_subset Ub Ub' (find_unblocked_ancestors_in_Z' G Z AZ Ab (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub)))
      /\ get_values G g Ub' [] = Some Ab' /\ (unobs_valid_given_u G Ub' Ab' u b) /\ (unobs_conditions_on_Z G g Ub' AZ Z)
  (* value of v must stay constant *)
  -> get_assigned_value Aa v = get_assigned_value Ab' v.

(* S := nodes that changed from subset Ua to Ub
        { w: Ua(w) neq Ub(w), Aa(w) neq Ab(w) } *)

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

Definition g_path' (X: Type) `{EqType X} (A1: assignments nat) (A2: assignments (nat * nat * X * X)) (A3: assignments nat) (A4: assignments X) (A5: assignments (nodefun X)) (def: nodefun X) (u: node): nodefun X :=
  match (get_assigned_value A1 u) with
  | Some i => f_parent_i X i (* mediators in the path, sometimes u and v depending on arrow directions *)
  | None => match (get_assigned_value A2 u) with
            | Some (i, j, x, y) => f_equate_ij X i j x y (* colliders, need to equate two parents in path *)
            | None => match (get_assigned_value A3 u) with
                      | Some i => f_parent_i X i (* descendants of colliders *)
                      | None => match (get_assigned_value A4 u) with
                                | Some c => f_constant X c (* confounders, sometimes u and v *)
                                | None => match (get_assigned_value A5 u) with
                                          | Some f => f
                                          | None => def
                                          end
                                end
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

Lemma A1_nodes_in_graph: forall (G: graph) (u v x: node) (l: nodes),
  G_well_formed G = true
  -> is_path_in_graph (u, v, l) G = true
  -> In x (get_A1_binded_nodes_in_g_path G (u, v, l))
  -> node_in_graph x G = true.
Proof.
  intros G u v x l. intros HG Hp Hx.
  unfold get_A1_binded_nodes_in_g_path in Hx.
  destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + destruct Hx as [Hx | Hx].
      * unfold path_into_start in Hin. destruct l as [| h t].
        -- apply is_edge_then_node_in_graph with (v := v). right. rewrite <- Hx. apply Hin.
        -- apply is_edge_then_node_in_graph with (v := h). right. rewrite <- Hx. apply Hin.
      * apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [[Hx _] | [Hx _]]]]].
        apply is_edge_then_node_in_graph with (v := y). right. apply Hx. apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
    + apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [[Hx _] | [Hx _ ]]]]].
      apply is_edge_then_node_in_graph with (v := y). right. apply Hx. apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + destruct Hx as [Hx | Hx].
      * unfold path_into_start in Hin. destruct l as [| h t].
        -- apply is_edge_then_node_in_graph with (v := v). right. rewrite <- Hx. apply Hin.
        -- apply is_edge_then_node_in_graph with (v := h). right. rewrite <- Hx. apply Hin.
      * apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [[Hx _] | [Hx _]]]]].
           apply is_edge_then_node_in_graph with (v := y). right. apply Hx. apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
        -- destruct Hx as [Hx | F].
           ++ apply nodes_in_graph_in_V with (p := (u, v, l)). split.
              ** unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
              ** apply Hp.
           ++ exfalso. apply F.
    + apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [[Hx _] | [Hx _]]]]].
           apply is_edge_then_node_in_graph with (v := y). right. apply Hx. apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
        -- destruct Hx as [Hx | F].
           ++ apply nodes_in_graph_in_V with (p := (u, v, l)). split.
              ** unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
              ** apply Hp.
           ++ exfalso. apply F.
  - exfalso. apply Hx.
Qed.

Lemma A1_nodes_in_path: forall (G: graph) (u v x: node) (l: nodes),
  In x (get_A1_binded_nodes_in_g_path G (u, v, l))
  -> node_in_path x (u, v, l) = true.
Proof.
  intros G u v x l. intros Hx.
  unfold get_A1_binded_nodes_in_g_path in Hx.
  destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + destruct Hx as [Hx | Hx].
      * unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. reflexivity.
      * apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
    + apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + destruct Hx as [Hx | Hx].
      * unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. reflexivity.
      * apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
        -- unfold node_in_path. destruct Hx as [Hx | F]. rewrite Hx. rewrite eqb_refl. simpl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
    + apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply mediators_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
        -- unfold node_in_path. destruct Hx as [Hx | F]. rewrite Hx. rewrite eqb_refl. simpl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
  - exfalso. apply Hx.
Qed.

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

Lemma A1_induction_into_start: forall (G: graph) (u h v: node) (t: nodes),
  is_path_in_graph (u, v, h :: t) G = true /\ contains_cycle G = false
  -> path_into_start (u, v, h :: t) G = true -> get_A1_binded_nodes_in_g_path G (u, v, h :: t) = u :: (get_A1_binded_nodes_in_g_path G (h, v, t)).
Proof.
  intros G u h v t [Hp Hcyc] Hin.
  unfold get_A1_binded_nodes_in_g_path.
  destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    destruct (path_into_start (h, v, t) G) as [|] eqn:Hinh.
    + simpl. destruct t as [| h' t']. simpl.
      * unfold is_mediator_bool. simpl in Hin. rewrite Hin. simpl in Hinh. rewrite Hinh. rewrite orb_comm. simpl. reflexivity.
      * simpl. unfold is_mediator_bool. simpl in Hinh. simpl in Hin. rewrite Hin. rewrite Hinh. rewrite orb_comm. simpl. reflexivity.
    + simpl. destruct t as [| h' t']. simpl.
      * unfold is_mediator_bool. simpl in Hinh. simpl in Hin. apply acyclic_no_two_cycle in Hin. rewrite Hin. simpl. rewrite Hinh. simpl. reflexivity. apply Hcyc.
      * simpl. unfold is_mediator_bool. simpl in Hinh. simpl in Hin. apply acyclic_no_two_cycle in Hin. rewrite Hin. simpl. rewrite Hinh. simpl. reflexivity. apply Hcyc.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    destruct (path_into_start (h, v, t) G) as [|] eqn:Hinh.
    + simpl. destruct t as [| h' t']. simpl.
      * unfold is_mediator_bool. simpl in Hin. simpl in Hinh. rewrite Hinh. rewrite Hin. rewrite orb_comm. simpl. reflexivity.
      * simpl. unfold is_mediator_bool. simpl in Hinh. simpl in Hin. rewrite Hinh. rewrite Hin. rewrite orb_comm. simpl. reflexivity.
    + simpl. destruct t as [| h' t']. simpl.
      * unfold is_mediator_bool. simpl in Hinh. simpl in Hin. apply acyclic_no_two_cycle in Hin. rewrite Hin. simpl. rewrite Hinh. simpl. reflexivity. apply Hcyc.
      * simpl. unfold is_mediator_bool. simpl in Hinh. simpl in Hin. apply acyclic_no_two_cycle in Hin. rewrite Hin. simpl. rewrite Hinh. simpl. reflexivity. apply Hcyc.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma A1_induction_out_of_start_out_of_h: forall (G: graph) (u h v: node) (t: nodes),
  is_path_in_graph (u, v, h :: t) G = true /\ contains_cycle G = false
  -> path_into_start (u, v, h :: t) G = false /\ path_out_of_h G u v h t = true -> get_A1_binded_nodes_in_g_path G (u, v, h :: t) = h :: (get_A1_binded_nodes_in_g_path G (h, v, t)).
Proof.
  intros G u h v t [Hp Hcyc] [Hin Houth].
  unfold get_A1_binded_nodes_in_g_path.
  destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction in Houth.
    + rewrite Houth. simpl. destruct t as [| h' t'].
      * unfold is_mediator_bool. simpl in Hout. simpl in Houth. inversion Hout. rewrite H0 in Houth. discriminate Houth.
      * assert (Hmed: is_mediator_bool u h' h G = true).
        { unfold is_mediator_bool. simpl in Hin. simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [Hp Hp'].
          rewrite Hin in Hp. rewrite orb_comm in Hp. simpl in Hp. simpl. rewrite Hp. simpl.
          apply split_and_true in Hp'. destruct Hp' as [Hp' _]. simpl in Houth. simpl in Hp'. rewrite Houth in Hp'. rewrite orb_comm in Hp'. simpl in Hp'. rewrite Hp'. reflexivity. }
        simpl. rewrite Hmed. reflexivity.
    + split.
      * simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. apply Hp.
      * apply Hcyc.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction in Houth.
    + rewrite Houth. destruct t as [| h' t'].
      * simpl. assert (Hmed: is_mediator_bool u v h G = true).
        { unfold is_mediator_bool. simpl in Hin. simpl in Houth. simpl in Hp. rewrite Hin in Hp. rewrite Houth in Hp. rewrite orb_comm in Hp. simpl in Hp. rewrite orb_comm in Hp. simpl in Hp.
          destruct G as [V E]. rewrite andb_assoc in Hp. apply split_and_true in Hp. apply Hp. }
        rewrite Hmed. reflexivity.
      * assert (Hmed: is_mediator_bool u h' h G = true).
        { unfold is_mediator_bool. simpl in Hin. simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [Hp Hp'].
          rewrite Hin in Hp. rewrite orb_comm in Hp. simpl in Hp. simpl. rewrite Hp. simpl.
          apply split_and_true in Hp'. destruct Hp' as [Hp' _]. simpl in Houth. simpl in Hp'. rewrite Houth in Hp'. rewrite orb_comm in Hp'. simpl in Hp'. rewrite Hp'. reflexivity. }
        simpl. rewrite Hmed. reflexivity.
    + split.
      * apply is_path_in_graph_induction with (u := u). apply Hp.
      * apply Hcyc.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma path_into_start_induction_rev: forall (u v h: node) (t: nodes) (G: graph),
  path_into_start (u, v, rev (h :: t)) G = path_into_start (u, h, rev t) G.
Proof.
  intros u v h t G. simpl.
  induction (rev t) as [| h' t' IH].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma A1_induction_case_rev: forall (G: graph) (u v h: node) (t: nodes),
  path_out_of_end (u, v, rev (h :: t)) G = Some false
  -> contains_cycle G = false
  -> is_path_in_graph (u, v, rev (h :: t)) G = true
  -> get_A1_binded_nodes_in_g_path G (u, h, rev t) ++ [v] = get_A1_binded_nodes_in_g_path G (u, v, rev (h :: t)).
Proof.
  intros G u v h t H Hcyc Hpath.
  unfold get_A1_binded_nodes_in_g_path. rewrite H. 
  destruct (path_out_of_end (u, h, rev t) G) as [[|]|] eqn:Houth.
  + assert (Hmed: find_mediators_in_path (u, h, rev t) G = find_mediators_in_path (u, v, rev (h :: t)) G).
    { simpl in H. simpl. simpl in Hpath. generalize dependent u. induction (rev t) as [| h' t' IH].
      - intros u H Hpath Houth. simpl. unfold is_mediator_bool. simpl in Houth. inversion Houth.
        assert (Huh: is_edge (u, h) G = false). { apply acyclic_no_two_cycle. apply Hcyc. apply H1. } rewrite Huh. simpl. simpl in H. inversion H. rewrite H2. reflexivity.
      - intros u H Hpath Houth. simpl. destruct t' as [| h'' t''].
        + simpl. destruct (is_mediator_bool u h h' G) as [|] eqn:Huhh'.
          * unfold is_mediator_bool. simpl in Houth. inversion Houth.
            assert (Huh: is_edge (h', h) G = false). { apply acyclic_no_two_cycle. apply Hcyc. apply H1. } rewrite Huh. simpl. rewrite H1. simpl.
            simpl in H. inversion H. rewrite H2. reflexivity.
          * simpl in H. unfold is_mediator_bool. unfold is_mediator_bool in Huhh'. simpl in Houth. inversion Houth.
            assert (Huh: is_edge (h', h) G = false). { apply acyclic_no_two_cycle. apply Hcyc. apply H1. } rewrite Huh. simpl. rewrite H1. simpl.
            inversion H. rewrite H2. simpl. reflexivity.
        + simpl. destruct (is_mediator_bool u h'' h' G) as [|] eqn:Huhh'.
          * f_equal. simpl in IH. simpl. f_equal. apply IH.
            -- simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. apply Houth.
          * simpl. f_equal. destruct (is_mediator_bool h'' u h' G) as [|].
            { simpl. f_equal. apply IH.
            -- simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. apply Houth. }
            { apply IH.
            -- simpl in H. simpl. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. simpl. apply Houth. } }
    rewrite Hmed. destruct (path_into_start (u, v, rev (h :: t)) G) as [|] eqn:Hin.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
  + assert (Hmed: find_mediators_in_path (u, h, rev t) G ++ [h] = find_mediators_in_path (u, v, rev (h :: t)) G).
    { simpl in H. simpl. simpl in Hpath. generalize dependent u. induction (rev t) as [| h' t' IH].
      - intros u H Hpath Houth. simpl. unfold is_mediator_bool. simpl in Hpath. destruct G as [V E]. simpl in Houth. inversion Houth.
        simpl in Hpath. rewrite H1 in Hpath. simpl in H. inversion H. rewrite H2 in Hpath. simpl. apply split_and_true in Hpath. destruct Hpath as [Huh Hhv].
        rewrite orb_comm in Huh. simpl in Huh. rewrite Huh. rewrite andb_comm in Hhv. rewrite orb_comm in Hhv. simpl in Hhv. rewrite Hhv. simpl. reflexivity.
      - intros u H Hpath Houth. simpl. destruct t' as [| h'' t''].
        + simpl. destruct (is_mediator_bool u h h' G) as [|] eqn:Huhh'.
          * unfold is_mediator_bool. simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [Hhh Hhv].
             simpl in Houth. inversion Houth. simpl in Hhh. rewrite H1 in Hhh. rewrite orb_comm in Hhh. simpl in Hhh. simpl. rewrite Hhh.
             simpl in H. inversion H. simpl in Hhv. rewrite H2 in Hhv. rewrite andb_comm in Hhv. rewrite orb_comm in Hhv. simpl in Hhv. rewrite Hhv. simpl. reflexivity.
          * simpl. unfold is_mediator_bool. simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [Hhh Hhv].
             simpl in Houth. inversion Houth. simpl in Hhh. rewrite H1 in Hhh. rewrite orb_comm in Hhh. simpl in Hhh. simpl. rewrite Hhh.
             simpl in H. inversion H. simpl in Hhv. rewrite H2 in Hhv. rewrite andb_comm in Hhv. rewrite orb_comm in Hhv. simpl in Hhv. rewrite Hhv. simpl. rewrite H1. simpl. reflexivity.
        + simpl. destruct (is_mediator_bool u h'' h' G || is_mediator_bool h'' u h' G) as [|] eqn:Huhh'.
          * simpl. f_equal. apply IH.
            -- simpl. simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. simpl. apply Houth.
          * simpl. apply IH.
            -- simpl. simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. simpl. apply Houth. }
    rewrite Hmed. destruct (path_into_start (u, v, rev (h :: t)) G) as [|] eqn:Hin.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
  + apply path_out_of_end_Some in Houth. exfalso. apply Houth.
Qed.

Definition A1_nodes_binded_to_parent_in_path (G: graph) (p: path) (A1: assignments nat): Prop :=
  forall (m: node) (i: nat), In (m, i) A1
  -> exists (a: node), nth_error (find_parents m G) i = Some a
     /\ (sublist [a; m] ((path_start p) :: (path_int p) ++ [path_end p]) = true \/ sublist [m; a] ((path_start p) :: (path_int p) ++ [path_end p]) = true).


Definition get_A2_binded_nodes_in_g_path (G: graph) (p: path): nodes :=
  find_colliders_in_path p G. (* TODO and descendants as necessary *)

Lemma A2_induction_case: forall (G: graph) (u h v: node) (t: nodes),
  contains_cycle G = false
  -> (path_into_start (u, v, h :: t) G = true \/ path_out_of_h G u v h t = true) -> get_A2_binded_nodes_in_g_path G (u, v, h :: t) = get_A2_binded_nodes_in_g_path G (h, v, t).
Proof.
  intros G u h v t Hcyc Hin.
  unfold get_A2_binded_nodes_in_g_path.
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

Lemma A2_nodes_not_in_A1: forall (G: graph) (u: node) (p: path),
  In u (get_A2_binded_nodes_in_g_path G p) -> ~(In u (get_A1_binded_nodes_in_g_path G p)).
Proof.
  (* when A2 includes descendants, not always true. *)
Admitted.

Definition A2_nodes_colliders_in_graph {X: Type} (G: graph) (p: path) (A2: assignments (nat * nat * X * X)): Prop :=
  forall (c: node) (i j: nat) (x y: X), In (c, (i, j, x, y)) A2
  -> exists (a b: node), nth_error (find_parents c G) i = Some a /\ nth_error (find_parents c G) j = Some b
     /\ sublist [a; c; b] ((path_start p) :: (path_int p) ++ [path_end p]) = true /\ is_collider_bool a b c G = true.

(* confounders, u if u is a parent, and v if v is a parent *)
Definition get_A3_binded_nodes_in_g_path (G: graph) (p: path): nodes :=
  match find_colliders_in_path p G with
  | [] => []
  | h :: t => [] (* TODO this should be a function that finds unblocked path to blocked ancestor *)
  end.

(* confounders, u if u is a parent, and v if v is a parent *)
Definition get_A4_binded_nodes_in_g_path (G: graph) (p: path): nodes :=
  match p with
  | (u, v, l) =>
    match path_out_of_end p G with
    | Some b => if b then (if path_into_start p G then (find_confounders_in_path p G) ++ [v] else u :: (find_confounders_in_path p G) ++ [v])
                     else (if path_into_start p G then (find_confounders_in_path p G) else u :: (find_confounders_in_path p G))
    | None => [] (* since p has at least two nodes, will not reach this *)
    end
  end.

Lemma A4_nodes_in_graph: forall (G: graph) (u v x: node) (l: nodes),
  G_well_formed G = true
  -> is_path_in_graph (u, v, l) G = true
  -> In x (get_A4_binded_nodes_in_g_path G (u, v, l))
  -> node_in_graph x G = true.
Proof.
  intros G u v x l. intros HG Hp Hx.
  unfold get_A4_binded_nodes_in_g_path in Hx.
  destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
      * apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [Hx _]]]].
        apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
      * destruct Hx as [Hx | F].
           ++ apply nodes_in_graph_in_V with (p := (u, v, l)). split.
              ** unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
              ** apply Hp.
           ++ exfalso. apply F.
    + destruct Hx as [Hx | Hx].
      * apply nodes_in_graph_in_V with (p := (u, v, l)). split.
              ** unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. reflexivity.
              ** apply Hp.
      * apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [Hx _]]]].
           apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
        -- destruct Hx as [Hx | F].
           ++ apply nodes_in_graph_in_V with (p := (u, v, l)). split.
              ** unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
              ** apply Hp.
           ++ exfalso. apply F.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [Hx _]]]].
        apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
    + destruct Hx as [Hx | Hx].
      * apply nodes_in_graph_in_V with (p := (u, v, l)). split.
              ** unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. reflexivity.
              ** apply Hp.
      * apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [_ [Hx _]]]].
        apply is_edge_then_node_in_graph with (v := y). left. apply Hx.
  - exfalso. apply Hx.
Qed.

Lemma A4_nodes_in_path: forall (G: graph) (u v x: node) (l: nodes),
  In x (get_A4_binded_nodes_in_g_path G (u, v, l))
  -> node_in_path x (u, v, l) = true.
Proof.
  intros G u v x l. intros Hx.
  unfold get_A4_binded_nodes_in_g_path in Hx.
  destruct (path_out_of_end (u, v, l) G) as [[|]|] eqn:Hout.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
        -- unfold node_in_path. destruct Hx as [Hx | F]. rewrite Hx. rewrite eqb_refl. simpl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
    + destruct Hx as [Hx | Hx].
      * unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. reflexivity.
      * apply membership_append_or in Hx. destruct Hx as [Hx | Hx].
        -- apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
        -- unfold node_in_path. destruct Hx as [Hx | F]. rewrite Hx. rewrite eqb_refl. simpl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
  - destruct (path_into_start (u, v, l) G) as [|] eqn:Hin.
    + apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
    + destruct Hx as [Hx | Hx].
      * unfold node_in_path. simpl. rewrite Hx. rewrite eqb_refl. reflexivity.
      * apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hx _]]].
        assert (In x (u :: l ++ [v])). { apply sublist_member with (l1 := [y; x; z]). split. right. left. reflexivity. apply Hx. }
        unfold node_in_path. simpl. destruct H as [H | H]. rewrite H. rewrite eqb_refl. reflexivity.
        apply membership_append_or in H. destruct H as [H | H]. apply member_In_equiv in H. rewrite H. rewrite orb_comm. reflexivity.
        destruct H as [H | F]. rewrite H. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
        exfalso. apply F.
  - exfalso. apply Hx.
Qed.


Lemma A4_induction_case: forall (G: graph) (u h v: node) (t: nodes),
  is_path_in_graph (u, v, h :: t) G = true /\ contains_cycle G = false
  -> path_into_start (u, v, h :: t) G = true -> get_A4_binded_nodes_in_g_path G (u, v, h :: t) = get_A4_binded_nodes_in_g_path G (h, v, t).
Proof.
  intros G u h v t [Hp Hcyc] Hin.
  unfold get_A4_binded_nodes_in_g_path.
  destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    destruct (path_into_start (h, v, t) G) as [|] eqn:Houth.
    + destruct t as [| h' t'].
      * simpl. simpl in Houth. unfold is_confounder_bool. apply acyclic_no_two_cycle in Houth.
        -- rewrite Houth. rewrite andb_comm. simpl. reflexivity.
        -- apply Hcyc.
      * simpl in Houth. simpl. unfold is_confounder_bool. apply acyclic_no_two_cycle in Houth.
        -- rewrite Houth. rewrite andb_comm. simpl. reflexivity.
        -- apply Hcyc.
    + destruct t as [| h' t'].
      * simpl in Houth. simpl in Hout. inversion Hout. rewrite H0 in Houth. discriminate Houth.
      * simpl in Hin. simpl in Houth. simpl. unfold is_confounder_bool. rewrite Hin.
        simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. apply split_and_true in Hp. destruct Hp as [Hp _].
        rewrite Houth in Hp. rewrite orb_comm in Hp. simpl in Hp. simpl. rewrite Hp. reflexivity.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    destruct (path_into_start (h, v, t) G) as [|] eqn:Houth.
    + destruct t as [| h' t'].
      * simpl. simpl in Houth. unfold is_confounder_bool. apply acyclic_no_two_cycle in Houth.
        -- rewrite Houth. rewrite andb_comm. simpl. reflexivity.
        -- apply Hcyc.
      * simpl in Houth. simpl. unfold is_confounder_bool. apply acyclic_no_two_cycle in Houth.
        -- rewrite Houth. rewrite andb_comm. simpl. reflexivity.
        -- apply Hcyc.
    + destruct t as [| h' t'].
      * simpl in Houth. simpl. unfold is_confounder_bool. simpl in Hin. rewrite Hin. simpl in Hp. destruct G as [V E].
        apply split_and_true in Hp. destruct Hp as [_ Hp]. rewrite Houth in Hp. rewrite andb_comm in Hp. rewrite orb_comm in Hp. simpl in Hp.
        simpl. rewrite Hp. reflexivity.
      * simpl in Hin. simpl in Houth. simpl. unfold is_confounder_bool. rewrite Hin.
        simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. apply split_and_true in Hp. destruct Hp as [Hp _].
        rewrite Houth in Hp. rewrite orb_comm in Hp. simpl in Hp. simpl. rewrite Hp. reflexivity.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma A4_induction_out_of_start_out_of_h: forall (G: graph) (u h v: node) (t: nodes),
  is_path_in_graph (u, v, h :: t) G = true /\ contains_cycle G = false
  -> path_into_start (u, v, h :: t) G = false /\ path_out_of_h G u v h t = true
  -> exists (A: nodes),
     get_A4_binded_nodes_in_g_path G (u, v, h :: t) = u :: A
     /\ get_A4_binded_nodes_in_g_path G (h, v, t) = h :: A.
Proof.
  intros G u h v t [Hp Hcyc] [Hin Houth].
  unfold get_A4_binded_nodes_in_g_path.
  destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction in Houth.
    + rewrite Houth. exists (find_confounders_in_path (u, v, h :: t) G ++ [v]). split. reflexivity. f_equal.
      unfold find_confounders_in_path. simpl. destruct t as [| h' t'].
      * simpl. unfold is_confounder_bool. simpl in Houth. simpl in Hout. inversion Hout. rewrite H0 in Houth. discriminate Houth.
      * simpl. assert (Hcon: is_confounder_bool u h' h G = false).
        { unfold is_confounder_bool. simpl in Houth. simpl in Hin. rewrite Hin. reflexivity. }
        rewrite Hcon. reflexivity.
    + split. apply is_path_in_graph_induction with (u := u). apply Hp. apply Hcyc.
  - rewrite Hin. rewrite <- path_out_of_end_same with (u := u). rewrite Hout.
    rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction in Houth.
    + rewrite Houth. exists (find_confounders_in_path (u, v, h :: t) G). split. reflexivity. f_equal.
      unfold find_confounders_in_path. simpl. destruct t as [| h' t'].
      * simpl. unfold is_confounder_bool. simpl in Houth. simpl in Hin. rewrite Hin. simpl. reflexivity.
      * simpl. assert (Hcon: is_confounder_bool u h' h G = false).
        { unfold is_confounder_bool. simpl in Houth. simpl in Hin. rewrite Hin. reflexivity. }
        rewrite Hcon. reflexivity.
    + split. apply is_path_in_graph_induction with (u := u). apply Hp. apply Hcyc.
  - apply path_out_of_end_Some in Hout. exfalso. apply Hout.
Qed.

Lemma A4_induction_case_rev: forall (G: graph) (u v h: node) (t: nodes),
  path_out_of_end (u, v, rev (h :: t)) G = Some false
  -> contains_cycle G = false
  -> is_path_in_graph (u, v, rev (h :: t)) G = true
  -> get_A4_binded_nodes_in_g_path G (u, h, rev t) = get_A4_binded_nodes_in_g_path G (u, v, rev (h :: t)).
Proof.
  intros G u v h t H Hcyc Hpath.
  unfold get_A4_binded_nodes_in_g_path. rewrite H.
  destruct (path_out_of_end (u, h, rev t) G) as [[|]|] eqn:Houth.
  + assert (Hcon: find_confounders_in_path (u, h, rev t) G ++ [h] = find_confounders_in_path (u, v, rev (h :: t)) G).
    { simpl in H. simpl. simpl in Hpath. generalize dependent u. induction (rev t) as [| h' t' IH].
      - intros u H Hpath Houth. simpl. unfold is_confounder_bool. simpl in Houth. inversion Houth. rewrite H1. simpl in H. inversion H.
        simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hhv]. rewrite H2 in Hhv.
        rewrite andb_comm in Hhv. rewrite orb_comm in Hhv. simpl in Hhv. simpl. rewrite Hhv. reflexivity.
      - intros u H Hpath Houth. simpl. destruct t' as [| h'' t''].
        + simpl. destruct (is_confounder_bool u h h' G) as [|] eqn:Huhh'.
          * unfold is_confounder_bool. simpl in Houth. inversion Houth. rewrite H1. simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [_ Hhv].
            simpl in H. inversion H. simpl in Hhv. rewrite H2 in Hhv. rewrite andb_comm in Hhv. rewrite orb_comm in Hhv. simpl in Hhv. simpl. rewrite Hhv. simpl. reflexivity.
          * simpl. unfold is_confounder_bool. simpl in Houth. inversion Houth. rewrite H1. simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply split_and_true in Hpath. destruct Hpath as [_ Hhv].
             simpl in H. inversion H. simpl in Hhv. rewrite H2 in Hhv. rewrite andb_comm in Hhv. rewrite orb_comm in Hhv. simpl in Hhv. simpl. rewrite Hhv. simpl. reflexivity.
        + simpl. destruct (is_confounder_bool u h'' h' G) as [|] eqn:Huhh'.
          * simpl. f_equal. apply IH.
            -- simpl. simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. simpl. apply Houth.
          * simpl. apply IH.
            -- simpl. simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. simpl. apply Houth. }
    rewrite Hcon. destruct (path_into_start (u, v, rev (h :: t)) G) as [|] eqn:Hin.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
  + assert (Hcon: find_confounders_in_path (u, h, rev t) G = find_confounders_in_path (u, v, rev (h :: t)) G).
    { simpl in H. simpl. simpl in Hpath. generalize dependent u. induction (rev t) as [| h' t' IH].
      - intros u H Hpath Houth. simpl. unfold is_confounder_bool. simpl in Houth. inversion Houth. rewrite H1. simpl. reflexivity.
      - intros u H Hpath Houth. simpl. destruct t' as [| h'' t''].
        + simpl. destruct (is_confounder_bool u h h' G) as [|] eqn:Huhh'.
          * unfold is_confounder_bool. simpl in Houth. inversion Houth. rewrite H1. simpl. reflexivity.
          * simpl in H. unfold is_confounder_bool. simpl in Houth. inversion Houth. rewrite H1. simpl. reflexivity.
        + simpl. destruct (is_confounder_bool u h'' h' G) as [|] eqn:Huhh'.
          * f_equal. simpl in IH. apply IH.
            -- simpl in H. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. apply Houth.
          * apply IH.
            -- simpl in H. simpl. apply H.
            -- simpl in Hpath. destruct G as [V E]. apply split_and_true in Hpath. destruct Hpath as [_ Hpath]. apply Hpath.
            -- simpl in Houth. simpl. apply Houth. }
    rewrite Hcon. destruct (path_into_start (u, v, rev (h :: t)) G) as [|] eqn:Hin.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
    - rewrite path_into_start_induction_rev in Hin. rewrite Hin. reflexivity.
  + apply path_out_of_end_Some in Houth. exfalso. apply Houth.
Qed.

Lemma A4_induction_case_rev_out: forall (G: graph) (u v h: node) (t: nodes),
  path_out_of_end (u, v, rev (h :: t)) G = Some true
  -> contains_cycle G = false
  -> is_path_in_graph (u, v, rev (h :: t)) G = true
  -> exists (l: nodes), l ++ [v] = get_A4_binded_nodes_in_g_path G (u, v, rev (h :: t)).
Proof.
  intros G u v h t H Hcyc Hpath.
  unfold get_A4_binded_nodes_in_g_path. rewrite H. destruct (path_into_start (u, v, rev (h :: t)) G) as [|].
  - exists (find_confounders_in_path (u, v, rev (h :: t)) G). reflexivity.
  - exists (u :: find_confounders_in_path (u, v, rev (h :: t)) G). reflexivity.
Qed.


Lemma A4_nodes_not_in_A1: forall (G: graph) (u: node) (p: path),
  In u (get_A4_binded_nodes_in_g_path G p) -> ~(In u (get_A1_binded_nodes_in_g_path G p)).
Proof.
Admitted.

Lemma A4_nodes_not_in_A2: forall (G: graph) (u: node) (p: path),
  In u (get_A4_binded_nodes_in_g_path G p) -> ~(In u (get_A2_binded_nodes_in_g_path G p)).
Proof.
Admitted.

Lemma A4_nodes_not_in_A3: forall (G: graph) (u: node) (p: path),
  In u (get_A4_binded_nodes_in_g_path G p) -> ~(In u (get_A3_binded_nodes_in_g_path G p)).
Proof.
Admitted.

Lemma sublist_of_path_has_edge: forall (a b h v: node) (t: nodes) (G: graph),
  sublist [b; a] (h :: t ++ [v]) = true
  -> is_path_in_graph (h, v, t) G = true
  -> is_edge (b, a) G = true \/ is_edge (a, b) G = true.
Proof.
  intros a b h v t G Hsub Hpath.
  generalize dependent h. induction t as [| h' t' IH].
  - intros h Hsub Hpath. simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [Hsub | F].
    + apply split_and_true in Hsub. destruct Hsub as [Hbh Hav].
      simpl in Hpath. destruct G as [V E]. apply eqb_eq in Hbh. rewrite Hbh. rewrite andb_comm in Hav. simpl in Hav. apply eqb_eq in Hav. rewrite Hav.
      rewrite andb_comm in Hpath. simpl in Hpath. apply split_orb_true in Hpath. apply Hpath.
    + rewrite orb_comm in F. simpl in F. rewrite andb_comm in F. simpl in F. discriminate F.
  - intros h Hsub Hpath. simpl in Hsub. apply split_orb_true in Hsub. destruct Hsub as [Hsub | Hsub].
    + apply split_and_true in Hsub. destruct Hsub as [Hbh Hav].
      simpl in Hpath. destruct G as [V E]. apply eqb_eq in Hbh. rewrite Hbh. rewrite andb_comm in Hav. simpl in Hav. apply eqb_eq in Hav. rewrite Hav.
      apply split_and_true in Hpath. destruct Hpath as [Hpath _ ]. apply split_orb_true in Hpath. apply Hpath.
    + apply IH with (h := h').
      * apply Hsub.
      * apply is_path_in_graph_induction with (u := h). apply Hpath.
Qed.

Lemma sublist_path_out_of_end: forall (x v h: node) (t: nodes) (G: graph),
  is_edge (v, x) G = true
  -> sublist [x; v] (h :: t ++ [v]) = true
  -> ~(In v (h :: t))
  -> path_out_of_end (h, v, t) G = Some true.
Proof.
  intros x v h t G. intros Hedge Hsub Hmem.
  unfold path_out_of_end.
  generalize dependent h. induction t as [| h' t' IH].
  - intros h Hsub Hmem. simpl in Hsub. simpl.
    rewrite orb_comm in Hsub. rewrite andb_comm in Hsub. simpl in Hsub. apply split_and_true in Hsub. destruct Hsub as [Hxh _].
    apply eqb_eq in Hxh. rewrite Hxh in Hedge. rewrite Hedge. reflexivity.
  - intros h Hsub Hmem. simpl in Hsub. rewrite andb_assoc in Hsub. destruct ((x =? h) && (v =? h')) as [|] eqn:H.
    + apply split_and_true in H. destruct H as [_ Hvh']. apply eqb_eq in Hvh'. exfalso. apply Hmem. right. left. rewrite Hvh'. reflexivity.
    + simpl in Hsub. simpl. specialize IH with (h := h').
      destruct t' as [| h'' t''].
      * simpl. simpl in Hsub. rewrite orb_comm in Hsub. rewrite andb_comm in Hsub. simpl in Hsub. apply split_and_true in Hsub. destruct Hsub as [Hsub _].
        apply eqb_eq in Hsub. rewrite <- Hsub. rewrite Hedge. reflexivity.
      * simpl. apply IH.
        -- apply Hsub.
        -- intros F. apply Hmem. right. apply F.
Qed.

Definition A3_nodes_not_assigned_elsewhere {X: Type} (A3: assignments nat) (G: graph) (p: path): Prop :=
  forall (u: node),
    (In u (get_A1_binded_nodes_in_g_path G p) -> is_assigned A3 u = false)
    /\ (In u (get_A2_binded_nodes_in_g_path G p) -> is_assigned A3 u = false)
    /\ (In u (get_A4_binded_nodes_in_g_path G p) -> is_assigned A3 u = false).

Fixpoint get_A3_nodes_for_path (c d: node) (p: nodes) (G: graph): option (assignments nat) :=
  match (c =? d) with
  | true => Some []
  | false => match p with
             | [] => match (index (find_parents d G) c) with
                     | Some i => Some [(d, i)]
                     | None => None
                     end
             | h :: t => match (index (find_parents h G) c) with
                         | Some i => match (get_A3_nodes_for_path h d t G) with
                                     | Some r => Some ((h, i) :: r)
                                     | None => None
                                     end
                         | None => None
                         end
             end
  end.

Fixpoint get_A3_assignments_for_desc_paths (D: assignments (nodes * node)) (G: graph): option (assignments nat) :=
  match D with
  | [] => Some []
  | (c, (p, d)) :: t => match (get_A3_nodes_for_path c d p G) with
                        | Some r => match (get_A3_assignments_for_desc_paths t G) with
                                    | Some t' => Some (r ++ t')
                                    | None => None
                                    end
                        | None => None
                        end
  end.


(* using g_path and specific values for A1, A2, A3, A4, A5, for a d-connected path betw u and v, provide a graphfun
   that requires all non-collider node values along the path (and importantly, f(v) and f(u)), to be equal *)
Lemma path_d_connected_then_can_equate_values' {X : Type} `{EqType X}: forall (G: graph) (u v: node) (p: path),
  generic_graph_and_type_properties_hold X G /\ In p (find_all_paths_from_start_to_end u v G) ->
  forall (Z: nodes), ~(In u Z) -> d_connected_2 p G Z
  -> forall (AZ: assignments X), is_assignment_for AZ Z = true
  -> exists (A1: assignments nat) (A2: assignments (nat * nat * X * X)) (A3: assignments nat),
     is_exact_assignment_for A1 (get_A1_binded_nodes_in_g_path G p) /\ A1_nodes_binded_to_parent_in_path G p A1
     /\ is_exact_assignment_for A2 (get_A2_binded_nodes_in_g_path G p) /\ A2_nodes_colliders_in_graph G p A2
     /\ is_exact_assignment_for A3 (get_A3_binded_nodes_in_g_path G p)
     /\ forall (A4: assignments X) (A5: assignments (nodefun X)) (default: nodefun X) (U: assignments X),
        is_exact_assignment_for A4 (get_A4_binded_nodes_in_g_path G p)
        -> is_assignment_for U (nodes_in_graph G) = true ->
           (* the colliders that are given a nodefun, but will still evaluate to conditioned value *)
           (forall (w: node), In w Z /\ is_assigned A2 w = true -> find_value G (g_path' X A1 A2 A3 A4 A5 default) w U [] = get_assigned_value AZ w)
           /\ (unobs_conditions_on_Z G (g_path' X A1 A2 A3 A4 A5 default) U AZ Z
              -> exists (x: X), forall (w: node), node_in_path w p = true /\ ~(In w (find_colliders_in_path p G))
                 -> find_value G (g_path' X A1 A2 A3 A4 A5 default) w U [] = Some x).
Proof.
  intros G u v p [HG Hp]. intros Z HuZ Hconn. intros AZ HAZ.
  assert (Hpath: exists (l: nodes), p = (u, v, l)).
  { destruct p as [[u' v'] l]. apply paths_start_to_end_correct in Hp. destruct Hp as [_ [Hp _]].
    apply path_start_end_equal in Hp. destruct Hp as [Huu' Hvv']. exists l. rewrite Huu'. rewrite Hvv'. reflexivity. }
  destruct Hpath as [l Hpath]. rewrite Hpath in *. clear Hpath.

  remember (u :: l ++ [v]) as n.
  assert (Hl: exists (l': nodes), l' = u :: l ++ [v] /\ sublist l' n = true).
  { exists n. split.
    - apply Heqn.
    - apply sublist_breaks_down_list. exists []. exists []. simpl. rewrite append_identity. reflexivity. }
  clear Heqn.
  generalize dependent u. generalize dependent l. induction n as [| hn tn IH].
  - intros l u Hp HuZ Hconn Hl. destruct Hl as [l' [Hl' Hsub]]. destruct l' as [| hl tl]. discriminate Hl'. simpl in Hsub. discriminate Hsub.
  - intros l u Hp HuZ Hconn Hl. destruct l as [| h t].

    (* base case: path consists of only u and v *)
    { destruct (path_out_of_start (u, v, []) G) as [|] eqn:Hout.
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
        exists [(v, i)]. exists []. exists []. repeat split.
        * simpl. simpl in Hin. rewrite Hin. simpl. rewrite eqb_refl. simpl. reflexivity.
        * intros w Hmem. simpl in Hmem. simpl in Hin. rewrite Hin in Hmem. simpl in Hmem.
          simpl. destruct (v =? w) as [|] eqn:Hvw.
          -- discriminate Hmem.
          -- rewrite eqb_sym. rewrite Hvw. reflexivity.
        * unfold A1_nodes_binded_to_parent_in_path. intros m i' Hmem. simpl in Hmem. destruct Hmem as [Hmem | F]. inversion Hmem. rewrite H1 in *. rewrite H2 in *. exists u. repeat split.
          -- apply index_correct. symmetry. apply Hi.
          -- left. simpl. repeat rewrite eqb_refl. reflexivity.
          -- exfalso. apply F.
        * unfold A2_nodes_colliders_in_graph. intros c i' j' x y F. exfalso. apply F.
        * intros w Hw. simpl in Hw. destruct Hw as [_ F]. discriminate F.
        * pose proof H1 as HU. clear H1. pose proof H0 as HA4. clear H0. intros Hcond. remember (g_path' X [(v, i)] [] [] A4 A5 default) as g.
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
                     + rewrite Heqg. unfold g_path'. simpl. rewrite eqb_refl. reflexivity. }
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
        exists [(u, i)]. exists []. exists []. repeat split.
        * simpl. simpl in Hin. rewrite Hin. simpl. rewrite eqb_refl. simpl. reflexivity.
        * intros w Hmem. simpl in Hmem. simpl in Hin. rewrite Hin in Hmem. simpl in Hmem.
          simpl. destruct (u =? w) as [|] eqn:Huw.
          -- discriminate Hmem.
          -- rewrite eqb_sym. rewrite Huw. reflexivity.
        * unfold A1_nodes_binded_to_parent_in_path. intros m i' Hmem. simpl in Hmem. destruct Hmem as [Hmem | F]. inversion Hmem. rewrite H1 in *. rewrite H2 in *. exists v. repeat split.
          -- apply index_correct. symmetry. apply Hi.
          -- right. simpl. repeat rewrite eqb_refl. reflexivity.
          -- exfalso. apply F.
        * unfold A2_nodes_colliders_in_graph. intros c i' j' x y F. exfalso. apply F.
        * intros w Hw. simpl in Hw. destruct Hw as [_ F]. discriminate F.
        * pose proof H1 as HU. clear H1. pose proof H0 as HA4. clear H0. intros Hcond. remember (g_path' X [(u, i)] [] [] A4 A5 default) as g.
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
                     + rewrite Heqg. unfold g_path'. simpl. rewrite eqb_refl. reflexivity. }
                 apply eqb_eq in Hwu. rewrite Hwu. rewrite Huv. apply Hgv.
             +++ apply eqb_eq in Hwv. rewrite Hwv. apply Hgv.
          -- simpl in F. discriminate F. }

    (* induction step: assume true for path (h, v, t). Show true for (u, v, h :: t) *)
    { destruct (path_out_of_h G u v h t) as [|] eqn:Houth.
      { (* out of h: u <-> h -> ... v *)
        specialize IH with (u := h) (l := t).
        assert (Hp': In (h, v, t) (find_all_paths_from_start_to_end h v G)).
        { apply paths_start_to_end_correct in Hp. apply paths_start_to_end_correct. split.
          - apply is_path_in_graph_induction with (u := u). apply Hp.
          - split. apply path_start_end_refl. apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity. apply Hp. }
        pose proof Hp' as Hpind. apply IH in Hp'. clear IH.
        + destruct Hp' as [A1' [A2' [A3' HA12]]]. destruct HA12 as [HA1' [HA1'' [HA2' [HA2'' [HA3' HA12]]]]].
          (* u <-> h -> ... <-> v *)
          assert (HA2ind: get_A2_binded_nodes_in_g_path G (u, v, h :: t) = get_A2_binded_nodes_in_g_path G (h, v, t)).
          { apply A2_induction_case.
            - destruct HG as [_ [_ HG]]. apply HG.
            - right. apply Houth. }
          assert (HindA2: is_exact_assignment_for A2' (get_A2_binded_nodes_in_g_path G (u, v, h :: t)) /\ A2_nodes_colliders_in_graph G (u, v, h :: t) A2').
          { repeat split.
            -- unfold nodes. rewrite HA2ind. unfold is_exact_assignment_for in HA2'. destruct HA2' as [HA2' _]. apply HA2'.
            -- (* since h is not a collider, nothing changes from induction case *)
               unfold nodes. rewrite HA2ind. unfold is_exact_assignment_for in HA2'. destruct HA2' as [_ HA2']. apply HA2'.
            -- unfold A2_nodes_colliders_in_graph. intros c i' j' x y Hc. unfold A2_nodes_colliders_in_graph in HA2''.
               specialize HA2'' with (c := c) (i := i') (j := j') (x := x) (y := y). apply HA2'' in Hc. destruct Hc as [a [b Hc]].
               exists a. exists b. repeat split.
               ++ apply Hc.
               ++ apply Hc.
               ++ destruct Hc as [_ [_ [Hc _]]]. apply sublist_breaks_down_list in Hc. simpl in Hc. destruct Hc as [l2 [l3 Hc]].
                  apply sublist_breaks_down_list. exists (u :: l2). exists l3. simpl. rewrite Hc. reflexivity.
               ++ apply Hc. }

          assert (Hi'': forall (g: graphfun) (iw: nat) (a w: node) (unobs' xa: X) (pa: list X) (P U: assignments X),
                        node_in_graph a G = true
                        -> is_assignment_for U (nodes_in_graph G) = true
                        -> nth_error (find_parents w G) iw = Some a
                        -> Some pa = get_parent_assignments P (find_parents w G) /\ find_values G g (find_parents w G) U [] = Some P
                        -> find_value G g a U [] = Some xa
                        -> nth_default unobs' pa iw = xa).
          { intros g i' a w' un xa Pa P1 U Hnodea HU Hi' Hpa Ha.
            assert (Hxa': get_assigned_value P1 a = Some xa).
             { apply find_values_get_assigned with (G := G) (g := g) (P := find_parents w' G) (U := U) (A := []). repeat split.
               - apply Hpa.
               - apply nth_error_In with (n := i'). apply Hi'.
               - apply Ha. }
             assert (Hiw: nth_error Pa i' = get_assigned_value P1 a).
             { rewrite Hxa'. apply parent_assignments_preserves_index with (P := P1) (V := find_parents w' G) (m := a). repeat split.
               - symmetry. apply Hpa.
               - symmetry. apply index_correct_appears_once.
                 + apply each_parent_appears_once. apply HG. apply nth_error_In with (n := i'). apply Hi'.
                 + apply Hi'.
               - apply Hxa'. }
             unfold nth_default. rewrite Hiw. rewrite Hxa'. reflexivity. }

          assert (Hi': forall (g g': graphfun) (iw: nat) (a w: node) (unobs': X) (pa pa': list X) (P P' U: assignments X),
                        node_in_graph a G = true
                        -> is_assignment_for U (nodes_in_graph G) = true
                        -> nth_error (find_parents w G) iw = Some a
                        -> Some pa = get_parent_assignments P (find_parents w G) /\ find_values G g (find_parents w G) U [] = Some P
                        -> Some pa' = get_parent_assignments P' (find_parents w G) /\ find_values G g' (find_parents w G) U [] = Some P'
                        -> find_value G g a U [] = find_value G g' a U []
                        -> nth_default unobs' pa iw = nth_default unobs' pa' iw).
           { intros g g' i' a w' un Pa Pa' P1 P1' U Hnodea HU Hi' Hpa Hpa' Ha.
             assert (Hxa: exists (xa: X), find_value G g a U [] = Some xa).
             { apply find_value_existence. apply HG. split. apply HU. apply Hnodea. }
             destruct Hxa as [xa Hxa].
             assert (Hxa': nth_default un Pa i' = xa). { apply Hi'' with (g := g) (a := a) (w := w') (P := P1) (U := U). easy. easy. easy. easy. easy. }
             rewrite Hxa'. clear Hxa'.

             assert (Hxa': exists (xa': X), find_value G g' a U [] = Some xa').
             { apply find_value_existence. apply HG. split. apply HU. apply Hnodea. }
             destruct Hxa' as [xa' Hxa'].
             assert (Hxa'': nth_default un Pa' i' = xa'). { apply Hi'' with (g := g') (a := a) (w := w') (P := P1') (U := U). easy. easy. easy. easy. easy.  }
             rewrite Hxa''. rewrite Hxa in Ha. rewrite Hxa' in Ha. inversion Ha. reflexivity. }

          assert (HhA4: In h (get_A4_binded_nodes_in_g_path G (h, v, t))).
          { unfold get_A4_binded_nodes_in_g_path. rewrite path_out_of_h_same in Houth. apply acyclic_path_one_direction in Houth.
            - destruct (path_out_of_end (h, v, t) G) as [[|]|] eqn:Hout.
              + unfold nodes in *. rewrite Houth. left. reflexivity.
              + unfold nodes in *. rewrite Houth. left. reflexivity.
              + apply path_out_of_end_Some in Hout. exfalso. apply Hout.
            - split.
              + apply paths_start_to_end_correct in Hp. apply is_path_in_graph_induction with (u := u). apply Hp.
              + apply HG. }

          assert (Hfv: forall (g g': graphfun) (U A4: assignments X) (a: node), In a (find_mediators_in_path (h, v, t) G) \/
                                                In a (find_confounders_in_path (h, v, t) G)
                              -> (forall (x: node), is_assigned A4 x = true -> find_value G g x U [] = find_value G g' x U []) (* HA4_const *)
                              -> is_assignment_for A4 (get_A4_binded_nodes_in_g_path G (u, v, h :: t)) = true
                              -> (forall (x: node), is_assigned A1' x = true -> find_value G g x U [] = find_value G g' x U []) (* HA1_const *)
                              -> find_value G g a U [] = find_value G g' a U []).
         { intros g g' U A4 a Hat HA4_const HA4 HA1_const. destruct Hat as [Hamed | Hacon].
           + assert (HaA1: In a (get_A1_binded_nodes_in_g_path G (h, v, t))).
             { unfold get_A1_binded_nodes_in_g_path. destruct (path_out_of_end (h, v, t) G) as [[|]|] eqn:Hout.
               - destruct (path_into_start (h, v, t) G) as [|]. right. apply Hamed. apply Hamed.
               - destruct (path_into_start (h, v, t) G) as [|]. right. apply membership_append. apply Hamed. apply membership_append. apply Hamed.
               - apply path_out_of_end_Some in Hout. exfalso. apply Hout. }
             apply HA1_const. apply assigned_is_true. apply assigned_has_value with (L := get_A1_binded_nodes_in_g_path G (h, v, t)). split.
             * apply HaA1.
             * unfold is_exact_assignment_for in HA1'. apply HA1'.
           + assert (HaA4: In a (get_A4_binded_nodes_in_g_path G (u, v, h :: t))).
             { unfold get_A4_binded_nodes_in_g_path. destruct (path_out_of_end (u, v, h :: t) G) as [[|]|] eqn:Hout.
               - destruct (path_into_start (u, v, h :: t) G) as [|].
                 + apply membership_append. apply add_node_preserves_confounders. apply Hacon.
                 + right. apply membership_append. apply add_node_preserves_confounders. apply Hacon.
               - destruct (path_into_start (u, v, h :: t) G) as [|]. apply add_node_preserves_confounders. apply Hacon. right. apply add_node_preserves_confounders. apply Hacon.
               - apply path_out_of_end_Some in Hout. exfalso. apply Hout. }
             apply HA4_const. apply assigned_is_true. apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (u, v, h :: t)). split.
             * apply HaA4.
             * apply HA4. }

          destruct (path_into_start (u, v, h :: t) G) as [|] eqn:Hin.
          * (* u <- h -> ... *)
            assert (Hi: exists i: nat, index (find_parents u G) h = Some i).
            { assert (Hh: In h (find_parents u G)).
              { apply edge_from_parent_to_child. simpl in Hin. destruct G as [V E]. simpl. simpl in Hin. apply split_and_true in Hin.
                destruct Hin as [_ Hin]. apply Hin. }
              apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
            destruct Hi as [i Hi].
            exists ((u, i) :: A1'). exists A2'. exists A3'.
            assert (HA1ind: get_A1_binded_nodes_in_g_path G (u, v, h :: t) = u :: get_A1_binded_nodes_in_g_path G (h, v, t)).
            { apply A1_induction_into_start.
              - split.
                ** apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
                ** destruct HG as [_ [_ HG]]. apply HG.
              - apply Hin. }
            assert (HA4ind: get_A4_binded_nodes_in_g_path G (u, v, h :: t) = get_A4_binded_nodes_in_g_path G (h, v, t)).
            { apply A4_induction_case.
              - split.
                ** apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
                ** destruct HG as [_ [_ HG]]. apply HG.
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
            -- unfold A1_nodes_binded_to_parent_in_path. intros c i' Hmi'. simpl in Hmi'. destruct Hmi' as [Hmi' | Hmi'].
               ++ inversion Hmi'. rewrite <- H1 in *. rewrite <- H2 in *. exists h. repeat split.
                  ** apply index_correct. symmetry. apply Hi.
                  ** right. simpl. repeat rewrite eqb_refl. reflexivity.
               ++ unfold A1_nodes_binded_to_parent_in_path in HA1''. specialize HA1'' with (m := c) (i := i'). apply HA1'' in Hmi'.
                  destruct Hmi' as [a [Ha Hsub]]. exists a. split.
                  ** apply Ha.
                  ** destruct Hsub as [Hsub | Hsub].
                     --- left. simpl. simpl in Hsub. rewrite Hsub. rewrite orb_comm. reflexivity.
                     --- right. simpl. simpl in Hsub. rewrite Hsub. rewrite orb_comm. reflexivity.
            -- apply HindA2.
            -- apply HindA2.
            -- apply HindA2.
            -- admit.
            -- admit.
            -- (* only change from induction is u, but since w is in A2', it is not in A1, so w != u *)
               specialize HA12 with (A4 := A4) (A5 := A5) (default := default) (U := U). pose proof H0 as HA4. pose proof H1 as HU. clear H0.
               apply HA12 in H1.
               { destruct H1 as [H1 _].
                 intros w Hw.
                 assert (Hnodew: node_in_graph w G = true).
                 { destruct Hw as [_ Hw].
                   assert (Hcolw: is_assigned A2' w = true /\ is_exact_assignment_for A2' (get_A2_binded_nodes_in_g_path G (h, v, t))). { split. apply Hw. apply HA2'. }
                   apply assigned_true_then_in_list in Hcolw. unfold get_A2_binded_nodes_in_g_path in Hcolw. apply colliders_vs_edges_in_path in Hcolw.
                   destruct Hcolw as [w1 [w2 Hcolw]]. destruct Hcolw as [_ [Hcolw _]]. unfold is_edge in Hcolw. destruct G as [V E]. apply split_and_true in Hcolw.
                   destruct Hcolw as [Hcolw _]. apply split_and_true in Hcolw. simpl. apply Hcolw. }
                 remember (g_path' X ((u, i) :: A1') A2' A3' A4 A5 default) as g.
                 assert (Hw': exists (P: assignments X), find_values G g (find_parents w G) U [] = Some P
                      /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                      /\ exists (unobs: X), get_assigned_value U w = Some unobs
                      /\ find_value G g w U [] = Some (g w (unobs, pa))).
                 { apply find_value_evaluates_to_g. split.
                   - destruct HG as [_ HG]. apply HG.
                   - split. apply HU. apply Hnodew. }
                 destruct Hw' as [P [HP [pa [Hpar [unobs [HwU Hw']]]]]].
                 rewrite Hw'. rewrite Heqg. unfold g_path'.
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
                 rewrite HA1w. specialize H1 with (w := w). apply H1 in Hw as HAZw. clear H1.
                 destruct Hw as [_ Hw]. apply assigned_is_true in Hw. destruct Hw as [[[[iw jw] xw] yw] Hvalw]. rewrite Hvalw.
                 rewrite <- HAZw. remember (g_path' X A1' A2' A3' A4 A5 default) as g'.
                 (* show that the induction case evaluates to the same thing *)
                 assert (Hw'': exists (P: assignments X), find_values G g' (find_parents w G) U [] = Some P
                      /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                      /\ exists (unobs: X), get_assigned_value U w = Some unobs
                      /\ find_value G g' w U [] = Some (g' w (unobs, pa))).
                 { apply find_value_evaluates_to_g. split.
                   - destruct HG as [_ HG]. apply HG.
                   - split. apply HU. apply Hnodew. }
                 destruct Hw'' as [P' [HP' [pa' [Hpar' [unobs' [HwU' Hw'']]]]]].
                 rewrite Hw''. rewrite Heqg'. unfold g_path'. simpl in HA1w. destruct (u =? w). discriminate HA1w.
                 rewrite HA1w. rewrite Hvalw.
                 unfold f_equate_ij. simpl.
                 rewrite HwU in HwU'. inversion HwU'. f_equal.

                 (* show that all nodes in A4 don't change value (since they have constant functions) *)
                 assert (HA4_const: forall (x: node), is_assigned A4 x = true -> find_value G g x U [] = find_value G g' x U []).
                 { intros x HxA4.
                   assert (Hx': exists (P: assignments X), find_values G g (find_parents x G) U [] = Some P
                        /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents x G)
                        /\ exists (unobs: X), get_assigned_value U x = Some unobs
                        /\ find_value G g x U [] = Some (g x (unobs, pa))).
                   { apply find_value_evaluates_to_g. split.
                     - destruct HG as [_ HG]. apply HG.
                     - split. apply HU. apply A4_nodes_in_graph with (u := u) (v := v) (l := h :: t). apply HG. apply paths_start_to_end_correct in Hp. apply Hp.
                       apply assigned_true_then_in_list with (A := A4). split. apply HxA4. apply HA4. }
                   destruct Hx' as [Px [HPx [pax [Hparx [unobsx [HxU Hx]]]]]]. rewrite Hx.
                   assert (Hx': exists (P: assignments X), find_values G g' (find_parents x G) U [] = Some P
                        /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents x G)
                        /\ exists (unobs: X), get_assigned_value U x = Some unobs
                        /\ find_value G g' x U [] = Some (g' x (unobs, pa))).
                   { apply find_value_evaluates_to_g. split.
                     - destruct HG as [_ HG]. apply HG.
                     - split. apply HU. apply A4_nodes_in_graph with (u := u) (v := v) (l := h :: t). apply HG. apply paths_start_to_end_correct in Hp. apply Hp.
                       apply assigned_true_then_in_list with (A := A4). split. apply HxA4. apply HA4. }
                   destruct Hx' as [Px' [HPx' [pax' [Hparx' [unobsx' [HxU' Hx']]]]]]. rewrite Hx'.
                   rewrite Heqg. rewrite Heqg'. unfold g_path'.

                   assert (HA4x: In x (get_A4_binded_nodes_in_g_path G (h, v, t))).
                   { apply assigned_true_then_in_list with (A := A4). split. apply HxA4. rewrite <- HA4ind. apply HA4. }
                   rewrite <- HA4ind in HA4x.
                   assert (HA1x: get_assigned_value ((u, i) :: A1') x = None).
                   { apply A4_nodes_not_in_A1 in HA4x. rewrite HA1ind in HA4x. destruct (u =? x) as [|] eqn:Hux.
                     - exfalso. apply HA4x. left. apply eqb_eq in Hux. apply Hux.
                     - destruct HA1' as [_ HA1']. apply assigned_is_false. specialize HA1' with (u := x). simpl. rewrite eqb_sym. rewrite Hux. simpl. apply HA1'.
                       destruct (member x (get_A1_binded_nodes_in_g_path G (h, v, t))) as [|] eqn:Hmem.
                       + exfalso. apply HA4x. right. apply member_In_equiv. apply Hmem.
                       + apply Hmem. }
                   rewrite HA1x. simpl in HA1x. destruct (u =? x) as [|]. discriminate HA1x. rewrite HA1x.
                   assert (HA2x: get_assigned_value A2' x = None).
                   { apply A4_nodes_not_in_A2 in HA4x. rewrite HA2ind in HA4x. destruct HA2' as [_ HA2']. apply assigned_is_false.
                     specialize HA2' with (u := x). apply HA2'.
                     destruct (member x (get_A2_binded_nodes_in_g_path G (h, v, t))) as [|] eqn:Hmem.
                     + exfalso. apply HA4x. apply member_In_equiv. apply Hmem.
                     + apply Hmem. }
                   rewrite HA2x.
                   assert (HA3x: get_assigned_value A3' x = None).
                   { apply A4_nodes_not_in_A3 in HA4x. apply assigned_is_false. unfold is_exact_assignment_for in HA3'. destruct HA3' as [_ HA3']. apply HA3'.
                     simpl in HA4x. apply member_In_equiv_F. admit. }
                   rewrite HA3x.
                   assert (HA4x': exists (xA4: X), get_assigned_value A4 x = Some xA4).
                   { apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (u, v, h :: t)). split. apply HA4x. apply HA4. }
                   destruct HA4x' as [xA4 HA4x']. rewrite HA4x'. unfold f_constant. reflexivity. }

                 (* show that all nodes in A1 don't change value (since they are tied to their parents, which becomes a chain that
                    must eventually end at a node in A4) *)
                 assert (HA1_const: forall (x: node), is_assigned A1' x = true -> find_value G g x U [] = find_value G g' x U []).
                 { intros x HxA1'.
                   assert (Hx': exists (P: assignments X), find_values G g (find_parents x G) U [] = Some P
                        /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents x G)
                        /\ exists (unobs: X), get_assigned_value U x = Some unobs
                        /\ find_value G g x U [] = Some (g x (unobs, pa))).
                   { apply find_value_evaluates_to_g. split.
                     - destruct HG as [_ HG]. apply HG.
                     - split. apply HU. apply A1_nodes_in_graph with (u := h) (v := v) (l := t). apply HG. apply paths_start_to_end_correct in Hp. apply is_path_in_graph_induction with (u := u). apply Hp.
                       apply assigned_true_then_in_list with (A := A1'). split. apply HxA1'. apply HA1'. }
                   destruct Hx' as [Px [HPx [pax [Hparx [unobsx [HxU Hx]]]]]]. rewrite Hx.
                   assert (Hx': exists (P: assignments X), find_values G g' (find_parents x G) U [] = Some P
                        /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents x G)
                        /\ exists (unobs: X), get_assigned_value U x = Some unobs
                        /\ find_value G g' x U [] = Some (g' x (unobs, pa))).
                   { apply find_value_evaluates_to_g. split.
                     - destruct HG as [_ HG]. apply HG.
                     - split. apply HU. apply A1_nodes_in_graph with (u := h) (v := v) (l := t). apply HG. apply paths_start_to_end_correct in Hp. apply is_path_in_graph_induction with (u := u). apply Hp.
                       apply assigned_true_then_in_list with (A := A1'). split. apply HxA1'. apply HA1'. }
                   destruct Hx' as [Px' [HPx' [pax' [Hparx' [unobsx' [HxU' Hx']]]]]]. rewrite Hx'.
                   rewrite Heqg. rewrite Heqg'. unfold g_path'.

                   assert (Hxu: u =? x = false).
                   { assert (Hpathx: node_in_path x (h, v, t) = true). { apply A1_nodes_in_path with (G := G). apply assigned_true_then_in_list with (A := A1').
                     split. apply HxA1'. apply HA1'. }
                     apply paths_start_to_end_correct in Hp. destruct Hp as [_ [_ Hp]].
                     destruct (u =? x) as [|] eqn:Hux.
                     - apply eqb_eq in Hux. unfold acyclic_path_2 in Hp. unfold node_in_path in Hpathx. simpl in Hpathx.
                       apply split_orb_true in Hpathx. destruct Hpathx as [Hxhv | Hxt].
                       + apply split_orb_true in Hxhv. destruct Hxhv as [Hxh | Hxv].
                         * destruct Hp as [_ [Hp _]]. exfalso. apply Hp. left. rewrite Hux. apply eqb_eq in Hxh. rewrite Hxh. reflexivity.
                         * destruct Hp as [Hp _]. exfalso. apply Hp. rewrite Hux. apply eqb_eq in Hxv. apply Hxv.
                       + destruct Hp as [_ [Hp _]]. exfalso. apply Hp. right. rewrite Hux. apply member_In_equiv. apply Hxt.
                     - reflexivity. }
                   simpl. rewrite Hxu.
                   apply assigned_is_true in HxA1'. destruct HxA1' as [ix HxA1']. rewrite HxA1'. unfold f_parent_i. simpl.
                   unfold A1_nodes_binded_to_parent_in_path in HA1''. pose proof HA1'' as HA1bind. specialize HA1'' with (m := x) (i := ix). apply get_assigned_In in HxA1'.
                   apply HA1'' in HxA1'. destruct HxA1' as [a [Haxix Haxsub]]. f_equal. rewrite HxU' in HxU. inversion HxU. apply Hi' with (g := g) (g' := g') (U := U) (a := a) (w := x) (P := Px) (P' := Px').
                   - apply parents_in_graph with (u := x). apply HG. apply nth_error_In in Haxix. apply Haxix.
                   - apply HU.
                   - apply Haxix.
                   - split. apply Hparx. apply HPx.
                   - split. apply Hparx'. apply HPx'.
                   - destruct Haxsub as [Haxsub | Haxsub].
                     + (* a -> x is in the path. *)
                       assert (Hamem: In a (h :: t ++ [v])). { apply sublist_member with (l1 := [a; x]). split. left. reflexivity. apply Haxsub. }
                       apply index_exists in Hamem. destruct Hamem as [ia Hia].
                       clear HA1''. clear HPx. clear Hparx. clear Hx. clear HPx'. clear HxU. clear Hparx'. clear HxU'. clear Hx'. clear Hxu.
                       clear Hconn. clear HA2''. clear HA12. clear Hi. clear HA1ind. clear HA2ind. clear HA1w.
                       generalize dependent a. generalize dependent ix. generalize dependent x. induction ia as [| ia' IH].
                       * intros x ix a Haxix Haxsub Hia. (* a = h, and h is in A4, so true by HA4_const *)
                         apply index_correct in Hia. simpl in Hia. inversion Hia.
                         apply HA4_const. apply assigned_is_true. apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (h, v, t)). split.
                         -- rewrite <- H3. apply HhA4.
                         -- rewrite <- HA4ind. apply HA4.
                       * intros x ix a Haxix Haxsub Hia. (* induct on node at index ia' *)
                         assert (Hnodex: node_in_graph x G = true).
                         { assert (Hnodex: node_in_graph a G = true /\ node_in_graph x G = true).
                           { apply edge_corresponds_to_nodes_in_well_formed. split. apply HG. simpl.
                             apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. apply Haxix. }
                           apply Hnodex. }
                         simpl in Haxsub. destruct (a =? h) as [|] eqn:Hha.
                         -- apply eqb_eq in Hha. rewrite Hha in Hia. simpl in Hia. rewrite eqb_refl in Hia. inversion Hia.
                         -- simpl in Haxsub.
                            assert (Hb: exists (b: node), sublist [b; a] (h :: t ++ [v]) = true).
                            { apply not_first_node_has_sublist. split. apply Hha. apply sublist_member with (l1 := [a; x]). split.
                              left. reflexivity. apply Haxsub. }
                            destruct Hb as [b Hb].
                            assert (Hba: (edge_in_graph (b, a) G = true \/ edge_in_graph (a, b) G = true)
                                          /\ (node_in_graph b G = true /\ node_in_graph a G = true)).
                            { assert (Hedge: is_edge (b, a) G = true \/ is_edge (a, b) G = true).
                              { apply sublist_of_path_has_edge with (h := h) (v := v) (t := t). apply Hb.
                                apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply is_path_in_graph_induction with (u := u). apply Hp. }
                              destruct Hedge as [Hba | Hab].
                              - split.
                                + left. unfold is_edge in Hba. destruct G as [V E]. apply split_and_true in Hba. simpl. apply Hba.
                                + unfold is_edge in Hba. destruct G as [V E]. apply split_and_true in Hba. simpl. apply split_and_true. apply Hba.
                              - split.
                                + right. unfold is_edge in Hab. destruct G as [V E]. apply split_and_true in Hab. simpl. apply Hab.
                                + unfold is_edge in Hab. destruct G as [V E]. apply split_and_true in Hab. simpl. apply split_and_true. rewrite andb_comm. apply Hab. }

                            assert (Ha: exists (P: assignments X), find_values G g (find_parents a G) U [] = Some P
                                     /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents a G)
                                     /\ exists (unobs: X), get_assigned_value U a = Some unobs
                                     /\ find_value G g a U [] = Some (g a (unobs, pa))).
                            { apply find_value_evaluates_to_g. split.
                              - destruct HG as [_ HG]. apply HG.
                              - split. apply HU. apply Hba. }
                            destruct Ha as [Pa [HPa [paa [Hpara [unobsa [HaU Ha]]]]]]. rewrite Ha.
                            assert (Ha2: exists (P: assignments X), find_values G g' (find_parents a G) U [] = Some P
                                 /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents a G)
                                 /\ exists (unobs: X), get_assigned_value U a = Some unobs
                                 /\ find_value G g' a U [] = Some (g' a (unobs, pa))).
                            { apply find_value_evaluates_to_g. split.
                              - destruct HG as [_ HG]. apply HG.
                              - split. apply HU. apply Hba. }
                            destruct Ha2 as [Pa' [HPa' [paa' [Hpara' [unobsa' [HaU' Ha2]]]]]]. rewrite Ha2.
                            rewrite Heqg. rewrite Heqg'. unfold g_path'.
                            assert (Hau: u =? a = false). (* a is in path not including u. since path acyclic, cannot equal u *)
                            { apply paths_start_to_end_correct in Hp. destruct Hp as [_ [_ Hp]].
                              destruct (u =? a) as [|] eqn:Hua.
                              - apply eqb_eq in Hua. rewrite Hua in Hp. unfold acyclic_path_2 in Hp.
                                assert (Hmema: In a ((h :: t) ++ [v])). { apply sublist_member with (l1 := [b; a]). split. right. left. reflexivity. apply Hb. }
                                apply membership_append_or in Hmema. destruct Hmema as [Hmema | Hmema].
                                + destruct Hp as [_ [Hp _]]. exfalso. apply Hp. apply Hmema.
                                + simpl in Hmema. destruct Hp as [Hp _]. exfalso. apply Hp. destruct Hmema as [Hmema | Hmema]. rewrite Hmema. reflexivity. exfalso. apply Hmema.
                              - reflexivity. }
                            simpl. rewrite Hau.
                            destruct Hba as [Hba Hnodeba]. destruct Hba as [Hba | Hab].
                            ++ assert (Hib: exists (ib: nat), Some ib = index (find_parents a G) b).
                               { apply index_exists. apply edge_from_parent_to_child. apply Hba. }
                               destruct Hib as [ib Hib].
                               assert (Hca: count a (h :: t ++ [v]) = 1).
                               { apply acyclic_path_count.
                                 * apply sublist_member with (l1 := [b; a]). split. right. left. reflexivity. apply Hb.
                                 * apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity.
                                   apply paths_start_to_end_correct in Hp. apply Hp. }
                               specialize IH with (x := a) (ix := ib) (a := b).
                               assert (Hind: find_value G g b U [] = find_value G g' b U []).
                               { apply IH.
                                 - apply index_correct. apply Hib.
                                 - apply Hb.
                                 - apply index_of_sublist with (a := a).
                                   + apply Hb.
                                   + apply Hca.
                                   + apply acyclic_path_count.
                                     * apply sublist_member with (l1 := [b; a]). split. left. reflexivity. apply Hb.
                                     * apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity.
                                       apply paths_start_to_end_correct in Hp. apply Hp.
                                   + apply Hia. }

                               assert (HaA1': exists (ia: nat), get_assigned_value A1' a = Some ia).
                               { apply assigned_has_value with (L := get_A1_binded_nodes_in_g_path G (h, v, t)). split.
                                 - assert (Hamed: In a (find_mediators_in_path (h, v, t) G)).
                                   { apply mediators_vs_edges_in_path. exists b. exists x. repeat split.
                                     - apply merge_two_sublists.
                                       + simpl. apply split_orb_true. right. apply Haxsub.
                                       + apply Hb.
                                       + apply Hca.
                                     - left. split. unfold is_edge. destruct G as [V E]. simpl in Hnodeba. destruct Hnodeba as [Hnodeb Hnodea].
                                       rewrite Hnodeb. rewrite Hnodea. simpl in Hba. rewrite Hba. reflexivity.
                                       apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. unfold is_edge. destruct G as [V E].
                                       simpl in Hnodeba. destruct Hnodeba as [_ Hnodea]. rewrite Hnodea. simpl in Haxix. rewrite Haxix.
                                       simpl in Hnodex. rewrite Hnodex. reflexivity. }
                                   unfold get_A1_binded_nodes_in_g_path. destruct (path_out_of_end (h, v, t) G) as [[|]|] eqn:Hout.
                                   + destruct (path_into_start (h, v, t) G) as [|]. right. apply Hamed. apply Hamed.
                                   + destruct (path_into_start (h, v, t) G) as [|]. right. apply membership_append. apply Hamed. apply membership_append. apply Hamed.
                                   + apply path_out_of_end_Some in Hout. apply Hout.
                                 - unfold is_exact_assignment_for in HA1'. apply HA1'. }
                               destruct HaA1' as [ia HaA1']. rewrite HaA1'. unfold f_parent_i. simpl. f_equal.

                               unfold A1_nodes_binded_to_parent_in_path in HA1bind. specialize HA1bind with (m := a) (i := ia). apply get_assigned_In in HaA1'.
                               apply HA1bind in HaA1'. destruct HaA1' as [b' [Hia' Hba']]. rewrite HaU' in HaU. inversion HaU. apply Hi' with (g := g) (g' := g') (U := U) (a := b') (w := a) (P := Pa) (P' := Pa').
                               ** apply parents_in_graph with (u := a). apply HG. apply nth_error_In in Hia'. apply Hia'.
                               ** apply HU.
                               ** apply Hia'.
                               ** split. apply Hpara. apply HPa.
                               ** split. apply Hpara'. apply HPa'.
                               ** destruct Hba' as [Hba' | Hab'].
                                  --- assert (Hbb': b = b').
                                      { apply two_sublists_the_same_2 with (l := h :: t ++ [v]) (a := a).
                                        - apply Hb.
                                        - apply Hba'.
                                        - apply Hca. }
                                      rewrite <- Hbb'. apply Hind.
                                  --- assert (Hbb': x = b').
                                      { apply two_sublists_the_same with (l := h :: t ++ [v]) (a := a).
                                        - simpl. apply split_orb_true. right. apply Haxsub.
                                        - apply Hab'.
                                        - apply Hca. }
                                      unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [_ HG]]. apply contains_cycle_false_correct with (p := (a, a, [x])) in HG.
                                      +++ unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
                                      +++ apply directed_path_is_path. simpl. unfold is_edge. destruct G as [V E].
                                          rewrite <- Hbb' in Hia'. apply nth_error_In in Hia'. apply edge_from_parent_to_child in Hia'. simpl in Hia'. rewrite Hia'.
                                          apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. simpl in Haxix. rewrite Haxix.
                                          destruct Hnodeba as [_ Hnodea]. simpl in Hnodea. rewrite Hnodea. simpl in Hnodex. rewrite Hnodex. reflexivity.

                            ++ assert (HaA4': exists (xa: X), get_assigned_value A4 a = Some xa).
                               { apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (h, v, t)). split.
                                 - assert (Hacon: In a (find_confounders_in_path (h, v, t) G)).
                                   { apply confounders_vs_edges_in_path. exists b. exists x. repeat split.
                                     - apply merge_two_sublists.
                                       + simpl. apply split_orb_true. right. apply Haxsub.
                                       + apply Hb.
                                       + apply acyclic_path_count.
                                         * apply sublist_member with (l1 := [b; a]). split. right. left. reflexivity. apply Hb.
                                         * apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity.
                                           apply paths_start_to_end_correct in Hp. apply Hp.
                                     - unfold is_edge. destruct G as [V E]. simpl in Hnodeba. destruct Hnodeba as [Hnodeb Hnodea].
                                       rewrite Hnodeb. rewrite Hnodea. simpl in Hab. rewrite Hab. reflexivity.
                                     - apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. unfold is_edge. destruct G as [V E].
                                       simpl in Hnodeba. destruct Hnodeba as [_ Hnodea]. rewrite Hnodea. simpl in Haxix. rewrite Haxix. simpl in Hnodex. rewrite Hnodex. reflexivity. }
                                   unfold get_A4_binded_nodes_in_g_path. destruct (path_out_of_end (h, v, t) G) as [[|]|] eqn:Hout.
                                   + destruct (path_into_start (h, v, t) G) as [|]. apply membership_append. apply Hacon. right. apply membership_append. apply Hacon.
                                   + destruct (path_into_start (h, v, t) G) as [|]. apply Hacon. right. apply Hacon.
                                   + apply path_out_of_end_Some in Hout. apply Hout.
                                 - unfold is_exact_assignment_for in HA4. rewrite <- HA4ind. apply HA4. }
                               simpl.
                               assert (HaA4: In a (get_A4_binded_nodes_in_g_path G (h, v, t))).
                               { apply assigned_true_then_in_list with (A := A4). split. apply assigned_is_true. apply HaA4'. rewrite <- HA4ind. apply HA4. }
                               assert (HaA1': get_assigned_value A1' a = None).
                               { apply A4_nodes_not_in_A1 in HaA4. destruct HA1' as [_ HA1']. apply assigned_is_false. specialize HA1' with (u := a). apply HA1'.
                                 apply member_In_equiv_F. apply HaA4. }
                               rewrite HaA1'.
                               assert (HaA2: get_assigned_value A2' a = None).
                               { apply A4_nodes_not_in_A2 in HaA4. destruct HA2' as [_ HA2']. apply assigned_is_false. apply HA2'. apply member_In_equiv_F. apply HaA4. }
                               rewrite HaA2.
                               assert (HaA3: get_assigned_value A3' a = None).
                               { apply A4_nodes_not_in_A3 in HaA4. apply assigned_is_false. unfold is_exact_assignment_for in HA3'. destruct HA3' as [_ HA3']. apply HA3'.
                                 apply member_In_equiv_F. apply HaA4. }
                               rewrite HaA3.
                               destruct HaA4' as [xa HaA4']. rewrite HaA4'. unfold f_constant. reflexivity.

                     + (* x <- a is in the path. *)
                       assert (Hamem: In a (rev (h :: t ++ [v]))). { apply membership_rev. apply sublist_member with (l1 := [x; a]). split. right. left. reflexivity. apply Haxsub. }
                       apply index_exists in Hamem. destruct Hamem as [ia Hia].
                       clear HA1''. clear HPx. clear Hparx. clear Hx. clear HPx'. clear HxU. clear Hparx'. clear HxU'. clear Hx'. clear Hxu.
                       clear Hconn. clear HA2''. clear HA12. clear Hi. clear HA1ind. clear HA2ind. clear HA1w.
                       generalize dependent a. generalize dependent ix. generalize dependent x. induction ia as [| ia' IH].
                       * intros x ix a Haxix Haxsub Hia. (* a = v, so path_out_of_end, so v is in A4, so true by HA4_const *)
                         apply index_correct in Hia. simpl in Hia. rewrite reverse_list_append in Hia. simpl in Hia. inversion Hia.
                         apply HA4_const. apply assigned_is_true. apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (h, v, t)). split.
                         -- rewrite <- H3. unfold get_A4_binded_nodes_in_g_path.
                            assert (Hout: path_out_of_end (h, v, t) G = Some true).
                            { rewrite <- H3 in Haxsub. rewrite <- H3 in Haxix. apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. apply sublist_path_out_of_end with (x := x).
                              - unfold is_edge.
                                assert (Hnodevx: node_in_graph v G = true /\ node_in_graph x G = true).
                                { apply edge_corresponds_to_nodes_in_well_formed. split. apply HG. apply Haxix. }
                                destruct G as [V E]. simpl in Haxix. rewrite Haxix. simpl in Hnodevx. destruct Hnodevx as [Hnodev Hnodex]. rewrite Hnodev. rewrite Hnodex. reflexivity.
                              - apply Haxsub.
                              - apply paths_start_to_end_correct in Hp. destruct Hp as [_ [_ Hp]]. unfold acyclic_path_2 in Hp. destruct Hp as [_ [_ [Hp _]]]. apply Hp. }
                            rewrite Hout. destruct (path_into_start (h, v, t) G) as [|]. apply membership_append_r. left. reflexivity. right. apply membership_append_r. left. reflexivity.
                         -- rewrite <- HA4ind. apply HA4.
                       * intros x ix a Haxix Haxsub Hia. (* induct on node at index ia' of reverse path (after a in original path) *)
                         assert (Hnodex: node_in_graph x G = true).
                         { assert (Hnodex: node_in_graph a G = true /\ node_in_graph x G = true).
                           { apply edge_corresponds_to_nodes_in_well_formed. split. apply HG. simpl.
                             apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. apply Haxix. }
                           apply Hnodex. }
                         simpl in Haxsub. destruct (a =? v) as [|] eqn:Hva.
                         -- simpl in Hia. rewrite reverse_list_append in Hia. simpl in Hia. rewrite eqb_sym in Hva. rewrite Hva in Hia. inversion Hia.
                         -- assert (Hb: exists (b: node), sublist [a; b] (h :: t ++ [v]) = true).
                            { assert (Hb: exists b : nat, sublist [b; a] (v :: rev t ++ [h]) = true).
                              { apply not_first_node_has_sublist. split. apply Hva.
                                assert (Hmem: In a (rev (h :: t ++ [v]))). { apply index_exists. exists (S ia'). apply Hia. }
                                simpl in Hmem. rewrite reverse_list_append in Hmem. simpl in Hmem. destruct Hmem as [Hmem | Hmem].
                                - rewrite Hmem in Hva. rewrite eqb_refl in Hva. discriminate Hva.
                                - apply Hmem. }
                              destruct Hb as [b Hb]. exists b. rewrite reverse_list_twice with (l := h :: t ++ [v]). rewrite reverse_list_twice with (l := (@cons node a (@cons node b (@nil node)))).
                              apply sublist_rev. simpl. rewrite reverse_list_append. simpl. apply Hb. }
                            destruct Hb as [b Hb].

                            assert (Hba: (edge_in_graph (b, a) G = true \/ edge_in_graph (a, b) G = true)
                                          /\ (node_in_graph b G = true /\ node_in_graph a G = true)).
                            { assert (Hedge: is_edge (b, a) G = true \/ is_edge (a, b) G = true).
                              { apply or_comm. apply sublist_of_path_has_edge with (h := h) (v := v) (t := t). apply Hb.
                                apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply is_path_in_graph_induction with (u := u). apply Hp. }
                              destruct Hedge as [Hba | Hab].
                              - split.
                                + left. unfold is_edge in Hba. destruct G as [V E]. apply split_and_true in Hba. simpl. apply Hba.
                                + unfold is_edge in Hba. destruct G as [V E]. apply split_and_true in Hba. simpl. apply split_and_true. apply Hba.
                              - split.
                                + right. unfold is_edge in Hab. destruct G as [V E]. apply split_and_true in Hab. simpl. apply Hab.
                                + unfold is_edge in Hab. destruct G as [V E]. apply split_and_true in Hab. simpl. apply split_and_true. rewrite andb_comm. apply Hab. }

                            assert (Ha: exists (P: assignments X), find_values G g (find_parents a G) U [] = Some P
                                     /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents a G)
                                     /\ exists (unobs: X), get_assigned_value U a = Some unobs
                                     /\ find_value G g a U [] = Some (g a (unobs, pa))).
                            { apply find_value_evaluates_to_g. split.
                              - destruct HG as [_ HG]. apply HG.
                              - split. apply HU. apply Hba. }
                            destruct Ha as [Pa [HPa [paa [Hpara [unobsa [HaU Ha]]]]]]. rewrite Ha.
                            assert (Ha2: exists (P: assignments X), find_values G g' (find_parents a G) U [] = Some P
                                 /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents a G)
                                 /\ exists (unobs: X), get_assigned_value U a = Some unobs
                                 /\ find_value G g' a U [] = Some (g' a (unobs, pa))).
                            { apply find_value_evaluates_to_g. split.
                              - destruct HG as [_ HG]. apply HG.
                              - split. apply HU. apply Hba. }
                            destruct Ha2 as [Pa' [HPa' [paa' [Hpara' [unobsa' [HaU' Ha2]]]]]]. rewrite Ha2.
                            rewrite Heqg. rewrite Heqg'. unfold g_path'.

                            assert (Hau: u =? a = false). (* a is in path not including u. since path acyclic, cannot equal u *)
                            { apply paths_start_to_end_correct in Hp. destruct Hp as [_ [_ Hp]].
                              destruct (u =? a) as [|] eqn:Hua.
                              - apply eqb_eq in Hua. rewrite Hua in Hp. unfold acyclic_path_2 in Hp.
                                assert (Hmema: In a ((h :: t) ++ [v])). { apply sublist_member with (l1 := [a; b]). split. left. reflexivity. apply Hb. }
                                apply membership_append_or in Hmema. destruct Hmema as [Hmema | Hmema].
                                + destruct Hp as [_ [Hp _]]. exfalso. apply Hp. apply Hmema.
                                + simpl in Hmema. destruct Hp as [Hp _]. exfalso. apply Hp. destruct Hmema as [Hmema | Hmema]. rewrite Hmema. reflexivity. exfalso. apply Hmema.
                              - reflexivity. } (* TODO can generalize above using generalized l1 for sublist_member *)
                            simpl. rewrite Hau.

                            assert (Hca: count a (h :: t ++ [v]) = 1).
                            { apply acyclic_path_count.
                              * apply sublist_member with (l1 := [a; b]). split. left. reflexivity. apply Hb.
                              * apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity.
                                apply paths_start_to_end_correct in Hp. apply Hp. }
                            destruct Hba as [Hba Hnodeba]. destruct Hba as [Hba | Hab].

                            ++ assert (Hib: exists (ib: nat), Some ib = index (find_parents a G) b).
                               { apply index_exists. apply edge_from_parent_to_child. apply Hba. }
                               destruct Hib as [ib Hib].

                               specialize IH with (x := a) (ix := ib) (a := b).
                               assert (Hind: find_value G g b U [] = find_value G g' b U []).
                               { apply IH.
                                 - apply index_correct. apply Hib.
                                 - apply Hb.
                                 - apply index_of_sublist with (a := a).
                                   + rewrite reverse_list_twice with (l := (@cons nat b (@cons nat a (@nil nat)))). apply sublist_rev. simpl. apply Hb.
                                   + rewrite <- count_reverse. apply Hca.
                                   + rewrite <- count_reverse. apply acyclic_path_count.
                                     * apply sublist_member with (l1 := [a; b]). split. right. left. reflexivity. apply Hb.
                                     * apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity.
                                       apply paths_start_to_end_correct in Hp. apply Hp.
                                   + apply Hia. }

                               assert (HaA1': exists (ia: nat), get_assigned_value A1' a = Some ia).
                               { apply assigned_has_value with (L := get_A1_binded_nodes_in_g_path G (h, v, t)). split.
                                 - assert (Hamed: In a (find_mediators_in_path (h, v, t) G)).
                                   { apply mediators_vs_edges_in_path. exists x. exists b. repeat split.
                                     - apply merge_two_sublists.
                                       + apply Hb.
                                       + apply Haxsub.
                                       + apply Hca.
                                     - right. split. apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. apply edge_in_graph_then_is_edge. apply HG. apply Haxix.
                                       apply edge_in_graph_then_is_edge. apply HG. apply Hba. }

                                   unfold get_A1_binded_nodes_in_g_path. destruct (path_out_of_end (h, v, t) G) as [[|]|] eqn:Hout.
                                   + destruct (path_into_start (h, v, t) G) as [|]. right. apply Hamed. apply Hamed.
                                   + destruct (path_into_start (h, v, t) G) as [|]. right. apply membership_append. apply Hamed. apply membership_append. apply Hamed.
                                   + apply path_out_of_end_Some in Hout. apply Hout.
                                 - unfold is_exact_assignment_for in HA1'. apply HA1'. }
                               destruct HaA1' as [ia HaA1']. rewrite HaA1'. unfold f_parent_i. simpl. f_equal.

                               unfold A1_nodes_binded_to_parent_in_path in HA1bind. specialize HA1bind with (m := a) (i := ia). apply get_assigned_In in HaA1'.
                               apply HA1bind in HaA1'. destruct HaA1' as [b' [Hia' Hba']]. rewrite HaU' in HaU. inversion HaU. apply Hi' with (g := g) (g' := g') (U := U) (a := b') (w := a) (P := Pa) (P' := Pa').
                               ** apply parents_in_graph with (u := a). apply HG. apply nth_error_In in Hia'. apply Hia'.
                               ** apply HU.
                               ** apply Hia'.
                               ** split. apply Hpara. apply HPa.
                               ** split. apply Hpara'. apply HPa'.
                               ** destruct Hba' as [Hba' | Hab'].
                                  --- assert (Hbb': x = b').
                                      { apply two_sublists_the_same_2 with (l := h :: t ++ [v]) (a := a).
                                        - apply Haxsub.
                                        - apply Hba'.
                                        - apply Hca. }
                                      unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [_ HG]]. apply contains_cycle_false_correct with (p := (a, a, [x])) in HG.
                                      +++ unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
                                      +++ apply directed_path_is_path. simpl. unfold is_edge. destruct G as [V E].
                                          rewrite <- Hbb' in Hia'. apply nth_error_In in Hia'. apply edge_from_parent_to_child in Hia'. simpl in Hia'. rewrite Hia'.
                                          apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. simpl in Haxix. rewrite Haxix.
                                          destruct Hnodeba as [_ Hnodea]. simpl in Hnodea. rewrite Hnodea. simpl in Hnodex. rewrite Hnodex. reflexivity.
                                  --- assert (Hbb': b = b').
                                      { apply two_sublists_the_same with (l := h :: t ++ [v]) (a := a).
                                        - apply Hb.
                                        - apply Hab'.
                                        - apply Hca. }
                                      rewrite <- Hbb'. apply Hind.

                            ++ assert (HaA4': exists (xa: X), get_assigned_value A4 a = Some xa).
                               { apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (h, v, t)). split.
                                 - assert (Hacon: In a (find_confounders_in_path (h, v, t) G)).
                                   { apply confounders_vs_edges_in_path. exists x. exists b. repeat split.
                                     - apply merge_two_sublists.
                                       + apply Hb.
                                       + apply Haxsub.
                                       + apply acyclic_path_count.
                                         * apply sublist_member with (l1 := [a; b]). split. left. reflexivity. apply Hb.
                                         * apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity.
                                           apply paths_start_to_end_correct in Hp. apply Hp.
                                     - apply nth_error_In in Haxix. apply edge_from_parent_to_child in Haxix. unfold is_edge. destruct G as [V E].
                                       simpl in Hnodeba. destruct Hnodeba as [_ Hnodea]. rewrite Hnodea. simpl in Haxix. rewrite Haxix. simpl in Hnodex. rewrite Hnodex. reflexivity.
                                     - unfold is_edge. destruct G as [V E]. simpl in Hnodeba. destruct Hnodeba as [Hnodeb Hnodea].
                                       rewrite Hnodeb. rewrite Hnodea. simpl in Hab. rewrite Hab. reflexivity. }
                                   unfold get_A4_binded_nodes_in_g_path. destruct (path_out_of_end (h, v, t) G) as [[|]|] eqn:Hout.
                                   + destruct (path_into_start (h, v, t) G) as [|]. apply membership_append. apply Hacon. right. apply membership_append. apply Hacon.
                                   + destruct (path_into_start (h, v, t) G) as [|]. apply Hacon. right. apply Hacon.
                                   + apply path_out_of_end_Some in Hout. apply Hout.
                                 - unfold is_exact_assignment_for in HA4. rewrite <- HA4ind. apply HA4. }
                               simpl.
                               assert (HaA4: In a (get_A4_binded_nodes_in_g_path G (h, v, t))).
                               { apply assigned_true_then_in_list with (A := A4). split. apply assigned_is_true. apply HaA4'. rewrite <- HA4ind. apply HA4. }
                               assert (HaA1': get_assigned_value A1' a = None).
                               { apply A4_nodes_not_in_A1 in HaA4. destruct HA1' as [_ HA1']. apply assigned_is_false. specialize HA1' with (u := a). apply HA1'.
                                 apply member_In_equiv_F. apply HaA4. }
                               rewrite HaA1'.
                               assert (HaA2: get_assigned_value A2' a = None).
                               { apply A4_nodes_not_in_A2 in HaA4. destruct HA2' as [_ HA2']. apply assigned_is_false. apply HA2'. apply member_In_equiv_F. apply HaA4. }
                               rewrite HaA2.
                               assert (HaA3: get_assigned_value A3' a = None).
                               { apply A4_nodes_not_in_A3 in HaA4. apply assigned_is_false. unfold is_exact_assignment_for in HA3'. destruct HA3' as [_ HA3']. apply HA3'.
                                 apply member_In_equiv_F. apply HaA4. }
                               rewrite HaA3.
                               destruct HaA4' as [xa HaA4']. rewrite HaA4'. unfold f_constant. reflexivity. }

                 unfold A2_nodes_colliders_in_graph in HA2''. specialize HA2'' with (c := w) (i := iw) (j := jw) (x := xw) (y := yw).
                 apply get_assigned_In in Hvalw. apply HA2'' in Hvalw. destruct Hvalw as [a [b Hvalw]].

                 (* since a and b are in the path and not colliders, they must be in A1 or A4 -> use HA4_const or HA1_const *)
                 assert (Ha: find_value G g a U [] = find_value G g' a U []).
                 { destruct Hvalw as [_ [_ [Hawbsub Hawbcol]]]. simpl in Hawbsub.
                   destruct (a =? h) as [|] eqn:Hah. (* since path is h ->, h is in A4 *)
                   - assert (HaA4: In a (get_A4_binded_nodes_in_g_path G (h, v, t))).
                     { apply eqb_eq in Hah. rewrite Hah. apply HhA4. }
                     apply HA4_const. apply assigned_is_true. apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (h, v, t)). split.
                     + apply HaA4.
                     + unfold is_exact_assignment_for in HA4. rewrite <- HA4ind. apply HA4.
                   - simpl in Hawbsub. assert (Hat: In a t). { apply first_elt_of_sublist_not_last_elt with (b := w) (c := b) (v := v). apply Hawbsub. }
                     assert (Hpath: is_path_in_graph (h, v, t) G = true). { apply paths_start_to_end_correct in Hp. apply is_path_in_graph_induction with (u := u). apply Hp. }
                     apply intermediate_node_in_path with (x := a) in Hpath. apply Hpath in Hat. clear Hpath. rewrite <- or_assoc in Hat. destruct Hat as [Hat | Hacol].
                     + apply Hfv with (g := g) (g' := g') (U := U) (A4 := A4) in Hat. apply Hat. apply HA4_const. apply HA4. apply HA1_const.
                     + (* contradiction: since a -> w is an edge, a is not a collider *)
                       apply colliders_vs_edges_in_path in Hacol. destruct Hacol as [a1 [a2 [Hasub Haedge]]].
                       assert (Ha2w: (w =? a2) = false).
                       { unfold is_collider_bool in Hawbcol. destruct (w =? a2) as [|] eqn:Hwa2.
                         - unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [_ HG]]. apply contains_cycle_false_correct with (p := (a, a, [w])) in HG.
                           + unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
                           + apply directed_path_is_path. simpl. destruct Haedge as [_ Ha2a]. apply eqb_eq in Hwa2. rewrite <- Hwa2 in Ha2a. rewrite Ha2a.
                             apply split_and_true in Hawbcol. destruct Hawbcol as [Haw _]. rewrite Haw. reflexivity.
                         - reflexivity. }
                       assert (Ha2w': w = a2).
                       { apply two_sublists_the_same with (l := t ++ [v]) (a := a).
                         - apply start_of_sublist_still_sublist in Hawbsub. apply Hawbsub.
                         - apply end_of_sublist_still_sublist in Hasub. apply Hasub.
                         - assert (Hca: count a (h :: t ++ [v]) = 1).
                           { apply acyclic_path_count.
                             * apply sublist_member with (l1 := [a1; a; a2]). split. right. left. reflexivity. apply Hasub.
                             * apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity.
                               apply paths_start_to_end_correct in Hp. apply Hp. }
                           simpl in Hca. rewrite eqb_sym in Hah. rewrite Hah in Hca. apply Hca. }
                       rewrite Ha2w' in Ha2w. rewrite eqb_refl in Ha2w. discriminate Ha2w. }
                 assert (Hb: find_value G g b U [] = find_value G g' b U []).
                 { destruct Hvalw as [_ [_ [Hawbsub Hawbcol]]]. simpl in Hawbsub.
                   destruct (b =? v) as [|] eqn:Hbv. (* depending on arrow into v, v is in A4 or A1 *)
                   - apply eqb_eq in Hbv. rewrite Hbv in *. destruct (path_out_of_end (h, v, t) G) as [[|]|] eqn:Hout.
                     + assert (HbA4: In v (get_A4_binded_nodes_in_g_path G (h, v, t))).
                       { unfold get_A4_binded_nodes_in_g_path. rewrite Hout. destruct (path_into_start (h, v, t) G) as [|]. apply membership_append_r. left. reflexivity.
                         right. apply membership_append_r. left. reflexivity. }
                       apply HA4_const. apply assigned_is_true. apply assigned_has_value with (L := get_A4_binded_nodes_in_g_path G (h, v, t)). split.
                       * apply HbA4.
                       * unfold is_exact_assignment_for in HA4. rewrite <- HA4ind. apply HA4.
                     + assert (HbA1: In v (get_A1_binded_nodes_in_g_path G (h, v, t))).
                       { unfold get_A1_binded_nodes_in_g_path. rewrite Hout. destruct (path_into_start (h, v, t) G) as [|]. right. apply membership_append_r. left. reflexivity.
                         apply membership_append_r. left. reflexivity. }
                       apply HA1_const. apply assigned_is_true. apply assigned_has_value with (L := get_A1_binded_nodes_in_g_path G (h, v, t)). split.
                       * apply HbA1.
                       * unfold is_exact_assignment_for in HA1'. apply HA1'.
                     + apply path_out_of_end_Some in Hout. exfalso. apply Hout.
                   - assert (Hatv: In b (t ++ [v])). { apply middle_elt_of_sublist_not_first_elt_gen with (A := [w; b]) (a := a) (h := h). split. apply Hawbsub. right. left. reflexivity. }
                     assert (Hbt: In b t). { apply membership_append_or in Hatv. destruct Hatv as [Hatv | Hatv]. apply Hatv. destruct Hatv as [Hatv | Hatv]. rewrite Hatv in Hbv. rewrite eqb_refl in Hbv. discriminate Hbv. exfalso. apply Hatv. }
                     clear Hatv.
                     assert (Hpath: is_path_in_graph (h, v, t) G = true). { apply paths_start_to_end_correct in Hp. apply is_path_in_graph_induction with (u := u). apply Hp. }
                     apply intermediate_node_in_path with (x := b) in Hpath. apply Hpath in Hbt. clear Hpath. apply or_assoc in Hbt. destruct Hbt as [Hbt | Hbcol].
                     + apply Hfv with (g := g) (g' := g') (U := U) (A4 := A4) in Hbt. apply Hbt. apply HA4_const. apply HA4. apply HA1_const.
                     + (* contradiction: since w <- b is an edge, b is not a collider *)
                       apply colliders_vs_edges_in_path in Hbcol. destruct Hbcol as [b1 [b2 [Hbsub Hbedge]]].
                       assert (Hb1w: (w =? b1) = false).
                       { unfold is_collider_bool in Hawbcol. destruct (w =? b1) as [|] eqn:Hwb1.
                         - unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ [_ HG]]. apply contains_cycle_false_correct with (p := (b, b, [w])) in HG.
                           + unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
                           + apply directed_path_is_path. simpl. destruct Hbedge as [Hb1w _]. apply eqb_eq in Hwb1. rewrite <- Hwb1 in Hb1w. rewrite Hb1w.
                             apply split_and_true in Hawbcol. destruct Hawbcol as [_ Hwb]. rewrite Hwb. reflexivity.
                         - reflexivity. }
                       assert (Hb1w': w = b1).
                       { apply two_sublists_the_same_2 with (l := h :: t ++ [v]) (a := b).
                         - apply end_of_sublist_still_sublist_2 in Hawbsub. apply Hawbsub.
                         - apply start_of_sublist_still_sublist in Hbsub. apply Hbsub.
                         - assert (Hcb: count b (h :: t ++ [v]) = 1).
                           { apply acyclic_path_count.
                             * apply sublist_member with (l1 := [b1; b; b2]). split. right. left. reflexivity. apply Hbsub.
                             * apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity.
                               apply paths_start_to_end_correct in Hp. apply Hp. }
                           apply Hcb. }
                       rewrite Hb1w' in Hb1w. rewrite eqb_refl in Hb1w. discriminate Hb1w. }

                 assert (Hiw: nth_default unobs' pa iw = nth_default unobs' pa' iw).
                 { apply Hi' with (g := g) (g' := g') (U := U) (a := a) (w := w) (P := P) (P' := P'). apply parents_in_graph with (u := w). apply HG. destruct Hvalw as [Hvalw _]. apply nth_error_In in Hvalw. apply Hvalw. apply HU.
                   apply Hvalw. easy. easy. apply Ha. }
                 assert (Hjw: nth_default unobs' pa jw = nth_default unobs' pa' jw).
                 { apply Hi' with (g := g) (g' := g') (U := U) (a := b) (w := w) (P := P) (P' := P'). apply parents_in_graph with (u := w). apply HG. destruct Hvalw as [_ [Hvalw _]]. apply nth_error_In in Hvalw. apply Hvalw. apply HU.
                   apply Hvalw. easy. easy. apply Hb. }
                 rewrite Hiw. rewrite Hjw. reflexivity. }
               { unfold nodes in *. rewrite HA4ind in HA4. apply HA4. }
            -- intros Hcond. specialize HA12 with (A4 := A4) (default := default) (U := U) (A5 := (u, f_parent_i X i) :: A5). pose proof H1 as HU. apply HA12 in H1. clear HA12.
               { destruct H1 as [_ HA12].
                 remember (g_path' X A1' A2' A3' A4 ((u, f_parent_i X i) :: A5) default) as g. remember (g_path' X ((u, i) :: A1') A2' A3' A4 A5 default) as g'.
                 assert (Hg: g = g').
                 { apply functional_extensionality. intros x. rewrite Heqg. rewrite Heqg'. unfold g_path'. simpl.
                   destruct (u =? x) as [|] eqn:Hux.
                   - apply eqb_eq in Hux. rewrite <- Hux in *. assert (Humem: node_in_path u (h, v, t) = false).
                     { apply paths_start_to_end_correct in Hp. destruct Hp as [_ [_ Hp]]. unfold acyclic_path_2 in Hp.
                       unfold node_in_path. simpl. destruct (u =? h) as [|] eqn:Huh.
                       - exfalso. destruct Hp as [_ [Hp _]]. apply Hp. left. apply eqb_eq in Huh. rewrite Huh. reflexivity.
                       - simpl. destruct (u =? v) as [|] eqn:Huv.
                         + exfalso. destruct Hp as [Hp _]. apply Hp. apply eqb_eq in Huv. apply Huv.
                         + simpl. destruct Hp as [_ [Hp _]]. apply member_In_equiv_F. intros F. apply Hp. right. apply F. }
                     assert (HxA1': get_assigned_value A1' u = None).
                     { destruct (is_assigned A1' u) as [|] eqn:HxA1'.
                       - assert (Hmem: node_in_path u (h, v, t) = true).
                         { apply A1_nodes_in_path with (G := G). apply assigned_true_then_in_list with (A := A1'). split. apply HxA1'. apply HA1'. }
                         rewrite Hmem in Humem. discriminate Humem.
                       - apply assigned_is_false. apply HxA1'. }
                     rewrite HxA1'.
                     assert (HxA2': get_assigned_value A2' u = None).
                     { destruct (is_assigned A2' u) as [|] eqn:HxA2'.
                       - assert (Hcol: In u (get_A2_binded_nodes_in_g_path G (h, v, t))).
                         { apply assigned_true_then_in_list with (A := A2'). split. apply HxA2'. apply HA2'. }
                         unfold get_A2_binded_nodes_in_g_path in Hcol. apply colliders_vs_edges_in_path in Hcol. destruct Hcol as [y [z [Hsub _]]].
                         assert (Hmem: In u (h :: t ++ [v])). { apply sublist_member with (l1 := [y; u; z]). split. right. left. reflexivity. apply Hsub. }
                         unfold node_in_path in Humem. simpl in Humem. destruct Hmem as [Hmem | Hmem]. rewrite Hmem in Humem. rewrite eqb_refl in Humem. discriminate Humem.
                         apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem]. apply member_In_equiv in Hmem. rewrite Hmem in Humem. rewrite orb_comm in Humem. discriminate Humem.
                         destruct Hmem as [Hmem | Hmem]. rewrite Hmem in Humem. rewrite eqb_refl in Humem. rewrite <- orb_assoc in Humem. rewrite orb_comm in Humem. discriminate Humem. exfalso. apply Hmem.
                       - apply assigned_is_false. apply HxA2'. }
                     rewrite HxA2'.
                     assert (HxA3': get_assigned_value A3' u = None). { admit. }
                     rewrite HxA3'.
                     assert (HxA4: get_assigned_value A4 u = None).
                     { destruct (is_assigned A4 u) as [|] eqn:HxA4.
                       - assert (Hmem: node_in_path u (h, v, t) = true).
                         { apply A4_nodes_in_path with (G := G). apply assigned_true_then_in_list with (A := A4). split. apply HxA4. unfold nodes. rewrite <- HA4ind.
                           apply H0. }
                         rewrite Hmem in Humem. discriminate Humem.
                       - apply assigned_is_false. apply HxA4. }
                     rewrite HxA4. reflexivity.
                   - reflexivity. }
                 assert (Hcond': unobs_conditions_on_Z G g U AZ Z).
                 { rewrite Hg. apply Hcond. }

                 apply HA12 in Hcond'. destruct Hcond' as [x Hcond']. exists x. intros w [Hwp Hwcol].
                 rewrite <- Hg.
                 unfold node_in_path in Hwp. simpl in Hwp. apply split_orb_true in Hwp. destruct Hwp as [Hwp | Hwp].
                 - assert (Hh: find_value G g h U [] = Some x).
                   { apply Hcond'. split.
                     * unfold node_in_path. simpl. rewrite eqb_refl. reflexivity.
                     * intros Hmem. apply colliders_vs_edges_in_path in Hmem. destruct Hmem as [y [z [Hsub _]]].
                       assert (Hacyc: acyclic_path_2 (h, v, t)).
                       { apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity.
                         apply paths_start_to_end_correct in Hp. apply Hp. }
                       unfold acyclic_path_2 in Hacyc.
                       assert (Hmem: In h (t ++ [v])). { apply middle_elt_of_sublist_not_first_elt_gen with (A := [h; z]) (a := y) (h := h). split. apply Hsub. left. reflexivity. }
                       apply membership_append_or in Hmem. destruct Hmem as [Hmem | [Hmem | F]]. destruct Hacyc as [_ [Hacyc _]]. apply Hacyc. apply Hmem.
                       destruct Hacyc as [Hacyc _]. apply Hacyc. rewrite Hmem. reflexivity. apply F. }

                   specialize Hcond' with (w := w). apply split_orb_true in Hwp. destruct Hwp as [Hwp | Hwp].
                   + assert (Hw: exists (P: assignments X), find_values G g (find_parents w G) U [] = Some P
                              /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                              /\ exists (unobs: X), get_assigned_value U w = Some unobs
                              /\ find_value G g w U [] = Some (g w (unobs, pa))).
                     { apply find_value_evaluates_to_g. split.
                       - destruct HG as [_ HG]. apply HG.
                       - split. apply HU. apply eqb_eq in Hwp. rewrite Hwp. unfold path_into_start in Hin. apply is_edge_then_node_in_graph with (v := h). right. apply Hin. }
                     destruct Hw as [Pw [HPw [paw [Hpaw [unobsw [HwU Hw]]]]]]. rewrite Hw. apply eqb_eq in Hwp. rewrite Hwp in *.
                     rewrite Hg. rewrite Heqg'. f_equal. unfold g_path'. simpl. rewrite eqb_refl. unfold f_parent_i. simpl.

                     assert (HPwh: get_assigned_value Pw h = Some x).
                     { apply find_values_get_assigned with (G := G) (g := g) (P := find_parents u G) (U := U) (A := []). repeat split.
                       - apply HPw.
                       - apply index_exists. exists i. symmetry. apply Hi.
                       - apply Hh. }
                     assert (Hiw: nth_error paw i = get_assigned_value Pw h).
                     { rewrite HPwh. apply parent_assignments_preserves_index with (P := Pw) (V := find_parents u G) (m := h). repeat split.
                       - symmetry. apply Hpaw.
                       - apply Hi.
                       - apply HPwh. }
                     unfold nth_default. rewrite Hiw. rewrite HPwh. reflexivity.
                   + apply Hcond'. split.
                     * unfold node_in_path. simpl. rewrite Hwp. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
                     * unfold get_A2_binded_nodes_in_g_path in HA2ind. intros Hmem. apply Hwcol. unfold node in *. unfold nodes in *. unfold find_colliders_in_path. unfold find_colliders_in_path in HA2ind.
                       rewrite HA2ind. unfold find_colliders_in_path in Hmem. apply Hmem.
                 - apply Hcond'. split.
                   + unfold node_in_path. simpl. destruct (w =? h) as [|] eqn:Hwh. reflexivity. rewrite eqb_sym in Hwh. rewrite Hwh in Hwp. rewrite Hwp.
                     simpl. rewrite orb_comm. reflexivity.
                   + unfold get_A2_binded_nodes_in_g_path in HA2ind. intros Hmem. apply Hwcol. unfold node in *. unfold nodes in *. unfold find_colliders_in_path. unfold find_colliders_in_path in HA2ind.
                     rewrite HA2ind. unfold find_colliders_in_path in Hmem. apply Hmem. }
               { unfold nodes in *. rewrite HA4ind in H0. apply H0. }

          * (* u -> h -> ... *)
            assert (Hi: exists i: nat, index (find_parents h G) u = Some i).
            { assert (Hh: In u (find_parents h G)).
              { apply edge_from_parent_to_child. simpl in Hin. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _].
                simpl in Hp. rewrite Hin in Hp. destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [Hp _]. rewrite orb_comm in Hp.
                simpl in Hp. simpl. apply split_and_true in Hp. apply Hp. }
              apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
            destruct Hi as [i Hi].
            assert (Hnodeu: node_in_graph u G = true).
            { apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. simpl in Hp. apply is_edge_then_node_in_graph with (v := h). destruct G as [V E].
              apply split_and_true in Hp. destruct Hp as [Hp _]. apply split_orb_true. apply Hp. }
            assert (HA1ind: get_A1_binded_nodes_in_g_path G (u, v, h :: t) = h :: get_A1_binded_nodes_in_g_path G (h, v, t)).
            { apply A1_induction_out_of_start_out_of_h.
              - split.
                ** apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
                ** destruct HG as [_ [_ HG]]. apply HG.
              - split.
                ** apply Hin.
                ** apply Houth. }
            assert (HA4ind: exists (A4'': nodes), get_A4_binded_nodes_in_g_path G (u, v, h :: t) = u :: A4'' /\ get_A4_binded_nodes_in_g_path G (h, v, t) = h :: A4'').
            { apply A4_induction_out_of_start_out_of_h.
              - split.
                ** apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
                ** destruct HG as [_ [_ HG]]. apply HG.
              - split. apply Hin. apply Houth. }
            destruct HA4ind as [A4'' HA4ind].
            exists ((h, i) :: A1'). exists A2'. exists A3'. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split.
            repeat split.

            -- (* since arrow into u, u is in A1 *)
               unfold nodes. rewrite HA1ind. simpl. rewrite eqb_refl. simpl. apply is_assignment_for_cat.
               unfold is_exact_assignment_for in HA1'. destruct HA1' as [HA1' _]. apply HA1'.
            -- intros u' Hmemu'. unfold is_exact_assignment_for in HA1'. destruct HA1' as [_ HA1']. simpl.
               assert (Hmemu: In h (get_A1_binded_nodes_in_g_path G (u, v, h :: t))).
               { rewrite HA1ind. left. reflexivity. }
               destruct (u' =? h) as [|] eqn:Huu'.
               ++ apply eqb_eq in Huu'. apply member_In_equiv in Hmemu. rewrite Huu' in Hmemu'. unfold nodes in Hmemu'. rewrite Hmemu in Hmemu'. discriminate Hmemu'.
               ++ simpl. apply HA1'. unfold nodes in Hmemu'. rewrite HA1ind in Hmemu'. unfold member in Hmemu'. rewrite eqb_sym in Hmemu'. rewrite Huu' in Hmemu'. apply Hmemu'.
            -- unfold A1_nodes_binded_to_parent_in_path. intros c i' Hmi'. simpl in Hmi'. destruct Hmi' as [Hmi' | Hmi'].
               ++ inversion Hmi'. rewrite <- H1 in *. rewrite <- H2 in *. exists u. repeat split.
                  ** apply index_correct. symmetry. apply Hi.
                  ** left. simpl. repeat rewrite eqb_refl. reflexivity.
               ++ unfold A1_nodes_binded_to_parent_in_path in HA1''. specialize HA1'' with (m := c) (i := i'). apply HA1'' in Hmi'.
                  destruct Hmi' as [a [Ha Hsub]]. exists a. split.
                  ** apply Ha.
                  ** destruct Hsub as [Hsub | Hsub].
                     --- left. simpl. simpl in Hsub. rewrite Hsub. rewrite orb_comm. reflexivity.
                     --- right. simpl. simpl in Hsub. rewrite Hsub. rewrite orb_comm. reflexivity.
            -- apply HindA2.
            -- apply HindA2.
            -- apply HindA2.
            -- admit.
            -- admit.
            -- intros A4 A5 default U HA4 HU.
               assert (HuA4: exists (cu: X), get_assigned_value A4 u = Some cu).
               { apply assigned_has_value with (L := (get_A4_binded_nodes_in_g_path G (u, v, h :: t))). split.
                 - destruct HA4ind as [HA4ind _]. rewrite HA4ind. left. reflexivity.
                 - apply HA4. }
               destruct HuA4 as [cu HuA4]. (* u evaluates to the constant cu, which h will also evaluate to *)
               specialize HA12 with (A4 := (h, cu) :: (remove_assignment_for A4 u)) (A5 := (u, f_constant X cu) :: A5) (default := default) (U := U). pose proof HU as H1.
               remember (g_path' X ((h, i) :: A1') A2' A3' A4 A5 default) as g.
               remember (g_path' X A1' A2' A3' ((h, cu) :: (remove_assignment_for A4 u)) ((u, f_constant X cu) :: A5) default) as g'.
               apply HA12 in H1.
               { assert (Hu: find_value G g u U [] = find_value G g' u U [] /\ find_value G g u U [] = Some cu).
                 { assert (Hx': exists (P: assignments X), find_values G g (find_parents u G) U [] = Some P
                        /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents u G)
                        /\ exists (unobs: X), get_assigned_value U u = Some unobs
                        /\ find_value G g u U [] = Some (g u (unobs, pa))).
                   { apply find_value_evaluates_to_g. split.
                     - destruct HG as [_ HG]. apply HG.
                     - split. apply HU. apply Hnodeu. }
                   destruct Hx' as [Px [HPx [pax [Hparx [unobsx [HxU Hx]]]]]]. rewrite Hx.
                   assert (Hx': exists (P: assignments X), find_values G g' (find_parents u G) U [] = Some P
                        /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents u G)
                        /\ exists (unobs: X), get_assigned_value U u = Some unobs
                        /\ find_value G g' u U [] = Some (g' u (unobs, pa))).
                   { apply find_value_evaluates_to_g. split.
                     - destruct HG as [_ HG]. apply HG.
                     - split. apply HU. apply Hnodeu. }
                   destruct Hx' as [Px' [HPx' [pax' [Hparx' [unobsx' [HxU' Hx']]]]]]. rewrite Hx'.
                   rewrite Heqg. rewrite Heqg'. unfold g_path'.

                   assert (HuA4': In u (get_A4_binded_nodes_in_g_path G (u, v, h :: t))). { destruct HA4ind as [HA4ind _]. rewrite HA4ind. left. reflexivity. }
                   assert (Hhu: h =? u = false).
                   { destruct (h =? u) as [|] eqn:Hhu.
                     - exfalso. apply paths_start_to_end_correct in Hp. destruct Hp as [_ [_ Hp]]. unfold acyclic_path_2 in Hp. destruct Hp as [_ [Hp _]]. apply Hp.
                       left. apply eqb_eq. apply Hhu.
                     - reflexivity. }
                   assert (HA1u: get_assigned_value ((h, i) :: A1') u = None).
                   { simpl. rewrite Hhu. apply A4_nodes_not_in_A1 in HuA4'.
                     destruct HA1' as [_ HA1']. apply assigned_is_false. specialize HA1' with (u := u). apply HA1'. apply member_In_equiv_F. intros F.
                     apply HuA4'. rewrite HA1ind. right. apply F. }
                   rewrite HA1u. simpl in HA1u. rewrite Hhu in HA1u. rewrite HA1u.
                   assert (HA2u: get_assigned_value A2' u = None).
                   { apply A4_nodes_not_in_A2 in HuA4'. destruct HA2' as [_ HA2']. apply assigned_is_false.
                     specialize HA2' with (u := u). apply HA2'. apply member_In_equiv_F. rewrite HA2ind in HuA4'. apply HuA4'. }
                   rewrite HA2u.
                   assert (HA3u: get_assigned_value A3' u = None).
                   { apply A4_nodes_not_in_A3 in HuA4'. apply assigned_is_false. unfold is_exact_assignment_for in HA3'. destruct HA3' as [_ HA3']. apply HA3'.
                     simpl in HuA4'. apply member_In_equiv_F. admit. }
                   rewrite HA3u. rewrite HuA4. unfold f_constant. f_equal.
                   simpl. rewrite Hhu. assert (HA4u': get_assigned_value (remove_assignment_for A4 u) u = None). { apply remove_assignment_None. }
                   rewrite HA4u'. rewrite eqb_refl. split. reflexivity. reflexivity. }

                 assert (HAh: get_assigned_value A1' h = None /\ get_assigned_value A2' h = None /\ get_assigned_value A3' h = None).
                 { repeat split.
                   { apply A4_nodes_not_in_A1 in HhA4.
                     destruct HA1' as [_ HA1']. apply assigned_is_false. specialize HA1' with (u := h). apply HA1'. apply member_In_equiv_F. intros F.
                     exfalso. apply HhA4. apply F. }
                   { apply A4_nodes_not_in_A2 in HhA4. destruct HA2' as [_ HA2']. apply assigned_is_false.
                     specialize HA2' with (u := h). apply HA2'. apply member_In_equiv_F. apply HhA4. }
                   { apply A4_nodes_not_in_A3 in HhA4. apply assigned_is_false. unfold is_exact_assignment_for in HA3'. destruct HA3' as [_ HA3']. apply HA3'.
                     simpl in HhA4. apply member_In_equiv_F. apply HhA4. } }

                 assert (Hhu: find_value G g h U [] = find_value G g u U []).
                 { assert (Hx': exists (P: assignments X), find_values G g (find_parents h G) U [] = Some P
                        /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents h G)
                        /\ exists (unobs: X), get_assigned_value U h = Some unobs
                        /\ find_value G g h U [] = Some (g h (unobs, pa))).
                   { apply find_value_evaluates_to_g. split.
                     - destruct HG as [_ HG]. apply HG.
                     - split. apply HU. apply A1_nodes_in_graph with (u := u) (v := v) (l := h :: t). apply HG. apply paths_start_to_end_correct in Hp. apply Hp.
                       unfold nodes. rewrite HA1ind. left. reflexivity. }
                   destruct Hx' as [Px [HPx [pax [Hparx [unobsx [HxU Hx]]]]]]. rewrite Hx. destruct Hu as [_ Hu]. rewrite Hu.
                   rewrite Heqg. unfold g_path'. simpl. rewrite eqb_refl. simpl.
                   destruct HAh as [HA1h [HA2h HA3h]]. unfold f_parent_i. simpl. f_equal.
                   apply Hi'' with (g := g) (a := u) (w := h) (P := Px) (U := U). (* TODO probably a few places to use Hi'' *)
                   + apply Hnodeu.
                   + apply HU.
                   + apply index_correct. symmetry. apply Hi.
                   + split. apply Hparx. apply HPx.
                   + apply Hu. }

                 assert (Hh: find_value G g h U [] = find_value G g' h U []).
                 { assert (Hx': exists (P: assignments X), find_values G g (find_parents h G) U [] = Some P
                        /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents h G)
                        /\ exists (unobs: X), get_assigned_value U h = Some unobs
                        /\ find_value G g h U [] = Some (g h (unobs, pa))).
                   { apply find_value_evaluates_to_g. split.
                     - destruct HG as [_ HG]. apply HG.
                     - split. apply HU. apply A1_nodes_in_graph with (u := u) (v := v) (l := h :: t). apply HG. apply paths_start_to_end_correct in Hp. apply Hp.
                       unfold nodes. rewrite HA1ind. left. reflexivity. }
                   destruct Hx' as [Px [HPx [pax [Hparx [unobsx [HxU Hx]]]]]]. 
                   assert (Hx': exists (P: assignments X), find_values G g' (find_parents h G) U [] = Some P
                        /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents h G)
                        /\ exists (unobs: X), get_assigned_value U h = Some unobs
                        /\ find_value G g' h U [] = Some (g' h (unobs, pa))).
                   { apply find_value_evaluates_to_g. split.
                     - destruct HG as [_ HG]. apply HG.
                     - split. apply HU. apply A1_nodes_in_graph with (u := u) (v := v) (l := h :: t). apply HG. apply paths_start_to_end_correct in Hp. apply Hp.
                       unfold nodes. rewrite HA1ind. left. reflexivity. }
                   destruct Hx' as [Px' [HPx' [pax' [Hparx' [unobsx' [HxU' Hx']]]]]]. rewrite Hx'.
                   rewrite Heqg'. unfold g_path'. simpl. rewrite eqb_refl. simpl.

                   destruct HAh as [HA1h [HA2h HA3h]]. rewrite HA1h. rewrite HA2h. rewrite HA3h. unfold f_constant. f_equal. rewrite Hhu. apply Hu. }

                 assert (Hf: forall (w: node), node_in_graph w G = true -> find_value G g w U [] = find_value G g' w U []).
                 { intros w Hw.
                   (* induction on index in topo sort. *)

                   unfold generic_graph_and_type_properties_hold in HG. destruct HG as [_ HG]. apply topo_sort_exists_for_acyclic in HG as Hts.
                   destruct Hts as [ts Hts].
                   apply topo_sort_contains_nodes with (u := w) in Hts as Hnode. apply Hnode in Hw as Hiw. clear Hnode. apply index_exists in Hiw. destruct Hiw as [j Hiw].
                   assert (Hj: exists (iw: nat), Some iw = index ts w /\ iw <= j). { exists j. split. apply Hiw. lia. } clear Hiw.

                   generalize dependent w. induction j as [| j' IH].
                   - intros w Hw Hiw.
                     destruct (w =? h) as [|] eqn:Hwh. apply eqb_eq in Hwh. rewrite Hwh. apply Hh.
                     destruct (u =? w) as [|] eqn:Huw. apply eqb_eq in Huw. rewrite <- Huw. apply Hu.

                     assert (Hw': exists (P: assignments X), find_values G g (find_parents w G) U [] = Some P
                        /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                        /\ exists (unobs: X), get_assigned_value U w = Some unobs
                        /\ find_value G g w U [] = Some (g w (unobs, pa))).
                     { apply find_value_evaluates_to_g. split.
                       - apply HG.
                       - split. apply HU. apply Hw. }
                     destruct Hw' as [P [HP [pa [Hpar [unobs [HwU Hw']]]]]].
                     rewrite Hw'. rewrite Heqg. unfold g_path'.

                     assert (Hw'': exists (P: assignments X), find_values G g' (find_parents w G) U [] = Some P
                          /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                          /\ exists (unobs: X), get_assigned_value U w = Some unobs
                          /\ find_value G g' w U [] = Some (g' w (unobs, pa))).
                     { apply find_value_evaluates_to_g. split.
                       - apply HG.
                       - split. apply HU. apply Hw. }
                     destruct Hw'' as [P' [HP' [pa' [Hpar' [unobs' [HwU' Hw'']]]]]].
                     rewrite Hw''. rewrite Heqg'. unfold g_path'. simpl.

                     assert (Hwp: find_parents w G = []).
                     { destruct Hiw as [iw Hiw]. assert (Hiw0: iw = 0). { lia. } destruct Hiw as [Hiw _].
                       destruct ts as [| hts tts]. simpl in Hiw. discriminate Hiw.
                       rewrite Hiw0 in Hiw. simpl in Hiw. destruct (hts =? w) as [|] eqn:Hhts.
                       - apply topo_sort_first_node_no_parents with (ts := tts). split. apply HG. apply eqb_eq in Hhts. rewrite <- Hhts. apply Hts.
                       - destruct (index tts w) as [it|]. discriminate Hiw. discriminate Hiw. }
                     rewrite eqb_sym in Hwh. rewrite Hwh. rewrite Huw. rewrite remove_assignment_preserves_other_nodes.
                     + rewrite HwU in HwU'. inversion HwU'. rewrite Hwp in *. simpl in HP. inversion HP. rewrite <- H3 in Hpar.
                       simpl in Hpar. inversion Hpar. simpl in HP'. inversion HP'. rewrite <- H5 in Hpar'. simpl in Hpar'. inversion Hpar'.
                       reflexivity.
                     + apply Huw.
                   - intros w Hw Hiw.
                     destruct (w =? h) as [|] eqn:Hwh. apply eqb_eq in Hwh. rewrite Hwh. apply Hh.
                     destruct (u =? w) as [|] eqn:Huw. apply eqb_eq in Huw. rewrite <- Huw. apply Hu.

                     assert (Hw': exists (P: assignments X), find_values G g (find_parents w G) U [] = Some P
                        /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                        /\ exists (unobs: X), get_assigned_value U w = Some unobs
                        /\ find_value G g w U [] = Some (g w (unobs, pa))).
                     { apply find_value_evaluates_to_g. split.
                       - apply HG.
                       - split. apply HU. apply Hw. }
                     destruct Hw' as [P [HP [pa [Hpar [unobs [HwU Hw']]]]]].
                     rewrite Hw'. rewrite Heqg. unfold g_path'.

                     assert (Hw'': exists (P: assignments X), find_values G g' (find_parents w G) U [] = Some P
                          /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                          /\ exists (unobs: X), get_assigned_value U w = Some unobs
                          /\ find_value G g' w U [] = Some (g' w (unobs, pa))).
                     { apply find_value_evaluates_to_g. split.
                       - apply HG.
                       - split. apply HU. apply Hw. }
                     destruct Hw'' as [P' [HP' [pa' [Hpar' [unobs' [HwU' Hw'']]]]]].
                     rewrite Hw''. rewrite Heqg'. unfold g_path'. simpl. rewrite eqb_sym in Hwh. rewrite Hwh.
                     rewrite remove_assignment_preserves_other_nodes.
                     + rewrite HwU in HwU'. inversion HwU'.
                       assert (HPP': Some P' = Some P).
                       { rewrite <- HP. rewrite <- HP'. apply find_values_same_if_parents_same. intros pw Hpw.
                         assert (Hnodepw: node_in_graph pw G = true). { apply parents_in_graph with (u := w). apply HG. apply Hpw. }
                         apply IH.
                         - apply Hnodepw.
                         - assert (Hlem: exists (ip iw': nat), Some ip = index ts pw /\ Some iw' = index ts w /\ ip < iw').
                           { apply topo_sort_parents with (G := G). split. apply HG. apply Hts. apply Hpw. }
                           destruct Hlem as [ip [iw' [Hip [Hiw' Hipiw]]]]. exists ip. split.
                           + apply Hip.
                           + destruct Hiw as [iw [Hiw Hiwj]]. rewrite <- Hiw in Hiw'. inversion Hiw'. lia. }

                       inversion HPP'. rewrite H3 in Hpar'. rewrite <- Hpar in Hpar'. inversion Hpar'. rewrite Huw. reflexivity.
                     + apply Huw. }

                 split.

                 { destruct H1 as [H1 _].
                   intros w Hw.
                   assert (Hnodew: node_in_graph w G = true).
                   { destruct Hw as [_ Hw].
                     assert (Hcolw: is_assigned A2' w = true /\ is_exact_assignment_for A2' (get_A2_binded_nodes_in_g_path G (h, v, t))). { split. apply Hw. apply HA2'. }
                     apply assigned_true_then_in_list in Hcolw. unfold get_A2_binded_nodes_in_g_path in Hcolw. apply colliders_vs_edges_in_path in Hcolw.
                     destruct Hcolw as [w1 [w2 Hcolw]]. destruct Hcolw as [_ [Hcolw _]]. unfold is_edge in Hcolw. destruct G as [V E]. apply split_and_true in Hcolw.
                     destruct Hcolw as [Hcolw _]. apply split_and_true in Hcolw. simpl. apply Hcolw. }

                   rewrite Hf. apply H1. apply Hw. apply Hnodew. }

                 { intros Hcond. clear HA12. destruct H1 as [_ HA12].
                   unfold unobs_conditions_on_Z in Hcond.
                   assert (Hcond': unobs_conditions_on_Z G g' U AZ Z).
                   { unfold unobs_conditions_on_Z. intros w Hw.
                     rewrite <- Hf. apply Hcond. apply Hw. apply Hw. }

                   apply HA12 in Hcond'. destruct Hcond' as [x Hcond']. exists x. intros w [Hwp Hwcol].
                   assert (Hnodew: node_in_graph w G = true).
                   { apply nodes_in_graph_in_V with (p := (u, v, h :: t)). split.
                     - apply Hwp.
                     - apply paths_start_to_end_correct in Hp. apply Hp. }

                   unfold node_in_path in Hwp. simpl in Hwp. apply split_orb_true in Hwp. destruct Hwp as [Hwp | Hwp].
                   - assert (Hhx: find_value G g' h U [] = Some x).
                     { apply Hcond'. split.
                       * unfold node_in_path. simpl. rewrite eqb_refl. reflexivity.
                       * intros Hmem. apply colliders_vs_edges_in_path in Hmem. destruct Hmem as [y [z [Hsub _]]].
                         assert (Hacyc: acyclic_path_2 (h, v, t)).
                         { apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity.
                           apply paths_start_to_end_correct in Hp. apply Hp. }
                         unfold acyclic_path_2 in Hacyc.
                         assert (Hmem: In h (t ++ [v])). { apply middle_elt_of_sublist_not_first_elt_gen with (A := [h; z]) (a := y) (h := h). split. apply Hsub. left. reflexivity. }
                         apply membership_append_or in Hmem. destruct Hmem as [Hmem | [Hmem | F]]. destruct Hacyc as [_ [Hacyc _]]. apply Hacyc. apply Hmem.
                         destruct Hacyc as [Hacyc _]. apply Hacyc. rewrite Hmem. reflexivity. apply F. }

                     specialize Hcond' with (w := w). apply split_orb_true in Hwp. destruct Hwp as [Hwp | Hwp].
                     + apply eqb_eq in Hwp. rewrite Hwp. rewrite <- Hhu. rewrite Hh. apply Hhx.
                     + rewrite Hf. apply Hcond'. split.
                       * unfold node_in_path. simpl. rewrite Hwp. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
                       * unfold get_A2_binded_nodes_in_g_path in HA2ind. intros Hmem. apply Hwcol. unfold node in *. unfold nodes in *. unfold find_colliders_in_path. unfold find_colliders_in_path in HA2ind.
                         rewrite HA2ind. unfold find_colliders_in_path in Hmem. apply Hmem.
                       * apply Hnodew.
                   - rewrite Hf. apply Hcond'. split.
                     + unfold node_in_path. simpl. destruct (w =? h) as [|] eqn:Hwh. reflexivity. rewrite eqb_sym in Hwh. rewrite Hwh in Hwp. rewrite Hwp.
                       simpl. rewrite orb_comm. reflexivity.
                     + unfold get_A2_binded_nodes_in_g_path in HA2ind. intros Hmem. apply Hwcol. unfold node in *. unfold nodes in *. unfold find_colliders_in_path. unfold find_colliders_in_path in HA2ind.
                       rewrite HA2ind. unfold find_colliders_in_path in Hmem. apply Hmem.
                     + apply Hnodew. } }

               { destruct HA4ind as [HA4ind1 HA4ind2]. unfold nodes. rewrite HA4ind2. apply remove_assignment_exact_cat.
                 - rewrite <- HA4ind1. apply HA4.
                 - intros F. assert (HuA4': In u (get_A4_binded_nodes_in_g_path G (h, v, t))).
                   { rewrite HA4ind2. right. apply F. }
                   apply A4_nodes_in_path in HuA4'. apply node_in_subpath_not_acyclic with (u := u) (v := v) (h := h) (t := t). apply HuA4'.
                   apply paths_start_to_end_correct in Hp. apply Hp. }

        + (* since arrow out of h is ->, h cannot be a collider, so h not in Z *)
          intros HhZ. unfold d_connected_2 in Hconn.
          assert (Hh: In h (find_mediators_in_path (u, v, h :: t) G) \/ In h (find_confounders_in_path (u, v, h :: t) G)).
          { destruct (path_out_of_start (u, v, h :: t) G) as [|] eqn:Hout.
            - simpl in Hout. left. apply mediators_vs_edges_in_path. destruct t as [| ht tt].
              + exists u. exists v. repeat split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                apply Hout. simpl in Houth. apply Houth.
              + exists u. exists ht. repeat split. simpl. repeat rewrite eqb_refl. reflexivity. left. split.
                apply Hout. simpl in Houth. apply Houth.
            - simpl in Hout. assert (Hedge: is_edge (h, u) G = true).
              { apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. simpl in Hp. rewrite Hout in Hp. simpl in Hp.
                destruct G as [V E]. apply split_and_true in Hp. apply Hp. }
              right. apply confounders_vs_edges_in_path. destruct t as [| ht tt].
              + exists u. exists v. repeat split. simpl. repeat rewrite eqb_refl. reflexivity.
                apply Hedge. simpl in Houth. apply Houth.
              + exists u. exists ht. repeat split. simpl. repeat rewrite eqb_refl. reflexivity.
                apply Hedge. simpl in Houth. apply Houth. }
          destruct Hh as [Hh | Hh].
          * destruct Hconn as [Hmed _]. apply no_overlap_non_member with (x := h) in Hmed.
            -- apply Hmed. apply HhZ.
            -- apply Hh.
          * destruct Hconn as [_ [Hcon _]]. apply no_overlap_non_member with (x := h) in Hcon.
            -- apply Hcon. apply HhZ.
            -- apply Hh.
        + apply subpath_still_d_connected with (u := u). apply Hconn.
        + destruct Hl as [l' [Hl' Hsub]]. exists (h :: t ++ [v]). split. reflexivity.
          apply end_of_sublist_still_sublist_gen with (a := u) (h := hn). rewrite Hl' in Hsub. apply Hsub. }

    { destruct (path_into_start (u, v, h :: t) G) as [|] eqn:Hin.
      - (* u <- h <- ...t... <-> v ANNA *)
        specialize IH with (u := h) (l := t).
        assert (Hp': In (h, v, t) (find_all_paths_from_start_to_end h v G)).
        { apply paths_start_to_end_correct in Hp. apply paths_start_to_end_correct. split.
          - apply is_path_in_graph_induction with (u := u). apply Hp.
          - split. apply path_start_end_refl. apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity. apply Hp. }
        pose proof Hp' as Hpind. apply IH in Hp'. clear IH.

        + destruct Hp' as [A1' [A2' [A3' HA12]]]. destruct HA12 as [HA1' [HA1'' [HA2' [HA2'' [HA3' HA12]]]]].
          assert (Hi: exists i: nat, index (find_parents u G) h = Some i).
          { assert (Hh: In h (find_parents u G)).
            { simpl in Hin. apply edge_from_parent_to_child. unfold is_edge in Hin. destruct G as [V E]. simpl. apply split_and_true in Hin. apply Hin. }
            apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
          destruct Hi as [i Hi].
          assert (Hnodeu: node_in_graph u G = true).
          { apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. simpl in Hp. apply is_edge_then_node_in_graph with (v := h). destruct G as [V E].
            apply split_and_true in Hp. destruct Hp as [Hp _]. apply split_orb_true. apply Hp. }

          assert (HA1ind: get_A1_binded_nodes_in_g_path G (u, v, h :: t) = u :: get_A1_binded_nodes_in_g_path G (h, v, t)).
          { apply A1_induction_into_start.
            - split.
              ** apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
              ** destruct HG as [_ [_ HG]]. apply HG.
            - apply Hin. }
          assert (HA2ind: get_A2_binded_nodes_in_g_path G (u, v, h :: t) = get_A2_binded_nodes_in_g_path G (h, v, t)).
          { apply A2_induction_case.
            - destruct HG as [_ [_ HG]]. apply HG.
            - left. apply Hin. }
          assert (HindA2: is_exact_assignment_for A2' (get_A2_binded_nodes_in_g_path G (u, v, h :: t)) /\ A2_nodes_colliders_in_graph G (u, v, h :: t) A2').
          { repeat split.
            -- unfold nodes. rewrite HA2ind. unfold is_exact_assignment_for in HA2'. destruct HA2' as [HA2' _]. apply HA2'.
            -- (* since h is not a collider, nothing changes from induction case *)
               unfold nodes. rewrite HA2ind. unfold is_exact_assignment_for in HA2'. destruct HA2' as [_ HA2']. apply HA2'.
            -- unfold A2_nodes_colliders_in_graph. intros c i' j' x y Hc. unfold A2_nodes_colliders_in_graph in HA2''.
               specialize HA2'' with (c := c) (i := i') (j := j') (x := x) (y := y). apply HA2'' in Hc. destruct Hc as [a [b Hc]].
               exists a. exists b. repeat split.
               ++ apply Hc.
               ++ apply Hc.
               ++ destruct Hc as [_ [_ [Hc _]]]. apply sublist_breaks_down_list in Hc. simpl in Hc. destruct Hc as [l2 [l3 Hc]].
                  apply sublist_breaks_down_list. exists (u :: l2). exists l3. simpl. rewrite Hc. reflexivity.
               ++ apply Hc. }
          assert (HA4ind: get_A4_binded_nodes_in_g_path G (u, v, h :: t) = get_A4_binded_nodes_in_g_path G (h, v, t)).
          { apply A4_induction_case.
            - split.
              ** apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. apply Hp.
              ** destruct HG as [_ [_ HG]]. apply HG.
            - apply Hin. }

          exists ((u, i) :: A1'). exists A2'. exists A3'. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split.
          repeat split.
          * (* since arrow into u, u is in A1 *)
            unfold nodes. rewrite HA1ind. simpl. rewrite eqb_refl. simpl. apply is_assignment_for_cat.
            unfold is_exact_assignment_for in HA1'. destruct HA1' as [HA1' _]. apply HA1'.
          * intros u' Hmemu'. unfold is_exact_assignment_for in HA1'. destruct HA1' as [_ HA1']. simpl.
            assert (Hmemu: In u (get_A1_binded_nodes_in_g_path G (u, v, h :: t))).
            { rewrite HA1ind. left. reflexivity. }
            destruct (u' =? u) as [|] eqn:Huu'.
            ++ apply eqb_eq in Huu'. apply member_In_equiv in Hmemu. rewrite Huu' in Hmemu'. unfold nodes in Hmemu'. rewrite Hmemu in Hmemu'. discriminate Hmemu'.
            ++ simpl. apply HA1'. unfold nodes in Hmemu'. rewrite HA1ind in Hmemu'. unfold member in Hmemu'. rewrite eqb_sym in Hmemu'. rewrite Huu' in Hmemu'. apply Hmemu'.
          * unfold A1_nodes_binded_to_parent_in_path. intros c i' Hmi'. simpl in Hmi'. destruct Hmi' as [Hmi' | Hmi'].
            ++ inversion Hmi'. rewrite <- H1 in *. rewrite <- H2 in *. exists h. repeat split.
               ** apply index_correct. symmetry. apply Hi.
               ** right. simpl. repeat rewrite eqb_refl. reflexivity.
            ++ unfold A1_nodes_binded_to_parent_in_path in HA1''. specialize HA1'' with (m := c) (i := i'). apply HA1'' in Hmi'.
               destruct Hmi' as [a [Ha Hsub]]. exists a. split.
               ** apply Ha.
               ** destruct Hsub as [Hsub | Hsub].
                  --- left. simpl. simpl in Hsub. rewrite Hsub. rewrite orb_comm. reflexivity.
                  --- right. simpl. simpl in Hsub. rewrite Hsub. rewrite orb_comm. reflexivity.
          * apply HindA2.
          * apply HindA2.
          * apply HindA2.
          * admit.
          * admit.
          * intros A4 A5 default U HA4 HU. pose proof HU as H1.

            specialize HA12 with (A4 := A4) (default := default) (U := U) (A5 := (u, f_parent_i X i) :: A5).
            remember (g_path' X A1' A2' A3' A4 ((u, f_parent_i X i) :: A5) default) as g. remember (g_path' X ((u, i) :: A1') A2' A3' A4 A5 default) as g'.
            apply HA12 in H1.

            2: { unfold nodes. rewrite <- HA4ind. apply HA4. }

            assert (Hg: g = g').
            { apply functional_extensionality. intros x. rewrite Heqg. rewrite Heqg'. unfold g_path'. simpl.
              destruct (u =? x) as [|] eqn:Hux.
               - apply eqb_eq in Hux. rewrite <- Hux in *. assert (Humem: node_in_path u (h, v, t) = false).
                 { apply paths_start_to_end_correct in Hp. destruct Hp as [_ [_ Hp]]. unfold acyclic_path_2 in Hp.
                   unfold node_in_path. simpl. destruct (u =? h) as [|] eqn:Huh.
                   - exfalso. destruct Hp as [_ [Hp _]]. apply Hp. left. apply eqb_eq in Huh. rewrite Huh. reflexivity.
                   - simpl. destruct (u =? v) as [|] eqn:Huv.
                     + exfalso. destruct Hp as [Hp _]. apply Hp. apply eqb_eq in Huv. apply Huv.
                     + simpl. destruct Hp as [_ [Hp _]]. apply member_In_equiv_F. intros F. apply Hp. right. apply F. }
                 assert (HxA1': get_assigned_value A1' u = None).
                 { destruct (is_assigned A1' u) as [|] eqn:HxA1'.
                   - assert (Hmem: node_in_path u (h, v, t) = true).
                     { apply A1_nodes_in_path with (G := G). apply assigned_true_then_in_list with (A := A1'). split. apply HxA1'. apply HA1'. }
                     rewrite Hmem in Humem. discriminate Humem.
                   - apply assigned_is_false. apply HxA1'. }
                 rewrite HxA1'.
                 assert (HxA2': get_assigned_value A2' u = None).
                 { destruct (is_assigned A2' u) as [|] eqn:HxA2'.
                   - assert (Hcol: In u (get_A2_binded_nodes_in_g_path G (h, v, t))).
                     { apply assigned_true_then_in_list with (A := A2'). split. apply HxA2'. apply HA2'. }
                     unfold get_A2_binded_nodes_in_g_path in Hcol. apply colliders_vs_edges_in_path in Hcol. destruct Hcol as [y [z [Hsub _]]].
                     assert (Hmem: In u (h :: t ++ [v])). { apply sublist_member with (l1 := [y; u; z]). split. right. left. reflexivity. apply Hsub. }
                     unfold node_in_path in Humem. simpl in Humem. destruct Hmem as [Hmem | Hmem]. rewrite Hmem in Humem. rewrite eqb_refl in Humem. discriminate Humem.
                     apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem]. apply member_In_equiv in Hmem. rewrite Hmem in Humem. rewrite orb_comm in Humem. discriminate Humem.
                     destruct Hmem as [Hmem | Hmem]. rewrite Hmem in Humem. rewrite eqb_refl in Humem. rewrite <- orb_assoc in Humem. rewrite orb_comm in Humem. discriminate Humem. exfalso. apply Hmem.
                   - apply assigned_is_false. apply HxA2'. }
                 rewrite HxA2'.
                 assert (HxA3': get_assigned_value A3' u = None). { admit. }
                 rewrite HxA3'.
                 assert (HxA4: get_assigned_value A4 u = None).
                 { destruct (is_assigned A4 u) as [|] eqn:HxA4.
                   - assert (Hmem: node_in_path u (h, v, t) = true).
                     { apply A4_nodes_in_path with (G := G). apply assigned_true_then_in_list with (A := A4). split. apply HxA4. unfold nodes. rewrite <- HA4ind.
                       apply HA4. }
                     rewrite Hmem in Humem. discriminate Humem.
                   - apply assigned_is_false. apply HxA4. }
                 rewrite HxA4. reflexivity.
               - reflexivity. }

            split.
            { intros w Hw. destruct H1 as [H1 _]. rewrite <- Hg. apply H1. apply Hw. }

            { intros Hcond. rewrite <- Hg in Hcond. destruct H1 as [_ H1]. apply H1 in Hcond. destruct Hcond as [x Hcond]. exists x.
              intros w [Hwp Hwcol]. destruct (u =? w) as [|] eqn:Huw.
              - apply eqb_eq in Huw.
                assert (Hh: find_value G g h U [] = Some x).
                { apply Hcond. split.
                  * unfold node_in_path. simpl. rewrite eqb_refl. reflexivity.
                  * intros Hmem. apply colliders_vs_edges_in_path in Hmem. destruct Hmem as [y [z [Hsub _]]].
                    assert (Hacyc: acyclic_path_2 (h, v, t)).
                    { apply subpath_still_acyclic with (w := u) (l1 := []) (l3 := h :: t). split. reflexivity.
                      apply paths_start_to_end_correct in Hp. apply Hp. }
                    unfold acyclic_path_2 in Hacyc.
                    assert (Hmem: In h (t ++ [v])). { apply middle_elt_of_sublist_not_first_elt_gen with (A := [h; z]) (a := y) (h := h). split. apply Hsub. left. reflexivity. }
                    apply membership_append_or in Hmem. destruct Hmem as [Hmem | [Hmem | F]]. destruct Hacyc as [_ [Hacyc _]]. apply Hacyc. apply Hmem.
                    destruct Hacyc as [Hacyc _]. apply Hacyc. rewrite Hmem. reflexivity. apply F. }

                assert (Hw: exists (P: assignments X), find_values G g (find_parents w G) U [] = Some P
                              /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents w G)
                              /\ exists (unobs: X), get_assigned_value U w = Some unobs
                              /\ find_value G g w U [] = Some (g w (unobs, pa))).
                { apply find_value_evaluates_to_g. split.
                  - destruct HG as [_ HG]. apply HG.
                  - split. apply HU. unfold path_into_start in Hin. apply is_edge_then_node_in_graph with (v := h). right. rewrite <- Huw. apply Hin. }
                destruct Hw as [Pw [HPw [paw [Hpaw [unobsw [HwU Hw]]]]]]. rewrite <- Hg. rewrite Hw. rewrite <- Huw in *.
                rewrite Hg. rewrite Heqg'. f_equal. unfold g_path'. simpl. rewrite eqb_refl. unfold f_parent_i. simpl.

                assert (HPwh: get_assigned_value Pw h = Some x).
                { apply find_values_get_assigned with (G := G) (g := g) (P := find_parents u G) (U := U) (A := []). repeat split.
                  - apply HPw.
                  - apply index_exists. exists i. symmetry. apply Hi.
                  - apply Hh. }
                assert (Hiw: nth_error paw i = get_assigned_value Pw h).
                { rewrite HPwh. apply parent_assignments_preserves_index with (P := Pw) (V := find_parents u G) (m := h). repeat split.
                  - symmetry. apply Hpaw.
                  - apply Hi.
                  - apply HPwh. }
                unfold nth_default. rewrite Hiw. rewrite HPwh. reflexivity.

              - rewrite <- Hg. apply Hcond. split.
                + unfold node_in_path. simpl. destruct (w =? h) as [|] eqn:Hwh. reflexivity. rewrite eqb_sym in Hwh. unfold node_in_path in Hwp. simpl in Hwp. rewrite eqb_sym in Huw. rewrite Huw in Hwp.
                  simpl in Hwp. rewrite Hwh in Hwp. simpl. apply Hwp.
                + unfold get_A2_binded_nodes_in_g_path in HA2ind. intros Hmem. apply Hwcol. unfold node in *. unfold nodes in *. unfold find_colliders_in_path. unfold find_colliders_in_path in HA2ind.
                  rewrite HA2ind. unfold find_colliders_in_path in Hmem. apply Hmem. }
        + (* path is u <- h, so h cannot be a collider. Thus, h not in Z *)
          intros HhZ. unfold d_connected_2 in Hconn.
          assert (Hh: In h (find_mediators_in_path (u, v, h :: t) G)).
          { apply mediators_vs_edges_in_path. destruct t as [| ht tt].
            - exists u. exists v. repeat split. simpl. repeat rewrite eqb_refl. reflexivity.
              simpl in Hin. simpl in Houth. right. split. apply Hin. apply paths_start_to_end_correct in Hpind. destruct Hpind as [Hpind _].
              simpl in Hpind. rewrite Houth  in Hpind. simpl in Hpind. destruct G as [V E]. rewrite andb_comm in Hpind. simpl in Hpind. apply Hpind.
            - exists u. exists ht. repeat split. simpl. repeat rewrite eqb_refl. reflexivity.
              simpl in Hin. simpl in Houth. right. split. apply Hin. apply paths_start_to_end_correct in Hpind. destruct Hpind as [Hpind _].
              simpl in Hpind. rewrite Houth  in Hpind. simpl in Hpind. destruct G as [V E]. apply split_and_true in Hpind. apply Hpind. }
          destruct Hconn as [Hmed _]. apply no_overlap_non_member with (x := h) in Hmed.
          * apply Hmed. apply HhZ.
          * apply Hh.
        + apply subpath_still_d_connected with (u := u). apply Hconn.
        + exists (h :: t ++ [v]). split. reflexivity. apply end_of_sublist_still_sublist_gen with (a := u) (h := hn).
          destruct Hl as [l' [Hl' Hsub]]. rewrite Hl' in Hsub. apply Hsub.
      - (* u -> h <- ...t... <-> v *)
        destruct t as [| h' t'].
        + (* u -> h <- v *)
          assert (Huh: is_edge (u, h) G = true).
          { simpl in Hin. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. simpl in Hp. rewrite Hin in Hp. rewrite orb_comm in Hp. simpl in Hp.
            destruct G as [V E]. apply split_and_true in Hp. apply Hp. }
          assert (Hhv: is_edge (v, h) G = true).
          { simpl in Houth. apply paths_start_to_end_correct in Hp. destruct Hp as [Hp _]. simpl in Hp. rewrite Houth in Hp. simpl in Hp.
            destruct G as [V E]. apply split_and_true in Hp. destruct Hp as [_ Hp]. rewrite andb_comm in Hp. simpl in Hp. apply Hp. }

          exists [].
          assert (Hi: exists i: nat, index (find_parents h G) u = Some i).
          { assert (Hh: In u (find_parents h G)).
            { apply edge_from_parent_to_child. unfold is_edge in Huh. destruct G as [V E]. simpl. apply split_and_true in Huh. apply Huh. }
            apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
          destruct Hi as [iu Hiu].
          assert (Hi: exists i: nat, index (find_parents h G) v = Some i).
          { assert (Hh: In v (find_parents h G)).
            { apply edge_from_parent_to_child. unfold is_edge in Hhv. destruct G as [V E]. simpl. apply split_and_true in Hhv. apply Hhv. }
            apply index_exists in Hh. destruct Hh as [i Hi]. exists i. rewrite Hi. reflexivity. }
          destruct Hi as [iv Hiv].
          assert (Hd: exists (d: node), In d (find_descendants h G) /\ In d Z).
          { unfold d_connected_2 in Hconn. destruct Hconn as [_ [_ Hconn]]. unfold all_colliders_have_descendant_conditioned_on in Hconn.
            apply forallb_true_iff_mem with (x := h) in Hconn.
            - unfold some_descendant_in_Z_bool in Hconn. apply overlap_has_member_in_common in Hconn. destruct Hconn as [d Hd]. exists d. apply Hd.
            - simpl. unfold is_collider_bool. rewrite Huh. rewrite Hhv. simpl. left. reflexivity. }
          destruct Hd as [d [Hd HdZ]].
          assert (HdAZ: exists (xd: X), get_assigned_value AZ d = Some xd).
          { apply assigned_has_value with (L := Z). split. apply HdZ. apply HAZ. }
          destruct HdAZ as [xd HdAZ].
          assert (Hxd: exists (y: X), y <> xd).
          { destruct HG as [HG _]. destruct HG as [xX [yX Hxy]]. destruct (eqb xX xd) as [|] eqn:Hxd.
            - exists yX. apply eqb_eq' in Hxd. rewrite <- Hxd. intros Hxy'. apply Hxy. symmetry. apply Hxy'.
            - exists xX. intros Hxy'. rewrite Hxy' in Hxd. rewrite eqb_refl' in Hxd. discriminate Hxd. }
          destruct Hxd as [y Hxd].
          exists [(h, (iu, iv, xd, y))].

          (* need to make A3 based on path from h -> ... -> d *)
          apply find_descendants_correct in Hd. destruct Hd as [Hd | Hd].
          { exists [].

            rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. rewrite <- and_assoc. split.
            repeat split.
            * simpl. rewrite Hhv. simpl in Hin. rewrite Hin. unfold is_mediator_bool. simpl in Houth. rewrite Houth. rewrite Hin. rewrite andb_comm. simpl.
              rewrite andb_comm. simpl. reflexivity.
            * unfold A1_nodes_binded_to_parent_in_path. intros m i F. exfalso. apply F.
            * simpl. unfold is_collider_bool. rewrite Huh. rewrite Hhv. simpl. rewrite eqb_refl. simpl. reflexivity.
            * intros w Hw. simpl. rewrite orb_comm. simpl. simpl in Hw. unfold is_collider_bool in Hw. rewrite Huh in Hw. rewrite Hhv in Hw. simpl in Hw.
              destruct (h =? w) as [|] eqn:Hhw. discriminate Hw. rewrite eqb_sym. apply Hhw.
            * unfold A2_nodes_colliders_in_graph. intros c i j x' y' Hc. exists u. exists v. simpl in Hc. inversion Hc. inversion H0. repeat split.
              -- rewrite <- H2. rewrite <- H3. apply index_correct. symmetry. apply Hiu.
              -- rewrite <- H2. rewrite <- H4. apply index_correct. symmetry. apply Hiv.
              -- simpl. repeat rewrite eqb_refl. reflexivity.
              -- unfold is_collider_bool. rewrite <- H2. rewrite Huh. rewrite Hhv. reflexivity.
              -- exfalso. apply H0.
            * admit.
            * intros A4 A5 def U HA4 HU. remember (g_path' X [] [(h, (iu, iv, xd, y))] [] A4 A5 def) as g. split.
              -- intros w [HwZ Hhw]. simpl in Hhw. rewrite orb_comm in Hhw. simpl in Hhw.
                 admit.
              -- intros Hcond.
                 assert (Hu: exists (xu: X), find_value G g u U [] = Some xu). { admit. } destruct Hu as [xu Hxu].
                 exists xu. intros w [Hwp Hwcol]. unfold node_in_path in Hwp. simpl in Hwp. apply split_orb_true in Hwp. rewrite split_orb_true in Hwp. destruct Hwp as [[Hwp | Hwp] | Hwp].
                 ++ apply eqb_eq in Hwp. rewrite Hwp. apply Hxu.
                 ++ apply eqb_eq in Hwp. rewrite Hwp. admit.
                 ++ destruct (h =? w) as [|] eqn:Hhw. exfalso. apply Hwcol. simpl. unfold is_collider_bool. rewrite Huh. rewrite Hhv. simpl. left. apply eqb_eq. apply Hhw.
                    discriminate Hwp. }

          { destruct Hd as [U [HdirU Huhd]]. admit. }
        + specialize IH with (u := h') (l := t'). admit. }
Admitted.





(* (* using g_path and specific values for A1, A2, and A3, for a d-connected path betw u and v, provide a graphfun
   that requires all non-collider node values along the path (and importantly, f(v) and f(u)), to be equal *)
Lemma path_d_connected_then_can_equate_values {X : Type} `{EqType X}: forall (G: graph) (u v: node) (p: path),
  generic_graph_and_type_properties_hold X G /\ In p (find_all_paths_from_start_to_end u v G) ->
  forall (Z: nodes), ~(In u Z) -> d_connected_2 p G Z
  -> forall (AZ: assignments X), is_assignment_for AZ Z = true
  -> exists (A1: assignments nat) (A2: assignments (nat * nat * X * X)),
     is_exact_assignment_for A1 (get_A1_binded_nodes_in_g_path G p) /\ is_exact_assignment_for A2 (get_A2_binded_nodes_in_g_path G p)
     /\ A2_nodes_colliders_in_graph G p A2
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
      * unfold A2_nodes_colliders_in_graph. intros c i' j' x y F. exfalso. apply F.
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
      * unfold A2_nodes_colliders_in_graph. intros c i' j' x y F. exfalso. apply F.
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
      + destruct Hp' as [A1' [A2' HA12]]. destruct HA12 as [HA1' [HA2' [HA2'' HA12]]].
        (* u <-> h -> ... <-> v *)
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
            - (* apply Hin. *) admit. }
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
          -- unfold A2_nodes_colliders_in_graph. intros c i' j' x y Hc. unfold A2_nodes_colliders_in_graph in HA2''.
             specialize HA2'' with (c := c) (i := i') (j := j') (x := x) (y := y). apply HA2'' in Hc. destruct Hc as [a [b Hc]].
             exists a. exists b. repeat split.
             ++ apply Hc.
             ++ apply Hc.
             ++ destruct Hc as [_ [_ [Hc _]]]. apply sublist_breaks_down_list in Hc. simpl in Hc. destruct Hc as [l2 [l3 Hc]].
                apply sublist_breaks_down_list. exists (u :: l2). exists l3. simpl. rewrite Hc. reflexivity.
             ++ apply Hc.
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
             rewrite HwU in HwU'. inversion HwU'. f_equal.
             (* since w is in A2', it is a collider. iw and jw are its two parents in the path, which are not u. thus, no change from induction *)
             assert (Hiw: nth_default unobs' pa iw = nth_default unobs' pa' iw).
             { unfold A2_nodes_colliders_in_graph in HA2''. specialize HA2'' with (c := w) (i := iw) (j := jw) (x := xw) (y := yw).
               apply get_assigned_In in Hvalw. apply HA2'' in Hvalw. destruct Hvalw as [a [b Hvalw]].
               assert (Hxa: exists (xa: X), find_value G g a U [] = Some xa).
               { apply find_value_existence. apply HG. admit. }
               destruct Hxa as [xa Hxa].
               assert (Hxa': get_assigned_value P a = Some xa).
               { apply find_values_get_assigned with (G := G) (g := g) (P := find_parents w G) (U := U) (A := []). repeat split.
                 - apply HP.
                 - destruct Hvalw as [Hvalw _]. apply nth_error_In with (n := iw). apply Hvalw.
                 - apply Hxa. }
               assert (Hiw: nth_error pa iw = get_assigned_value P a).
               { rewrite Hxa'. apply parent_assignments_preserves_index with (P := P) (V := find_parents w G) (m := a). repeat split.
                 - symmetry. apply Hpar.
                 - symmetry. apply index_correct_appears_once.
                   + apply each_parent_appears_once. apply HG. apply nth_error_In with (n := iw). apply Hvalw.
                   + apply Hvalw.
                 - apply Hxa'. }
               unfold nth_default. rewrite Hiw. rewrite Hxa'.

               assert (Hxa'': exists (xa': X), find_value G g' a U [] = Some xa').
               { apply find_value_existence. apply HG. admit. }
               destruct Hxa'' as [xa' Hxa''].
               assert (Hxa''': get_assigned_value P' a = Some xa').
               { apply find_values_get_assigned with (G := G) (g := g') (P := find_parents w G) (U := U) (A := []). repeat split.
                 - apply HP'.
                 - destruct Hvalw as [Hvalw _]. apply nth_error_In with (n := iw). apply Hvalw.
                 - apply Hxa''. }
               assert (Hiw': nth_error pa' iw = get_assigned_value P' a).
               { rewrite Hxa'''. apply parent_assignments_preserves_index with (P := P') (V := find_parents w G) (m := a). repeat split.
                 - symmetry. apply Hpar'.
                 - symmetry. apply index_correct_appears_once.
                   + apply each_parent_appears_once. apply HG. apply nth_error_In with (n := iw). apply Hvalw.
                   + apply Hvalw.
                 - apply Hxa'''. }
               unfold nth_default. rewrite Hiw'. rewrite Hxa'''. admit. }

             

(* lhs = P(Pa(w)[iw]),      rhs = P'(Pa(w)[iw])
       = fv(g, Pa(w)[iw]),      = fv(g', Pa(w)[iw])
       = fv(g', Pa(w)[iw]) unless Pa(w)[iw] = u, which would be cyclic
 *)


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
        + destruct Hp' as [A1' [A2' HA12]]. destruct HA12 as [HA1' [HA2' [HA2'' HA12]]].
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
          -- admit.
        + admit. (* h cannot be a collider, so h not in Z *)
        + unfold d_connected_2 in Hconn. unfold d_connected_2. admit.
      - (* u -> h <- ... h is a collider, have to include h in A2.
                                         destruct t: if [], manually? else, use induction step with path not incl u and h *)
        admit. }
Admitted. *)

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
  -> d_connected_2 p G Z -> ~(conditionally_independent' X G u v Z).
Proof.
  intros G u v p HGp. intros Z [HZ [HZnode [HuZ HvZ]]] Hconn. intros Hcond. unfold conditionally_independent' in Hcond.
  pose proof HGp as Hxy. unfold generic_graph_and_type_properties_hold in Hxy. destruct Hxy as [[Hxy _] _]. destruct Hxy as [x [y Hxy]].
  assert (Hpath: exists (l: nodes), p = (u, v, l)).
  { destruct p as [[u' v'] l]. destruct HGp as [_ Hp]. apply paths_start_to_end_correct in Hp. destruct Hp as [_ [Hp _]].
    apply path_start_end_equal in Hp. destruct Hp as [Huu' Hvv']. exists l. rewrite Huu'. rewrite Hvv'. reflexivity. }
  destruct Hpath as [l Hpath].
  remember (get_assignment_for Z x) as AZ. (* use arbitrary assignment of nodes in Z *)
  pose proof path_d_connected_then_can_equate_values' as Heq. specialize Heq with (G := G) (u := u) (v := v) (p := p) (Z := Z) (AZ := AZ).
  apply Heq in HGp as HA12. destruct HA12 as [A1 [A2 [A3 HA123]]]. clear Heq. destruct HA123 as [HA1 [HA1' [HA2 [HA2' [HA3 Hg]]]]].
  - (* show contradiction with Hcond by showing that v's value changes with u's *)
    (* find node w to bind to either a or b (not in A1 or A2 or Z) *)
    assert (Hanc: exists (w: node), is_assigned A1 w = false /\ is_assigned A2 w = false /\ ~(In w Z) /\ In w (find_unblocked_ancestors G u Z) /\ node_in_path w p = true).
    { apply exists_node_not_defined_in_path with (v := v). split.
      - destruct HGp as [HG _]. apply HG.
      - destruct HGp as [_ Hp]. apply Hp.
      - apply Hconn.
      - split. unfold is_exact_assignment_for in *. destruct HA1 as [_ HA1]. apply HA1. destruct HA2 as [_ HA2]. apply HA2. }
    destruct Hanc as [w Hw].
    remember (get_constant_nodefun_assignments AZ) as AZf. remember ((w, fun (x: (X * (list X))) => fst x) :: AZf) as A4.
Admitted.
(* originally path_d_connected_then_not_independent fully proved, but changed g_path *)
    (* specialize Hg with (A3 := A3) (default := f_constant X x).
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
Qed. *)

Lemma find_values_unequal {X: Type} `{EqType X}: forall (G: graph) (g: graphfun) (u: node) (U1 U2 P1 P2: assignments X),
  find_values G g (find_parents u G) U1 [] = Some P1
  -> find_values G g (find_parents u G) U2 [] = Some P2
  -> P1 <> P2
  -> exists (p: node), In p (find_parents u G) /\ find_value G g p U1 [] <> find_value G g p U2 [].
Proof.
  intros G g u U1 U2 P1 P2. intros HP1 HP2 HP.
  generalize dependent P2. generalize dependent P1. induction (find_parents u G) as [| h t IH].
  - intros P1 HP1 P2 HP2 HP. simpl in HP1. simpl in HP2. exfalso. apply HP. inversion HP1. inversion HP2. reflexivity.
  - intros P1 HP1 P2 HP2 HP. simpl in HP1. destruct (find_value G g h U1 []) as [x1|] eqn:Hx1.
    + simpl in HP2. destruct (find_value G g h U2 []) as [x2|] eqn:Hx2.
      * destruct (eqb x1 x2) as [|] eqn:Hx.
        -- destruct (find_values G g t U1 []) as [P1'|] eqn:HP1'.
           ++ destruct (find_values G g t U2 []) as [P2'|] eqn:HP2'.
              ** specialize IH with (P1 := P1') (P2 := P2').
                 assert (Hind: exists p : node,
                               In p t /\ find_value G g p U1 [] <> find_value G g p U2 []).
                 { apply IH. reflexivity. reflexivity. intros F. apply HP. inversion HP1. inversion HP2. rewrite F.
                   apply eqb_eq' in Hx. rewrite Hx. reflexivity. }
                 destruct Hind as [p [Hmem Hp]]. exists p. split. right. apply Hmem. apply Hp.
              ** discriminate HP2.
           ++ discriminate HP1.
        -- exists h. split.
           ++ left. reflexivity.
           ++ rewrite Hx1. rewrite Hx2. intros F. inversion F. rewrite H1 in Hx. rewrite eqb_refl' in Hx. discriminate Hx.
      * discriminate HP2.
    + discriminate HP1.
Qed.

Lemma nodefun_value_only_affected_by_unblocked_ancestors {X: Type} `{EqType X}: forall (G: graph) (u: node) (Z: nodes) (U1 U2 AZ: assignments X) (g: graphfun),
  G_well_formed G = true /\ contains_cycle G = false
  -> find_value G g u U1 [] <> find_value G g u U2 []
  -> is_assignment_for U1 (nodes_in_graph G) = true /\ is_assignment_for U2 (nodes_in_graph G) = true
  -> node_in_graph u G = true
  -> unobs_conditions_on_Z G g U1 AZ Z /\ unobs_conditions_on_Z G g U2 AZ Z
  -> exists (a: node), In a (find_unblocked_ancestors G u Z)
      /\ get_assigned_value U1 a <> get_assigned_value U2 a
      /\ find_value G g a U1 [] <> find_value G g a U2 [].
Proof.
  intros G u Z U1 U2 AZ g.
  intros HG Hg [HU1 HU2] HuG [HZ1 HZ2].

  assert (Hpa1: exists (P: assignments X), find_values G g (find_parents u G) U1 [] = Some P
                /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents u G)
                /\ exists (unobs: X), get_assigned_value U1 u = Some unobs
                /\ find_value G g u U1 [] = Some (g u (unobs, pa))).
  { apply find_value_evaluates_to_g. easy. }
  assert (Hpa2: exists (P: assignments X), find_values G g (find_parents u G) U2 [] = Some P
                /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents u G)
                /\ exists (unobs: X), get_assigned_value U2 u = Some unobs
                /\ find_value G g u U2 [] = Some (g u (unobs, pa))).
  { apply find_value_evaluates_to_g. easy. }
  destruct Hpa1 as [P1 [HP1 [pa1 [Hpa1 [unobs1 [Hunobs1 Hg1]]]]]].
  destruct Hpa2 as [P2 [HP2 [pa2 [Hpa2 [unobs2 [Hunobs2 Hg2]]]]]].

  destruct (eqb unobs1 unobs2) as [|] eqn:Hunobs.
  - apply eqb_eq' in Hunobs.

    assert (Hts: exists (ts: nodes), topological_sort G = Some ts).
    { apply topo_sort_exists_for_acyclic. easy. }
    destruct Hts as [ts Hts].

    assert (Hi: exists (i: nat), Some i = index ts u).
    { apply index_exists. apply topo_sort_contains_nodes with (u := u) in Hts. apply Hts. apply HuG. }
    destruct Hi as [i Hi].

    assert (Hj: exists (j: nat), Some j = index ts u /\ j <= i).
    { exists i. split. apply Hi. easy. }
    clear Hi.

    generalize dependent pa2. generalize dependent P2. generalize dependent pa1. generalize dependent P1.
    generalize dependent unobs2. generalize dependent unobs1. generalize dependent u. induction i as [| i' IH].
    + intros u Hg HuG Hj unobs1 Hunobs1 unobs2 Hunobs2 Hunobs P1 HP1 pa1 Hpa1 Hg1 P2 HP2 pa2 Hpa2 Hg2.
      destruct Hj as [j [Hi Hj0]].
      destruct j as [| j'].
      * assert (Hpar: find_parents u G = []).
        { destruct ts as [| h t].
          - simpl in Hi. discriminate Hi.
          - simpl in Hi. destruct (h =? u) as [|] eqn:Hhu.
            + apply topo_sort_first_node_no_parents with (ts := t). split. easy. apply eqb_eq in Hhu. rewrite Hhu in Hts. apply Hts.
            + destruct (index t u) as [j|]. inversion Hi. discriminate Hi. }
        rewrite Hpar in *. simpl in Hpa1. inversion Hpa1. rewrite H1 in *.
        simpl in Hpa2. inversion Hpa2. rewrite H2 in *.
        exfalso. apply Hg. rewrite Hg1. rewrite Hg2. rewrite Hunobs. reflexivity.
      * lia.
    + intros u Hg HuG Hj unobs1 Hunobs1 unobs2 Hunobs2 Hunobs P1 HP1 pa1 Hpa1 Hg1 P2 HP2 pa2 Hpa2 Hg2.
      rewrite Hg1 in Hg. rewrite Hg2 in Hg. rewrite Hunobs in Hg.
      assert (HP: Some P1 <> Some P2).
      { intros F.
        assert (Hpa: Some pa1 <> Some pa2).
        { intros F'. apply Hg. inversion F'. reflexivity. }
        apply Hpa. rewrite Hpa1. rewrite Hpa2. inversion F. reflexivity. }
      assert (Hp: exists (p: node), In p (find_parents u G) /\ find_value G g p U1 [] <> find_value G g p U2 []).
      { apply find_values_unequal with (P1 := P1) (P2 := P2). easy. easy. intros F. apply HP. rewrite F. reflexivity. }
      destruct Hp as [p [Hmemp Hp]].

      assert (HpG: node_in_graph p G = true /\ node_in_graph u G = true).
      { apply edge_corresponds_to_nodes_in_well_formed. split. easy. apply edge_from_parent_to_child. apply Hmemp. }
      destruct HpG as [HpG _].

      assert (Hppa1: exists (P: assignments X), find_values G g (find_parents p G) U1 [] = Some P
                /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents p G)
                /\ exists (unobs: X), get_assigned_value U1 p = Some unobs
                /\ find_value G g p U1 [] = Some (g p (unobs, pa))).
      { apply find_value_evaluates_to_g. easy. }
      assert (Hppa2: exists (P: assignments X), find_values G g (find_parents p G) U2 [] = Some P
                    /\ exists (pa: list X), Some pa = get_parent_assignments P (find_parents p G)
                    /\ exists (unobs: X), get_assigned_value U2 p = Some unobs
                    /\ find_value G g p U2 [] = Some (g p (unobs, pa))).
      { apply find_value_evaluates_to_g. easy. }
      destruct Hppa1 as [P1p [HP1p [pa1p [Hpa1p [unobs1p [Hunobs1p Hg1p]]]]]].
      destruct Hppa2 as [P2p [HP2p [pa2p [Hpa2p [unobs2p [Hunobs2p Hg2p]]]]]].

      assert (Hpu: In p (find_unblocked_ancestors G u Z)).
      { apply unblocked_ancestors_have_unblocked_directed_path. right. exists []. repeat split.
         ++ simpl. unfold is_edge. destruct G as [V E]. simpl in HuG. rewrite HuG. simpl in HpG. rewrite HpG.
            apply edge_from_parent_to_child in Hmemp. simpl in Hmemp. rewrite Hmemp. reflexivity.
         ++ repeat split. intros F.
            apply edge_from_parent_to_child in Hmemp. rewrite F in Hmemp.
            assert (Hmemp': is_edge (u, u) G = false). { apply acyclic_no_self_loop. easy. }
            unfold is_edge in Hmemp'. destruct G as [V E]. simpl in HuG. rewrite HuG in Hmemp'. simpl in Hmemp'.
            simpl in Hmemp. rewrite Hmemp in Hmemp'. discriminate Hmemp'.
         ++ intros F. apply F.
         ++ intros F. apply F.
         ++ intros w [Hw | Hw].
            ** intros Hmem. unfold unobs_conditions_on_Z in HZ1. unfold unobs_conditions_on_Z in HZ2.
               assert (Hpmem: In p Z /\ node_in_graph p G = true).
               { split. rewrite <- Hw. apply Hmem. apply HpG. }
               apply HZ1 in Hpmem as HAZ1. apply HZ2 in Hpmem as HAZ2.
               rewrite Hw in *. apply Hp. rewrite HAZ1. rewrite HAZ2. reflexivity.
            ** exfalso. apply Hw. }

      destruct (eqb unobs1p unobs2p) as [|] eqn:Hunobsp.
      * specialize IH with (u := p) (unobs1 := unobs1p) (unobs2 := unobs2p) (P1 := P1p) (pa1 := pa1p) (P2 := P2p) (pa2 := pa2p).
        assert (Hind: exists a : node,
                       In a (find_unblocked_ancestors G p Z) /\
                       get_assigned_value U1 a <> get_assigned_value U2 a /\
                       find_value G g a U1 [] <> find_value G g a U2 []).
        { apply IH. clear IH. easy. easy.
          - assert (Hpj: exists (j i': nat), Some j = index ts p /\ Some i' = index ts u /\ j < i').
            { apply topo_sort_parents with (G := G). easy. easy. }
            destruct Hpj as [ixp [ixu [Hixp [Hixu Hix]]]].
            exists ixp. split. apply Hixp.
            destruct Hj as [j [Hj Hji']]. rewrite <- Hj in Hixu. inversion Hixu. rewrite H1 in Hix. lia.
          - easy.
          - easy.
          - apply eqb_eq' in Hunobsp. apply Hunobsp.
          - easy.
          - easy.
          - easy.
          - easy.
          - easy.
          - easy. }
        destruct Hind as [a Ha]. exists a. repeat split.
        -- apply unblocked_ancestors_transitive with (ancu' := p).
           ++ apply Hpu.
           ++ apply Ha.
        -- apply Ha.
        -- apply Ha.
      * exists p. repeat split.
        -- apply Hpu.
        -- intros F. rewrite Hunobs1p in F. rewrite Hunobs2p in F. inversion F. rewrite H1 in Hunobsp. rewrite eqb_refl' in Hunobsp. discriminate Hunobsp.
        -- apply Hp.

  - exists u. repeat split.
    + unfold find_unblocked_ancestors. left. reflexivity.
    + intros F. rewrite Hunobs1 in F. rewrite Hunobs2 in F. inversion F. rewrite H1 in Hunobs. rewrite eqb_refl' in Hunobs. discriminate Hunobs.
    + apply Hg.
Qed.

Theorem conditional_independence_d_separation {X : Type} `{EqType X}: forall (G: graph) (u v: node),
  u <> v /\ generic_graph_and_type_properties_hold X G /\ node_in_graph v G = true
  -> forall (Z: nodes), subset Z (nodes_in_graph G) = true /\ each_node_appears_once Z /\ member u Z = false /\ member v Z = false
  -> d_separated_bool u v G Z = true <-> conditionally_independent' X G u v Z.
Proof.
  intros G u' v'. intros [Huveq [HG Hnodev]] Z HZ. split.
  { intros Hdsep. unfold conditionally_independent'.
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

    assert (Hdconn_con: forall (anc: node) (u v: node), u <> v -> In anc (find_unblocked_ancestors G v Z) /\ In anc (find_unblocked_ancestors G u Z)
                    -> (exists (l: nodes), d_connected_2 (v, u, l) G Z /\ is_directed_path_in_graph (v, u, l) G = true /\ acyclic_path_2 (v, u, l) /\ (forall w : node, w = v \/ In w l -> ~ In w Z))
                       \/ (exists (l: nodes), d_connected_2 (u, v, l) G Z /\ is_directed_path_in_graph (u, v, l) G = true /\ acyclic_path_2 (u, v, l) /\ (forall w : node, w = u \/ In w l -> ~ In w Z))
                       \/ (exists (lu lv: nodes) (anc: node), d_connected_2 (u, v, (rev lu) ++ anc :: lv) G Z /\ is_path_in_graph (u, v, (rev lu) ++ anc :: lv) G = true
                            /\ is_directed_path_in_graph (anc, u, lu) G = true /\ is_directed_path_in_graph (anc, v, lv) G = true
                            /\ acyclic_path_2 (u, v, (rev lu) ++ anc :: lv) /\ (forall w : node, w = anc \/ In w lu \/ In w lv -> ~ In w Z))).
    { intros anc u v Huv [Hancv Hancu].
      destruct (member v (find_unblocked_ancestors G u Z)) as [|] eqn:Heqancv.
      - apply member_In_equiv in Heqancv. destruct (member u (find_unblocked_ancestors G v Z)) as [|] eqn:Heqancu.
        + (* cycle, contradiction *) exfalso. apply member_In_equiv in Heqancu. apply unblocked_ancestors_have_unblocked_directed_path in Heqancv.
          apply unblocked_ancestors_have_unblocked_directed_path in Heqancu.
          destruct Heqancu as [Heqancu | Heqancu]. apply Huv. apply Heqancu.
          destruct Heqancv as [Heqancv | Heqancv]. apply Huv. rewrite Heqancv. reflexivity.
          destruct Heqancu as [lu [Hlu _]]. destruct Heqancv as [lv [Hlv _]].
          assert (Hcycle: is_directed_path_in_graph (concat u v u lu lv) G = true).
          { apply concat_directed_paths. split. apply Hlu. apply Hlv. }
          destruct HG as [_ [_ HG]]. apply contains_cycle_false_correct with (p := (concat u v u lu lv)) in HG.
          * unfold concat in HG. unfold acyclic_path_2 in HG. destruct HG as [HG _]. apply HG. reflexivity.
          * apply directed_path_is_path. apply Hcycle.
        + (* v -> ...l... -> u is d-connected path *) left. clear Hancu. clear Hancv.
          apply unblocked_ancestors_have_unblocked_directed_path in Heqancv. destruct Heqancv as [Hancu | Hancu]. exfalso. apply Huv. rewrite Hancu. reflexivity.
          destruct Hancu as [l [Hdir [Hcycu HlZ]]]. exists l.
          assert (Hconn: d_connected_2 (v, u, l) G Z). { apply Hdconn1. split. apply Hdir. apply HlZ. }
          split. apply Hconn. split. apply Hdir. split. apply Hcycu. apply HlZ.
      - pose proof Hancv as Hancv'. apply unblocked_ancestors_have_unblocked_directed_path in Hancv. destruct Hancv as [Hancv | Hancv].
        (* v is not an unblocked ancestor of u *) rewrite Hancv in Hancu. apply member_In_equiv in Hancu. rewrite Hancu in Heqancv. discriminate Heqancv.
        destruct (member u (find_unblocked_ancestors G v Z)) as [|] eqn:Heqancu.
        + (* u -> ...lv... -> v is a d-connected path *) right. left. clear Hancu. clear Hancv. apply member_In_equiv in Heqancu.
          apply unblocked_ancestors_have_unblocked_directed_path in Heqancu. destruct Heqancu as [Hancv | Hancv]. exfalso. apply Huv. apply Hancv.
          destruct Hancv as [l [Hdir [Hcycv HlZ]]]. exists l.
          assert (Hconn: d_connected_2 (u, v, l) G Z). { apply Hdconn1. split. apply Hdir. apply HlZ. }
          split. apply Hconn. split. apply Hdir. split. apply Hcycv. apply HlZ.
        + (* u <- ...lu... <- anc -> ...lv... -> v  is a d-connected path *) right. right.
          apply unblocked_ancestors_have_unblocked_directed_path in Hancu. destruct Hancu as [Hancu | Hancu]. rewrite Hancu in Hancv'. apply member_In_equiv in Hancv'. rewrite Hancv' in Heqancu. discriminate Heqancu.
          assert (Hanc': exists (anc': node) (lu lv: nodes), is_directed_path_in_graph (anc', u, lu) G = true /\ is_directed_path_in_graph (anc', v, lv) G = true
                         /\ (forall w : node, w = anc' \/ In w lu \/ In w lv -> ~ In w Z) /\ acyclic_path_2 (u, v, (rev lu) ++ (anc' :: lv))).
          { destruct Hancv as [lv' Hv']. destruct Hancu as [lu' Hu']. apply acyclic_path_if_common_ancestor with (anc := anc) (lu := lu') (lv := lv') (len := S (length lu')).
            - split. apply Huv. split. intros Hmem. apply member_In_equiv in Hmem. rewrite Hmem in Heqancu. discriminate Heqancu.
              intros Hmem. apply member_In_equiv in Hmem. rewrite Hmem in Heqancv. discriminate Heqancv.
            - lia.
            - apply Hv'.
            - apply Hu'. }
          destruct Hanc' as [anc' [lu [lv [Hdiru [Hdirv [HlulvZ Hcycuv]]]]]]. exists lu. exists lv. exists anc'.
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
          split. apply Hconn. split. apply Hpath. split. apply Hdiru. split. apply Hdirv. split. apply Hcycuv. apply HlulvZ. }

    assert (Hdconn_con': forall (anc: node) (u v: node), u <> v -> In anc (find_unblocked_ancestors G v Z) /\ In anc (find_unblocked_ancestors G u Z)
                    -> d_separated_bool u v G Z = true -> False).
    { intros anc u v Huv [Hancv Hancu] Hsep.
      specialize Hdconn_con with (anc := anc) (u := u) (v := v). apply Hdconn_con in Huv.
      destruct Huv as [Hvlu | [Hulv | Hcon]].
      - destruct Hvlu as [l [Hconn [Hdir [Hcyc HlZ]]]].
        apply d_connected_path_not_d_separated with (l := rev l) in Hsep.
        * apply Hsep.
        * apply reverse_d_connected_paths. apply Hconn.
        * split. apply reverse_path_in_graph. apply directed_path_is_path. apply Hdir. apply reverse_path_still_acyclic. apply Hcyc.
      - destruct Hulv as [l [Hconn [Hdir [Hcyc HlZ]]]].
        apply d_connected_path_not_d_separated with (l := l) in Hsep.
        * apply Hsep.
        * apply Hconn.
        * split. apply directed_path_is_path. apply Hdir. apply Hcyc.
      - destruct Hcon as [lu [lv [anc' [Hconn [Hpath [_ [_ [Hcyc HlZ]]]]]]]].
        apply d_connected_path_not_d_separated with (u := u) (v := v) (l := (rev lu) ++ (anc' :: lv)) (G := G) (Z := Z).
        -- apply Hconn.
        -- split. apply Hpath. apply Hcyc.
        -- apply Hsep.
      - split. apply Hancv. apply Hancu. }

    assert (Hanc_con: forall (u ancu' z v: node) (lu luz lv: nodes),
                is_directed_path_in_graph (ancu', z, luz) G = true
                -> is_directed_path_in_graph (ancu', u, lu) G = true /\ ~(In ancu' Z)
                -> In ancu' (find_confounders_in_path (concat u ancu' v (rev lu) (luz ++ z :: rev lv)) G) /\ ~ In ancu' Z).
    { intros u z x v lu luz1 lv1 Hdirluz1 [Hdirlu HluZ]. split.
      + apply confounders_vs_edges_in_path. destruct lu as [| hlu tlu].
        * destruct luz1 as [| hluz tluz].
          -- exists u. exists x. split.
             ++ simpl. repeat rewrite eqb_refl. reflexivity.
             ++ simpl in Hdirlu. rewrite andb_comm in Hdirlu. simpl in Hdirlu. split. apply Hdirlu.
                simpl in Hdirluz1. rewrite andb_comm in Hdirluz1. simpl in Hdirluz1. apply Hdirluz1.
          -- exists u. exists hluz. split.
             ++ apply sublist_breaks_down_list. exists []. exists (tluz ++ x :: rev lv1 ++ [v]). simpl. rewrite <- app_assoc. simpl. reflexivity.
             ++ simpl in Hdirlu. rewrite andb_comm in Hdirlu. simpl in Hdirlu. split. apply Hdirlu.
                simpl in Hdirluz1. apply split_and_true in Hdirluz1. destruct Hdirluz1 as [Hdirluz1 _]. apply Hdirluz1.
        * destruct luz1 as [| hluz tluz].
          -- exists hlu. exists x. split.
             ++ apply sublist_breaks_down_list. exists (u :: rev tlu). exists (rev lv1 ++ [v]). simpl. repeat rewrite <- app_assoc; simpl. reflexivity.
             ++ simpl in Hdirlu. apply split_and_true in Hdirlu. destruct Hdirlu as [Hdirlu _]. split. apply Hdirlu.
                simpl in Hdirluz1. rewrite andb_comm in Hdirluz1. simpl in Hdirluz1. apply Hdirluz1.
          -- exists hlu. exists hluz. split.
             ++ apply sublist_breaks_down_list. exists (u :: rev tlu). exists (tluz ++ x :: rev lv1 ++ [v]). simpl. repeat rewrite <- app_assoc; simpl. rewrite <- app_assoc. simpl. reflexivity.
             ++ simpl in Hdirlu. apply split_and_true in Hdirlu. destruct Hdirlu as [Hdirlu _]. split. apply Hdirlu.
                simpl in Hdirluz1. apply split_and_true in Hdirluz1. destruct Hdirluz1 as [Hdirluz1 _]. apply Hdirluz1.
      + apply HluZ. }

    assert (Hconn_col: forall (u z v: node) (lu lv: nodes),
              In z Z /\ u <> v /\ overlap (find_unblocked_ancestors G u Z) (find_unblocked_ancestors G v Z) = false
              -> is_directed_path_in_graph (u, z, lu) G = true /\ acyclic_path_2 (u, z, lu) /\ (forall w : node, w = u \/ In w lu -> ~ In w Z)
              -> is_directed_path_in_graph (v, z, lv) G = true /\ acyclic_path_2 (v, z, lv) /\ (forall w : node, w = v \/ In w lv -> ~ In w Z)
              -> (is_path_in_graph (concat u z v lu (rev lv)) G = true /\ acyclic_path_2 (concat u z v lu (rev lv)) /\ d_connected_2 (concat u z v lu (rev lv)) G Z)
                 \/ (exists (lu1 lu2 lv' lv1 lv2: nodes) (x: node), is_directed_path_in_graph (v, z, lv') G = true /\ acyclic_path_2 (v, z, lv') /\ (forall w : node, (w = v \/ In w lv') -> ~ In w Z)
                      /\ lu = lu1 ++ [x] ++ lu2 /\ lv = lv1 ++ [x] ++ lv2 /\ lv' = lv1 ++ [x] ++ lu2 /\ overlap lu1 lv1 = false
                      /\ d_connected_2 (u, v, lu1 ++ [x] ++ (rev lv1)) G Z /\ is_path_in_graph (u, v, lu1 ++ [x] ++ (rev lv1)) G = true /\ acyclic_path_2 (u, v, lu1 ++ [x] ++ (rev lv1)))).
    { intros u z v lu lv. intros [HzZ [Huv Hover]] [Hdiru [Hcycu HluZ]] [Hdirv [Hcycv HlvZ]].
      assert (Hacyc: overlap lu lv = false \/
                     exists (l2': nodes), is_directed_path_in_graph (v, z, l2') G = true /\ acyclic_path_2 (v, z, l2')
                      /\ (forall w : node, (w = v \/ In w l2') -> ~ In w Z)
                      /\ exists (l1'' l2'': nodes) (l3 l3': nodes) (x: node), lu = l1'' ++ [x] ++ l3 /\ l2' = l2'' ++ [x] ++ l3 /\ lv = l2'' ++ [x] ++ l3' /\ overlap l1'' l2'' = false).
      { apply acyclic_paths_intersect_if_common_endpoint with (anc1 := u).
        - destruct HG as [_ [_ HG]]. apply HG.
        - split. apply Hdiru. split. apply Hcycu. apply HluZ.
        - split. apply Hdirv. split. apply Hcycv. apply HlvZ. }
      destruct Hacyc as [Hacyc | Hacyc].
      *** (* lu and lv have no overlap, so the path is acyclic *) left.
          assert (Hpath: is_path_in_graph (concat u z v lu (rev lv)) G = true).
          { apply concat_paths_still_a_path. split.
            + apply directed_path_is_path in Hdiru. apply Hdiru.
            + apply reverse_path_in_graph. apply directed_path_is_path in Hdirv. apply Hdirv. }
          assert (Hcat: acyclic_path_2 (concat u z v lu (rev lv))).
          { apply concat_paths_acyclic.
            - split. apply Huv. split. apply Hcycu. apply reverse_path_still_acyclic. apply Hcycv.
            - split.
              + intros F. apply membership_rev in F. rewrite <- reverse_list_twice in F.
                apply no_overlap_non_member with (x := v) in Hover.
                * apply Hover. apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := lv). split.
                  -- apply Hdirv.
                  -- split. apply Hcycv. apply HlvZ.
                  -- apply F.
                * unfold find_unblocked_ancestors. left. reflexivity.
              + intros F. apply no_overlap_non_member_rev with (x := u) in Hover.
                * apply Hover. apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := lu). split.
                  -- apply Hdiru.
                  -- split. apply Hcycu. apply HluZ.
                  -- apply F.
                * unfold find_unblocked_ancestors. left. reflexivity.
            - apply overlap_rev. apply Hacyc. }
          split. apply Hpath. split. apply Hcat.
          apply concat_d_connected_paths.
          - destruct HG as [_ [_ HG]]. apply HG.
          - apply Hpath.
          - split.
            + apply Hdconn1. split.
              * apply Hdiru.
              * apply HluZ.
            + split.
              * apply reverse_d_connected_paths. apply Hdconn1. split. apply Hdirv. apply HlvZ.
              * apply Hcat.
          - right. right. split.
            + apply colliders_vs_edges_in_path.
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
              * apply HzZ.
      *** right. (* need to address case of the two paths meeting prior to z, in which case z is the descendant of a collider *)
          clear Hdirv. clear Hcycv. clear HlvZ.
          destruct Hacyc as [lv' [Hdirv [Hcycv [HlvZ [lu'' [lv'' [l [l' [x [Hlu' [Hlv' [Hlv'' Hacyc]]]]]]]]]]]]. remember lu as lu'.
          assert (Hpath: is_path_in_graph (concat u x v lu'' (rev lv'')) G = true).
          { apply concat_paths_still_a_path. split.
            + apply directed_path_is_path. apply subpath_still_directed_2 with (v := z) (l2 := l) (l3 := lu'). split. rewrite Hlu'. reflexivity. apply Hdiru.
            + apply reverse_path_in_graph. apply directed_path_is_path. apply subpath_still_directed_2 with (v := z) (l2 := l) (l3 := lv'). split.
              symmetry. apply Hlv'. apply Hdirv. }
          assert (Hcat: acyclic_path_2 (concat u x v lu'' (rev lv''))).
          { apply concat_paths_acyclic.
            - split. apply Huv. split. apply subpath_still_acyclic_2 with (v := z) (l2 := l) (l3 := lu'). split. symmetry. apply Hlu'. apply Hcycu.
              apply reverse_path_still_acyclic. apply subpath_still_acyclic_2 with (v := z) (l2 := l) (l3 := lv'). split. symmetry. apply Hlv'. apply Hcycv.
            - split.
              + intros F. apply membership_rev in F. rewrite <- reverse_list_twice in F.
                apply no_overlap_non_member with (x := v) in Hover.
                * apply Hover. apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := lv'). split.
                  -- apply Hdirv.
                  -- split. apply Hcycv. apply HlvZ.
                  -- apply membership_splits_list in F. destruct F as [lu1 [lu2 F]]. apply membership_splits_list. exists lu1. exists (lu2 ++ [x] ++ l).
                     rewrite Hlv'. rewrite <- F. rewrite <- app_assoc. reflexivity.
                * unfold find_unblocked_ancestors. left. reflexivity.
              + intros F. apply no_overlap_non_member_rev with (x := u) in Hover.
                * apply Hover. apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := lu'). split.
                  -- apply Hdiru.
                  -- split. apply Hcycu. apply HluZ.
                  -- apply membership_splits_list in F. destruct F as [lv1 [lv2 F]]. apply membership_splits_list. exists lv1. exists (lv2 ++ [x] ++ l).
                     rewrite Hlu'. rewrite <- F. rewrite <- app_assoc. reflexivity.
                * unfold find_unblocked_ancestors. left. reflexivity.
            - apply overlap_rev. apply Hacyc. }
          assert (Hdiru': is_directed_path_in_graph (u, x, lu'') G = true). { apply subpath_still_directed_2 with (v := z) (l2 := l) (l3 := lu'). split. rewrite Hlu'. reflexivity. apply Hdiru. }
          assert (Hdirv': is_directed_path_in_graph (v, x, lv'') G = true). { apply subpath_still_directed_2 with (v := z) (l2 := l) (l3 := lv'). split. rewrite Hlv'. reflexivity. apply Hdirv. }
          exists lu''. exists l. exists lv'. exists lv''. exists l'. exists x. split. apply Hdirv. split. apply Hcycv. split. apply HlvZ.
          split. apply Hlu'. split. apply Hlv''. split. apply Hlv'. split. apply Hacyc. split.
          apply concat_d_connected_paths.
          - destruct HG as [_ [_ HG]]. apply HG.
          - apply Hpath.
          - split.
            + apply Hdconn1. split.
              * apply Hdiru'.
              * intros w Hw. apply HluZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. apply membership_append with (l2 := [x] ++ l) in Hw. rewrite Hlu'. apply Hw.
            + split.
              * apply reverse_d_connected_paths. apply Hdconn1. split.
                -- apply Hdirv'.
                -- intros w Hw. apply HlvZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. apply membership_append with (l2 := [x] ++ l) in Hw. rewrite Hlv'. apply Hw.
              * apply Hcat.
          - right. right. split.
            + apply colliders_vs_edges_in_path.
              apply directed_path_has_directed_edge_end in Hdiru' as Hdiru''. destruct Hdiru'' as [Hdiru'' | Hdiru''].
              * apply directed_path_has_directed_edge_end in Hdirv' as Hdirv''. destruct Hdirv'' as [Hdirv'' | Hdirv''].
                exists u. exists v. rewrite Hdirv'' in *. rewrite Hdiru'' in *. split.
                -- apply sublist_breaks_down_list. exists []. exists []. simpl. reflexivity.
                -- split. simpl in Hdiru'. rewrite andb_comm in Hdiru'. simpl in Hdiru'. apply Hdiru'.
                   simpl in Hdirv'. rewrite andb_comm in Hdirv'. simpl in Hdirv'. apply Hdirv'.
                -- destruct Hdirv'' as [l'' [x' Hdirv'']]. exists u. exists x'. split.
                   ++ apply sublist_breaks_down_list. exists []. exists (rev l'' ++ [v]).
                      simpl. rewrite Hdiru''. destruct Hdirv'' as [Hdirv'' Hxz]. rewrite Hdirv''. rewrite reverse_list_append.
                      simpl. reflexivity.
                   ++ split. rewrite Hdiru'' in Hdiru'. simpl in Hdiru'. rewrite andb_comm in Hdiru'. simpl in Hdiru'. apply Hdiru'.
                      destruct Hdirv'' as [_ Hdirv'']. apply Hdirv''.
              * destruct Hdiru'' as [l'' [x'' [Hl' Hxx']]].
                apply directed_path_has_directed_edge_end in Hdirv' as Hdirv''. destruct Hdirv'' as [Hdirv'' | Hdirv''].
                { exists x''. exists v. rewrite Hdirv'' in *. split.
                  -- apply sublist_breaks_down_list. rewrite Hl'. exists (u :: l''). exists []. simpl. unfold node.
                     f_equal. repeat rewrite <- app_assoc; simpl. reflexivity.
                  -- split. apply Hxx'. simpl in Hdirv'. rewrite andb_comm in Hdirv'. simpl in Hdirv'. apply Hdirv'. }
                { destruct Hdirv'' as [l''' [x''' [Hl'' Hxx'']]]. exists x''. exists x'''. split.
                  -- apply sublist_breaks_down_list. exists (u :: l''). exists (rev l''' ++ [v]).
                     simpl. rewrite Hl''. rewrite reverse_list_append.
                     simpl. rewrite Hl'. simpl. unfold node. f_equal. repeat rewrite <- app_assoc; simpl. reflexivity.
                  -- split. apply Hxx'. apply Hxx''. }
            + unfold some_descendant_in_Z_bool. apply overlap_has_member_in_common. exists z.
              split.
              * apply find_descendants_correct. right. exists (x, z, l). split.
                -- apply subpath_still_directed with (w := u) (l1 := lu'') (l3 := lu'). split. symmetry. apply Hlu'. apply Hdiru.
                -- apply path_start_end_refl.
              * apply HzZ.
          - split. apply Hpath. apply Hcat. }

    assert (HvUa: exists (va: X), find_value G g v' Ua [] = Some va).
    { apply find_value_existence.
      - destruct HG as [_ HG]. apply HG.
      - split. destruct HUa as [HUa _]. apply HUa. apply Hnodev. }
    assert (HvUb: exists (vb: X), find_value G g v' Ub [] = Some vb).
    { apply find_value_existence.
      - destruct HG as [_ HG]. apply HG.
      - split. destruct HUb as [HUb _]. apply HUb. apply Hnodev. }
    assert (HvUb': exists (vb': X), find_value G g v' Ub' [] = Some vb').
    { apply find_value_existence.
      - destruct HG as [_ HG]. apply HG.
      - split. destruct HUb' as [HUb' _]. apply HUb'. apply Hnodev. }
    destruct HvUa as [va HvUa]. destruct HvUb as [vb HvUb]. destruct HvUb' as [vb' HvUb'].

    destruct (overlap (find_unblocked_ancestors G u' Z) (find_unblocked_ancestors G v' Z)) as [|] eqn:Hover.
    { (* contradiction: d-connected path u' <- ... <- anc -> ... -> v' *)
      apply overlap_has_member_in_common in Hover. destruct Hover as [anc [Hancu Hancv]].
      specialize Hdconn_con' with (anc := anc) (u := u') (v := v'). exfalso. apply Hdconn_con'. repeat split.
      + apply Huveq.
      + split. apply Hancv. apply Hancu.
      + apply Hdsep. }
    { destruct (eqb va vb') as [|] eqn:Hvavb'.
      - apply eqb_eq' in Hvavb'. rewrite Hvavb' in HvUa. unfold find_value in HvUa. unfold find_value in HvUb'. rewrite HAa in HvUa. rewrite HAb' in HvUb'.
        rewrite HvUa. rewrite HvUb'. reflexivity.
      - assert (Hfvavb': find_value G g v' Ua [] <> find_value G g v' Ub' []).
        { rewrite HvUa. rewrite HvUb'. intros F. inversion F. rewrite H1 in Hvavb'. rewrite eqb_refl' in Hvavb'. discriminate Hvavb'. }
        assert (Hancv: exists a : node,
            In a (find_unblocked_ancestors G v' Z) /\
            get_assigned_value Ua a <> get_assigned_value Ub' a /\
            find_value G g a Ua [] <> find_value G g a Ub' []).
        { apply nodefun_value_only_affected_by_unblocked_ancestors with (Z := Z) (AZ := AZ). 
          - apply HG.
          - apply Hfvavb'.
          - split. apply HUa. apply HUb'.
          - apply Hnodev.
          - split. apply HZUa. apply HZUb'. }
        destruct Hancv as [ancv [Hancv [HancvU Hancvf]]].

        assert (HancvUab: get_assigned_value Ua ancv = get_assigned_value Ub ancv).
        { unfold assignments_change_only_for_subset in HUab. specialize HUab with (x := ancv). destruct HUab as [_ HUab]. apply HUab.
          apply no_overlap_non_member with (x := ancv) in Hover.
          - apply Hover.
          - apply Hancv. }

        unfold assignments_change_only_for_subset in HUbb'. specialize HUbb' with (x := ancv).
        assert (Hz: exists (z: node), In ancv (find_unblocked_ancestors G z Z) /\ overlap (find_unblocked_ancestors G z Z)
                                                (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub) = true
                                                /\ is_assigned AZ z = true /\ find_value G g z Ub [] <> get_assigned_value AZ z).
        { apply unblocked_ancestor_of_node_in_Z' with (Ab := Ab). repeat split.
          - destruct (member ancv (find_unblocked_ancestors_in_Z' G Z AZ Ab
                        (unblocked_ancestors_that_changed_A_to_B (nodes_in_graph G) Ua Ub))) as [|] eqn:HmemZ.
            + apply member_In_equiv in HmemZ. apply HmemZ.
            + assert (F: get_assigned_value Ub ancv = get_assigned_value Ub' ancv).
              { destruct HUbb' as [_ HUbb']. apply HUbb'. intros F. apply member_In_equiv in F. rewrite F in HmemZ. discriminate HmemZ. }
              exfalso. apply HancvU. rewrite HancvUab. apply F.
          - apply HAb.
          - destruct HAZ as [_ HAZ]. apply HAZ. }
        destruct Hz as [z [Hancvz [Hoverz [HAZz HUbz]]]].
        (* now show that z shares and unblocked ancestor with u due to HUab *)
        assert (HzZ: In z Z /\ node_in_graph z G = true).
        { split. destruct (member z Z) as [|] eqn:HzZ.
          - apply member_In_equiv in HzZ. apply HzZ.
          - unfold is_exact_assignment_for in HAZ. destruct HAZ as [[_ HAZ] _]. specialize HAZ with (u := z).
            apply HAZ in HzZ. rewrite HzZ in HAZz. discriminate HAZz.
          - apply unblocked_ancestors_have_unblocked_directed_path in Hancvz. destruct Hancvz as [Hz | Hz].
            + apply unblocked_ancestors_have_unblocked_directed_path in Hancv. destruct Hancv as [Hz' | Hz'].
              * rewrite <- Hz. rewrite Hz'. apply Hnodev.
              * destruct Hz' as [l Hz']. apply nodes_in_graph_in_V with (p := (ancv, v', l)). split.
                -- unfold node_in_path. simpl. rewrite Hz. rewrite eqb_refl. reflexivity.
                -- apply directed_path_is_path. apply Hz'.
            + destruct Hz as [l Hz]. apply nodes_in_graph_in_V with (p := (ancv, z, l)). split.
              * unfold node_in_path. simpl. rewrite eqb_refl. rewrite <- orb_assoc. rewrite orb_comm. reflexivity.
              * apply directed_path_is_path. apply Hz. }

        assert (Hfzazb: find_value G g z Ua [] <> find_value G g z Ub []).
        { (* show that f(z, Ua) = AZ(z) using HZUa *)
          unfold unobs_conditions_on_Z in HZUa. specialize HZUa with (w := z). apply HZUa in HzZ. rewrite HzZ. intros F. rewrite F in HUbz. apply HUbz. reflexivity. }

        apply overlap_has_member_in_common in Hoverz. destruct Hoverz as [ancu [Hancuz Hancu]].
        assert (HancuU: get_assigned_value Ua ancu <> get_assigned_value Ub ancu).
        { apply in_unblocked_that_changed with (G := G). apply Hancu. }
        clear Hancu.

        unfold assignments_change_only_for_subset in HUab. specialize HUab with (x := ancu).
        assert (Hancu: In ancu (find_unblocked_ancestors G u' Z)).
        { destruct (member ancu (find_unblocked_ancestors G u' Z)) as [|] eqn:Hancu'.
          - apply member_In_equiv. apply Hancu'.
          - destruct HUab as [_ HUab]. assert (Hancu: ~ In ancu (find_unblocked_ancestors G u' Z)).
            { intros F. apply member_In_equiv in F. rewrite Hancu' in F. discriminate F. }
            clear Hancu'. apply HUab in Hancu. rewrite Hancu in HancuU. exfalso. apply HancuU. reflexivity. }

            (* u <- ... <- ancu -> ... -> z <- ... <- ancv -> ... -> v is a d-connected path *)
            pose proof Hdconn_con as Hconvz. specialize Hconvz with (anc := ancv) (u := z) (v := v').
            pose proof Hdsep as Hdsep'. clear Hdsep. pose proof Hover as Hover'. clear Hover. pose proof Huveq as Hequv'. clear Huveq.

            assert (Hconn_con_col': forall (u v ancu': node) (lv lu luz: nodes), z <> v /\ u <> z /\ u <> v
                      -> d_connected_2 (v, z, lv) G Z /\ is_directed_path_in_graph (v, z, lv) G = true /\ acyclic_path_2 (v, z, lv) /\ (forall w : node, w = v \/ In w lv -> ~ In w Z)
                      -> d_connected_2 (u, z, rev lu ++ ancu' :: luz) G Z /\ is_path_in_graph (u, z, rev lu ++ ancu' :: luz) G = true /\ acyclic_path_2 (u, z, rev lu ++ ancu' :: luz)
                         /\ is_directed_path_in_graph (ancu', u, lu) G = true /\ is_directed_path_in_graph (ancu', z, luz) G = true /\ (forall w : node, w = ancu' \/ In w lu \/ In w luz -> ~ In w Z)
                      -> overlap (find_unblocked_ancestors G u Z) (find_unblocked_ancestors G v Z) = false
                      -> exists (x: node) (luz1 lv1: nodes), (d_connected_2 (concat u x v (rev lu ++ ancu' :: luz1) (rev lv1)) G Z /\ is_path_in_graph (concat u x v (rev lu ++ ancu' :: luz1) (rev lv1)) G = true
                          /\ acyclic_path_2 (concat u x v (rev lu ++ ancu' :: luz1) (rev lv1)))
                          /\ ((luz1 = luz /\ lv1 = lv /\ z = x) \/ (exists (luz2 lv2: nodes), luz = luz1 ++ [x] ++ luz2 /\ lv = lv1 ++ [x] ++ lv2))).
            { intros u v ancu' lv lu luz. intros [Hzv [Huz Huveq]]. intros [Hconnvz [Hdirvz [Hcycvz HlvZ]]]. intros [Hconnuz [Hpathuz [Hcycuz [Hdirlu [Hdirluz HluZ]]]]].
              intros Hover.
              (* helper lemmas to use later on *)
              assert (Hvancu': ancu' <> v). (* else, v is an unblocked ancestor of u *)
              { intros F. apply no_overlap_non_member with (x := v) in Hover.
                - apply Hover. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lu.
                  rewrite F in *. split. apply Hdirlu. split. rewrite reverse_list_twice with (l := lu). apply reverse_path_still_acyclic.
                  apply subpath_still_acyclic_2 with (v := z) (l2 := luz) (l3 := rev lu ++ [v] ++ luz).
                  + split. reflexivity. apply Hcycuz.
                  + intros w Hw. apply HluZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. left. apply Hw.
                - unfold find_unblocked_ancestors. left. reflexivity. }
              specialize Hconn_col with (u := ancu') (z := z) (v := v) (lu := luz) (lv := lv).

              assert (Heqvancu': In z Z /\ ancu' <> v /\ overlap (find_unblocked_ancestors G ancu' Z) (find_unblocked_ancestors G v Z) = false).
              { split. apply HzZ. split. apply Hvancu'.
                (* else, the member in common is a common unblocked ancestor of u and v *)
                destruct (overlap (find_unblocked_ancestors G ancu' Z) (find_unblocked_ancestors G v Z)) as [|] eqn:F.
                - apply overlap_has_member_in_common in F. destruct F as [x [Hxancu' Hxv]].
                  apply no_overlap_non_member with (x := x) in Hover.
                  + exfalso. apply Hover. apply unblocked_ancestors_have_unblocked_directed_path in Hxancu'. destruct Hxancu' as [Hxancu' | [lx [Hdirx [Hcycx HlxZ]]]].
                    -- rewrite Hxancu'. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lu. split. apply Hdirlu. split.
                       rewrite reverse_list_twice with (l := lu). apply reverse_path_still_acyclic.
                       apply subpath_still_acyclic_2 with (v := z) (l2 := luz) (l3 := rev lu ++ [ancu'] ++ luz).
                       ++ split. reflexivity. apply Hcycuz.
                       ++ intros w Hw. apply HluZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. left. apply Hw.
                    -- apply unblocked_ancestors_have_unblocked_directed_path. right.
                       assert (Hdir: is_directed_path_in_graph (x, u, lx ++ [ancu'] ++ lu) G = true).
                       { apply concat_directed_paths. split. apply Hdirx. apply Hdirlu. }
                       apply directed_path_can_be_acyclic in Hdir. destruct Hdir as [lx' [Hdir' [Hcyc' Hlx']]].
                       exists lx'. split. apply Hdir'. split. apply Hcyc'.
                       intros w Hw. destruct Hw as [Hw | Hw].
                       ++ apply HlxZ. left. apply Hw.
                       ++ assert (Hmem: In w (lx ++ [ancu'] ++ lu)). { apply subset_larger_set_membership with (l1 := lx'). split. apply Hlx'. apply Hw. }
                          apply membership_append_or in Hmem. destruct Hmem as [Hmem | Hmem].
                          ** apply HlxZ. right. apply Hmem.
                          ** apply HluZ. simpl in Hmem. destruct Hmem as [Hmem | Hmem]. left. symmetry. apply Hmem. right. left. apply Hmem.
                  + apply Hxv.
                - reflexivity. }
              apply Hconn_col in Heqvancu'.
              -- (* helper lemmas *)
                 assert (Hcyclu: acyclic_path_2 (u, ancu', rev lu)).
                 { apply subpath_still_acyclic_2 with (v := z) (l2 := luz) (l3 := rev lu ++ [ancu'] ++ luz). split. reflexivity. apply Hcycuz. }
                 assert (Hvlu: ~(In v lu)).
                 { intros Hvlu. (* contradiction: then v is an unblocked ancestor of u *)
                   apply no_overlap_non_member with (x := v) in Hover.
                   ++ apply Hover. apply unblocked_ancestor_if_in_unblocked_directed_path with (anc := ancu') (l := lu).
                      ** split. apply Hdirlu. split. apply reverse_path_still_acyclic in Hcyclu. rewrite <- reverse_list_twice in Hcyclu. apply Hcyclu. intros w Hw. apply HluZ.
                         rewrite <- or_assoc. left. apply Hw.
                      ** apply Hvlu.
                   ++ unfold find_unblocked_ancestors. left. reflexivity. }
                 assert (Hulv: ~(In u lv)).
                 { (* contradiction: then v is an unblocked ancestor of u *)
                   intros Hu.
                   apply no_overlap_non_member with (x := v) in Hover.
                   ++ apply Hover. apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := lv).
                      ** easy.
                      ** apply Hu.
                   ++ unfold find_unblocked_ancestors. left. reflexivity. }
                 assert (Hlulv: overlap lu lv = false).
                 { destruct (overlap lu lv) as [|] eqn: F. apply overlap_has_member_in_common in F. destruct F as [x [Hxlu Hx]].
                   { (* contradiction: v is an unblocked ancestor of u, through x *)
                     apply no_overlap_non_member with (x := v) in Hover.
                     exfalso. apply Hover. apply membership_splits_list in Hx. destruct Hx as [lv1 [lv2 Hx]]. apply membership_splits_list in Hxlu. destruct Hxlu as [lu1 [lu2 Hxlu]]. apply unblocked_ancestors_have_unblocked_directed_path. right. exists (lv1 ++ [x] ++ lu2).
                      split. apply concat_directed_paths. split. apply subpath_still_directed_2 with (v := z) (l2 := lv2) (l3 := lv). split. apply Hx. apply Hdirvz.
                      apply subpath_still_directed with (w := ancu') (l1 := lu1) (l3 := lu). split. apply Hxlu. apply Hdirlu. split.
                      - apply concat_paths_acyclic. split. intros Hequv. apply Huveq. symmetry. apply Hequv. split.
                        apply subpath_still_acyclic_2 with (v := z) (l2 := lv2) (l3 := lv). split. apply Hx. apply Hcycvz.
                        apply subpath_still_acyclic with (w := ancu') (l1 := lu1) (l3 := lu). split. apply Hxlu. rewrite reverse_list_twice with (l := lu). apply reverse_path_still_acyclic. apply Hcyclu.
                        split.
                        + intros Hvlu2. apply Hvlu. apply membership_append_r with (l1 := lu1 ++ [x]) in Hvlu2. rewrite <- Hxlu. rewrite app_assoc. apply Hvlu2.
                        + intros Hulv1. apply Hulv. apply membership_append with (l2 := [x] ++ lv2) in Hulv1. rewrite <- Hx. apply Hulv1.
                        + (* if there were overlap, then there would be a cycle with x *) 
                          destruct (overlap lv1 lu2) as [|] eqn:F.
                          * apply overlap_has_member_in_common in F. destruct F as [x' [Hxlv1' Hxlu2']]. apply membership_splits_list in Hxlv1'. destruct Hxlv1' as [lv1' [lv1'' Hlv1]].
                            apply membership_splits_list in Hxlu2'. destruct Hxlu2' as [lu2' [lu2'' Hlu2]].
                            assert (Hcycle: is_directed_path_in_graph (concat x' x x' lv1'' lu2') G = true).
                            { apply concat_directed_paths. split. apply subpath_still_directed with (w := v) (l1 := lv1') (l3 := lv1). split. apply Hlv1.
                              apply subpath_still_directed_2 with (v := z) (l2 := lv2) (l3 := lv). split. apply Hx. apply Hdirvz.
                              apply subpath_still_directed_2 with (v := u) (l2 := lu2'') (l3 := lu2). split. apply Hlu2.
                              apply subpath_still_directed with (w := ancu') (l1 := lu1) (l3 := lu). split. apply Hxlu. apply Hdirlu. }
                            destruct HG as [_ [_ HG]]. apply contains_cycle_false_correct with (p := (concat x' x x' lv1'' lu2')) in HG. unfold acyclic_path_2 in HG. destruct HG as [HG _]. exfalso. apply HG. reflexivity.
                            apply directed_path_is_path. apply Hcycle.
                          * reflexivity.
                      - intros w Hw. destruct Hw as [Hw | Hw]. apply HlvZ. left. apply Hw. apply membership_append_or in Hw. destruct Hw as [Hw | Hw].
                        + apply HlvZ. right. apply membership_append with (l2 := [x] ++ lv2) in Hw. rewrite <- Hx. apply Hw.
                        + apply HluZ. right. left. apply membership_append_r with (l1 := lu1) in Hw. rewrite <- Hxlu. apply Hw.
                      - unfold find_unblocked_ancestors. left. reflexivity. }
                    { reflexivity. } }
                assert (Hluluz: overlap lu luz = false).
                { destruct (overlap lu luz) as [|] eqn:F.
                  - (* contradicts Hcycuz, which passes through both lu and luz *)
                    apply overlap_has_member_in_common in F. destruct F as [x [Hxlu Hx]].
                    apply acyclic_path_correct in Hcycuz. simpl in Hcycuz. apply split_and_true in Hcycuz; destruct Hcycuz as [_ Hcycuz]. apply split_and_true in Hcycuz; destruct Hcycuz as [_ Hcycuz].
                    apply acyclic_path_intermediate_nodes with (p := rev lu ++ ancu' :: luz) (x := x) in Hcycuz. destruct Hcycuz as [Hc | Hc].
                    ** rewrite count_app in Hc. apply member_count_at_least_1 in Hxlu. apply member_count_at_least_1 in Hx. rewrite count_reverse in Hc. rewrite <- reverse_list_twice in Hc. lia.
                    ** rewrite count_app in Hc. apply member_count_at_least_1 in Hxlu. apply member_count_at_least_1 in Hx. rewrite count_reverse in Hc. rewrite <- reverse_list_twice in Hc. simpl in Hc. destruct (ancu' =? x) as [|] eqn:F. lia. lia.
                  - reflexivity. }
                assert (Hancu_con: forall (z: node) (luz: nodes) (lv: nodes), is_directed_path_in_graph (ancu', z, luz) G = true
                                -> In ancu' (find_confounders_in_path (concat u ancu' v (rev lu) (luz ++ z :: rev lv)) G) /\ ~ In ancu' Z).
                { intros x luz1 lv1 Hdirluz1. split.
                  + apply confounders_vs_edges_in_path. destruct lu as [| hlu tlu].
                    * destruct luz1 as [| hluz tluz].
                      -- exists u. exists x. split.
                         ++ simpl. repeat rewrite eqb_refl. reflexivity.
                         ++ simpl in Hdirlu. rewrite andb_comm in Hdirlu. simpl in Hdirlu. split. apply Hdirlu.
                            simpl in Hdirluz1. rewrite andb_comm in Hdirluz1. simpl in Hdirluz1. apply Hdirluz1.
                      -- exists u. exists hluz. split.
                         ++ apply sublist_breaks_down_list. exists []. exists (tluz ++ x :: rev lv1 ++ [v]). simpl. rewrite <- app_assoc. simpl. reflexivity.
                         ++ simpl in Hdirlu. rewrite andb_comm in Hdirlu. simpl in Hdirlu. split. apply Hdirlu.
                            simpl in Hdirluz1. apply split_and_true in Hdirluz1. destruct Hdirluz1 as [Hdirluz1 _]. apply Hdirluz1.
                    * destruct luz1 as [| hluz tluz].
                      -- exists hlu. exists x. split.
                         ++ apply sublist_breaks_down_list. exists (u :: rev tlu). exists (rev lv1 ++ [v]). simpl. repeat rewrite <- app_assoc; simpl. reflexivity.
                         ++ simpl in Hdirlu. apply split_and_true in Hdirlu. destruct Hdirlu as [Hdirlu _]. split. apply Hdirlu.
                            simpl in Hdirluz1. rewrite andb_comm in Hdirluz1. simpl in Hdirluz1. apply Hdirluz1.
                      -- exists hlu. exists hluz. split.
                         ++ apply sublist_breaks_down_list. exists (u :: rev tlu). exists (tluz ++ x :: rev lv1 ++ [v]). simpl. repeat rewrite <- app_assoc; simpl. rewrite <- app_assoc. simpl. reflexivity.
                         ++ simpl in Hdirlu. apply split_and_true in Hdirlu. destruct Hdirlu as [Hdirlu _]. split. apply Hdirlu.
                            simpl in Hdirluz1. apply split_and_true in Hdirluz1. destruct Hdirluz1 as [Hdirluz1 _]. apply Hdirluz1.
                  + apply HluZ. left. reflexivity. }

                destruct Heqvancu' as [Hcol | Hcol].
                ++ (* no overlap between luz and lv, z is the collider *) destruct Hcol as [Hpathz [Hcycz Hconnz]].
                    exists z. exists luz. exists lv.
                    assert (Hconn: d_connected_2 (concat u ancu' v (rev lu) (luz ++ z :: (rev lv))) G Z /\ is_path_in_graph (u, v, rev lu ++ ancu' :: luz ++ z :: rev lv) G = true
                                    /\ acyclic_path_2 (u, v, rev lu ++ ancu' :: luz ++ z :: rev lv)).
                    { assert (Hpath: is_path_in_graph (u, v, rev lu ++ ancu' :: luz ++ z :: rev lv) G = true).
                      { apply concat_paths_still_a_path. split. apply reverse_path_in_graph. apply directed_path_is_path. apply Hdirlu.
                        apply concat_paths_still_a_path. split. apply directed_path_is_path. apply Hdirluz. apply reverse_path_in_graph. apply directed_path_is_path. apply Hdirvz. }
                      assert (Hcyc: acyclic_path_2 (u, v, rev lu ++ ancu' :: luz ++ z :: rev lv)).
                      { apply concat_paths_acyclic.
                        * split. apply Huveq. split.
                          -- apply Hcyclu.
                          -- apply Hcycz.
                        * split.
                          -- intros Hu. apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]].
                             ++ (* contradicts Hcycuz, which starts at u and passes through luz *)
                                unfold acyclic_path_2 in Hcycuz. destruct Hcycuz as [_ [Hcycuz _]]. apply Hcycuz. apply membership_append_r. right. apply Hu.
                             ++ (* contradiction: z is in Z, while u is not *)
                                apply Huz. symmetry. apply Hu.
                             ++ (* contradiction: then v is an unblocked ancestor of u *)
                                apply Hulv. apply membership_rev. apply Hu.
                          -- intros Hvlu'. apply Hvlu. apply membership_rev. apply Hvlu'.
                        * destruct (overlap (rev lu) (luz ++ z :: rev lv)) as [|] eqn:F.
                          -- apply overlap_has_member_in_common in F. destruct F as [x [Hxlu Hx]].
                             apply membership_append_or in Hx. destruct Hx as [Hx | [Hx | Hx]].
                             ++ apply no_overlap_non_member with (x := x) in Hluluz.
                                ** exfalso. apply Hluluz. apply membership_rev. apply Hxlu.
                                ** apply Hx.
                             ++ (* contradiction: HluZ implies z is not in Z *)
                                exfalso. apply HluZ with (w := z). right. left. rewrite Hx. apply membership_rev. apply Hxlu. apply HzZ.
                             ++ apply no_overlap_non_member with (x := x) in Hlulv.
                                ** exfalso. apply Hlulv. apply membership_rev. apply Hxlu.
                                ** apply membership_rev. apply Hx.
                          -- reflexivity. }
                      split. apply concat_d_connected_paths.
                      - apply HG.
                      - apply Hpath.
                      - split.
                        + apply reverse_d_connected_paths. apply Hdconn1. split. apply Hdirlu. intros w [Hw | Hw]. apply HluZ. left. apply Hw. apply HluZ. right. left. apply Hw.
                        + split. apply Hconnz. apply Hcyc.
                      - right. left. apply Hanc_con. apply Hdirluz. split. apply Hdirlu. apply HluZ. left. reflexivity.
                      - split. apply Hpath. apply Hcyc. }
                     split. unfold concat in Hconn. unfold concat. rewrite <- app_assoc. apply Hconn.
                     left. easy.
                 ++ (* z is a descendant of the collider (overlapping point of lu and lv) *) 
                    destruct Hcol as [luz1 [luz2 [lv' [lv1 [lv2 [x [Hdirvz' [Hcycvz' [HlvZ' [Hluz [Hlv [Hlv' [Hlu1lv1 [Hconnx [Hpathx Hcycx]]]]]]]]]]]]]]].
                    exists x. exists luz1. exists lv1.
                    assert (Hconn: d_connected_2 (concat u ancu' v (rev lu) (luz1 ++ x :: (rev lv1))) G Z /\ is_path_in_graph (concat u ancu' v (rev lu) (luz1 ++ x :: (rev lv1))) G = true
                                    /\ acyclic_path_2 (concat u ancu' v (rev lu) (luz1 ++ x :: (rev lv1)))).
                    { assert (Hpath: is_path_in_graph (concat u ancu' v (rev lu) (luz1 ++ x :: (rev lv1))) G = true).
                      { apply concat_paths_still_a_path. split. apply reverse_path_in_graph. apply directed_path_is_path. apply Hdirlu.
                        apply concat_paths_still_a_path. split. apply directed_path_is_path.
                        apply subpath_still_directed_2 with (v := z) (l2 := luz2) (l3 := luz). split. symmetry. apply Hluz. apply Hdirluz.
                        apply reverse_path_in_graph. apply directed_path_is_path. apply subpath_still_directed_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply Hlv. apply Hdirvz. }
                      assert (Hcyc: acyclic_path_2 (concat u ancu' v (rev lu) (luz1 ++ x :: (rev lv1)))).
                      { apply concat_paths_acyclic.
                        * split. apply Huveq. split.
                          -- apply Hcyclu.
                          -- apply concat_paths_acyclic. split. apply Hvancu'.
                             ++ split. apply subpath_still_acyclic_2 with (v := z) (l2 := luz2) (l3 := luz). split. symmetry. apply Hluz.
                                apply subpath_still_acyclic with (w := u) (l1 := rev lu) (l3 := rev lu ++ [ancu'] ++ luz). split. reflexivity. apply Hcycuz.
                                apply reverse_path_still_acyclic. apply subpath_still_acyclic_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply Hlv. apply Hcycvz.
                             ++ split.
                                ** (* contradiction: then v is an unblocked ancestor of u *)
                                   intros Hancu'. apply membership_rev in Hancu'. rewrite <- reverse_list_twice in Hancu'.
                                   apply membership_splits_list in Hancu'. destruct Hancu' as [lv1' [lv1'' Hlv1]].

                                   assert (Hlv1': forall (x': node), In x' lv1' -> In x' lv).
                                   { intros x' Hxlv1'. apply membership_append with (l2 := [ancu'] ++ lv1'') in Hxlv1'. apply membership_append with (l2 := [x] ++ lv2) in Hxlv1'.
                                     rewrite Hlv. rewrite <- Hlv1. apply Hxlv1'. }

                                   apply no_overlap_non_member with (x := v) in Hover. apply Hover.
                                   --- apply unblocked_ancestors_have_unblocked_directed_path. right. exists (lv1' ++ ancu' :: lu).
                                       split. apply concat_directed_paths. split. apply subpath_still_directed_2 with (v := x) (l2 := lv1'') (l3 := lv1).
                                       split. apply Hlv1. apply subpath_still_directed_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply Hlv. apply Hdirvz.
                                       apply Hdirlu. split. apply concat_paths_acyclic.
                                       +++ split. intros Hvu. apply Huveq. symmetry. apply Hvu. split.
                                           *** apply subpath_still_acyclic_2 with (v := x) (l2 := lv1'') (l3 := lv1). split. apply Hlv1.
                                               apply subpath_still_acyclic_2 with (v := z) (l2 := lv2) (l3 := lv). split. symmetry. apply Hlv. apply Hcycvz.
                                           *** rewrite reverse_list_twice with (l := lu). apply reverse_path_still_acyclic. apply Hcyclu.
                                       +++ split.
                                           *** apply Hvlu.
                                           *** intros Hulv1. apply Hlv1' in Hulv1. apply Hulv. apply Hulv1.
                                       +++ destruct (overlap lv1' lu) as [|] eqn:F. apply overlap_has_member_in_common in F. destruct F as [x' [Hxlv1' Hxlu]].
                                           apply no_overlap_non_member with (x := x') in Hlulv.
                                           *** exfalso. apply Hlulv. apply Hxlu.
                                           *** apply Hlv1'. apply Hxlv1'.
                                           *** reflexivity.
                                       +++ intros w [Hw | Hw]. apply HlvZ'. left. apply Hw. apply membership_append_or in Hw. destruct Hw as [Hw | [Hw | Hw]].
                                           *** apply HlvZ. right. apply Hlv1'. apply Hw.
                                           *** apply HluZ. left. symmetry. apply Hw.
                                           *** apply HluZ. right. left. apply Hw.
                                   --- unfold find_unblocked_ancestors. left. reflexivity.
                                ** intros Hvluz1. 
                                   (* contradicts Hcycx, which passes through both v and luz1 *)
                                   unfold acyclic_path_2 in Hcycx. destruct Hcycx as [_ [_ [Hcycx _]]]. apply Hcycx. apply membership_append. apply Hvluz1.
                             ++ apply overlap_rev. apply Hlu1lv1.
                        * split.
                          -- intros Hu. apply membership_append_or in Hu. destruct Hu as [Hu | [Hu | Hu]].
                             ++ (* contradicts Hcycuz, which starts at u and passes through luz *)
                                unfold acyclic_path_2 in Hcycuz. destruct Hcycuz as [_ [Hcycuz _]]. apply Hcycuz. apply membership_append_r. right. apply membership_append with (l2 := [x] ++ luz2) in Hu. rewrite Hluz. apply Hu.
                             ++ (* contradiction: contradicts Hcycuz, which starts at u and passes through luz *)
                                unfold acyclic_path_2 in Hcycuz. destruct Hcycuz as [_ [Hcycuz _]]. apply Hcycuz. apply membership_append_r. right. rewrite Hluz. apply membership_append_r. apply membership_append. left. apply Hu.
                             ++ apply Hulv. apply membership_rev in Hu. rewrite <- reverse_list_twice in Hu. apply membership_append with (l2 := [x] ++ lv2) in Hu. rewrite Hlv. apply Hu.
                          -- intros Hvlu'. apply Hvlu. apply membership_rev. apply Hvlu'.
                        * destruct (overlap (rev lu) (luz1 ++ x :: rev lv1)) as [|] eqn:F.
                          -- apply overlap_has_member_in_common in F. destruct F as [x' [Hxlu Hx]].
                             apply membership_append_or in Hx. destruct Hx as [Hx | [Hx | Hx]].
                             ++ apply no_overlap_non_member with (x := x') in Hluluz.
                                ** exfalso. apply Hluluz. apply membership_rev. apply Hxlu.
                                ** apply membership_append with (l2 := [x] ++ luz2) in Hx. rewrite Hluz. apply Hx.
                             ++ apply no_overlap_non_member with (x := x) in Hluluz.
                                ** exfalso. apply Hluluz. apply membership_rev. rewrite Hx. apply Hxlu.
                                ** rewrite Hluz. apply membership_append_r. apply membership_append. left. reflexivity.
                             ++ apply no_overlap_non_member with (x := x') in Hlulv.
                                ** exfalso. apply Hlulv. apply membership_rev. apply Hxlu.
                                ** rewrite Hlv. apply membership_append. apply membership_rev. apply Hx.
                          -- reflexivity. }
                      split. apply concat_d_connected_paths.
                      - apply HG.
                      - apply Hpath.
                      - split.
                        + apply reverse_d_connected_paths. apply Hdconn1. split. apply Hdirlu. intros w [Hw | Hw]. apply HluZ. left. apply Hw. apply HluZ. right. left. apply Hw.
                        + split. apply Hconnx. apply Hcyc.
                      - right. left. apply Hanc_con. apply subpath_still_directed_2 with (v := z) (l2 := luz2) (l3 := luz).
                        split. symmetry. apply Hluz. apply Hdirluz. split. apply Hdirlu. apply HluZ. left. reflexivity.
                      - split. apply Hpath. apply Hcyc. }
                     split. unfold concat in Hconn. unfold concat. rewrite <- app_assoc. apply Hconn.
                     right. exists luz2. exists lv2. easy.
              -- split. apply Hdirluz. split. apply subpath_still_acyclic with (w := u) (l1 := rev lu) (l3 := rev lu ++ [ancu'] ++ luz).
                 ++ split. reflexivity. apply Hcycuz.
                 ++ intros w Hw. apply HluZ. destruct Hw as [Hw | Hw]. left. apply Hw. right. right. apply Hw.
              -- split. apply Hdirvz. split. apply Hcycvz. apply HlvZ. }


            (* in a path with structure u <- ..lu.. <- ancu' -> ..luz.. -> z <- ..lv.. <- v, where z is the only node in the path in Z,
               u and v cannot be d-separated *)
            assert (Hconn_con_col: forall (u v ancu': node) (lv lu luz: nodes), z <> v /\ u <> z /\ u <> v
                      -> d_connected_2 (v, z, lv) G Z /\ is_directed_path_in_graph (v, z, lv) G = true /\ acyclic_path_2 (v, z, lv) /\ (forall w : node, w = v \/ In w lv -> ~ In w Z)
                      -> d_connected_2 (u, z, rev lu ++ ancu' :: luz) G Z /\ is_path_in_graph (u, z, rev lu ++ ancu' :: luz) G = true /\ acyclic_path_2 (u, z, rev lu ++ ancu' :: luz)
                         /\ is_directed_path_in_graph (ancu', u, lu) G = true /\ is_directed_path_in_graph (ancu', z, luz) G = true /\ (forall w : node, w = ancu' \/ In w lu \/ In w luz -> ~ In w Z)
                      -> d_separated_bool u v G Z = true
                      -> overlap (find_unblocked_ancestors G u Z) (find_unblocked_ancestors G v Z) = false
                      -> False).
            { intros u v ancu' lv lu luz. intros Heq. intros Hvz. intros Huz. intros Hdsep. intros Hover.
              specialize Hconn_con_col' with (u := u) (v := v) (ancu' := ancu') (lv := lv) (lu := lu) (luz := luz).

              assert (Hcol: exists (x : node) (luz1 lv1 : nodes),
                     (d_connected_2 (concat u x v (rev lu ++ ancu' :: luz1) (rev lv1)) G Z /\
                      is_path_in_graph (concat u x v (rev lu ++ ancu' :: luz1) (rev lv1)) G = true /\
                      acyclic_path_2 (concat u x v (rev lu ++ ancu' :: luz1) (rev lv1))) /\
                     (luz1 = luz /\ lv1 = lv /\ z = x \/
                      (exists luz2 lv2 : nodes, luz = luz1 ++ [x] ++ luz2 /\ lv = lv1 ++ [x] ++ lv2))).
              { apply Hconn_con_col'. easy. easy. easy. easy. }
              destruct Hcol as [x [luz1 [lvz1 [Hpath Hcol]]]].
              unfold concat in Hpath. apply d_connected_path_not_d_separated with (l := (rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) in Hdsep.
              + exfalso. apply Hdsep.
              + apply Hpath.
              + apply Hpath. }

            destruct HzZ as [HzZ Hnodez].
            assert (Hzv: z <> v'). { intros Hzv. rewrite Hzv in HzZ. destruct HZ as [_ [_ [_ HZ]]]. apply member_In_equiv in HzZ. rewrite HzZ in HZ. discriminate HZ. }
            assert (Hzu: u' <> z). { intros Hzu. rewrite <- Hzu in HzZ. destruct HZ as [_ [_ [HZ _]]]. apply member_In_equiv in HzZ. rewrite HzZ in HZ. discriminate HZ. }
            pose proof Hdsep' as Hdsep. clear Hdsep'. pose proof Hover' as Hover. clear Hover'. pose proof Hequv' as Huveq. clear Hequv'.
            remember u' as u. remember v' as v.

            apply Hconvz in Hzv as Hzv'. clear Hconvz. destruct Hzv' as [Hvlz | [Hzlv | Hconvz]].
            + destruct Hvlz as [lv [Hconnvz [Hdirvz [Hcycvz HlvZ]]]]. (* z <- ..lv.. <- v *)
              pose proof Hdconn_con as Hconuz. specialize Hconuz with (anc := ancu) (u := u) (v := z).
              apply Hconuz in Hzu as Hzu'. clear Hconuz. destruct Hzu' as [Hzlu | [Hulz | Hconuz]].
              * destruct Hzlu as [lz [Hconnzu [Hdirzu [Hcyczu HlzZ]]]]. (* u <- ..lz.. <- z *)
                (* contradiction, HlzZ says z is not in Z. *)
                specialize HlzZ with (w := z). exfalso. apply HlzZ. left. reflexivity. apply HzZ.
              * destruct Hulz as [lu [Hconnuz [Hdiruz [Hcycuz HluZ]]]].
                (* u -> ..lu.. -> z <- ..lv.. <- v *)
                assert (Hconn: exists (l: nodes), d_connected_2 (u, v, l) G Z /\ is_path_in_graph (u, v, l) G = true /\ acyclic_path_2 (u, v, l)).
                { assert (Hcol: is_path_in_graph (concat u z v lu (rev lv)) G = true /\
                                acyclic_path_2 (concat u z v lu (rev lv)) /\
                                d_connected_2 (concat u z v lu (rev lv)) G Z \/
                                (exists (lu1 lu2 lv' lv1 lv2 : nodes) (x : node),
                                   is_directed_path_in_graph (v, z, lv') G = true /\
                                   acyclic_path_2 (v, z, lv') /\
                                   (forall w : node, w = v \/ In w lv' -> ~ In w Z) /\
                                   lu = lu1 ++ [x] ++ lu2 /\
                                   lv = lv1 ++ [x] ++ lv2 /\
                                   lv' = lv1 ++ [x] ++ lu2 /\
                                   overlap lu1 lv1 = false /\
                                   d_connected_2 (u, v, lu1 ++ [x] ++ rev lv1) G Z /\
                                   is_path_in_graph (u, v, lu1 ++ [x] ++ rev lv1) G = true /\
                                   acyclic_path_2 (u, v, lu1 ++ [x] ++ rev lv1))).
                  { apply Hconn_col.
                    - split. apply HzZ. split. apply Huveq. apply Hover.
                    - split. apply Hdiruz. split. apply Hcycuz. apply HluZ.
                    - split. apply Hdirvz. split. apply Hcycvz. apply HlvZ. }
                  destruct Hcol as [[Hpath [Hcyc Hconn]] | [lu'' [l [lv' [lv'' [l' [x [_ [_ [_ [_ [_ [_ [_ Hcol]]]]]]]]]]]]]].
                  - exists (lu ++ z :: (rev lv)). split. apply Hconn. split. apply Hpath. apply Hcyc.
                  - exists (lu'' ++ [x] ++ (rev lv'')). apply Hcol. }
                exfalso. destruct Hconn as [l Hconn]. apply d_connected_path_not_d_separated with (u := u) (v := v) (l := l) (G := G) (Z := Z).
                ** apply Hconn.
                ** apply Hconn.
                ** apply Hdsep.
              * destruct Hconuz as [lu [luz [ancu' [Hconnuz [Hpathuz [Hdirlu [Hdirluz [Hcycuz HluZ]]]]]]]].
                (* u <- ..lu.. <- ancu' -> ..luz.. -> z <- ..lv.. <- v *)
                exfalso. specialize Hconn_con_col with (u := u) (v := v) (ancu' := ancu') (lv := lv) (lu := lu) (luz := luz).
                apply Hconn_con_col. easy. easy. easy. easy. easy.
              * split. apply Hancuz. apply Hancu.
            + destruct Hzlv as [lz [Hconnzv [Hdirzv [Hcyczv HlzZ]]]].
              (* contradiction, HlzZ says z is not in Z. *)
              specialize HlzZ with (w := z). exfalso. apply HlzZ. left. reflexivity. apply HzZ.
            + destruct Hconvz as [lvz [lv [ancv' [Hconnzv [Hpathzv [Hdirlvz [Hdirlv [Hcyczv HlvZ]]]]]]]].
              (* z <- ..lvz.. <- ancv' -> ..lv.. -> v *)
              pose proof Hdconn_con as Hconuz. specialize Hconuz with (anc := ancu) (u := u) (v := z).
              apply Hconuz in Hzu as Hzu'. clear Hconuz. destruct Hzu' as [Hzlu | [Hulz | Hconuz]].
              * destruct Hzlu as [lz [Hconnzu [Hdirzu [Hcyczu HlzZ]]]]. (* u <- ..lz.. <- z *)
                (* contradiction, HlzZ says z is not in Z. *)
                specialize HlzZ with (w := z). exfalso. apply HlzZ. left. reflexivity. apply HzZ.
              * destruct Hulz as [lu [Hconnuz [Hdiruz [Hcycuz HluZ]]]].
                (* u -> ..lu.. -> z <- ..lvz.. <- ancv' -> ..lv.. -> v *)
                exfalso. specialize Hconn_con_col with (u := v) (v := u) (ancu' := ancv') (lv := lu) (lu := lv) (luz := lvz).
                apply Hconn_con_col. easy. easy.
                rewrite reverse_list_twice with (l := rev lv ++ ancv' :: lvz). rewrite reverse_list_append. rewrite <- reverse_list_twice.
                split.
                -- apply reverse_d_connected_paths. simpl. rewrite <- app_assoc. apply Hconnzv.
                -- split.
                   ++ simpl. apply reverse_path_in_graph. rewrite append_vs_concat. apply Hpathzv.
                   ++ split. simpl. apply reverse_path_still_acyclic. rewrite append_vs_concat. apply Hcyczv.
                      split. easy. split. easy. intros w Hw. apply HlvZ. destruct Hw as  [Hw | [Hw | Hw]].
                      left. apply Hw. right. right. apply Hw. right. left. apply Hw.
                -- apply d_separated_symmetry. apply Hdsep.
                -- apply overlap_flip. apply Hover.
              * destruct Hconuz as [lu [luz [ancu' [Hconnuz [Hpathuz [Hdirlu [Hdirluz [Hcycuz HluZ]]]]]]]].
                assert (Hvancv': is_directed_path_in_graph (ancv', v, lv) G = true /\ acyclic_path_2 (ancv', v, lv) /\ (forall w : node, w = ancv' \/ In w lv -> ~ In w Z)).
                { split. apply Hdirlv. split.
                  - apply subpath_still_acyclic with (w := z) (l1 := rev lvz) (l3 := rev lvz ++ [ancv'] ++ lv).
                    split. reflexivity. apply Hcyczv.
                  - intros w Hw. apply HlvZ. rewrite <- or_assoc. rewrite or_comm. rewrite <- or_assoc. left. rewrite or_comm. apply Hw. }
                assert (Huancu': is_directed_path_in_graph (ancu', u, lu) G = true /\ acyclic_path_2 (ancu', u, lu) /\ (forall w : node, w = ancu' \/ In w lu -> ~ In w Z)).
                { split. apply Hdirlu. split.
                  ++ rewrite reverse_list_twice with (l := lu). apply reverse_path_still_acyclic.
                     apply subpath_still_acyclic_2 with (v := z) (l2 := luz) (l3 := rev lu ++ [ancu'] ++ luz).
                     split. reflexivity. apply Hcycuz.
                  ++ intros w Hw. apply HluZ. rewrite <- or_assoc. left. apply Hw. }
                assert (Hzancu': is_directed_path_in_graph (ancu', z, luz) G = true /\ acyclic_path_2 (ancu', z, luz) /\ (forall w : node, w = ancu' \/ In w luz -> ~ In w Z)).
                { split. apply Hdirluz. split. apply subpath_still_acyclic with (w := u) (l1 := rev lu) (l3 := rev lu ++ [ancu'] ++ luz). split. reflexivity. apply Hcycuz.
                  intros w [Hw | Hw]. apply HluZ. left. apply Hw. apply HluZ. right. right. apply Hw. }

                (* u <- ..lu.. <- ancu' -> ..luz.. -> z <- ..lvz.. <- ancv' -> ..lv.. -> v *)
                specialize Hconn_con_col' with (u := u) (v := ancv') (ancu' := ancu') (lv := lvz) (lu := lu) (luz := luz).
                assert (Hcol: exists (x : node) (luz1 lv1 : nodes),
                     (d_connected_2
                        (concat u x ancv' (rev lu ++ ancu' :: luz1) (rev lv1)) G Z /\
                      is_path_in_graph
                        (concat u x ancv' (rev lu ++ ancu' :: luz1) (rev lv1)) G =
                      true /\
                      acyclic_path_2
                        (concat u x ancv' (rev lu ++ ancu' :: luz1) (rev lv1))) /\
                     (luz1 = luz /\ lv1 = lvz /\ z = x \/
                      (exists luz2 lv2 : nodes,
                         luz = luz1 ++ [x] ++ luz2 /\ lvz = lv1 ++ [x] ++ lv2))).
                { apply Hconn_con_col'.
                  - repeat split.
                    + intros Hancvz'. apply HlvZ with (w := z). left. apply Hancvz'. apply HzZ.
                    + apply Hzu.
                    + (* else, u is an unblocked ancestor of v *) intros F. apply no_overlap_non_member_rev with (x := u) in Hover.
                      { apply Hover. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lv.
                        rewrite F in *. apply Hvancv'. }
                      { unfold find_unblocked_ancestors. left. reflexivity. }
                  - split.
                    + apply Hdconn1. split. apply Hdirlvz. intros w Hw. apply HlvZ. rewrite <- or_assoc. left. apply Hw.
                    + split. apply Hdirlvz. split.
                      * rewrite reverse_list_twice with (l := lvz). apply reverse_path_still_acyclic.
                        apply subpath_still_acyclic_2 with (v := v) (l2 := lv) (l3 := rev lvz ++ [ancv'] ++ lv).
                        split.  reflexivity. apply Hcyczv.
                      * intros w Hw. apply HlvZ. rewrite <- or_assoc. left. apply Hw.
                  - easy.
                  - (* otherwise, u and v would have a common unblocked ancestor *) apply overlap_flip. apply no_common_unblocked_ancestors_transitive with (u := v).
                    split. apply overlap_flip. apply Hover. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lv. easy. }
                unfold concat in Hcol. destruct Hcol as [x [luz1 [lvz1 Hcol]]]. destruct Hcol as [[Hconnu [Hpathu Hcycu]] Hcol].
                assert (Hconn: d_connected_2 (concat u ancv' v ((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) lv) G Z
                                  /\ is_path_in_graph (concat u ancv' v ((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) lv) G = true
                                  /\ acyclic_path_2 (concat u ancv' v ((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) lv)).
                { assert (Hpath: is_path_in_graph (concat u ancv' v ((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) lv) G = true).
                  { apply concat_paths_still_a_path. split. apply Hpathu. apply directed_path_is_path. apply Hdirlv. }
                  assert (Hcyc: acyclic_path_2 (concat u ancv' v ((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) lv)).
                  { apply concat_paths_acyclic.
                    - split. apply Huveq. split. apply Hcycu. apply subpath_still_acyclic with (w := z) (l1 := rev lvz) (l3 := rev lvz ++ [ancv'] ++ lv).
                      split. reflexivity. apply Hcyczv.
                    - split.
                      + (* contradiction: then u is an unblocked ancestor of v *)
                        intros Hu.
                        apply no_overlap_non_member with (x := u) in Hover.
                        ++ apply Hover. unfold find_unblocked_ancestors. left. reflexivity.
                        ++ apply unblocked_ancestor_if_in_unblocked_directed_path with (anc := ancv') (l := lv).
                           ** easy.
                           ** apply Hu.
                      + intros Hvmem. apply membership_append_or in Hvmem. destruct Hvmem as [Hvmem | Hmem].
                        * apply membership_append_or in Hvmem. destruct Hvmem as [Hvmem | Hmem].
                          -- apply no_overlap_non_member with (x := v) in Hover. (* contradiction: then v is an unblocked ancestor of u *)
                             apply Hover.
                             apply unblocked_ancestor_if_in_unblocked_directed_path with (anc := ancu') (l := lu).
                             ** apply Huancu'.
                             ** apply membership_rev. apply Hvmem.
                             ** unfold find_unblocked_ancestors. left. reflexivity.
                          -- destruct Hmem as [F | F].
                             { apply no_overlap_non_member with (x := v) in Hover.
                               - apply Hover. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lu. rewrite <- F. apply Huancu'.
                               - unfold find_unblocked_ancestors. left. reflexivity. }
                             { (* contradiction: then ancu' is a common ancestor of u and v *)
                               apply no_overlap_non_member with (x := ancu') in Hover.
                               - apply Hover. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lu. apply Huancu'.
                               - apply unblocked_ancestors_have_unblocked_directed_path. right. apply membership_splits_list in F. destruct F as [luz1' [luz1'' Hluz1]]. exists luz1'.
                                 destruct Hcol as [Hcol | Hcol].
                                 + destruct Hcol as [Hcol _]. rewrite Hcol in *. split. apply subpath_still_directed_2 with (v := z) (l2 := luz1'') (l3 := luz). split. apply Hluz1.
                                   apply Hdirluz. split. apply subpath_still_acyclic_2 with (v := z) (l2 := luz1'') (l3 := luz). split. apply Hluz1. apply Hzancu'.
                                   intros w Hw. destruct Hzancu' as [_ [_ Hzancu']]. apply Hzancu'. destruct Hw as [Hw | Hw]. left. apply Hw. right. apply membership_append with (l2 := [v] ++ luz1'') in Hw. rewrite <- Hluz1. apply Hw.
                                 + destruct Hcol as [luz2 [_ [Hluz _]]]. split. apply subpath_still_directed_2 with (v := x) (l2 := luz1'') (l3 := luz1). split. apply Hluz1.
                                   apply subpath_still_directed_2 with (v := z) (l2 := luz2) (l3 := luz). split. symmetry. apply Hluz. apply Hdirluz.
                                   split. apply subpath_still_acyclic_2 with (v := x) (l2 := luz1'') (l3 := luz1). split. apply Hluz1.
                                   apply subpath_still_acyclic_2 with (v := z) (l2 := luz2) (l3 := luz). split. symmetry. apply Hluz. apply Hzancu'.
                                   intros w Hw. destruct Hzancu' as [_ [_ Hzancu']]. apply Hzancu'. destruct Hw as [Hw | Hw]. left. apply Hw. right. apply membership_append with (l2 := [v] ++ luz1'') in Hw. rewrite Hluz. rewrite <- Hluz1. apply membership_append. apply Hw. }
                        * unfold acyclic_path_2 in Hcyczv. destruct Hcol as [Hcol | Hcol].
                          -- destruct Hmem as [Hmem | Hmem]. destruct Hcyczv as [Hcyczv _]. apply Hcyczv. destruct Hcol as [_ [_ Hcol]]. rewrite Hcol. apply Hmem.
                             destruct Hcyczv as [_ [_ [Hcycvz _]]]. apply Hcycvz. apply membership_append. destruct Hcol as [_ [Hcol _]]. rewrite Hcol in Hmem. apply Hmem.
                          -- destruct Hcyczv as [_ [_ [Hcycvz _]]]. apply Hcycvz. apply membership_append. destruct Hcol as [_ [lvz2 [_ Hluz]]]. rewrite Hluz.
                             rewrite app_assoc. rewrite reverse_list_append. apply membership_append_r. rewrite reverse_list_append. simpl. simpl in Hmem. apply Hmem.
                    - apply no_overlap_non_member. intros x' Hxlv Hx'.
                      assert (Hxv': In x' (find_unblocked_ancestors G v Z)).
                      { apply unblocked_ancestor_if_in_unblocked_directed_path with (anc := ancv') (l := lv). apply Hvancv'. apply Hxlv. }
                      rewrite <- append_vs_concat in Hx'. apply membership_append_or in Hx'. destruct Hx' as [Hx' | Hx'].
                      + (* contradiction: ancu' is a shared unblocked ancestor of u and v *)
                        assert (Hxu': In ancu' (find_unblocked_ancestors G v Z)).
                        { apply unblocked_ancestors_transitive with (ancu' := x'). apply Hxv'.
                          apply membership_append_or in Hx'; destruct Hx' as [Hx' | Hx']. apply membership_append_or in Hx'; destruct Hx' as [Hx' | Hx'].
                          - apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := u) (l := lu). apply Huancu'. apply membership_rev. apply Hx'.
                          - destruct Hx' as [Hx' | Hx']. apply unblocked_ancestors_have_unblocked_directed_path. left. apply Hx'.
                            apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := luz). apply Hzancu'.
                            destruct Hcol as [Hcol | Hcol].
                            + destruct Hcol as [Hcol _]. rewrite <- Hcol. apply Hx'.
                            + destruct Hcol as [luz2 [_ [Hluz _]]]. rewrite Hluz. apply membership_append. apply Hx'.
                          - destruct Hcol as [Hcol | Hcol].
                            + simpl in Hx'. destruct Hx' as [Hx' | F]. rewrite <- Hx'. destruct Hcol as [_ [_ Hcol]]. rewrite <- Hcol.
                              apply unblocked_ancestors_have_unblocked_directed_path. right. exists luz. apply Hzancu'. exfalso. apply F.
                            + apply unblocked_ancestor_if_in_unblocked_directed_path_2 with (v := z) (l := luz). apply Hzancu'.
                              destruct Hcol as [luz2 [_ [Hluz _]]]. rewrite Hluz. apply membership_append_r. apply membership_append. apply Hx'. }
                        apply no_overlap_non_member with (x := ancu') in Hover.
                        * apply Hover. apply unblocked_ancestors_have_unblocked_directed_path. right. exists lu. apply Huancu'.
                        * apply Hxu'.
                      + (* contradicts Hcyczv *)
                        apply acyclic_path_correct in Hcyczv. simpl in Hcyczv. apply split_and_true in Hcyczv; destruct Hcyczv as [_ Hcyczv]. apply split_and_true in Hcyczv; destruct Hcyczv as [_ Hcyczv].
                        apply acyclic_path_intermediate_nodes with (p := rev lvz ++ ancv' :: lv) (x := x') in Hcyczv. destruct Hcyczv as [Hc | Hc].
                        ** rewrite count_app in Hc. apply member_count_at_least_1 in Hxlv. apply membership_rev in Hx'. rewrite <- reverse_list_twice in Hx'.
                           apply member_count_at_least_1 in Hx'. simpl in Hc. destruct (ancv' =? x') as [|]. lia. lia.
                        ** destruct Hcol as [Hcol | Hcol].
                           -- destruct Hcol as [_ [Hcol _]]. rewrite Hcol in Hx'. apply member_count_at_least_1 in Hx'. rewrite <- count_reverse in Hx'. apply member_count_at_least_1 in Hxlv.
                              rewrite count_app in Hc. rewrite count_reverse in Hc. rewrite <- reverse_list_twice in Hc. simpl in Hc. destruct (ancv' =? x') as [|]. lia. lia.
                           -- destruct Hcol as [_ [lvz2 [_ Hlvz]]]. apply <- membership_rev in Hx'. rewrite <- reverse_list_twice in Hx'. apply membership_append with (l2 := [x] ++ lvz2) in Hx'. rewrite <- Hlvz in Hx'.
                              apply member_count_at_least_1 in Hx'. apply member_count_at_least_1 in Hxlv. rewrite count_app in Hc. simpl in Hc. rewrite count_reverse in Hc. rewrite <- reverse_list_twice in Hc. destruct (ancv' =? x') as [|]. lia. lia. }
                  split.
                  - apply concat_d_connected_paths.
                    + apply HG.
                    + apply Hpath.
                    + split. apply Hconnu. split.
                      * apply Hdconn1. split. apply Hvancv'. apply Hvancv'.
                      * apply Hcyc.
                    + right. left. split.
                      * assert (Hcon: In ancv' (find_confounders_in_path (concat v ancv' ancu' (rev lv) (lvz1 ++ x :: rev luz1)) G) /\ ~(In ancv' Z)).
                        { specialize Hanc_con with (u := v) (ancu' := ancv') (z := x) (v := ancu') (lu := lv) (luz := lvz1) (lv := luz1). apply Hanc_con.
                          - destruct Hcol as [Hcol | Hcol].
                            + destruct Hcol as [_ [Hlvz Hzx]]. rewrite Hlvz. rewrite <- Hzx. apply Hdirlvz.
                            + destruct Hcol as [luz2 [lvz2 [Hluz Hlvz]]]. apply subpath_still_directed_2 with (v := z) (l2 := lvz2) (l3 := lvz). split. symmetry. apply Hlvz. apply Hdirlvz.
                          - split. apply Hvancv'. apply HlvZ. left. reflexivity. }
                        unfold concat in Hcon. destruct Hcon as [Hcon Hancv']. apply confounders_same_in_reverse_path in Hcon. rewrite reverse_list_append in Hcon.
                        rewrite <- reverse_list_twice in Hcon.
                        apply concat_preserves_confounders_r with (u := u) (l1 := rev lu) in Hcon.
                        unfold concat in Hcon. unfold concat.
                        replace (((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) ++ ancv' :: lv) with (rev lu ++ ancu' :: rev (ancv' :: lvz1 ++ x :: rev luz1) ++ lv).
                        -- apply Hcon.
                        -- simpl. rewrite reverse_list_append. simpl. rewrite <- reverse_list_twice. simpl. rewrite <- app_assoc. clear Hconn_con_col. clear Hconn_con_col'. clear Hconn_col. clear Hdconn_con.
                           rewrite <- append_vs_concat. rewrite <- app_assoc. simpl. rewrite <- app_assoc. rewrite <- app_assoc. simpl.
                           replace ((rev lu ++ ancu' :: luz) ++ x :: rev lvz) with (rev lu ++ ancu' :: luz ++ x :: rev lvz). repeat rewrite <- app_assoc.
                           simpl. reflexivity.
                           rewrite <- app_assoc. simpl. reflexivity.
                      * apply HlvZ. left. reflexivity.
                  - split. apply Hpath. apply Hcyc. }
                unfold concat in Hconn. apply d_connected_path_not_d_separated with (l := ((rev lu ++ ancu' :: luz1) ++ x :: rev lvz1) ++ ancv' :: lv) in Hdsep.
                -- exfalso. apply Hdsep.
                -- apply Hconn.
                -- apply Hconn.
              * split. apply Hancuz. apply Hancu.
            + split. apply Hancv. apply Hancvz. } }
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
      (* need to update for new definition of conditionally_independent; before, could just do "contradiction." *)
      admit. }
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
    apply find_descendants_correct in Hdesc. destruct Hdesc as [F | Hdesc].
    apply edge_from_parent_to_child in Hparent. rewrite F in Hparent. apply acyclic_no_self_loop with (u := P) in Hacyc.
    apply edge_in_graph_then_is_edge in Hparent. rewrite Hparent in Hacyc. discriminate Hacyc. apply HG.
    destruct Hdesc as [U [Hdir HUse]].
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
  - destruct G as [V E]. simpl in Ho.
    destruct Hedge as [Hedge | Hedge].
    { left. split.
    + destruct Hedge as [Hyx _]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hyx.
    + destruct Hedge as [_ Hxz]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hxz. }
    { right. split.
    + destruct Hedge as [Hyx _]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hyx.
    + destruct Hedge as [_ Hxz]. apply duplicate_graph_maintains_edges.
      * simpl. apply Ho.
      * apply Hxz. } }
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
    - destruct Hedge as [Hedge | Hedge].
      { left. split.
      + destruct Hedge as [Hedge _]. apply duplicate_graph_maintains_edges with (o := o).
        * apply Ho.
        * rewrite <- Hy in Hedge. apply Hedge.
      + destruct Hedge as [_ Hedge]. apply duplicate_graph_maintains_edges with (o := o).
        * apply Ho.
        * rewrite <- Hz in Hedge. apply Hedge. }
      { right. split.
      + destruct Hedge as [Hedge _]. apply duplicate_graph_maintains_edges with (o := o).
        * apply Ho.
        * rewrite <- Hy in Hedge. apply Hedge.
      + destruct Hedge as [_ Hedge]. apply duplicate_graph_maintains_edges with (o := o).
        * apply Ho.
        * rewrite <- Hz in Hedge. apply Hedge. } }
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
  - intros Hd. apply find_descendants_correct in Hd. destruct Hd as [Hd | Hd].
    apply find_descendants_correct. left. lia.
    destruct Hd as [p [Hdir Hse]].
    destruct p as [[u' d'] l]. apply path_start_end_equal in Hse. destruct Hse as [Hu Hd].
    apply find_descendants_correct. right.
    exists (u + o, d + o, shift_nodes_by_offset l o). split.
    + rewrite Hu in Hdir. rewrite Hd in Hdir.
      apply duplicate_graph_maintains_dir_paths with (o := o) in Hdir. apply Hdir. apply Ho.
    + apply path_start_end_refl.
  - intros Hd. apply find_descendants_correct in Hd. destruct Hd as [Hd | Hd].
    apply find_descendants_correct. left. lia.
    destruct Hd as [p' [Hdir Hse]].
    destruct p' as [[u' d'] l'].
    apply duplicate_graph_shifts_dir_paths with (o := o) in Hdir as Huvl.
    destruct Huvl as [u1 [d1 [l [Hu1 [Hd1 Hl]]]]].
    apply path_start_end_equal in Hse. destruct Hse as [Hu Hd].
    + apply find_descendants_correct. right. exists (u, d, l). split.
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




