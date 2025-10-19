From CausalDiagrams Require Import IntermediateNodes.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.

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

Lemma path_into_start_induction_rev: forall (u v h: node) (t: nodes) (G: graph),
  path_into_start (u, v, rev (h :: t)) G = path_into_start (u, h, rev t) G.
Proof.
  intros u v h t G. simpl.
  induction (rev t) as [| h' t' IH].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

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

Lemma path_out_of_node_mem_gen: forall (l: nodes) (u v x: node) (G: graph),
  In x (u :: l) <-> exists (b: bool), path_out_of_node x (u, v, l) G = Some b.
Proof.
  intros l u v x G. split.
  { intros Hmem. unfold path_out_of_node. apply path_out_of_node_mem_2. apply Hmem. }
  { intros [b Hb]. unfold path_out_of_node in Hb. generalize dependent u. induction l as [| h t IH].
    - intros u Hb. simpl in Hb. destruct (u =? x) as [|] eqn:Hux. left. apply eqb_eq in Hux. apply Hux. discriminate Hb.
    - intros u Hb. simpl in Hb. destruct (u =? x) as [|] eqn:Hux. left. apply eqb_eq. apply Hux. right. apply IH. apply Hb. }
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

Theorem superpath_preserves_path_out_of_node_2: forall (w u v a: node) (l1 l2 l3: nodes) (G: graph) (b: bool),
  l1 ++ [u] ++ l2 = l3
  -> path_out_of_node a (w, v, l3) G = Some b
  -> In a (w :: l1)
  -> path_out_of_node a (w, u, l1) G = Some b.
Proof.
  intros w u v a l1 l2 l3 G b. intros Hl Ha Hmem. unfold path_out_of_node in *.

  generalize dependent l3. generalize dependent w. induction l1 as [| h1 t1 IH].
  - intros w Hwa l3 Hl Hb. simpl in Hl. simpl in Hb. simpl. rewrite <- Hl in Hb. simpl in Hb.
    destruct Hwa as [Hwa | Hwa]. rewrite Hwa in *. rewrite eqb_refl in *. apply Hb. exfalso. apply Hwa.
  - intros w Hwa l3 Hl Hb. rewrite <- Hl in Hb. simpl in Hb. simpl. destruct (w =? a) as [|] eqn:Hwa'.
    + apply Hb.
    + destruct Hwa as [Hwa | Hwa]. rewrite Hwa in Hwa'. rewrite eqb_refl in Hwa'. discriminate Hwa'.
      apply IH with (l3 := t1 ++ [u] ++ l2). apply Hwa. reflexivity. apply Hb.
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

Theorem subpath_preserves_path_out_of_node_2: forall (w u v a: node) (l1 l2 l3: nodes) (G: graph) (b: bool),
  l1 ++ [u] ++ l2 = l3 /\ path_out_of_node a (w, u, l1) G = Some b
  -> path_out_of_node a (w, v, l3) G = Some b.
Proof.
  intros w u v a l1 l2 l3 G b. intros [Hl Hb]. unfold path_out_of_node in *.
  generalize dependent w. generalize dependent l3. induction l1 as [| hl1 tl1 IH].
  - intros l3 Hl w Hb. simpl. simpl in Hb. rewrite <- Hl. simpl.
    destruct (w =? a) as [|]. apply Hb. discriminate Hb.
  - intros l3 Hl w Hb. simpl. simpl in Hb. rewrite <- Hl. simpl. destruct (w =? a) as [|]. apply Hb. simpl in IH. apply IH.
    reflexivity. apply Hb.
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

Lemma path_out_in_directed_path: forall (u v x: node) (l: nodes) (G: graph),
  G_well_formed G = true
  -> is_directed_path_in_graph (u, v, l) G = true
  -> In x (u :: l)
  -> path_out_of_node x (u, v, l) G = Some true.
Proof.
  intros u v x l G. intros HG Hdir Hmem.
  generalize dependent u. induction l as [| h t IH].
  - intros u Hdir Hmem. simpl in Hdir. unfold path_out_of_node. simpl. destruct Hmem as [Hmem | F]. apply eqb_eq in Hmem. rewrite Hmem.
    rewrite <- edge_in_graph_equiv. rewrite andb_comm in Hdir. simpl in Hdir. rewrite Hdir. reflexivity. apply HG. exfalso. apply F.
  - intros u Hdir Hmem. destruct (u =? x) as [|] eqn:Hux.
    + simpl in Hdir. unfold path_out_of_node. simpl. rewrite Hux.
      rewrite <- edge_in_graph_equiv. apply split_and_true in Hdir. destruct Hdir as [Hdir _]. rewrite Hdir. reflexivity. apply HG.
    + destruct Hmem as [Hmem | Hmem]. apply eqb_eq in Hmem. rewrite Hmem in Hux. discriminate Hux.
      unfold path_out_of_node. simpl. rewrite Hux. apply IH. simpl in Hdir. apply split_and_true in Hdir. apply Hdir. apply Hmem.
Qed.

Lemma path_out_in_directed_path_rev: forall (u v x: node) (l: nodes) (G: graph),
  G_well_formed G = true /\ contains_cycle G = false
  -> is_directed_path_in_graph (v, u, rev l) G = true
  -> In x (u :: l)
  -> path_out_of_node x (u, v, l) G = Some false.
Proof.
  intros u v x l G. intros HG Hdir Hmem.
  generalize dependent u. induction l as [| h t IH].
  - intros u Hdir Hmem. simpl in Hdir. unfold path_out_of_node. simpl. destruct Hmem as [Hmem | F]. apply eqb_eq in Hmem. rewrite Hmem.
    rewrite <- edge_in_graph_equiv. rewrite andb_comm in Hdir. simpl in Hdir. apply acyclic_no_two_cycle in Hdir. rewrite Hdir. reflexivity. apply HG. apply HG. exfalso. apply F.
  - intros u Hdir Hmem. destruct (u =? x) as [|] eqn:Hux.
    + assert (Hdir': is_directed_path_in_graph (h, u, []) G = true). { apply subpath_still_directed with (w := v) (l1 := rev t) (l3 := rev t ++ [h]). split. reflexivity. apply Hdir. }
      unfold path_out_of_node. simpl. rewrite Hux.
      rewrite <- edge_in_graph_equiv. simpl in Hdir'. rewrite andb_comm in Hdir'. simpl in Hdir'. apply acyclic_no_two_cycle in Hdir'. rewrite Hdir'. reflexivity. apply HG. apply HG.
    + destruct Hmem as [Hmem | Hmem]. apply eqb_eq in Hmem. rewrite Hmem in Hux. discriminate Hux.
      unfold path_out_of_node. simpl. rewrite Hux. apply IH.
      apply subpath_still_directed_2 with (v := u) (l2 := []) (l3 := rev t ++ [h]). split. reflexivity. apply Hdir. apply Hmem.
Qed.

Lemma path_out_of_end_same: forall (G: graph) (u h v: node) (t: nodes),
  path_out_of_end (u, v, h :: t) G = path_out_of_end (h, v, t) G.
Proof.
  intros G u h v t.
  destruct t as [| h' t'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma subpath_preserves_path_out_of_end: forall (G: graph) (u w v: node) (l l1 l2: nodes),
  l = l1 ++ [w] ++ l2
  -> path_out_of_end (u, v, l) G = path_out_of_end (w, v, l2) G.
Proof.
  intros G u w v l l1 l2 Hl.
  generalize dependent l. generalize dependent u. induction l1 as [| hl1 tl1 IH].
  - intros u l Hl. rewrite Hl. simpl. destruct l2 as [| hl2 tl2]. simpl. reflexivity. simpl. reflexivity.
  - intros u l Hl. rewrite Hl. simpl. destruct tl1 as [| hl1' tl1']. simpl. apply IH with (u := hl1) (l := w :: l2). reflexivity.
    simpl. apply IH with (u := hl1) (l := hl1' :: tl1' ++ [w] ++ l2). reflexivity.
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


Lemma directed_path_into_end: forall (u v: node) (l: nodes) (G: graph),
  contains_cycle G = false
  -> is_directed_path_in_graph (u, v, l) G = true
  -> path_out_of_end (u, v, l) G = Some false.
Proof.
  intros u v l G HG Hdir.
  generalize dependent u. induction l as [| h t IH].
  - intros u Hdir. simpl. simpl in Hdir. rewrite andb_comm in Hdir. simpl in Hdir. apply acyclic_no_two_cycle in Hdir. f_equal. apply Hdir. apply HG.
  - intros u Hdir. rewrite path_out_of_end_same. apply IH. simpl in Hdir. apply split_and_true in Hdir. apply Hdir.
Qed.

Lemma path_out_of_end_edge: forall (u v: node) (l: nodes) (G: graph),
  contains_cycle G = false
  -> is_path_in_graph (u, v, l) G = true
  -> path_out_of_end (u, v, l) G = Some false
  -> exists (x: node) (l': nodes), l' ++ [x] = u :: l /\ is_edge (x, v) G = true.
Proof.
  intros u v l G HG Hp Hout.
  generalize dependent u. induction l as [| h t IH].
  - intros u Hp Hout. exists u. exists []. split. reflexivity.
    simpl in Hp. simpl in Hout. inversion Hout. rewrite H0 in Hp. rewrite orb_comm in Hp. simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. apply Hp.
  - intros u Hp Hout. rewrite path_out_of_end_same in Hout. apply IH in Hout. 2: { apply is_path_in_graph_induction with (u := u). apply Hp. }
    destruct Hout as [x [l' Hout]]. exists x. exists (u :: l'). split.
    + simpl. destruct Hout as [Hout _]. rewrite Hout. reflexivity.
    + apply Hout.
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

Lemma sublist_path_out_of_end_false: forall (x v h: node) (t: nodes) (G: graph),
  is_edge (v, x) G = false
  -> sublist [x; v] (h :: t ++ [v]) = true
  -> ~(In v (h :: t))
  -> path_out_of_end (h, v, t) G = Some false.
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