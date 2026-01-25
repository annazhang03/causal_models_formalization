From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.

Import ListNotations.

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
    assert (Hpath: is_directed_path_in_graph (u, u, [x]) G = true).
    { simpl. rewrite H1. rewrite H3. simpl. reflexivity. }
    apply contains_cycle_false_correct in Hpath.
    + simpl in Hpath. destruct Hpath as [contra _]. unfold not in contra.
      exfalso. apply contra. reflexivity.
    + admit.
    + apply Hcyc.
  - reflexivity. }
  { destruct (is_collider_bool u v x G) as [|] eqn:Hcol.
  - unfold is_collider_bool in Hcol. apply split_and_true in Hcol. destruct Hcol as [H3 H4].
    assert (Hpath: is_directed_path_in_graph (v, v, [x]) G = true).
    { simpl. rewrite H2. rewrite H4. simpl. reflexivity. }
    apply contains_cycle_false_correct in Hpath.
    + simpl in Hpath. destruct Hpath as [contra _]. unfold not in contra.
      exfalso. apply contra. reflexivity.
    + admit.
    + apply Hcyc.
  - reflexivity. }
Admitted.

Theorem if_mediator_then_not_confounder_path: forall (G: graph) (u: node) (p: path),
  contains_cycle G = false
  -> acyclic_path_2 p
  -> In u (find_mediators_in_path p G)
  -> ~(In u (find_confounders_in_path p G)) /\ ~(In u (find_colliders_in_path p G)).
Proof.
  intros G w [[u v] l] HG Hc Hu.
  split.
  - intros Hu'. apply mediators_vs_edges_in_path in Hu. destruct Hu as [y [z [Hsub1 Hedge1]]].
    apply confounders_vs_edges_in_path in Hu'. destruct Hu' as [y' [z' [Hsub2 Hedge2]]].
    destruct Hedge1 as [Hedge1 | Hedge1].
    + assert (Hy: y = y').
      { apply two_sublists_the_same_2 with (l := u :: l ++ [v]) (a := w).
        - apply start_of_sublist_still_sublist in Hsub1. apply Hsub1.
        - apply start_of_sublist_still_sublist in Hsub2. apply Hsub2.
        - apply acyclic_path_count with (x := w) in Hc. apply Hc. apply sublist_member with (l1 := [y; w; z]). split.
          right. left. reflexivity. apply Hsub1. }
      rewrite <- Hy in *.
      apply contains_cycle_false_correct with (p := (w, w, [y])) in HG. exfalso. destruct HG as [HG _]. apply HG. reflexivity.
      admit.
      simpl. destruct Hedge1 as [Hedge1 _]. rewrite Hedge1. destruct Hedge2 as [Hedge2 _]. rewrite Hedge2. simpl. destruct G as [V E]. reflexivity.
    + assert (Hy: z = z').
      { apply two_sublists_the_same with (l := u :: l ++ [v]) (a := w).
        - apply end_of_sublist_still_sublist_2 in Hsub1. apply Hsub1.
        - apply end_of_sublist_still_sublist_2 in Hsub2. apply Hsub2.
        - apply acyclic_path_count with (x := w) in Hc. apply Hc. apply sublist_member with (l1 := [y; w; z]). split.
          right. left. reflexivity. apply Hsub1. }
      rewrite <- Hy in *.
      apply contains_cycle_false_correct with (p := (w, w, [z])) in HG. exfalso. destruct HG as [HG _]. apply HG. reflexivity.
      admit.
      simpl. destruct Hedge1 as [_ Hedge1]. rewrite Hedge1. destruct Hedge2 as [_ Hedge2]. rewrite Hedge2. simpl. destruct G as [V E]. reflexivity.
  - intros Hu'. apply mediators_vs_edges_in_path in Hu. destruct Hu as [y [z [Hsub1 Hedge1]]].
    apply colliders_vs_edges_in_path in Hu'. destruct Hu' as [y' [z' [Hsub2 Hedge2]]].
    destruct Hedge1 as [Hedge1 | Hedge1].
    + assert (Hy: z = z').
      { apply two_sublists_the_same with (l := u :: l ++ [v]) (a := w).
        - apply end_of_sublist_still_sublist_2 in Hsub1. apply Hsub1.
        - apply end_of_sublist_still_sublist_2 in Hsub2. apply Hsub2.
        - apply acyclic_path_count with (x := w) in Hc. apply Hc. apply sublist_member with (l1 := [y; w; z]). split.
          right. left. reflexivity. apply Hsub1. }
      rewrite <- Hy in *.
      apply contains_cycle_false_correct with (p := (w, w, [z])) in HG. exfalso. destruct HG as [HG _]. apply HG. reflexivity.
      admit.
      simpl. destruct Hedge1 as [_ Hedge1]. rewrite Hedge1. destruct Hedge2 as [_ Hedge2]. rewrite Hedge2. simpl. destruct G as [V E]. reflexivity.
    + assert (Hy: y = y').
      { apply two_sublists_the_same_2 with (l := u :: l ++ [v]) (a := w).
        - apply start_of_sublist_still_sublist in Hsub1. apply Hsub1.
        - apply start_of_sublist_still_sublist in Hsub2. apply Hsub2.
        - apply acyclic_path_count with (x := w) in Hc. apply Hc. apply sublist_member with (l1 := [y; w; z]). split.
          right. left. reflexivity. apply Hsub1. }
      rewrite <- Hy in *.
      apply contains_cycle_false_correct with (p := (w, w, [y])) in HG. exfalso. destruct HG as [HG _]. apply HG. reflexivity.
      admit.
      simpl. destruct Hedge1 as [Hedge1 _]. rewrite Hedge1. destruct Hedge2 as [Hedge2 _]. rewrite Hedge2. simpl. destruct G as [V E]. reflexivity.
Admitted.

Theorem if_confounder_then_not_mediator_path: forall (G: graph) (u: node) (p: path),
  contains_cycle G = false
  -> acyclic_path_2 p
  -> In u (find_confounders_in_path p G)
  -> ~(In u (find_mediators_in_path p G)) /\ ~(In u (find_colliders_in_path p G)).
Proof.
  intros G w [[u v] l] HG Hc Hu.
  split.
  - intros Hu'. apply if_mediator_then_not_confounder_path in Hu'.
    + destruct Hu' as [Hu' _]. apply Hu'. apply Hu.
    + apply HG.
    + apply Hc.
  - intros Hu'. apply colliders_vs_edges_in_path in Hu'. destruct Hu' as [y [z [Hsub1 Hedge1]]].
    apply confounders_vs_edges_in_path in Hu. destruct Hu as [y' [z' [Hsub2 Hedge2]]].
    assert (Hy: y = y').
    { apply two_sublists_the_same_2 with (l := u :: l ++ [v]) (a := w).
      - apply start_of_sublist_still_sublist in Hsub1. apply Hsub1.
      - apply start_of_sublist_still_sublist in Hsub2. apply Hsub2.
      - apply acyclic_path_count with (x := w) in Hc. apply Hc. apply sublist_member with (l1 := [y; w; z]). split.
        right. left. reflexivity. apply Hsub1. }
    rewrite <- Hy in *.
    apply contains_cycle_false_correct with (p := (w, w, [y])) in HG. exfalso. destruct HG as [HG _]. apply HG. reflexivity.
    admit.
    simpl. destruct Hedge1 as [Hedge1 _]. rewrite Hedge1. destruct Hedge2 as [Hedge2 _]. rewrite Hedge2. simpl. destruct G as [V E]. reflexivity.
Admitted.

Theorem if_collider_then_not_mediator_path: forall (G: graph) (u: node) (p: path),
  contains_cycle G = false
  -> acyclic_path_2 p
  -> In u (find_colliders_in_path p G)
  -> ~(In u (find_mediators_in_path p G)) /\ ~(In u (find_confounders_in_path p G)).
Proof.
  intros G w [[u v] l] HG Hc Hu.
  split.
  - intros Hu'. apply if_mediator_then_not_confounder_path in Hu'.
    + destruct Hu' as [_ Hu']. apply Hu'. apply Hu.
    + apply HG.
    + apply Hc.
  - intros Hu'. apply if_confounder_then_not_mediator_path in Hu'.
  + destruct Hu' as [_ Hu']. apply Hu'. apply Hu.
    + apply HG.
    + apply Hc.
Qed.

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
  l1 ++ [u] ++ l2 = l3 /\ (In m (find_confounders_in_path (u, v, l2) G) \/ In m (find_confounders_in_path (w, u, l1) G))
  -> In m (find_confounders_in_path (w, v, l3) G).
Proof.
  intros w u v m l1 l2 l3 G. intros [Hl3 Hx].
  destruct Hx as [Hx | Hx].
  { apply confounders_vs_edges_in_path. apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hyz [Hyx Hxz]]]].
    exists y. exists z. repeat split.
    -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l21 [l22 Hl2]].
       exists (w :: l1 ++ l21). exists l22. simpl. rewrite <- Hl3. simpl. rewrite <- app_assoc. rewrite <- app_assoc. simpl. simpl in Hl2. rewrite <- Hl2. reflexivity.
    -- apply Hyx.
    -- apply Hxz. }
  { apply confounders_vs_edges_in_path. apply confounders_vs_edges_in_path in Hx. destruct Hx as [y [z [Hyz [Hyx Hxz]]]].
    exists y. exists z. repeat split.
    -- apply sublist_breaks_down_list. apply sublist_breaks_down_list in Hyz. destruct Hyz as [l21 [l22 Hl2]].
       exists l21. exists (l22 ++ l2 ++ [v]). simpl. rewrite <- Hl3. simpl. rewrite <- app_assoc. simpl.
       rewrite <- append_vs_concat. rewrite <- append_vs_concat. rewrite <- append_vs_concat. rewrite app_assoc.
       simpl in Hl2. rewrite <- append_vs_concat in Hl2. rewrite <- append_vs_concat in Hl2. rewrite <- append_vs_concat in Hl2.
       rewrite Hl2. simpl. rewrite append_vs_concat. reflexivity.
    -- apply Hyx.
    -- apply Hxz. }
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

Lemma subpath_preserves_confounders_2: forall (w u v: node) (l1 l2 l3: nodes) (G: graph),
  l1 ++ [u] ++ l2 = l3
  -> find_confounders_in_path (w, v, l3) G = (find_confounders_in_path (w, u, l1) G) ++ [u] ++ (find_confounders_in_path (u, v, l2) G)
     \/ find_confounders_in_path (w, v, l3) G = (find_confounders_in_path (w, u, l1) G) ++ (find_confounders_in_path (u, v, l2) G).
Proof.
  intros w u v l1 l2 l3 G. intros H.
  generalize dependent w. generalize dependent l3. induction l1 as [| h t IH].
  - intros l3 H w. simpl in H. rewrite <- H. simpl. destruct l2 as [| h2 t2].
    + simpl. destruct (is_confounder_bool w v u G) as [|]. left. reflexivity. right. reflexivity.
    + simpl. destruct (is_confounder_bool w h2 u G) as [|]. left. reflexivity. right. reflexivity.
  - intros l3 H w. simpl. destruct l3 as [| h3 t3].
    + simpl. discriminate H.
    + specialize IH with (l3 := t3) (w := h3). simpl in H. inversion H. rewrite <- H1 in *. apply IH in H2 as Hind.
      simpl. rewrite H2. simpl in Hind. destruct t3 as [| h' t'].
      * destruct t as [| ht tt]. discriminate H. discriminate H.
      * simpl. simpl in Hind. destruct (is_confounder_bool w h' h G) as [|] eqn:Hcol.
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

Lemma collider_count_acyclic: forall (u v c: node) (l: nodes) (G: graph),
  In c (find_colliders_in_path (u, v, l) G)
  -> acyclic_path_2 (u, v, l)
  -> is_path_in_graph (u, v, l) G = true
  -> count c (find_colliders_in_path (u, v, l) G) = 1.
Proof.
  intros u v c l G Hc Hcyc Hp.
  generalize dependent u. induction l as [| h t IH].
  - intros u Hc Hcyc Hp. simpl in Hc. exfalso. apply Hc.
  - intros u Hc Hcyc Hp. simpl in Hc. destruct t as [| h' t'].
    + simpl in Hc. destruct (is_collider_bool u v h G) as [|] eqn:Hcol.
      * destruct Hc as [Hc | Hc]. simpl. rewrite Hcol. simpl. rewrite Hc. rewrite eqb_refl. reflexivity. exfalso. apply Hc.
      * exfalso. apply Hc.
    + simpl in Hc.
      assert (Hp': is_path_in_graph (h, v, h' :: t') G = true). { simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. apply Hp. }
      assert (Hcyc': acyclic_path_2 (h, v, h' :: t')). { apply acyclic_path_cat with (u := u). apply Hcyc. }
      destruct (is_collider_bool u h' h G) as [|] eqn:Hcol.
      * destruct Hc as [Hc | Hc].
        --- simpl. rewrite Hcol. simpl. rewrite Hc. rewrite eqb_refl.
            assert (~In c (find_colliders_in_path (h, v, h' :: t') G)).
            { intros Hcmem.
              apply intermediate_node_in_path with (x := c) in Hp'. assert (In c (h' :: t')). { apply Hp'. right. right. apply Hcmem. }
              destruct Hcyc' as [_ [H1 _]]. apply H1.
              rewrite Hc. apply H. }
            apply member_In_equiv_F in H. apply not_member_count_0 in H. simpl in H. rewrite Hc in *. rewrite H. reflexivity.
        --- simpl. rewrite Hcol. simpl.
            assert (In c (h' :: t')).
            { apply intermediate_node_in_path with (x := c) in Hp'. apply Hp'. right. right. apply Hc. }
            destruct (h =? c) as [|] eqn:Hhc. apply eqb_eq in Hhc. exfalso. destruct Hcyc' as [_ [Hcyc' _]]. apply Hcyc'. rewrite Hhc. apply H.
            apply IH in Hc. apply Hc. apply Hcyc'. apply Hp'.
      * simpl. rewrite Hcol. simpl.
        assert (In c (h' :: t')).
        { apply intermediate_node_in_path with (x := c) in Hp'. apply Hp'. right. right. apply Hc. }
        destruct (h =? c) as [|] eqn:Hhc. apply eqb_eq in Hhc. exfalso. destruct Hcyc' as [_ [Hcyc' _]]. apply Hcyc'. rewrite Hhc. apply H.
        apply IH in Hc. apply Hc. apply Hcyc'. apply Hp'.
Qed.

Lemma confounder_count_acyclic: forall (u v c: node) (l: nodes) (G: graph),
  In c (find_confounders_in_path (u, v, l) G)
  -> acyclic_path_2 (u, v, l)
  -> is_path_in_graph (u, v, l) G = true
  -> count c (find_confounders_in_path (u, v, l) G) = 1.
Proof.
  intros u v c l G Hc Hcyc Hp.
  generalize dependent u. induction l as [| h t IH].
  - intros u Hc Hcyc Hp. simpl in Hc. exfalso. apply Hc.
  - intros u Hc Hcyc Hp. simpl in Hc. destruct t as [| h' t'].
    + simpl in Hc. destruct (is_confounder_bool u v h G) as [|] eqn:Hcol.
      * destruct Hc as [Hc | Hc]. simpl. rewrite Hcol. simpl. rewrite Hc. rewrite eqb_refl. reflexivity. exfalso. apply Hc.
      * exfalso. apply Hc.
    + simpl in Hc.
      assert (Hp': is_path_in_graph (h, v, h' :: t') G = true). { simpl in Hp. destruct G as [V E]. apply split_and_true in Hp. apply Hp. }
      assert (Hcyc': acyclic_path_2 (h, v, h' :: t')). { apply acyclic_path_cat with (u := u). apply Hcyc. }
      destruct (is_confounder_bool u h' h G) as [|] eqn:Hcol.
      * destruct Hc as [Hc | Hc].
        --- simpl. rewrite Hcol. simpl. rewrite Hc. rewrite eqb_refl.
            assert (~In c (find_confounders_in_path (h, v, h' :: t') G)).
            { intros Hcmem.
              apply intermediate_node_in_path with (x := c) in Hp'. assert (In c (h' :: t')). { apply Hp'. right. left. apply Hcmem. }
              destruct Hcyc' as [_ [H1 _]]. apply H1.
              rewrite Hc. apply H. }
            apply member_In_equiv_F in H. apply not_member_count_0 in H. simpl in H. rewrite Hc in *. rewrite H. reflexivity.
        --- simpl. rewrite Hcol. simpl.
            assert (In c (h' :: t')).
            { apply intermediate_node_in_path with (x := c) in Hp'. apply Hp'. right. left. apply Hc. }
            destruct (h =? c) as [|] eqn:Hhc. apply eqb_eq in Hhc. exfalso. destruct Hcyc' as [_ [Hcyc' _]]. apply Hcyc'. rewrite Hhc. apply H.
            apply IH in Hc. apply Hc. apply Hcyc'. apply Hp'.
      * simpl. rewrite Hcol. simpl.
        assert (In c (h' :: t')).
        { apply intermediate_node_in_path with (x := c) in Hp'. apply Hp'. right. left. apply Hc. }
        destruct (h =? c) as [|] eqn:Hhc. apply eqb_eq in Hhc. exfalso. destruct Hcyc' as [_ [Hcyc' _]]. apply Hcyc'. rewrite Hhc. apply H.
        apply IH in Hc. apply Hc. apply Hcyc'. apply Hp'.
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
     - assert (H: y = dy /\ rev tly1 ++ [hly1] = py). { apply Hpdy. apply Hly2. } destruct H as [H1 H2]. rewrite <- H1 in Hdir.
       assert (Hdir': is_directed_path_in_graph (hly1, y, []) G = true). { apply subpath_still_directed with (w := cy) (l1 := rev tly1) (l3 := py). split. apply H2. apply Hdir. }
       simpl in Hdir'. apply split_and_true in Hdir'. apply Hdir'.
     - assert (H: dy = hly2 /\ py = (rev tly1 ++ [hly1]) ++ [y] ++ rev tly2). { apply Hpdy. apply Hly2. }
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
    - assert (Hy: y = d2 /\ l2' = l2). { apply Hl2. apply Hl2''. } destruct Hy as [Hy1 Hy2]. rewrite <- Hy1 in Hd2. rewrite <- Hy2 in Hd2. rewrite Hl20 in Hd2.
      simpl in Hd2. apply split_and_true in Hd2. apply Hd2.
    - assert (Hy: d2 = hl2' /\ l2 = l2' ++ [y] ++ rev tl2'). { apply Hl2. apply Hl2''. } destruct Hy as [Hy1 Hy2]. rewrite Hy1 in Hd2. rewrite Hy2 in Hd2. rewrite Hl20 in Hd2.
      simpl in Hd2. apply split_and_true in Hd2. apply Hd2. }

  assert (Hcy2': forall (hl2: node) (tl2: nodes), l2' = rev tl2 ++ [hl2] -> is_edge (hl2, y) G = true).
  { intros hl2 tl2 Hl20. destruct (rev l2'') as [| hl2' tl2'] eqn:Hl2''.
    - assert (Hy: y = d2 /\ l2' = l2). { apply Hl2. apply Hl2''. } destruct Hy as [Hy1 Hy2]. rewrite <- Hy1 in Hd2. rewrite <- Hy2 in Hd2. rewrite Hl20 in Hd2.
      assert (Hd': is_directed_path_in_graph (hl2, y, []) G = true). { apply subpath_still_directed with (w := c2) (l1 := rev tl2) (l3 := rev tl2 ++ [hl2]). split. rewrite append_identity. reflexivity. apply Hd2. }
      simpl in Hd'. apply split_and_true in Hd'. apply Hd'.
    - assert (Hy: d2 = hl2' /\ l2 = l2' ++ [y] ++ rev tl2'). { apply Hl2. apply Hl2''. } destruct Hy as [Hy1 Hy2]. rewrite Hy2 in Hd2. rewrite Hl20 in Hd2.
      assert (Hd': is_directed_path_in_graph (hl2, d2, y :: rev tl2') G = true). { apply subpath_still_directed with (w := c2) (l1 := rev tl2) (l3 := rev tl2 ++ [hl2] ++ [y] ++ rev tl2'). split. reflexivity. rewrite app_assoc. apply Hd2. }
      simpl in Hd'. apply split_and_true in Hd'. apply Hd'. }

  destruct (rev l1') as [| hl1 tl1] eqn:Hl1'.
  - exists c1. assert (Hl10: l1' = []). { rewrite reverse_list_twice with (l := l1'). unfold node in *. rewrite Hl1'. reflexivity. }
    assert (Hcy1: is_edge (c1, y) G = true).
    { destruct (rev l1'') as [| hl1' tl1'] eqn:Hl1''.
      - assert (Hy: y = d1 /\ l1' = l1). { apply Hl1. apply Hl1''. } destruct Hy as [Hy1 Hy2]. rewrite <- Hy1 in Hd1. rewrite <- Hy2 in Hd1. rewrite Hl10 in Hd1.
        simpl in Hd1. apply split_and_true in Hd1. apply Hd1.
      - assert (Hy: d1 = hl1' /\ l1 = l1' ++ [y] ++ rev tl1'). { apply Hl1. apply Hl1''. } destruct Hy as [Hy1 Hy2]. rewrite Hy1 in Hd1. rewrite Hy2 in Hd1. rewrite Hl10 in Hd1.
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
      - assert (Hy: y = d1 /\ l1' = l1). { apply Hl1. apply Hl1''. } destruct Hy as [Hy1 Hy2]. rewrite <- Hy1 in Hd1. rewrite <- Hy2 in Hd1. rewrite Hl10 in Hd1.
        assert (Hd': is_directed_path_in_graph (hl1, y, []) G = true). { apply subpath_still_directed with (w := c1) (l1 := rev tl1) (l3 := rev tl1 ++ [hl1]). split. rewrite append_identity. reflexivity. apply Hd1. }
        simpl in Hd'. apply split_and_true in Hd'. apply Hd'.
      - assert (Hy: d1 = hl1' /\ l1 = l1' ++ [y] ++ rev tl1'). { apply Hl1. apply Hl1''. } destruct Hy as [Hy1 Hy2]. rewrite Hy2 in Hd1. rewrite Hl10 in Hd1.
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
