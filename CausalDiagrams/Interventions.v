From CausalDiagrams Require Import DSeparation.
From CausalDiagrams Require Import CausalPaths.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.

Import ListNotations.

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


Lemma edges_in_do : forall (X : node) (G : graph),
  edges_in_graph (do X G) = remove_edges_into X (edges_in_graph G).
Proof. unfold do. destruct G as [V E]. simpl. reflexivity.
Qed.

Lemma num_nodes_do : forall (X : node) (G : graph),
  num_nodes (do X G) = num_nodes G.
Proof. unfold do. destruct G as [V E]. simpl. reflexivity.
Qed.

Lemma directed_edges_as_paths_no_end_X : forall (X : node) (E : edges),
  (forall u, ~ In (u, X) E) ->
  filter (fun p => path_end p =? X) (directed_edges_as_paths E) = [].
Proof. intros X E HnotIn. induction E as [| (u, v) t IH].
  - simpl. reflexivity.
  - simpl. assert (Hv : v <> X).
    { intro Heq. subst v. apply (HnotIn u). left. reflexivity. }
    rewrite <- Nat.eqb_neq in Hv. rewrite Hv. apply IH. intros u' HIn. apply (HnotIn u'). right. exact HIn.
Qed.

Lemma dfs_extend_by_edge_no_end_X : forall (X : node) (e : edge) (l : paths),
  snd e <> X ->
  filter (fun p => path_end p =? X) l = [] ->
  filter (fun p => path_end p =? X) (snd (dfs_extend_by_edge e l)) = [].
Proof.
  intros X e l Hne Hfilter. destruct e as [u2 v2]. simpl in Hne.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl in Hfilter. destruct h as [[u1 v1] l1].
    destruct (path_end (u1, v1, l1) =? X) eqn:Hh.
    + discriminate Hfilter.
    + simpl in Hfilter. specialize (IH Hfilter). simpl.
      destruct (u2 =? v2) eqn:Hself.
      { simpl. reflexivity. }
      destruct ((u2 =? v1) && (u1 =? v2)) eqn:Hcycle1.
      { simpl. reflexivity. }
      destruct ((u2 =? v1) && member v2 l1) eqn:Hcycle2.
      { simpl. reflexivity. }
      destruct (u2 =? v1) eqn:Hext.
      { simpl. simpl in Hh. rewrite Hh. unfold add_path_no_repeats.
        destruct (member_path (u1, v2, l1 ++ [v1]) (snd (dfs_extend_by_edge (u2, v2) t))) eqn:Hmem.
        - exact IH.
        - rewrite filter_app. rewrite IH. simpl. assert ((v2 =? X)=false). rewrite eqb_neq. auto. rewrite H. reflexivity. }
      { simpl. unfold path_end in Hh. rewrite Hh. exact IH. }
Qed.

Lemma dfs_extend_by_edges_no_end_X : forall (X : node) (E : edges) (l : paths),
  (forall u, ~ In (u, X) E) ->
  filter (fun p => path_end p =? X) l = [] ->
  filter (fun p => path_end p =? X) (snd (dfs_extend_by_edges E l)) = [].
Proof.
  intros X. induction E as [| h t IHt]; intros l HnoX Hfilter.
  - simpl. exact Hfilter.
  - simpl. destruct (dfs_extend_by_edge h l) as [b l'] eqn:Hdfs.
    destruct b; simpl.
    + reflexivity.
    + apply IHt.
      * intros u Hin. apply (HnoX u). right. exact Hin.
      * assert (Haux : filter (fun p => path_end p =? X) (snd (dfs_extend_by_edge h l)) = []).
        { apply dfs_extend_by_edge_no_end_X.
          - destruct h as [u2 v2]. simpl. intros Heq. subst v2.
            specialize (HnoX u2). simpl in HnoX. apply demorgan in HnoX. destruct HnoX as [hf _].
            eauto.
          - exact Hfilter. }
        rewrite Hdfs in Haux. simpl in Haux. exact Haux.
Qed.

Lemma dfs_extend_by_edges_iter_no_end_X :
  forall (X : node) (E : edges) (l : paths) (k : nat),
  (forall u, ~ In (u, X) E) ->
  filter (fun p => path_end p =? X) l = [] ->
  filter (fun p => path_end p =? X) (snd (dfs_extend_by_edges_iter E l k)) = [].
Proof.
  intros X E l k. revert k l.
  induction k as [| k' IHk']; intros l HnoX Hfilter.
  - simpl. exact Hfilter.
  - simpl. destruct (fst (dfs_extend_by_edges E l)) eqn:Hcycle.
    + simpl. apply dfs_extend_by_edges_no_end_X; assumption.
    + apply IHk'.
      * exact HnoX.
      * apply dfs_extend_by_edges_no_end_X; assumption.
Qed.


Theorem do_removes_paths_to_X: forall (X: node) (G: graph),
  find_directed_paths_to_end X (do X G) = [].
Proof. intros X G. unfold find_directed_paths_to_end.
  rewrite edges_in_do. rewrite num_nodes_do.
  apply dfs_extend_by_edges_iter_no_end_X.
  - intro u. intro HIn. unfold remove_edges_into in HIn. apply filter_In in HIn.
    destruct HIn as [_ Hbad]. simpl in Hbad. rewrite Nat.eqb_refl in Hbad. simpl in Hbad. discriminate.
  - apply directed_edges_as_paths_no_end_X.
    intro u. intro HIn. unfold remove_edges_into in HIn. apply filter_In in HIn.
    destruct HIn as [_ Hbad]. simpl in Hbad. rewrite Nat.eqb_refl in Hbad. simpl in Hbad. discriminate.
Qed.

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
    apply edge_in_graph_then_is_edge in Hparent. rewrite Hparent in Hacyc. discriminate Hacyc. apply HG. apply HG.
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
    { apply contains_cycle_false_correct with (p:=(concat X P X l [])) in Hacyc. apply Hacyc. apply HG.
      apply HnewPath. }
    simpl in contra. destruct contra as [contra _].
    apply eqb_neq in contra. rewrite eqb_refl in contra. discriminate contra. auto. auto.
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
