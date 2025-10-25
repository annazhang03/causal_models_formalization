From DAGs Require Import Basics.
From Utils Require Import Lists.
From Utils Require Import Logic.

Import ListNotations.

(* this file defines the function which outputs all acyclic undirected paths from node u to
   node v in a given graph and states the required theorems to prove its correctness *)

(*helper function for paths-finding validity*)
Definition PathsValid (G: graph) (ps: paths) : Prop :=
  Forall (fun p => is_path_in_graph p G = true) ps.

Lemma In_PathsValid_implies_valid :
  forall (G: graph) (ps: paths) (p: path),
    PathsValid G ps -> In p ps -> is_path_in_graph p G = true.
Proof.
  intros G ps p H HIn.
  eapply Forall_forall in H; eauto.
Qed.

(* append path p to end of l if p is not already in l *)
Definition add_path_no_repeats (p: path) (l: paths) : paths :=
  if (member_path p l) then l else l ++ [p].

Lemma add_path_no_repeats_valid :
  forall (G: graph) (p: path) (l: paths),
    is_path_in_graph p G = true -> PathsValid G l -> PathsValid G (add_path_no_repeats p l).
Proof. intros G p l Hp Hps. unfold add_path_no_repeats.
  destruct (member_path p l) eqn:Hmem.
  - exact Hps.
  - unfold PathsValid in *. apply Forall_app; split.
    + exact Hps.
    + constructor; [exact Hp| constructor].
Qed.

(* helper for add_path_no_repeats: adds all nodes in S to V without repeats *)
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



(* return list of 1-paths (paths consisting of a single edge)
   starting from u (undirected, so the arrow in the edge could go forwards or backwards) *)
Fixpoint edges_as_paths_from_start (u: node) (E: edges) : paths :=
  match E with
  | [] => []
  | h :: t => match h with
              | (a, b) => if (u =? a) then (a, b, []) :: edges_as_paths_from_start u t (* u -> b *)
                          else if (u =? b) then (b, a, []) :: edges_as_paths_from_start u t (* a <- u *)
                          else edges_as_paths_from_start u t (* this edge (a,b) does not involve u *)
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

(*helper 1.1 for paths_start_to_end_valid*)
Lemma edge_in_extended_graph :
  forall V E a x y,
    is_edge (x, y) (V, E) = true ->
    is_edge (x, y) (V, a :: E) = true.
Proof.
  intros V E a x y H. unfold is_edge in *; simpl.
  assert ((eqbedge a (x, y) || member_edge (x, y) E)=true).
  apply orb_true_intro. right. apply andb_true_iff in H.
  destruct H as [h1 h3]. exact h3. apply andb_true_iff in H.
  destruct H as [h1 h3]. apply andb_true_iff in h1.
  destruct h1 as [h1 h2]. rewrite h1. rewrite h2. rewrite H0. trivial.
Qed.

(*helper 1.2 for paths_start_to_end_valid*)
Lemma is_path_in_graph_helper_monotone_edges :
  forall V E a l,
    is_path_in_graph_helper l (V, E) = true ->
    is_path_in_graph_helper l (V, a :: E) = true.
Proof.
  intros V E a l H. induction l as [|h l' IH]. simpl. reflexivity. destruct l' as [|h' l''].
    - simpl. reflexivity.
    - simpl in *. apply andb_prop in H. destruct H as [Hedge Hrest].
      apply andb_true_intro. split. unfold is_edge in *. simpl in *.
      apply orb_prop in Hedge. destruct Hedge as [H1 | H2].
        -- apply orb_true_intro. left. apply (edge_in_extended_graph V E a h h' H1).
        -- apply orb_true_intro. right. apply (edge_in_extended_graph V E a h' h H2).
        -- apply (IH Hrest).
Qed.

(*helper 1.3 for paths_start_to_end_valid*)
Lemma path_monotone_edges :
  forall V E a p,
    is_path_in_graph p (V,E) = true ->
    is_path_in_graph p (V, a::E) = true.
Proof. intros V E a p H. destruct p as [[u v] l]. unfold is_path_in_graph in *.
  apply (is_path_in_graph_helper_monotone_edges V E a ((u :: l) ++ [v]) H).
Qed.

(*helper 1.4 for paths_start_to_end_valid*)
Lemma edges_as_paths_helper :
  forall V x y (E: edges), In x V -> In y V ->
    is_path_in_graph (x,y,[]) (V, (x,y)::E) = true.
Proof. intros V x y E Hx Hy. unfold is_path_in_graph. simpl.
  apply andb_true_iff. split.
  - apply orb_true_iff. left. apply andb_true_iff. split.
    apply andb_true_iff. split; rewrite member_In_equiv; assumption.
    apply orb_true_iff. left. apply andb_true_iff; split; apply Nat.eqb_refl.
  - reflexivity.
Qed.
Lemma edges_as_paths_helper2 :
  forall V x y E, In x V -> In y V ->
    is_path_in_graph (y,x,[]) (V, (x,y)::E) = true.
Proof. intros V x y E Hx Hy. unfold is_path_in_graph. simpl.
  apply andb_true_iff. split.
  - apply orb_true_iff. right. apply andb_true_iff. split.
    apply andb_true_iff. split; rewrite member_In_equiv; assumption.
    apply orb_true_iff. left. apply andb_true_iff; split; apply Nat.eqb_refl.
  - reflexivity.
Qed.

(*helper 1.5 for paths_start_to_end_valid*)
Lemma G_well_formed_corollary : forall (V: nodes) (E: edges),
  G_well_formed (V, E) = true -> forall (u v :node), In (u, v) E -> In u V /\ In v V.
Proof.
  intros V E Hwf u v Hin. unfold G_well_formed in Hwf.
  apply andb_prop in Hwf. destruct Hwf as [Hwf _].
  apply andb_prop in Hwf. destruct Hwf as [Hwf _].
  rewrite forallb_forall in Hwf. pose proof (Hwf (u,v) Hin); simpl in H.
  apply andb_true_iff in H. repeat rewrite <- member_In_equiv. exact H.
Qed.

(*helper 1.6 for paths_start_to_end_valid*)
Lemma G_well_formed_induction : forall (V:nodes) (E:edges) (e:edge),
  G_well_formed (V, e :: E) = true -> G_well_formed (V, E)=true.
Proof. intros V E e Hwf. unfold G_well_formed in *.
  apply andb_prop in Hwf. destruct Hwf as [H12 H3].
  apply andb_prop in H12. destruct H12 as [H1 H2].
  apply andb_true_intro; split. apply andb_true_intro; split.
  - apply forallb_forall. intros [u v] Hin. rewrite forallb_forall in H1.
    assert (Hin' : In (u,v) (e::E)). right. exact Hin. pose proof (H1 (u,v) Hin');
    simpl in H1. apply andb_true_iff in H. apply andb_true_iff. exact H.
  - exact H2.
  - apply forallb_forall. intros x Hin. rewrite forallb_forall in H3.
    assert (Hin' : In x (e::E)). right. exact Hin.
    pose proof (H3 x Hin'). clear H1 H2 H3 Hin'. apply Nat.eqb_eq.

    apply Nat.eqb_eq in H. inversion H. case (eqbedge e x) eqn: Heq.
    + (*false statement*) exfalso; clear H Heq. injection H1 as H1.
      induction E as [|h t IH]; simpl in *.
      -- contradiction.
      -- destruct Hin as [Hx | Hin].
        ++ subst h. rewrite <- eqbedge_refl in H1. discriminate H1.
        ++ destruct (eqbedge h x) eqn:Heq.
          * discriminate H1.
          * simpl in H1. eapply IH; eauto.
    + reflexivity.
Qed.

(*helper 1 for paths_start_to_end_valid*)
Lemma edges_as_paths_from_start_valid : forall (u v: node) (l: nodes) (V:nodes) (E:edges),
  G_well_formed (V, E) = true ->
  In (u, v, l) (edges_as_paths_from_start u E) -> is_path_in_graph (u, v, l) (V,E) = true.
Proof. intros u v l V E Hwf Hin. induction E. simpl in Hin. exfalso; assumption.
  destruct a as [x y].
  pose proof (G_well_formed_induction V E (x,y) Hwf) as Hwf'.
  case (u =? x) eqn:Hx. simpl in Hin. rewrite Hx in Hin. simpl in Hin.
  destruct Hin as [Hin | Hin].
  (*u=x case*)
  - inversion Hin; subst; clear Hin.
  destruct (G_well_formed_corollary V ((u,v)::E) Hwf u v (or_introl eq_refl)) as [Hu Hv].
  rewrite edges_as_paths_helper; [reflexivity | exact Hu | exact Hv].
  - specialize (IHE (Hwf') Hin). now apply path_monotone_edges with (a := (x,y)).
  (*u=y case*)
  - destruct (u =? y) eqn:Hy. simpl in Hin. rewrite Hy in Hin. rewrite Hx in Hin.
  simpl in Hin. destruct Hin as [Hin | Hin].
    + inversion Hin; subst; clear Hin.
    pose proof (G_well_formed_corollary V ((v,u)::E) Hwf v u (or_introl eq_refl)) as [Hu Hv].
    rewrite edges_as_paths_helper2; [reflexivity | exact Hu | exact Hv].
    + specialize (IHE (Hwf') Hin). now apply path_monotone_edges with (a := (x,y)).
  (*u!=x and u!=y case*)
    + simpl in Hin. rewrite Hx in Hin. rewrite Hy in Hin. specialize (IHE (Hwf') Hin).
  eapply path_monotone_edges with (a := (x,y)) in IHE. exact IHE.
Qed.


(*helper 1 for paths_start_to_end_acyclic*)
Lemma edges_as_paths_from_start_acyclic : forall (u: node) (p:path) (E: edges),
  no_one_cycles E = true ->
  In p (edges_as_paths_from_start u E) -> acyclic_path_2 p.
Proof. intros u [[u' v] l] E Hloop Hin. induction E.
    + simpl in *. exfalso. assumption.
    + destruct a as [a1 a2]. assert (IHloop: no_one_cycles E = true).
      { unfold no_one_cycles in *. destruct (a1 =? a2). discriminate. assumption. }
      simpl in Hin. destruct (u =? a1) eqn:Hua1.
        { simpl in Hin. destruct Hin as [Hin | Hin].
          - injection Hin as Hu Hv Hl; subst. split. apply Nat.eqb_eq in Hua1; subst.
            simpl in Hloop. destruct (u' =? v) eqn:H. discriminate. apply Nat.eqb_neq in H. assumption.
            split; simpl; tauto.
          - apply IHE; assumption. }
        { destruct (u =? a2) eqn:Hua2.
        simpl in Hin. destruct Hin as [Hin | Hin].
          - injection Hin as Hu Hv Hl; subst. split. apply Nat.eqb_eq in Hua2; subst.
            simpl in Hloop. destruct (u' =? v) eqn:H. discriminate. apply Nat.eqb_neq in H. assumption.
            split; simpl; tauto.
          - apply IHE; assumption.
          - apply IHE; assumption. }
Qed.

(* helper 1.1 for paths_start_to_end_correct*)
Lemma edges_as_paths_from_start_start :
  forall u E p, In p (edges_as_paths_from_start u E) ->
    path_start p = u.
Proof.
  intros u E; induction E as [|[a b] E IHE]; simpl; intros p Hin; try tauto.
  destruct (u =? a) eqn:Ha; simpl in Hin.
  - apply Nat.eqb_eq in Ha; subst.
    destruct Hin as [Hin|Hin]; [subst; reflexivity| now eauto].
  - destruct (u =? b) eqn:Hb; simpl in Hin.
    + apply Nat.eqb_eq in Hb; subst.
      destruct Hin as [Hin|Hin]; [subst; reflexivity| now eauto].
    + now eauto.
Qed.

(* given an edge e and a list of paths l, grow each path in l by e if any of the nodes of e match
   the endpoint (not the start point) of the path in l.
   example: if the path 1->2 were in l, and e = (3, 2), then we would append 1->2->3 to l
            however, if e = (1, 3), we would not extend this path, since we do not modify the front *)
Fixpoint extend_paths_from_start_by_edge (e : edge) (l: paths) : paths :=
  match l with
  | [] => []
  | h :: t => match h, e with
                | (u1, v1, l1), (u2, v2) =>
                      if ((u1 =? u2) || (u1 =? v2)) then h :: extend_paths_from_start_by_edge e t (* do not modify front of path h *)
                      else if (member u2 l1 || member v2 l1) then h :: extend_paths_from_start_by_edge e t (* do not introduce repeats into paths *)
                      else if (v1 =? u2) then add_path_no_repeats (u1, v2, l1 ++ [v1]) (h :: extend_paths_from_start_by_edge e t) (* extend h by e *)
                      else if (v1 =? v2) then add_path_no_repeats (u1, u2, l1 ++ [v1]) (h :: extend_paths_from_start_by_edge e t) (* extend h by reverse of e *)
                      else h :: extend_paths_from_start_by_edge e t (* no overlap between h and e *)
               end
end.

Example extend_edges_from_1: extend_paths_from_start_by_edge (3, 2) [(1, 2, []); (1, 3, []); (1, 4, [])]
  = [(1, 2, []); (1, 3, []); (1, 4, []); (1, 2, [3]); (1, 3, [2])].
Proof. reflexivity. Qed.

Example no_extend_edges_from_1: extend_paths_from_start_by_edge (3, 1) [(1, 2, []); (1, 3, []); (1, 4, [])]
  = [(1, 2, []); (1, 3, []); (1, 4, [])].
Proof. reflexivity. Qed.


(*helper 2.1 for paths_start_to_end_valid*)
Lemma is_path_in_graph_helper_app_one :
  forall (G: graph) (x: list node) (y z: node),
    is_path_in_graph_helper (x ++ [y]) G = true ->
    (is_edge (y, z) G || is_edge (z, y) G) = true ->
    is_path_in_graph_helper (x ++ [y; z]) G = true.
Proof.
  intros [V E] x; induction x as [|a x IH]; intros y z Hxy Hor; simpl in *.
  - now rewrite Hor.
  - destruct x as [|a2 x']; simpl in *.
    + apply Bool.andb_true_iff in Hxy as [A _].
      apply Bool.andb_true_iff; split; [exact A| now rewrite Hor].
    + apply Bool.andb_true_iff in Hxy as [A B].
      apply Bool.andb_true_iff; split; [exact A| now apply IH].
Qed.

(*helper 2 for paths_start_to_end_valid*)
Lemma extend_paths_from_start_by_edge_valid :
  forall (G: graph) (e: (nat*nat)) (ps: paths),
    G_well_formed G = true -> is_edge e G = true -> PathsValid G ps ->
    PathsValid G (extend_paths_from_start_by_edge e ps).
Proof. intros G e ps Hwf He Hps. revert e He.
  induction ps as [| a ps IH]; intros e He; simpl.
  - constructor.
  - destruct a as [[u1 v1] l1]. destruct e as [u2 v2].
  (* destruct the function case by case. *)

    destruct (orb (u1 =? u2) (u1 =? v2)) eqn:Hcase1.
    {inversion Hps as [| ? ? Hhd Htl]; subst. constructor. exact Hhd.
    unfold PathsValid in IH. pose proof (IH Htl (u2,v2) He) as IH. exact IH. }

    destruct (orb (member u2 l1) (member v2 l1)) eqn:Hcase2.
    {inversion Hps as [| ? ? Hhd Htl]; subst. constructor. exact Hhd.
    unfold PathsValid in IH. pose proof (IH Htl (u2,v2) He) as IH. exact IH. }

    destruct (v1 =? u2) eqn:Hv1u2.
    inversion Hps as [| ? ? Hhd Htl]; subst. clear Hcase1 Hcase2.
    apply add_path_no_repeats_valid.
    { apply Nat.eqb_eq in Hv1u2. subst u2. unfold is_path_in_graph in *.
    pose proof (is_path_in_graph_helper_app_one G _ v1 v2 Hhd).
    rewrite orb_true_iff in H. assert (is_edge (v1, v2) G = true \/ is_edge (v2, v1) G = true).
    left. exact He. apply H in H0. rewrite <- H0. f_equal.
    simpl. rewrite <- app_assoc. reflexivity.
    } (*v1 = u2 -> is_edge (v1,v2) -> is_path (u1,v2, l1++v1)*)
    {constructor. exact Hhd. unfold PathsValid in IH. pose proof (IH Htl (u2,v2) He) as IH. exact IH. }

    destruct (v1 =? v2) eqn:Hv1v2.
    inversion Hps as [| ? ? Hhd Htl]; subst. clear Hcase1 Hcase2.
    apply add_path_no_repeats_valid.
    { apply Nat.eqb_eq in Hv1v2. subst v2. unfold is_path_in_graph in *.
    pose proof (is_path_in_graph_helper_app_one G _ v1 u2 Hhd).
    rewrite orb_true_iff in H. assert (is_edge (v1, u2) G = true \/ is_edge (u2, v1) G = true).
    right. exact He. apply H in H0. rewrite <- H0. f_equal.
    simpl. rewrite <- app_assoc. reflexivity.
    } (*v1 = v2 -> is_edge (u2,v1) -> is_path (u1,u2, l1++v1)*)
    {constructor. exact Hhd. unfold PathsValid in IH. pose proof (IH Htl (u2,v2) He) as IH. exact IH. }

    {inversion Hps as [| ? ? Hhd Htl]; subst. constructor. exact Hhd.
    unfold PathsValid in IH. pose proof (IH Htl (u2,v2) He) as IH. exact IH. }
Qed.

(* helper 1.2 for paths_start_to_end_correct*)
Lemma extend_paths_from_start_by_edge_start :
  forall e u ps, (forall p, In p ps -> path_start p = u) ->
  forall p, In p (extend_paths_from_start_by_edge e ps) -> path_start p = u.
Proof. intros [u2 v2] u ps Hstarts p. revert p; induction ps as [|h t IH]; simpl; intros p Hin; [contradiction|].
  destruct h as [[u1 v1] l1]. assert (forall p : path, In p t -> path_start p = u).
  { intros p0 h0. apply Hstarts. simpl. right. auto. } specialize (IH H); clear H.
  assert (Hh : path_start (u1, v1, l1) = u) by (apply Hstarts; left; reflexivity); subst.

  destruct ((u1 =? u2) || (u1 =? v2)) eqn:case1; simpl in Hin.
    { destruct Hin as [Hin|Hin]. - rewrite <- Hin. auto. - apply IH. auto. }

  destruct (member u2 l1 || member v2 l1) eqn:case2; simpl in Hin.
    { destruct Hin as [Hin|Hin]. - rewrite <- Hin. auto. - apply IH. auto. }

  destruct (v1 =? u2) eqn:case3; simpl in Hin.
   { apply Nat.eqb_eq in case3; subst. unfold add_path_no_repeats in Hin; simpl in Hin.
    destruct ((u1 =? u1) && (u2 =? v2) && eqblist l1 (l1 ++ [u2])).
      { destruct Hin as [Hin|Hin]. - rewrite <- Hin. auto. - apply IH. auto. }
    destruct (member_path (u1, v2, l1 ++ [u2]) (extend_paths_from_start_by_edge (u2, v2) t)) eqn:Hmem.
      { destruct Hin as [Hin|Hin]. - rewrite <- Hin. auto. - apply IH. auto. }
      { destruct Hin as [Hin|Hin]. - rewrite <- Hin. auto.
        - apply in_app_or in Hin. destruct Hin as [Hin|Hin].
          + apply IH. auto.
          + simpl in Hin. destruct Hin as [Heq | []]. rewrite <- Heq. auto. } }

  destruct (v1 =? v2) eqn:case4; simpl in Hin.
   { apply Nat.eqb_eq in case4; subst. unfold add_path_no_repeats in Hin; simpl in Hin.
    destruct ((u1 =? u1) && (v2 =? u2) && eqblist l1 (l1 ++ [v2])).
      { destruct Hin as [Hin|Hin]. - rewrite <- Hin. auto. - apply IH. auto. }
    destruct (member_path (u1, u2, l1 ++ [v2]) (extend_paths_from_start_by_edge (u2, v2) t)) eqn:Hmem.
      { destruct Hin as [Hin|Hin]. - rewrite <- Hin. auto. - apply IH. auto. }
      { destruct Hin as [Hin|Hin]. - rewrite <- Hin. auto.
        - apply in_app_or in Hin. destruct Hin as [Hin|Hin].
          + apply IH. auto.
          + simpl in Hin. destruct Hin as [Heq | []]. rewrite <- Heq. auto. } }

  destruct Hin as [Hin|Hin]. - rewrite <- Hin; auto. - apply IH; auto.
Qed.

(* given several edges, attempt to extend the paths of l with each given edge in the manner
   described above in extend_paths_from_start_by_edge *)
Fixpoint extend_paths_from_start_by_edges (E : edges) (l: paths) : paths :=
  match E with
  | [] => l
  | h :: t => extend_paths_from_start_by_edges t (extend_paths_from_start_by_edge h l)
  end.

Compute extend_paths_from_start_by_edges E (edges_as_paths_from_start 1 E).

(*helper 3 for paths_start_to_end_valid*)
Lemma extend_paths_from_start_by_edges_valid :
  forall (E:edges) (G:graph) (ps: paths), G_well_formed G = true ->
    (forall e, In e E -> is_edge e G = true) -> PathsValid G ps ->
      PathsValid G (extend_paths_from_start_by_edges E ps).
Proof. induction E.
  - intros G ps Hwf Hedge Hvalid. simpl. exact Hvalid.
  - intros G ps Hwf Hedge Hvalid. simpl.
    apply IHE.
    + exact Hwf.
    + intros e Hin. apply Hedge. right. exact Hin.
    + apply extend_paths_from_start_by_edge_valid.
      * exact Hwf.
      * apply Hedge. left. reflexivity.
      * exact Hvalid.
Qed.

(*helper 2 for paths_start_to_end_acyclic*)
Lemma extend_paths_from_start_by_edges_acyclic:
  forall (E:edges) (p:path) (ps:paths), no_one_cycles E = true ->
  (forall p', In p' ps -> acyclic_path_2 p') ->
  In p (extend_paths_from_start_by_edges E ps) ->
  acyclic_path_2 p.
Proof. induction E. (* the following proof can potentially be reduced by half with helper lemmas and customized tactics.*)
  - simpl. eauto.
  - destruct a as [a1 a2]. simpl. intros p ps Hacyc Hps. eapply IHE with (ps:= (extend_paths_from_start_by_edge _ ps)); eauto; clear IHE.
    {case (a1 =? a2) in Hacyc. discriminate. assumption. }
    intros pind Hin. induction ps; try auto. destruct a as [[u v] l]. simpl in Hin.
      destruct (orb (u =? a1) (u =? a2)) eqn:case1. apply orb_prop in case1.
        destruct case1.
        { apply Nat.eqb_eq in H; subst. simpl in Hin. destruct Hin as [Heq | Hin].
          - inversion Heq; subst. apply Hps. left. reflexivity.
          - apply IHps.
            + intros q Hinq. apply Hps. right. assumption.
            + assumption. }
        { apply Nat.eqb_eq in H; subst. simpl in Hin. destruct Hin as [Heq | Hin].
          - inversion Heq; subst. apply Hps. left. reflexivity.
          - apply IHps.
            + intros q Hinq. apply Hps. right. assumption.
            + assumption. }
      destruct (orb (member a1 l) (member a2 l)) eqn:case2. apply orb_prop in case2.
        destruct case2.
        { simpl in Hin. destruct Hin as [Heq | Hin'].
          - inversion Heq; subst. apply Hps. left. reflexivity.
          - apply IHps.
            + intros q Hinq. apply Hps. right. assumption.
            + assumption.
        }
        { simpl in Hin. destruct Hin as [Heq | Hin'].
          - inversion Heq; subst. apply Hps. left. reflexivity.
          - apply IHps.
            + intros q Hinq. apply Hps. right. assumption.
            + assumption.
        }
      destruct (v =? a1) eqn:case3. apply Nat.eqb_eq in case3; subst.
      { unfold add_path_no_repeats in Hin. simpl in Hin. assert (a1 <> a2).
        intro Heq; subst. rewrite Nat.eqb_refl in Hacyc. discriminate Hacyc.
        assert ((a1 =? a2) = false) as Ha12 by (apply Nat.eqb_neq; assumption).
        rewrite Ha12 in Hin. rewrite andb_false_r in Hin. rewrite andb_false_l in Hin.
        destruct (member_path (u, a2, l ++ [a1]) (extend_paths_from_start_by_edge (a1, a2) ps)) eqn:Hmem.
          - simpl in Hin. destruct Hin as [Heq | Hin]; subst.
            + eapply Hps with (p' := (u, a1, l)). simpl. left. reflexivity.
            + apply IHps; simpl; auto. intros p' Hin'. apply Hps. right. exact Hin'.
          - simpl in Hin. destruct Hin as [Heq | Hin].
            + inversion Heq; subst; clear H0. eapply Hps with (p' := (u, a1, l)). simpl. left. reflexivity.
            + apply in_app_or in Hin. destruct Hin as [Hin_tail | Hin_last].
              * apply IHps; simpl; auto. intros p' Hin'. apply Hps. right. exact Hin'.
              * simpl in Hin_last. destruct Hin_last as [Heq | Hfalse]; subst.
              apply orb_false_iff in case1. destruct case1 as [h11 h12].
              apply orb_false_iff in case2. destruct case2 as [h21 h22].
              { clear IHps H Hmem. rewrite Ha12 in Hacyc.
              specialize (Hps (u, a1, l)). pose proof (Hps (or_introl eq_refl)) as Hacyc_head; clear Hps.
              unfold acyclic_path_2 in *. constructor.
              rewrite Nat.eqb_neq in h12; auto. constructor.
              destruct Hacyc_head as [mem1 [mem2 [mem3 mem4]]].
              rewrite in_app_iff. assert (~ In u [a1]) as hright.
              { intro Hin. simpl in Hin. destruct Hin as [Heq | []]. apply Nat.eqb_neq in h11. congruence. }
              eapply Classical_Prop.and_not_or; eauto. constructor.
              destruct Hacyc_head as [mem1 [mem2 [mem3 mem4]]].
              rewrite in_app_iff. eapply Classical_Prop.and_not_or; eauto. constructor.
              { intro hn. rewrite <- member_In_equiv in hn. congruence. }
              { intro Hin. simpl in Hin. destruct Hin as [Heq | []]. apply Nat.eqb_neq in Ha12. congruence. }
              destruct Hacyc_head as [mem1 [mem2 [mem3 mem4]]].
              case l eqn:hl. simpl. auto. replace ((n :: n0) ++ [a1]) with (n :: (n0 ++ [a1])) by auto.
              assert (acyclic_path (rev (n :: n0 ++ [a1])) = true) as hrev. replace (rev (n :: n0 ++ [a1])) with
              (a1 :: rev (n :: n0)); cycle 1. rewrite app_comm_cons. rewrite rev_unit with (l:= n :: n0) (a:=a1). reflexivity.
              simpl. apply andb_true_iff. replace (rev n0 ++ [n]) with (rev (n :: n0)) by trivial. constructor.
              - rewrite negb_true_iff.
              (*helper lemma 1*)
              assert (Happ : forall xs ys, member a1 (xs ++ ys) = member a1 xs || member a1 ys).
              { induction xs as [|h t IH]; intros ys; simpl.
                - reflexivity.
                - rewrite IH. case (h =? a1). eauto. reflexivity. }
              (*helper lemma 2*)
              assert (Hrev : forall xs, member a1 (rev xs) = member a1 xs).
              { induction xs as [|h t IH]; simpl.
                - reflexivity.
                - rewrite Happ, IH. simpl. rewrite Bool.orb_comm. case (h =? a1); eauto. }
              simpl in h21. apply Bool.orb_false_iff in h21 as [Ha1n Htail]. simpl. rewrite Happ. rewrite Hrev. simpl.
              rewrite Htail. case (n =? a1) eqn: nh. apply Nat.eqb_eq in nh; subst. apply demorgan in mem3. destruct mem3 as [wrong _]. congruence. auto.
              - eapply acyclic_path_reverse; eauto.
              - replace (n :: n0 ++ [a1]) with (rev (rev (n :: n0 ++ [a1]))); cycle 1. apply rev_involutive. eapply acyclic_path_reverse; eauto.
              }
              exfalso; auto.
      }
      destruct (v =? a2) eqn:case4. apply Nat.eqb_eq in case4; subst.
      { unfold add_path_no_repeats in Hin. simpl in Hin. assert (a1 <> a2).
        intro Heq; subst. rewrite Nat.eqb_refl in Hacyc. discriminate Hacyc.
        rewrite case3 in Hin. rewrite andb_false_r in Hin. rewrite andb_false_l in Hin.
        destruct (member_path (u, a1, l ++ [a2]) (extend_paths_from_start_by_edge (a1, a2) ps)) eqn:Hmem.
          - simpl in Hin. destruct Hin as [Heq | Hin]; subst.
            + eapply Hps with (p' := (u, a2, l)). simpl. left. reflexivity.
            + apply IHps; simpl; auto. intros p' Hin'. apply Hps. right. exact Hin'.
          - simpl in Hin. destruct Hin as [Heq | Hin].
            + inversion Heq; subst; clear H0. eapply Hps with (p' := (u, a2, l)). simpl. left. reflexivity.
            + apply in_app_or in Hin. destruct Hin as [Hin_tail | Hin_last].
              * apply IHps; simpl; auto. intros p' Hin'. apply Hps. right. exact Hin'.
              * simpl in Hin_last. destruct Hin_last as [Heq | Hfalse]; subst.
              apply orb_false_iff in case1. destruct case1 as [h11 h12].
              apply orb_false_iff in case2. destruct case2 as [h21 h22].
              { clear IHps H Hmem. rewrite Nat.eqb_sym in Hacyc. rewrite case3 in Hacyc.
              specialize (Hps (u, a2, l)). pose proof (Hps (or_introl eq_refl)) as Hacyc_head; clear Hps.
              unfold acyclic_path_2 in *. constructor.
              rewrite Nat.eqb_neq in h11; auto. constructor.
              destruct Hacyc_head as [mem1 [mem2 [mem3 mem4]]].
              rewrite in_app_iff. assert (~ In u [a2]) as hright.
              { intro Hin. simpl in Hin. destruct Hin as [Heq | []]. apply Nat.eqb_neq in h12. congruence. }
              eapply Classical_Prop.and_not_or; eauto. constructor.
              destruct Hacyc_head as [mem1 [mem2 [mem3 mem4]]].
              rewrite in_app_iff. eapply Classical_Prop.and_not_or; eauto. constructor.
              { intro hn. rewrite <- member_In_equiv in hn. congruence. }
              { intro Hin. simpl in Hin. destruct Hin as [Heq | []]. apply Nat.eqb_neq in case3. congruence. }
              destruct Hacyc_head as [mem1 [mem2 [mem3 mem4]]].
              case l eqn:hl. simpl. auto. replace ((n :: n0) ++ [a2]) with (n :: (n0 ++ [a2])) by auto.
              assert (acyclic_path (rev (n :: n0 ++ [a2])) = true) as hrev. replace (rev (n :: n0 ++ [a2])) with
              (a2 :: rev (n :: n0)); cycle 1. rewrite app_comm_cons. rewrite rev_unit with (l:= n :: n0) (a:=a2). reflexivity.
              simpl. apply andb_true_iff. replace (rev n0 ++ [n]) with (rev (n :: n0)) by trivial. constructor.
              - rewrite negb_true_iff.
              (*helper lemma 1*)
              assert (Happ : forall xs ys, member a2 (xs ++ ys) = member a2 xs || member a2 ys).
              { induction xs as [|h t IH]; intros ys; simpl.
                - reflexivity.
                - rewrite IH. case (h =? a2). eauto. reflexivity. }
              (*helper lemma 2*)
              assert (Hrev : forall xs, member a2 (rev xs) = member a2 xs).
              { induction xs as [|h t IH]; simpl.
                - reflexivity.
                - rewrite Happ, IH. simpl. rewrite Bool.orb_comm. case (h =? a2); eauto. }
              simpl in h22. apply Bool.orb_false_iff in h22 as [Ha1n Htail]. simpl. rewrite Happ. rewrite Hrev. simpl.
              rewrite Htail. case (n =? a2) eqn: nh. apply Nat.eqb_eq in nh; subst. apply demorgan in mem3. destruct mem3 as [wrong _]. congruence. auto.
              - eapply acyclic_path_reverse; eauto.
              - replace (n :: n0 ++ [a2]) with (rev (rev (n :: n0 ++ [a2]))); cycle 1. apply rev_involutive. eapply acyclic_path_reverse; eauto.
              }
              exfalso; auto.
      }
      { simpl in Hin. case Hin.
      - intro H. apply Hps. left. exact H.
      - eapply IHps; eauto. intros p' Hin'. apply Hps. right. exact Hin'.
      }
Qed.

(* helper 1.3 for paths_start_to_end_correct*)
Lemma extend_paths_from_start_by_edges_start :
  forall u ps E, (forall p, In p ps -> path_start p = u) ->
  forall p, In p (extend_paths_from_start_by_edges E ps) -> path_start p = u.
Proof. intros u ps E. revert ps. induction E; simpl in *; eauto. intros. apply IHE with (ps:=(extend_paths_from_start_by_edge a ps)); eauto.
  apply extend_paths_from_start_by_edge_start. exact H.
Qed.

(* iteratively extend paths k times, like a for loop *)
Fixpoint extend_paths_from_start_iter (E: edges) (l: paths) (k: nat) : paths :=
  match k with
  | 0 => l
  | S k' => extend_paths_from_start_iter E (extend_paths_from_start_by_edges E l) k'
  end.

Compute extend_paths_from_start_iter E (edges_as_paths_from_start 1 E) 4.

(*helper 4 for paths_start_to_end_valid*)
Lemma extend_paths_from_start_iter_valid :
  forall (V:nodes) (E:edges) (n:nat) (ps:list path) (p:path),
    G_well_formed (V,E) = true -> (forall q, In q ps -> is_path_in_graph q (V,E) = true) ->
    In p (extend_paths_from_start_iter E ps n) -> is_path_in_graph p (V,E) = true.
Proof. induction n.
    - unfold extend_paths_from_start_iter. intros ps p Hwf Hall. exact (Hall p).
    - intros paths path H1 H2 H3. simpl in H3.
    pose proof (IHn (extend_paths_from_start_by_edges E paths) path H1) as Hpose.
    apply Hpose.
    + intros q Hin. pose proof (extend_paths_from_start_by_edges_valid E (V,E) paths H1) as Hvalid.
    assert (forall e : edge, In e E -> is_edge e (V, E) = true).
    { intros e Hin'. unfold is_edge. simpl. destruct e as [u v].
    pose proof ((G_well_formed_corollary V E H1 u v) Hin'). apply andb_true_iff. split.
      - apply andb_true_iff. split.
        + rewrite member_In_equiv. exact (proj1 H).
        + rewrite member_In_equiv. exact (proj2 H).
      - rewrite member_edge_In_equiv. exact Hin'. }
    assert (PathsValid (V, E) paths) as Hvalid'. unfold PathsValid. rewrite Forall_forall.
    exact (H2). pose proof (Hvalid H Hvalid') as Hvalid; clear Hvalid'.
    apply (In_PathsValid_implies_valid (V,E) _ _ Hvalid Hin).
    + exact H3.
Qed.

(*helper 3 for paths_start_to_end_acyclic*)
Lemma extend_paths_from_start_iter_acyclic:
  forall (E: edges) (p:path) (l: paths) (k: nat), no_one_cycles E = true ->
  (forall p', In p' l -> acyclic_path_2 p') ->
  In p (extend_paths_from_start_iter E l k) ->
  acyclic_path_2 p.
Proof. intros. revert H1 H0 H. revert l p E. induction k.
  - unfold extend_paths_from_start_iter. intros. exact (H0 _ H1).
  - intros. simpl in H1.
    pose proof (IHk (extend_paths_from_start_by_edges E l) p E H1) as Hpose.
    apply Hpose; eauto.
    intros q Hin. pose proof (extend_paths_from_start_by_edges_acyclic E q l) as Hacyc.
    eapply Hacyc; eauto.
Qed.

(* helper 1.4 for paths_start_to_end_correct*)
Lemma extend_paths_from_start_iter_start :
  forall u ps E n, (forall p, In p ps -> path_start p = u) ->
  forall p, In p (extend_paths_from_start_iter E ps n) -> path_start p = u.
Proof. intros u ps E n. revert u ps E. induction n; simpl in *; eauto. intros.
  eapply IHn with (ps:= (extend_paths_from_start_by_edges E ps)); eauto. apply extend_paths_from_start_by_edges_start. auto.
Qed.

(* find all acyclic undirected paths in G that start from s *)
Definition find_all_paths_from_start (s: node) (G: graph) : paths :=
  match G with
  | (V, E) => extend_paths_from_start_iter E (edges_as_paths_from_start s E) (length V)
  (* each path can have at most |V| vertices, since we consider only acyclic paths *)
  end.

Compute find_all_paths_from_start 1 G.
Compute find_all_paths_from_start 2 G.
Compute find_all_paths_from_start 3 G.
Compute find_all_paths_from_start 4 G.

(* find all paths in l that end at v *)
Fixpoint find_all_paths_to_end (v: node) (l: paths) : paths :=
  match l with
  | [] => []
  | h :: t => match h with
              | (a, b, int) => if (b =? v) then h :: (find_all_paths_to_end v t) else find_all_paths_to_end v t
              end
  end.

(* find all acyclic undirected paths in G that start at u and end at v *)
Definition find_all_paths_from_start_to_end (u v: node) (G: graph) : paths :=
  match G with
  | (V, E) => filter (fun p => v =? path_end p)
          (extend_paths_from_start_iter E (edges_as_paths_from_start u E) (length V))
  end.

Example paths_from_4_to_2: find_all_paths_from_start_to_end 4 2 G = [(4, 2, [1]); (4, 2, [1; 3])].
Proof. reflexivity. Qed.


(* correctness theorems for the find_all_paths_from_start_to_end function *)

Lemma edges_as_paths_from_start_helper : forall (u u' v' : node) (l' : nodes) (E : edges),
    In (u', v', l') (edges_as_paths_from_start u E) -> u' = u.
Proof.
  intros u u' v' l' E; induction E as [| [a b] E IH]; simpl; intro Hin.
  - contradiction.
  - destruct (u =? a) eqn:HuA; simpl in Hin.
    + destruct Hin as [Hin | Hin].
      * inversion Hin; subst; clear Hin. now apply Nat.eqb_eq in HuA.
      * now apply IH in Hin.
    + destruct (u =? b) eqn:HuB; simpl in Hin.
      * destruct Hin as [Hin | Hin].
        { inversion Hin; subst; clear Hin. now apply Nat.eqb_eq in HuB. }
        { now apply IH in Hin. }
      * now apply IH in Hin.
Qed.

(* a path outputted in the find_all_paths_from_start_to_end function is a valid path in G *)
Theorem paths_start_to_end_valid : forall u v: node, forall l: nodes, forall G: graph,
  G_well_formed G = true ->
  In (u, v, l) (find_all_paths_from_start_to_end u v G) -> is_path_in_graph (u, v, l) G = true.
Proof. intros u v l G Hwf Hin. unfold find_all_paths_from_start_to_end in Hin.
  destruct G as [V E]; simpl in Hin. apply filter_In in Hin.
  destruct Hin as [Hin Hend]. apply Nat.eqb_eq in Hend.
  induction (length V) in Hin.
    (*base case: edges_as_paths_from_start u E => is path in graph*)
  - unfold extend_paths_from_start_iter in Hin.
    apply (edges_as_paths_from_start_valid u v l V E Hwf Hin).
    (*ind case: extend_paths_from_start_iter E (paths in graph) (any n) => is path in graph *)
  - clear IHn. eapply extend_paths_from_start_iter_valid
        with (ps := edges_as_paths_from_start u E); eauto.
    intro q. destruct q as [[u' v'] l']. case (u =? u') eqn:Heq.
    (* subcase 1: q starts with u *)
    + apply Nat.eqb_eq in Heq; subst.
      apply (edges_as_paths_from_start_valid u' v' l' V E Hwf).
    (* subcase 2: ~ q starts with u -> impossible *)
    + intros Hin0. pose proof (edges_as_paths_from_start_helper u u' v' l' E Hin0) as Hu.
      rewrite Hu in Heq. rewrite Nat.eqb_refl in Heq. discriminate.
Qed.

(* a path outputted in the find_all_paths_from_start_to_end function is acyclic *)
Theorem paths_start_to_end_acyclic : forall u v: node, forall l: nodes, forall G: graph,
  no_one_cycles (snd G) = true ->
  In (u, v, l) (find_all_paths_from_start_to_end u v G) -> acyclic_path_2 (u, v, l).
Proof. intros u v l G Hloop Hin. unfold find_all_paths_from_start_to_end in Hin.
  destruct G as [V E]; simpl in Hin. apply filter_In in Hin. simpl in Hin, Hloop. destruct Hin as [Hin _].
  revert Hin. induction (length V).
  - intro Hin. simpl in Hin. eapply edges_as_paths_from_start_acyclic; eauto.
  - intro Hin. simpl in Hin. eapply extend_paths_from_start_iter_acyclic; eauto.
    intro p1. eapply extend_paths_from_start_by_edges_acyclic; eauto.
    intro p2. eapply edges_as_paths_from_start_acyclic; eauto.
Qed.

(*helper 2 for paths_start_to_end_correct*)
Lemma paths_start_to_end_endpoints :
  forall u v l G,
    In (u, v, l) (find_all_paths_from_start_to_end u v G) ->
    path_start_and_end (u, v, l) u v = true.
Admitted.

(*helper 3 for paths_start_to_end_correct*)
Lemma find_all_paths_complete :
  forall G u v p,
    G_well_formed G = true ->
    no_one_cycles (snd G) = true ->
    is_path_in_graph p G = true ->
    path_start_and_end p u v = true ->
    acyclic_path_2 p ->
    In p (find_all_paths_from_start_to_end u v G).
Admitted.

(* an acyclic path from u to v is in G iff it is outputted in the find_all_paths_from_start_to_end function *)
Theorem paths_start_to_end_correct : forall p: path, forall u v: node, forall G: graph,
  G_well_formed G = true -> no_one_cycles (snd G) = true -> (
      (is_path_in_graph p G = true) /\ (path_start_and_end p u v = true) /\ acyclic_path_2 p
  <-> In p (find_all_paths_from_start_to_end u v G) ).
Proof. intros [[u' v'] l] u v [V E] Hwf Hno. split.
  - (* -> completeness *)
    intros (Hpath & Hend & Hacyc).
    eapply find_all_paths_complete; eauto.
  - (* <- soundness *)
    intro Hin. assert (u = u' /\ v = v').
    { unfold find_all_paths_from_start_to_end in Hin. apply filter_In in Hin. simpl in Hin. destruct Hin as [Hin Hend].
    constructor; cycle 1. rewrite Nat.eqb_eq in Hend. auto. clear Hend.
    eapply extend_paths_from_start_iter_start in Hin; eauto. eapply edges_as_paths_from_start_start; eauto.
    } destruct H as [h1 h2]; subst.
    split.
    + eapply paths_start_to_end_valid; eauto.
    + split.
      * eapply paths_start_to_end_endpoints; eauto.
      * eapply paths_start_to_end_acyclic; eauto.
Qed.




(* below we define functions to find all undirected acyclic paths in G, without a specific
   start or end node. They follow the same structure as the above process to find all paths in a graph
   from a given start node to a given end node. The below functions are not used further in this
   repository, but are included for future work. *)

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
