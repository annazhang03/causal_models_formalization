From FCM Require Import DAG_Basics.
From FCM Require Import Helpers.

Import ListNotations.

(* Finding paths in a graph *)

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

(* add p to end of l if p is not already in l *)
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


Lemma path_monotone_edges :
  forall V E a p,
    is_path_in_graph p (V,E) = true ->
    is_path_in_graph p (V, a::E) = true.
Proof. intros V E a p H. destruct p as [[u v] l]. unfold is_path_in_graph in *.
  apply (is_path_in_graph_helper_monotone_edges V E a ((u :: l) ++ [v]) H).
Qed.


Lemma edges_as_paths :
  forall V x y (E: edges), In x V -> In y V ->
    is_path_in_graph (x,y,[]) (V, (x,y)::E) = true.
Proof. intros V x y E Hx Hy. unfold is_path_in_graph. simpl.
  apply andb_true_iff. split.
  - apply orb_true_iff. left. apply andb_true_iff. split.
    apply andb_true_iff. split; rewrite member_In_equiv; assumption.
    apply orb_true_iff. left. apply andb_true_iff; split; apply Nat.eqb_refl.
  - reflexivity.
Qed.
Lemma edges_as_paths2 :
  forall V x y E, In x V -> In y V ->
    is_path_in_graph (y,x,[]) (V, (x,y)::E) = true.
Proof. intros V x y E Hx Hy. unfold is_path_in_graph. simpl.
  apply andb_true_iff. split.
  - apply orb_true_iff. right. apply andb_true_iff. split.
    apply andb_true_iff. split; rewrite member_In_equiv; assumption.
    apply orb_true_iff. left. apply andb_true_iff; split; apply Nat.eqb_refl.
  - reflexivity.
Qed.


Lemma G_well_formed_corollary : forall (V: nodes) (E: edges),
  G_well_formed (V, E) = true -> forall (u v :node), In (u, v) E -> In u V /\ In v V.
Proof.
  intros V E Hwf u v Hin. unfold G_well_formed in Hwf.
  apply andb_prop in Hwf. destruct Hwf as [Hwf _].
  apply andb_prop in Hwf. destruct Hwf as [Hwf _].
  rewrite forallb_forall in Hwf. pose proof (Hwf (u,v) Hin); simpl in H.
  apply andb_true_iff in H. repeat rewrite <- member_In_equiv. exact H.
Qed.


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
  rewrite edges_as_paths; [reflexivity | exact Hu | exact Hv].
  - specialize (IHE (Hwf') Hin). now apply path_monotone_edges with (a := (x,y)).
  (*u=y case*)
  - destruct (u =? y) eqn:Hy. simpl in Hin. rewrite Hy in Hin. rewrite Hx in Hin.
  simpl in Hin. destruct Hin as [Hin | Hin].
    + inversion Hin; subst; clear Hin.
    pose proof (G_well_formed_corollary V ((v,u)::E) Hwf v u (or_introl eq_refl)) as [Hu Hv].
    rewrite edges_as_paths2; [reflexivity | exact Hu | exact Hv].
    + specialize (IHE (Hwf') Hin). now apply path_monotone_edges with (a := (x,y)).
  (*u!=x and u!=y case*)
    + simpl in Hin. rewrite Hx in Hin. rewrite Hy in Hin. specialize (IHE (Hwf') Hin).
  eapply path_monotone_edges with (a := (x,y)) in IHE. exact IHE.
Qed.


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

(* given a path p, add all concatenations of p with paths in l to the list of paths *)
Fixpoint extend_paths_from_start_by_edges (E : edges) (l: paths) : paths :=
  match E with
  | [] => l
  | h :: t => extend_paths_from_start_by_edges t (extend_paths_from_start_by_edge h l)
  end.

Compute extend_paths_from_start_by_edges E (edges_as_paths_from_start 1 E).


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

(* iteratively extend paths k times, like a for loop *)
Fixpoint extend_paths_from_start_iter (E: edges) (l: paths) (k: nat) : paths :=
  match k with
  | 0 => l
  | S k' => extend_paths_from_start_iter E (extend_paths_from_start_by_edges E l) k'
  end.

Compute extend_paths_from_start_iter E (edges_as_paths_from_start 1 E) 4.


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

Theorem paths_start_to_end_valid : forall u v: node, forall l: nodes, forall G: graph,
  G_well_formed G = true
  -> In (u, v, l) (find_all_paths_from_start_to_end u v G) -> is_path_in_graph (u, v, l) G = true.
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
    + apply Nat.eqb_eq in Hxueq. rewrite Hxueq in Hmem. unfold not in Hxu. apply Hxu in Hmem. exfalso. apply Hmem.
    + apply Nat.eqb_neq. apply Hxueq.
  - destruct (x =? v) as [|] eqn:Hxveq.
    + apply Nat.eqb_eq in Hxveq. rewrite Hxveq in Hmem. unfold not in Hxv. apply Hxv in Hmem. exfalso. apply Hmem.
    + apply Nat.eqb_neq. apply Hxveq.
Qed.
