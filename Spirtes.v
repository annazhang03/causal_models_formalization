From FCM Require Export CausalModels.
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


(* all nodes in the given list of colliders, cols, are ancestors of either u or v *)
Definition all_given_nodes_are_ancestors (cols: nodes) (u v: node) (G: graph) : Prop :=
  forall (c: node), In c cols -> In u (find_descendants c G) \/ In v (find_descendants c G).

Definition all_colliders_are_ancestors (p: path) (G: graph): Prop :=
  match p with
  | (u, v, l) => all_given_nodes_are_ancestors (find_colliders_in_path p G) u v G
  end.

(* return True iff all nodes in O on U are colliders in U *)
Fixpoint observed_nodes_are_colliders (U: path) (O: nodes) (G: graph) : Prop :=
  match U with 
  | (u, v, l) => match O with
                 | [] => True
                 | h :: t => if (member h l) then is_collider_in_path h U G /\ observed_nodes_are_colliders U t G
                             else observed_nodes_are_colliders U t G
                 end
  end.

(* return True iff U is an inducing path on G over O
   According to Spirtes, this is true iff every non-endpoint member of O on U is a collider on U,
   and every collider on U is an ancestor of either A or B. *)
Definition inducing_path (U: path) (G: graph) (O: nodes) : Prop :=
  is_path_in_graph U G = true /\ all_colliders_are_ancestors U G 
                              /\ observed_nodes_are_colliders U O G.

Lemma inducing_path_out_of_A: forall G: graph, forall O: nodes, forall A B: node,
  contains_cycle G = false ->
  (exists U: path, path_start_and_end U A B = true /\ path_out_of_start U G = true /\ inducing_path U G O) ->
  (forall Z: nodes, subset Z (set_subtract O [A; B]) = true -> 
   exists p: path, is_path_in_graph p G = true /\ path_start_and_end p A B = true
                                                 /\ path_out_of_start p G = true
                                                 /\ d_connected_2 p G Z).
Proof.
Admitted.

Lemma inducing_path_into_A: forall G: graph, forall O: nodes, forall A B: node,
  contains_cycle G = false ->
  (exists U: path, path_start_and_end U A B = true /\ path_into_start U G = true /\ inducing_path U G O) ->
  (forall Z: nodes, subset Z (set_subtract O [A; B]) = true -> 
   exists p: path, is_path_in_graph p G = true /\ path_start_and_end p A B = true
                                                 /\ path_into_start p G = true
                                                 /\ d_connected_2 p G Z).
Proof.
Admitted.

(* for an undirected path U in G from A to B, any node on U is an ancestor of A, B, or some collider on U *)
Theorem path_nodes_ancestors: forall U: path, forall G: graph, forall A B X: node,
  is_path_in_graph U G = true /\ path_start_and_end U A B = true /\ path_contains_node U X = true
  -> In X (find_ancestors A G) \/ In X (find_ancestors B G) 
     \/ (exists C, In C (find_colliders_in_path U G) /\ In X (find_ancestors C G)).
Proof. 
Admitted.


(* Lemma 3 from Spirtes
   If G is a DAG, and A and B are not d-separated by any subset Z of O\{A,B}, then 
   there is an inducing path over O between A and B.
*)
Lemma not_d_separated: forall G: graph, forall O: nodes, forall A B: node,
  contains_cycle G = false ->
  (forall Z: nodes, subset Z (set_subtract O [A; B]) = true -> (d_separated_bool A B G Z = false)) ->
  exists U: path, path_start_and_end U A B = true /\ inducing_path U G O.
Proof.
  intros G O A B.
  intros acyclic d_sep.
  destruct (is_edge (A, B) G) as [|] eqn:edgeAB.
  (* if (A, B) is an edge in G, then that edge is an inducing path *)
  - exists (A, B, []). split.
    + unfold path_start_and_end. simpl. rewrite eqb_refl. simpl. apply eqb_refl.
    + unfold inducing_path. split.
      * simpl. rewrite edgeAB. destruct G as [V E]. reflexivity.
      * split.
        (* no colliders, so trivially all colliders are ancestors of A or B *)
        -- cbn. unfold all_given_nodes_are_ancestors. intros c contra. 
           simpl in contra. exfalso. apply contra.
        (* no observed nodes that are also non-endpoints on U, so trivially all are colliders *)
        -- induction O as [| h t IH].
           ++ simpl. apply I.
           ++ simpl. apply IH. intros Z HZ.
              apply d_sep. simpl. destruct (A =? h) as [|] eqn:HAh.
              { destruct (B =? h) as [|] eqn:HBh.
                - simpl. apply HZ.
                - simpl. apply HZ. }
              { destruct (B =? h) as [|] eqn:HBh.
                - simpl. apply HZ.
                - simpl. induction Z as [| hZ tZ IHZ].
                  + simpl. reflexivity.
                  + simpl. destruct (h =? hZ) as [|] eqn:HhhZ.
                    * simpl. apply IHZ. simpl in HZ. rewrite andb_comm in HZ. apply andb_true_elim2 in HZ. apply HZ.
                    * simpl in HZ. apply split_and_true in HZ. destruct HZ as [mem sub].
                      rewrite mem. simpl. apply IHZ. apply sub. }
  - destruct (is_edge (B, A) G) as [|] eqn:edgeBA.
    (* if (B, A) is an edge in G, then that edge is an inducing path *)
    + exists (A, B, []). split.
      * unfold path_start_and_end. simpl. rewrite eqb_refl. simpl. apply eqb_refl.
      * unfold inducing_path. split.
        -- simpl. rewrite edgeBA. rewrite orb_comm. destruct G as [V E]. reflexivity.
        -- split.
           (* no colliders, so trivially all colliders are ancestors of A or B *)
            --- simpl. unfold all_given_nodes_are_ancestors. intros c contra.
                simpl in contra. exfalso. apply contra.
            (* no observed nodes that are also non-endpoints on U, so trivially all are colliders *)
            --- induction O as [| h t IH].
               ++ simpl. apply I.
               ++ simpl. apply IH. intros Z HZ.
                  apply d_sep. simpl. destruct (A =? h) as [|] eqn:HAh.
                  { destruct (B =? h) as [|] eqn:HBh.
                    - simpl. apply HZ.
                    - simpl. apply HZ. }
                  { destruct (B =? h) as [|] eqn:HBh.
                    - simpl. apply HZ.
                    - simpl. induction Z as [| hZ tZ IHZ].
                      + simpl. reflexivity.
                      + simpl. destruct (h =? hZ) as [|] eqn:HhhZ.
                        * simpl. apply IHZ. simpl in HZ. rewrite andb_comm in HZ. apply andb_true_elim2 in HZ. apply HZ.
                        * simpl in HZ. apply split_and_true in HZ. destruct HZ as [mem sub].
                          rewrite mem. simpl. apply IHZ. apply sub. }
    (* neither (A, B) nor (B, A) are edges in G *)
    + remember (union (find_ancestors A G) (find_ancestors B G)) as allAnc. (* allAnc = anc(A) \cup anc(B) *)
      remember (intersect (set_subtract O [A; B]) allAnc) as O'. (* O' = allAnc \cap O\{A,B} *)
      specialize (d_sep O').
      assert (Hsubset: subset O' (set_subtract O [A; B]) = true).
      { rewrite HeqO'. apply intersect_correct. }
      apply d_sep in Hsubset.
      unfold d_separated_bool in Hsubset. 
      (* there is a path U between A and B, that is not blocked over O' *)
      apply demorgan_many_bool in Hsubset. destruct Hsubset as [U [HUpath HUblocked]].
      apply paths_start_to_end_correct in HUpath. destruct HUpath as [HUpath [HUse HUacyc]].
      exists U.
      split.
      * apply HUse.
      * unfold inducing_path. split.
        -- apply HUpath.
        -- split.
           ++ (* show that for all colliders C in U, C is an ancestor of some member of O' *)
              assert (HcolInO': forall C: node, is_collider_in_path C U G 
                                -> exists d: node, In d O' /\ In d (find_descendants C G)).
              { intros C Hcol. unfold path_is_blocked_bool in HUblocked.
                rewrite orb_comm in HUblocked. apply orb_true_elim2 in HUblocked.
                unfold is_blocked_by_collider_2 in HUblocked.
                unfold collider_descendants_not_conditioned2 in HUblocked.
                (* why were next 5 lines so complicated TODO *)
                remember (fun c : node => descendants_not_in_Z_bool (find_descendants c G) O') as P.
                remember (find_colliders_in_path U G) as ls.
                destruct (demorgan_many_bool_2 node P ls) as [Hf _].
                assert (Hfa: forall x : node, In x ls -> P x = false).
                { apply Hf. apply HUblocked. }
                specialize (Hfa C). 
                apply colliders_in_path in Hcol. rewrite <- Heqls in Hcol. apply Hfa in Hcol.
                rewrite HeqP in Hcol.
                unfold descendants_not_in_Z_bool in Hcol. (* exists a desc of C that is in O' *)
                apply demorgan_many_bool in Hcol. destruct Hcol as [desc [Hdesc HdescO]].
                exists desc. split. 
                - apply member_In_equiv. apply negb_both_sides in HdescO. simpl in HdescO. apply HdescO.
                - apply Hdesc. }
              (* since colliders are all ancestors of a member of O', then they must also be
                 ancestors of A or B *)
              destruct U as [[u v] l]. unfold all_colliders_are_ancestors.
              apply path_start_end_equal in HUse. destruct HUse as [HuA HvB].
              rewrite HuA. rewrite HvB.
              unfold all_given_nodes_are_ancestors. intros C Hcol. apply colliders_in_path in Hcol.
              rewrite HuA in HcolInO'. rewrite HvB in HcolInO'.
              assert (Hd: exists d : node, In d O' /\ In d (find_descendants C G)). 
              { apply HcolInO' in Hcol. apply Hcol. }
              destruct Hd as [d [HdO' Hdesc]].
              (* C is an ancestor of d, which is a member of O'
                 In order to show that C is an ancestor of A or B, can show that d is an ancestor of A or B *)
              assert (HdIsAnc: In d (find_ancestors A G) \/ In d (find_ancestors B G)).
              { rewrite HeqO' in HdO'. apply intersect_correct_element in HdO'.
                rewrite HeqallAnc in HdO'. apply union_correct in HdO'. apply HdO'. }
              destruct HdIsAnc as [HdA | HdB].
              ** left. apply descendants_ancestors_correct.
                 --- apply nodes_in_path_in_graph in HUpath. destruct HUpath as [HAG [HBG HCG]].
                     rewrite HuA in HAG. specialize (HCG C). split.
                     apply HAG. unfold is_collider_in_path in Hcol.

      

(* 
Steps:
1. functions: list union and intersection
2. proof: subset A (intersect A B) = true
3. proof: x in (union A B) => x in A || x in B
4. function: find ancestors of a node
5. proof: x descendant of y <=> y ancestor of x
6. proof: every vertex on U is an ancestor of A, B, or a collider on U
*)
Admitted.

(* Theorem 1 from Spirtes
   If G is a DAG over variables V, and O \subseteq V, then A and B are not d-separated 
   by any subset of O\{A, B} <=> there is an inducing path over O between A and B.
   TODO didn't use assumption that vertex_subset O G = true.
*)
Theorem d_separation_and_inducing_paths: forall G: graph, forall O: nodes, forall A B: node,
  contains_cycle G = false /\ vertex_subset O G = true ->
  (forall Z: nodes, subset Z (set_subtract O [A; B]) = true -> d_separated_bool A B G Z = false)
  <-> exists U: path, path_start_and_end U A B = true /\ inducing_path U G O.
Proof.
  intros G O A B.
  intros [acyclic subset].
  split.
  (* forward direction: G acyclic and A and B are not d-separated by any Z => exists an inducing path *)
  - apply not_d_separated. apply acyclic.
  (* backward direction: G acyclic and exists an inducing path between A and B => A and B not d-separated by any Z *)
  - intros [U HU]. intros Z subsetZ. apply d_separated_vs_connected. 
    destruct (path_into_start U G) as [|] eqn:Udir.
    (* inducing path goes into A, apply Lemma 2 *)
    + pose proof inducing_path_into_A as lemma.
      specialize (lemma G O A B).
      specialize (lemma acyclic).
      assert (H: path_start_and_end U A B = true /\ path_into_start U G = true /\ inducing_path U G O).
      { rewrite and_comm. rewrite and_assoc. rewrite and_comm. split.
        - rewrite and_comm. apply HU.
        - apply Udir. }
      specialize (lemma (ex_intro _ U H)).
      specialize (lemma Z subsetZ).
      destruct lemma as [p [p_in_graph [p_A_to_B [p_into_A p_d_conn]]]]. destruct p as [[u v] l].
      apply path_start_end_equal in p_A_to_B. destruct p_A_to_B as [HuA HvB].
      rewrite <- HuA. rewrite <- HvB. exists l.
      split. 
      * apply contains_cycle_false_correct with (G:=G). apply acyclic. apply p_in_graph.
      * split. apply p_in_graph. apply p_d_conn.
    (* inducing path goes out of A, apply Lemma 1 *)
    + pose proof inducing_path_out_of_A as lemma.
      specialize (lemma G O A B).
      specialize (lemma acyclic).
      assert (H: path_start_and_end U A B = true /\ path_out_of_start U G = true /\ inducing_path U G O).
      { rewrite and_comm. rewrite and_assoc. rewrite and_comm. split.
        - rewrite and_comm. apply HU.
        - apply path_must_have_direction in Udir. apply Udir.
          destruct HU as [UAB indpath].
          unfold inducing_path in indpath. destruct indpath as [p_in_G _]. apply p_in_G. }
      specialize (lemma (ex_intro _ U H)).
      specialize (lemma Z subsetZ).
      destruct lemma as [p [p_in_graph [p_A_to_B [p_out_of_A p_d_conn]]]]. destruct p as [[u v] l].
      apply path_start_end_equal in p_A_to_B. destruct p_A_to_B as [HuA HvB].
      rewrite <- HuA. rewrite <- HvB. exists l.
      split. 
      * apply contains_cycle_false_correct with (G:=G). apply acyclic. apply p_in_graph.
      * split. apply p_in_graph. apply p_d_conn.
Qed.