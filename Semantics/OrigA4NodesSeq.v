From Semantics Require Import OrigA4Nodes.
From Semantics Require Import ConditionallyIndependentDef.
From CausalDiagrams Require Import CausalPaths.
From CausalDiagrams Require Import IntermediateNodes.
From CausalDiagrams Require Import Assignments.
From CausalDiagrams Require Import DSeparation.
From CausalDiagrams Require Import UnblockedAncestors.
From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.
From Utils Require Import EqType.

Fixpoint get_assignment_sequence_from_A4 {X: Type} `{EqType X} (A4: nodes) (U: assignments X) (x: X): list (assignments X) :=
  match A4 with
  | [] => []
  | h :: t => ((h, x) :: U) :: (get_assignment_sequence_from_A4 t ((h, x) :: U) x)
  end.

Fixpoint get_assignment_sequence_from_A4' {X: Type} `{EqType X} (A4: nodes) (U: assignments X) (x: X): option (list (assignments X)) :=
  match A4 with
  | [] => Some []
  | h :: t => match (get_assigned_value U h) with
              | Some hu => if (eqb hu x) then get_assignment_sequence_from_A4' t ((h, x) :: U) x
                           else match (get_assignment_sequence_from_A4' t ((h, x) :: U) x) with
                                | Some r => Some (((h, x) :: U) :: r)
                                | None => None
                                end
              | None => None
              end
  end.

Lemma assignment_sequence_from_A4_existence_gen {X: Type} `{EqType X}: forall (A4: nodes) (U: assignments X) (x: X),
  is_assignment_for U A4 = true
  -> exists (seq: list (assignments X)), get_assignment_sequence_from_A4' A4 U x = Some seq.
Proof.
  intros A4 U x HU.
  generalize dependent U. induction A4 as [| h t IH].
  - simpl. exists []. reflexivity.
  - intros U HU. simpl.
    assert (Hh: exists (hu: X), get_assigned_value U h = Some hu).
    { apply assigned_has_value with (L := h :: t). split. left. reflexivity. apply HU. }
    destruct Hh as [hu Hh]. rewrite Hh. destruct (eqb hu x) as [|] eqn:Hhu.
    + apply IH. apply is_assignment_for_cat. simpl in HU. apply split_and_true in HU. apply HU.
    + assert (Hind: exists (seq: list (assignments X)), get_assignment_sequence_from_A4' t ((h, x) :: U) x = Some seq).
      { apply IH. apply is_assignment_for_cat. simpl in HU. apply split_and_true in HU. apply HU. }
      destruct Hind as [seq Hind]. exists (((h, x) :: U) :: seq). rewrite Hind. reflexivity.
Qed.

Lemma assignment_sequence_from_A4_existence {X: Type} `{EqType X}: forall (G: graph) (A4: nodes) (p: path) (U: assignments X) (x: X),
  is_assignment_for U (nodes_in_graph G) = true
  -> G_well_formed G = true
  -> is_path_in_graph p G = true
  -> get_A4_binded_nodes_in_g_path G p = A4
  -> exists (seq: list (assignments X)), get_assignment_sequence_from_A4' A4 U x = Some seq.
Proof.
  intros G A4 p U x HU HG Hp HA4.
  apply assignment_sequence_from_A4_existence_gen. apply forallb_true_iff_mem. intros w Hw.
  apply forallb_true_iff_mem with (x := w) in HU. apply HU.
  rewrite <- HA4 in Hw. destruct p as [[u v] l]. apply A4_nodes_in_graph in Hw.
  - destruct G as [V E]. apply member_In_equiv. apply Hw.
  - apply HG.
  - apply Hp.
Qed.

Lemma assignment_sequence_len_shorter_than_A4 {X: Type} `{EqType X}: forall (A: nodes) (U: assignments X) (L: list (assignments X)) (x: X),
  get_assignment_sequence_from_A4 A U x = L
  -> length L <= length A.
Proof.
  intros A U L x HL.
  generalize dependent U. generalize dependent L.
  induction A as [| h t IH].
  - intros L U HL. simpl in HL. rewrite <- HL. simpl. lia.
  - intros L U HL. simpl in HL. assert (Hind: length (get_assignment_sequence_from_A4 t ((h, x) :: U) x) <= length t).
    { apply IH with (U := (h, x) :: U). reflexivity. }
    rewrite <- HL. simpl. f_equal. lia.
Qed.

Lemma assignment_sequence_len_shorter_than_path {X: Type} `{EqType X}: forall (G: graph) (p: path) (U: assignments X) (L: list (assignments X)) (x: X),
  is_path_in_graph p G = true
  -> contains_cycle G = false
  -> get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G p) U x = L
  -> length L <= path_length p.
Proof.
  intros G [[u v] l] U L x Hp Hc HL.
  assert (Hl: length (get_A4_binded_nodes_in_g_path G (u, v, l)) <= path_length (u, v, l)).
  { apply A4_nodes_len with (G := G). apply Hp. apply Hc. reflexivity. }
  assert (Hl': length L <= length (get_A4_binded_nodes_in_g_path G (u, v, l))).
  { apply assignment_sequence_len_shorter_than_A4 with (U := U) (x := x). apply HL. }
  lia.
Qed.

Lemma assignment_sequence_len_U {X: Type} `{EqType X}: forall (A: nodes) (U U': assignments X) (L L': list (assignments X)) (x: X),
  get_assignment_sequence_from_A4 A U x = L
  -> get_assignment_sequence_from_A4 A U' x = L'
  -> length L = length L'.
Proof.
  intros A U U' L L' x HL HL'.
  generalize dependent L. generalize dependent L'. generalize dependent U. generalize dependent U'.
  induction A as [| h t IH].
  - intros U' U L' HL' L HL. simpl in HL. rewrite <- HL. simpl in HL'. rewrite <- HL'. reflexivity.
  - intros U' U L' HL' L HL. simpl in HL. simpl in HL'.
    assert (Hind: length (get_assignment_sequence_from_A4 t ((h, x) :: U') x) = length (get_assignment_sequence_from_A4 t ((h, x) :: U) x)).
    { apply IH with (U := (h, x) :: U') (U' := (h, x) :: U). reflexivity. reflexivity. }
    rewrite <- HL. rewrite <- HL'. simpl. f_equal. symmetry. apply Hind.
Qed.

Lemma assignment_sequence_fst {X: Type} `{EqType X}: forall (A4: nodes) (U Ux: assignments X) (LUx: list (assignments X)) (x: X) (h: node),
  get_assignment_sequence_from_A4 (h :: A4) U x = Ux :: LUx
  -> Ux = ((h, x) :: U).
Proof.
  intros A4 U Ux LUx x h HA. simpl in HA. inversion HA. reflexivity.
Qed.

Lemma assignment_sequence_U {X: Type} `{EqType X}: forall (A4: nodes) (U: assignments X) (L: list (assignments X)) (x: X) (G: graph),
  get_assignment_sequence_from_A4 A4 U x = L
  -> is_assignment_for U (nodes_in_graph G) = true
  -> forall (U': assignments X), In U' L -> is_assignment_for U' (nodes_in_graph G) = true.
Proof.
  intros A4 U L x G HL HU U' HU'.
  generalize dependent L. generalize dependent U. induction A4 as [| h t IH].
  - intros U HU L HL HU'. simpl in HL. rewrite <- HL in HU'. exfalso. apply HU'.
  - intros U HU L HL HU'. simpl in HL. rewrite <- HL in HU'. destruct HU' as [HU' | HU'].
    + rewrite <- HU'. apply is_assignment_for_cat. apply HU.
    + apply IH with (L := get_assignment_sequence_from_A4 t ((h, x) :: U) x) (U := ((h, x) :: U)).
      * apply is_assignment_for_cat. apply HU.
      * reflexivity.
      * apply HU'.
Qed.

Lemma assignments_change_A4 {X: Type} `{EqType X}: forall (U Ux AZ: assignments X) (Z: nodes) (G: graph) (LUx: list (assignments X)) (x: X) (p: path),
  G_well_formed G = true
  -> contains_cycle G = false
  -> ~ In (path_start p) Z /\ ~ In (path_end p) Z
  -> is_path_in_graph p G = true
  -> acyclic_path_2 p
  -> d_connected_2 p G Z
  -> is_assignment_for AZ Z = true
  -> (forall (w: node), In w (get_A4_binded_nodes_in_g_path G p) -> (exists (r: X), get_assigned_value U w = Some r /\ eqb r x = false))
  -> get_assignment_sequence_from_A4 (get_A4_binded_nodes_in_g_path G p) U x = Ux :: LUx
  -> is_assignment_for U (nodes_in_graph G) = true
  -> assignments_change_only_for_Z_anc_seq' (U :: Ux :: LUx) Z AZ G.
Proof.
  intros U Ux AZ Z G LUx x p. intros HG1 HG2 HZ Hp Hcyc Hconn HAZ HUx HA HU.

  destruct (get_A4_binded_nodes_in_g_path G p) as [| a l4] eqn:HA4.
  simpl in HA. discriminate HA.
  destruct l4 as [| b l4]. simpl in HA. inversion HA. simpl. apply I.

  generalize dependent a. generalize dependent b. generalize dependent l4. generalize dependent p.
  generalize dependent U. generalize dependent Ux. induction LUx as [| U1 LUx' IH].
  - intros Ux U HU p HZ Hp Hcyc Hconn l4 b a HA4 HUx HA. simpl. apply I.
  - intros Ux U HU p HZ Hp Hcyc Hconn l4 b a HA4 HUx HA. simpl. split.
    * simpl in HA. (* destruct (get_assigned_value U a) as [au|]. destruct (eqb au x) as [|]. *) inversion HA.
      unfold assignments_change_only_for_subset. intros w. split.
      -- apply is_assigned_iff_cat. apply assigned_is_true. apply assigned_has_value with (L := nodes_in_graph G).
         split.
         assert (Hb: node_in_graph b G = true). { apply A4_nodes_in_graph with (u := path_start p) (v := path_end p) (l := path_int p). apply HG1.
          destruct p as [[u v] l]. apply Hp. destruct p as [[u v] l]. simpl. simpl in HA4. rewrite HA4. right. left. reflexivity. }
         destruct G as [V E]. simpl. apply member_In_equiv. simpl in Hb. apply Hb.
         apply is_assignment_for_cat. apply HU.
      -- intros Hw. simpl. destruct (a =? w) as [|] eqn:Haw.
         destruct (b =? w) as [|]. reflexivity. reflexivity.
         destruct (b =? w) as [|] eqn:Hbw.
         ++ (* u ... <-a-> ..->z<-.. <-b-> ...
               b is unblocked anc of z, which changed due to a, so contradicts Hw *)
            apply eqb_eq in Hbw. rewrite <- Hbw in *. clear Hbw.
            apply conditioned_node_between_A4_nodes with (Z := Z) in HA4 as Hz. destruct Hz as [z Hz]. exfalso. apply Hw.
            apply ancestor_in_Z_corresponds_to_conditioned_node with (z := z).
            ** apply assigned_is_true. apply assigned_has_value with (L := Z). split. apply Hz. apply HAZ.
            ** split. apply Hz.
               assert (Hau: exists (au: X), get_assigned_value U a = Some au /\ eqb au x = false). { apply HUx. left. reflexivity. }
               destruct Hau as [au Hau].
               apply in_unblocked_that_changed_cat with (u := a) (r := au) (x := x) in HU.
               --- exists a. split. apply Hz. apply HU.
               --- apply Hau.
               --- assert (Ha: node_in_graph a G = true). { apply A4_nodes_in_graph with (u := path_start p) (v := path_end p) (l := path_int p). apply HG1.
                    destruct p as [[u v] l]. apply Hp. destruct p as [[u v] l]. simpl. simpl in HA4. rewrite HA4. left. reflexivity. }
                   destruct G as [V E]. simpl. apply member_In_equiv. simpl in Ha. apply Ha.
               --- intros Haux. destruct Hau as [_ Hau]. rewrite Haux in Hau. rewrite eqb_refl' in Hau. discriminate Hau.
            ** apply HG2.
            ** apply HZ.
            ** apply Hp.
            ** apply Hcyc.
            ** apply Hconn.
         ++ reflexivity.
    * destruct p as [[u v] l].
      destruct l4 as [| c l4]. simpl in HA. inversion HA. apply I.
      (* b not equal to v since c comes after in A4 *)
      assert (Hb: In b l).
      { apply mid_A4_nodes_in_path in HA4. apply HA4. apply Hp. }
      apply membership_splits_list in Hb. destruct Hb as [l1 [l2 Hb]].
      specialize IH with (p := (b, v, l2)) (l4 := l4) (a := b) (b := c) (Ux := U1) (U := Ux).
      apply IH.
      -- simpl in HA. inversion HA. apply is_assignment_for_cat. apply HU.
      -- simpl. split.
         ++ apply A4_nodes_not_in_Z with (G := G) (p := (u, v, l)). rewrite HA4. right. left. reflexivity. apply HZ. apply Hconn.
         ++ apply HZ.
      -- apply subpath_still_path with (w := u) (l1 := l1) (l3 := l). split. apply Hb. apply Hp.
      -- apply subpath_still_acyclic with (w := u) (l1 := l1) (l3 := l). split. apply Hb. apply Hcyc.
      -- apply subpath_still_d_connected_gen with (w := u) (l1 := l1) (l3 := l). split. apply Hb. apply Hconn.
      -- apply subpath_preserves_A4 with (u := u) (l1 := l1) (A := c :: l4) (l := l) (A' := [a]). apply HG2. apply Hp. apply HA4. apply Hb. apply Hcyc.
      -- intros w Hw. assert (Hind: exists (r: X), get_assigned_value U w = Some r /\ eqb r x = false).
         { apply HUx. right. apply Hw. } destruct Hind as [r Hr].
         simpl in HA. inversion HA. simpl.
         destruct (a =? w) as [|] eqn:Haw.
         ++ (* Hw and Haw and HA4 contradict acyclic *) exfalso.
            assert (Hcount: count w (a :: b :: c :: l4) = 1). { rewrite <- HA4. apply A4_count_acyclic.
              rewrite HA4. right. apply Hw. apply Hcyc. apply Hp. }
            simpl in Hcount. rewrite Haw in Hcount. inversion Hcount. apply member_count_at_least_1 in Hw. simpl in Hw. lia.
         ++ exists r. apply Hr.
      -- simpl. simpl in HA. inversion HA. reflexivity.
Qed.

Lemma list_assignments_assignments_equiv {X: Type} `{EqType X}: forall (L L': list (assignments X)) (x: X) (A: nodes) (U U': assignments X),
  assignments_equiv U U'
  -> L = get_assignment_sequence_from_A4 A U x
  -> L' = get_assignment_sequence_from_A4 A U' x
  -> list_assignments_equiv L L'.
Proof.
  intros L L' x A U U' HU HL HL'.
  generalize dependent L'. generalize dependent A. generalize dependent U. generalize dependent U'.
  induction L as [| h t IH].
  - intros U' U HU A HL L' HL'. destruct A as [| ha ta]. simpl in HL'. rewrite HL'. simpl. apply I.
    simpl in HL. discriminate HL.
  - intros U' U HU A HL L' HL'. destruct A as [| ha ta]. simpl in HL. discriminate HL.
    assert (Hta: assignments_equiv ((ha, x) :: U) ((ha, x) :: U')).
    { unfold assignments_equiv. intros u. simpl. destruct (ha =? u) as [|]. reflexivity.
      apply HU. }
    simpl in HL'. simpl in HL. inversion HL. inversion HL'. simpl. split.
    + apply Hta.
    + rewrite <- H2. apply IH with (U' := (ha, x) :: U') (U := (ha, x) :: U) (A := ta).
      simpl. apply Hta. apply H2. reflexivity.
Qed.


Lemma list_assignments_equiv_cat {X: Type} `{EqType X}: forall (L L': list (assignments X)) (c x: X) (h: node) (A: nodes) (U': assignments X),
  L = tl (get_assignment_sequence_from_A4 (h :: A) U' x)
  -> L' = tl (get_assignment_sequence_from_A4 (h :: A) ((h, c) :: U') x)
  -> list_assignments_equiv L L'.
Proof.
  intros L L' c x u A U HL HL'.
  simpl in HL'. simpl in HL. apply list_assignments_assignments_equiv with (x := x) (A := A) (U := (u, x) :: U) (U' := (u, x) :: (u, c) :: U).
  - unfold assignments_equiv. intros u'. simpl. destruct (u =? u') as [|]. reflexivity. reflexivity.
  - apply HL.
  - apply HL'.
Qed.

Lemma list_assignments_preserve_value {X: Type} `{EqType X}: forall (U Ux: assignments X) (A: nodes) (LUx: list (assignments X)) (x: X) (u: node),
  list_assignments_equiv (Ux :: LUx) (get_assignment_sequence_from_A4 A U x)
  -> ~In u A
  -> get_assigned_value (last (Ux :: LUx) Ux) u = get_assigned_value U u.
Proof.
  intros U Ux A LUx x u HL Hu.
  generalize dependent U. generalize dependent Ux. generalize dependent LUx. induction A as [| h t IH].
  - intros LUx Ux U HL. simpl in HL. exfalso. apply HL.
  - intros LUx Ux U HL. simpl in HL.
    assert (Hhu: h =? u = false).
    { destruct (h =? u) as [|] eqn:Hhu. apply eqb_eq in Hhu. exfalso. apply Hu. left. apply Hhu.
      reflexivity. }
    destruct LUx as [| hl tl].
    + simpl in HL.
      simpl. destruct HL as [HL]. unfold assignments_equiv in HL. rewrite HL. simpl.
      simpl in Hu. rewrite Hhu. reflexivity.
    + specialize IH with (LUx := tl) (Ux := hl) (U := (h, x) :: U). destruct HL as [HL HL']. apply IH in HL'.
      * rewrite last_suffix with (b := hl). simpl in HL'. rewrite Hhu in HL'. apply HL'.
      * intros F. apply Hu. right. apply F.
Qed.

Lemma assignments_seq_nodes_map_to_x {X: Type} `{EqType X}: forall (U Ux: assignments X) (A: nodes) (LUx: list (assignments X)) (x: X),
  list_assignments_equiv (Ux :: LUx) (get_assignment_sequence_from_A4 A U x)
  -> forall (u: node), In u A
     -> get_assigned_value (last (Ux :: LUx) Ux) u = Some x.
Proof.
  intros U Ux A LUx x HL u Hu.
  generalize dependent Ux. generalize dependent U. generalize dependent A. induction LUx as [| hl tl IH].
  - intros A Hu U Ux HL. destruct (A) as [| h t].
    + exfalso. apply Hu.
    + destruct t as [| h' t'].
      * destruct Hu as [Hu | Hu]. simpl in HL. rewrite <- Hu. simpl. destruct HL as [HL]. unfold assignments_equiv in HL.
        specialize HL with (u := h). simpl in HL. rewrite eqb_refl in HL. apply HL. exfalso. apply Hu.
      * simpl in HL. exfalso. apply HL.
  - intros A Hu U Ux HL. destruct A as [| h t].
    exfalso. apply Hu. simpl in HL. destruct t as [| h' t']. simpl in HL. exfalso. apply HL.
    simpl in HL. rewrite last_suffix with (b := hl).
    destruct Hu as [Hu | Hu].
    + destruct (member h (h' :: t')) as [|] eqn:Hmem.
      * apply IH with (U := (h, x) :: U) (A := h' :: t'). apply member_In_equiv. rewrite <- Hu. apply Hmem.
        apply HL.
      * rewrite list_assignments_preserve_value with (U := (h, x) :: U) (A := h' :: t') (x := x).
        -- simpl. apply eqb_eq in Hu. rewrite Hu. reflexivity.
        -- apply HL.
        -- apply member_In_equiv_F. rewrite <- Hu. apply Hmem.
    + apply IH with (U := (h, x) :: U) (A := h' :: t'). apply Hu.
      apply HL.
Qed.