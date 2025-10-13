Require Import Coq.Lists.List.
Require Import Coq.Structures.Equalities.
Import ListNotations.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
Require Import Classical.
From Utils Require Import List_Basics.
From Utils Require Import Logic.

Fixpoint prefix (l1 l2: list nat): bool :=
  match l1 with
  | [] => true
  | h1 :: t1 => match l2 with
                | [] => false
                | h2 :: t2 => (h1 =? h2) && prefix t1 t2
                end
  end.

Fixpoint sublist (l1 l2: list nat) : bool :=
  match l2 with
  | [] => eqblist l1 []
  | h1 :: t1 => prefix l1 l2 || sublist l1 t1
  end.


Example sublist_1: sublist [2;3] [1;2;3;4] = true.
Proof. reflexivity. Qed.

Example sublist_2: sublist [2;3] [1;2;4;3;2;3;2] = true.
Proof. reflexivity. Qed.

Example sublist_3: sublist [2;3] [1;2;4;3] = false.
Proof. reflexivity. Qed.

Lemma sublist_empty: forall l: list nat, sublist [] l = true.
Proof.
  destruct l as [| h t].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Class EqType (X : Type) := {
  eqb : X -> X -> bool;
  eqb_refl' : forall x, eqb x x = true;
  eqb_sym' : forall x y, eqb x y = eqb y x;
  eqb_eq' : forall x y, eqb x y = true <-> x = y
}.

Fixpoint eqblistX {X: Type} `{EqType X} (l1 l2 : list X) : bool
  := match l1, l2 with
      | nil, nil => true
      | nil, _ => false
      | _, nil => false
      | h1 :: t1, h2 :: t2 => if (eqb h1 h2) then eqblistX t1 t2 else false
end.


Fixpoint prefixX {X: Type} `{EqType X} (l1 l2: list X): bool :=
  match l1 with
  | [] => true
  | h1 :: t1 => match l2 with
                | [] => false
                | h2 :: t2 => (eqb h1 h2) && prefixX t1 t2
                end
  end.

Fixpoint sublistX {X: Type} `{EqType X} (l1 l2: list X) : bool :=
  match l2 with
  | [] => eqblistX l1 []
  | h1 :: t1 => prefixX l1 l2 || sublistX l1 t1
  end.

Lemma prefix_member_X {X: Type} `{EqType X}: forall (l1 l2: list X) (x: X),
  In x l1 /\ prefixX l1 l2 = true -> In x l2.
Proof.
  intros l1.
  induction l1 as [| h1 t1 IH].
  - intros l2 x. intros [Hmem Hpre]. exfalso. apply Hmem.
  - intros l2 x. intros [Hmem Hpre]. destruct l2 as [| h2 t2].
    + simpl in Hpre. discriminate Hpre.
    + simpl in Hpre. simpl in Hmem. simpl.
      apply split_and_true in Hpre. destruct Hpre as [H12 Hpre].
      destruct Hmem as [Hhx | Hmem].
      * apply eqb_eq' in H12. rewrite H12 in Hhx. left. apply Hhx.
      * right. apply IH with (l2 := t2). split.
        -- apply Hmem.
        -- apply Hpre.
Qed.

Lemma prefix_member: forall (l1 l2: list nat) (x: nat),
  In x l1 /\ prefix l1 l2 = true -> In x l2.
Proof.
  intros l1.
  induction l1 as [| h1 t1 IH].
  - intros l2 x. intros [Hmem Hpre]. exfalso. apply Hmem.
  - intros l2 x. intros [Hmem Hpre]. destruct l2 as [| h2 t2].
    + simpl in Hpre. discriminate Hpre.
    + simpl in Hpre. simpl in Hmem. simpl.
      apply split_and_true in Hpre. destruct Hpre as [H12 Hpre].
      destruct Hmem as [Hhx | Hmem].
      * apply eqb_eq in H12. rewrite H12 in Hhx. left. apply Hhx.
      * right. apply IH with (l2 := t2). split.
        -- apply Hmem.
        -- apply Hpre.
Qed.


Theorem sublist_member: forall (l1 l2: list nat) (x: nat),
  In x l1 /\ sublist l1 l2 = true -> In x l2.
Proof.
  intros l1 l2 x.
  intros [Hmem Hsub].
  induction l2 as [| h2 t2 IH].
  - destruct l1 as [| h1 t1].
    + apply Hmem.
    + simpl in Hsub. discriminate Hsub.
  - simpl. simpl in Hsub.
    apply split_orb_true in Hsub. destruct Hsub as [Hpre | Hind].
    + destruct l1 as [| h1 t1].
      * exfalso. apply Hmem.
      * simpl in Hmem. simpl in Hpre. apply split_and_true in Hpre.
        destruct Hpre as [H12 Hpre].
        destruct Hmem as [Hhx | Hmem].
        -- left. rewrite <- Hhx. apply eqb_eq in H12. rewrite H12. reflexivity.
        -- right. apply prefix_member with (l1 := t1). split.
           apply Hmem. apply Hpre.
    + right. apply IH. apply Hind.
Qed.

Lemma prefix_identity: forall (l1 l2: list nat),
  prefix l1 (l1 ++ l2) = true.
Proof.
  intros l1 l2. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite eqb_refl. rewrite IH. reflexivity.
Qed.

Lemma prefix_implies_sublist: forall (l1 l2: list nat),
  prefix l1 l2 = true -> sublist l1 l2 = true.
Proof.
  intros l1 l2 H.
  destruct l1 as [| h t].
  - destruct l2 as [| h' t'].
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct l2 as [| h' t'].
    + simpl in H. discriminate H.
    + simpl in H. apply split_and_true in H. destruct H as [Hh Hpre].
      simpl. rewrite Hh. rewrite Hpre. reflexivity.
Qed.

Lemma prefix_breaks_down_list: forall (l1 l: list nat),
  prefix l1 l = true <-> exists (l2: list nat), l1 ++ l2 = l.
Proof.
  intros l1 l. split.
  { generalize dependent l1. induction l as [| h t IH].
  - intros l1 H. simpl in H. destruct l1 as [| h' t'].
    + simpl. exists []. reflexivity.
    + simpl in H. discriminate H.
  - intros l1 H. destruct l1 as [| h' t'].
    + exists (h :: t). simpl. reflexivity.
    + simpl in H. apply split_and_true in H. destruct H as [Hh Hpre].
      specialize IH with (l1 := t'). apply IH in Hpre. destruct Hpre as [l2 Hl2].
      exists l2. simpl. rewrite Hl2. apply eqb_eq in Hh. rewrite Hh. reflexivity. }
  { intros [l2 H]. rewrite <- H. apply prefix_identity. }
Qed.

Theorem sublist_breaks_down_list: forall (l1 l: list nat),
  sublist l1 l = true <-> exists (l2 l3: list nat), l2 ++ l1 ++ l3 = l.
Proof.
  intros l1 l. split.
  { intros H. induction l as [| h t IH].
  - simpl in H. destruct l1 as [| h' t'].
    + simpl. exists []. exists []. reflexivity.
    + simpl in H. discriminate H.
  - simpl in H. apply split_orb_true in H. destruct H as [Hpre | Hsub].
    + exists []. simpl. apply prefix_breaks_down_list. apply Hpre.
    + apply IH in Hsub. destruct Hsub as [l2 [l3 H]].
      exists (h :: l2). exists l3. simpl. rewrite H. reflexivity. }
  { intros [l2 [l3 H]]. generalize dependent l3. generalize dependent l1. generalize dependent l2. induction l as [| h t IH].
  - intros l2 l1 l3 H. destruct l1 as [| h1 t1].
    + reflexivity.
    + simpl in H. destruct l2 as [| h2 t2]. simpl in H. discriminate H. discriminate H.
  - intros l2 l1 l3 H. destruct l1 as [| h1 t1].
    + reflexivity.
    + destruct l2 as [| h2 t2].
      * simpl in H.
        assert (Hpre: prefix (h1 :: t1) (h :: t) = true). { apply prefix_breaks_down_list. exists l3. apply H. }
        simpl. simpl in Hpre. rewrite Hpre. reflexivity.
      * specialize IH with (l2 := t2) (l1 := (h1 :: t1)) (l3 := l3).
        assert (Hsub: sublist (h1 :: t1) t = true). { apply IH. simpl in H. inversion H. reflexivity. }
        simpl. rewrite Hsub. rewrite orb_comm. reflexivity. }
Qed.

Lemma not_first_node_has_sublist: forall (a h v: nat) (t: list nat),
  (a =? h) = false /\ In a (t ++ [v])
  -> exists b : nat, sublist [b; a] (h :: t ++ [v]) = true.
Proof.
  intros a h v t [H1 H2]. generalize dependent h. induction t as [| h' t' IH].
  - intros h H1. exists h. simpl. simpl in H2. destruct H2 as [H2 | F].
    + rewrite H2. repeat rewrite eqb_refl. reflexivity.
    + exfalso. apply F.
  - intros h H1. simpl. destruct (a =? h') as [|] eqn:Ha.
    + exists h. rewrite eqb_refl. simpl. reflexivity.
    + simpl. assert (Hind: exists b : nat, sublist [b; a] (h' :: t' ++ [v]) = true).
      { apply IH. simpl in H2. destruct H2 as [F | H2].
        - rewrite F in Ha. rewrite eqb_refl in Ha. discriminate Ha.
        - apply H2.
        - apply Ha. }
      destruct Hind as [b Hb]. exists b. simpl in Hb. rewrite Hb. rewrite orb_comm. reflexivity.
Qed.

Lemma sublist_length_less: forall (l1 l2 l3: list nat) (len': nat),
  length l3 < S len' /\ l1 ++ l2 = l3 /\ ~(l1 = []) -> length l2 < len'.
Proof.
  intros l1 l2 l3 len'. intros [Hlen [Hl Hl1]].
  generalize dependent l1. generalize dependent l3. generalize dependent len'. induction l2 as [| h t IH].
  - intros len' l3 Hlen l1 Hl Hl1. simpl. destruct l1 as [| h1 t1].
    + exfalso. apply Hl1. reflexivity.
    + rewrite <- Hl in Hlen. simpl in Hlen. lia.
  - intros len' l3 Hlen l1 Hl Hl1. simpl.
    destruct len' as [| len''].
    + destruct l1 as [| h1 t1].
      * exfalso. apply Hl1. reflexivity.
      * rewrite <- Hl in Hlen. simpl in Hlen. lia.
    + destruct l1 as [| h1 t1].
      * exfalso. apply Hl1. reflexivity.
      * assert (length t < len'').
        { apply IH with (l1 := t1 ++ [h]) (l3 := t1 ++ h :: t).
          - rewrite <- Hl in Hlen. simpl in Hlen. lia.
          - rewrite <- app_assoc. simpl. reflexivity.
          - destruct t1 as [| h1' t1']. simpl. intros F. discriminate F. intros F. discriminate F. }
        lia.
Qed.

Lemma middle_elt_of_sublist_not_last_elt: forall (l: list nat) (a b c: nat),
  sublist [a; b; c] (l ++ [b]) = true -> In b l.
Proof.
  intros l a b c H.
  induction l as [| h t IH].
  - simpl in H. rewrite orb_comm in H. simpl in H. rewrite andb_comm in H. simpl in H. discriminate H.
  - simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + destruct t as [| h' t'].
      * simpl in H. rewrite eqb_refl in H. simpl in H. rewrite andb_comm in H. discriminate H.
      * simpl in H. apply split_and_true in H. destruct H as [_ H]. apply split_and_true in H. destruct H as [H _].
        simpl. right. left. apply eqb_eq in H. rewrite H. reflexivity.
    + simpl. right. apply IH. apply H.
Qed.

Lemma first_elt_of_sublist_not_last_elt: forall (l: list nat) (a b c v: nat),
  sublist [a; b; c] (l ++ [v]) = true -> In a l.
Proof.
  intros l a b c v H.
  induction l as [| h t IH].
  - simpl in H. rewrite orb_comm in H. simpl in H. rewrite andb_comm in H. simpl in H. discriminate H.
  - simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + destruct t as [| h' t'].
      * simpl in H. rewrite andb_comm in H. rewrite <- andb_assoc in H. rewrite andb_comm in H. discriminate H.
      * simpl in H. apply split_and_true in H. destruct H as [H _]. left. apply eqb_eq in H. rewrite H. reflexivity.
    + simpl. right. apply IH. apply H.
Qed.

Lemma first_elt_of_sublist_not_last_elt_gen: forall (l t: list nat) (a b v: nat),
  sublist (a :: b :: t) (l ++ [v]) = true -> In a l.
Proof.
  intros l t a b v H.
  induction l as [| hl tl IH].
  - simpl in H. rewrite orb_comm in H. simpl in H. rewrite andb_comm in H. simpl in H. discriminate H.
  - simpl in H. apply split_orb_true in H. destruct H as [H | H].
    + destruct t as [| h' t'].
      * simpl in H. rewrite andb_comm in H. apply split_and_true in H. left. destruct H as [_ H]. apply eqb_eq in H. rewrite H. reflexivity.
      * simpl in H. apply split_and_true in H. destruct H as [H _]. left. apply eqb_eq in H. rewrite H. reflexivity.
    + simpl. right. apply IH. apply H.
Qed.

Lemma middle_elt_of_sublist_not_first_elt: forall (l: list nat) (a b c: nat),
  sublist [a; b; c] (b :: l) = true -> In b l.
Proof.
  intros l a b c H.
  simpl in H.
  destruct l as [| h t].
  - simpl in H. rewrite orb_comm in H. simpl in H. rewrite andb_comm in H. simpl in H. discriminate H.
  - apply split_orb_true in H. destruct H as [H | H].
    + apply split_and_true in H. destruct H as [_ H]. apply split_and_true in H. destruct H as [H _].
      simpl. left. apply eqb_eq in H. rewrite H. reflexivity.
    + apply sublist_member with (l1 := [a; b; c]). split.
      * simpl. right. left. reflexivity.
      * apply H.
Qed.

Lemma middle_elt_of_sublist_not_first_elt_gen: forall (A t: list nat) (a b h: nat),
  sublist (a :: A) (h :: t) = true /\ In b A -> In b t.
Proof.
  intros A t a b h [H1 H2].
  generalize dependent h. induction t as [| hl tl IH].
  - intros h H1. simpl in H1. rewrite orb_comm in H1. simpl in H1. apply split_and_true in H1. destruct H1 as [_ H1].
    destruct A as [| ha ta]. apply H2. simpl in H1. discriminate H1.
  - intros h H1. simpl in H1. destruct ((a =? h) && prefix A (hl :: tl)) as [|] eqn:Hpre.
    + apply split_and_true in Hpre. destruct Hpre as [_ Hpre]. apply prefix_breaks_down_list in Hpre.
      apply membership_splits_list in H2. destruct H2 as [A1 [A2 HA]]. rewrite <- HA in Hpre. destruct Hpre as [t2 Ht].
      rewrite <- Ht. apply membership_append. apply membership_append_r. apply membership_append. left. reflexivity.
    + simpl in H1. right. apply IH with (h := hl). apply H1.
Qed.

Lemma index_of_sublist: forall (a b: nat) (i: nat) (l: list nat),
  sublist [b; a] l = true
  -> count a l = 1
  -> count b l = 1
  -> Some (S i) = index l a
  -> Some i = index l b.
Proof.
  intros a b i l. intros H1 Hc Hcb H2.
  generalize dependent i. induction l as [| h t IH].
  - simpl in H1. discriminate H1.
  - intros i H2. simpl in H2. destruct (h =? a) as [|] eqn:Hha. inversion H2.
    simpl in H1. destruct t as [| h' t'].
    + simpl in H1. rewrite andb_comm in H1. simpl in H1. discriminate H1.
    + destruct (a =? h') as [|] eqn:Hah.
      * simpl in H2. rewrite eqb_sym in Hah. rewrite Hah in H2. inversion H2. destruct (h =? b) as [|] eqn:Hhb.
        -- simpl. rewrite Hhb. reflexivity.
        -- rewrite eqb_sym in Hhb. rewrite Hhb in H1. simpl in H1.
           assert (In a t').
           { apply middle_elt_of_sublist_not_first_elt_gen with (A := [a]) (a := b) (h := h'). split. apply H1. left. reflexivity. }
           simpl in Hc. rewrite Hha in Hc. rewrite Hah in Hc. apply member_count_at_least_1 in H. lia.
      * destruct i as [|i'] eqn:Hi.
        -- rewrite eqb_sym in Hah. simpl in H2. rewrite Hah in H2. destruct (index t' a) as [j|]. inversion H2. discriminate H2.
        -- specialize IH with (i := i').
           assert (b =? h = false).
           { destruct (b =? h) as [|] eqn:Hbh.
             - simpl in H1. assert (In b (h' :: t')). { apply sublist_member with (l1 := [b; a]). split.
               + left. reflexivity.
               + apply H1. }
               simpl in Hcb. rewrite eqb_sym in Hbh. rewrite Hbh in Hcb. apply member_count_at_least_1 in H. simpl in H. lia.
             - reflexivity. }
           assert (Hind: Some i' = index (h' :: t') b).
           { apply IH.
             - rewrite andb_comm in H1. simpl in H1. apply H1.
             - simpl in Hc. rewrite Hha in Hc. apply Hc.
             - destruct (index (h' :: t') a) as [j|].
               + simpl in Hcb. rewrite eqb_sym in H. rewrite H in Hcb. apply Hcb.
               + inversion H2.
             - destruct (index (h' :: t') a) as [j|].
               + inversion H2. reflexivity.
               + discriminate H2. }
           simpl. rewrite eqb_sym in H. rewrite H. simpl in Hind. rewrite <- Hind. reflexivity.
Qed.


Lemma merge_two_sublists: forall (l: list nat) (a b x: nat),
  sublist [a; x] l = true
  -> sublist [b; a] l = true
  -> count a l = 1
  -> sublist [b; a; x] l = true.
Proof.
  intros l a b x Hx Hb Hc.
  induction l as [| h t IH].
  - simpl in Hx. discriminate Hx.
  - simpl in Hx.
    destruct (a =? h) as [|] eqn:Hah.
    + assert (Hat: In a t).
      { apply middle_elt_of_sublist_not_first_elt_gen with (A := [a]) (a := b) (h := h). split.
        - apply Hb.
        - left. reflexivity. }
      simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. apply member_count_at_least_1 in Hat. lia.
    + simpl in Hx. simpl in Hb. destruct (b =? h) as [|] eqn:Hbh.
      * destruct t as [| h' t'].
        -- simpl in Hb. discriminate Hb.
        -- simpl in Hb. destruct (a =? h') as [|] eqn:Hah'.
           ++ simpl in Hx. rewrite Hah' in Hx. destruct t' as [| h'' t''].
              ** simpl in Hx. discriminate Hx.
              ** destruct (x =? h'') as [|] eqn:Hxh''.
                 --- simpl. rewrite Hbh. rewrite Hah'. rewrite Hxh''. reflexivity.
                 --- assert (Ha: In a (h'' :: t'')).
                     { apply sublist_member with (l1 := [a; x]). split. left. reflexivity. simpl in Hx. apply Hx. }
                     simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. rewrite eqb_sym in Hah'. rewrite Hah' in Hc.
                     apply member_count_at_least_1 in Ha. simpl in Ha. lia.
           ++ simpl. apply split_orb_true. right. apply IH.
              ** apply Hx.
              ** apply Hb.
              ** simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. apply Hc.
      * simpl in Hb. simpl. apply split_orb_true. right. apply IH.
        -- apply Hx.
        -- apply Hb.
        -- simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. apply Hc.
Qed.

Lemma two_sublists_the_same: forall (l: list nat) (a b b': nat),
  sublist [a; b] l = true
  -> sublist [a; b'] l = true
  -> count a l = 1
  -> b = b'.
Proof.
  intros l a b b' Hb Hb' Hc.
  induction l as [| h t IH].
  - simpl in Hb. discriminate Hb.
  - simpl in Hb.
    destruct (a =? h) as [|] eqn:Hah.
    + destruct t as [| h' t'].
      * simpl in Hb. discriminate Hb.
      * destruct (b =? h') as [|] eqn:Hbh'.
        -- simpl in Hb'. rewrite Hah in Hb'. destruct (b' =? h') as [|] eqn:Hbh''.
           ++ apply eqb_eq in Hbh'. rewrite Hbh'. apply eqb_eq in Hbh''. rewrite Hbh''. reflexivity.
           ++ simpl in Hb'. assert (Ha: In a (h' :: t')). { apply sublist_member with (l1 := [a; b']). split. left. reflexivity. apply Hb'. }
              simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. apply member_count_at_least_1 in Ha. simpl in Ha. lia.
        -- simpl in Hb. assert (Ha: In a (h' :: t')). { apply sublist_member with (l1 := [a; b]). split. left. reflexivity. apply Hb. }
           simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. apply member_count_at_least_1 in Ha. simpl in Ha. lia.
    + simpl in Hb. simpl in Hb'. rewrite Hah in Hb'. simpl in Hb'. apply IH.
      * apply Hb.
      * apply Hb'.
      * simpl in Hc. rewrite eqb_sym in Hah. rewrite Hah in Hc. apply Hc.
Qed.

Lemma two_sublists_the_same_gen: forall (l l1 l1' l2 l2': list nat) (a: nat),
  l = l1 ++ [a] ++ l2
  -> l = l1' ++ [a] ++ l2'
  -> count a l = 1
  -> l2 = l2'.
Proof.
  intros l l1 l1' l2 l2' a Hl Hl' Hc.
  generalize dependent l1. generalize dependent l1'. induction l as [| h t IH].
  - intros l1' Hl' l1 Hl. simpl in Hc. discriminate Hc.
  - intros l1' Hl' l1 Hl. simpl in Hc.
    destruct l1' as [| hl1' tl1'].
    + simpl in Hl'. destruct l1 as [| hl1 tl1].
      * simpl in Hl. inversion Hl'. inversion Hl. rewrite <- H3. apply H1.
      * inversion Hl. inversion Hl'. rewrite H2 in Hc. rewrite eqb_refl in Hc.
        assert (In a t). { rewrite H1. apply membership_append_r. left. reflexivity. } apply member_count_at_least_1 in H. lia.
    + destruct l1 as [| hl1 tl1].
      * inversion Hl'. inversion Hl. rewrite H2 in Hc. rewrite eqb_refl in Hc.
        assert (In a t). { rewrite H1. apply membership_append_r. left. reflexivity. } apply member_count_at_least_1 in H. lia.
      * apply IH with (l1' := tl1') (l1 := tl1).
        -- destruct (h =? a) as [|] eqn:Hha. 
           ++ assert (In a t). { inversion Hl. apply membership_append_r. left. reflexivity. } apply member_count_at_least_1 in H. lia.
           ++ apply Hc.
        -- inversion Hl'. reflexivity.
        -- inversion Hl. reflexivity.
Qed.

Lemma sublist_rev: forall (l1 l2: list nat),
  sublist l1 l2 = true -> sublist (rev l1) (rev l2) = true.
Proof.
  intros l1 l2 H.
  apply sublist_breaks_down_list in H. destruct H as [A [B H]].
  apply sublist_breaks_down_list. exists (rev B). exists (rev A).
  rewrite <- reverse_list_append. rewrite <- reverse_list_append. f_equal. rewrite <- app_assoc. apply H.
Qed.

Lemma two_sublists_the_same_2: forall (l: list nat) (a b b': nat),
  sublist [b; a] l = true
  -> sublist [b'; a] l = true
  -> count a l = 1
  -> b = b'.
Proof.
  intros l a b b' Hb Hb' Hc.
  apply sublist_rev in Hb. simpl in Hb. apply sublist_rev in Hb'. simpl in Hb'.
  rewrite count_reverse in Hc.
  apply two_sublists_the_same with (l := rev l) (a := a).
  - apply Hb.
  - apply Hb'.
  - apply Hc.
Qed.

Lemma end_of_sublist_still_sublist: forall (a1 a a2 h v: nat) (t: list nat),
  sublist [a1; a; a2] (h :: t ++ [v]) = true
  -> sublist [a; a2] (t ++ [v]) = true.
Proof.
  intros a1 a a2 h v t H.
  simpl in H. destruct (a1 =? h) as [|] eqn:Ha1h.
  - destruct (match t ++ [v] with
    | [] => false
    | h2 :: t2 => (a =? h2) && match t2 with
                               | [] => false
                               | h3 :: _ => (a2 =? h3) && true
                               end
    end) as [|] eqn:H1.
    + destruct t as [| h' t'].
      * simpl in H1. rewrite andb_comm in H1. discriminate H1.
      * simpl. simpl in H1. rewrite H1. reflexivity.
    + simpl in H. apply sublist_breaks_down_list in H. destruct H as [l1 [l2 H]].
      apply sublist_breaks_down_list. exists (l1 ++ [a1]). exists l2. rewrite <- H. simpl. rewrite append_vs_concat. reflexivity.
  - simpl in H. apply sublist_breaks_down_list in H. destruct H as [l1 [l2 H]].
      apply sublist_breaks_down_list. exists (l1 ++ [a1]). exists l2. rewrite <- H. simpl. rewrite append_vs_concat. reflexivity.
Qed.

Lemma end_of_sublist_still_sublist_2: forall (a1 a a2 h v: nat) (t: list nat),
  sublist [a1; a; a2] (h :: t ++ [v]) = true
  -> sublist [a; a2] (h :: t ++ [v]) = true.
Proof.
  intros a1 a a2 h v t H.
  simpl in H. destruct (a1 =? h) as [|] eqn:Ha1h.
  - destruct (match t ++ [v] with
    | [] => false
    | h2 :: t2 => (a =? h2) && match t2 with
                               | [] => false
                               | h3 :: _ => (a2 =? h3) && true
                               end
    end) as [|] eqn:H1.
    + simpl. destruct t as [| h' t'].
      * simpl in H1. rewrite andb_comm in H1. discriminate H1.
      * simpl. simpl in H1. rewrite H1. rewrite orb_comm. simpl. reflexivity.
    + simpl in H. apply sublist_breaks_down_list in H. destruct H as [l1 [l2 H]].
      apply sublist_breaks_down_list. exists (h :: l1 ++ [a1]). exists l2. rewrite <- H. simpl. rewrite append_vs_concat. reflexivity.
  - simpl in H. apply sublist_breaks_down_list in H. destruct H as [l1 [l2 H]].
      apply sublist_breaks_down_list. exists (h :: l1 ++ [a1]). exists l2. rewrite <- H. simpl. rewrite append_vs_concat. reflexivity.
Qed.

Lemma end_of_sublist_still_sublist_gen: forall (a h: nat) (t l: list nat),
  sublist (a :: l) (h :: t) = true
  -> sublist l t = true.
Proof.
  intros a h t l H.
  generalize dependent h. induction t as [| h' t' IH].
  - intros h H. simpl in H. destruct (a =? h) as [|] eqn:Hah.
    + simpl in H. destruct l as [| hl tl]. simpl. reflexivity. simpl in H. discriminate H.
    + simpl in H. discriminate H.
  - intros h H. simpl in H. destruct ((a =? h) && prefix l (h' :: t')) as [|] eqn:H'.
    + apply split_and_true in H'. simpl. destruct H' as [_ H']. rewrite H'. reflexivity.
    + simpl in H. apply IH in H. simpl. rewrite H. rewrite orb_comm. reflexivity.
Qed.

Lemma start_of_sublist_still_sublist: forall (a w b: nat) (l: list nat),
  sublist [a; w; b] l = true
  -> sublist [a; w] l = true.
Proof.
  intros a w b l H.
  apply sublist_breaks_down_list in H. destruct H as [l1 [l2 H]].
  apply sublist_breaks_down_list. exists l1. exists (b :: l2). rewrite <- H. simpl. reflexivity.
Qed.