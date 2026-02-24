Require Import Stdlib.Lists.List.
Require Import Stdlib.Structures.Equalities.
Import ListNotations.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import Classical.


(* this file proves logic-related lemmas, often relating boolean functions
   with their propositional equivalents, or allowing simplification of
   boolean expressions *)

Lemma negb_both_sides: forall b c: bool, negb b = c -> b = negb c.
Proof.
  intros b c H.
  destruct b as [|]. destruct c as [|].
  - simpl in H. discriminate H.
  - simpl. reflexivity.
  - destruct c as [|]. simpl. reflexivity. simpl in H. discriminate H.
Qed.


Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c.
  intros H.
  destruct b eqn:Eb.
  - reflexivity.
  - rewrite <- H. destruct c eqn: Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem orb_true_elim2 : forall b c : bool,
  orb b c = false -> b = false.
Proof.
  intros b c.
  intros H.
  destruct b eqn:Eb.
  - simpl in H. discriminate H.
  - reflexivity.
Qed.

Lemma split_and_true : forall a b, a && b = true <-> a = true /\ b = true.
Proof.
  intros a b. split.
  { intros H.
    split.
    - apply andb_true_elim2 in H. apply H.
    - rewrite andb_comm in H. apply andb_true_elim2 in H. apply H. }
  { intros H. destruct H as [H1 H2]. rewrite H1. rewrite H2. reflexivity. }
Qed.

Lemma split_orb_false : forall a b, a || b = false <-> a = false /\ b = false.
Proof.
  intros a b. split.
  { intros H.
  split.
  - apply orb_true_elim2 in H. apply H.
  - rewrite orb_comm in H. apply orb_true_elim2 in H. apply H. }
  { intros [Ha Hb]. rewrite Ha. rewrite Hb. simpl. reflexivity. }
Qed.

Lemma split_orb_true : forall a b, a || b = true <-> a = true \/ b = true.
Proof.
  intros a b. split.
  { intros H. destruct a as [|] eqn:A.
    - left. reflexivity.
    - simpl in H. right. apply H. }
  { intros [H | H].
    - rewrite H. simpl. reflexivity.
    - rewrite H. rewrite orb_comm. simpl. reflexivity. }
Qed.


(* several proofs of variations of demorgan's law *)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x' :: l' => P x' /\ (All P l')
  end.

Theorem demorgan : forall (P Q : Prop),
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  tauto.
Qed.

Theorem demorgan_and: forall (P Q : Prop),
  ~(P /\ Q) -> ~P \/ ~Q.
Proof.
  intros P Q H.
  unfold not in H.
  apply NNPP.
  intro contra.
  apply H.
  split.
  - apply NNPP.
    intros NP.
    apply contra.
    left. apply NP.
  - apply NNPP.
    intros NQ.
    apply contra.
    right. apply NQ.
Qed.

Theorem demorgan_many: forall (T: Type) (P: T -> Prop) (l : list T), ~(All P l) -> exists x: T, (In x l) /\ ~(P x).
Proof.
  intros T P l.
  intros H.
  induction l as [| h t IH].
  - unfold not in H. simpl in H. exfalso. apply H. apply I.
  - simpl in H. apply demorgan_and in H.
    destruct H as [H1 | H2].
    + exists h. simpl. split.
      * left. reflexivity.
      * apply H1.
    + apply IH in H2. destruct H2 as [x [HIn HP]].
      exists x. split.
      * simpl. right. apply HIn.
      * apply HP.
Qed.

Theorem demorgan_bool : forall (A B : bool), A || B = false <-> A = false /\ B = false.
Proof.
  intros A B. split.
  { intros H.
  destruct A as [|] eqn:HA.
  - simpl in H. discriminate H.
  - split. reflexivity. simpl in H. apply H. }
  { intros [H1 H2]. rewrite H1. simpl. apply H2. }
Qed.

Theorem demorgan_and_bool: forall (A B: bool), A && B = false
  <-> A = false \/ B = false.
Proof.
  intros A B. split.
  { intros H.
  destruct A as [|] eqn:HA.
  - simpl in H. right. apply H.
  - left. reflexivity. }
  { intros [H | H].
  - rewrite H. simpl. reflexivity.
  - rewrite andb_comm. rewrite H. reflexivity. }
Qed.

Theorem demorgan_many_bool: forall (T: Type) (P: T -> bool) (l : list T), forallb P l = false
  <-> exists x: T, In x l /\ (P x = false).
Proof.
  intros T P l. split.
  { intros H.
  induction l as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. apply demorgan_and_bool in H. destruct H as [H | H].
    + exists h. simpl. split.
      * left. reflexivity.
      * apply H.
    + apply IH in H. destruct H as [x [HIn HP]].
      exists x. split.
      * simpl. right. apply HIn.
      * apply HP. }
  { intros [x [HIn HP]].
  induction l as [| h t IH].
  - simpl in HIn. exfalso. apply HIn.
  - simpl. simpl in HIn.
    destruct HIn as [Hhx | HIn].
    + rewrite Hhx. rewrite HP. simpl. reflexivity.
    + apply IH in HIn. rewrite HIn. rewrite andb_comm. simpl. reflexivity. }
Qed.

Theorem demorgan_many_bool_2: forall (T: Type) (P: T -> bool) (l : list T), (existsb P l = false)
  <-> (forall x: T, In x l -> (P x = false)).
Proof.
  intros T P l. split.
  { intros Hex x HIn.
  induction l as [| h t IH].
  - simpl in HIn. exfalso. apply HIn.
  - simpl in Hex. simpl in HIn. apply split_orb_false in Hex. destruct Hex as [H1 H2].
    destruct HIn as [Hhx | HIn].
    + rewrite <- Hhx. apply H1.
    + apply IH in H2. apply H2. apply HIn. }
  { intros H. induction l as [| h t IH].
    - simpl. reflexivity.
    - simpl in H. simpl. apply split_orb_false. split.
      + specialize (H h). apply H. left. reflexivity.
      + apply IH. intros x Hx. apply H. right. apply Hx. }
Qed.


(* properties of forallb, existsb, filter *)
Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test.
  intros l.
  split.
  - intros H. induction l as [| h t IH].
    + simpl. apply I.
    + simpl. simpl in H.
      destruct (test h) as [|] eqn:Hh.
      * split. reflexivity. apply IH. apply H.
      * discriminate H.
  - intros H. induction l as [| h t IH].
    + simpl. reflexivity.
    + simpl. simpl in H.
      destruct H as [H1 H2].
      destruct (test h) as [|] eqn:Hh.
      * apply IH. apply H2.
      * apply H1.
Qed.

Theorem forallb_true_iff_mem : forall X test (l : list X),
  forallb test l = true <-> (forall x: X, In x l -> test x = true).
Proof.
  intros X test.
  intros l.
  split.
  - intros H. intros x Hmem. induction l as [| h t IH].
    + simpl in Hmem. exfalso. apply Hmem.
    + simpl in H. simpl in Hmem. destruct Hmem as [Hhx | Hmem].
      * apply split_and_true in H. destruct H as [H _]. rewrite Hhx in H. apply H.
      * apply IH.
        -- apply split_and_true in H. destruct H as [_ H]. apply H.
        -- apply Hmem.
  - intros H. induction l as [| h t IH].
    + simpl. reflexivity.
    + simpl. assert (Hh: test h = true).
      { specialize H with (x := h). apply H. simpl. left. reflexivity. }
      rewrite Hh. simpl. apply IH. intros x Hind.
      apply H. simpl. right. apply Hind.
Qed.

Theorem forallb_true : forall (X : Type) (test : X -> bool) (x : X) (l: list X),
  In x l -> (forallb test l = true -> test x = true).
Proof.
  intros X test.
  intros x l. intros Hmem.
  induction l as [| h t IHt].
  - simpl in Hmem. exfalso. apply Hmem.
  - simpl. intros H.
    destruct (test h) as [|] eqn:Htesth.
    + simpl in H. simpl in Hmem. destruct Hmem as [H1 | H1].
      * rewrite <- H1. apply Htesth.
      * apply IHt. apply H1. apply H.
    + simpl in H. discriminate H.
Qed.

Theorem existsb_false :
  forall (T: Type) (P: T -> bool) (ls : list T), existsb P ls = false -> (forall x : T, In x ls -> P x = false).
Proof.
  intros T P ls H.
  destruct (demorgan_many_bool_2 T P ls) as [Hf Hb]. apply Hf. apply H.
Qed.


Theorem filter_true : forall (X : Type) (test : X -> bool) (x : X) (l: list X),
  In x (filter test l) <-> In x l /\ test x = true.
Proof.
  intros X test.
  intros x l.
  split.
  { induction l as [| h t IHt].
  - simpl. intros F. exfalso. apply F.
  - simpl. intros H.
    destruct (test h) as [|] eqn:Htesth.
    + simpl in H. destruct H as [H | H].
      * rewrite <- H. split.
        -- left. reflexivity.
        -- apply Htesth.
      * apply IHt in H. destruct H as [H1 H2]. split.
        -- right. apply H1.
        -- apply H2.
    + apply IHt in H. destruct H as [H1 H2]. split.
      * right. apply H1.
      * apply H2. }
  { intros [H1 H2]. induction l as [| h t IHt].
  - simpl in H1. exfalso. apply H1.
  - simpl. destruct (test h) as [|] eqn:Htesth.
    + simpl in H1. destruct H1 as [H1 | H1].
      * simpl. left. apply H1.
      * simpl. right. apply IHt. apply H1.
    + simpl in H1. destruct H1 as [H1 | H1].
      * rewrite H1 in Htesth. rewrite H2 in Htesth. discriminate Htesth.
      * apply IHt. apply H1. }
Qed.
