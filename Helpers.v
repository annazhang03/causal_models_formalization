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

Fixpoint eqblist (l1 l2 : list nat) : bool
  := match l1, l2 with
      | nil, nil => true
      | nil, _ => false
      | _, nil => false
      | h1 :: t1, h2 :: t2 => if (h1 =? h2) then eqblist t1 t2 else false
end.

Theorem eqblist_refl : forall l: list nat,
  true = eqblist l l.
Proof.
  induction l as [| h t IHl].
  - simpl. reflexivity.
  - simpl. rewrite eqb_refl. rewrite IHl. reflexivity.
Qed.

Fixpoint member (v : nat) (s : list nat) : bool
  := match s with
      | nil => false
      | h :: t => if (h =? v) then true else member v t
    end.

Fixpoint overlap (s1 : list nat) (s2 : list nat) : bool
  := match s1 with 
      | nil => false
      | h :: t => if (member h s2) then true else overlap t s2
    end.

Example no_overlap : overlap [1;2;3] [4] = false.
Proof. reflexivity. Qed.

Example one_overlap : overlap [1;2;3] [2] = true.
Proof. reflexivity. Qed.

Fixpoint count (v : nat) (l : list nat) : nat
  := match l with 
      | nil => 0
      | h :: t => if (h =? v) then S (count v t) else count v t
     end.

Lemma not_member_count_0 : 
  forall (l : list nat) (x : nat), member x l = false -> count x l = 0.
Proof.
  intros l x H.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. simpl in H. destruct (h =? x) as [|] eqn:Hhx.
    * discriminate H.
    * apply IH in H. apply H.
Qed.

Lemma member_In_equiv : 
  forall (l : list nat) (x: nat), member x l = true <-> In x l.
Proof.
  intros l x.
  split.
  - intros H. induction l as [| h t IH].
    + simpl in H. discriminate H.
    + simpl in H. simpl. destruct (h =? x) as [|] eqn:Hhx.
      * left. apply eqb_eq. apply Hhx.
      * right. apply IH. apply H.
  - intros H. induction l as [| h t IH].
    + simpl in H. exfalso. apply H.
    + simpl. simpl in H. destruct H as [H | H].
      * apply eqb_eq in H. rewrite H. reflexivity.
      * destruct (h =? x) as [|] eqn:Hhx.
        -- reflexivity.
        -- apply IH. apply H.
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

Lemma split_and_true : forall a b, a && b = true -> a = true /\ b = true.
Proof.
  intros a b H.
  split.
  - apply andb_true_elim2 in H. apply H.
  - rewrite andb_comm in H. apply andb_true_elim2 in H. apply H.
Qed. 

(* output true if l1 is subset of l2 *)
Definition subset (l1 l2 : list nat) : bool :=
  forallb (fun x => member x l2) l1.

Example test_subset_true: subset [1; 2; 3] [3; 4; 2; 5; 1] = true.
Proof. reflexivity. Qed.

Example test_subset_false: subset [1; 2; 3] [3; 4; 2; 5] = false.
Proof. reflexivity. Qed.

(* set subtraction: elements in l1 that are not in l2 *)
Definition set_subtract (l1 l2 : list nat) : list nat :=
  filter (fun x => negb (member x l2)) l1.

Example test_set_subtract: set_subtract [3; 4; 2; 5; 1] [4; 3] = [2; 5; 1].
Proof. reflexivity. Qed.

Example test_set_subtract_not_in_set: set_subtract [3; 4] [1; 2; 3] = [4].
Proof. reflexivity. Qed.

Example test_set_subtract_duplicates: set_subtract [3; 4] [4; 4] = [3].
Proof. reflexivity. Qed.

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



