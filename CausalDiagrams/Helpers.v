From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From DAGs Require Import Descendants.
From DAGs Require Import PathFinding.
From Utils Require Import Lists.
From Utils Require Import Logic.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.

Import ListNotations.


(* very specific theorem that makes a common structure convenient to prove *)
Lemma path_breaks_down_midpoint_vs_endpoint: forall (l1 l2 l3: nodes) (a b: node),
  l1 ++ [a] ++ l2 = l3 ++ [b]
  -> (rev l2 = [] -> a = b /\ l1 = l3) /\ (forall (hl2: node) (tl2: nodes), rev l2 = hl2 :: tl2 -> b = hl2 /\ l3 = l1 ++ [a] ++ rev tl2).
Proof.
  intros l1' l2' l3 a b H. split.
  { intros Hlp2.
    assert (Hlem: rev (l1' ++ [a]) = rev (l3 ++ [b])).
    { rewrite <- H. rewrite reverse_list_append. rewrite reverse_list_append. rewrite reverse_list_append. unfold nodes in *. unfold node in *. rewrite Hlp2.
      simpl. reflexivity. }
    rewrite reverse_list_append in Hlem. rewrite reverse_list_append in Hlem. simpl in Hlem.
    inversion Hlem. split. reflexivity. rewrite reverse_list_twice with (l := l1'). rewrite H2. rewrite <- reverse_list_twice.
    reflexivity. }
  { intros hlp2' tlp2' Hlp2'. assert (Hlem: rev (l1' ++ [a] ++ l2') = rev (l3 ++ [b])).
    { rewrite <- H. reflexivity. }
    rewrite reverse_list_append in Hlem. rewrite reverse_list_append in Hlem. unfold nodes in *. unfold node in *. rewrite Hlp2' in Hlem. simpl in Hlem. rewrite reverse_list_append in Hlem.
    simpl in Hlem. inversion Hlem. split. reflexivity. rewrite reverse_list_twice with (l := l3).
    rewrite <- H2. repeat rewrite reverse_list_append. rewrite <- reverse_list_twice. simpl. reflexivity. }
Qed.