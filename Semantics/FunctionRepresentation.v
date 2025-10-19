From DAGs Require Import Basics.
From Utils Require Import EqType.

Definition nodefun (X: Type) : Type := X * (list X) -> X. (* takes in unobserved term and values for each parent *)
Definition graphfun {X: Type} : Type := node -> nodefun X. (* takes in node and returns function for that node *)
