From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From Utils Require Import EqType.

Definition nodefun (X: Type) : Type := X * (list X) -> X. (* takes in unobserved term and values for each parent *)
Definition graphfun {X: Type} : Type := node -> nodefun X. (* takes in node and returns function for that node *)

Definition generic_graph_and_type_properties_hold (X: Type) (G: graph): Prop :=
  (exists (x y: X), x <> y) /\ G_well_formed G = true /\ contains_cycle G = false.