From DAGs Require Import Basics.
From DAGs Require Import CycleDetection.
From Utils Require Import EqType.


(* In this file, we introduce a function-based formal semantics of causal models.
   We assume that X is the type of values assigned to the nodes, such as a natural
   number or a finite enumeration *)


(* Causal models tell us the relationship that may exist between nodes. We choose
   to capture those relationships using nodefuns, each of which assigns a value to
   a node based on an unobserved term (of type X) and the values of its parents
   (each of type X, provided in a list) *)
Definition nodefun (X: Type) : Type := X * (list X) -> X.


(* A causal model is represented with an overarching graphfun, which maps each node
   in the graph to its corresponding nodefun *)
Definition graphfun {X: Type} : Type := node -> nodefun X.


(* We will often use the simple below proposition as an assumption in our semantics-related
   proofs: a type X and a graph G satisfy the below if
   1. there exist at least two distinct elements of X
   2. G has no duplicate nodes or edges, and all nodes appearing in the edges of G
      also appear in the nodes of G
   3. G is acyclic *)
Definition generic_graph_and_type_properties_hold (X: Type) (G: graph): Prop :=
  (exists (x y: X), x <> y) /\ G_well_formed G = true /\ contains_cycle G = false.