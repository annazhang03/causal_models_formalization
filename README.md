
# Causality and Semantic Separation

This repository presents a semantics-driven formalization of causal models within the Rocq Prover. The formalization includes a library of graph-theoretic and causal-reasoning tools, encompassing key concepts such as mediators, confounders, and colliders. It introduces a novel semantic definition of _semantic separation_ and proves that it exactly coincides with _d_-separation, the classic condition on graphs in causal inference that determines when the design of an experiment controls for an appropriate set of variables.

## Structure

- `Utils`: supporting definitions and lemmas for lists, logic, and types, not yet involving graphs
- `DAGs`: representation of directed acyclic graphs within Rocq and many definitions and proofs relating to all aspects of DAGs, such as pathfinding and topological sort
- `CausalDiagrams`: DAGs but specific to causal models, such as _d_-separation, intermediate node classifications, interventions
- `Semantics`: the function-based semantic definition of causal models, as well as all the proof details to the equivalence proof between semantic separation and _d_-separation

## Building

To compile:

```bash
coq_makefile -f _CoqProject -o Makefile
make
```
Tested with **Rocq 8.20**.

## Correspondence Between Paper Sections and Mechanized Theorems
TODO
