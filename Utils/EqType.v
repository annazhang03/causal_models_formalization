Require Import Coq.Lists.List.
Require Import Coq.Structures.Equalities.
Import ListNotations.

(* generalize some of the above properties to any types containing a decidable equality function
   that satisfies reflexivity and symmetry *)
Class EqType (X : Type) := {
  eqb : X -> X -> bool;
  eqb_refl' : forall x, eqb x x = true;
  eqb_sym' : forall x y, eqb x y = eqb y x;
  eqb_eq' : forall x y, eqb x y = true <-> x = y
}.

Fixpoint eqblist_X {X: Type} `{EqType X} (l1 l2 : list X) : bool
  := match l1, l2 with
      | nil, nil => true
      | nil, _ => false
      | _, nil => false
      | h1 :: t1, h2 :: t2 => if (eqb h1 h2) then eqblist_X t1 t2 else false
end.