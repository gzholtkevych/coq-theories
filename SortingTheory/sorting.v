Require Import Karazin.SortingTheory.comparable.

Section SortingProblem.
  Variables (X : Set) (cmp : X -> X -> cmpout).
  Context `{HC : Comparable X cmp}.

  Inductive array : Set :=
  | array0 : array
  | arrayn : array -> X -> array.

End SortingProblem.

