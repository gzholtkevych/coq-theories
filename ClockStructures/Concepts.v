Require Import ClockStructures.Preliminaries.


Record Event (C : Set) := Event_def
{ src : C
; num : nat
}.


Class ClockStructureConstraint
  (C : Set)
  (prec : relation (Event C))
  (sync : relation (Event C)) : Prop :=
{ clock_fin : Finitary C
; prec_sord : Asymmetric prec /\ Transitive prec
; sync_equiv : Reflexive sync /\ Symmetric sync /\ Transitive sync
; prec_sync_constr : forall x x' y y' : Event C,
    prec x y -> sync x x' -> sync y y' -> prec x' y'
; prec_for_line : forall x y : Event C,
    src C x = src C y ->
      (num C x < num C y <-> prec x y)
; prec_fin : forall x : Event C, exists N : nat,
    forall y : Event C, prec y x -> num C y <= N
}.

Structure ClockStructure := ClockStructure_def
{ clock : Set
; prec : relation (Event clock)
; sync : relation (Event clock)
; ClockStructureConstraint_cert :
    ClockStructureConstraint clock prec sync
}.


Class ClockMorphismConstrain
Structure ClockMorphism := cm_def {
  dom : ClockStructure;
  cod : ClockStructure;
  map : event dom -> event cod;
  clock_inv : forall x y : event dom,
    src (clock dom) x = src (clock dom) y ->
      src (clock cod) (map x) = src (clock cod) (map y)
}.