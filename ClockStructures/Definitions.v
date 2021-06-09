Require Import Karazin.AboutTypes.TypeProperties.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.


Record event (C : Set) : Set := defEvent {cn : C; tc : nat}.

Eval compute in tc unit (defEvent unit tt 5).

Class Eventable (C : Set) (before synch : relation (event C)) := {
  fin_constraint : Finite C;
  before_constraint : StrictOrder before;
  synch_constraint : Equivalence synch;
  before_synch_constraint : forall i i' j j' : event C,
    synch i i' -> synch j j' -> before i j -> before i' j';
  less_constraint : forall (c : C) (n m : nat), n < m ->
    before {| cn := c; tc := n |} {| cn := c; tc := m |};
  past_constraint : forall i : event C, exists e : list (event C),
    forall j : event C, before j i -> In j e
}.

Record CS (C : Set) := defCS {
  clock := C;
  before : relation (event clock);
  synch : relation (event clock);
  constraints : Eventable clock before synch
}.

Definition one_clocked : CS unit := {|
  before := fun i j => tc unit i < tc unit j;
  synch := fun i j => tc unit i = tc unit j;
  constraints := Eventable unit before synch |}.

