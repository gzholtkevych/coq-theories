Require Import Karazin.AboutTypes.TypeProperties.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.


Record event (C : Set) : Set := defEvent {cn : C; tc : nat}.

Record CS := defCS {
  clock : Set;
  tick := event clock;
  happen_before : relation tick;
  synchronisation : relation tick;
  fin_constr : Finite clock;
  so_constr : StrictOrder happen_before;
  eq_constr : Equivalence synchronisation;
  con_constr : forall i i' j j' : tick,
    synchronisation i i' -> synchronisation j j' ->
      happen_before i j -> happen_before i' j';
  lt_constr : forall (c : clock) (n m : nat),
    n < m -> happen_before {| cn := c; tc := n |} {| cn := c; tc := m |};
  past_constr : forall i : tick,
    exists e : list tick, forall j : tick, happen_before j i -> In j e
}.
