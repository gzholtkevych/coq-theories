Require Import Karazin.AboutTypes.TypeProperties.
Require Import Karazin.AboutTypes.Examples.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Open Scope type_scope.



Record Event (clock : Set) `{fin_proof : Finitary clock}
: Set := logEvent {
  cn : clock;
  tn : nat
}.


Inductive two_clocks
: Set :=
  first : two_clocks
| second : two_clocks.

Example two_clocks_is_Finite : Finite two_clocks.
Proof.
  exists (first :: second :: nil). intro. simpl.
  destruct t; [left | right; left]; reflexivity.
Qed.

Instance two_clocks_fin_proof : Finitary two_clocks.
Proof. unfold Finitary. exact two_clocks_is_Finite. Defined.
Definition two_event_lines := Event two_clocks.
Definition ee : two_event_lines := {| cn := first; tn := 8 |}.


Definition event_line := Event unit.
Definition e : event_line := {| cn := tt; tn := 5 |}.


Class ClockStruct
  {clock : Set}
  `{clock_fin : Finitary clock}
  (before : relation (Event clock))
  (synchro : relation (Event clock))
: Prop := {
  event := Event clock;
  before_ord : StrictOrder before;
  synchro_eq : Equivalence synchro;
  before_synchro_cons
  : forall x x' y y' : event,
      synchro x x' -> synchro y y' -> before x y -> before x' y';
  before_lt_cons
  : forall x y : event,
      cn clock x = cn clock y -> tn clock x < tn clock y -> before x y;
  past_fin
  : forall x : event, exists e : list event,
      forall y : event, before y x -> In y e
}.


