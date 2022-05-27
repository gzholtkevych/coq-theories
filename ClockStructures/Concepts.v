Require Import Karazin.TypeProperties.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Import ListNotations.
Open Scope type_scope.


Record ClockSet : Type := mkClockSet
{ clock : Set
; clock_fin_cert : Finite clock
}.


Definition one_clock_set : ClockSet := {| clock := unit |}.


Record Event (cs : ClockSet) := mkEvent
{ clk : clock cs
; idx : nat
}.


Class Synchronisable (cs : ClockSet) (sync : relation  (Event cs)) : Prop := 
{ synrefl : forall i : Event cs, sync i i
; synsymm : forall i j : Event cs, sync i j -> sync j i
; syntrns : forall i j k : Event cs, sync i j -> sync j k -> sync i k
}.


Class Causal (cs : ClockSet) (causes : relation  (Event cs)) : Prop :=
{ cauirrf : forall i : Event cs, ~ causes i i
; cautrns : forall i j k : Event cs, causes i j -> causes j k -> causes i k
}.


Class ClockStructure_Axioms
  (ClockSet : Set)
  (lhb : relation (clock * nat))
  (sync : relation (clock * nat)) : Prop :=
  { 
  ; clock_fin_cert : Finite clock
  ; prec_irrefl : forall i : clock * nat, ~ prec i i
  ; prec_trans : forall i j k : clock * nat, prec i j -> prec j k -> prec i k
  ; prec_line : forall (c : clock) (n m : nat), prec (c, n) (c, m) <-> n < m
  ; sync_refl : forall i : clock * nat, sync i i
  ; sync_symm : forall i j : clock * nat, sync i j -> sync j i
  ; sync_trans : forall i j k : clock * nat, sync i j -> sync j k -> sync i k
  ; prec_sync : forall i i' j j' : clock * nat,
                   prec i j -> sync i i' -> sync j j' -> prec i' j'
}.

Structure ClockStructure := mkClockStructure
{ clock : Set
; prec : relation (clock * nat)
; sync : relation (clock * nat)
; clockStructure_Axioms : ClockStructure_Axioms clock prec sync}.

Instance timer_axiom_cert : ClockStructure_Axioms
  unit
  (fun i j : unit * nat => snd i < snd j)
  (fun i j : unit * nat => snd i = snd j).
Proof.
  constructor.
  - exact unit_is_Finite.
  - intros * H. 

Definition timer : ClockStructure := {|
  clock := unit;
  prec (i j : unit * nat) := snd i < snd j;
  sync (i j : unit * nat) := snd i = snd j
|}.