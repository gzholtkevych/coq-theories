Require Export Lists.List.
Import ListNotations.


Section Definitions.
Variable T : Type.

  Class Inhabited
  : Prop :=
    exist_proof : exists e : list T, e <> nil.
  Class Finite
  : Prop :=
    fin_proof : exists e : list T, forall t : T, In t e.

End Definitions.


Section BasicDependence.
Variable T : Type.

  Theorem not_Inhabited_is_Finite : ~ Inhabited T -> Finite T.
  Proof.
    intros* H.
    exists nil. intro. exfalso. apply H.
    exists (t :: nil). intro H'. discriminate H'.
  Qed.

End BasicDependence.

(* Inhabitence of some standard types                                       *)

Instance bool_is_Inhabited : Inhabited bool.
Proof. now exists (true :: nil). Defined.

Instance nat_is_Inhabited : Inhabited nat.
Proof. now exists (0 :: nil). Defined.

(* Some types are not inhabited *)

Example False_isnot_Inhabited : ~ Inhabited False.
Proof.
  intro. elim H. intros e H1. apply H1.
  destruct e as [| t e']; [ trivial | now exfalso ].
Qed.

(* Finiteness of some standard types                                        *)

Instance False_is_Finite : Finite False.
Proof.
  apply not_Inhabited_is_Finite.
  exact False_isnot_Inhabited.
Defined.

Instance unit_is_Finite : Finite unit.
Proof.
  exists (tt :: nil). intro.
  destruct t. now left.
Defined.

Instance bool_is_Finite : Finite bool.
Proof.
  exists (true :: false :: nil). intro.
  destruct t; [ now left | right; now left ].
Defined.

(* Infiniteness of type nat                                                 *)

Require Import Arith.Compare_dec.
Require Import Arith.Le.
Require Import Arith.Lt.
Section NatIsNotFinite.
(*  Here we prove that nat is not a finite type/
    The idea of the proof is to construct a function
    outside : list nat -> nat meeting the requirement
      forall e : list nat, ~ In (outside e) e.                              *)


  Fixpoint outside (ns : list nat) : nat :=
    match ns with
      nil     => 0
    | n :: ns' => let n' := outside ns' in
                  if le_lt_dec n' n then S n else n'
    end.

  Section Lemmas.
    Variable e : list nat.

    Lemma lt_member_outside : forall n : nat, In n e -> n < outside e.
    Proof.
      intros * H.
      induction e as [| m e' IHe]; simpl.
      - now exfalso.
      - case H; intro HC.
        + rewrite HC. case (le_lt_dec (outside e') n); intro HD;
          [apply le_n | assumption].
        + pose (IHe' := IHe HC).
          case (le_lt_dec (outside e') m); intro HD; assumption || idtac.
            assert (HAux : n < m). {
              now apply le_trans with (outside e'). }
            now apply le_S.
    Qed.

    Lemma outside_list : ~ In (outside e) e.
    Proof.
      intro H.
      pose (H1 := lt_member_outside (outside e) H).
      now pose (H2 := lt_irrefl (outside e)).
    Qed.
  End Lemmas.

  Theorem nat_isnot_Finite : ~ Finite nat.
  Proof.
    unfold Finite. intro. elim H. intros e H1.
    pose (H2 := H1 (outside e)).
    now pose (H2' := outside_list e).
  Qed.

End NatIsNotFinite.
