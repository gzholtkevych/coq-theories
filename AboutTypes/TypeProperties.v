Require Import List.
Require Import Arith.Compare_dec.
Require Import Arith.Le.
Require Import Arith.Lt.
Open Scope list_scope.

Section Definitions.
  Variable T : Type.

  Definition Inhabited : Prop := exists e : list T, e <> nil.
  Definition Finite : Prop := exists e : list T, forall t : T, In t e.
End Definitions.

Section Examples_for_Inhabited.
  Example bool_is_Inhabited : Inhabited bool.
  Proof. now exists (true :: nil). Qed.

  Example False_isnot_Inhabited : ~ Inhabited False.
  Proof.
    intro. elim H. intros e H1. apply H1.
    destruct e as [| t e']; [ trivial | now exfalso ].
  Qed.
End Examples_for_Inhabited.

Theorem not_Inhabited_is_Finite : forall T : Type, ~ Inhabited T -> Finite T.
Proof.
  intros* H.
  exists nil. intro. exfalso. apply H.
  exists (t :: nil). intro H'. discriminate H'.
Qed.

Section Examples_for_Finite.

  Example False_is_Finite : Finite False.
  Proof.
    apply not_Inhabited_is_Finite.
    exact False_isnot_Inhabited.
  Qed.

  Example bool_is_Finite : Finite bool.
  Proof.
    exists (true :: false :: nil). intro.
    destruct t; [ now left | right; now left ].
  Qed.

  Section NatIsNotFinite.
  (*  Here we prove that nat is not a finite type/
      The idea of the proof is to construct a function
      outside : list nat -> nat meeting the requirement
      forall e : list nat, ~ In (outside e) e.                                *)

    Fixpoint outside (ns : list nat) : nat :=
      match ns with
        nil     => 0
      | n :: ns' => let n' := outside ns' in
                    if le_lt_dec n' n then S n else n'
      end.

    Compute outside nil.
    Compute outside (7 :: 3 :: 5 :: 2 :: nil).

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
            case (le_lt_dec (outside e') m); intro HD.
            * assert (HAux : n < m). now apply le_trans with (outside e').
              now apply le_S.
            * assumption.
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
End Examples_for_Finite.
