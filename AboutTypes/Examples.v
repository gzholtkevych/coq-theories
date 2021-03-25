Require Import Karazin.AboutTypes.TypeProperties.
Require Import Arith.Compare_dec.
Require Import List.
Require Import Arith.Le.
Require Import Arith.Lt.


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
(*
Section Cardinality.
  Variable T : Type.
  Hypothesis eq_dec : forall x y : T, {x = y} + {x <> y}.

  Definition In_dec : forall (x : T) (e : list T), {In x e} + {~ In x e}.
  Proof.
    intros.
    induction e as [| y e' IHe].
    - right. now simpl.
    - elim IHe; intro HIn.
      + left. now right.
      + case (eq_dec x y); intro HE.
        * left. rewrite HE. now left.
        * right. intro H. simpl in H. elim H. intro HE'.
          now symmetry in HE'. trivial.
  Defined.

  Fixpoint refine (lst : list T) : list T :=
    match lst with
      nil => lst
    | x :: nil  => lst
    | x :: lst' => match In_dec x lst' with
                     left _  => refine lst'
                   | right _ => x :: (refine lst')
                   end
    end.





End Cardinality.

Definition eq_dec_nat : forall n m : nat, {n = m} + {n <> m}.
Proof.
  induction n as [| n' IHn].
  - intro. destruct m; [now left | right; intro H; discriminate H].
  - intro. induction m as [| m' IHm].
    + right. intro H. discriminate H.
    + elim IHm.
      * intro H. right. rewrite H. intro H'.
        now pose (H'' := n_Sn m').
      * intro H.

Compute refine nat dec_eq_nat (1 :: 1 :: 2 :: 2 :: 3 :: nil).
*)