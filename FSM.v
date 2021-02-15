Require Import Karazin.TypeProperties.
Require Import List.
Open Scope list_scope.

Record FST : Type := mkFST {
  input : Set;
  output : Set;
  state : Set;
  do : state -> input -> state * output;
  fin : Finite input /\ Finite output /\ Finite state
}.

Fixpoint run (m : FST) (sini : state m)
             (w : list (input m))
         : (state m) * list (output m) :=
  match w with
    nil => (sini, nil)
  | a :: w' => let (s, b) := do m sini a in
               let (s', u') := run m s w' in
               (s', b :: u')
  end.

Section FST_Example.
  Inductive A : Set := green : A | red : A.
  Inductive B : Set := even : B | odd : B.
  Inductive S : Set := init : S | another : S.
  Let f (s : S) (a : A) : S * B :=
    match s with
      init => match a with
                red => (init, even)
              | green => (another, odd)
              end
    | another => match a with
                   red => (another, odd)
                 | green => (init, even)
                 end
    end.
  Lemma finABS : Finite A /\ Finite B /\ Finite S.
  Proof.
    repeat split; [
      exists (green :: red :: nil)
    | exists (even :: odd :: nil)
    | exists (init :: another :: nil)]; intro;
    destruct t; (now left) || (right; now left).
  Qed.

  Let m : FST := {|
    input := A; output := B; state := S; do := f;
    fin := finABS
  |}.
End FST_Example.














































































































