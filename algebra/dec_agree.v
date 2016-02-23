From algebra Require Export cmra.
From algebra Require Import functor upred.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments unit _ _ !_ /.

(* This is isomorphic to optiob, but has a very different RA structure. *)
Inductive dec_agree (A : Type) : Type := 
  | DecAgree : A → dec_agree A
  | DecAgreeBot : dec_agree A.
Arguments DecAgree {_} _.
Arguments DecAgreeBot {_}.

Section dec_agree.
Context {A : Type} `{∀ x y : A, Decision (x = y)}.

Instance dec_agree_valid : Valid (dec_agree A) := λ x,
  if x is DecAgree _ then True else False.
Instance dec_agree_equiv : Equiv (dec_agree A) := equivL.
Canonical Structure dec_agreeC : cofeT := leibnizC (dec_agree A).

Instance dec_agree_op : Op (dec_agree A) := λ x y,
  match x, y with
  | DecAgree a, DecAgree b => if decide (a = b) then DecAgree a else DecAgreeBot
  | _, _ => DecAgreeBot
  end.
Instance dec_agree_unit : Unit (dec_agree A) := id.
Instance dec_agree_minus : Minus (dec_agree A) := λ x y, x.

Definition dec_agree_ra : RA (dec_agree A).
Proof.
  split.
  - apply _.
  - apply _.
  - apply _.
  - apply _.
  - intros [?|] [?|] [?|]; simpl; repeat (case_match; simpl); subst; congruence.
  - intros [?|] [?|]; simpl; repeat (case_match; simpl); try subst; congruence.
  - intros [?|]; simpl; repeat (case_match; simpl); try subst; congruence.
  - intros [?|]; simpl; repeat (case_match; simpl); try subst; congruence.
  - intros [?|] [?|] ?; simpl; done.
  - intros [?|] [?|] ?; simpl; done.
  - intros [?|] [?|] [[?|]]; simpl; repeat (case_match; simpl); subst;
      try congruence; [].
    case=>EQ. destruct EQ. done.
Qed.

Canonical Structure dec_agreeRA : cmraT := discreteRA dec_agree_ra.

End dec_agree.