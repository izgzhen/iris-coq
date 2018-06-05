From iris.base_logic Require Export derived.
From iris.bi Require Export bi.
From iris.algebra Require Import proofmode_classes.
Set Default Proof Using "Type".

(* The trick of having multiple [uPred] modules, which are all exported in
another [uPred] module is by Jason Gross and described in:
https://sympa.inria.fr/sympa/arc/coq-club/2016-12/msg00069.html *)
Module Import uPred.
  Export base_logic.bi.uPred.
  Export derived.uPred.
  Export bi.bi.
End uPred.

(* Setup of the proof mode *)
Section class_instances.
Context {M : ucmraT}.
Implicit Types P Q R : uPred M.

Global Instance into_pure_cmra_valid `{CmraDiscrete A} (a : A) :
  @IntoPure (uPredI M) (✓ a) (✓ a).
Proof. by rewrite /IntoPure discrete_valid. Qed.

Global Instance from_pure_cmra_valid {A : cmraT} af (a : A) :
  @FromPure (uPredI M) af (✓ a) (✓ a).
Proof.
  rewrite /FromPure. eapply bi.pure_elim; [by apply affinely_if_elim|]=> ?.
  rewrite -cmra_valid_intro //.
Qed.

Global Instance from_sep_ownM (a b1 b2 : M) :
  IsOp a b1 b2 →
  FromSep (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof. intros. by rewrite /FromSep -ownM_op -is_op. Qed.
Global Instance from_sep_ownM_core_id (a b1 b2 : M) :
  IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
  FromAnd (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof.
  intros ? H. rewrite /FromAnd (is_op a) ownM_op.
  destruct H; by rewrite persistent_and_sep.
Qed.

Global Instance into_and_ownM p (a b1 b2 : M) :
  IsOp a b1 b2 → IntoAnd p (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof.
  intros. apply intuitionistically_if_mono. by rewrite (is_op a) ownM_op sep_and.
Qed.

Global Instance into_sep_ownM (a b1 b2 : M) :
  IsOp a b1 b2 → IntoSep (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof. intros. by rewrite /IntoSep (is_op a) ownM_op. Qed.
End class_instances.
