From iris.base_logic Require Export derived.
From iris.bi Require Export bi.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import proofmode_classes.
Set Default Proof Using "Type".

(* The trick of having multiple [uPred] modules, which are all exported in
another [uPred] module is by Jason Gross and described in:
https://sympa.inria.fr/sympa/arc/coq-club/2016-12/msg00069.html *)
Module Import uPred.
  Export upred.uPred.
  Export derived.uPred.
  Export bi.
End uPred.

(* Hint DB for the logic *)
Hint Resolve pure_intro : I.
Hint Resolve or_elim or_intro_l' or_intro_r' : I.
Hint Resolve and_intro and_elim_l' and_elim_r' : I.
Hint Resolve persistently_mono : I.
Hint Resolve sep_mono : I. (* sep_elim_l' sep_elim_r'  *)
Hint Immediate True_intro False_elim : I.
Hint Immediate iff_refl internal_eq_refl : I.

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
  rewrite -cmra_valid_intro //. by apply pure_intro.
Qed.

(* FromOp *)
(* TODO: Worst case there could be a lot of backtracking on these instances,
try to refactor. *)
Global Instance is_op_pair {A B : cmraT} (a b1 b2 : A) (a' b1' b2' : B) :
  IsOp a b1 b2 → IsOp a' b1' b2' → IsOp' (a,a') (b1,b1') (b2,b2').
Proof. by constructor. Qed.
Global Instance is_op_pair_core_id_l {A B : cmraT} (a : A) (a' b1' b2' : B) :
  CoreId  a → IsOp a' b1' b2' → IsOp' (a,a') (a,b1') (a,b2').
Proof. constructor=> //=. by rewrite -core_id_dup. Qed.
Global Instance is_op_pair_core_id_r {A B : cmraT} (a b1 b2 : A) (a' : B) :
  CoreId a' → IsOp a b1 b2 → IsOp' (a,a') (b1,a') (b2,a').
Proof. constructor=> //=. by rewrite -core_id_dup. Qed.

Global Instance is_op_Some {A : cmraT} (a : A) b1 b2 :
  IsOp a b1 b2 → IsOp' (Some a) (Some b1) (Some b2).
Proof. by constructor. Qed.
(* This one has a higher precendence than [is_op_op] so we get a [+] instead of
an [⋅]. *)
Global Instance is_op_plus (n1 n2 : nat) : IsOp (n1 + n2) n1 n2.
Proof. done. Qed.

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
  intros. apply affinely_persistently_if_mono. by rewrite (is_op a) ownM_op sep_and.
Qed.

Global Instance into_sep_ownM (a b1 b2 : M) :
  IsOp a b1 b2 → IntoSep (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof. intros. by rewrite /IntoSep (is_op a) ownM_op. Qed.
End class_instances.
