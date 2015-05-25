(* This file defines all axioms we are relying on in our development. *)
Require Import Coq.Logic.ProofIrrelevance.
Require Import Util CSetoid.

Definition ProofIrrelevance := proof_irrelevance.
Ltac rewrite_pi p q := erewrite (ProofIrrelevance _ p q).
Ltac pi := try apply equivR; f_equal; now eapply ProofIrrelevance.
