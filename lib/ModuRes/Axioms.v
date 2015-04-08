(* This file defines all axioms we are relying on in our development. *)
Require Import Coq.Logic.ProofIrrelevance.

Definition ProofIrrelevance := proof_irrelevance.
Ltac pi p q := erewrite (ProofIrrelevance _ p q).
