(* This file defines all axioms we are relying on in our development. *)

Axiom ProofIrrelevance: forall (P: Prop) (p q: P), p = q.
Ltac pi p q := erewrite (ProofIrrelevance _ p q).
