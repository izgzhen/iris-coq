From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export ghost_ownership.

Section ghost.
Context `{inG Λ Σ A}.
Implicit Types a b : A.

Global Instance sep_destruct_own p γ a b :
  SepDestruct p (own γ (a ⋅ b)) (own γ a) (own γ b).
Proof. apply sep_destruct_spatial. by rewrite own_op. Qed.
Global Instance sep_split_own γ a b :
  SepSplit (own γ (a ⋅ b)) (own γ a) (own γ b) | 90.
Proof. by rewrite /SepSplit own_op. Qed.
End ghost.
