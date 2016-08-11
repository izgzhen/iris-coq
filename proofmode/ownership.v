From iris.proofmode Require Export classes.
From iris.base_logic Require Export ownership.

Section ghost.
Context `{inG Σ A}.
Implicit Types a b : A.

Global Instance into_sep_own p γ a b1 b2 :
  IntoOp a b1 b2 → IntoSep p (own γ a) (own γ b1) (own γ b2).
Proof. rewrite /IntoOp /IntoSep => ->. by rewrite own_op. Qed.
Global Instance from_sep_own γ a b :
  FromSep (own γ (a ⋅ b)) (own γ a) (own γ b) | 90.
Proof. by rewrite /FromSep own_op. Qed.
End ghost.
