From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export pviewshifts.
From iris.program_logic Require Export weakestpre.
Import uPred.

Section weakestpre.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P Q : iProp Λ Σ.
Implicit Types Φ : val Λ → iProp Λ Σ.

Global Instance frame_wp E e R Φ Ψ :
  (∀ v, Frame R (Φ v) (Ψ v)) → Frame R (WP e @ E {{ Φ }}) (WP e @ E {{ Ψ }}).
Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.
Global Instance is_fsa_wp E e Φ :
  IsFSA (WP e @ E {{ Φ }})%I E (wp_fsa e) (language.atomic e) Φ.
Proof. split. done. apply _. Qed.
End weakestpre.
