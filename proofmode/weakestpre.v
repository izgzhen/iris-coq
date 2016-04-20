From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export pviewshifts.
From iris.program_logic Require Export weakestpre.
Import uPred.

Section weakestpre.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P Q : iProp Λ Σ.
Implicit Types Φ : val Λ → iProp Λ Σ.

Instance frame_wp E e R Φ mΨ :
  (∀ v, Frame R (Φ v) (mΨ v)) →
  Frame R (WP e @ E {{ Φ }})
          (Some (WP e @ E {{ v, if mΨ v is Some Q then Q else True }}))%I.
Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.
Global Instance fsa_split_wp E e Φ :
  FSASplit (WP e @ E {{ Φ }})%I E (wp_fsa e) (language.atomic e) Φ.
Proof. split. done. apply _. Qed.
End weakestpre.

Hint Extern 10 (Frame _ (WP _ @ _ {{ _ }}) _) =>
  class_apply frame_wp : typeclass_instances.