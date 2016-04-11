From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export pviewshifts.
From iris.program_logic Require Export weakestpre.
Import uPred.

Section weakestpre.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P Q : iProp Λ Σ.
Implicit Types Φ : val Λ → iProp Λ Σ.

Global Instance fsa_split_wp E e Φ :
  FSASplit (WP e @ E {{ Φ }})%I E (wp_fsa e) (language.atomic e) Φ.
Proof. split. done. apply _. Qed.
End weakestpre.
