From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.

Definition assert : val :=
  λ: "v", if: "v" #() then #() else #0 #0. (* #0 #0 is unsafe *)
(* just below ;; *)
Notation "'assert:' e" := (assert (λ: <>, e))%E (at level 99) : expr_scope.
Global Opaque assert.

Lemma wp_assert `{heapG Σ} E (Φ : val → iProp Σ) e `{!Closed [] e} :
  WP e @ E {{ v, v = #true ∧ ▷ Φ #() }} ⊢ WP assert: e @ E {{ Φ }}.
Proof.
  iIntros "HΦ". rewrite /assert. wp_let. wp_seq.
  iApply wp_wand_r; iFrame "HΦ"; iIntros (v) "[% ?]"; subst.
  wp_if. done.
Qed.
