From iris.program_logic Require Export weakestpre adequacy.
From iris.heap_lang Require Export heap.
From iris.program_logic Require Import auth ownership.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics weakestpre.

Definition heapΣ : gFunctors := #[authΣ heapUR; irisΣ heap_lang].

Definition heap_adequacy Σ `{irisPreG heap_lang Σ, authG Σ heapUR} e σ φ :
  (∀ `{heapG Σ}, heap_ctx ⊢ WP e {{ v, ■ φ v }}) →
  adequate e σ φ.
Proof.
  intros Hwp; eapply (wp_adequacy Σ); iIntros (?) "Hσ".
  iVs (auth_alloc (ownP ∘ of_heap) heapN _ (to_heap σ) with "[Hσ]") as (γ) "[??]".
  - auto using to_heap_valid.
  - rewrite /= (from_to_heap σ); auto.
  - iApply (Hwp (HeapG _ _ _ γ)). by rewrite /heap_ctx.
Qed.