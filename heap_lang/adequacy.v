From iris.program_logic Require Export weakestpre adequacy.
From iris.heap_lang Require Export heap.
From iris.algebra Require Import auth.
From iris.program_logic Require Import ownership.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.

Class heapPreG Σ := HeapPreG {
  heap_preG_iris :> irisPreG heap_lang Σ;
  heap_preG_heap :> inG Σ (authR heapUR)
}.

Definition heapΣ : gFunctors :=
  #[irisΣ heap_lang; GFunctor (constRF (authR heapUR))].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. intros [? ?%subG_inG]%subG_inv. split; apply _. Qed.

Definition heap_adequacy Σ `{heapPreG Σ} e σ φ :
  (∀ `{heapG Σ}, heap_ctx ⊢ WP e {{ v, ■ φ v }}) →
  adequate e σ φ.
Proof.
  intros Hwp; eapply (wp_adequacy Σ); iIntros (?) "Hσ".
  iVs (own_alloc (● to_heap σ)) as (γ) "Hh".
  { apply (auth_auth_valid (to_heap _)), to_heap_valid. }
  set (Hheap := HeapG _ _ _ γ).
  iVs (inv_alloc heapN _ heap_inv with "[-]"); [iNext; iExists σ; by iFrame|].
  iApply (Hwp _). by rewrite /heap_ctx.
Qed.