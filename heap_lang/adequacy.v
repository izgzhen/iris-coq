From iris.program_logic Require Export weakestpre adequacy.
From iris.heap_lang Require Export heap.
From iris.algebra Require Import auth.
From iris.program_logic Require Import wsat auth.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.

Class heapPreG Σ := HeapPreG {
  heap_preG_iris :> irisPreG heap_lang Σ;
  heap_preG_heap :> authG Σ heapUR
}.

Definition heapΣ : gFunctors :=
  #[irisΣ state; authΣ heapUR].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. intros [? ?]%subG_inv. split; apply _. Qed.

Definition heap_adequacy Σ `{heapPreG Σ} e σ φ :
  (∀ `{heapG Σ}, heap_ctx ⊢ WP e {{ v, ■ φ v }}) →
  adequate e σ φ.
Proof.
  intros Hwp; eapply (wp_adequacy Σ); iIntros (?) "Hσ".
  iMod (auth_alloc to_heap _ heapN _ σ with "[Hσ]") as (γ) "[Hh _]";[|by iNext|].
  { exact: to_heap_valid. }
  set (Hheap := HeapG _ _ _ γ).
  iApply (Hwp _). by rewrite /heap_ctx.
Qed.
