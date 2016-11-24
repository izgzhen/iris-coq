From iris.program_logic Require Export weakestpre adequacy.
From iris.heap_lang Require Export heap.
From iris.algebra Require Import auth.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.

Class heapPreG Σ := HeapPreG {
  heap_preG_iris :> invPreG Σ;
  heap_preG_heap :> inG Σ (authR heapUR)
}.

Definition heapΣ : gFunctors := #[invΣ; GFunctor (constRF (authR heapUR))].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. intros [? ?%subG_inG]%subG_inv. split; apply _. Qed.

Definition heap_adequacy Σ `{heapPreG Σ} e σ φ :
  (∀ `{heapG Σ}, True ⊢ WP e {{ v, ⌜φ v⌝ }}) →
  adequate e σ φ.
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (?) "".
  iMod (own_alloc (● to_heap σ)) as (γ) "Hh".
  { apply: auth_auth_valid. exact: to_heap_valid. }
  iModIntro. iExists (λ σ, own γ (● to_heap σ)); iFrame.
  set (Hheap := HeapG _ _ _ γ). iApply (Hwp _).
Qed.
