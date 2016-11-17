From iris.program_logic Require Export weakestpre adequacy gen_heap.
From iris.heap_lang Require Export rules.
From iris.algebra Require Import auth.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.

Class heapPreG Σ := HeapPreG {
  heap_preG_iris :> invPreG Σ;
  heap_preG_heap :> gen_heapPreG loc val Σ
}.

Definition heapΣ : gFunctors := #[invΣ; gen_heapΣ loc val].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. intros [? ?]%subG_inv; split; apply _. Qed.

Definition heap_adequacy Σ `{heapPreG Σ} e σ φ :
  (∀ `{heapG Σ}, True ⊢ WP e {{ v, ⌜φ v⌝ }}) →
  adequate e σ φ.
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (?) "".
  iMod (own_alloc (● to_gen_heap σ)) as (γ) "Hh".
  { apply: auth_auth_valid. exact: to_gen_heap_valid. }
  iModIntro. iExists (λ σ, own γ (● to_gen_heap σ)); iFrame.
  set (Hheap := GenHeapG loc val Σ _ _ _ γ).
  iApply (Hwp (HeapG _ _ _)).
Qed.
