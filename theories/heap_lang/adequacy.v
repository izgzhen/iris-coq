From iris.program_logic Require Export weakestpre adequacy.
From iris.heap_lang Require Export lifting.
From iris.algebra Require Import auth.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Class heapPreG Σ := HeapPreG {
  heap_preG_iris :> invPreG Σ;
  heap_preG_heap :> gen_heapPreG loc val Σ
}.

Definition heapΣ : gFunctors := #[invΣ; gen_heapΣ loc val].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. solve_inG. Qed.

Definition heap_adequacy Σ `{heapPreG Σ} s e σ φ :
  (∀ `{heapG Σ}, WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}%I) →
  adequate s e σ φ.
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (?) "".
  iMod (gen_heap_init σ) as (?) "Hh".
  iModIntro. iExists gen_heap_ctx. iFrame "Hh".
  iApply (Hwp (HeapG _ _ _)).
Qed.
