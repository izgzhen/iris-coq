From iris.program_logic Require Export total_adequacy.
From iris.heap_lang Require Export adequacy.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Definition heap_total Σ `{heapPreG Σ} s e σ φ :
  (∀ `{heapG Σ}, WP e @ s; ⊤ [{ v, ⌜φ v⌝ }]%I) →
  sn erased_step ([e], σ).
Proof.
  intros Hwp; eapply (twp_total _ _); iIntros (?) "".
  iMod (gen_heap_init σ) as (?) "Hh".
  iModIntro. iExists gen_heap_ctx; iFrame.
  iApply (Hwp (HeapG _ _ _)).
Qed.
