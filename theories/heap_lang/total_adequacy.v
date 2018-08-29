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
  iMod (gen_heap_init σ.1) as (?) "Hh".
  iMod (proph_map_init [] σ.2) as (?) "Hp".
  iModIntro.
  iExists (fun σ κs => (gen_heap_ctx σ.1 ∗ proph_map_ctx κs σ.2)%I). iFrame.
  iApply (Hwp (HeapG _ _ _ _)).
Qed.
