From iris.program_logic Require Export weakestpre adequacy.
From iris.algebra Require Import auth.
From iris.heap_lang Require Import proofmode notation proph_map.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Class heap_prophPreG Σ := HeapProphPreG {
  heap_proph_preG_iris :> invPreG Σ;
  heap_proph_preG_heap :> gen_heapPreG loc val Σ;
  heap_proph_preG_proph :> proph_mapPreG proph val Σ
}.

Definition heapΣ : gFunctors := #[invΣ; gen_heapΣ loc val; proph_mapΣ proph val].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heap_prophPreG Σ.
Proof. solve_inG. Qed.

Definition heap_adequacy Σ `{heap_prophPreG Σ} s e σ φ :
  (∀ `{heapG Σ}, WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}%I) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??) "".
  iMod (gen_heap_init σ.1) as (?) "Hh".
  iMod (proph_map_init κs σ.2) as (?) "Hp".
  iModIntro.
  iExists (fun σ κs => (gen_heap_ctx σ.1 ∗ proph_map_ctx κs σ.2)%I). iFrame.
  iApply (Hwp (HeapG _ _ _ _)).
Qed.
