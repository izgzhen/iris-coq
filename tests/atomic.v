From iris.heap_lang Require Export lifting notation.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

(* Test if AWP and the AU obtained from AWP print. *)
Section printing.
  Context `{!heapG Σ}.

  Definition code : expr := #().

  Lemma print_both_quant (P : val → iProp Σ) :
    <<< ∀ x, P x >>> code @ ⊤ <<< ∃ y, P y, RET #() >>>.
  Proof.
    Show. iIntros (Q Φ) "? AU". Show.
    iPoseProof (aupd_aacc with "AU") as "?". Show.
  Abort.

  Lemma print_first_quant l :
    <<< ∀ x, l ↦ x >>> code @ ⊤ <<< l ↦ x, RET #() >>>.
  Proof.
    Show. iIntros (Q Φ) "? AU". Show.
    iPoseProof (aupd_aacc with "AU") as "?". Show.
  Abort.

  Lemma print_second_quant l :
    <<< l ↦ #() >>> code @ ⊤ <<< ∃ y, l ↦ y, RET #() >>>.
  Proof.
    Show. iIntros (Q Φ) "? AU". Show.
    iPoseProof (aupd_aacc with "AU") as "?". Show.
  Abort.

  Lemma print_no_quant l :
    <<< l ↦ #() >>> code @ ⊤ <<< l ↦ #(), RET #() >>>.
  Proof.
    Show. iIntros (Q Φ) "? AU". Show.
    iPoseProof (aupd_aacc with "AU") as "?". Show.
  Abort.

  Check "Now come the long pre/post tests".

  Lemma print_both_quant_long l :
    <<< ∀ x, l ↦ x ∗ l ↦ x >>> code @ ⊤ <<< ∃ y, l ↦ y, RET #() >>>.
  Proof.
    Show. iIntros (Q Φ) "? AU". Show.
  Abort.

  Lemma print_both_quant_longpre l :
    <<< ∀ x, l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x >>> code @ ⊤ <<< ∃ y, l ↦ y, RET #() >>>.
  Proof.
    Show. iIntros (Q Φ) "? AU". Show.
  Abort.

  Lemma print_both_quant_longpost l :
    <<< ∀ xx, l ↦ xx ∗ l ↦ xx ∗ l ↦ xx >>> code @ ⊤ <<< ∃ yyyy, l ↦ yyyy ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx, RET #() >>>.
  Proof.
    Show. iIntros (Q Φ) "? ?". Show.
  Abort.

  Lemma print_first_quant_long l :
    <<< ∀ x, l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x >>> code @ ⊤ <<< l ↦ x, RET #() >>>.
  Proof.
    Show. iIntros (Q Φ) "? AU". Show.
  Abort.

  Lemma print_second_quant_long l x :
    <<< l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x >>> code @ ⊤ <<< ∃ y, l ↦ y, RET #() >>>.
  Proof.
    Show. iIntros (Q Φ) "? AU". Show.
  Abort.

  Lemma print_no_quant_long l x :
    <<< l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x >>> code @ ⊤ <<< l ↦ #(), RET #() >>>.
  Proof.
    Show. iIntros (Q Φ) "? AU". Show.
  Abort.

  Lemma print_no_quant_longpre l xx yyyy :
    <<< l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx >>> code @ ⊤ <<< l ↦ yyyy, RET #() >>>.
  Proof.
    Show. iIntros (Q Φ) "? AU". Show.
  Abort.

  Lemma print_no_quant_longpost l xx yyyy :
    <<< l ↦ xx ∗ l ↦ xx ∗ l ↦ xx >>> code @ ⊤ <<< l ↦ yyyy ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx, RET #() >>>.
  Proof.
    Show. iIntros (Q Φ) "? AU". Show.
  Abort.

End printing.
