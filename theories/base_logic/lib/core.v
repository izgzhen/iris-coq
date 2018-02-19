From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(** The "core" of an assertion is its maximal persistent part,
    i.e. the conjunction of all persistent assertions that are weaker
    than P (as in, implied by P). *)
Definition coreP {M : ucmraT} (P : uPred M) : uPred M :=
  (∀ Q, ■ (P → □ Q) → □ Q)%I.
Instance: Params (@coreP) 1.
Typeclasses Opaque coreP.

Section core.
  Context {M : ucmraT}.
  Implicit Types P Q : uPred M.

  Lemma coreP_intro P : P -∗ coreP P.
  Proof. rewrite /coreP. iIntros "HP" (Q) "HPQ". by iApply "HPQ". Qed.

  Global Instance coreP_persistent P : Persistent (coreP P).
  Proof. rewrite /coreP /Persistent. iIntros "#HC" (Q) "!#". iApply "HC". Qed.

  Global Instance coreP_ne : NonExpansive (@coreP M).
  Proof. solve_proper. Qed.
  Global Instance coreP_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@coreP M).
  Proof. solve_proper. Qed.

  Global Instance coreP_mono : Proper ((⊢) ==> (⊢)) (@coreP M).
  Proof. solve_proper. Qed.

  Lemma coreP_elim P : Persistent P → coreP P -∗ P.
  Proof.
    rewrite /coreP. iIntros (?) "HCP". iApply ("HCP" $! P with "[]"). auto.
  Qed.

  Lemma coreP_wand P Q : (coreP P ⊢ Q) ↔ (P ⊢ □ Q).
  Proof.
    split.
    - iIntros (HP) "HP". iDestruct (coreP_intro with "HP") as "#HcP".
      iAlways. by iApply HP.
    - iIntros (HPQ) "HcP". iDestruct (coreP_mono _ _ HPQ with "HcP") as "HcQ".
      by iDestruct (coreP_elim with "HcQ") as "#HQ".
  Qed.
End core.
