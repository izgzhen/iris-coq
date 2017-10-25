From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(** The "core" of an assertion is its maximal persistent part.
    It can be defined entirely within the logic... at least
    in the shallow embedding.
    WARNING: The function "coreP" is NOT NON-EXPANSIVE.
    This is because the turnstile is not non-expansive as a function
    from iProp to (discreteC Prop).
    To obtain a core that's non-expansive, we would have to add another
    modality to the logic: a box that removes access to *all* resources,
    not just restricts access to the core.
*)

Definition coreP {M : ucmraT} (P : uPred M) : uPred M :=
  (∀ `(!Persistent Q), ⌜P ⊢ Q⌝ → Q)%I.
Instance: Params (@coreP) 1.
Typeclasses Opaque coreP.

Section core.
  Context {M : ucmraT}.
  Implicit Types P Q : uPred M.

  Lemma coreP_intro P : P -∗ coreP P.
  Proof. rewrite /coreP. iIntros "HP". by iIntros (Q HQ ->). Qed.

  Global Instance coreP_persistent P : Persistent (coreP P).
  Proof. rewrite /coreP. apply _. Qed.

  Global Instance coreP_mono : Proper ((⊢) ==> (⊢)) (@coreP M).
  Proof.
    rewrite /coreP. iIntros (P P' ?) "H"; iIntros (Q ??).
    iApply ("H" $! Q with "[%]"). by etrans.
  Qed.

  Global Instance coreP_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@coreP M).
  Proof. intros P Q. rewrite !equiv_spec=>-[??]. by split; apply coreP_mono. Qed.

  Lemma coreP_elim P : Persistent P → coreP P -∗ P.
  Proof. rewrite /coreP. iIntros (?) "HCP". unshelve iApply ("HCP" $! P); auto. Qed.

  Lemma coreP_wand P Q :
    (coreP P ⊢ Q) ↔ (P ⊢ □ Q).
  Proof.
    split.
    - iIntros (HP) "HP". iDestruct (coreP_intro with "HP") as "#HcP".
      iAlways. by iApply HP.
    - iIntros (HPQ) "HcP". iDestruct (coreP_mono _ _ HPQ with "HcP") as "HcQ".
      iDestruct (coreP_elim with "HcQ") as "#HQ". done.
  Qed.
End core.
