From iris.bi Require Export bi plainly.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import bi.

(** The "core" of an assertion is its maximal persistent part,
    i.e. the conjunction of all persistent assertions that are weaker
    than P (as in, implied by P). *)
Definition coreP `{!BiPlainly PROP} (P : PROP) : PROP :=
  (∀ Q : PROP, ■ (Q -∗ <pers> Q) → ■ (P -∗ Q) → Q)%I.
Instance: Params (@coreP) 1.
Typeclasses Opaque coreP.

Section core.
  Context `{!BiPlainly PROP}.
  Implicit Types P Q : PROP.

  Lemma coreP_intro P : P -∗ coreP P.
  Proof. rewrite /coreP. iIntros "HP" (Q) "_ #HPQ". by iApply "HPQ". Qed.

  Global Instance coreP_persistent P : Persistent (coreP P).
  Proof.
    rewrite /coreP /Persistent. iIntros "HC" (Q).
    iApply persistently_impl_plainly. iIntros "#HQ".
    iApply persistently_impl_plainly. iIntros "#HPQ".
    iApply "HQ". by iApply ("HC" with "[#] [#]").
  Qed.

  Global Instance coreP_ne : NonExpansive (coreP (PROP:=PROP)).
  Proof. solve_proper. Qed.
  Global Instance coreP_proper : Proper ((⊣⊢) ==> (⊣⊢)) (coreP (PROP:=PROP)).
  Proof. solve_proper. Qed.

  Global Instance coreP_mono : Proper ((⊢) ==> (⊢)) (coreP (PROP:=PROP)).
  Proof. solve_proper. Qed.

  Lemma coreP_elim P : Persistent P → coreP P -∗ P.
  Proof. rewrite /coreP. iIntros (?) "HCP". iApply ("HCP" with "[#] [#]"); auto. Qed.

  (* TODO: Can we generalize this to non-affine BIs? *)
  Lemma coreP_wand `{!BiAffine PROP} P Q : (coreP P ⊢ Q) ↔ (P ⊢ <pers> Q).
  Proof.
    split.
    - iIntros (HP) "HP". iDestruct (coreP_intro with "HP") as "#HcP".
      iAlways. by iApply HP.
    - iIntros (HPQ) "HcP". iDestruct (coreP_mono _ _ HPQ with "HcP") as "HcQ".
      by iDestruct (coreP_elim with "HcQ") as "#HQ".
  Qed.
End core.
