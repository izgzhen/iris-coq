From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
Import uPred.

(** The "core" of an assertion is its maximal persistent part.
    It can be defined entirely within the logic... at least
    in the shallow embedding. *)

Definition coreP {M : ucmraT} (P : uPred M) : uPred M :=
  (∀ `(!PersistentP Q, P ⊢ Q), Q)%I.

Section core.
  Context {M : ucmraT}.
  Implicit Types P Q : uPred M.

  Lemma coreP_intro P : P -∗ coreP P.
  Proof. iIntros "HP". iIntros (Q HQ HPQ). by iApply HPQ. Qed.

  Global Instance coreP_persistent P : PersistentP (coreP P).
  Proof.
    iIntros "HCP". iApply always_forall. iIntros (Q).
    iApply always_forall. iIntros (HQ). iApply always_forall.
    iIntros (HPQ). iApply HQ. unshelve iApply ("HCP" $! Q). done.
  Qed.

  Global Instance coreP_mono : Proper ((⊢) ==> (⊢)) (@coreP M).
  Proof.
    unfold coreP. iIntros (?? ENT) "H *". unshelve iApply ("H" $! Q). by etrans.
  Qed.

  Global Instance coreP_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@coreP M).
  Proof. intros ??. rewrite !equiv_spec=>-[A B]. split; rewrite ?A // ?B //. Qed.

  Lemma coreP_elim P : PersistentP P → coreP P -∗ P.
  Proof.
    iIntros (?) "HCP". unshelve iApply ("HCP" $! P). iIntros "P". done.
  Qed.
End core.

Global Opaque coreP.
