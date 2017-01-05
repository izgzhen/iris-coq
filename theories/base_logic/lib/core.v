From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(** The "core" of an assertion is its maximal persistent part.
    It can be defined entirely within the logic... at least
    in the shallow embedding. *)

Definition coreP {M : ucmraT} (P : uPred M) : uPred M :=
  (∀ `(!PersistentP Q, P ⊢ Q), Q)%I.
Instance: Params (@coreP) 1.
Typeclasses Opaque coreP.

Section core.
  Context {M : ucmraT}.
  Implicit Types P Q : uPred M.

  Lemma coreP_intro P : P -∗ coreP P.
  Proof. iIntros "HP". by iIntros (Q HQ ->). Qed.

  Global Instance coreP_persistent P : PersistentP (coreP P).
  Proof. rewrite /coreP. apply _. Qed.

  Global Instance coreP_mono : Proper ((⊢) ==> (⊢)) (@coreP M).
  Proof.
    rewrite /coreP. iIntros (P P' ?) "H"; iIntros (Q ??).
    unshelve iApply ("H" $! Q). by etrans.
  Qed.

  Global Instance coreP_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@coreP M).
  Proof. intros P Q. rewrite !equiv_spec=>-[??]. by split; apply coreP_mono. Qed.

  Lemma coreP_elim P : PersistentP P → coreP P -∗ P.
  Proof. rewrite /coreP. iIntros (?) "HCP". unshelve iApply ("HCP" $! P); auto. Qed.
End core.

