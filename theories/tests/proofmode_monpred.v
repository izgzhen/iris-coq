From iris.proofmode Require Import tactics monpred.
From iris.base_logic Require Import base_logic lib.invariants.

Section tests.
  Context {I : biIndex} {PROP : sbi}.
  Local Notation monPred := (monPred I PROP).
  Local Notation monPredI := (monPredI I PROP).
  Local Notation monPredSI := (monPredSI I PROP).
  Implicit Types P Q R : monPred.
  Implicit Types i j : I.

  Lemma test0 P : P -∗ P.
  Proof. iIntros "$". Qed.

  Lemma test_iStartProof_1 P : P -∗ P.
  Proof. iStartProof. iStartProof. iIntros "$". Qed.
  Lemma test_iStartProof_2 P : P -∗ P.
  Proof. iStartProof monPred. iStartProof monPredI. iIntros "$". Qed.
  Lemma test_iStartProof_3 P : P -∗ P.
  Proof. iStartProof monPredI. iStartProof monPredSI. iIntros "$". Qed.
  Lemma test_iStartProof_4 P : P -∗ P.
  Proof. iStartProof monPredSI. iStartProof monPred. iIntros "$". Qed.
  Lemma test_iStartProof_5 P : P -∗ P.
  Proof. iStartProof PROP. iIntros (i) "$". Qed.
  Lemma test_iStartProof_6 P : P ⊣⊢ P.
  Proof. iStartProof PROP. iIntros (i). iSplit; iIntros "$". Qed.
  Lemma test_iStartProof_7 P : ((P ≡ P)%I : monPredI).
  Proof. iStartProof PROP. done. Qed.

  Lemma test_intowand_1 P Q : (P -∗ Q) -∗ P -∗ Q.
  Proof.
    iStartProof PROP. iIntros (i) "HW". iIntros (j ->) "HP". by iApply "HW".
  Qed.
  Lemma test_intowand_2 P Q : (P -∗ Q) -∗ P -∗ Q.
  Proof.
    iStartProof PROP. iIntros (i) "HW". iIntros (j ->) "HP".
    iSpecialize ("HW" with "[HP //]"). done.
  Qed.
  Lemma test_intowand_3 P Q : (P -∗ Q) -∗ P -∗ Q.
  Proof.
    iStartProof PROP. iIntros (i) "HW". iIntros (j ->) "HP".
    iSpecialize ("HW" with "HP"). done.
  Qed.
  Lemma test_intowand_4 P Q : (P -∗ Q) -∗ ▷ P -∗ ▷ Q.
  Proof.
    iStartProof PROP. iIntros (i) "HW". iIntros (j ->) "HP". by iApply "HW".
  Qed.
  Lemma test_intowand_5 P Q : (P -∗ Q) -∗ ▷ P -∗ ▷ Q.
  Proof.
    iStartProof PROP. iIntros (i) "HW". iIntros (j ->) "HP".
    iSpecialize ("HW" with "HP"). done.
  Qed.

  Lemma test_apply_in_elim (P : monPredI) (i : I) : monPred_in i ∧ ⎡ P i ⎤ -∗ P.
  Proof.
    iIntros. by iApply monPred_in_elim.
  Qed.
End tests.
