From iris.proofmode Require Import tactics monpred.
From iris.base_logic Require Import base_logic lib.invariants.

Section tests.
  Context {I : bi_index} {PROP : sbi}.
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

End tests.