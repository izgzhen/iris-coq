From iris.proofmode Require Import tactics monpred.

Section tests.
  Context {I : biIndex} {PROP : sbi}.
  Local Notation monPred := (monPred I PROP).
  Local Notation monPredI := (monPredI I PROP).
  Local Notation monPredSI := (monPredSI I PROP).
  Implicit Types P Q R : monPred.
  Implicit Types 𝓟 𝓠 𝓡 : PROP.
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
    iStartProof PROP. iIntros (i) "HW". Show.
    iIntros (j ->) "HP". Show. by iApply "HW".
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

  Lemma test_apply_in_elim (P : monPredI) (i : I) : monPred_in i -∗ ⎡ P i ⎤ → P.
  Proof. iIntros. by iApply monPred_in_elim. Qed.

  Lemma test_iStartProof_forall_1 (Φ : nat → monPredI) : ∀ n, Φ n -∗ Φ n.
  Proof.
    iStartProof PROP. iIntros (n i) "$".
  Qed.
  Lemma test_iStartProof_forall_2 (Φ : nat → monPredI) : ∀ n, Φ n -∗ Φ n.
  Proof.
    iStartProof. iIntros (n) "$".
  Qed.

  Lemma test_embed_wand (P Q : PROP) : (⎡P⎤ -∗ ⎡Q⎤) -∗ ⎡P -∗ Q⎤ : monPred.
  Proof.
    iIntros "H HP". by iApply "H".
  Qed.

  Lemma test_objectively P Q : <obj> emp -∗ <obj> P -∗ <obj> Q -∗ <obj> (P ∗ Q).
  Proof. iIntros "#? HP HQ". iAlways. by iSplitL "HP". Qed.

  Lemma test_objectively_absorbing P Q R `{!Absorbing P} :
    <obj> emp -∗ <obj> P -∗ <obj> Q -∗ R -∗ <obj> (P ∗ Q).
  Proof. iIntros "#? HP HQ HR". iAlways. by iSplitL "HP". Qed.

  Lemma test_objectively_affine P Q R `{!Affine R} :
    <obj> emp -∗ <obj> P -∗ <obj> Q -∗ R -∗ <obj> (P ∗ Q).
  Proof. iIntros "#? HP HQ HR". iAlways. by iSplitL "HP". Qed.

  Lemma test_iModIntro_embed P `{!Affine Q} 𝓟 𝓠 :
    □ P -∗ Q -∗ ⎡𝓟⎤ -∗ ⎡𝓠⎤ -∗ ⎡ 𝓟 ∗ 𝓠 ⎤.
  Proof. iIntros "#H1 _ H2 H3". iAlways. iFrame. Qed.

  Lemma test_iModIntro_embed_objective P `{!Objective Q} 𝓟 𝓠 :
    □ P -∗ Q -∗ ⎡𝓟⎤ -∗ ⎡𝓠⎤ -∗ ⎡ ∀ i, 𝓟 ∗ 𝓠 ∗ Q i ⎤.
  Proof. iIntros "#H1 H2 H3 H4". iAlways. Show. iFrame. Qed.

  Lemma test_iModIntro_embed_nested P 𝓟 𝓠 :
    □ P -∗ ⎡◇ 𝓟⎤ -∗ ⎡◇ 𝓠⎤ -∗ ⎡ ◇ (𝓟 ∗ 𝓠) ⎤.
  Proof. iIntros "#H1 H2 H3". iModIntro ⎡ _ ⎤%I. by iSplitL "H2". Qed.

  Lemma test_into_wand_embed 𝓟 𝓠 :
    (𝓟 -∗ ◇ 𝓠) →
    ⎡𝓟⎤ ⊢@{monPredI} ◇ ⎡𝓠⎤.
  Proof.
    iIntros (HPQ) "HP".
    iMod (HPQ with "[-]") as "$"; last by auto.
    iAssumption.
  Qed.

  (* This is a hack to avoid avoid coq bug #5735: sections variables ignore hint
     modes. So we assume the instances in a way that cannot be used by type
     class resolution, and then separately declare the instance as such. *)
  Context (FU0 : BiFUpd PROP * unit).
  Instance FU : BiFUpd PROP := fst FU0.

  Lemma test_apply_fupd_intro_mask E1 E2 P :
    E2 ⊆ E1 → P -∗ |={E1,E2}=> |={E2,E1}=> P.
  Proof. iIntros. by iApply @fupd_intro_mask. Qed.
  Lemma test_apply_fupd_intro_mask_2 E1 E2 P :
    E2 ⊆ E1 → P -∗ |={E1,E2}=> |={E2,E1}=> P.
  Proof. iIntros. iFrame. by iApply @fupd_intro_mask'. Qed.

  Lemma test_iFrame_embed_persistent (P : PROP) (Q: monPred) :
    Q ∗ □ ⎡P⎤ ⊢ Q ∗ ⎡P ∗ P⎤.
  Proof.
    iIntros "[$ #HP]". iFrame "HP".
  Qed.

  Lemma test_iNext_Bi P :
    @bi_entails monPredI (▷ P) (▷ P).
  Proof. iIntros "H". by iNext. Qed.

  (** Test monPred_at framing *)
  Lemma test_iFrame_monPred_at_wand (P Q : monPred) i :
    P i -∗ (Q -∗ P) i.
  Proof. iIntros "$". Show. Abort.

  Program Definition monPred_id (R : monPred) : monPred :=
    MonPred (λ V, R V) _.
  Next Obligation. intros ? ???. eauto. Qed.

  Lemma test_iFrame_monPred_id (Q R : monPred) i :
    Q i ∗ R i -∗ (Q ∗ monPred_id R) i.
  Proof.
    iIntros "(HQ & HR)". iFrame "HR". iAssumption.
  Qed.

  Lemma test_iFrame_rel P i j ij :
    IsBiIndexRel i ij → IsBiIndexRel j ij →
    P i -∗ P j -∗ P ij ∗ P ij.
  Proof. iIntros (??) "HPi HPj". iFrame. Qed.

  Lemma test_iFrame_later_rel `{!BiAffine PROP} P i j :
    IsBiIndexRel i j →
    ▷ (P i) -∗ (▷ P) j.
  Proof. iIntros (?) "?". iFrame. Qed.

  Lemma test_iFrame_laterN n P i :
    ▷^n (P i) -∗ (▷^n P) i.
  Proof. iIntros "?". iFrame. Qed.

  Lemma test_iFrame_quantifiers P i :
    P i -∗ (∀ _:(), ∃ _:(), P) i.
  Proof. iIntros "?". iFrame. Show. iIntros ([]). iExists (). iEmpIntro. Qed.

  Lemma test_iFrame_embed (P : PROP) i :
    P -∗ (embed (B:=monPredI) P) i.
  Proof. iIntros "$". Qed.

  (* Make sure search doesn't diverge on an evar *)
  Lemma test_iFrame_monPred_at_evar (P : monPred) i j :
    P i -∗ ∃ Q, (Q j).
  Proof. iIntros "HP". iExists _. Fail iFrame "HP". Abort.

End tests.
