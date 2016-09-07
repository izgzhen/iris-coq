From iris.program_logic Require Export iris.
From iris.program_logic Require Import ownership.
From iris.algebra Require Import upred_big_op gmap.
From iris.proofmode Require Import tactics.
Import uPred.

Program Definition pvs_def `{irisG Λ Σ}
    (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  (wsat ★ ownE E1 =r=★ ◇ (wsat ★ ownE E2 ★ P))%I.
Definition pvs_aux : { x | x = @pvs_def }. by eexists. Qed.
Definition pvs := proj1_sig pvs_aux.
Definition pvs_eq : @pvs = @pvs_def := proj2_sig pvs_aux.
Arguments pvs {_ _ _} _ _ _%I.
Instance: Params (@pvs) 5.

Notation "|={ E1 , E2 }=> Q" := (pvs E1 E2 Q%I)
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }=>  Q") : uPred_scope.
Notation "P ={ E1 , E2 }=★ Q" := (P -★ |={E1,E2}=> Q)%I
  (at level 99, E1,E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }=★  Q") : uPred_scope.
Notation "P ={ E1 , E2 }=> Q" := (P ⊢ |={E1,E2}=> Q)
  (at level 99, E1, E2 at level 50, Q at level 200, only parsing) : C_scope.

Notation "|={ E }=> Q" := (pvs E E Q%I)
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }=>  Q") : uPred_scope.
Notation "P ={ E }=★ Q" := (P -★ |={E}=> Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }=★  Q") : uPred_scope.
Notation "P ={ E }=> Q" := (P ⊢ |={E}=> Q)
  (at level 99, E at level 50, Q at level 200, only parsing) : C_scope.

Notation "|={ E1 , E2 }▷=> Q" := (|={E1%I,E2%I}=> ▷ |={E2,E1}=> Q)%I
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }▷=>  Q") : uPred_scope.
Notation "|={ E }▷=> Q" := (|={E,E}▷=> Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }▷=>  Q") : uPred_scope.

Section pvs.
Context `{irisG Λ Σ}.
Implicit Types P Q : iProp Σ.

Global Instance pvs_ne E1 E2 n : Proper (dist n ==> dist n) (@pvs Λ Σ _ E1 E2).
Proof. rewrite pvs_eq. solve_proper. Qed.
Global Instance pvs_proper E1 E2 : Proper ((≡) ==> (≡)) (@pvs Λ Σ _ E1 E2).
Proof. apply ne_proper, _. Qed.

Lemma pvs_intro' E1 E2 P : E2 ⊆ E1 → ((|={E2,E1}=> True) -★ P) ={E1,E2}=> P.
Proof.
  intros (E1''&->&?)%subseteq_disjoint_union_L.
  rewrite pvs_eq /pvs_def ownE_op //; iIntros "H ($ & $ & HE) !==>".
  iApply except_last_intro. iApply "H".
  iIntros "[$ $] !==>". by iApply except_last_intro.
Qed.
Lemma except_last_pvs E1 E2 P : ◇ (|={E1,E2}=> P) ={E1,E2}=> P.
Proof.
  rewrite pvs_eq. iIntros "H [Hw HE]". iTimeless "H". iApply "H"; by iFrame.
Qed.
Lemma rvs_pvs E P : (|=r=> P) ={E}=> P.
Proof.
  rewrite pvs_eq /pvs_def. iIntros "H [$ $]"; iVs "H".
  iVsIntro. by iApply except_last_intro.
Qed.
Lemma pvs_mono E1 E2 P Q : (P ⊢ Q) → (|={E1,E2}=> P) ={E1,E2}=> Q.
Proof.
  rewrite pvs_eq /pvs_def. iIntros (HPQ) "HP HwE".
  rewrite -HPQ. by iApply "HP".
Qed.
Lemma pvs_trans E1 E2 E3 P : (|={E1,E2}=> |={E2,E3}=> P) ={E1,E3}=> P.
Proof.
  rewrite pvs_eq /pvs_def. iIntros "HP HwE".
  iVs ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
Qed.
Lemma pvs_mask_frame_r' E1 E2 Ef P :
  E1 ⊥ Ef → (|={E1,E2}=> E2 ⊥ Ef → P) ={E1 ∪ Ef,E2 ∪ Ef}=> P.
Proof.
  intros. rewrite pvs_eq /pvs_def ownE_op //. iIntros "Hvs (Hw & HE1 &HEf)".
  iVs ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
  iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
  iVsIntro; iApply except_last_intro. by iApply "HP".
Qed.
Lemma pvs_frame_r E1 E2 P Q : (|={E1,E2}=> P) ★ Q ={E1,E2}=> P ★ Q.
Proof. rewrite pvs_eq /pvs_def. by iIntros "[HwP $]". Qed.

(** * Derived rules *)
Global Instance pvs_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (@pvs Λ Σ _ E1 E2).
Proof. intros P Q; apply pvs_mono. Qed.
Global Instance pvs_flip_mono' E1 E2 :
  Proper (flip (⊢) ==> flip (⊢)) (@pvs Λ Σ _ E1 E2).
Proof. intros P Q; apply pvs_mono. Qed.

Lemma pvs_intro E P : P ={E}=> P.
Proof. iIntros "HP". by iApply rvs_pvs. Qed.
Lemma pvs_except_last E1 E2 P : (|={E1,E2}=> ◇ P) ={E1,E2}=> P.
Proof. by rewrite {1}(pvs_intro E2 P) except_last_pvs pvs_trans. Qed.

Lemma pvs_frame_l E1 E2 P Q : (P ★ |={E1,E2}=> Q) ={E1,E2}=> P ★ Q.
Proof. rewrite !(comm _ P); apply pvs_frame_r. Qed.
Lemma pvs_wand_l E1 E2 P Q : (P -★ Q) ★ (|={E1,E2}=> P) ={E1,E2}=> Q.
Proof. by rewrite pvs_frame_l wand_elim_l. Qed.
Lemma pvs_wand_r E1 E2 P Q : (|={E1,E2}=> P) ★ (P -★ Q) ={E1,E2}=> Q.
Proof. by rewrite pvs_frame_r wand_elim_r. Qed.

Lemma pvs_trans_frame E1 E2 E3 P Q :
  ((Q ={E2,E3}=★ True) ★ |={E1,E2}=> (Q ★ P)) ={E1,E3}=> P.
Proof.
  rewrite pvs_frame_l assoc -(comm _ Q) wand_elim_r.
  by rewrite pvs_frame_r left_id pvs_trans.
Qed.

Lemma pvs_mask_frame_r E1 E2 Ef P :
  E1 ⊥ Ef → (|={E1,E2}=> P) ={E1 ∪ Ef,E2 ∪ Ef}=> P.
Proof.
  iIntros (?) "H". iApply pvs_mask_frame_r'; auto.
  iApply pvs_wand_r; iFrame "H"; eauto.
Qed.
Lemma pvs_mask_mono E1 E2 P : E1 ⊆ E2 → (|={E1}=> P) ={E2}=> P.
Proof.
  intros (Ef&->&?)%subseteq_disjoint_union_L. by apply pvs_mask_frame_r.
Qed.

Lemma pvs_sep E P Q : (|={E}=> P) ★ (|={E}=> Q) ={E}=> P ★ Q.
Proof. by rewrite pvs_frame_r pvs_frame_l pvs_trans. Qed.
Lemma pvs_big_sepM `{Countable K} {A} E (Φ : K → A → iProp Σ) (m : gmap K A) :
  ([★ map] k↦x ∈ m, |={E}=> Φ k x) ={E}=> [★ map] k↦x ∈ m, Φ k x.
Proof.
  rewrite /uPred_big_sepM.
  induction (map_to_list m) as [|[i x] l IH]; csimpl; auto using pvs_intro.
  by rewrite IH pvs_sep.
Qed.
Lemma pvs_big_sepS `{Countable A} E (Φ : A → iProp Σ) X :
  ([★ set] x ∈ X, |={E}=> Φ x) ={E}=> [★ set] x ∈ X, Φ x.
Proof.
  rewrite /uPred_big_sepS.
  induction (elements X) as [|x l IH]; csimpl; csimpl; auto using pvs_intro.
  by rewrite IH pvs_sep.
Qed.
End pvs.
