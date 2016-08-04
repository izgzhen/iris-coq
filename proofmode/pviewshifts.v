From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export tactics ghost_ownership.
From iris.program_logic Require Export pviewshifts.
Import uPred.

Section pvs.
Context `{irisG Λ Σ}.
Implicit Types P Q : iProp Σ.

Global Instance from_pure_pvs E P φ : FromPure P φ → FromPure (|={E}=> P) φ.
Proof. intros ??. by rewrite -pvs_intro (from_pure P). Qed.

Global Instance from_assumption_pvs E p P Q :
  FromAssumption p P (|=r=> Q) → FromAssumption p P (|={E}=> Q)%I.
Proof. rewrite /FromAssumption=>->. apply rvs_pvs. Qed.

Global Instance into_wand_pvs E1 E2 R P Q :
  IntoWand R P Q → IntoWand R (|={E1,E2}=> P) (|={E1,E2}=> Q) | 100.
Proof. rewrite /IntoWand=>->. apply wand_intro_l. by rewrite pvs_wand_r. Qed.

Global Instance from_sep_pvs E P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|={E}=> P) (|={E}=> Q1) (|={E}=> Q2).
Proof. rewrite /FromSep=><-. apply pvs_sep. Qed.

Global Instance or_split_pvs E1 E2 P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|={E1,E2}=> P) (|={E1,E2}=> Q1) (|={E1,E2}=> Q2).
Proof. rewrite /FromOr=><-. apply or_elim; apply pvs_mono; auto with I. Qed.

Global Instance exists_split_pvs {A} E1 E2 P (Φ : A → iProp Σ) :
  FromExist P Φ → FromExist (|={E1,E2}=> P) (λ a, |={E1,E2}=> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.

Global Instance frame_pvs E1 E2 R P Q :
  Frame R P Q → Frame R (|={E1,E2}=> P) (|={E1,E2}=> Q).
Proof. rewrite /Frame=><-. by rewrite pvs_frame_l. Qed.

Global Instance to_assert_pvs E1 E2 P Q :
  IntoAssert P (|={E1,E2}=> Q) (|={E1}=> P).
Proof. intros. by rewrite /IntoAssert pvs_frame_r wand_elim_r pvs_trans. Qed.

Global Instance is_now_True_pvs E1 E2 P : IsNowTrue (|={E1,E2}=> P).
Proof. by rewrite /IsNowTrue now_True_pvs. Qed.

Global Instance from_vs_pvs E P : FromVs (|={E}=> P) P.
Proof. by rewrite /FromVs -rvs_pvs. Qed.

Global Instance elim_vs_rvs_pvs E1 E2 P Q :
  ElimVs (|=r=> P) P (|={E1,E2}=> Q) (|={E1,E2}=> Q).
Proof. by rewrite /ElimVs (rvs_pvs E1) pvs_frame_r wand_elim_r pvs_trans. Qed.
Global Instance elim_vs_pvs_pvs E1 E2 E3 P Q :
  ElimVs (|={E1,E2}=> P) P (|={E1,E3}=> Q) (|={E2,E3}=> Q).
Proof. by rewrite /ElimVs pvs_frame_r wand_elim_r pvs_trans. Qed.
End pvs.

Hint Extern 2 (of_envs _ ⊢ _) =>
  match goal with |- _ ⊢ |={_}=> _ => iVsIntro end.
