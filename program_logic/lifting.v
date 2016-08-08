From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ownership.
From iris.proofmode Require Import pviewshifts.

Section lifting.
Context `{irisG Λ Σ}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Lemma wp_lift_step E Φ e1 :
  to_val e1 = None →
  (|={E,∅}=> ∃ σ1, ■ reducible e1 σ1 ★ ▷ ownP σ1 ★
    ▷ ∀ e2 σ2 efs, ■ prim_step e1 σ1 e2 σ2 efs ★ ownP σ2
          ={∅,E}=★ WP e2 @ E {{ Φ }} ★ wp_fork efs)
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "H". rewrite wp_unfold /wp_pre; iRight; iSplit; auto.
  iIntros (σ1) "Hσ". iVs "H" as (σ1') "(% & >Hσf & H)".
  iDestruct (ownP_agree σ1 σ1' with "[#]") as %<-; first by iFrame.
  iVsIntro; iSplit; [done|]; iNext; iIntros (e2 σ2 efs Hstep).
  iVs (ownP_update σ1 σ2 with "[-H]") as "[$ ?]"; first by iFrame.
  iApply "H"; eauto.
Qed.

Lemma wp_lift_pure_step E Φ e1 :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2 efs, prim_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (▷ ∀ e2 efs σ, ■ prim_step e1 σ e2 σ efs → WP e2 @ E {{ Φ }} ★ wp_fork efs)
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (He Hsafe Hstep) "H". rewrite wp_unfold /wp_pre; iRight; iSplit; auto.
  iIntros (σ1) "Hσ". iApply pvs_intro'; [set_solver|iIntros "Hclose"].
  iSplit; [done|]; iNext; iIntros (e2 σ2 efs ?).
  destruct (Hstep σ1 e2 σ2 efs); auto; subst.
  iVs "Hclose"; iVsIntro. iFrame "Hσ". iApply "H"; auto.
Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_atomic_step {E Φ} e1 σ1 :
  atomic e1 →
  reducible e1 σ1 →
  ▷ ownP σ1 ★ ▷ (∀ v2 σ2 efs,
    ■ prim_step e1 σ1 (of_val v2) σ2 efs ∧ ownP σ2 -★ (|={E}=> Φ v2) ★ wp_fork efs)
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (Hatomic ?) "[Hσ H]".
  iApply (wp_lift_step E _ e1); eauto using reducible_not_val.
  iApply pvs_intro'; [set_solver|iIntros "Hclose"].
  iExists σ1. iFrame "Hσ"; iSplit; eauto.
  iNext; iIntros (e2 σ2 efs) "[% Hσ]".
  edestruct (Hatomic σ1 e2 σ2 efs) as [v2 <-%of_to_val]; eauto.
  iDestruct ("H" $! v2 σ2 efs with "[Hσ]") as "[HΦ $]"; first by eauto.
  iVs "Hclose". iVs "HΦ". iApply wp_value; auto using to_of_val.
Qed.

Lemma wp_lift_atomic_det_step {E Φ e1} σ1 v2 σ2 efs :
  atomic e1 →
  reducible e1 σ1 →
  (∀ e2' σ2' efs', prim_step e1 σ1 e2' σ2' efs' →
                   σ2 = σ2' ∧ to_val e2' = Some v2 ∧ efs = efs') →
  ▷ ownP σ1 ★ ▷ (ownP σ2 -★ (|={E}=> Φ v2) ★ wp_fork efs) ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?? Hdet) "[Hσ1 Hσ2]". iApply (wp_lift_atomic_step _ σ1); try done.
  iFrame. iNext. iIntros (v2' σ2' efs') "[% Hσ2']".
  edestruct Hdet as (->&->%of_to_val%(inj of_val)&->). done. by iApply "Hσ2".
Qed.

Lemma wp_lift_pure_det_step {E Φ} e1 e2 efs :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs', prim_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs')→
  ▷ (WP e2 @ E {{ Φ }} ★ wp_fork efs) ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?? Hpuredet) "?". iApply (wp_lift_pure_step E); try done.
  by intros; eapply Hpuredet. iNext. by iIntros (e' efs' σ (_&->&->)%Hpuredet).
Qed.
End lifting.
