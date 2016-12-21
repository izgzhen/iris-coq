(** Some derived lemmas for ectx-based languages *)
From iris.program_logic Require Export ectx_language weakestpre lifting.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section wp.
Context {expr val ectx state} {Λ : EctxLanguage expr val ectx state}.
Context `{irisG (ectx_lang expr) Σ} {Hinh : Inhabited state}.
Implicit Types p : pbit.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr.
Hint Resolve head_prim_reducible head_reducible_prim_step.
Hint Resolve (reducible_not_val _ inhabitant).

Definition head_progressive (e : expr) (σ : state) :=
  is_Some(to_val e) ∨ ∃ K e', e = fill K e' ∧ head_reducible e' σ.

Lemma progressive_head_progressive e σ :
  progressive e σ → head_progressive e σ.
Proof.
  case=>[?|Hred]; first by left.
  right. move: Hred=> [] e' [] σ' [] efs [] K e1' e2' EQ EQ' Hstep. subst.
  exists K, e1'. split; first done. by exists e2', σ', efs.
Qed.
Hint Resolve progressive_head_progressive.

Lemma wp_ectx_bind {p E e} K Φ :
  WP e @ p; E {{ v, WP fill K (of_val v) @ p; E {{ Φ }} }}
  ⊢ WP fill K e @ p; E {{ Φ }}.
Proof. apply: weakestpre.wp_bind. Qed.

Lemma wp_ectx_bind_inv {p E Φ} K e :
  WP fill K e @ p; E {{ Φ }}
  ⊢ WP e @ p; E {{ v, WP fill K (of_val v) @ p; E {{ Φ }} }}.
Proof. apply: weakestpre.wp_bind_inv. Qed.

Lemma wp_lift_head_step {p E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ p; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step=>//. iIntros (σ1) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by destruct p; eauto. iNext. iIntros (e2 σ2 efs) "%".
  iApply "H"; eauto.
Qed.

(*
  PDS: Discard. It's confusing. In practice, we just need rules
  like wp_lift_head_{step,stuck}.
*)
Lemma wp_strong_lift_head_step p E Φ e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if p then head_reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ p; E {{ Φ }}
      ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step=>//. iIntros (σ1) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by destruct p; eauto. iNext. iIntros (e2 σ2 efs) "%".
  iApply "H"; eauto.
Qed.

Lemma wp_lift_head_stuck E Φ e :
  to_val e = None →
  (∀ σ, state_interp σ ={E,∅}=∗ ⌜¬ head_progressive e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_stuck; first done.
  iIntros (σ) "Hσ". iMod ("H" with "Hσ") as "%". by auto. 
Qed.

Lemma wp_lift_pure_head_step {p E E' Φ} e1 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2 σ2 efs, head_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (|={E,E'}▷=> ∀ e2 efs σ, ⌜head_step e1 σ e2 σ efs⌝ →
    WP e2 @ p; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof using Hinh.
  iIntros (??) "H". iApply wp_lift_pure_step; eauto.
  { by destruct p; auto. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (????). iApply "H"; eauto.
Qed.

(* PDS: Discard. *)
Lemma wp_strong_lift_pure_head_step p E Φ e1 :
  to_val e1 = None →
  (∀ σ1, if p then head_reducible e1 σ1 else True) →
  (∀ σ1 e2 σ2 efs, prim_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (▷ ∀ e2 efs σ, ⌜prim_step e1 σ e2 σ efs⌝ →
    WP e2 @ p; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof using Hinh.
  iIntros (???) "H". iApply wp_lift_pure_step; eauto. by destruct p; auto.
Qed.

Lemma wp_lift_pure_head_stuck E Φ e :
  to_val e = None →
  (∀ K e1 σ1 e2 σ2 efs, e = fill K e1 → ¬ head_step e1 σ1 e2 σ2 efs) →
  WP e @ E ?{{ Φ }}%I.
Proof using Hinh.
  iIntros (Hnv Hnstep). iApply wp_lift_head_stuck; first done.
  iIntros (σ) "_". iMod (fupd_intro_mask' E ∅) as "_"; first set_solver.
  iModIntro. iPureIntro. case; first by rewrite Hnv; case.
  move=>[] K [] e1 [] Hfill [] e2 [] σ2 [] efs /= Hstep. exact: Hnstep.
Qed.

Lemma wp_lift_atomic_head_step {E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗ [∗ list] ef ∈ efs, WP ef {{ _, True }})
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by eauto. iNext. iIntros (e2 σ2 efs) "%". iApply "H"; auto.
Qed.

(* PDS: Discard. *)
Lemma wp_strong_lift_atomic_head_step {p E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜if p then head_reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗ default False (to_val e2) Φ
      ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct p; eauto.
  by iNext; iIntros (e2 σ2 efs ?); iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step_no_fork {E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ state_interp σ2 ∗ default False (to_val e2) Φ)
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iNext; iIntros (v2 σ2 efs) "%".
  iMod ("H" $! v2 σ2 efs with "[# //]") as "(% & $ & $)"; subst; auto.
Qed.

(* PDS: Discard. *)
Lemma wp_strong_lift_atomic_head_step_no_fork {p E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜if p then head_reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ state_interp σ2 ∗ default False (to_val e2) Φ)
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_strong_lift_atomic_head_step; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" with "Hσ1") as "[$ H]"; iModIntro.
  iNext; iIntros (v2 σ2 efs) "%".
  iMod ("H" with "[#]") as "(% & $ & $)"=>//; subst.
  by iApply big_sepL_nil.
Qed.

Lemma wp_lift_pure_det_head_step {p E E' Φ} e1 e2 efs :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs') →
  (|={E,E'}▷=> WP e2 @ p; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step e1 e2 efs); eauto.
  destruct p; by auto.
Qed.

(* PDS: Discard. *)
Lemma wp_strong_lift_pure_det_head_step {p E Φ} e1 e2 efs :
  to_val e1 = None →
  (∀ σ1, if p then head_reducible e1 σ1 else True) →
  (∀ σ1 e2' σ2 efs',
    prim_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs') →
  ▷ (WP e2 @ p; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ p; ⊤ {{ _, True }})
  ⊢ WP e1 @ p; E {{ Φ }}.
Proof using Hinh.
  iIntros (???) "H"; iApply wp_lift_pure_det_step; eauto.
  by destruct p; eauto.
Qed.

Lemma wp_lift_pure_det_head_step_no_fork {p E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
  (|={E,E'}▷=> WP e2 @ p; E {{ Φ }}) ⊢ WP e1 @ p; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step e1 e2 []) /= ?right_id; eauto.
  destruct p; by auto.
Qed.

Lemma wp_lift_pure_det_head_step_no_fork' {p E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
  ▷ WP e2 @ E {{ Φ }} ⊢ WP e1 @ E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(WP e1 @ _ {{ _ }})%I]wp_lift_pure_det_head_step_no_fork //.
  rewrite -step_fupd_intro //.
Qed.

(* PDS: Discard. *)
Lemma wp_strong_lift_pure_det_head_step_no_fork {p E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, if p then head_reducible e1 σ1 else True) →
  (∀ σ1 e2' σ2 efs',
    prim_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
  ▷ WP e2 @ p; E {{ Φ }} ⊢ WP e1 @ p; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step e1 e2 []) ?big_sepL_nil ?right_id; eauto.
  by destruct p; eauto.
Qed.
End wp.
