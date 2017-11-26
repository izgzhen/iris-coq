From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import lifting adequacy.
From iris.program_logic Require ectx_language.
From iris.algebra Require Import auth.
From iris.proofmode Require Import tactics classes.
Set Default Proof Using "Type".

Class ownPG' (Λstate : Type) (Σ : gFunctors) := OwnPG {
  ownP_invG : invG Σ;
  ownP_inG :> inG Σ (authR (optionUR (exclR (leibnizC Λstate))));
  ownP_name : gname;
}.
Notation ownPG Λ Σ := (ownPG' (state Λ) Σ).

Instance ownPG_irisG `{ownPG' Λstate Σ} : irisG' Λstate Σ := {
  iris_invG := ownP_invG;
  state_interp σ := own ownP_name (● (Excl' (σ:leibnizC Λstate)))
}.
Global Opaque iris_invG.

Definition ownPΣ (Λstate : Type) : gFunctors :=
  #[invΣ;
    GFunctor (authUR (optionUR (exclR (leibnizC Λstate))))].

Class ownPPreG' (Λstate : Type) (Σ : gFunctors) : Set := IrisPreG {
  ownPPre_invG :> invPreG Σ;
  ownPPre_inG :> inG Σ (authR (optionUR (exclR (leibnizC Λstate))))
}.
Notation ownPPreG Λ Σ := (ownPPreG' (state Λ) Σ).

Instance subG_ownPΣ {Λstate Σ} : subG (ownPΣ Λstate) Σ → ownPPreG' Λstate Σ.
Proof. solve_inG. Qed.

(** Ownership *)
Definition ownP `{ownPG' Λstate Σ} (σ : Λstate) : iProp Σ :=
  own ownP_name (◯ (Excl' σ)).
Typeclasses Opaque ownP.
Instance: Params (@ownP) 3.


(* Adequacy *)
Theorem ownP_adequacy Σ `{ownPPreG Λ Σ} s e σ φ :
  (∀ `{ownPG Λ Σ}, ownP σ ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ φ.
Proof.
  intros Hwp. apply (wp_adequacy Σ _).
  iIntros (?) "". iMod (own_alloc (● (Excl' (σ : leibnizC _)) ⋅ ◯ (Excl' σ)))
    as (γσ) "[Hσ Hσf]"; first done.
  iModIntro. iExists (λ σ, own γσ (● (Excl' (σ:leibnizC _)))). iFrame "Hσ".
  iApply (Hwp (OwnPG _ _ _ _ γσ)). by rewrite /ownP.
Qed.

Theorem ownP_invariance Σ `{ownPPreG Λ Σ} s e σ1 t2 σ2 φ :
  (∀ `{ownPG Λ Σ},
    ownP σ1 ={⊤}=∗ WP e @ s; ⊤ {{ _, True }} ∗ |={⊤,∅}=> ∃ σ', ownP σ' ∧ ⌜φ σ'⌝) →
  rtc step ([e], σ1) (t2, σ2) →
  φ σ2.
Proof.
  intros Hwp Hsteps. eapply (wp_invariance Σ Λ s e σ1 t2 σ2 _)=> //.
  iIntros (?) "". iMod (own_alloc (● (Excl' (σ1 : leibnizC _)) ⋅ ◯ (Excl' σ1)))
    as (γσ) "[Hσ Hσf]"; first done.
  iExists (λ σ, own γσ (● (Excl' (σ:leibnizC _)))). iFrame "Hσ".
  iMod (Hwp (OwnPG _ _ _ _ γσ) with "[Hσf]") as "[$ H]"; first by rewrite /ownP.
  iIntros "!> Hσ". iMod "H" as (σ2') "[Hσf %]". rewrite/ownP.
  iDestruct (own_valid_2 with "Hσ Hσf")
    as %[->%Excl_included%leibniz_equiv _]%auth_valid_discrete_2; auto.
Qed.


(** Lifting *)
Section lifting.
  Context `{ownPG Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types e : expr Λ.
  Implicit Types Φ : val Λ → iProp Σ.

  Lemma ownP_eq σ1 σ2 : state_interp σ1 -∗ ownP σ2 -∗ ⌜σ1 = σ2⌝.
  Proof.
    iIntros "Hσ1 Hσ2"; rewrite/ownP.
    by iDestruct (own_valid_2 with "Hσ1 Hσ2")
      as %[->%Excl_included%leibniz_equiv _]%auth_valid_discrete_2.
  Qed.
  Lemma ownP_twice σ1 σ2 : ownP σ1 ∗ ownP σ2 ⊢ False.
  Proof. rewrite /ownP -own_op own_valid. by iIntros (?). Qed.
  Global Instance ownP_timeless σ : Timeless (@ownP (state Λ) Σ _ σ).
  Proof. rewrite /ownP; apply _. Qed.

  Lemma ownP_lift_step s E Φ e1 :
    to_val e1 = None →
    (|={E,∅}=> ∃ σ1, ⌜if s is not_stuck then reducible e1 σ1 else True⌝ ∗ ▷ ownP σ1 ∗
      ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ -∗ ownP σ2
            ={∅,E}=∗ WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_step; first done.
    iIntros (σ1) "Hσ"; iMod "H" as (σ1') "(% & >Hσf & H)".
    iDestruct (ownP_eq with "Hσ Hσf") as %->.
    iModIntro. iSplit; first done. iNext. iIntros (e2 σ2 efs Hstep).
    rewrite /ownP; iMod (own_update_2 with "Hσ Hσf") as "[Hσ Hσf]".
    { by apply auth_update, option_local_update,
        (exclusive_local_update _ (Excl σ2)). }
    iFrame "Hσ". by iApply ("H" with "[]"); eauto.
  Qed.

  Lemma ownP_lift_stuck E Φ e :
    (|={E,∅}=> ∃ σ, ⌜stuck e σ⌝ ∗ ▷ ownP σ)
    ⊢ WP e @ E ?{{ Φ }}.
  Proof.
    iIntros "H". destruct (to_val e) as [v|] eqn:EQe.
    - apply of_to_val in EQe as <-. iApply fupd_wp.
      iMod "H" as (σ1) "[H _]". iDestruct "H" as %[Hnv _]. exfalso.
      by rewrite to_of_val in Hnv.
    - iApply wp_lift_stuck; [done|]. iIntros (σ1) "Hσ".
      iMod "H" as (σ1') "(% & >Hσf)".
      by iDestruct (ownP_eq with "Hσ Hσf") as %->.
  Qed.

  Lemma ownP_lift_pure_step s E Φ e1 :
    to_val e1 = None →
    (∀ σ1, if s is not_stuck then reducible e1 σ1 else True) →
    (∀ σ1 e2 σ2 efs, prim_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
    (▷ ∀ e2 efs σ, ⌜prim_step e1 σ e2 σ efs⌝ →
      WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (? Hsafe Hstep) "H"; iApply wp_lift_step; first done.
    iIntros (σ1) "Hσ". iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
    iModIntro; iSplit; [by destruct s|]; iNext; iIntros (e2 σ2 efs ?).
    destruct (Hstep σ1 e2 σ2 efs); auto; subst.
    by iMod "Hclose"; iModIntro; iFrame; iApply "H".
  Qed.

  (** Derived lifting lemmas. *)
  Lemma ownP_lift_atomic_step {s E Φ} e1 σ1 :
    to_val e1 = None →
    (if s is not_stuck then reducible e1 σ1 else True) →
    (▷ ownP σ1 ∗ ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ -∗ ownP σ2 -∗
      default False (to_val e2) Φ ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (??) "[Hσ H]"; iApply ownP_lift_step; first done.
    iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
    iModIntro; iExists σ1; iFrame; iSplit; first by destruct s.
    iNext; iIntros (e2 σ2 efs) "% Hσ".
    iDestruct ("H" $! e2 σ2 efs with "[] [Hσ]") as "[HΦ $]"; [by eauto..|].
    destruct (to_val e2) eqn:?; last by iExFalso.
    by iMod "Hclose"; iApply wp_value; auto using to_of_val.
  Qed.

  Lemma ownP_lift_atomic_det_step {s E Φ e1} σ1 v2 σ2 efs :
    to_val e1 = None →
    (if s is not_stuck then reducible e1 σ1 else True) →
    (∀ e2' σ2' efs', prim_step e1 σ1 e2' σ2' efs' →
                     σ2 = σ2' ∧ to_val e2' = Some v2 ∧ efs = efs') →
    ▷ ownP σ1 ∗ ▷ (ownP σ2 -∗
      Φ v2 ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?? Hdet) "[Hσ1 Hσ2]"; iApply ownP_lift_atomic_step; try done.
    iFrame; iNext; iIntros (e2' σ2' efs') "% Hσ2'".
    edestruct Hdet as (->&Hval&->). done. by rewrite Hval; iApply "Hσ2".
  Qed.

  Lemma ownP_lift_atomic_det_step_no_fork {s E e1} σ1 v2 σ2 :
    to_val e1 = None →
    (if s is not_stuck then reducible e1 σ1 else True) →
    (∀ e2' σ2' efs', prim_step e1 σ1 e2' σ2' efs' →
      σ2 = σ2' ∧ to_val e2' = Some v2 ∧ [] = efs') →
    {{{ ▷ ownP σ1 }}} e1 @ s; E {{{ RET v2; ownP σ2 }}}.
  Proof.
    intros. rewrite -(ownP_lift_atomic_det_step σ1 v2 σ2 []); [|done..].
    rewrite big_sepL_nil right_id. by apply uPred.wand_intro_r.
  Qed.

  Lemma ownP_lift_pure_det_step {s E Φ} e1 e2 efs :
    to_val e1 = None →
    (∀ σ1, if s is not_stuck then reducible e1 σ1 else True) →
    (∀ σ1 e2' σ2 efs', prim_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs')→
    ▷ (WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤{{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?? Hpuredet) "?"; iApply ownP_lift_pure_step=>//.
    by apply Hpuredet. by iNext; iIntros (e' efs' σ (_&->&->)%Hpuredet).
  Qed.

  Lemma ownP_lift_pure_det_step_no_fork `{Inhabited (state Λ)} {s E Φ} e1 e2 :
    to_val e1 = None →
    (∀ σ1, if s is not_stuck then reducible e1 σ1 else True) →
    (∀ σ1 e2' σ2 efs', prim_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
    ▷ WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_pure_det_step e1 e2 []) ?big_sepL_nil ?right_id; eauto.
  Qed.
End lifting.

Section ectx_lifting.
  Import ectx_language.
  Context {Λ : ectxLanguage} `{ownPG Λ Σ} {Hinh : Inhabited (state Λ)}.
  Implicit Types s : stuckness.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types e : expr Λ.
  Hint Resolve head_prim_reducible head_reducible_prim_step.
  Hint Resolve (reducible_not_val _ inhabitant).
  Hint Resolve head_stuck_stuck.

  Lemma ownP_lift_head_step s E Φ e1 :
    to_val e1 = None →
    (|={E,∅}=> ∃ σ1, ⌜head_reducible e1 σ1⌝ ∗ ▷ ownP σ1 ∗
      ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ -∗ ownP σ2
            ={∅,E}=∗ WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply ownP_lift_step; first done.
    iMod "H" as (σ1 ?) "[Hσ1 Hwp]". iModIntro. iExists σ1.
    iSplit; first by destruct s; eauto. iFrame. iNext. iIntros (e2 σ2 efs) "% ?".
    iApply ("Hwp" with "[]"); eauto.
  Qed.

  Lemma ownP_lift_head_stuck E Φ e :
    sub_redexes_are_values e →
    (|={E,∅}=> ∃ σ, ⌜head_stuck e σ⌝ ∗ ▷ ownP σ)
    ⊢ WP e @ E ?{{ Φ }}.
  Proof.
    iIntros (?) "H". iApply ownP_lift_stuck. iMod "H" as (σ) "[% >Hσ]".
    iExists σ. by auto.
  Qed.

  Lemma ownP_lift_pure_head_step s E Φ e1 :
    to_val e1 = None →
    (∀ σ1, head_reducible e1 σ1) →
    (∀ σ1 e2 σ2 efs, head_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
    (▷ ∀ e2 efs σ, ⌜head_step e1 σ e2 σ efs⌝ →
      WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof using Hinh.
    iIntros (???) "H".  iApply ownP_lift_pure_step; eauto.
    { by destruct s; auto. }
    iNext. iIntros (????). iApply "H"; eauto.
  Qed.

  Lemma ownP_lift_atomic_head_step {s E Φ} e1 σ1 :
    to_val e1 = None →
    head_reducible e1 σ1 →
    ▷ ownP σ1 ∗ ▷ (∀ e2 σ2 efs,
    ⌜head_step e1 σ1 e2 σ2 efs⌝ -∗ ownP σ2 -∗
      default False (to_val e2) Φ ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (??) "[? H]". iApply ownP_lift_atomic_step; eauto.
    { by destruct s; eauto. }
    iFrame. iNext. iIntros (???) "% ?". iApply ("H" with "[]"); eauto.
  Qed.

  Lemma ownP_lift_atomic_det_head_step {s E Φ e1} σ1 v2 σ2 efs :
    to_val e1 = None →
    head_reducible e1 σ1 →
    (∀ e2' σ2' efs', head_step e1 σ1 e2' σ2' efs' →
      σ2 = σ2' ∧ to_val e2' = Some v2 ∧ efs = efs') →
    ▷ ownP σ1 ∗ ▷ (ownP σ2 -∗ Φ v2 ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    by destruct s; eauto 10 using ownP_lift_atomic_det_step.
  Qed.

  Lemma ownP_lift_atomic_det_head_step_no_fork {s E e1} σ1 v2 σ2 :
    to_val e1 = None →
    head_reducible e1 σ1 →
    (∀ e2' σ2' efs', head_step e1 σ1 e2' σ2' efs' →
      σ2 = σ2' ∧ to_val e2' = Some v2 ∧ [] = efs') →
    {{{ ▷ ownP σ1 }}} e1 @ s; E {{{ RET v2; ownP σ2 }}}.
  Proof.
    intros ???; apply ownP_lift_atomic_det_step_no_fork; eauto.
    by destruct s; eauto.
  Qed.

  Lemma ownP_lift_pure_det_head_step {s E Φ} e1 e2 efs :
    to_val e1 = None →
    (∀ σ1, head_reducible e1 σ1) →
    (∀ σ1 e2' σ2 efs', head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs') →
    ▷ (WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof using Hinh.
    iIntros (???) "H"; iApply wp_lift_pure_det_step; eauto.
    by destruct s; eauto.
  Qed.

  Lemma ownP_lift_pure_det_head_step_no_fork {s E Φ} e1 e2 :
    to_val e1 = None →
    (∀ σ1, head_reducible e1 σ1) →
    (∀ σ1 e2' σ2 efs', head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
    ▷ WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
  Proof using Hinh.
    iIntros (???) "H". iApply ownP_lift_pure_det_step_no_fork; eauto.
    by destruct s; eauto.
  Qed.
End ectx_lifting.
