From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import lifting adequacy.
From iris.program_logic Require ectx_language.
From iris.algebra Require Import auth.
From iris.proofmode Require Import tactics classes.
Set Default Proof Using "Type".

Class ownPG' (Λstate Λobservation: Type) (Σ : gFunctors) := OwnPG {
  ownP_invG : invG Σ;
  ownP_state_inG :> inG Σ (authR (optionUR (exclR (leibnizC Λstate))));
  ownP_obs_inG :> inG Σ (authR (optionUR (exclR (leibnizC (list Λobservation)))));
  ownP_state_name : gname;
  ownP_obs_name : gname
}.
Notation ownPG Λ Σ := (ownPG' (state Λ) (observation Λ) Σ).

Instance ownPG_irisG `{ownPG' Λstate Λobservation Σ} : irisG' Λstate Λobservation Σ := {
  iris_invG := ownP_invG;
  state_interp σ κs := (own ownP_state_name (● (Excl' (σ:leibnizC Λstate))) ∗
                       own ownP_obs_name (● (Excl' (κs:leibnizC (list Λobservation)))))%I
}.
Global Opaque iris_invG.

Definition ownPΣ (Λstate Λobservation : Type) : gFunctors :=
  #[invΣ;
    GFunctor (authR (optionUR (exclR (leibnizC Λstate))));
    GFunctor (authR (optionUR (exclR (leibnizC (list Λobservation)))))].

Class ownPPreG' (Λstate Λobservation : Type) (Σ : gFunctors) : Set := IrisPreG {
  ownPPre_invG :> invPreG Σ;
  ownPPre_state_inG :> inG Σ (authR (optionUR (exclR (leibnizC Λstate))));
  ownPPre_obs_inG :> inG Σ (authR (optionUR (exclR (leibnizC (list Λobservation)))))
}.
Notation ownPPreG Λ Σ := (ownPPreG' (state Λ) (observation Λ) Σ).

Instance subG_ownPΣ {Λstate Λobservation Σ} : subG (ownPΣ Λstate Λobservation) Σ → ownPPreG' Λstate Λobservation Σ.
Proof. solve_inG. Qed.

(** Ownership *)
Definition ownP_state `{ownPG' Λstate Λobservation Σ} (σ : Λstate) : iProp Σ :=
  own ownP_state_name (◯ (Excl' (σ:leibnizC Λstate))).

Definition ownP_obs `{ownPG' Λstate Λobservation Σ} (κs: list Λobservation) : iProp Σ :=
  own ownP_obs_name (◯ (Excl' (κs:leibnizC (list Λobservation)))).

Typeclasses Opaque ownP_state ownP_obs.
Instance: Params (@ownP_state) 3.
Instance: Params (@ownP_obs) 3.

(* Adequacy *)
Theorem ownP_adequacy Σ `{ownPPreG Λ Σ} s e σ φ :
  (∀ `{ownPG Λ Σ} κs, ownP_state σ ∗ ownP_obs κs ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply (wp_adequacy Σ _).
  iIntros (? κs).
  iMod (own_alloc (● (Excl' (σ : leibnizC _)) ⋅ ◯ (Excl' σ)))
    as (γσ) "[Hσ Hσf]"; first done.
  iMod (own_alloc (● (Excl' (κs : leibnizC _)) ⋅ ◯ (Excl' κs)))
    as (γκs) "[Hκs Hκsf]"; first done.
  iModIntro. iExists (λ σ κs,
                      own γσ (● (Excl' (σ:leibnizC _))) ∗ own γκs (● (Excl' (κs:leibnizC _))))%I.
  iFrame "Hσ Hκs".
  iApply (Hwp (OwnPG _ _ _ _ _ _ γσ γκs)). rewrite /ownP_state /ownP_obs. iFrame.
Qed.

Theorem ownP_invariance Σ `{ownPPreG Λ Σ} s e σ1 t2 σ2 φ :
  (∀ `{ownPG Λ Σ} κs,
      ownP_state σ1 ∗ ownP_obs κs ={⊤}=∗ WP e @ s; ⊤ {{ _, True }} ∗
      |={⊤,∅}=> ∃ σ' κs', ownP_state σ' ∗ ownP_obs κs' ∧ ⌜φ σ'⌝) →
  rtc erased_step ([e], σ1) (t2, σ2) →
  φ σ2.
Proof.
  intros Hwp Hsteps. eapply (wp_invariance Σ Λ s e σ1 t2 σ2 _)=> //.
  iIntros (? κs κs').
  iMod (own_alloc (● (Excl' (σ1 : leibnizC _)) ⋅ ◯ (Excl' σ1)))
    as (γσ) "[Hσ Hσf]"; first done.
  iMod (own_alloc (● (Excl' (κs ++ κs' : leibnizC _)) ⋅ ◯ (Excl' (κs ++ κs'))))
    as (γκs) "[Hκs Hκsf]"; first done.
  iExists (λ σ κs',
           own γσ (● (Excl' (σ:leibnizC _))) ∗ own γκs (● (Excl' (κs':leibnizC _))))%I.
  iFrame "Hσ Hκs".
  iMod (Hwp (OwnPG _ _ _ _ _ _ γσ γκs) with "[Hσf Hκsf]") as "[$ H]";
    first by rewrite /ownP_state /ownP_obs; iFrame.
  iIntros "!> [Hσ Hκs]". iMod "H" as (σ2' κs'') "[Hσf [Hκsf %]]". rewrite/ownP_state /ownP_obs.
  iDestruct (own_valid_2 with "Hσ Hσf") as %[Hp _]%auth_valid_discrete_2.
  pose proof (Excl_included _ _ Hp) as Hp'. apply leibniz_equiv in Hp'. inversion Hp'; subst. auto.
Qed.


(** Lifting *)
Section lifting.
  Context `{ownPG Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types e : expr Λ.
  Implicit Types Φ : val Λ → iProp Σ.

  Lemma ownP_eq σ1 σ2 κs1 κs2 : state_interp σ1 κs1 -∗ ownP_state σ2 -∗ ownP_obs κs2 -∗ ⌜σ1 = σ2 ∧ κs1 = κs2⌝.
  Proof.
    iIntros "[Hσ● Hκs●] Hσ◯ Hκs◯". rewrite /ownP_state /ownP_obs.
    iDestruct (own_valid_2 with "Hσ● Hσ◯")
      as %[Hps _]%auth_valid_discrete_2.
    iDestruct (own_valid_2 with "Hκs● Hκs◯")
      as %[Hpo _]%auth_valid_discrete_2.
    pose proof (leibniz_equiv _ _ (Excl_included _ _ Hps)) as ->.
    pose proof (leibniz_equiv _ _ (Excl_included _ _ Hpo)) as ->.
    done.
  Qed.
  Lemma ownP_state_twice σ1 σ2 : ownP_state σ1 ∗ ownP_state σ2 ⊢ False.
  Proof. rewrite /ownP_state -own_op own_valid. by iIntros (?). Qed.
  Lemma ownP_obs_twice κs1 κs2 : ownP_obs κs1 ∗ ownP_obs κs2 ⊢ False.
  Proof. rewrite /ownP_obs -own_op own_valid. by iIntros (?). Qed.
  Global Instance ownP_state_timeless σ : Timeless (@ownP_state (state Λ) (observation Λ) Σ _ σ).
  Proof. rewrite /ownP_state; apply _. Qed.
  Global Instance ownP_obs_timeless κs : Timeless (@ownP_obs (state Λ) (observation Λ) Σ _ κs).
  Proof. rewrite /ownP_obs; apply _. Qed.

  Lemma ownP_lift_step s E Φ e1 :
    (|={E,∅}=> ∃ σ1 κs, ⌜if s is NotStuck then reducible e1 σ1 else to_val e1 = None⌝ ∗
      ▷ ownP_state σ1 ∗ ▷ ownP_obs κs ∗
      ▷ ∀ κ κs' e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs ∧ κs = cons_obs κ κs'⌝ -∗
      ownP_state σ2 ∗ ownP_obs κs'
            ={∅,E}=∗ WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros "H". destruct (to_val e1) as [v|] eqn:EQe1.
    - apply of_to_val in EQe1 as <-. iApply fupd_wp.
      iMod "H" as (σ1 κs) "[Hred _]"; iDestruct "Hred" as %Hred.
      destruct s; last done. apply reducible_not_val in Hred.
      move: Hred; by rewrite to_of_val.
    - iApply wp_lift_step; [done|]; iIntros (σ1 κs) "Hσκs".
      iMod "H" as (σ1' κs' ?) "[>Hσf [>Hκsf H]]". iDestruct (ownP_eq with "Hσκs Hσf Hκsf") as %[-> ->].
      iModIntro; iSplit; [by destruct s|]; iNext; iIntros (κ κs'' e2 σ2 efs [Hstep ->]).
      iDestruct "Hσκs" as "[Hσ Hκs]".
      rewrite /ownP_state /ownP_obs.
      iMod (own_update_2 with "Hσ Hσf") as "[Hσ Hσf]".
       { apply auth_update. apply: option_local_update.
         by apply: (exclusive_local_update _ (Excl σ2)). }
      iMod (own_update_2 with "Hκs Hκsf") as "[Hκs Hκsf]".
      { apply auth_update. apply: option_local_update.
        by apply: (exclusive_local_update _ (Excl (κs'':leibnizC _))). }
      iFrame "Hσ Hκs". iApply ("H" with "[]"); eauto with iFrame.
  Qed.

  Lemma ownP_lift_stuck E Φ e :
    (|={E,∅}=> ∃ σ κs, ⌜stuck e σ⌝ ∗ ▷ (ownP_state σ ∗ ownP_obs κs))
    ⊢ WP e @ E ?{{ Φ }}.
  Proof.
    iIntros "H". destruct (to_val e) as [v|] eqn:EQe.
    - apply of_to_val in EQe as <-. iApply fupd_wp.
      iMod "H" as (σ1 κs) "[H _]". iDestruct "H" as %[Hnv _]. exfalso.
      by rewrite to_of_val in Hnv.
    - iApply wp_lift_stuck; [done|]. iIntros (σ1 κs) "Hσ".
      iMod "H" as (σ1' κs') "(% & >[Hσf Hκsf])".
      by iDestruct (ownP_eq with "Hσ Hσf Hκsf") as %[-> _].
  Qed.

  Lemma ownP_lift_pure_step `{Inhabited (state Λ)} s E Φ e1 :
    (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (∀ σ1 κ e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = None ∧ σ1 = σ2) →
    (▷ ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ →
      WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep) "H"; iApply wp_lift_step.
    { specialize (Hsafe inhabitant). destruct s; last done.
      by eapply reducible_not_val. }
    iIntros (σ1 κs) "Hσ". iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
    iModIntro; iSplit; [by destruct s|]; iNext; iIntros (κ κs' e2 σ2 efs [??]).
    destruct (Hstep σ1 κ e2 σ2 efs); auto; subst.
    by iMod "Hclose"; iModIntro; iFrame; iApply "H".
  Qed.

  (** Derived lifting lemmas. *)
  Lemma ownP_lift_atomic_step {s E Φ} e1 σ1 κs :
    (if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (▷ (ownP_state σ1 ∗ ownP_obs κs) ∗
       ▷ ∀ κ κs' e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs ∧ κs = cons_obs κ κs'⌝ -∗
         ownP_state σ2 -∗ ownP_obs κs' -∗
      from_option Φ False (to_val e2) ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "[[Hσ Hκs] H]"; iApply ownP_lift_step.
    iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
    iModIntro; iExists σ1, κs; iFrame; iSplit; first by destruct s.
    iNext; iIntros (κ κs' e2 σ2 efs [??]) "[Hσ Hκs]".
    iDestruct ("H" $! κ κs' e2 σ2 efs with "[] [Hσ] [Hκs]") as "[HΦ $]"; [by eauto..|].
    destruct (to_val e2) eqn:?; last by iExFalso.
    iMod "Hclose"; iApply wp_value; last done. by apply of_to_val.
  Qed.

  Lemma ownP_lift_atomic_det_step {s E Φ e1} σ1 κ κs v2 σ2 efs :
    (if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (∀ κ' e2' σ2' efs', prim_step e1 σ1 κ' e2' σ2' efs' →
                     κ = κ' ∧ σ2 = σ2' ∧ to_val e2' = Some v2 ∧ efs = efs') →
    ▷ (ownP_state σ1 ∗ ownP_obs (cons_obs κ κs)) ∗ ▷ (ownP_state σ2 -∗ ownP_obs κs -∗
      Φ v2 ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (? Hdet) "[[Hσ1 Hκs] Hσ2]"; iApply ownP_lift_atomic_step; try done.
    iFrame; iNext; iIntros (κ' κs' e2' σ2' efs' (? & Heq)) "Hσ2' Hκs'".
    edestruct (Hdet κ') as (->&->&Hval&->); first done. rewrite Hval. apply app_inv_head in Heq as ->.
    iApply ("Hσ2" with "Hσ2' Hκs'").
  Qed.

  Lemma ownP_lift_atomic_det_step_no_fork {s E e1} σ1 κ κs v2 σ2 :
    (if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (∀ κ' e2' σ2' efs', prim_step e1 σ1 κ' e2' σ2' efs' →
      κ = κ' ∧ σ2 = σ2' ∧ to_val e2' = Some v2 ∧ [] = efs') →
    {{{ ▷ (ownP_state σ1 ∗ ownP_obs (cons_obs κ κs)) }}} e1 @ s; E {{{ RET v2; ownP_state σ2 ∗ ownP_obs κs}}}.
  Proof.
    intros. rewrite -(ownP_lift_atomic_det_step σ1 κ κs v2 σ2 []); [|done..].
    rewrite big_sepL_nil right_id. apply bi.wand_intro_r. iIntros "[Hs Hs']".
    iSplitL "Hs"; first by iFrame. iModIntro. iIntros "Hσ2 Hκs". iApply "Hs'". iFrame.
  Qed.

  Lemma ownP_lift_pure_det_step `{Inhabited (state Λ)} {s E Φ} e1 e2 efs :
    (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' → κ = None ∧ σ1 = σ2 ∧ e2 = e2' ∧ efs = efs')→
    ▷ (WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤{{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (? Hpuredet) "?"; iApply ownP_lift_pure_step=>//.
    naive_solver. by iNext; iIntros (κ e' efs' σ (->&_&->&->)%Hpuredet).
  Qed.

  Lemma ownP_lift_pure_det_step_no_fork `{Inhabited (state Λ)} {s E Φ} e1 e2 :
    (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' → κ = None ∧ σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
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
    (|={E,∅}=> ∃ σ1 κs, ⌜head_reducible e1 σ1⌝ ∗ ▷ (ownP_state σ1  ∗ ownP_obs κs) ∗
            ▷ ∀ κ κs' e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs ∧ κs = cons_obs κ κs'⌝ -∗
            ownP_state σ2 -∗ ownP_obs κs'
            ={∅,E}=∗ WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros "H". iApply ownP_lift_step.
    iMod "H" as (σ1 κs ?) "[>[Hσ1 Hκs] Hwp]". iModIntro. iExists σ1, κs. iSplit.
    { destruct s; try by eauto using reducible_not_val. }
    iFrame. iNext. iIntros (κ κs' e2 σ2 efs [? ->]) "[Hσ2 Hκs']".
    iApply ("Hwp" with "[] Hσ2"); eauto.
  Qed.

  Lemma ownP_lift_head_stuck E Φ e :
    sub_redexes_are_values e →
    (|={E,∅}=> ∃ σ κs, ⌜head_stuck e σ⌝ ∗ ▷ (ownP_state σ ∗ ownP_obs κs))
    ⊢ WP e @ E ?{{ Φ }}.
  Proof.
    iIntros (?) "H". iApply ownP_lift_stuck. iMod "H" as (σ κs) "[% >[Hσ Hκs]]".
    iExists σ, κs. iModIntro. by auto with iFrame.
  Qed.

  Lemma ownP_lift_pure_head_step s E Φ e1 :
    (∀ σ1, head_reducible e1 σ1) →
    (∀ σ1 κ e2 σ2 efs, head_step e1 σ1 κ e2 σ2 efs → κ = None ∧ σ1 = σ2) →
    (▷ ∀ κ e2 efs σ, ⌜head_step e1 σ κ e2 σ efs⌝ →
      WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof using Hinh.
    iIntros (??) "H".  iApply ownP_lift_pure_step; eauto.
    { by destruct s; auto. }
    iNext. iIntros (?????). iApply "H"; eauto.
  Qed.

  Lemma ownP_lift_atomic_head_step {s E Φ} e1 σ1 κs :
    head_reducible e1 σ1 →
    ▷ (ownP_state σ1 ∗ ownP_obs κs) ∗ ▷ (∀ κ κs' e2 σ2 efs,
    ⌜head_step e1 σ1 κ e2 σ2 efs ∧ κs = cons_obs κ κs'⌝ -∗ ownP_state σ2 -∗ ownP_obs κs' -∗
      from_option Φ False (to_val e2) ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "[Hst H]". iApply ownP_lift_atomic_step; eauto.
    { by destruct s; eauto using reducible_not_val. }
    iSplitL "Hst"; first done.
    iNext. iIntros (????? [? ->]) "Hσ ?". iApply ("H" with "[] Hσ"); eauto.
  Qed.

  Lemma ownP_lift_atomic_det_head_step {s E Φ e1} σ1 κ κs v2 σ2 efs :
    head_reducible e1 σ1 →
    (∀ κ' e2' σ2' efs', head_step e1 σ1 κ' e2' σ2' efs' →
      κ = κ' ∧ σ2 = σ2' ∧ to_val e2' = Some v2 ∧ efs = efs') →
    ▷ (ownP_state σ1 ∗ ownP_obs (cons_obs κ κs)) ∗ ▷ (ownP_state σ2 -∗ ownP_obs κs -∗
                                                    Φ v2 ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    intros Hr Hs. destruct s; apply ownP_lift_atomic_det_step; eauto using reducible_not_val.
  Qed.

  Lemma ownP_lift_atomic_det_head_step_no_fork {s E e1} σ1 κ κs v2 σ2 :
    head_reducible e1 σ1 →
    (∀ κ' e2' σ2' efs', head_step e1 σ1 κ' e2' σ2' efs' →
      κ = κ' ∧ σ2 = σ2' ∧ to_val e2' = Some v2 ∧ [] = efs') →
    {{{ ▷ (ownP_state σ1 ∗ ownP_obs (cons_obs κ κs)) }}} e1 @ s; E {{{ RET v2; ownP_state σ2 ∗ ownP_obs κs }}}.
  Proof.
    intros ???; apply ownP_lift_atomic_det_step_no_fork; last naive_solver.
    by destruct s; eauto using reducible_not_val.
  Qed.

  Lemma ownP_lift_pure_det_head_step {s E Φ} e1 e2 efs :
    (∀ σ1, head_reducible e1 σ1) →
    (∀ σ1 κ e2' σ2 efs', head_step e1 σ1 κ e2' σ2 efs' → κ = None ∧ σ1 = σ2 ∧ e2 = e2' ∧ efs = efs') →
    ▷ (WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof using Hinh.
    iIntros (??) "H"; iApply wp_lift_pure_det_step; eauto.
    by destruct s; eauto using reducible_not_val.
  Qed.

  Lemma ownP_lift_pure_det_head_step_no_fork {s E Φ} e1 e2 :
    (∀ σ1, head_reducible e1 σ1) →
    (∀ σ1 κ e2' σ2 efs', head_step e1 σ1 κ e2' σ2 efs' → κ = None ∧ σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
    ▷ WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
  Proof using Hinh.
    iIntros (??) "H". iApply ownP_lift_pure_det_step_no_fork; eauto.
    by destruct s; eauto using reducible_not_val.
  Qed.
End ectx_lifting.
