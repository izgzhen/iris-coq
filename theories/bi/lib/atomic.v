From iris.bi Require Export bi updates.
From iris.bi.lib Require Import fixpoint laterable.
From stdpp Require Import coPset namespaces.
From iris.proofmode Require Import coq_tactics tactics.
Set Default Proof Using "Type".

(** Conveniently split a conjunction on both assumption and conclusion. *)
Local Tactic Notation "iSplitWith" constr(H) :=
  iApply (bi.and_parallel with H); iSplit; iIntros H.

Section definition.
  Context `{BiFUpd PROP} {A B : Type}.
  Implicit Types
    (Eo Em Ei : coPset) (* outside/module/inner masks *)
    (α : A → PROP) (* atomic pre-condition *)
    (P : PROP) (* abortion condition *)
    (β : A → B → PROP) (* atomic post-condition *)
    (Φ : A → B → PROP) (* post-condition *)
  .

  (** atomic_acc as the "introduction form" of atomic updates: An accessor
      that can be aborted back to [P]. *)
  Definition atomic_acc Eo Ei α P β Φ : PROP :=
    (|={Eo, Ei}=> ∃ x, α x ∗
          ((α x ={Ei, Eo}=∗ P) ∧ (∀ y, β x y ={Ei, Eo}=∗ Φ x y))
    )%I.

  Lemma atomic_acc_wand Eo Ei α P1 P2 β Φ1 Φ2 :
    ((P1 -∗ P2) ∧ (∀ x y, Φ1 x y -∗ Φ2 x y)) -∗
    (atomic_acc Eo Ei α P1 β Φ1 -∗ atomic_acc Eo Ei α P2 β Φ2).
  Proof.
    iIntros "HP12 AS". iMod "AS" as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα". iSplit.
    - iIntros "Hα". iDestruct "Hclose" as "[Hclose _]".
      iApply "HP12". iApply "Hclose". done.
    - iIntros (y) "Hβ". iDestruct "Hclose" as "[_ Hclose]".
      iApply "HP12". iApply "Hclose". done.
  Qed.

  Lemma atomic_acc_mask Eo Em α P β Φ :
    atomic_acc Eo (Eo∖Em) α P β Φ ⊣⊢ ∀ E, ⌜Eo ⊆ E⌝ → atomic_acc E (E∖Em) α P β Φ.
  Proof.
    iSplit; last first.
    { iIntros "Hstep". iApply ("Hstep" with "[% //]"). }
    iIntros "Hstep" (E HE).
    iApply (fupd_mask_frame_acc with "Hstep"); first done.
    iIntros "Hstep". iDestruct "Hstep" as (x) "[Hα Hclose]".
    iIntros "!> Hclose'".
    iExists x. iFrame. iSplitWith "Hclose".
    - iIntros "Hα". iApply "Hclose'". iApply "Hclose". done.
    - iIntros (y) "Hβ". iApply "Hclose'". iApply "Hclose". done.
  Qed.

  (** atomic_update as a fixed-point of the equation
   AU = ∃ P. ▷ P ∗ □ (▷ P ==∗ α ∗ (α ==∗ AU) ∧ (β ==∗ Q))
      = ∃ P. ▷ P ∗ □ (▷ P -∗ atomic_acc α AU β Q)
  *)
  Context Eo Em α β Φ.

  Definition atomic_update_pre (Ψ : () → PROP) (_ : ()) : PROP :=
    (∃ (P : PROP), ▷ P ∗
     □ (▷ P -∗ atomic_acc Eo (Eo∖Em) α (Ψ ()) β Φ))%I.

  Local Instance atomic_update_pre_mono : BiMonoPred atomic_update_pre.
  Proof.
    constructor.
    - iIntros (P1 P2) "#HP12". iIntros ([]) "AU".
      iDestruct "AU" as (P) "[HP #AS]". iExists P. iFrame.
      iIntros "!# HP". iApply (atomic_acc_wand with "[HP12]"); last by iApply "AS".
      iSplit; last by eauto. iApply "HP12".
    - intros ??. solve_proper.
  Qed.

  Definition atomic_update_def :=
    bi_greatest_fixpoint atomic_update_pre ().

End definition.

(** Seal it *)
Definition atomic_update_aux : seal (@atomic_update_def). by eexists. Qed.
Definition atomic_update `{BiFUpd PROP} {A B : Type} := atomic_update_aux.(unseal) PROP _ A B.
Definition atomic_update_eq :
  @atomic_update = @atomic_update_def := atomic_update_aux.(seal_eq).

(** Lemmas about AU *)
Section lemmas.
  Context `{BiFUpd PROP} {A B : Type}.
  Implicit Types (α : A → PROP) (β Φ : A → B → PROP) (P : PROP).

  Local Existing Instance atomic_update_pre_mono.

  Global Instance atomic_acc_ne Eo Em n :
    Proper (
        pointwise_relation A (dist n) ==>
        dist n ==>
        pointwise_relation A (pointwise_relation B (dist n)) ==>
        pointwise_relation A (pointwise_relation B (dist n)) ==>
        dist n
    ) (atomic_acc (PROP:=PROP) Eo Em).
  Proof. solve_proper. Qed.

  Global Instance atomic_update_ne Eo Em n :
    Proper (
        pointwise_relation A (dist n) ==>
        pointwise_relation A (pointwise_relation B (dist n)) ==>
        pointwise_relation A (pointwise_relation B (dist n)) ==>
        dist n
    ) (atomic_update (PROP:=PROP) Eo Em).
  Proof.
    rewrite atomic_update_eq /atomic_update_def /atomic_update_pre. solve_proper.
  Qed.

  (** The ellimination form: an accessor *)
  Lemma aupd_acc  Eo Em E α β Φ :
    Eo ⊆ E →
    atomic_update Eo Em α β Φ -∗
    atomic_acc E (E∖Em) α (atomic_update Eo Em α β Φ) β Φ.
  Proof using Type*.
    rewrite atomic_update_eq {1}/atomic_update_def /=. iIntros (HE) "HUpd".
    iPoseProof (greatest_fixpoint_unfold_1 with "HUpd") as "HUpd".
    iDestruct "HUpd" as (P) "(HP & Hshift)".
    iRevert (E HE). iApply atomic_acc_mask.
    iApply "Hshift". done.
  Qed.

  Global Instance aupd_laterable Eo Em α β Φ :
    Laterable (atomic_update Eo Em α β Φ).
  Proof.
    rewrite /Laterable atomic_update_eq {1}/atomic_update_def /=. iIntros "AU".
    iPoseProof (greatest_fixpoint_unfold_1 with "AU") as (P) "[HP #AS]".
    iExists P. iFrame. iIntros "!# HP !>".
    iApply greatest_fixpoint_unfold_2. iExists P. iFrame "#∗".
  Qed.

  Lemma aupd_intro P Q α β Eo Em Φ :
    Affine P → Persistent P → Laterable Q →
    (P ∗ Q -∗ atomic_acc Eo (Eo∖Em) α Q β Φ) →
    P ∗ Q -∗ atomic_update Eo Em α β Φ.
  Proof.
    rewrite atomic_update_eq {1}/atomic_update_def /=.
    iIntros (??? HAU) "[#HP HQ]".
    iApply (greatest_fixpoint_coind _ (λ _, Q)); last done. iIntros "!#" ([]) "HQ".
    iDestruct (laterable with "HQ") as (Q') "[HQ' #HQi]". iExists Q'. iFrame.
    iIntros "!# HQ'". iDestruct ("HQi" with "HQ'") as ">HQ {HQi}".
    iApply HAU. by iFrame.
  Qed.

  Lemma aacc_intro x Eo Ei α P β Φ :
    Ei ⊆ Eo → α x -∗
    ((α x ={Eo}=∗ P) ∧ (∀ y, β x y ={Eo}=∗ Φ x y)) -∗
    atomic_acc Eo Ei α P β Φ.
  Proof.
    iIntros (?) "Hα Hclose".
    iMod fupd_intro_mask' as "Hclose'"; last iModIntro; first set_solver.
    iExists x. iFrame. iSplitWith "Hclose".
    - iIntros "Hα". iMod "Hclose'" as "_". iApply "Hclose". done.
    - iIntros (y) "Hβ". iMod "Hclose'" as "_". iApply "Hclose". done.
  Qed.

  Global Instance elim_acc_aacc {X} E1 E2 Ei (α' β' : X → PROP) γ' α β Pas Φ :
    ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1) α' β' γ'
            (atomic_acc E1 Ei α Pas β Φ)
            (λ x', atomic_acc E2 Ei α (β' x' ∗ coq_tactics.maybe_wand (γ' x') Pas)%I β
                (λ x y, β' x' ∗ coq_tactics.maybe_wand (γ' x') (Φ x y)))%I.
  Proof.
    rewrite /ElimAcc.
    (* FIXME: Is there any way to prevent maybe_wand from unfolding?
       It gets unfolded by env_cbv in the proofmode, ideally we'd like that
       to happen only if one argument is a constructor. *)
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x') "[Hα' Hclose]".
    iMod ("Hinner" with "Hα'") as (x) "[Hα Hclose']".
    iMod (fupd_intro_mask') as "Hclose''"; last iModIntro; first done.
    iExists x. iFrame. iSplitWith "Hclose'".
    - iIntros "Hα". iMod "Hclose''" as "_".
      iMod ("Hclose'" with "Hα") as "[Hβ' HPas]".
      iMod ("Hclose" with "Hβ'") as "Hγ'".
      iModIntro. destruct (γ' x'); iApply "HPas"; done.
    - iIntros (y) "Hβ". iMod "Hclose''" as "_".
      iMod ("Hclose'" with "Hβ") as "[Hβ' HΦ]".
      iMod ("Hclose" with "Hβ'") as "Hγ'".
      iModIntro. destruct (γ' x'); iApply "HΦ"; done.
  Qed.

  Lemma aacc_aacc {A' B'} E1 E2 E3
        α P β Φ
        (α' : A' → PROP) P' (β' Φ' : A' → B' → PROP) :
    atomic_acc E1 E2 α P β Φ -∗
    (∀ x, α x -∗ atomic_acc E2 E3 α' (α x ∗ (P ={E1}=∗ P')) β'
            (λ x' y', (α x ∗ (P ={E1}=∗ Φ' x' y'))
                    ∨ ∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    atomic_acc E1 E3 α' P' β' Φ'.
  Proof.
    iIntros "Hupd Hstep". iMod ("Hupd") as (x) "[Hα Hclose]".
    iMod ("Hstep" with "Hα") as (x') "[Hα' Hclose']".
    iModIntro. iExists x'. iFrame "Hα'". iSplit.
    - iIntros "Hα'". iDestruct "Hclose'" as "[Hclose' _]".
      iMod ("Hclose'" with "Hα'") as "[Hα Hupd]".
      iDestruct "Hclose" as "[Hclose _]".
      iMod ("Hclose" with "Hα"). iApply "Hupd". auto.
    - iIntros (y') "Hβ'". iDestruct "Hclose'" as "[_ Hclose']".
      iMod ("Hclose'" with "Hβ'") as "[[Hα HΦ']|Hcont]".
      + (* Abort the step we are eliminating *)
        iDestruct "Hclose" as "[Hclose _]".
        iMod ("Hclose" with "Hα") as "HP".
        iApply "HΦ'". done.
      + (* Complete the step we are eliminating *)
        iDestruct "Hclose" as "[_ Hclose]".
        iDestruct "Hcont" as (y) "[Hβ HΦ']".
        iMod ("Hclose" with "Hβ") as "HΦ".
        iApply "HΦ'". done.
  Qed.

  Lemma aacc_aupd {A' B'} E1 E2 Eo Em
        α β Φ
        (α' : A' → PROP) P' (β' Φ' : A' → B' → PROP) :
    Eo ⊆ E1 →
    atomic_update Eo Em α β Φ -∗
    (∀ x, α x -∗ atomic_acc (E1∖Em) E2 α' (α x ∗ (atomic_update Eo Em α β Φ ={E1}=∗ P')) β'
            (λ x' y', (α x ∗ (atomic_update Eo Em α β Φ ={E1}=∗ Φ' x' y'))
                    ∨ ∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    atomic_acc E1 E2 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aacc_aacc with "[Hupd] Hstep").
    iApply aupd_acc; done.
  Qed.

  Lemma aacc_aupd_commit {A' B'} E1 E2 Eo Em
        α β Φ
        (α' : A' → PROP) P' (β' Φ' : A' → B' → PROP) :
    Eo ⊆ E1 →
    atomic_update Eo Em α β Φ -∗
    (∀ x, α x -∗ atomic_acc (E1∖Em) E2 α' (α x ∗ (atomic_update Eo Em α β Φ ={E1}=∗ P')) β'
            (λ x' y', ∃ y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    atomic_acc E1 E2 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aacc_aupd with "Hupd"); first done.
    iIntros (x) "Hα". iApply atomic_acc_wand; last first.
    { iApply "Hstep". done. }
    iSplit; first by eauto. iIntros (??) "?". by iRight.
  Qed.

  Lemma aacc_aupd_abort {A' B'} E1 E2 Eo Em
        α β Φ
        (α' : A' → PROP) P' (β' Φ' : A' → B' → PROP) :
    Eo ⊆ E1 →
    atomic_update Eo Em α β Φ -∗
    (∀ x, α x -∗ atomic_acc (E1∖Em) E2 α' (α x ∗ (atomic_update Eo Em α β Φ ={E1}=∗ P')) β'
            (λ x' y', α x ∗ (atomic_update Eo Em α β Φ ={E1}=∗ Φ' x' y'))) -∗
    atomic_acc E1 E2 α' P' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep". iApply (aacc_aupd with "Hupd"); first done.
    iIntros (x) "Hα". iApply atomic_acc_wand; last first.
    { iApply "Hstep". done. }
    iSplit; first by eauto. iIntros (??) "?". by iLeft.
  Qed.

End lemmas.

(** ProofMode support for atomic updates *)

Section proof_mode.
  Context `{BiFUpd PROP} {A B : Type}.
  Implicit Types (α : A → PROP) (β Φ : A → B → PROP) (P : PROP).

  Lemma tac_aupd_intro Γp Γs n α β Eo Em Φ P :
    Timeless (PROP:=PROP) emp →
    TCForall Laterable (env_to_list Γs) →
    P = prop_of_env Γs →
    envs_entails (Envs Γp Γs n) (atomic_acc Eo (Eo∖Em) α P β Φ) →
    envs_entails (Envs Γp Γs n) (atomic_update Eo Em α β Φ).
  Proof.
    intros ? HΓs ->. rewrite envs_entails_eq of_envs_eq' /atomic_acc /=.
    setoid_rewrite prop_of_env_sound =>HAU.
    apply aupd_intro; [apply _..|]. done.
  Qed.
End proof_mode.

(** Now the coq-level tactics *)

Tactic Notation "iAuIntro" :=
  iStartProof; eapply tac_aupd_intro; [
    iSolveTC || fail "iAuIntro: emp is not timeless"
  | iSolveTC || fail "iAuIntro: not all spatial assumptions are laterable"
  | (* P = ...: make the P pretty *) env_reflexivity
  | (* the new proof mode goal *) ].
