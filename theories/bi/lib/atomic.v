From iris.bi Require Export bi updates.
From iris.bi.lib Require Import fixpoint laterable.
From stdpp Require Import coPset.
From iris.proofmode Require Import coq_tactics tactics.
Set Default Proof Using "Type".

Section definition.
  Context `{BiFUpd PROP} {A B : Type}.
  Implicit Types
    (Eo Em : coPset) (* outside/module masks *)
    (α : A → PROP) (* atomic pre-condition *)
    (P : PROP) (* abortion condition *)
    (β : A → B → PROP) (* atomic post-condition *)
    (Φ : A → B → PROP) (* post-condition *)
  .

(** atomic_step as the "introduction form" of atomic updates *)
  Definition atomic_step Eo Em α P β Φ : PROP :=
    (|={Eo, Eo∖Em}=> ∃ x, α x ∗
          ((α x ={Eo∖Em, Eo}=∗ P) ∧ (∀ y, β x y ={Eo∖Em, Eo}=∗ Φ x y))
    )%I.

  Lemma atomic_shift_mono Eo Em α P1 P2 β Φ :
    □ (P1 -∗ P2) -∗
    □ (atomic_step Eo Em α P1 β Φ -∗ atomic_step Eo Em α P2 β Φ).
  Proof.
    iIntros "#HP12 !# AS". iMod "AS" as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα". iSplit.
    - iIntros "Hα". iDestruct "Hclose" as "[Hclose _]".
      iApply "HP12". iApply "Hclose". done.
    - iIntros (y) "Hβ". iDestruct "Hclose" as "[_ Hclose]".
      iApply "Hclose". done.
  Qed.

(** atomic_update as a fixed-point of the equation
   AU = ∃ P. ▷ P ∗ □ (▷ P ==∗ α ∗ (α ==∗ AU) ∧ (β ==∗ Q))
 *)
  Context Eo Em α β Φ.

  Definition atomic_update_pre (Ψ : () → PROP) (_ : ()) : PROP :=
    (∃ (P : PROP), ▷ P ∗
     □ (∀ E, ⌜Eo ⊆ E⌝ → (▷ P) -∗ atomic_step E Em α (Ψ ()) β Φ))%I.

  Local Instance atomic_update_pre_mono : BiMonoPred atomic_update_pre.
  Proof.
    constructor.
    - iIntros (P1 P2) "#HP12". iIntros ([]) "AU".
      iDestruct "AU" as (P) "[HP #AS]". iExists P. iFrame.
      iIntros "!# * % HP". iApply (atomic_shift_mono with "HP12").
      iApply ("AS" with "[%]"); done.
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
  Implicit Types (α : A → PROP) (β: A → B → PROP) (P : PROP) (Φ : A → B → PROP).

  Local Existing Instance atomic_update_pre_mono.

  Global Instance atomic_step_ne Eo Em n :
    Proper (
        pointwise_relation A (dist n) ==>
        dist n ==>
        pointwise_relation A (pointwise_relation B (dist n)) ==>
        pointwise_relation A (pointwise_relation B (dist n)) ==>
        dist n
    ) (atomic_step (PROP:=PROP) Eo Em).
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
    atomic_step E Em α (atomic_update Eo Em α β Φ) β Φ.
  Proof using Type*.
    rewrite atomic_update_eq {1}/atomic_update_def /=. iIntros (HE) "HUpd".
    iPoseProof (greatest_fixpoint_unfold_1 with "HUpd") as "HUpd".
    iDestruct "HUpd" as (P) "(HP & Hshift)".
    iMod ("Hshift" with "[% //] HP") as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame.
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
    Em ⊆ Eo → Affine P → Persistent P → Laterable Q →
    (P ∗ Q -∗ atomic_step Eo Em α Q β Φ) →
    P ∗ Q -∗ atomic_update Eo Em α β Φ.
  Proof.
    rewrite atomic_update_eq {1}/atomic_update_def /=.
    iIntros (???? HAU) "[#HP HQ]".
    iApply (greatest_fixpoint_coind _ (λ _, Q)); last done. iIntros "!#" ([]) "HQ".
    iDestruct (laterable with "HQ") as (Q') "[HQ' #HQi]". iExists Q'. iFrame.
    iIntros "!#" (E HE) "HQ'". iDestruct ("HQi" with "HQ'") as ">HQ {HQi}".
    iApply fupd_mask_frame_diff_open; last
      iMod (HAU with "[$HQ]") as (x) "[Hα Hclose]"; [done..|].
    iModIntro. iExists x. iFrame. iSplit.
    - iDestruct "Hclose" as "[Hclose _]". iIntros "Hα".
      iApply fupd_mask_frame_diff_close; last (by iApply "Hclose"); done.
    - iDestruct "Hclose" as "[_ Hclose]". iIntros (y) "Hβ".
      iApply fupd_mask_frame_diff_close; last (by iApply "Hclose"); done.
  Qed.
End lemmas.

(** ProofMode support for atomic updates *)

Section proof_mode.
  Context `{BiFUpd PROP} {A B : Type}.
  Implicit Types (α : A → PROP) (β: A → B → PROP) (P : PROP) (Φ : A → B → PROP).

  Lemma tac_aupd_intro Γp Γs n α β Eo Em Φ P :
    Em ⊆ Eo →
    Timeless (PROP:=PROP) emp →
    TCForall Laterable (env_to_list Γs) →
    P = prop_of_env Γs →
    envs_entails (Envs Γp Γs n) (atomic_step Eo Em α P β Φ) →
    envs_entails (Envs Γp Γs n) (atomic_update Eo Em α β Φ).
  Proof.
    intros ?? HΓs ->. rewrite envs_entails_eq of_envs_eq' /atomic_step /=.
    setoid_rewrite prop_of_env_sound =>HAU.
    apply aupd_intro; [done|apply _..|]. done.
  Qed. 
End proof_mode.

(** Now the coq-level tactics *)

Tactic Notation "iAuIntro" :=
  iStartProof; eapply tac_aupd_intro; [
    (* Em ⊆ Eo: to be proven by user *)
  | iSolveTC || fail "iAuIntro: emp is not timeless"
  | iSolveTC || fail "Not all spatial assumptions are laterable"
  | (* P = ...: make the P pretty *) env_reflexivity
  | (* the new proof mode goal *) ].
