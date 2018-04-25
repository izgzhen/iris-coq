From iris.bi Require Export bi updates.
From iris.bi.lib Require Import fixpoint laterable.
From stdpp Require Import coPset.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

(** atomic_update as a fixed-point of the equation
   AU = ∃ P. ▷ P ∗ □ (▷ P ==∗ α ∗ (α ==∗ AU) ∧ (β ==∗ Q))
 *)
Section definition.
  Context `{BiFUpd PROP} {A B : Type}
    (α : A → PROP) (* atomic pre-condition *)
    (β : A → B → PROP) (* atomic post-condition *)
    (Eo Em : coPset) (* outside/module masks *)
    (Φ : A → B → PROP) (* post-condition *)
  .

  Definition atomic_shift (P P' : PROP) : PROP :=
    (□ (∀ E, ⌜Eo ⊆ E⌝ → P ={E, E∖Em}=∗ ∃ x, α x ∗
          ((α x ={E∖Em, E}=∗ P') ∧ (∀ y, β x y ={E∖Em, E}=∗ Φ x y)))
    )%I.

  Lemma atomic_shift_mono P P1 P2:
    □ (P1 -∗ P2) -∗ □ (atomic_shift P P1 -∗ atomic_shift P P2).
  Proof.
    iIntros "#HP12 !# #AS !# * % HP".
    iMod ("AS" with "[% //] HP") as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα". iSplit.
    - iIntros "Hα". iDestruct "Hclose" as "[Hclose _]".
      iApply "HP12". iApply "Hclose". done.
    - iIntros (y) "Hβ". iDestruct "Hclose" as "[_ Hclose]".
      iApply "Hclose". done.
  Qed.

  Definition atomic_update_pre (Ψ : () → PROP) (_ : ()) : PROP :=
    (∃ (P : PROP), ▷ P ∗ atomic_shift (▷ P) (Ψ ()))%I.

  Local Instance atomic_update_pre_mono : BiMonoPred atomic_update_pre.
  Proof.
    constructor.
    - iIntros (P1 P2) "#HP12". iIntros ([]) "AU".
      iDestruct "AU" as (P) "[HP AS]". iExists P. iFrame.
      iApply (atomic_shift_mono with "[HP12]"); last done.
      iAlways. iApply "HP12".
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

  (** The ellimination form: an accessor *)
  Lemma aupd_acc α β Eo Em Φ E :
    Eo ⊆ E →
    atomic_update α β Eo Em Φ -∗
    |={E, E∖Em}=> ∃ x, α x ∗
      ((α x ={E∖Em, E}=∗ atomic_update α β Eo Em Φ) ∧
       (∀ y, β x y ={E∖Em, E}=∗ Φ x y)).
  Proof using Type*.
    rewrite atomic_update_eq {1}/atomic_update_def /=. iIntros (HE) "HUpd".
    iPoseProof (greatest_fixpoint_unfold_1 with "HUpd") as "HUpd".
    iDestruct "HUpd" as (P) "(HP & Hshift)".
    iMod ("Hshift" with "[% //] HP") as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame.
  Qed.

  Global Instance aupd_laterable α β Eo Em Φ :
    Laterable (atomic_update α β Eo Em Φ).
  Proof.
    rewrite /Laterable atomic_update_eq {1}/atomic_update_def /=. iIntros "AU".
    iPoseProof (greatest_fixpoint_unfold_1 with "AU") as (P) "[HP #AS]".
    iExists P. iFrame. iIntros "!# HP !>".
    iApply greatest_fixpoint_unfold_2. iExists P. iFrame "#∗".
  Qed.

  Lemma aupd_intro P α β Eo Em Φ :
    Em ⊆ Eo → Laterable P →
    P -∗
    □ (P -∗ |={Eo, Eo∖Em}=> ∃ x, α x ∗
      ((α x ={Eo∖Em, Eo}=∗ P) ∧ (∀ y, β x y ={Eo∖Em, Eo}=∗ Φ x y))) -∗
    atomic_update α β Eo Em Φ.
  Proof.
    rewrite atomic_update_eq {1}/atomic_update_def /=.
    iIntros (??) "HP #AU".
    iApply (greatest_fixpoint_coind _ (λ _, P)); last done. iIntros "!#" ([]) "HP".
    iDestruct (laterable with "HP") as (P') "[HP' #HPi]". iExists P'. iFrame.
    iIntros "!#" (E HE) "HP'". iDestruct ("HPi" with "HP'") as ">HP {HPi}".
    iApply fupd_mask_frame_diff_open; last
      iMod ("AU" with "HP") as (x) "[Hα Hclose] {AU}"; [done..|].
    iModIntro. iExists x. iFrame. iSplit.
    - iDestruct "Hclose" as "[Hclose _]". iIntros "Hα".
      iApply fupd_mask_frame_diff_close; last (by iApply "Hclose"); done.
    - iDestruct "Hclose" as "[_ Hclose]". iIntros (y) "Hβ".
      iApply fupd_mask_frame_diff_close; last (by iApply "Hclose"); done.
  Qed.
End lemmas.
