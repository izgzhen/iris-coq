From iris.base_logic.lib Require Export own.
From stdpp Require Export coPset.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Export invG.
Import uPred.

Definition uPred_fupd_def `{invG Σ} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  (wsat ∗ ownE E1 ==∗ ◇ (wsat ∗ ownE E2 ∗ P))%I.
Definition uPred_fupd_aux `{invG Σ} : seal uPred_fupd_def. by eexists. Qed.
Definition uPred_fupd `{invG Σ} : FUpd (iProp Σ):= uPred_fupd_aux.(unseal).
Definition uPred_fupd_eq `{invG Σ} : @fupd _ uPred_fupd = uPred_fupd_def :=
  uPred_fupd_aux.(seal_eq).

Lemma uPred_fupd_mixin `{invG Σ} : BiFUpdMixin (uPredSI (iResUR Σ)) uPred_fupd.
Proof.
  split.
  - rewrite uPred_fupd_eq. solve_proper.
  - intros E1 E2 P (E1''&->&?)%subseteq_disjoint_union_L.
    rewrite uPred_fupd_eq /uPred_fupd_def ownE_op //.
    by iIntros "$ ($ & $ & HE) !> !> [$ $] !> !>" .
  - rewrite uPred_fupd_eq. iIntros (E1 E2 P) ">H [Hw HE]". iApply "H"; by iFrame.
  - rewrite uPred_fupd_eq. iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
  - rewrite uPred_fupd_eq. iIntros (E1 E2 E3 P) "HP HwE".
    iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
  - intros E1 E2 Ef P HE1Ef. rewrite uPred_fupd_eq /uPred_fupd_def ownE_op //.
    iIntros "Hvs (Hw & HE1 &HEf)".
    iMod ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
    iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
    iIntros "!> !>". by iApply "HP".
  - rewrite uPred_fupd_eq /uPred_fupd_def. by iIntros (????) "[HwP $]".
Qed.
Instance uPred_bi_fupd `{invG Σ} : BiFUpd (uPredSI (iResUR Σ)) :=
  {| bi_fupd_mixin := uPred_fupd_mixin |}.

Instance uPred_bi_bupd_fupd `{invG Σ} : BiBUpdFUpd (uPredSI (iResUR Σ)).
Proof. rewrite /BiBUpdFUpd uPred_fupd_eq. by iIntros (E P) ">? [$ $] !> !>". Qed.

Instance uPred_bi_fupd_plainly `{invG Σ} : BiFUpdPlainly (uPredSI (iResUR Σ)).
Proof.
  split.
  - iIntros (E1 E2 E2' P Q ? (E3&->&HE)%subseteq_disjoint_union_L) "HQP HQ".
    rewrite uPred_fupd_eq /uPred_fupd_def ownE_op //. iIntros "H".
    iMod ("HQ" with "H") as ">(Hws & [HE1 HE3] & HQ)"; iModIntro.
    iAssert (◇ P)%I as "#HP".
    { by iMod ("HQP" with "HQ [$]") as "(_ & _ & HP)". }
    iMod "HP". iFrame. auto.
  - rewrite uPred_fupd_eq /uPred_fupd_def. iIntros (E P ?) "HP [Hw HE]".
    iAssert (▷ ◇ P)%I with "[-]" as "#$"; last by iFrame.
    iNext. by iMod ("HP" with "[$]") as "(_ & _ & HP)".
Qed.