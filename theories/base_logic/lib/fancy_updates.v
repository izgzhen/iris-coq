From iris.base_logic.lib Require Export own.
From stdpp Require Export coPset.
From iris.base_logic.lib Require Import wsat.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics classes.
Set Default Proof Using "Type".
Export invG.
Import uPred.

Definition uPred_fupd_def `{invG Σ} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  (wsat ∗ ownE E1 ==∗ ◇ (wsat ∗ ownE E2 ∗ P))%I.
Definition uPred_fupd_aux `{invG Σ} : seal uPred_fupd_def. by eexists. Qed.
Instance uPred_fupd `{invG Σ} : FUpd (iProp Σ):= unseal uPred_fupd_aux.
Definition uPred_fupd_eq `{invG Σ} : fupd = uPred_fupd_def := seal_eq uPred_fupd_aux.

Section fupd.
Context `{invG Σ}.
Implicit Types P Q : iProp Σ.

Global Instance fupd_ne E1 E2 : NonExpansive (fupd E1 E2).
Proof. rewrite uPred_fupd_eq. solve_proper. Qed.
Global Instance fupd_proper E1 E2 : Proper ((≡) ==> (≡)) (fupd E1 E2).
Proof. apply ne_proper, _. Qed.

Lemma fupd_intro_mask E1 E2 P : E2 ⊆ E1 → P ⊢ |={E1,E2}=> |={E2,E1}=> P.
Proof.
  intros (E1''&->&?)%subseteq_disjoint_union_L.
  rewrite uPred_fupd_eq /uPred_fupd_def ownE_op //.
  by iIntros "$ ($ & $ & HE) !> !> [$ $] !> !>" .
Qed.

Lemma except_0_fupd E1 E2 P : ◇ (|={E1,E2}=> P) ={E1,E2}=∗ P.
Proof. rewrite uPred_fupd_eq. iIntros ">H [Hw HE]". iApply "H"; by iFrame. Qed.

Lemma bupd_fupd E P : (|==> P) ={E}=∗ P.
Proof. rewrite uPred_fupd_eq. by iIntros ">? [$ $] !> !>". Qed.

Lemma fupd_mono E1 E2 P Q : (P ⊢ Q) → (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q.
Proof.
  rewrite uPred_fupd_eq. iIntros (HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
Qed.

Lemma fupd_trans E1 E2 E3 P : (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P.
Proof.
  rewrite uPred_fupd_eq. iIntros "HP HwE".
  iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
Qed.

Lemma fupd_mask_frame_r' E1 E2 Ef P :
  E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ={E1 ∪ Ef,E2 ∪ Ef}=∗ P.
Proof.
  intros. rewrite uPred_fupd_eq /uPred_fupd_def ownE_op //.
  iIntros "Hvs (Hw & HE1 &HEf)".
  iMod ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
  iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
  iIntros "!> !>". by iApply "HP".
Qed.

Lemma fupd_frame_r E1 E2 P Q : (|={E1,E2}=> P) ∗ Q ={E1,E2}=∗ P ∗ Q.
Proof. rewrite uPred_fupd_eq /uPred_fupd_def. by iIntros "[HwP $]". Qed.

Lemma fupd_plain' E1 E2 E2' P Q `{!Plain P} :
  E1 ⊆ E2 →
  (Q ={E1, E2'}=∗ P) -∗ (|={E1, E2}=> Q) ={E1}=∗ (|={E1, E2}=> Q) ∗ P.
Proof.
  iIntros ((E3&->&HE)%subseteq_disjoint_union_L) "HQP HQ".
  rewrite uPred_fupd_eq /uPred_fupd_def ownE_op //. iIntros "H".
  iMod ("HQ" with "H") as ">(Hws & [HE1 HE3] & HQ)"; iModIntro.
  iAssert (◇ P)%I as "#HP".
  { by iMod ("HQP" with "HQ [$]") as "(_ & _ & HP)". }
  iMod "HP". iFrame. auto.
Qed.

Lemma later_fupd_plain E P `{!Plain P} : (▷ |={E}=> P) ={E}=∗ ▷ ◇ P.
Proof.
  rewrite uPred_fupd_eq /uPred_fupd_def. iIntros "HP [Hw HE]".
  iAssert (▷ ◇ P)%I with "[-]" as "#$"; last by iFrame.
  iNext. by iMod ("HP" with "[$]") as "(_ & _ & HP)".
Qed.

(** * Derived rules *)
Global Instance fupd_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (fupd E1 E2).
Proof. intros P Q; apply fupd_mono. Qed.
Global Instance fupd_flip_mono' E1 E2 :
  Proper (flip (⊢) ==> flip (⊢)) (fupd E1 E2).
Proof. intros P Q; apply fupd_mono. Qed.

Lemma fupd_intro E P : P ={E}=∗ P.
Proof. iIntros "HP". by iApply bupd_fupd. Qed.
Lemma fupd_intro_mask' E1 E2 : E2 ⊆ E1 → (|={E1,E2}=> |={E2,E1}=> True)%I.
Proof. exact: fupd_intro_mask. Qed.
Lemma fupd_except_0 E1 E2 P : (|={E1,E2}=> ◇ P) ={E1,E2}=∗ P.
Proof. by rewrite {1}(fupd_intro E2 P) except_0_fupd fupd_trans. Qed.

Lemma fupd_frame_l E1 E2 P Q : (P ∗ |={E1,E2}=> Q) ={E1,E2}=∗ P ∗ Q.
Proof. rewrite !(comm _ P); apply fupd_frame_r. Qed.
Lemma fupd_wand_l E1 E2 P Q : (P -∗ Q) ∗ (|={E1,E2}=> P) ={E1,E2}=∗ Q.
Proof. by rewrite fupd_frame_l wand_elim_l. Qed.
Lemma fupd_wand_r E1 E2 P Q : (|={E1,E2}=> P) ∗ (P -∗ Q) ={E1,E2}=∗ Q.
Proof. by rewrite fupd_frame_r wand_elim_r. Qed.

Lemma fupd_trans_frame E1 E2 E3 P Q :
  ((Q ={E2,E3}=∗ True) ∗ |={E1,E2}=> (Q ∗ P)) ={E1,E3}=∗ P.
Proof.
  rewrite fupd_frame_l assoc -(comm _ Q) wand_elim_r.
  by rewrite fupd_frame_r left_id fupd_trans.
Qed.

Lemma fupd_mask_frame_r E1 E2 Ef P :
  E1 ## Ef → (|={E1,E2}=> P) ={E1 ∪ Ef,E2 ∪ Ef}=∗ P.
Proof.
  iIntros (?) "H". iApply fupd_mask_frame_r'; auto.
  iApply fupd_wand_r; iFrame "H"; eauto.
Qed.
Lemma fupd_mask_mono E1 E2 P : E1 ⊆ E2 → (|={E1}=> P) ={E2}=∗ P.
Proof.
  intros (Ef&->&?)%subseteq_disjoint_union_L. by apply fupd_mask_frame_r.
Qed.

Lemma fupd_sep E P Q : (|={E}=> P) ∗ (|={E}=> Q) ={E}=∗ P ∗ Q.
Proof. by rewrite fupd_frame_r fupd_frame_l fupd_trans. Qed.
Lemma fupd_big_sepL {A} E (Φ : nat → A → iProp Σ) (l : list A) :
  ([∗ list] k↦x ∈ l, |={E}=> Φ k x) ={E}=∗ [∗ list] k↦x ∈ l, Φ k x.
Proof.
  apply (big_opL_forall (λ P Q, P ={E}=∗ Q)); auto using fupd_intro.
  intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ -fupd_sep.
Qed.
Lemma fupd_big_sepM `{Countable K} {A} E (Φ : K → A → iProp Σ) (m : gmap K A) :
  ([∗ map] k↦x ∈ m, |={E}=> Φ k x) ={E}=∗ [∗ map] k↦x ∈ m, Φ k x.
Proof.
  apply (big_opM_forall (λ P Q, P ={E}=∗ Q)); auto using fupd_intro.
  intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ -fupd_sep.
Qed.
Lemma fupd_big_sepS `{Countable A} E (Φ : A → iProp Σ) X :
  ([∗ set] x ∈ X, |={E}=> Φ x) ={E}=∗ [∗ set] x ∈ X, Φ x.
Proof.
  apply (big_opS_forall (λ P Q, P ={E}=∗ Q)); auto using fupd_intro.
  intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ -fupd_sep.
Qed.

Lemma fupd_plain E1 E2 P Q `{!Plain P} :
  E1 ⊆ E2 → (Q -∗ P) -∗ (|={E1, E2}=> Q) ={E1}=∗ (|={E1, E2}=> Q) ∗ P.
Proof.
  iIntros (HE) "HQP HQ". iApply (fupd_plain' _ _ E1 with "[HQP] HQ"); first done.
  iIntros "?". iApply fupd_intro. by iApply "HQP".
Qed.
End fupd.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{invG Σ}.
  Implicit Types P Q : iProp Σ.

  Global Instance from_pure_fupd E P φ : FromPure P φ → FromPure (|={E}=> P) φ.
  Proof. rewrite /FromPure. intros <-. apply fupd_intro. Qed.

  Global Instance from_assumption_fupd E p P Q :
    FromAssumption p P (|==> Q) → FromAssumption p P (|={E}=> Q)%I.
  Proof. rewrite /FromAssumption=>->. apply bupd_fupd. Qed.

  Global Instance into_wand_fupd E p q R P Q :
    IntoWand false false R P Q →
    IntoWand p q (|={E}=> R) (|={E}=> P) (|={E}=> Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite !affinely_persistently_if_elim HR.
    apply wand_intro_l. by rewrite fupd_sep wand_elim_r.
  Qed.

  Global Instance into_wand_fupd_persistent E1 E2 p q R P Q :
    IntoWand false q R P Q → IntoWand p q (|={E1,E2}=> R) P (|={E1,E2}=> Q).
  Proof.
    rewrite /IntoWand /= => HR. rewrite affinely_persistently_if_elim HR.
    apply wand_intro_l. by rewrite fupd_frame_l wand_elim_r.
  Qed.

  Global Instance into_wand_fupd_args E1 E2 p q R P Q :
    IntoWand p false R P Q → IntoWand' p q R (|={E1,E2}=> P) (|={E1,E2}=> Q).
  Proof.
    rewrite /IntoWand' /IntoWand /= => ->.
    apply wand_intro_l. by rewrite affinely_persistently_if_elim fupd_wand_r.
  Qed.

  Global Instance from_sep_fupd E P Q1 Q2 :
    FromSep P Q1 Q2 → FromSep (|={E}=> P) (|={E}=> Q1) (|={E}=> Q2).
  Proof. rewrite /FromSep =><-. apply fupd_sep. Qed.

  Global Instance from_or_fupd E1 E2 P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|={E1,E2}=> P) (|={E1,E2}=> Q1) (|={E1,E2}=> Q2).
  Proof. rewrite /FromOr=><-. apply or_elim; apply fupd_mono; auto with I. Qed.

  Global Instance from_exist_fupd {A} E1 E2 P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|={E1,E2}=> P) (λ a, |={E1,E2}=> Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance frame_fupd p E1 E2 R P Q :
    Frame p R P Q → Frame p R (|={E1,E2}=> P) (|={E1,E2}=> Q).
  Proof. rewrite /Frame=><-. by rewrite fupd_frame_l. Qed.

  Global Instance is_except_0_fupd E1 E2 P : IsExcept0 (|={E1,E2}=> P).
  Proof. by rewrite /IsExcept0 except_0_fupd. Qed.

  Global Instance from_modal_fupd E P : FromModal (|={E}=> P) P.
  Proof. rewrite /FromModal. apply fupd_intro. Qed.

  (* Put a lower priority compared to [elim_modal_fupd_fupd], so that
     it is not taken when the first parameter is not specified (in
     spec. patterns). *)
  Global Instance elim_modal_bupd_fupd E1 E2 P Q :
    ElimModal (|==> P) P (|={E1,E2}=> Q) (|={E1,E2}=> Q) | 10.
  Proof.
    by rewrite /ElimModal (bupd_fupd E1) fupd_frame_r wand_elim_r fupd_trans.
  Qed.
  Global Instance elim_modal_fupd_fupd E1 E2 E3 P Q :
    ElimModal (|={E1,E2}=> P) P (|={E1,E3}=> Q) (|={E2,E3}=> Q).
  Proof. by rewrite /ElimModal fupd_frame_r wand_elim_r fupd_trans. Qed.
End proofmode_classes.

Hint Extern 2 (coq_tactics.envs_entails _ (|={_}=> _)) => iModIntro.

(** Fancy updates that take a step. *)

Notation "|={ E1 , E2 }▷=> Q" := (|={E1,E2}=> (▷ |={E2,E1}=> Q))%I
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }▷=>  Q") : bi_scope.
Notation "P ={ E1 , E2 }▷=∗ Q" := (P -∗ |={ E1 , E2 }▷=> Q)%I
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }▷=∗  Q") : bi_scope.
Notation "|={ E }▷=> Q" := (|={E,E}▷=> Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }▷=>  Q") : bi_scope.
Notation "P ={ E }▷=∗ Q" := (P ={E,E}▷=∗ Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }▷=∗  Q") : bi_scope.

Section step_fupd.
Context `{invG Σ}.

Lemma step_fupd_wand E1 E2 P Q : (|={E1,E2}▷=> P) -∗ (P -∗ Q) -∗ |={E1,E2}▷=> Q.
Proof. iIntros "HP HPQ". by iApply "HPQ". Qed.

Lemma step_fupd_mask_frame_r E1 E2 Ef P :
  E1 ## Ef → E2 ## Ef → (|={E1,E2}▷=> P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}▷=> P.
Proof.
  iIntros (??) "HP". iApply fupd_mask_frame_r. done. iMod "HP". iModIntro.
  iNext. by iApply fupd_mask_frame_r.
Qed.

Lemma step_fupd_mask_mono E1 E2 F1 F2 P :
  F1 ⊆ F2 → E1 ⊆ E2 → (|={E1,F2}▷=> P) ⊢ |={E2,F1}▷=> P.
Proof.
  iIntros (??) "HP".
  iMod (fupd_intro_mask') as "HM1"; first done. iMod "HP".
  iMod (fupd_intro_mask') as "HM2"; first done. iModIntro.
  iNext. iMod "HM2". iMod "HP". iMod "HM1". done.
Qed.

Lemma step_fupd_intro E1 E2 P : E2 ⊆ E1 → ▷ P -∗ |={E1,E2}▷=> P.
Proof. iIntros (?) "HP". iApply (step_fupd_mask_mono E2 _ _ E2); auto. Qed.
End step_fupd.
