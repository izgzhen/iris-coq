From stdpp Require Import namespaces.
From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(* Global functor setup *)
Definition invΣ : gFunctors :=
  #[GFunctor (authRF (gmapURF positive (agreeRF (laterCF idCF))));
    GFunctor coPset_disjUR;
    GFunctor (gset_disjUR positive)].

Class invPreG (Σ : gFunctors) : Set := WsatPreG {
  inv_inPreG :> inG Σ (authR (gmapUR positive (agreeR (laterC (iPreProp Σ)))));
  enabled_inPreG :> inG Σ coPset_disjR;
  disabled_inPreG :> inG Σ (gset_disjR positive);
}.

Instance subG_invΣ {Σ} : subG invΣ Σ → invPreG Σ.
Proof. solve_inG. Qed.

(* Allocation *)
Lemma wsat_alloc `{invPreG Σ} : (|==> ∃ _ : invG Σ, wsat ∗ ownE ⊤)%I.
Proof.
  iIntros.
  iMod (own_alloc (● (∅ : gmap _ _))) as (γI) "HI"; first done.
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  iModIntro; iExists (WsatG _ _ _ _ γI γE γD).
  rewrite /wsat /ownE -lock; iFrame.
  iExists ∅. rewrite fmap_empty big_opM_empty. by iFrame.
Qed.

(* Program logic adequacy *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)
}.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ κ t3 σ3, step (t2, σ2) κ (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists κ, (t2' ++ e3 :: t2'' ++ efs), σ3; econstructor; eauto.
Qed.

Section adequacy.
Context `{irisG Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation world' E σ κs := (wsat ∗ ownE E ∗ state_interp σ κs)%I (only parsing).
Notation world σ κs := (world' ⊤ σ κs) (only parsing).

Notation wptp s t := ([∗ list] ef ∈ t, WP ef @ s; ⊤ {{ _, True }})%I.

Lemma wp_step s E e1 σ1 κ κs e2 σ2 efs Φ :
  prim_step e1 σ1 κ e2 σ2 efs →
  world' E σ1 (κ ++ κs) ∗ WP e1 @ s; E {{ Φ }}
  ==∗  ▷ |==> ◇ (world' E σ2 κs ∗ WP e2 @ s; E {{ Φ }} ∗ wptp s efs).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "[(Hw & HE & Hσ) H]".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) // uPred_fupd_eq.
  iMod ("H" $! σ1 with "Hσ [Hw HE]") as ">(Hw & HE & _ & H)"; first by iFrame.
  iMod ("H" $! e2 σ2 efs with "[//] [$Hw $HE]") as ">(Hw & HE & H)".
  iIntros "!> !>". by iMod ("H" with "[$Hw $HE]") as ">($ & $ & $)".
Qed.

Lemma wptp_step s e1 t1 t2 κ κs σ1 σ2 Φ :
  step (e1 :: t1,σ1) κ (t2, σ2) →
  world σ1 (κ ++ κs) ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1
  ==∗ ∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗ ▷ |==> ◇ (world σ2 κs ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2').
Proof.
  iIntros (Hstep) "(HW & He & Ht)".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs). iSplitR; first by eauto.
    iFrame "Ht". iApply wp_step; eauto with iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iDestruct "Ht" as "($ & He' & $)". iFrame "He".
    iApply wp_step; eauto with iFrame.
Qed.

Lemma wptp_steps s n e1 t1 κs κs' t2 σ1 σ2 Φ :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  world σ1 (κs ++ κs') ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1 ⊢
  Nat.iter (S n) (λ P, |==> ▷ P) (∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗ world σ2 κs' ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2').
Proof.
  revert e1 t1 κs κs' t2 σ1 σ2; simpl; induction n as [|n IH]=> e1 t1 κs κs' t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "?"; eauto 10. }
  iIntros (Hsteps) "H". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite <- app_assoc.
  iMod (wptp_step with "H") as (e1' t1'') "[% H]"; first by eauto; simplify_eq.
  subst. iModIntro; iNext; iMod "H" as ">H". by iApply IH.
Qed.

Lemma bupd_iter_laterN_mono n P Q `{!Plain Q} :
  (P ⊢ Q) → Nat.iter n (λ P, |==> ▷ P)%I P ⊢ ▷^n Q.
Proof.
  intros HPQ. induction n as [|n IH]=> //=. by rewrite IH bupd_plain.
Qed.

Lemma bupd_iter_frame_l n R Q :
  R ∗ Nat.iter n (λ P, |==> ▷ P) Q ⊢ Nat.iter n (λ P, |==> ▷ P) (R ∗ Q).
Proof.
  induction n as [|n IH]; simpl; [done|].
  by rewrite bupd_frame_l {1}(later_intro R) -later_sep IH.
Qed.

Lemma wptp_result s n e1 t1 κs κs' v2 t2 σ1 σ2 φ :
  nsteps n (e1 :: t1, σ1) κs (of_val v2 :: t2, σ2) →
  world σ1 (κs ++ κs') ∗
  WP e1 @ s; ⊤ {{ v, ∀ σ, state_interp σ κs' ={⊤,∅}=∗ ⌜φ v σ⌝ }} ∗
  wptp s t1
  ⊢ ▷^(S (S n)) ⌜φ v2 σ2⌝.
Proof.
  intros. rewrite wptp_steps // laterN_later. apply: bupd_iter_laterN_mono.
  iDestruct 1 as (e2 t2' ?) "((Hw & HE & Hσ) & H & _)"; simplify_eq.
  iDestruct (wp_value_inv' with "H") as "H". rewrite uPred_fupd_eq.
  iMod ("H" with "[$]") as ">(Hw & HE & H)".
  iMod ("H" with "Hσ [$]") as ">(_ & _ & $)".
Qed.

Lemma wp_safe E e σ κs Φ :
  world' E σ κs -∗ WP e @ E {{ Φ }} ==∗ ▷ ⌜is_Some (to_val e) ∨ reducible e σ⌝.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "(Hw&HE&Hσ) H".
  destruct (to_val e) as [v|] eqn:?.
  { iIntros "!> !> !%". left. by exists v. }
  rewrite uPred_fupd_eq. iMod ("H" $! _ [] with "Hσ [-]") as ">(?&?&%&?)"; first by iFrame.
  iIntros "!> !> !%". by right.
Qed.

Lemma wptp_safe n e1 κs κs' e2 t1 t2 σ1 σ2 Φ :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) → e2 ∈ t2 →
  world σ1 (κs ++ κs') ∗ WP e1 {{ Φ }} ∗ wptp NotStuck t1
  ⊢ ▷^(S (S n)) ⌜is_Some (to_val e2) ∨ reducible e2 σ2⌝.
Proof.
  intros ? He2. rewrite wptp_steps // laterN_later. apply: bupd_iter_laterN_mono.
  iDestruct 1 as (e2' t2' ?) "(Hw & H & Htp)"; simplify_eq.
  apply elem_of_cons in He2 as [<-|?].
  - iMod (wp_safe with "Hw H") as "$".
  - iMod (wp_safe with "Hw [Htp]") as "$". by iApply (big_sepL_elem_of with "Htp").
Qed.

Lemma wptp_invariance s n e1 κs κs' e2 t1 t2 σ1 σ2 φ Φ :
  nsteps n (e1 :: t1, σ1) κs (t2, σ2) →
  (state_interp σ2 κs' ={⊤,∅}=∗ ⌜φ⌝) ∗ world σ1 (κs ++ κs') ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1
  ⊢ ▷^(S (S n)) ⌜φ⌝.
Proof.
  intros ?. rewrite wptp_steps // bupd_iter_frame_l laterN_later.
  apply: bupd_iter_laterN_mono.
  iIntros "[Hback H]"; iDestruct "H" as (e2' t2' ->) "[(Hw&HE&Hσ) _]".
  rewrite uPred_fupd_eq.
  iMod ("Hback" with "Hσ [$Hw $HE]") as "> (_ & _ & $)"; auto.
Qed.
End adequacy.

Theorem wp_strong_adequacy Σ Λ `{invPreG Σ} s e σ φ :
  (∀ `{Hinv : invG Σ} κs,
     (|={⊤}=> ∃ stateI : state Λ → list (observation Λ) → iProp Σ,
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ κs ∗ WP e @ s; ⊤ {{ v, ∀ σ, stateI σ [] ={⊤,∅}=∗ ⌜φ v σ⌝ }})%I) →
  adequate s e σ φ.
Proof.
  intros Hwp; split.
  - intros t2 σ2 v2 [n [κs ?]]%erased_steps_nsteps.
    eapply (soundness (M:=iResUR Σ) _ (S (S n))).
    iMod wsat_alloc as (Hinv) "[Hw HE]". specialize (Hwp _ κs).
    rewrite {1}uPred_fupd_eq in Hwp; iMod (Hwp with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
    iDestruct "Hwp" as (Istate) "[HI Hwp]".
    iApply (@wptp_result _ _ (IrisG _ _ _ Hinv Istate) _ _ _ _ _ []); first by eauto.
    rewrite app_nil_r. eauto with iFrame.
  - destruct s; last done. intros t2 σ2 e2 _ [n [κs ?]]%erased_steps_nsteps ?.
    eapply (soundness (M:=iResUR Σ) _ (S (S n))).
    iMod wsat_alloc as (Hinv) "[Hw HE]". specialize (Hwp _ κs).
    rewrite uPred_fupd_eq in Hwp; iMod (Hwp with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
    iDestruct "Hwp" as (Istate) "[HI Hwp]".
    iApply (@wptp_safe _ _ (IrisG _ _ _ Hinv Istate) _ _ _ []); [by eauto..|].
    rewrite app_nil_r. eauto with iFrame.
Qed.

Theorem wp_adequacy Σ Λ `{invPreG Σ} s e σ φ :
  (∀ `{Hinv : invG Σ} κs,
     (|={⊤}=> ∃ stateI : state Λ → list (observation Λ) → iProp Σ,
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }})%I) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply (wp_strong_adequacy Σ _)=> Hinv κs.
  iMod Hwp as (stateI) "[Hσ H]". iExists stateI. iIntros "{$Hσ} !>".
  iApply (wp_wand with "H"). iIntros (v ? σ') "_".
  iMod (fupd_intro_mask' ⊤ ∅) as "_"; auto.
Qed.

Theorem wp_invariance Σ Λ `{invPreG Σ} s e σ1 t2 σ2 φ :
  (∀ `{Hinv : invG Σ} κs κs',
     (|={⊤}=> ∃ stateI : state Λ → list (observation Λ) → iProp Σ,
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1 (κs ++ κs') ∗ WP e @ s; ⊤ {{ _, True }} ∗ (stateI σ2 κs' ={⊤,∅}=∗ ⌜φ⌝))%I) →
  rtc erased_step ([e], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (soundness (M:=iResUR Σ) _ (S (S n))).
  iMod wsat_alloc as (Hinv) "[Hw HE]". specialize (Hwp _ κs []).
  rewrite {1}uPred_fupd_eq in Hwp; iMod (Hwp with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
  iDestruct "Hwp" as (Istate) "(HIstate & Hwp & Hclose)".
  iApply (@wptp_invariance _ _ (IrisG _ _ _ Hinv Istate)); eauto with iFrame.
Qed.

(* An equivalent version that does not require finding [fupd_intro_mask'], but
can be confusing to use. *)
Corollary wp_invariance' Σ Λ `{invPreG Σ} s e σ1 t2 σ2 φ :
  (∀ `{Hinv : invG Σ} κs κs',
     (|={⊤}=> ∃ stateI : state Λ → list (observation Λ) → iProp Σ,
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI in
       stateI σ1 κs ∗ WP e @ s; ⊤ {{ _, True }} ∗ (stateI σ2 κs' -∗ ∃ E, |={⊤,E}=> ⌜φ⌝))%I) →
  rtc erased_step ([e], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp. eapply wp_invariance; first done.
  intros Hinv κs κs'. iMod (Hwp Hinv) as (stateI) "(? & ? & Hφ)".
  iModIntro. iExists stateI. iFrame. iIntros "Hσ".
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  iMod (fupd_intro_mask') as "_"; last by iModIntro. solve_ndisj.
Qed.
