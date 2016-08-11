From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic Require Import big_op adequacy.
From iris.program_logic Require Import wsat.
From iris.proofmode Require Import tactics weakestpre.
Import uPred.

Record adequate {Λ} (e1 : expr Λ) (σ1 : state Λ) (φ : val Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2;
  adequate_safe t2 σ2 e2 :
   rtc step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)
}.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate e1 σ1 φ →
  rtc step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_safe e1 σ1 φ Had t2 σ2 e2) as [?|(e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3; econstructor; eauto.
Qed.

Section adequacy.
Context `{irisG Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation world σ := (wsat ★ ownE ⊤ ★ ownP_auth σ)%I.

Definition wptp (t : list (expr Λ)) := ([★] (flip (wp ⊤) (λ _, True) <$> t))%I.

Lemma wptp_cons e t : wptp (e :: t) ⊣⊢ WP e {{ _, True }} ★ wptp t.
Proof. done. Qed.
Lemma wptp_app t1 t2 : wptp (t1 ++ t2) ⊣⊢ wptp t1 ★ wptp t2.
Proof. by rewrite /wptp fmap_app big_sep_app. Qed.

Lemma wp_step e1 σ1 e2 σ2 efs Φ :
  prim_step e1 σ1 e2 σ2 efs →
  world σ1 ★ WP e1 {{ Φ }} =r=> ▷ |=r=> ◇ (world σ2 ★ WP e2 {{ Φ }} ★ wp_fork efs).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (Hstep) "[(Hw & HE & Hσ) [H|[_ H]]]".
  { iDestruct "H" as (v) "[% _]". apply val_stuck in Hstep; simplify_eq. }
  rewrite pvs_eq /pvs_def.
  iVs ("H" $! σ1 with "Hσ [Hw HE]") as ">(Hw & HE & _ & H)"; first by iFrame.
  iVsIntro; iNext.
  iVs ("H" $! e2 σ2 efs with "[%] [Hw HE]")
    as ">($ & $ & $ & $)"; try iFrame; eauto.
Qed.

Lemma wptp_step e1 t1 t2 σ1 σ2 Φ :
  step (e1 :: t1,σ1) (t2, σ2) →
  world σ1 ★ WP e1 {{ Φ }} ★ wptp t1
  =r=> ∃ e2 t2', t2 = e2 :: t2' ★ ▷ |=r=> ◇ (world σ2 ★ WP e2 {{ Φ }} ★ wptp t2').
Proof.
  iIntros (Hstep) "(HW & He & Ht)".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs); iSplitR; first eauto.
    rewrite wptp_app. iFrame "Ht". iApply wp_step; try iFrame; eauto.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    rewrite !wptp_app !wptp_cons wptp_app.
    iDestruct "Ht" as "($ & He' & $)"; iFrame "He".
    iApply wp_step; try iFrame; eauto.
Qed.

Lemma wptp_steps n e1 t1 t2 σ1 σ2 Φ :
  nsteps step n (e1 :: t1, σ1) (t2, σ2) →
  world σ1 ★ WP e1 {{ Φ }} ★ wptp t1 ⊢
  Nat.iter (S n) (λ P, |=r=> ▷ P) (∃ e2 t2',
    t2 = e2 :: t2' ★ world σ2 ★ WP e2 {{ Φ }} ★ wptp t2').
Proof.
  revert e1 t1 t2 σ1 σ2; simpl; induction n as [|n IH]=> e1 t1 t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "?"; eauto 10. }
  iIntros (Hsteps) "H". inversion_clear Hsteps as [|?? [t1' σ1']].
  iVs (wptp_step with "H") as (e1' t1'') "[% H]"; first eauto; simplify_eq.
  iVsIntro; iNext; iVs "H" as ">?". by iApply IH.
Qed.

Instance rvs_iter_mono n : Proper ((⊢) ==> (⊢)) (Nat.iter n (λ P, |=r=> ▷ P)%I).
Proof. intros P Q HP. induction n; simpl; do 2?f_equiv; auto. Qed.

Lemma wptp_result n e1 t1 v2 t2 σ1 σ2 φ :
  nsteps step n (e1 :: t1, σ1) (of_val v2 :: t2, σ2) →
  world σ1 ★ WP e1 {{ v, ■ φ v }} ★ wptp t1 ⊢
  Nat.iter (S (S n)) (λ P, |=r=> ▷ P) (■ φ v2).
Proof.
  intros. rewrite wptp_steps //.
  rewrite (Nat_iter_S_r (S n)). apply rvs_iter_mono.
  iDestruct 1 as (e2 t2') "(% & (Hw & HE & _) & H & _)"; simplify_eq.
  iDestruct (wp_value_inv with "H") as "H". rewrite pvs_eq /pvs_def.
  iVs ("H" with "[Hw HE]") as ">(_ & _ & $)"; iFrame; auto.
Qed.

Lemma wp_safe e σ Φ :
  world σ ★ WP e {{ Φ }} =r=> ▷ ■ (is_Some (to_val e) ∨ reducible e σ).
Proof.
  rewrite wp_unfold /wp_pre. iIntros "[(Hw&HE&Hσ) [H|[_ H]]]".
  { iDestruct "H" as (v) "[% _]"; eauto 10. }
  rewrite pvs_eq. iVs ("H" with "* Hσ [-]") as ">(?&?&%&?)"; first by iFrame.
  eauto 10.
Qed.

Lemma wptp_safe n e1 e2 t1 t2 σ1 σ2 Φ :
  nsteps step n (e1 :: t1, σ1) (t2, σ2) → e2 ∈ t2 →
  world σ1 ★ WP e1 {{ Φ }} ★ wptp t1 ⊢
  Nat.iter (S (S n)) (λ P, |=r=> ▷ P) (■ (is_Some (to_val e2) ∨ reducible e2 σ2)).
Proof.
  intros ? He2. rewrite wptp_steps //; rewrite (Nat_iter_S_r (S n)). apply rvs_iter_mono.
  iDestruct 1 as (e2' t2') "(% & Hw & H & Htp)"; simplify_eq.
  apply elem_of_cons in He2 as [<-|?]; first (iApply wp_safe; by iFrame "Hw H").
  iApply wp_safe. iFrame "Hw".
  iApply (big_sep_elem_of with "Htp"); apply elem_of_list_fmap; eauto.
Qed.
End adequacy.

Theorem wp_adequacy Σ `{irisPreG Λ Σ} e σ φ :
  (∀ `{irisG Λ Σ}, ownP σ ⊢ WP e {{ v, ■ φ v }}) →
  adequate e σ φ.
Proof.
  intros Hwp; split.
  - intros t2 σ2 v2 [n ?]%rtc_nsteps.
    eapply (adequacy (M:=iResUR Σ) _ (S (S (S n)))); iIntros "".
    rewrite Nat_iter_S. iVs (iris_alloc σ) as (?) "(?&?&?&Hσ)".
    iVsIntro. iNext. iApply wptp_result; eauto.
    iFrame. iSplitL; auto. by iApply Hwp.
  - intros t2 σ2 e2 [n ?]%rtc_nsteps ?.
    eapply (adequacy (M:=iResUR Σ) _ (S (S (S n)))); iIntros "".
    rewrite Nat_iter_S. iVs (iris_alloc σ) as (?) "(Hw & HE & Hσ & Hσf)".
    iVsIntro. iNext. iApply wptp_safe; eauto.
    iFrame "Hw HE Hσ". iSplitL; auto. by iApply Hwp.
Qed.
