From iris.program_logic Require Export total_weakestpre adequacy.
From iris.algebra Require Import gmap auth agree gset coPset list.
From iris.bi Require Import big_op fixpoint.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Section adequacy.
Context `{irisG Λ Σ}.
Implicit Types e : expr Λ.

Definition twptp_pre (twptp : list (expr Λ) → iProp Σ)
    (t1 : list (expr Λ)) : iProp Σ :=
  (∀ t2 σ1 κ κs σ2 n, ⌜step (t1,σ1) κ (t2,σ2)⌝ -∗
    state_interp σ1 κs n ={⊤}=∗ ∃ n', ⌜κ = []⌝ ∗ state_interp σ2 κs n' ∗ twptp t2)%I.

Lemma twptp_pre_mono (twptp1 twptp2 : list (expr Λ) → iProp Σ) :
  (<pers> (∀ t, twptp1 t -∗ twptp2 t) →
  ∀ t, twptp_pre twptp1 t -∗ twptp_pre twptp2 t)%I.
Proof.
  iIntros "#H"; iIntros (t) "Hwp". rewrite /twptp_pre.
  iIntros (t2 σ1 κ κs σ2 n1) "Hstep Hσ".
  iMod ("Hwp" with "[$] [$]") as (n2) "($ & Hσ & ?)".
  iModIntro. iExists n2. iFrame "Hσ". by iApply "H".
Qed.

Local Instance twptp_pre_mono' : BiMonoPred twptp_pre.
Proof.
  constructor; first apply twptp_pre_mono.
  intros wp Hwp n t1 t2 ?%(discrete_iff _ _)%leibniz_equiv; solve_proper.
Qed.

Definition twptp (t : list (expr Λ)) : iProp Σ :=
  bi_least_fixpoint twptp_pre t.

Lemma twptp_unfold t : twptp t ⊣⊢ twptp_pre twptp t.
Proof. by rewrite /twptp least_fixpoint_unfold. Qed.

Lemma twptp_ind Ψ :
  ((□ ∀ t, twptp_pre (λ t, Ψ t ∧ twptp t) t -∗ Ψ t) → ∀ t, twptp t -∗ Ψ t)%I.
Proof.
  iIntros "#IH" (t) "H".
  assert (NonExpansive Ψ).
  { by intros n ?? ->%(discrete_iff _ _)%leibniz_equiv. }
  iApply (least_fixpoint_strong_ind _ Ψ with "[] H").
  iIntros "!#" (t') "H". by iApply "IH".
Qed.

Instance twptp_Permutation : Proper ((≡ₚ) ==> (⊢)) twptp.
Proof.
  iIntros (t1 t1' Ht) "Ht1". iRevert (t1' Ht); iRevert (t1) "Ht1".
  iApply twptp_ind; iIntros "!#" (t1) "IH"; iIntros (t1' Ht).
  rewrite twptp_unfold /twptp_pre. iIntros (t2 σ1 κ κs σ2 n Hstep) "Hσ".
  destruct (step_Permutation t1' t1 t2 κ σ1 σ2) as (t2'&?&?); try done.
  iMod ("IH" $! t2' with "[% //] Hσ") as (n2) "($ & Hσ & IH & _)".
  iModIntro. iExists n2. iFrame "Hσ". by iApply "IH".
Qed.

Lemma twptp_app t1 t2 : twptp t1 -∗ twptp t2 -∗ twptp (t1 ++ t2).
Proof.
  iIntros "H1". iRevert (t2). iRevert (t1) "H1".
  iApply twptp_ind; iIntros "!#" (t1) "IH1". iIntros (t2) "H2".
  iRevert (t1) "IH1"; iRevert (t2) "H2".
  iApply twptp_ind; iIntros "!#" (t2) "IH2". iIntros (t1) "IH1".
  rewrite twptp_unfold /twptp_pre. iIntros (t1'' σ1 κ κs σ2 n Hstep) "Hσ1".
  destruct Hstep as [e1 σ1' e2 σ2' efs' t1' t2' [=Ht ?] ? Hstep]; simplify_eq/=.
  apply app_eq_inv in Ht as [(t&?&?)|(t&?&?)]; subst.
  - destruct t as [|e1' ?]; simplify_eq/=.
    + iMod ("IH2" with "[%] Hσ1") as (n2) "($ & Hσ & IH2 & _)".
      { by eapply step_atomic with (t1:=[]). }
      iModIntro. iExists n2. iFrame "Hσ".
      rewrite -{2}(left_id_L [] (++) (e2 :: _)). iApply "IH2".
      by setoid_rewrite (right_id_L [] (++)).
    + iMod ("IH1" with "[%] Hσ1") as (n2) "($ & Hσ & IH1 & _)"; first by econstructor.
      iAssert (twptp t2) with "[IH2]" as "Ht2".
      { rewrite twptp_unfold. iApply (twptp_pre_mono with "[] IH2").
        iIntros "!# * [_ ?] //". }
      iModIntro. iExists n2. iFrame "Hσ".
      rewrite -assoc_L (comm _ t2) !cons_middle !assoc_L. by iApply "IH1".
  - iMod ("IH2" with "[%] Hσ1") as (n2) "($ & Hσ & IH2 & _)"; first by econstructor.
    iModIntro. iExists n2. iFrame "Hσ". rewrite -assoc_L. by iApply "IH2".
Qed.

Lemma twp_twptp s Φ e : WP e @ s; ⊤ [{ Φ }] -∗ twptp [e].
Proof.
  iIntros "He". remember (⊤ : coPset) as E eqn:HE.
  iRevert (HE). iRevert (e E Φ) "He". iApply twp_ind.
  iIntros "!#" (e E Φ); iIntros "IH" (->).
  rewrite twptp_unfold /twptp_pre /twp_pre. iIntros (t1' σ1' κ κs σ2' n Hstep) "Hσ1".
  destruct Hstep as [e1 σ1 e2 σ2 efs [|? t1] t2 ?? Hstep];
    simplify_eq/=; try discriminate_list.
  destruct (to_val e1) as [v|] eqn:He1.
  { apply val_stuck in Hstep; naive_solver. }
  iMod ("IH" with "Hσ1") as "[_ IH]".
  iMod ("IH" with "[% //]") as "($ & Hσ & [IH _] & IHfork)".
  iModIntro. iExists (length efs + n). iFrame "Hσ".
  iApply (twptp_app [_] with "[IH]"); first by iApply "IH".
  clear. iInduction efs as [|e efs] "IH"; simpl.
  { rewrite twptp_unfold /twptp_pre. iIntros (t2 σ1 κ κs σ2 n1 Hstep).
    destruct Hstep; simplify_eq/=; discriminate_list. }
  iDestruct "IHfork" as "[[IH' _] IHfork]".
  iApply (twptp_app [_] with "[IH']"). by iApply "IH'". by iApply "IH".
Qed.

Lemma twptp_total n σ t :
  state_interp σ [] n -∗ twptp t ={⊤}=∗ ▷ ⌜sn erased_step (t, σ)⌝.
Proof.
  iIntros "Hσ Ht". iRevert (σ n) "Hσ". iRevert (t) "Ht".
  iApply twptp_ind; iIntros "!#" (t) "IH"; iIntros (σ n) "Hσ".
  iApply (pure_mono _ _ (Acc_intro _)). iIntros ([t' σ'] [κ Hstep]).
  rewrite /twptp_pre.
  iMod ("IH" with "[% //] Hσ") as (n' ->) "[Hσ [H _]]".
  by iApply "H".
Qed.
End adequacy.

Theorem twp_total Σ Λ `{invPreG Σ} s e σ Φ :
  (∀ `{Hinv : invG Σ},
     (|={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI fork_post in
       stateI σ [] 0 ∗ WP e @ s; ⊤ [{ Φ }])%I) →
  sn erased_step ([e], σ). (* i.e. ([e], σ) is strongly normalizing *)
Proof.
  intros Hwp. apply (soundness (M:=iResUR Σ) _  2); simpl.
  apply (fupd_plain_soundness ⊤ _)=> Hinv.
  iMod (Hwp) as (stateI fork_post) "[Hσ H]".
  iApply (@twptp_total _ _ (IrisG _ _ Hinv stateI fork_post) with "Hσ").
  by iApply (@twp_twptp _ _ (IrisG _ _ Hinv stateI fork_post)).
Qed.
