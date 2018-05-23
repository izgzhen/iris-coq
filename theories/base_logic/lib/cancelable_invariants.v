From iris.base_logic.lib Require Export invariants.
From iris.bi.lib Require Import fractional.
From iris.algebra Require Export frac.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Class cinvG Σ := cinv_inG :> inG Σ fracR.
Definition cinvΣ : gFunctors := #[GFunctor fracR].

Instance subG_cinvΣ {Σ} : subG cinvΣ Σ → cinvG Σ.
Proof. solve_inG. Qed.

Section defs.
  Context `{invG Σ, cinvG Σ}.

  Definition cinv_own (γ : gname) (p : frac) : iProp Σ := own γ p.

  Definition cinv (N : namespace) (γ : gname) (P : iProp Σ) : iProp Σ :=
    (∃ P', □ ▷ (P ↔ P') ∗ inv N (P' ∨ cinv_own γ 1%Qp))%I.
End defs.

Instance: Params (@cinv) 5.

Section proofs.
  Context `{invG Σ, cinvG Σ}.

  Global Instance cinv_own_timeless γ p : Timeless (cinv_own γ p).
  Proof. rewrite /cinv_own; apply _. Qed.

  Global Instance cinv_contractive N γ : Contractive (cinv N γ).
  Proof. solve_contractive. Qed.
  Global Instance cinv_ne N γ : NonExpansive (cinv N γ).
  Proof. exact: contractive_ne. Qed.
  Global Instance cinv_proper N γ : Proper ((≡) ==> (≡)) (cinv N γ).
  Proof. exact: ne_proper. Qed.

  Global Instance cinv_persistent N γ P : Persistent (cinv N γ P).
  Proof. rewrite /cinv; apply _. Qed.

  Global Instance cinv_own_fractional γ : Fractional (cinv_own γ).
  Proof. intros ??. by rewrite /cinv_own -own_op. Qed.
  Global Instance cinv_own_as_fractional γ q :
    AsFractional (cinv_own γ q) (cinv_own γ) q.
  Proof. split. done. apply _. Qed.

  Lemma cinv_own_valid γ q1 q2 : cinv_own γ q1 -∗ cinv_own γ q2 -∗ ✓ (q1 + q2)%Qp.
  Proof. apply (own_valid_2 γ q1 q2). Qed.

  Lemma cinv_own_1_l γ q : cinv_own γ 1 -∗ cinv_own γ q -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (cinv_own_valid with "H1 H2") as %[]%(exclusive_l 1%Qp).
  Qed.

  Lemma cinv_iff N γ P P' :
    ▷ □ (P ↔ P') -∗ cinv N γ P -∗ cinv N γ P'.
  Proof.
    iIntros "#HP' Hinv". iDestruct "Hinv" as (P'') "[#HP'' Hinv]".
    iExists _. iFrame "Hinv". iAlways. iNext. iSplit.
    - iIntros "?". iApply "HP''". iApply "HP'". done.
    - iIntros "?". iApply "HP'". iApply "HP''". done.
  Qed.

  Lemma cinv_alloc_strong (G : gset gname) E N :
    (|={E}=> ∃ γ, ⌜ γ ∉ G ⌝ ∧ cinv_own γ 1 ∗ ∀ P, ▷ P ={E}=∗ cinv N γ P)%I.
  Proof.
    iMod (own_alloc_strong 1%Qp G) as (γ) "[Hfresh Hγ]"; first done.
    iExists γ; iIntros "!> {$Hγ $Hfresh}" (P) "HP".
    iMod (inv_alloc N _ (P ∨ own γ 1%Qp)%I with "[HP]"); first by eauto.
    iIntros "!>". iExists P. iSplit; last done. iIntros "!# !>"; iSplit; auto.
  Qed.

  Lemma cinv_alloc E N P : ▷ P ={E}=∗ ∃ γ, cinv N γ P ∗ cinv_own γ 1.
  Proof.
    iIntros "HP". iMod (cinv_alloc_strong ∅ E N) as (γ _) "[Hγ Halloc]".
    iExists γ. iFrame "Hγ". by iApply "Halloc".
  Qed.

  Lemma cinv_cancel E N γ P : ↑N ⊆ E → cinv N γ P -∗ cinv_own γ 1 ={E}=∗ ▷ P.
  Proof.
    iIntros (?) "#Hinv Hγ". iDestruct "Hinv" as (P') "[#HP' Hinv]".
    iInv N as "[HP|>Hγ']".
    - iModIntro. iFrame "Hγ". iModIntro. iApply "HP'". done.
    - iDestruct (cinv_own_1_l with "Hγ Hγ'") as %[].
  Qed.

  Lemma cinv_open E N γ p P :
    ↑N ⊆ E →
    cinv N γ P -∗ cinv_own γ p ={E,E∖↑N}=∗ ▷ P ∗ cinv_own γ p ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "#Hinv Hγ". iDestruct "Hinv" as (P') "[#HP' Hinv]".
    iInv N as "[HP | >Hγ']" "Hclose".
    - iIntros "!> {$Hγ}". iSplitL "HP".
      + iNext. iApply "HP'". done.
      + iIntros "HP". iApply "Hclose". iLeft. iNext. by iApply "HP'".
    - iDestruct (cinv_own_1_l with "Hγ' Hγ") as %[].
  Qed.

  Global Instance into_inv_cinv N γ P : IntoInv (cinv N γ P) N.

  Global Instance into_acc_cinv E N γ P p :
    IntoAcc (X:=unit) (cinv N γ P)
            (↑N ⊆ E) (cinv_own γ p) (fupd E (E∖↑N)) (fupd (E∖↑N) E)
            (λ _, ▷ P ∗ cinv_own γ p)%I (λ _, ▷ P)%I (λ _, None)%I.
  Proof.
    rewrite /IntoAcc /accessor. iIntros (?) "#Hinv Hown".
    rewrite exist_unit -assoc.
    iApply (cinv_open with "Hinv"); done.
  Qed.
End proofs.

Typeclasses Opaque cinv_own cinv.
