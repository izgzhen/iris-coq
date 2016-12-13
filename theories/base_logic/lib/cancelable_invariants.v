From iris.base_logic.lib Require Export invariants fractional.
From iris.algebra Require Export frac.
From iris.proofmode Require Import tactics.
Import uPred.

Class cinvG Σ := cinv_inG :> inG Σ fracR.

Section defs.
  Context `{invG Σ, cinvG Σ}.

  Definition cinv_own (γ : gname) (p : frac) : iProp Σ := own γ p.

  Definition cinv (N : namespace) (γ : gname) (P : iProp Σ) : iProp Σ :=
    inv N (P ∨ cinv_own γ 1%Qp)%I.
End defs.

Instance: Params (@cinv) 5.
Typeclasses Opaque cinv_own cinv.

Section proofs.
  Context `{invG Σ, cinvG Σ}.

  Global Instance cinv_own_timeless γ p : TimelessP (cinv_own γ p).
  Proof. rewrite /cinv_own; apply _. Qed.

  Global Instance cinv_ne N γ n : Proper (dist n ==> dist n) (cinv N γ).
  Proof. solve_proper. Qed.
  Global Instance cinv_proper N γ : Proper ((≡) ==> (≡)) (cinv N γ).
  Proof. apply (ne_proper _). Qed.

  Global Instance cinv_persistent N γ P : PersistentP (cinv N γ P).
  Proof. rewrite /cinv; apply _. Qed.

  Global Instance cinv_own_fractionnal γ : Fractional (cinv_own γ).
  Proof. intros ??. by rewrite -own_op. Qed.
  Global Instance cinv_own_as_fractionnal γ q :
    AsFractional (cinv_own γ q) (cinv_own γ) q.
  Proof. split. done. apply _. Qed.

  Lemma cinv_own_valid γ q1 q2 : cinv_own γ q1 -∗ cinv_own γ q2 -∗ ✓ (q1 + q2)%Qp.
  Proof. apply (own_valid_2 γ q1 q2). Qed.

  Lemma cinv_own_1_l γ q : cinv_own γ 1 -∗ cinv_own γ q -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (cinv_own_valid with "H1 H2") as %[]%(exclusive_l 1%Qp).
  Qed.

  Lemma cinv_alloc E N P : ▷ P ={E}=∗ ∃ γ, cinv N γ P ∗ cinv_own γ 1.
  Proof.
    rewrite /cinv /cinv_own. iIntros "HP".
    iMod (own_alloc 1%Qp) as (γ) "H1"; first done.
    iMod (inv_alloc N _ (P ∨ own γ 1%Qp)%I with "[HP]"); eauto.
  Qed.

  Lemma cinv_cancel E N γ P : ↑N ⊆ E → cinv N γ P -∗ cinv_own γ 1 ={E}=∗ ▷ P.
  Proof.
    rewrite /cinv. iIntros (?) "#Hinv Hγ".
    iInv N as "[$|>Hγ']" "Hclose"; first iApply "Hclose"; eauto.
    iDestruct (cinv_own_1_l with "Hγ Hγ'") as %[].
  Qed.

  Lemma cinv_open E N γ p P :
    ↑N ⊆ E →
    cinv N γ P -∗ cinv_own γ p ={E,E∖↑N}=∗ ▷ P ∗ cinv_own γ p ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    rewrite /cinv. iIntros (?) "#Hinv Hγ".
    iInv N as "[$ | >Hγ']" "Hclose".
    - iIntros "!> {$Hγ} HP". iApply "Hclose"; eauto.
    - iDestruct (cinv_own_1_l with "Hγ' Hγ") as %[].
  Qed.
End proofs.
