From iris.algebra Require Export auth upred_tactics.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.proofmode Require Import invariants ghost_ownership.
Import uPred.

(* The CMRA we need. *)
Class authG Λ Σ (A : ucmraT) := AuthG {
  auth_inG :> inG Λ Σ (authR A);
  auth_timeless :> CMRADiscrete A;
}.
(* The Functor we need. *)
Definition authGF (A : ucmraT) : gFunctor := GFunctor (constRF (authR A)).
(* Show and register that they match. *)
Instance authGF_inGF (A : ucmraT) `{inGF Λ Σ (authGF A)}
  `{CMRADiscrete A} : authG Λ Σ A.
Proof. split; try apply _. apply: inGF_inG. Qed.

Section definitions.
  Context `{authG Λ Σ A} (γ : gname).
  Definition auth_own (a : A) : iPropG Λ Σ :=
    own γ (◯ a).
  Definition auth_inv (φ : A → iPropG Λ Σ) : iPropG Λ Σ :=
    (∃ a, own γ (● a) ★ φ a)%I.
  Definition auth_ctx (N : namespace) (φ : A → iPropG Λ Σ) : iPropG Λ Σ :=
    inv N (auth_inv φ).

  Global Instance auth_own_ne n : Proper (dist n ==> dist n) auth_own.
  Proof. solve_proper. Qed.
  Global Instance auth_own_proper : Proper ((≡) ==> (⊣⊢)) auth_own.
  Proof. solve_proper. Qed.
  Global Instance auth_own_timeless a : TimelessP (auth_own a).
  Proof. apply _. Qed.
  Global Instance auth_inv_ne n : 
    Proper (pointwise_relation A (dist n) ==> dist n) (auth_inv).
  Proof. solve_proper. Qed.
  Global Instance auth_ctx_ne n N :
    Proper (pointwise_relation A (dist n) ==> dist n) (auth_ctx N).
  Proof. solve_proper. Qed.
  Global Instance auth_ctx_persistent N φ : PersistentP (auth_ctx N φ).
  Proof. apply _. Qed.
End definitions.

Typeclasses Opaque auth_own auth_ctx.
Instance: Params (@auth_inv) 5.
Instance: Params (@auth_own) 5.
Instance: Params (@auth_ctx) 6.

Section auth.
  Context `{AuthI : authG Λ Σ A}.
  Context (φ : A → iPropG Λ Σ) {φ_proper : Proper ((≡) ==> (⊣⊢)) φ}.
  Implicit Types N : namespace.
  Implicit Types P Q R : iPropG Λ Σ.
  Implicit Types a b : A.
  Implicit Types γ : gname.

  Lemma auth_own_op γ a b : auth_own γ (a ⋅ b) ⊣⊢ auth_own γ a ★ auth_own γ b.
  Proof. by rewrite /auth_own -own_op auth_frag_op. Qed.

  Lemma auth_own_mono γ a b : a ≼ b → auth_own γ b ⊢ auth_own γ a.
  Proof. intros [? ->]. by rewrite auth_own_op sep_elim_l. Qed.

  Global Instance auth_own_persistent γ a :
    Persistent a → PersistentP (auth_own γ a).
  Proof. rewrite /auth_own. apply _. Qed.

  Lemma auth_own_valid γ a : auth_own γ a ⊢ ✓ a.
  Proof. by rewrite /auth_own own_valid auth_validI. Qed.

  Lemma auth_alloc_strong N E a (G : gset gname) :
    ✓ a → nclose N ⊆ E →
    ▷ φ a ={E}=> ∃ γ, ■(γ ∉ G) ∧ auth_ctx γ N φ ∧ auth_own γ a.
  Proof.
    iIntros {??} "Hφ". rewrite /auth_own /auth_ctx.
    iPvs (own_alloc_strong (Auth (Excl' a) a) _ G) as {γ} "[% Hγ]"; first done.
    iRevert "Hγ"; rewrite auth_both_op; iIntros "[Hγ Hγ']".
    iPvs (inv_alloc N _ (auth_inv γ φ) with "[-Hγ']"); first done.
    { iNext. iExists a. by iFrame. }
    iPvsIntro; iExists γ. iSplit; first by iPureIntro. by iFrame.
  Qed.

  Lemma auth_alloc N E a :
    ✓ a → nclose N ⊆ E →
    ▷ φ a ={E}=> ∃ γ, auth_ctx γ N φ ∧ auth_own γ a.
  Proof.
    iIntros {??} "Hφ".
    iPvs (auth_alloc_strong N E a ∅ with "Hφ") as {γ} "[_ ?]"; [done..|].
    by iExists γ.
  Qed.

  Lemma auth_empty γ E : True ={E}=> auth_own γ ∅.
  Proof. by rewrite -own_empty. Qed.

  Context {V} (fsa : FSA Λ (globalF Σ) V) `{!FrameShiftAssertion fsaV fsa}.

  Lemma auth_fsa E N (Ψ : V → iPropG Λ Σ) γ a :
    fsaV → nclose N ⊆ E →
    auth_ctx γ N φ ★ ▷ auth_own γ a ★ (∀ af,
      ■ ✓ (a ⋅ af) ★ ▷ φ (a ⋅ af) -★
      fsa (E ∖ nclose N) (λ x, ∃ b,
        ■ (a ~l~> b @ Some af) ★ ▷ φ (b ⋅ af) ★ (auth_own γ b -★ Ψ x)))
     ⊢ fsa E Ψ.
  Proof.
    iIntros {??} "(#? & Hγf & HΨ)". rewrite /auth_ctx /auth_own.
    iInv N as {a'} "[Hγ Hφ]".
    iTimeless "Hγ"; iTimeless "Hγf"; iCombine "Hγ" "Hγf" as "Hγ".
    iDestruct (own_valid _ with "#Hγ") as "Hvalid".
    iDestruct (auth_validI _ with "Hvalid") as "[Ha' %]"; simpl; iClear "Hvalid".
    iDestruct "Ha'" as {af} "Ha'"; iDestruct "Ha'" as %Ha'.
    rewrite ->(left_id _ _) in Ha'; setoid_subst.
    iApply pvs_fsa_fsa; iApply fsa_wand_r; iSplitL "HΨ Hφ".
    { iApply "HΨ"; by iSplit. }
    iIntros {v}; iDestruct 1 as {b} "(% & Hφ & HΨ)".
    iPvs (own_update _ with "Hγ") as "[Hγ Hγf]"; first eapply auth_update; eauto.
    iPvsIntro. iSplitL "Hφ Hγ"; last by iApply "HΨ".
    iNext. iExists (b ⋅ af). by iFrame.
  Qed.
End auth.
