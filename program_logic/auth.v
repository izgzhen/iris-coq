From iris.algebra Require Export auth upred_tactics.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.proofmode Require Import invariants ghost_ownership.
Import uPred.

(* The CMRA we need. *)
Class authG Λ Σ (A : cmraT) `{Empty A} := AuthG {
  auth_inG :> inG Λ Σ (authR A);
  auth_identity :> CMRAUnit A;
  auth_timeless :> CMRADiscrete A;
}.
(* The Functor we need. *)
Definition authGF (A : cmraT) : gFunctor := GFunctor (constRF (authR A)).
(* Show and register that they match. *)
Instance authGF_inGF (A : cmraT) `{inGF Λ Σ (authGF A)}
  `{CMRAUnit A, CMRADiscrete A} : authG Λ Σ A.
Proof. split; try apply _. apply: inGF_inG. Qed.

Section definitions.
  Context `{authG Λ Σ A} (γ : gname).
  Definition auth_own  (a : A) : iPropG Λ Σ :=
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
  Global Instance auth_ctx_persistent N φ : PersistentP (auth_ctx N φ).
  Proof. apply _. Qed.
End definitions.

Typeclasses Opaque auth_own auth_ctx.
Instance: Params (@auth_inv) 6.
Instance: Params (@auth_own) 6.
Instance: Params (@auth_ctx) 7.

Section auth.
  Context `{AuthI : authG Λ Σ A}.
  Context (φ : A → iPropG Λ Σ) {φ_proper : Proper ((≡) ==> (⊣⊢)) φ}.
  Implicit Types N : namespace.
  Implicit Types P Q R : iPropG Λ Σ.
  Implicit Types a b : A.
  Implicit Types γ : gname.

  Lemma auth_own_op γ a b :
    auth_own γ (a ⋅ b) ⊣⊢ (auth_own γ a ★ auth_own γ b).
  Proof. by rewrite /auth_own -own_op auth_frag_op. Qed.
  Lemma auth_own_valid γ a : auth_own γ a ⊢ ✓ a.
  Proof. by rewrite /auth_own own_valid auth_validI. Qed.

  Lemma auth_alloc N E a :
    ✓ a → nclose N ⊆ E →
    ▷ φ a ⊢ (|={E}=> ∃ γ, auth_ctx γ N φ ∧ auth_own γ a).
  Proof.
    iIntros {??} "Hφ". rewrite /auth_own /auth_ctx.
    iPvs (own_alloc (Auth (Excl a) a)) as {γ} "Hγ"; first done.
    iRevert "Hγ"; rewrite auth_both_op; iIntros "[Hγ Hγ']".
    iPvs (inv_alloc N _ (auth_inv γ φ) with "-[Hγ']"); first done.
    { iNext. iExists a. by iFrame "Hφ". }
    iPvsIntro; iExists γ; by iFrame "Hγ'".
  Qed.

  Lemma auth_empty γ E : True ⊢ |={E}=> auth_own γ ∅.
  Proof. by rewrite -own_empty. Qed.

  Context {V} (fsa : FSA Λ (globalF Σ) V) `{!FrameShiftAssertion fsaV fsa}.

  Lemma auth_fsa E N (Ψ : V → iPropG Λ Σ) γ a :
    fsaV → nclose N ⊆ E →
    (auth_ctx γ N φ ★ ▷ auth_own γ a ★ ∀ a',
      ■ ✓ (a ⋅ a') ★ ▷ φ (a ⋅ a') -★
      fsa (E ∖ nclose N) (λ x, ∃ L Lv (Hup : LocalUpdate Lv L),
        ■ (Lv a ∧ ✓ (L a ⋅ a')) ★ ▷ φ (L a ⋅ a') ★
        (auth_own γ (L a) -★ Ψ x)))
     ⊢ fsa E Ψ.
  Proof.
    iIntros {??} "(#? & Hγf & HΨ)". rewrite /auth_ctx /auth_own.
    iInv N as {a'} "[Hγ Hφ]".
    iTimeless "Hγ"; iTimeless "Hγf"; iCombine "Hγ" "Hγf" as "Hγ".
    iDestruct (own_valid _ with "Hγ !") as "Hvalid".
    iDestruct (auth_validI _ with "Hvalid") as "[Ha' %]"; simpl; iClear "Hvalid".
    iDestruct "Ha'" as {b} "Ha'"; iDestruct "Ha'" as %Ha'.
    rewrite ->(left_id _ _) in Ha'; setoid_subst.
    iApply pvs_fsa_fsa; iApply fsa_wand_r; iSplitL "HΨ Hφ".
    { iApply "HΨ"; by iSplit. }
    iIntros {v} "HL". iDestruct "HL" as {L Lv ?} "(% & Hφ & HΨ)".
    iPvs (own_update _ with "Hγ") as "[Hγ Hγf]".
    { apply (auth_local_update_l L); tauto. }
    iPvsIntro. iSplitL "Hφ Hγ"; last by iApply "HΨ".
    iNext. iExists (L a ⋅ b). by iFrame "Hφ".
  Qed.

  Lemma auth_fsa' L `{!LocalUpdate Lv L} E N (Ψ : V → iPropG Λ Σ) γ a :
    fsaV → nclose N ⊆ E →
    (auth_ctx γ N φ ★ ▷ auth_own γ a ★ (∀ a',
      ■ ✓ (a ⋅ a') ★ ▷ φ (a ⋅ a') -★
      fsa (E ∖ nclose N) (λ x,
        ■ (Lv a ∧ ✓ (L a ⋅ a')) ★ ▷ φ (L a ⋅ a') ★
        (auth_own γ (L a) -★ Ψ x))))
    ⊢ fsa E Ψ.
  Proof.
    iIntros {??} "(#Ha & Hγf & HΨ)"; iApply (auth_fsa E N Ψ γ a); auto.
    iFrame "Ha Hγf". iIntros {a'} "H".
    iApply fsa_wand_r; iSplitL; first by iApply "HΨ".
    iIntros {v} "?"; by iExists L, Lv, _.
  Qed.
End auth.
