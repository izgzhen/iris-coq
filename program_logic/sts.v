From iris.algebra Require Export sts upred_tactics.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.proofmode Require Import invariants ghost_ownership.
Import uPred.

(** The CMRA we need. *)
Class stsG Λ Σ (sts : stsT) := StsG {
  sts_inG :> inG Λ Σ (stsR sts);
  sts_inhabited :> Inhabited (sts.state sts);
}.
Coercion sts_inG : stsG >-> inG.
(** The Functor we need. *)
Definition stsGF (sts : stsT) : gFunctor := GFunctor (constRF (stsR sts)).
(* Show and register that they match. *)
Instance inGF_stsG sts `{inGF Λ Σ (stsGF sts)}
  `{Inhabited (sts.state sts)} : stsG Λ Σ sts.
Proof. split; try apply _. apply: inGF_inG. Qed.

Section definitions.
  Context `{i : stsG Λ Σ sts} (γ : gname).
  Definition sts_ownS (S : sts.states sts) (T : sts.tokens sts) : iPropG Λ Σ:=
    own γ (sts_frag S T).
  Definition sts_own (s : sts.state sts) (T : sts.tokens sts) : iPropG Λ Σ :=
    own γ (sts_frag_up s T).
  Definition sts_inv (φ : sts.state sts → iPropG Λ Σ) : iPropG Λ Σ :=
    (∃ s, own γ (sts_auth s ∅) ★ φ s)%I.
  Definition sts_ctx (N : namespace) (φ: sts.state sts → iPropG Λ Σ) : iPropG Λ Σ :=
    inv N (sts_inv φ).

  Global Instance sts_inv_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) sts_inv.
  Proof. solve_proper. Qed.
  Global Instance sts_inv_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) sts_inv.
  Proof. solve_proper. Qed.
  Global Instance sts_ownS_proper : Proper ((≡) ==> (≡) ==> (⊣⊢)) sts_ownS.
  Proof. solve_proper. Qed.
  Global Instance sts_own_proper s : Proper ((≡) ==> (⊣⊢)) (sts_own s).
  Proof. solve_proper. Qed.
  Global Instance sts_ctx_ne n N :
    Proper (pointwise_relation _ (dist n) ==> dist n) (sts_ctx N).
  Proof. solve_proper. Qed.
  Global Instance sts_ctx_proper N :
    Proper (pointwise_relation _ (≡) ==> (⊣⊢)) (sts_ctx N).
  Proof. solve_proper. Qed.
  Global Instance sts_ctx_persistent N φ : PersistentP (sts_ctx N φ).
  Proof. apply _. Qed.
End definitions.

Typeclasses Opaque sts_own sts_ownS sts_ctx.
Instance: Params (@sts_inv) 5.
Instance: Params (@sts_ownS) 5.
Instance: Params (@sts_own) 6.
Instance: Params (@sts_ctx) 6.

Section sts.
  Context `{stsG Λ Σ sts} (φ : sts.state sts → iPropG Λ Σ).
  Implicit Types N : namespace.
  Implicit Types P Q R : iPropG Λ Σ.
  Implicit Types γ : gname.
  Implicit Types S : sts.states sts.
  Implicit Types T : sts.tokens sts.

  (* The same rule as implication does *not* hold, as could be shown using
     sts_frag_included. *)
  Lemma sts_ownS_weaken E γ S1 S2 T1 T2 :
    T2 ⊆ T1 → S1 ⊆ S2 → sts.closed S2 T2 →
    sts_ownS γ S1 T1 ={E}=> sts_ownS γ S2 T2.
  Proof. intros ???. by apply own_update, sts_update_frag. Qed.

  Lemma sts_own_weaken E γ s S T1 T2 :
    T2 ⊆ T1 → s ∈ S → sts.closed S T2 →
    sts_own γ s T1 ={E}=> sts_ownS γ S T2.
  Proof. intros ???. by apply own_update, sts_update_frag_up. Qed.

  Lemma sts_ownS_op γ S1 S2 T1 T2 :
    T1 ⊥ T2 → sts.closed S1 T1 → sts.closed S2 T2 →
    sts_ownS γ (S1 ∩ S2) (T1 ∪ T2) ⊣⊢ (sts_ownS γ S1 T1 ★ sts_ownS γ S2 T2).
  Proof. intros. by rewrite /sts_ownS -own_op sts_op_frag. Qed.

  Lemma sts_alloc E N s :
    nclose N ⊆ E →
    ▷ φ s ={E}=> ∃ γ, sts_ctx γ N φ ∧ sts_own γ s (⊤ ∖ sts.tok s).
  Proof.
    iIntros {?} "Hφ". rewrite /sts_ctx /sts_own.
    iPvs (own_alloc (sts_auth s (⊤ ∖ sts.tok s))) as {γ} "Hγ".
    { apply sts_auth_valid; set_solver. }
    iExists γ; iRevert "Hγ"; rewrite -sts_op_auth_frag_up; iIntros "[Hγ $]".
    iPvs (inv_alloc N _ (sts_inv γ φ) with "[Hφ Hγ]") as "#?"; auto.
    iNext. iExists s. by iFrame.
  Qed.

  Context {V} (fsa : FSA Λ (globalF Σ) V) `{!FrameShiftAssertion fsaV fsa}.

  Lemma sts_fsaS E N (Ψ : V → iPropG Λ Σ) γ S T :
    fsaV → nclose N ⊆ E →
    sts_ctx γ N φ ★ sts_ownS γ S T ★ (∀ s,
      ■ (s ∈ S) ★ ▷ φ s -★
      fsa (E ∖ nclose N) (λ x, ∃ s' T',
        ■ sts.steps (s, T) (s', T') ★ ▷ φ s' ★ (sts_own γ s' T' -★ Ψ x)))
    ⊢ fsa E Ψ.
  Proof.
    iIntros {??} "(#? & Hγf & HΨ)". rewrite /sts_ctx /sts_ownS /sts_inv /sts_own.
    iInv N as {s} "[Hγ Hφ]"; iTimeless "Hγ".
    iCombine "Hγ" "Hγf" as "Hγ"; iDestruct (own_valid with "#Hγ") as %Hvalid.
    assert (s ∈ S) by eauto using sts_auth_frag_valid_inv.
    assert (✓ sts_frag S T) as [??] by eauto using cmra_valid_op_r.
    iRevert "Hγ"; rewrite sts_op_auth_frag //; iIntros "Hγ".
    iApply pvs_fsa_fsa; iApply fsa_wand_r; iSplitL "HΨ Hφ".
    { iApply "HΨ"; by iSplit. }
    iIntros {a} "H"; iDestruct "H" as {s' T'} "(% & Hφ & HΨ)".
    iPvs (own_update with "Hγ") as "Hγ"; first eauto using sts_update_auth.
    iRevert "Hγ"; rewrite -sts_op_auth_frag_up; iIntros "[Hγ Hγf]".
    iPvsIntro; iSplitL "Hφ Hγ"; last by iApply "HΨ".
    iNext; iExists s'; by iFrame.
  Qed.

  Lemma sts_fsa E N (Ψ : V → iPropG Λ Σ) γ s0 T :
    fsaV → nclose N ⊆ E →
    sts_ctx γ N φ ★ sts_own γ s0 T ★ (∀ s,
      ■ (s ∈ sts.up s0 T) ★ ▷ φ s -★
      fsa (E ∖ nclose N) (λ x, ∃ s' T',
        ■ (sts.steps (s, T) (s', T')) ★ ▷ φ s' ★
        (sts_own γ s' T' -★ Ψ x)))
    ⊢ fsa E Ψ.
  Proof. by apply sts_fsaS. Qed.
End sts.
