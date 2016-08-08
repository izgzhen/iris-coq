From iris.program_logic Require Export pviewshifts.
From iris.algebra Require Export sts.
From iris.proofmode Require Import invariants.
Import uPred.

(** The CMRA we need. *)
Class stsG Σ (sts : stsT) := StsG {
  sts_inG :> inG Σ (stsR sts);
  sts_inhabited :> Inhabited (sts.state sts);
}.

(* The global functor we need and register that they match. *)
Definition stsΣ (sts : stsT) : gFunctors := #[ GFunctor (constRF (stsR sts)) ].
Instance subG_stsΣ Σ sts :
  subG (stsΣ sts) Σ → Inhabited (sts.state sts) → stsG Σ sts.
Proof. intros ?%subG_inG ?. by split. Qed.

Section definitions.
  Context `{irisG Λ Σ, stsG Σ sts} (γ : gname).

  Definition sts_ownS (S : sts.states sts) (T : sts.tokens sts) : iProp Σ :=
    own γ (sts_frag S T).
  Definition sts_own (s : sts.state sts) (T : sts.tokens sts) : iProp Σ :=
    own γ (sts_frag_up s T).
  Definition sts_inv (φ : sts.state sts → iProp Σ) : iProp Σ :=
    (∃ s, own γ (sts_auth s ∅) ★ φ s)%I.
  Definition sts_ctx (N : namespace) (φ: sts.state sts → iProp Σ) : iProp Σ :=
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
  Context `{irisG Λ Σ, stsG Σ sts} (φ : sts.state sts → iProp Σ).
  Implicit Types N : namespace.
  Implicit Types P Q R : iProp Σ.
  Implicit Types γ : gname.
  Implicit Types S : sts.states sts.
  Implicit Types T : sts.tokens sts.

  (* The same rule as implication does *not* hold, as could be shown using
     sts_frag_included. *)
  Lemma sts_ownS_weaken γ S1 S2 T1 T2 :
    T2 ⊆ T1 → S1 ⊆ S2 → sts.closed S2 T2 →
    sts_ownS γ S1 T1 =r=> sts_ownS γ S2 T2.
  Proof. intros ???. by apply own_update, sts_update_frag. Qed.

  Lemma sts_own_weaken γ s S T1 T2 :
    T2 ⊆ T1 → s ∈ S → sts.closed S T2 →
    sts_own γ s T1 =r=> sts_ownS γ S T2.
  Proof. intros ???. by apply own_update, sts_update_frag_up. Qed.

  Lemma sts_ownS_op γ S1 S2 T1 T2 :
    T1 ⊥ T2 → sts.closed S1 T1 → sts.closed S2 T2 →
    sts_ownS γ (S1 ∩ S2) (T1 ∪ T2) ⊣⊢ (sts_ownS γ S1 T1 ★ sts_ownS γ S2 T2).
  Proof. intros. by rewrite /sts_ownS -own_op sts_op_frag. Qed.

  Lemma sts_alloc E N s :
    ▷ φ s ={E}=> ∃ γ, sts_ctx γ N φ ∧ sts_own γ s (⊤ ∖ sts.tok s).
  Proof.
    iIntros "Hφ". rewrite /sts_ctx /sts_own.
    iVs (own_alloc (sts_auth s (⊤ ∖ sts.tok s))) as (γ) "Hγ".
    { apply sts_auth_valid; set_solver. }
    iExists γ; iRevert "Hγ"; rewrite -sts_op_auth_frag_up; iIntros "[Hγ $]".
    iVs (inv_alloc N _ (sts_inv γ φ) with "[Hφ Hγ]") as "#?"; auto.
    iNext. iExists s. by iFrame.
  Qed.

  Lemma sts_openS E N γ S T :
    nclose N ⊆ E →
    sts_ctx γ N φ ★ sts_ownS γ S T ={E,E∖N}=> ∃ s,
      ■ (s ∈ S) ★ ▷ φ s ★ ∀ s' T',
      ■ sts.steps (s, T) (s', T') ★ ▷ φ s' ={E∖N,E}=★ sts_own γ s' T'.
  Proof.
    iIntros (?) "[#? Hγf]". rewrite /sts_ctx /sts_ownS /sts_inv /sts_own.
    iInv N as (s) "[>Hγ Hφ]" "Hclose".
    iCombine "Hγ" "Hγf" as "Hγ"; iDestruct (own_valid with "#Hγ") as %Hvalid.
    assert (s ∈ S) by eauto using sts_auth_frag_valid_inv.
    assert (✓ sts_frag S T) as [??] by eauto using cmra_valid_op_r.
    rewrite sts_op_auth_frag //.
    iVsIntro; iExists s; iSplit; [done|]; iFrame "Hφ".
    iIntros (s' T') "[% Hφ]".
    iVs (own_update with "Hγ") as "Hγ"; first eauto using sts_update_auth.
    iRevert "Hγ"; rewrite -sts_op_auth_frag_up; iIntros "[Hγ $]".
    iApply "Hclose". iNext; iExists s'; by iFrame.
  Qed.

  Lemma sts_open E N γ s0 T :
    nclose N ⊆ E →
    sts_ctx γ N φ ★ sts_own γ s0 T ={E,E∖N}=> ∃ s,
      ■ (s ∈ sts.up s0 T) ★ ▷ φ s ★ ∀ s' T',
      ■ (sts.steps (s, T) (s', T')) ★ ▷ φ s' ={E∖N,E}=★ sts_own γ s' T'.
  Proof. by apply sts_openS. Qed.
End sts.
