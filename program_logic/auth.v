From iris.program_logic Require Export invariants.
From iris.algebra Require Export auth.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
Import uPred.

(* The CMRA we need. *)
Class authG Σ (A : ucmraT) := AuthG {
  auth_inG :> inG Σ (authR A);
  auth_discrete :> CMRADiscrete A;
}.
Definition authΣ (A : ucmraT) : gFunctors := #[ GFunctor (constRF (authR A)) ].

Instance subG_authΣ Σ A : subG (authΣ A) Σ → CMRADiscrete A → authG Σ A.
Proof. intros ?%subG_inG ?. by split. Qed.

Section definitions.
  Context `{irisG Λ Σ, authG Σ A} (γ : gname).
  Definition auth_own (a : A) : iProp Σ :=
    own γ (◯ a).
  Definition auth_inv (φ : A → iProp Σ) : iProp Σ :=
    (∃ a, own γ (● a) ★ φ a)%I.
  Definition auth_ctx (N : namespace) (φ : A → iProp Σ) : iProp Σ :=
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
Instance: Params (@auth_inv) 6.
Instance: Params (@auth_own) 6.
Instance: Params (@auth_ctx) 7.

Section auth.
  Context `{irisG Λ Σ, authG Σ A}.
  Context (φ : A → iProp Σ) {φ_proper : Proper ((≡) ==> (⊣⊢)) φ}.
  Implicit Types N : namespace.
  Implicit Types P Q R : iProp Σ.
  Implicit Types a b : A.
  Implicit Types γ : gname.

  Lemma auth_own_op γ a b : auth_own γ (a ⋅ b) ⊣⊢ auth_own γ a ★ auth_own γ b.
  Proof. by rewrite /auth_own -own_op auth_frag_op. Qed.

  Global Instance from_sep_own_authM γ a b :
    FromSep (auth_own γ (a ⋅ b)) (auth_own γ a) (auth_own γ b) | 90.
  Proof. by rewrite /FromSep auth_own_op. Qed.

  Lemma auth_own_mono γ a b : a ≼ b → auth_own γ b ⊢ auth_own γ a.
  Proof. intros [? ->]. by rewrite auth_own_op sep_elim_l. Qed.

  Global Instance auth_own_persistent γ a :
    Persistent a → PersistentP (auth_own γ a).
  Proof. rewrite /auth_own. apply _. Qed.

  Lemma auth_own_valid γ a : auth_own γ a ⊢ ✓ a.
  Proof. by rewrite /auth_own own_valid auth_validI. Qed.

  Lemma auth_alloc_strong N E a (G : gset gname) :
    ✓ a → ▷ φ a ={E}=> ∃ γ, ■ (γ ∉ G) ∧ auth_ctx γ N φ ∧ auth_own γ a.
  Proof.
    iIntros (?) "Hφ". rewrite /auth_own /auth_ctx.
    iVs (own_alloc_strong (Auth (Excl' a) a) G) as (γ) "[% Hγ]"; first done.
    iRevert "Hγ"; rewrite auth_both_op; iIntros "[Hγ Hγ']".
    iVs (inv_alloc N _ (auth_inv γ φ) with "[-Hγ']").
    { iNext. iExists a. by iFrame. }
    iVsIntro; iExists γ. iSplit; first by iPureIntro. by iFrame.
  Qed.

  Lemma auth_alloc N E a :
    ✓ a → ▷ φ a ={E}=> ∃ γ, auth_ctx γ N φ ∧ auth_own γ a.
  Proof.
    iIntros (?) "Hφ".
    iVs (auth_alloc_strong N E a ∅ with "Hφ") as (γ) "[_ ?]"; eauto.
  Qed.

  Lemma auth_empty γ : True =r=> auth_own γ ∅.
  Proof. by rewrite /auth_own -own_empty. Qed.

  Lemma auth_open E N γ a :
    nclose N ⊆ E →
    auth_ctx γ N φ ★ ▷ auth_own γ a ={E,E∖N}=> ∃ af,
      ■ ✓ (a ⋅ af) ★ ▷ φ (a ⋅ af) ★ ∀ b,
      ■ (a ~l~> b @ Some af) ★ ▷ φ (b ⋅ af) ={E∖N,E}=★ auth_own γ b.
  Proof.
    iIntros (?) "(#? & >Hγf)". rewrite /auth_ctx /auth_own.
    iInv N as (a') "[>Hγ Hφ]" "Hclose". iCombine "Hγ" "Hγf" as "Hγ".
    iDestruct (own_valid with "Hγ") as % [[af Ha'] ?]%auth_valid_discrete.
    simpl in Ha'; rewrite ->(left_id _ _) in Ha'; setoid_subst.
    iVsIntro. iExists af; iFrame "Hφ"; iSplit; first done.
    iIntros (b) "[% Hφ]".
    iVs (own_update with "Hγ") as "[Hγ Hγf]"; first eapply auth_update; eauto.
    iVs ("Hclose" with "[Hφ Hγ]") as "_"; auto.
    iNext. iExists (b ⋅ af). by iFrame.
  Qed.
End auth.
