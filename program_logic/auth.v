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
  Context {T : Type}.
  Definition auth_own (a : A) : iProp Σ :=
    own γ (◯ a).
  Definition auth_inv (f : T → A) (φ : T → iProp Σ) : iProp Σ :=
    (∃ t, own γ (● f t) ★ φ t)%I.
  Definition auth_ctx (N : namespace) (f : T → A) (φ : T → iProp Σ) : iProp Σ :=
    inv N (auth_inv f φ).

  Global Instance auth_own_ne n : Proper (dist n ==> dist n) auth_own.
  Proof. solve_proper. Qed.
  Global Instance auth_own_proper : Proper ((≡) ==> (⊣⊢)) auth_own.
  Proof. solve_proper. Qed.
  Global Instance auth_own_timeless a : TimelessP (auth_own a).
  Proof. apply _. Qed.
  Global Instance auth_inv_ne: 
    Proper (pointwise_relation T (≡) ==>
            pointwise_relation T (≡) ==> (≡)) (auth_inv).
  Proof. solve_proper. Qed.
  Global Instance auth_ctx_ne N :
    Proper (pointwise_relation T (≡) ==>
            pointwise_relation T (≡) ==> (≡)) (auth_ctx N).
  Proof. solve_proper. Qed.
  Global Instance auth_ctx_persistent N f φ : PersistentP (auth_ctx N f φ).
  Proof. apply _. Qed.
End definitions.

Typeclasses Opaque auth_own auth_inv auth_ctx.
(* TODO: Not sure what to put here. *)
Instance: Params (@auth_inv) 5.
Instance: Params (@auth_own) 4.
Instance: Params (@auth_ctx) 7.

Section auth.
  Context `{irisG Λ Σ, authG Σ A}.
  Context {T : Type} `{!Inhabited T}.
  Context (f : T → A) (φ : T → iProp Σ).
  Implicit Types N : namespace.
  Implicit Types P Q R : iProp Σ.
  Implicit Types a b : A.
  Implicit Types t u : T.
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

  Lemma auth_alloc_strong N E t (G : gset gname) :
    ✓ (f t) → ▷ φ t ={E}=> ∃ γ, ■ (γ ∉ G) ∧ auth_ctx γ N f φ ∧ auth_own γ (f t).
  Proof.
    iIntros (?) "Hφ". rewrite /auth_own /auth_ctx.
    iVs (own_alloc_strong (Auth (Excl' (f t)) (f t)) G) as (γ) "[% Hγ]"; first done.
    iRevert "Hγ"; rewrite auth_both_op; iIntros "[Hγ Hγ']".
    iVs (inv_alloc N _ (auth_inv γ f φ) with "[-Hγ']").
    { iNext. rewrite /auth_inv. iExists t. by iFrame. }
    iVsIntro; iExists γ. iSplit; first by iPureIntro. by iFrame.
  Qed.

  Lemma auth_alloc N E t :
    ✓ (f t) → ▷ φ t ={E}=> ∃ γ, auth_ctx γ N f φ ∧ auth_own γ (f t).
  Proof.
    iIntros (?) "Hφ".
    iVs (auth_alloc_strong N E t ∅ with "Hφ") as (γ) "[_ ?]"; eauto.
  Qed.

  Lemma auth_empty γ : True =r=> auth_own γ ∅.
  Proof. by rewrite /auth_own -own_empty. Qed.

  Lemma auth_acc E γ a :
    ▷ auth_inv γ f φ ★ auth_own γ a ={E}=> ∃ t,
      ■ (a ≼ f t) ★ ▷ φ t ★ ∀ u b,
      ■ ((f t, a) ~l~> (f u, b)) ★ ▷ φ u ={E}=★ ▷ auth_inv γ f φ ★ auth_own γ b.
  Proof.
    iIntros "(Hinv & Hγf)". rewrite /auth_inv /auth_own.
    iDestruct "Hinv" as (t) "[>Hγa Hφ]". iVsIntro.
    iExists t. iCombine "Hγa" "Hγf" as "Hγ".
    iDestruct (own_valid with "Hγ") as % [? ?]%auth_valid_discrete_2.
    iSplit; first done. iFrame. iIntros (u b) "[% Hφ]".
    iVs (own_update with "Hγ") as "[Hγa Hγf]".
    { eapply auth_update. eassumption. }
    iVsIntro. iFrame. iExists u. iFrame.
  Qed.

  Lemma auth_open E N γ a :
    nclose N ⊆ E →
    auth_ctx γ N f φ ★ auth_own γ a ={E,E∖N}=> ∃ t,
      ■ (a ≼ f t) ★ ▷ φ t ★ ∀ u b,
      ■ ((f t, a) ~l~> (f u, b)) ★ ▷ φ u ={E∖N,E}=★ auth_own γ b.
  Proof.
    iIntros (?) "[#? Hγf]". rewrite /auth_ctx. iInv N as "Hinv" "Hclose".
    (* The following is essentially a very trivial composition of the accessors
       [auth_acc] and [inv_open] -- but since we don't have any good support
       for that currently, this gets more tedious than it should, with us having
       to unpack and repack various proofs.
       TODO: Make this mostly automatic, by supporting "opening accessors
       around accessors". *)
    iVs (auth_acc with "[Hinv Hγf]") as (t) "(?&?&HclAuth)"; first by iFrame.
    iVsIntro. iExists t. iFrame. iIntros (u b) "H".
    iVs ("HclAuth" $! u b with "H") as "(Hinv & ?)". by iVs ("Hclose" with "Hinv").
  Qed.
End auth.
