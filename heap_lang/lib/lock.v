From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import invariants tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl.

Definition newlock : val := λ: <>, ref #false.
Definition acquire : val :=
  rec: "acquire" "l" :=
    if: CAS "l" #false #true then #() else "acquire" "l".
Definition release : val := λ: "l", "l" <- #false.
Global Opaque newlock acquire release.

(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitC) }.
Definition lockΣ : gFunctors := #[GFunctor (constRF (exclR unitC))].

Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section proof.
Context `{!heapG Σ, !lockG Σ} (N : namespace).

Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
  (∃ b : bool, l ↦ #b ★ if b then True else own γ (Excl ()) ★ R)%I.

Definition is_lock (l : loc) (R : iProp Σ) : iProp Σ :=
  (∃ γ, heapN ⊥ N ∧ heap_ctx ∧ inv N (lock_inv γ l R))%I.

Definition locked (l : loc) (R : iProp Σ) : iProp Σ :=
  (∃ γ, heapN ⊥ N ∧ heap_ctx ∧
        inv N (lock_inv γ l R) ∧ own γ (Excl ()))%I.

Global Instance lock_inv_ne n γ l : Proper (dist n ==> dist n) (lock_inv γ l).
Proof. solve_proper. Qed.
Global Instance is_lock_ne n l : Proper (dist n ==> dist n) (is_lock l).
Proof. solve_proper. Qed.
Global Instance locked_ne n l : Proper (dist n ==> dist n) (locked l).
Proof. solve_proper. Qed.

(** The main proofs. *)
Global Instance is_lock_persistent l R : PersistentP (is_lock l R).
Proof. apply _. Qed.

Lemma locked_is_lock l R : locked l R ⊢ is_lock l R.
Proof. rewrite /is_lock. iDestruct 1 as (γ) "(?&?&?&_)"; eauto. Qed.

Lemma newlock_spec (R : iProp Σ) Φ :
  heapN ⊥ N →
  heap_ctx ★ R ★ (∀ l, is_lock l R -★ Φ #l) ⊢ WP newlock #() {{ Φ }}.
Proof.
  iIntros (?) "(#Hh & HR & HΦ)". rewrite /newlock.
  wp_seq. wp_alloc l as "Hl".
  iShift (own_alloc (Excl ())) as (γ) "Hγ"; first done.
  iShift (inv_alloc N _ (lock_inv γ l R) with "[-HΦ]") as "#?".
  { iIntros "!>". iExists false. by iFrame. }
  iShiftIntro. iApply "HΦ". iExists γ; eauto.
Qed.

Lemma acquire_spec l R (Φ : val → iProp Σ) :
  is_lock l R ★ (locked l R -★ R -★ Φ #()) ⊢ WP acquire #l {{ Φ }}.
Proof.
  iIntros "[Hl HΦ]". iDestruct "Hl" as (γ) "(%&#?&#?)".
  iLöb as "IH". wp_rec. wp_bind (CAS _ _ _)%E.
  iInv N as ([]) "[Hl HR]" "Hclose".
  - wp_cas_fail. iShift ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
    iShiftIntro. wp_if. by iApply "IH".
  - wp_cas_suc. iDestruct "HR" as "[Hγ HR]".
    iShift ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
    iShiftIntro. wp_if. iApply ("HΦ" with "[-HR] HR"). iExists γ; eauto.
Qed.

Lemma release_spec R l (Φ : val → iProp Σ) :
  locked l R ★ R ★ Φ #() ⊢ WP release #l {{ Φ }}.
Proof.
  iIntros "(Hl&HR&HΦ)"; iDestruct "Hl" as (γ) "(% & #? & #? & Hγ)".
  rewrite /release. wp_let. iInv N as (b) "[Hl _]" "Hclose".
  wp_store. iFrame "HΦ". iApply "Hclose". iNext. iExists false. by iFrame.
Qed.
End proof.
