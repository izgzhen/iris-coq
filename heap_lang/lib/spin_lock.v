From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl.
From iris.heap_lang.lib Require Import lock.

Definition newlock : val := λ: <>, ref #false.
Definition try_acquire : val := λ: "l", CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".
Definition release : val := λ: "l", "l" <- #false.
Global Opaque newlock try_acquire acquire release.

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

  Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: loc, heapN ⊥ N ∧ heap_ctx ∧ lk = #l ∧ inv N (lock_inv γ l R))%I.

  Definition locked (γ : gname): iProp Σ := own γ (Excl ()).

  Lemma locked_exclusive (γ : gname) : locked γ ★ locked γ ⊢ False.
  Proof. rewrite /locked own_valid_2. by iIntros (?). Qed.

  Global Instance lock_inv_ne n γ l : Proper (dist n ==> dist n) (lock_inv γ l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne n l : Proper (dist n ==> dist n) (is_lock γ l).
  Proof. solve_proper. Qed.

  (** The main proofs. *)
  Global Instance is_lock_persistent γ l R : PersistentP (is_lock γ l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : TimelessP (locked γ).
  Proof. apply _. Qed.

  Lemma newlock_spec (R : iProp Σ) Φ :
    heapN ⊥ N →
    heap_ctx ★ R ★ (∀ lk γ, is_lock γ lk R -★ Φ lk) ⊢ WP newlock #() {{ Φ }}.
  Proof.
    iIntros (?) "(#Hh & HR & HΦ)". rewrite /newlock /=.
    wp_seq. wp_alloc l as "Hl".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (lock_inv γ l R) with "[-HΦ]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iModIntro. iApply "HΦ". iExists l. eauto.
  Qed.

  Lemma try_acquire_spec γ lk R (Φ: val → iProp Σ) :
    is_lock γ lk R ★ ((locked γ -★ R -★ Φ #true) ∧ Φ #false)
    ⊢ WP try_acquire lk {{ Φ }}.
  Proof.
    iIntros "[#Hl HΦ]". iDestruct "Hl" as (l) "(% & #? & % & #?)". subst.
    wp_rec. iInv N as ([]) "[Hl HR]" "Hclose".
    - wp_cas_fail. iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iModIntro. iDestruct "HΦ" as "[_ HΦ]". iApply "HΦ".
    - wp_cas_suc. iDestruct "HR" as "[Hγ HR]".
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iModIntro. iDestruct "HΦ" as "[HΦ _]". rewrite /locked. by iApply ("HΦ" with "Hγ HR").
  Qed.

  Lemma acquire_spec γ lk R (Φ : val → iProp Σ) :
    is_lock γ lk R ★ (locked γ -★ R -★ Φ #()) ⊢ WP acquire lk {{ Φ }}.
  Proof.
    iIntros "[#Hl HΦ]". iLöb as "IH". wp_rec. wp_bind (try_acquire _).
    iApply try_acquire_spec. iFrame "#". iSplit.
    - iIntros "Hlked HR". wp_if. iModIntro. iApply ("HΦ" with "Hlked HR").
    - wp_if. iApply ("IH" with "HΦ").
  Qed.

  Lemma release_spec γ lk R (Φ : val → iProp Σ) :
    is_lock γ lk R ★ locked γ ★ R ★ Φ #() ⊢ WP release lk {{ Φ }}.
  Proof.
    iIntros "(Hlock & Hlocked & HR & HΦ)".
    iDestruct "Hlock" as (l) "(% & #? & % & #?)". subst.
    rewrite /release /=. wp_let. iInv N as (b) "[Hl _]" "Hclose".
    wp_store. iFrame "HΦ". iApply "Hclose". iNext. iExists false. by iFrame.
  Qed.

End proof.

Definition spin_lock `{!heapG Σ, !lockG Σ} : lock Σ :=
  {| lock.locked_exclusive := locked_exclusive; lock.newlock_spec := newlock_spec;
     lock.acquire_spec := acquire_spec; lock.release_spec := release_spec |}.
