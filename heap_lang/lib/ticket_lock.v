From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.program_logic Require Import auth.
From iris.proofmode Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import gset.
From iris.heap_lang.lib Require Import lock.
Import uPred.

Definition wait_loop: val :=
  rec: "wait_loop" "x" "lock" :=
    let: "o" := !(Fst "lock") in
    if: "x" = "o"
      then #() (* my turn *)
      else "wait_loop" "x" "lock".

Definition newlock : val := λ: <>, ((* owner *) ref #0, (* next *) ref #0).

Definition acquire : val :=
  rec: "acquire" "lock" :=
    let: "n" := !(Snd "lock") in
    if: CAS (Snd "lock") "n" ("n" + #1)
      then wait_loop "n" "lock"
      else "acquire" "lock".

Definition release : val :=
  rec: "release" "lock" :=
    let: "o" := !(Fst "lock") in
    if: CAS (Fst "lock") "o" ("o" + #1)
      then #()
      else "release" "lock".

Global Opaque newlock acquire release wait_loop.

(** The CMRAs we need. *)
Class tlockG Σ := TlockG {
   tlock_G :> authG Σ (gset_disjUR nat);
   tlock_exclG  :> inG Σ (exclR unitC)
}.
Definition tlockΣ : gFunctors :=
  #[authΣ (gset_disjUR nat); GFunctor (constRF (exclR unitC))].

Instance subG_tlockΣ {Σ} : subG tlockΣ Σ → tlockG Σ.
Proof. intros [? [?%subG_inG _]%subG_inv]%subG_inv. split; apply _. Qed.

Section proof.
  Context `{!heapG Σ, !tlockG Σ} (N : namespace).

  Definition tickets_inv (n: nat) (gs: gset_disjUR nat) : iProp Σ :=
    (gs = GSet (seq_set 0 n))%I.

  Definition lock_inv (γ1 γ2: gname) (lo ln: loc) (R : iProp Σ) : iProp Σ :=
    (∃ (o n: nat),
       lo ↦ #o ★ ln ↦ #n ★
       auth_inv γ1 (tickets_inv n) ★
       ((own γ2 (Excl ()) ★  R) ∨ auth_own γ1 (GSet {[ o ]})))%I.

  Definition is_lock (γs: gname * gname) (l: val) (R: iProp Σ) : iProp Σ :=
    (∃ (lo ln: loc),
       heapN ⊥ N ∧ heap_ctx ∧
       l = (#lo, #ln)%V ∧ inv N (lock_inv (fst γs) (snd γs) lo ln R))%I.

  Definition issued (γs: gname * gname) (l : val) (x: nat) (R : iProp Σ) : iProp Σ :=
    (∃ (lo ln: loc),
       heapN ⊥ N ∧ heap_ctx ∧
       l = (#lo, #ln)%V ∧ inv N (lock_inv (fst γs) (snd γs) lo ln R) ∧
       auth_own (fst γs) (GSet {[ x ]}))%I.

  Definition locked (γs: gname * gname) : iProp Σ := own (snd γs) (Excl ())%I.

  Global Instance lock_inv_ne n γ1 γ2 lo ln : Proper (dist n ==> dist n) (lock_inv γ1 γ2 lo ln).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne γs n l : Proper (dist n ==> dist n) (is_lock γs l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_persistent γs l R : PersistentP (is_lock γs l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γs : TimelessP (locked γs).
  Proof. apply _. Qed.

  Lemma locked_exclusive (γs: gname * gname) : (locked γs ★ locked γs ⊢ False)%I.
  Proof.
    iIntros "[Hl Hl']". iCombine "Hl" "Hl'" as "Hl". by iDestruct (own_valid with "Hl") as %[].
  Qed.

  Lemma newlock_spec (R : iProp Σ) Φ :
    heapN ⊥ N → heap_ctx ★ R ★ (∀ lk γs, is_lock γs lk R -★ Φ lk) ⊢ WP newlock #() {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & HR & HΦ)". rewrite /newlock.
    wp_seq. wp_alloc lo as "Hlo". wp_alloc ln as "Hln".
    iVs (own_alloc (Excl ())) as (γ2) "Hγ2"; first done.
    iVs (own_alloc_strong (Auth (Excl' ∅) ∅) {[ γ2 ]}) as (γ1) "[% Hγ1]"; first done.
    iVs (inv_alloc N _ (lock_inv γ1 γ2 lo ln R) with "[-HΦ]").
    - iNext. rewrite /lock_inv.
      iExists 0%nat, 0%nat.
      iFrame.
      iSplitL "Hγ1".
      + rewrite /auth_inv.
        iExists (GSet ∅).
        by iFrame.
      + iLeft. by iFrame.
    - iVsIntro.
      iSpecialize ("HΦ" $! (#lo, #ln)%V (γ1, γ2)). iApply "HΦ".
      iExists lo, ln.
      iSplit; by eauto.
  Qed.

Lemma wait_loop_spec γs l x R (Φ : val → iProp Σ) :
  issued γs l x R ★ (locked γs -★ R -★ Φ #()) ⊢ WP wait_loop #x l {{ Φ }}.
Proof.
  iIntros "[Hl HΦ]". iDestruct "Hl" as (lo ln) "(% & #? & % & #? & Ht)".
  iLöb as "IH". wp_rec. subst. wp_let. wp_proj. wp_bind (! _)%E.
  iInv N as (o n) "[Hlo [Hln Ha]]" "Hclose".
  wp_load. destruct (decide (x = o)) as [->|Hneq].
  - iDestruct "Ha" as "[Hainv [[Ho HR] | Haown]]".
    + iVs ("Hclose" with "[Hlo Hln Hainv Ht]").
      { iNext. iExists o, n. iFrame. eauto. }
      iVsIntro. wp_let. wp_op=>[_|[]] //.
      wp_if. iVsIntro.
      iApply ("HΦ" with "[-HR] HR"). eauto.
    + iExFalso. iCombine "Ht" "Haown" as "Haown".
      iDestruct (auth_own_valid with "Haown") as % ?%gset_disj_valid_op.
      set_solver.
  - iVs ("Hclose" with "[Hlo Hln Ha]").
    { iNext. iExists o, n. by iFrame. }
    iVsIntro. wp_let. wp_op=>[[/Nat2Z.inj //]|?].
    wp_if. iApply ("IH" with "Ht"). by iExact "HΦ".
Qed.

Lemma acquire_spec γs l R (Φ : val → iProp Σ) :
  is_lock γs l R ★ (locked γs -★ R -★ Φ #()) ⊢ WP acquire l {{ Φ }}.
Proof.
  iIntros "[Hl HΦ]". iDestruct "Hl" as (lo ln) "(% & #? & % & #?)".
  iLöb as "IH". wp_rec. wp_bind (! _)%E. subst. wp_proj.
  iInv N as (o n) "[Hlo [Hln Ha]]" "Hclose".
  wp_load. iVs ("Hclose" with "[Hlo Hln Ha]").
  { iNext. iExists o, n. by iFrame. }
  iVsIntro. wp_let. wp_proj. wp_op.
  wp_bind (CAS _ _ _).
  iInv N as (o' n') "[Hlo' [Hln' [Hainv Haown]]]" "Hclose".
  destruct (decide (#n' = #n))%V as [[= ->%Nat2Z.inj] | Hneq].
  - wp_cas_suc.
    iDestruct "Hainv" as (s) "[Ho %]"; subst.
    iVs (own_update with "Ho") as "Ho".
    { eapply auth_update_no_frag, (gset_alloc_empty_local_update n).
      rewrite elem_of_seq_set; omega. }
    iDestruct "Ho" as "[Hofull Hofrag]".
    iVs ("Hclose" with "[Hlo' Hln' Haown Hofull]").
    { rewrite gset_disj_union; last by apply (seq_set_S_disjoint 0).
      rewrite -(seq_set_S_union_L 0).
      iNext. iExists o', (S n)%nat.
      rewrite Nat2Z.inj_succ -Z.add_1_r.
      iFrame. iExists (GSet (seq_set 0 (S n))). by iFrame. }
    iVsIntro. wp_if.
    iApply (wait_loop_spec γs (#lo, #ln)).
    iSplitR "HΦ"; last by auto.
    rewrite /issued /auth_own; eauto 10.
  - wp_cas_fail.
    iVs ("Hclose" with "[Hlo' Hln' Hainv Haown]").
    { iNext. iExists o', n'. by iFrame. }
    iVsIntro. wp_if. by iApply "IH".
Qed.

Lemma release_spec γs l R (Φ : val → iProp Σ):
  is_lock γs l R ★ locked γs ★ R ★ Φ #() ⊢ WP release l {{ Φ }}.
Proof.
  iIntros "(Hl & Hγ & HR & HΦ)". iDestruct "Hl" as (lo ln) "(% & #? & % & #?)".
  iLöb as "IH". wp_rec. subst. wp_proj. wp_bind (! _)%E.
  iInv N as (o n) "[Hlo [Hln Hr]]" "Hclose".
  wp_load. iVs ("Hclose" with "[Hlo Hln Hr]").
  { iNext. iExists o, n. by iFrame. }
  iVsIntro. wp_let. wp_bind (CAS _ _ _ ).
  wp_proj. wp_op.
  iInv N as (o' n') "[Hlo' [Hln' Hr]]" "Hclose".
  destruct (decide (#o' = #o))%V as [[= ->%Nat2Z.inj ] | Hneq].
  - wp_cas_suc.
    iDestruct "Hr" as "[Hainv [[Ho _] | Hown]]".
    + iExFalso. iCombine "Hγ" "Ho" as "Ho".
      iDestruct (own_valid with "#Ho") as %[].
    + iVs ("Hclose" with "[Hlo' Hln' HR Hγ Hainv]").
      { iNext. iExists (o + 1)%nat, n'%nat.
        iFrame. rewrite Nat2Z.inj_add.
        iFrame. iLeft; by iFrame. }
      iVsIntro. by wp_if.
  - wp_cas_fail. iVs ("Hclose" with "[Hlo' Hln' Hr]").
    { iNext. iExists o', n'. by iFrame. }
    iVsIntro. wp_if. by iApply ("IH" with "Hγ HR").
Qed.
End proof.

Typeclasses Opaque is_lock issued locked.

Definition ticket_lock `{!heapG Σ, !tlockG Σ} :=
  Lock _ _ newlock acquire release (gname * gname) is_lock locked _ _ _ locked_exclusive newlock_spec acquire_spec release_spec.
