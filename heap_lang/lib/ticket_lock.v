From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.program_logic Require Import auth.
From iris.proofmode Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import gset.
Import uPred.

Definition wait_loop: val :=
  rec: "wait_loop" "x" "l" :=
    let: "o" := Fst !"l" in
    if: "x" = "o"
      then #() (* my turn *)
      else "wait_loop" "x" "l".

Definition newlock : val := λ: <>, ref((* owner *) #0, (* next *) #0).
Definition acquire : val :=
  rec: "acquire" "l" :=
    let: "oldl" := !"l" in
    if: CAS "l" "oldl" (Fst "oldl", Snd "oldl" + #1)
      then wait_loop (Snd "oldl") "l"
      else "acquire" "l".

Definition release : val :=
  rec: "release" "l" :=
    let: "oldl" := !"l" in
    if: CAS "l" "oldl" (Fst "oldl" + #1, Snd "oldl")
      then #()
      else "release" "l".

Global Opaque newlock acquire release wait_loop.

(** The CMRAs we need. *)
Class tlockG Σ := TlockG {
   tlock_G :> authG Σ (gset_disjUR nat);
   tlock_exclG  :> inG Σ (exclR unitC)
}.

Definition tlockGF : gFunctorList :=
  [authGF (gset_disjUR nat); GFunctor (constRF (exclR unitC))].
Instance inGF_tlockG `{H : inGFs Σ tlockGF} : tlockG Σ.
Proof. destruct H as (? & ? & ?). split. apply _. apply: inGF_inG. Qed.

Section proof.
Context `{!heapG Σ, !tlockG Σ} (N : namespace).

Definition tickets_inv (n: nat) (gs: gset_disjUR nat) : iProp Σ :=
  (gs = GSet (seq_set 0 n))%I.

Definition lock_inv (γ1 γ2: gname) (l : loc) (R : iProp Σ) : iProp Σ :=
  (∃ o n: nat, l ↦ (#o, #n) ★
               auth_inv γ1 (tickets_inv n) ★
               ((own γ2 (Excl ()) ★  R) ∨ auth_own γ1 (GSet {[ o ]})))%I.

Definition is_lock (l: loc) (R: iProp Σ) : iProp Σ :=
  (∃ γ1 γ2, heapN ⊥ N ∧ heap_ctx ∧ inv N (lock_inv γ1 γ2 l R))%I.

Definition issued (l : loc) (x: nat) (R : iProp Σ) : iProp Σ :=
  (∃ γ1 γ2, heapN ⊥ N ∧ heap_ctx ∧ inv N (lock_inv γ1 γ2 l R) ∧
            auth_own γ1 (GSet {[ x ]}))%I.

Definition locked (l : loc) (R : iProp Σ) : iProp Σ :=
  (∃ γ1 γ2, heapN ⊥ N ∧ heap_ctx ∧ inv N (lock_inv γ1 γ2 l R) ∧
            own γ2 (Excl ()))%I.

Global Instance lock_inv_ne n γ1 γ2 l : Proper (dist n ==> dist n) (lock_inv γ1 γ2 l).
Proof. solve_proper. Qed.
Global Instance is_lock_ne n l: Proper (dist n ==> dist n) (is_lock l).
Proof. solve_proper. Qed.
Global Instance locked_ne n l: Proper (dist n ==> dist n) (locked l).
Proof. solve_proper. Qed.

Global Instance is_lock_persistent l R : PersistentP (is_lock l R).
Proof. apply _. Qed.

Lemma newlock_spec (R : iProp Σ) Φ :
  heapN ⊥ N →
  heap_ctx ★ R ★ (∀ l, is_lock l R -★ Φ #l) ⊢ WP newlock #() {{ Φ }}.
Proof.
  iIntros (?) "(#Hh & HR & HΦ)". rewrite /newlock.
  wp_seq. wp_alloc l as "Hl".
  iVs (own_alloc (Excl ())) as (γ2) "Hγ2"; first done.
  iVs (own_alloc_strong (Auth (Excl' ∅) ∅) {[ γ2 ]}) as (γ1) "[% Hγ1]"; first done.
  iVs (inv_alloc N _ (lock_inv γ1 γ2 l R) with "[-HΦ]").
  { iNext. rewrite /lock_inv.
    iExists 0%nat, 0%nat.
    iFrame.
    iSplitL "Hγ1".
    { rewrite /auth_inv.
      iExists (GSet ∅).
      by iFrame. }
    iLeft.
    by iFrame. }
  iVsIntro.
  iApply "HΦ".
  iExists γ1, γ2.
  iSplit; by auto.
Qed.

Lemma wait_loop_spec l x R (Φ : val → iProp Σ) :
  issued l x R ★ (∀ l, locked l R -★ R -★ Φ #()) ⊢ WP wait_loop #x #l {{ Φ }}.
Proof.
  iIntros "[Hl HΦ]". iDestruct "Hl" as (γ1 γ2) "(% & #? & #? & Ht)".
  iLöb as "IH". wp_rec. wp_let. wp_focus (! _)%E.
  iInv N as (o n) "[Hl Ha]" "Hclose".
  wp_load. destruct (decide (x = o)) as [->|Hneq].
  - iDestruct "Ha" as "[Hainv [[Ho HR] | Haown]]".
    + iVs ("Hclose" with "[Hl Hainv Ht]").
      { iNext. iExists o, n. iFrame. eauto. }
      iVsIntro. wp_proj. wp_let. wp_op=>[_|[]] //.
      wp_if. iVsIntro.
      iApply ("HΦ" with "[-HR] HR"). iExists γ1, γ2; eauto.
    + iExFalso. iCombine "Ht" "Haown" as "Haown".
      iDestruct (auth_own_valid with "Haown") as % ?%gset_disj_valid_op.
      set_solver.
  - iVs ("Hclose" with "[Hl Ha]").
    { iNext. iExists o, n. by iFrame. }
    iVsIntro. wp_proj. wp_let. wp_op=>?; first omega.
    wp_if. by iApply ("IH" with "Ht").
Qed.

Lemma acquire_spec l R (Φ : val → iProp Σ) :
  is_lock l R ★ (∀ l, locked l R -★ R -★ Φ #()) ⊢ WP acquire #l {{ Φ }}.
Proof.
  iIntros "[Hl HΦ]". iDestruct "Hl" as (γ1 γ2) "(% & #? & #?)".
  iLöb as "IH". wp_rec. wp_focus (! _)%E.
  iInv N as (o n) "[Hl Ha]" "Hclose".
  wp_load. iVs ("Hclose" with "[Hl Ha]").
  { iNext. iExists o, n. by iFrame. }
  iVsIntro. wp_let. wp_proj. wp_proj. wp_op.
  wp_focus (CAS _ _ _).
  iInv N as (o' n') "[Hl [Hainv Haown]]" "Hclose".
  destruct (decide ((#o', #n') = (#o, #n)))%V
    as [[= ->%Nat2Z.inj ->%Nat2Z.inj] | Hneq].
  - wp_cas_suc.
    iDestruct "Hainv" as (s) "[Ho %]"; subst.
    iVs (own_update with "Ho") as "Ho".
    { eapply auth_update_no_frag, (gset_alloc_empty_local_update n).
      rewrite elem_of_seq_set; omega. }
    iDestruct "Ho" as "[Hofull Hofrag]".
    iVs ("Hclose" with "[Hl Haown Hofull]").
    { rewrite gset_disj_union; last by apply (seq_set_S_disjoint 0).
      rewrite -(seq_set_S_union_L 0).
      iNext. iExists o, (S n)%nat.
      rewrite Nat2Z.inj_succ -Z.add_1_r.
      iFrame. iExists (GSet (seq_set 0 (S n))). by iFrame. }
    iVsIntro. wp_if. wp_proj.
    iApply wait_loop_spec.
    iSplitR "HΦ"; last by done.
    rewrite /issued /auth_own; eauto 10.
  - wp_cas_fail.
    iVs ("Hclose" with "[Hl Hainv Haown]").
    { iNext. iExists o', n'. by iFrame. }
    iVsIntro. wp_if. by iApply "IH".
Qed.

Lemma release_spec R l (Φ : val → iProp Σ):
  locked l R ★ R ★ Φ #() ⊢ WP release #l {{ Φ }}.
Proof.
  iIntros "(Hl & HR & HΦ)"; iDestruct "Hl" as (γ1 γ2) "(% & #? & #? & Hγ)".
  iLöb as "IH". wp_rec. wp_focus (! _)%E.
  iInv N as (o n) "[Hl Hr]" "Hclose".
  wp_load. iVs ("Hclose" with "[Hl Hr]").
  { iNext. iExists o, n. by iFrame. }
  iVsIntro. wp_let. wp_focus (CAS _ _ _ ).
  wp_proj. wp_op. wp_proj.
  iInv N as (o' n') "[Hl Hr]" "Hclose".
  destruct (decide ((#o', #n') = (#o, #n)))%V
    as [[= ->%Nat2Z.inj ->%Nat2Z.inj] | Hneq].
  - wp_cas_suc.
    iDestruct "Hr" as "[Hainv [[Ho _] | Hown]]".
    + iExFalso. iCombine "Hγ" "Ho" as "Ho".
      iDestruct (own_valid with "#Ho") as %[].
    + iVs ("Hclose" with "[Hl HR Hγ Hainv]").
      { iNext. iExists (o + 1)%nat, n%nat.
        iFrame. rewrite Nat2Z.inj_add.
        iFrame. iLeft; by iFrame. }
      iVsIntro. by wp_if.
  - wp_cas_fail. iVs ("Hclose" with "[Hl Hr]").
    { iNext. iExists o', n'. by iFrame. }
    iVsIntro. wp_if. by iApply ("IH" with "Hγ HR").
Qed.
End proof.

Typeclasses Opaque is_lock issued locked.
