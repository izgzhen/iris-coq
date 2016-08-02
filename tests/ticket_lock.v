From iris.program_logic Require Export global_functor auth.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import gset.
From iris.prelude Require Import set.
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

(** The CMRA we need. *)
Class tlockG Σ := TlockG {
   tlock_G :> authG heap_lang Σ (gset_disjUR nat);
   tlock_exclG  :> inG heap_lang Σ (exclR unitC)
}.

Definition tlockGF : gFunctorList := [ authGF (gset_disjUR nat)
                                     ; GFunctor (constRF (exclR unitC))].
Instance inGF_tlockG `{H : inGFs heap_lang Σ tlockGF} : tlockG Σ.
Proof. destruct H as (? & ? & ?). split. apply _. apply: inGF_inG. Qed.

Section proof.
Context `{!heapG Σ, !tlockG Σ} (N : namespace).
Local Notation iProp := (iPropG heap_lang Σ).

Section natstuff.
Open Scope nat_scope.
Fixpoint natset (s len: nat) : gset nat :=
  match len with
  | O => ∅
  | S len' => natset s len' ∪ {[ s + len' ]}
  end.

Lemma natset_range: ∀ (len s x: nat), x ∈ natset s len -> x < (s + len).
Proof.
  intros len.
  elim len.
  + intros. simpl in H. set_solver.
  + intros. simpl in H0. apply elem_of_union in H0.
    destruct H0.
    - apply H in H0.
      omega.
    - assert (x = s + n).
      set_solver.
      omega.
Qed.

Lemma natset_not_in: ∀ x, x ∉ natset 0 x.
Proof.
  intros x H.
  apply natset_range in H.
  omega.
Qed.

Lemma natset_incr: ∀ x, {[x]} ∪ natset 0 x = natset 0 (x + 1).
Proof.
  intros.
  rewrite Nat.add_1_r.
  simpl.
  set_solver.
Qed.

Lemma natset_disj: ∀ x, {[x]} ⊥ natset 0 x.
Proof.
  intros.
  assert (x ∉ natset 0 x).
  apply natset_not_in.
  set_solver.
Qed.

End natstuff.

Definition tickets_inv (n: nat) (gs: gset_disjUR nat) :iProp :=
  (∃ gs', GSet gs' = gs ∧ gs' = natset 0 n)%I.

Definition lock_inv (γ1 γ2: gname) (l : loc) (R : iProp) : iProp :=
  (∃ (o n: nat), l ↦ (#o, #n) ★
               auth_inv γ1 (tickets_inv n) ★
               ((own γ2 (Excl ()) ★  R) ∨
                auth_own γ1 (GSet {[ o ]})))%I.

Definition is_lock (l: loc) (R: iProp) : iProp :=
  (∃ γ1 γ2, heapN ⊥ N ∧ heap_ctx ∧ inv N (lock_inv γ1 γ2 l R))%I.

Definition issued (l : loc) (x: nat) (R : iProp) : iProp :=
  (∃ γ1 γ2, heapN ⊥ N ∧ heap_ctx ∧ inv N (lock_inv γ1 γ2 l R) ∧ auth_own γ1 (GSet {[ x ]}))%I.

Definition locked (l : loc) (R : iProp) : iProp :=
  (∃ γ1 γ2, heapN ⊥ N ∧ heap_ctx ∧ inv N (lock_inv γ1 γ2 l R) ∧ own γ2 (Excl ()))%I.

Global Instance lock_inv_ne n γ1 γ2 l : Proper (dist n ==> dist n) (lock_inv γ1 γ2 l).
Proof. solve_proper. Qed.
Global Instance is_lock_ne n l: Proper (dist n ==> dist n) (is_lock l).
Proof. solve_proper. Qed.
Global Instance locked_ne n l: Proper (dist n ==> dist n) (locked l).
Proof. solve_proper. Qed.

Global Instance is_lock_persistent l R : PersistentP (is_lock l R).
Proof. apply _. Qed.

Lemma newlock_spec (R : iProp) Φ :
  heapN ⊥ N →
  heap_ctx ★ R ★ (∀ l, is_lock l R -★ Φ #l) ⊢ WP newlock #() {{ Φ }}.
Proof.
  iIntros (?) "(#Hh & HR & HΦ)". rewrite /newlock.
  wp_seq. wp_alloc l as "Hl".
  iPvs (own_alloc (Excl ())) as (γ2) "Hγ2"; first done.
  iPvs (own_alloc_strong (Auth (Excl' ∅) ∅) _ {[ γ2 ]}) as (γ1) "[% Hγ1]"; first done.
  iPvs (inv_alloc N _ (lock_inv γ1 γ2 l R) with "[-HΦ]"); first done.
  { iNext. rewrite /lock_inv.
    iExists 0%nat, 0%nat.
    iFrame.
    iSplitL "Hγ1".
    { rewrite /auth_inv.
      iExists (GSet ∅).
      iFrame.
      rewrite /tickets_inv.
      iExists ∅; by iSplit.
    }
    iLeft.
    by iFrame.
  }
  iPvsIntro.
  iApply "HΦ".
  iExists γ1, γ2.
  iSplit; by auto.
Qed.

Lemma wait_loop_spec l x R (Φ : val → iProp) :
  issued l x R ★ (∀ l, locked l R -★ R -★ Φ #()) ⊢ WP wait_loop #x #l {{ Φ }}.
Proof.
  iIntros "[Hl HΦ]". iDestruct "Hl" as (γ1 γ2) "(% & #? & #? & Ht)".
  iLöb as "IH". wp_rec. wp_let. wp_focus (! _)%E.
  iInv N as (o n) "[Hl Ha]".
  wp_load. iPvsIntro.
  destruct (decide (x = o)) as [Heq|Hneq].
  - subst.
    iDestruct "Ha" as "[Hainv [[Ho HR] | Haown]]".
    + iSplitL "Hl Hainv Ht".
      * iNext.
        iExists o, n.
        iFrame.
        by iRight.
      * wp_proj. wp_let. wp_op=>Ho; last by contradiction Ho. clear Ho.
        wp_if. iPvsIntro.
        iApply ("HΦ" with "[-HR] HR"). iExists γ1, γ2; eauto.
    + iExFalso. iCombine "Ht" "Haown" as "Haown".
      iDestruct (auth_own_valid with "Haown") as "%".
      apply gset_disj_valid_op in H0.
      set_solver.
  - iSplitL "Hl Ha".
    + iNext. iExists o, n. by iFrame.
    + wp_proj. wp_let. wp_op=>?.
      * subst. contradiction Hneq. omega.
      * wp_if. by iApply ("IH" with "Ht").
Qed.

Lemma acquire_spec l R (Φ : val → iProp) :
  is_lock l R ★ (∀ l, locked l R -★ R -★ Φ #()) ⊢ WP acquire #l {{ Φ }}.
Proof.
  iIntros "[Hl HΦ]". iDestruct "Hl" as (γ1 γ2) "(% & #? & #?)".
  iLöb as "IH". wp_rec. wp_focus (! _)%E.
  iInv N as (o n) "[Hl Ha]".
  wp_load. iPvsIntro.
  iSplitL "Hl Ha".
  - iNext. iExists o, n. by iFrame.
  - wp_let.
    wp_focus (CAS _ _ _).
    wp_proj. wp_proj.
    wp_op.
    iInv N as (o' n') "[Hl [Hainv Haown]]". 
    destruct (decide ((#o', #n')%V = (#o, #n)%V)) as [Heq | Hneq].
    + wp_cas_suc.
      inversion Heq; subst.
      iDestruct "Hainv" as (s) "[Ho Ht]".
      iDestruct (own_valid with "#Ho") as "Hvalid".
      iDestruct (auth_validI _ with "Hvalid") as "[_ %]"; simpl; iClear "Hvalid".
      destruct s as [s|]; last by contradiction.
      iDestruct "Ht" as (gs) "[% %]".
      inversion H3. subst. subst. clear H3.
      iPvs (own_update with "Ho") as "Ho".
      { eapply auth_update_no_frag, gset_alloc_empty_local_update.
        eapply natset_not_in. }
      iDestruct "Ho" as "[Hofull Hofrag]".
      iSplitL "Hl Haown Hofull".
      * replace (GSet {[n']} ⋅ GSet (natset 0 n')) with (GSet (natset 0 (n' + 1))).
        { iPvsIntro. iNext.
          iExists o', (n' + 1)%nat.
          rewrite Nat2Z.inj_add.
          iFrame. iExists (GSet (natset 0 (n' + 1))).
          iFrame. iExists (natset 0 (n' + 1)).
          by auto.
        }
        { rewrite gset_disj_union.
          replace (natset 0 (n' + 1)) with ({[n']} ∪ natset 0 n').
          - auto.
          - apply natset_incr.
          - apply natset_disj.
        }
      * iPvsIntro. wp_if. wp_proj.
        iApply wait_loop_spec.
        iSplitR "HΦ"; last by done.
        iExists γ1, γ2.
        (* FIXME: iFrame should be able to make progress here. *)
        repeat (iSplit; first by auto).
        by rewrite /auth_own.
    + wp_cas_fail.
      iPvsIntro.
      iSplitL "Hl Hainv Haown".
      { iNext. iExists o', n'. by iFrame. }
      { wp_if. by iApply "IH". }
Qed.

Lemma release_spec R l (Φ : val → iProp):
  locked l R ★ R ★ Φ #() ⊢ WP release #l {{ Φ }}.
Proof.
  iIntros "(Hl & HR & HΦ)"; iDestruct "Hl" as (γ1 γ2) "(% & #? & #? & Hγ)".
  iLöb as "IH". wp_rec. wp_focus (! _)%E.
  iInv N as (o n) "[Hl Hr]".
  wp_load. iPvsIntro.
  iSplitL "Hl Hr".
  - iNext. iExists o, n. by iFrame.
  - wp_let. wp_focus (CAS _ _ _ ).
    wp_proj. wp_op. wp_proj.
    iInv N as (o' n') "[Hl Hr]".
    destruct (decide ((#o', #n')%V = (#o, #n)%V)) as [Heq | Hneq].
    + inversion Heq; subst.
      wp_cas_suc.
      iDestruct "Hr" as "[Hainv [[Ho _] | Hown]]".
      * iExFalso. iCombine "Hγ" "Ho" as "Ho".
        iDestruct (own_valid with "#Ho") as "Hvalid".
        by iDestruct (excl_validI _ with "Hvalid") as "%".
      * iSplitL "Hl HR Hγ Hainv".
        { iPvsIntro. iNext. iExists (o' + 1)%nat, n'%nat.
          iFrame. rewrite Nat2Z.inj_add.
          iFrame. iLeft; by iFrame. }
        { iPvsIntro. by wp_if. }
    + wp_cas_fail.
      iPvsIntro.
      iSplitL "Hl Hr".
      * iNext. iExists o', n'. by iFrame.
      * wp_if. by iApply ("IH" with "Hγ HR").
Qed.
End proof.

Typeclasses Opaque is_lock issued locked.

