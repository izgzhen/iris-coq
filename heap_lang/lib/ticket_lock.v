From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import auth gset.
From iris.heap_lang.lib Require Export lock.
Import uPred.

Definition wait_loop: val :=
  rec: "wait_loop" "x" "lk" :=
    let: "o" := !(Fst "lk") in
    if: "x" = "o"
      then #() (* my turn *)
      else "wait_loop" "x" "lk".

Definition newlock : val := λ: <>, ((* owner *) ref #0, (* next *) ref #0).

Definition acquire : val :=
  rec: "acquire" "lk" :=
    let: "n" := !(Snd "lk") in
    if: CAS (Snd "lk") "n" ("n" + #1)
      then wait_loop "n" "lk"
      else "acquire" "lk".

Definition release : val := λ: "lk",
  (Fst "lk") <- !(Fst "lk") + #1.

Global Opaque newlock acquire release wait_loop.

(** The CMRAs we need. *)
Class tlockG Σ :=
  tlock_G :> inG Σ (authR (prodUR (optionUR (exclR natC)) (gset_disjUR nat))).
Definition tlockΣ : gFunctors :=
  #[ GFunctor (constRF (authR (prodUR (optionUR (exclR natC)) (gset_disjUR nat)))) ].

Instance subG_tlockΣ {Σ} : subG tlockΣ Σ → tlockG Σ.
Proof. by intros ?%subG_inG. Qed.

Section proof.
  Context `{!heapG Σ, !tlockG Σ} (N : namespace).

  Definition lock_inv (γ : gname) (lo ln : loc) (R : iProp Σ) : iProp Σ :=
    (∃ o n : nat,
      lo ↦ #o ★ ln ↦ #n ★
      own γ (● (Excl' o, GSet (seq_set 0 n))) ★
      ((own γ (◯ (Excl' o, ∅)) ★ R) ∨ own γ (◯ (∅, GSet {[ o ]}))))%I.

  Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ lo ln : loc,
       heapN ⊥ N ∧ heap_ctx ∧
       lk = (#lo, #ln)%V ∧ inv N (lock_inv γ lo ln R))%I.

  Definition issued (γ : gname) (lk : val) (x : nat) (R : iProp Σ) : iProp Σ :=
    (∃ lo ln: loc,
       heapN ⊥ N ∧ heap_ctx ∧
       lk = (#lo, #ln)%V ∧ inv N (lock_inv γ lo ln R) ∧
       own γ (◯ (∅, GSet {[ x ]})))%I.

  Definition locked (γ : gname) : iProp Σ := (∃ o, own γ (◯ (Excl' o, ∅)))%I.

  Global Instance lock_inv_ne n γ lo ln :
    Proper (dist n ==> dist n) (lock_inv γ lo ln).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne γ n lk : Proper (dist n ==> dist n) (is_lock γ lk).
  Proof. solve_proper. Qed.
  Global Instance is_lock_persistent γ lk R : PersistentP (is_lock γ lk R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : TimelessP (locked γ).
  Proof. apply _. Qed.

  Lemma locked_exclusive (γ : gname) : (locked γ ★ locked γ ⊢ False)%I.
  Proof.
    iIntros "[H1 H2]". iDestruct "H1" as (o1) "H1". iDestruct "H2" as (o2) "H2".
    iCombine "H1" "H2" as "H". iDestruct (own_valid with "H") as %[[] _].
  Qed.

  Lemma newlock_spec (R : iProp Σ) Φ :
    heapN ⊥ N →
    heap_ctx ★ R ★ (∀ lk γ, is_lock γ lk R -★ Φ lk) ⊢ WP newlock #() {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & HR & HΦ)". rewrite /newlock /=.
    wp_seq. wp_alloc lo as "Hlo". wp_alloc ln as "Hln".
    iVs (own_alloc (● (Excl' 0%nat, ∅) ⋅ ◯ (Excl' 0%nat, ∅))) as (γ) "[Hγ Hγ']".
    { by rewrite -auth_both_op. }
    iVs (inv_alloc _ _ (lock_inv γ lo ln R) with "[-HΦ]").
    { iNext. rewrite /lock_inv.
      iExists 0%nat, 0%nat. iFrame. iLeft. by iFrame. }
    iVsIntro. iApply ("HΦ" $! (#lo, #ln)%V γ). iExists lo, ln. eauto.
  Qed.

  Lemma wait_loop_spec γ lk x R (Φ : val → iProp Σ) :
    issued γ lk x R ★ (locked γ -★ R -★ Φ #()) ⊢ WP wait_loop #x lk {{ Φ }}.
  Proof.
    iIntros "[Hl HΦ]". iDestruct "Hl" as (lo ln) "(% & #? & % & #? & Ht)".
    iLöb as "IH". wp_rec. subst. wp_let. wp_proj. wp_bind (! _)%E.
    iInv N as (o n) "(Hlo & Hln & Ha)" "Hclose".
    wp_load. destruct (decide (x = o)) as [->|Hneq].
    - iDestruct "Ha" as "[Hainv [[Ho HR] | Haown]]".
      + iVs ("Hclose" with "[Hlo Hln Hainv Ht]") as "_".
        { iNext. iExists o, n. iFrame. eauto. }
        iVsIntro. wp_let. wp_op=>[_|[]] //.
        wp_if. iVsIntro.
        iApply ("HΦ" with "[-HR] HR"). rewrite /locked; eauto.
      + iExFalso. iCombine "Ht" "Haown" as "Haown".
        iDestruct (own_valid with "Haown") as % [_ ?%gset_disj_valid_op].
        set_solver.
    - iVs ("Hclose" with "[Hlo Hln Ha]").
      { iNext. iExists o, n. by iFrame. }
      iVsIntro. wp_let. wp_op=>[[/Nat2Z.inj //]|?].
      wp_if. iApply ("IH" with "Ht"). by iExact "HΦ".
  Qed.

  Lemma acquire_spec γ lk R (Φ : val → iProp Σ) :
    is_lock γ lk R ★ (locked γ -★ R -★ Φ #()) ⊢ WP acquire lk {{ Φ }}.
  Proof.
    iIntros "[Hl HΦ]". iDestruct "Hl" as (lo ln) "(% & #? & % & #?)".
    iLöb as "IH". wp_rec. wp_bind (! _)%E. subst. wp_proj.
    iInv N as (o n) "[Hlo [Hln Ha]]" "Hclose".
    wp_load. iVs ("Hclose" with "[Hlo Hln Ha]") as "_".
    { iNext. iExists o, n. by iFrame. }
    iVsIntro. wp_let. wp_proj. wp_op.
    wp_bind (CAS _ _ _).
    iInv N as (o' n') "(>Hlo' & >Hln' & >Hauth & Haown)" "Hclose".
    destruct (decide (#n' = #n))%V as [[= ->%Nat2Z.inj] | Hneq].
    - wp_cas_suc.
      iVs (own_update with "Hauth") as "Hauth".
      { eapply (auth_update_no_frag _ (∅, _)), prod_local_update,
          (gset_disj_alloc_empty_local_update n); [done|].
        rewrite elem_of_seq_set. omega. }
      rewrite pair_op left_id_L. iDestruct "Hauth" as "[Hauth Hofull]".
      rewrite gset_disj_union; last by apply (seq_set_S_disjoint 0).
      rewrite -(seq_set_S_union_L 0).
      iVs ("Hclose" with "[Hlo' Hln' Haown Hauth]") as "_".
      { iNext. iExists o', (S n).
        rewrite Nat2Z.inj_succ -Z.add_1_r. by iFrame. }
      iVsIntro. wp_if.
      iApply (wait_loop_spec γ (#lo, #ln)).
      iFrame "HΦ". rewrite /issued; eauto 10.
    - wp_cas_fail.
      iVs ("Hclose" with "[Hlo' Hln' Hauth Haown]").
      { iNext. iExists o', n'. by iFrame. }
      iVsIntro. wp_if. by iApply "IH".
  Qed.

  Lemma release_spec γ lk R (Φ : val → iProp Σ):
    is_lock γ lk R ★ locked γ ★ R ★ Φ #() ⊢ WP release lk {{ Φ }}.
  Proof.
    iIntros "(Hl & Hγ & HR & HΦ)".
    iDestruct "Hl" as (lo ln) "(% & #? & % & #?)"; subst.
    iDestruct "Hγ" as (o) "Hγo".
    rewrite /release. wp_let. wp_proj. wp_proj. wp_bind (! _)%E.
    iInv N as (o' n) "(>Hlo & >Hln & >Hauth & Haown)" "Hclose".
    wp_load.
    iAssert (o' = o)%I with "[#]" as "%"; subst.
    { iCombine "Hγo" "Hauth" as "Hγo".
      by iDestruct (own_valid with "Hγo") (* FIXME: this is horrible *)
        as %[[[[?|] ?] [=]%leibniz_equiv_iff] ?]%auth_valid_discrete. }
    iVs ("Hclose" with "[Hlo Hln Hauth Haown]") as "_".
    { iNext. iExists o, n. by iFrame. }
    iVsIntro. wp_op.
    iInv N as (o' n') "(>Hlo & >Hln & >Hauth & Haown)" "Hclose".
    wp_store.
    iAssert (o' = o)%I with "[#]" as "%"; subst.
    { iCombine "Hγo" "Hauth" as "Hγo".
      by iDestruct (own_valid with "Hγo")
        as %[[[[?|] ?] [=]%leibniz_equiv_iff] ?]%auth_valid_discrete. }
    iDestruct "Haown" as "[[Hγo' _]|?]".
    { iCombine "Hγo" "Hγo'" as "Hγo".
      iDestruct (own_valid with "Hγo") as %[[] ?]. }
    iCombine "Hauth" "Hγo" as "Hauth".
    iVs (own_update with "Hauth") as "Hauth".
    { rewrite pair_split_L. apply: (auth_update _ _ (Excl' (S o), _)). (* FIXME: apply is slow *)
      apply prod_local_update, reflexivity; simpl.
      by apply option_local_update, exclusive_local_update. }
    rewrite -pair_split_L. iDestruct "Hauth" as "[Hauth Hγo]".
    iVs ("Hclose" with "[Hlo Hln Hauth Haown Hγo HR]") as "_"; last auto.
    iNext. iExists (S o), n'.
    rewrite Nat2Z.inj_succ -Z.add_1_r. iFrame. iLeft. by iFrame.
  Qed.
End proof.

Typeclasses Opaque is_lock issued locked.

Definition ticket_lock `{!heapG Σ, !tlockG Σ} : lock Σ :=
  {| lock.locked_exclusive := locked_exclusive; lock.newlock_spec := newlock_spec;
     lock.acquire_spec := acquire_spec; lock.release_spec := release_spec |}.
