From iris.heap_lang Require Export lifting.
From iris.algebra Require Import auth gmap frac dec_agree.
From iris.base_logic.lib Require Export invariants.
From iris.base_logic.lib Require Import wsat auth.
From iris.proofmode Require Import tactics.
Import uPred.
(* TODO: The entire construction could be generalized to arbitrary languages that have
   a finmap as their state. Or maybe even beyond "as their state", i.e. arbitrary
   predicates over finmaps instead of just ownP. *)

Definition heapN : namespace := nroot .@ "heap".
Definition heapUR : ucmraT := gmapUR loc (prodR fracR (dec_agreeR val)).

(** The CMRA we need. *)
Class heapG Σ := HeapG {
  heapG_iris_inG :> irisG heap_lang Σ;
  heap_inG :> authG Σ heapUR;
  heap_name : gname
}.

Definition to_heap : state → heapUR := fmap (λ v, (1%Qp, DecAgree v)).

Section definitions.
  Context `{heapG Σ}.

  Definition heap_mapsto_def (l : loc) (q : Qp) (v: val) : iProp Σ :=
    auth_own heap_name ({[ l := (q, DecAgree v) ]}).
  Definition heap_mapsto_aux : { x | x = @heap_mapsto_def }. by eexists. Qed.
  Definition heap_mapsto := proj1_sig heap_mapsto_aux.
  Definition heap_mapsto_eq : @heap_mapsto = @heap_mapsto_def :=
    proj2_sig heap_mapsto_aux.

  Definition heap_ctx : iProp Σ := auth_ctx heap_name heapN to_heap ownP.
End definitions.

Typeclasses Opaque heap_ctx heap_mapsto.

Notation "l ↦{ q } v" := (heap_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : uPred_scope.

Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : uPred_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : uPred_scope.

Section heap.
  Context {Σ : gFunctors}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types h g : heapUR.

  (** Conversion to heaps and back *)
  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Lemma lookup_to_heap_None σ l : σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.
  Lemma heap_singleton_included σ l q v :
    {[l := (q, DecAgree v)]} ≼ to_heap σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included=> -[[q' av] [/leibniz_equiv_iff Hl Hqv]].
    move: Hl. rewrite /to_heap lookup_fmap fmap_Some=> -[v' [Hl [??]]]; subst.
    by move: Hqv=> /Some_pair_included_total_2 [_ /DecAgree_included ->].
  Qed.
  Lemma heap_singleton_included' σ l q v :
    {[l := (q, DecAgree v)]} ≼ to_heap σ → to_heap σ !! l = Some (1%Qp,DecAgree v).
  Proof.
    intros Hl%heap_singleton_included. by rewrite /to_heap lookup_fmap Hl.
  Qed.
  Lemma to_heap_insert l v σ :
    to_heap (<[l:=v]> σ) = <[l:=(1%Qp, DecAgree v)]> (to_heap σ).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Context `{heapG Σ}.

  (** General properties of mapsto *)
  Global Instance heap_ctx_persistent : PersistentP heap_ctx.
  Proof. rewrite /heap_ctx. apply _. Qed.
  Global Instance heap_mapsto_timeless l q v : TimelessP (l ↦{q} v).
  Proof. rewrite heap_mapsto_eq /heap_mapsto_def. apply _. Qed.

  Lemma heap_mapsto_op_eq l q1 q2 v : l ↦{q1} v ∗ l ↦{q2} v ⊣⊢ l ↦{q1+q2} v.
  Proof.
    by rewrite heap_mapsto_eq -auth_own_op op_singleton pair_op dec_agree_idemp.
  Qed.

  Lemma heap_mapsto_op l q1 q2 v1 v2 :
    l ↦{q1} v1 ∗ l ↦{q2} v2 ⊣⊢ ⌜v1 = v2⌝ ∧ l ↦{q1+q2} v1.
  Proof.
    destruct (decide (v1 = v2)) as [->|].
    { by rewrite heap_mapsto_op_eq pure_True // left_id. }
    apply (anti_symm (⊢)); last by apply pure_elim_l.
    rewrite heap_mapsto_eq -auth_own_op auth_own_valid discrete_valid.
    eapply pure_elim; [done|] =>  /=.
    rewrite op_singleton pair_op dec_agree_ne // singleton_valid. by intros [].
  Qed.

  Lemma heap_mapsto_op_1 l q1 q2 v1 v2 :
    l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ ⌜v1 = v2⌝ ∧ l ↦{q1+q2} v1.
  Proof. by rewrite heap_mapsto_op. Qed.

  Lemma heap_mapsto_op_half l q v1 v2 :
    l ↦{q/2} v1 ∗ l ↦{q/2} v2 ⊣⊢ ⌜v1 = v2⌝ ∧ l ↦{q} v1.
  Proof. by rewrite heap_mapsto_op Qp_div_2. Qed.

  Lemma heap_mapsto_op_half_1 l q v1 v2 :
    l ↦{q/2} v1 ∗ l ↦{q/2} v2 ⊢ ⌜v1 = v2⌝ ∧ l ↦{q} v1.
  Proof. by rewrite heap_mapsto_op_half. Qed.

  Lemma heap_ex_mapsto_op l q1 q2 : l ↦{q1} - ∗ l ↦{q2} - ⊣⊢ l ↦{q1+q2} -.
  Proof.
    iSplit.
    - iIntros "[H1 H2]". iDestruct "H1" as (v1) "H1". iDestruct "H2" as (v2) "H2".
      iDestruct (heap_mapsto_op_1 with "[$H1 $H2]") as "[% ?]"; subst; eauto.
    - iDestruct 1 as (v) "H". rewrite -heap_mapsto_op_eq.
      iDestruct "H" as "[H1 H2]"; iSplitL "H1"; eauto.
  Qed.

  Lemma heap_ex_mapsto_op_half l q : l ↦{q/2} - ∗ l ↦{q/2} - ⊣⊢ l ↦{q} -.
  Proof. by rewrite heap_ex_mapsto_op Qp_div_2. Qed.

  Lemma heap_mapsto_valid l q v : l ↦{q} v ⊢ ✓ q.
  Proof.
    rewrite heap_mapsto_eq /heap_mapsto_def auth_own_valid !discrete_valid.
    by apply pure_mono=> /singleton_valid [??].
  Qed.
  Lemma heap_mapsto_valid_2 l q1 q2 v1 v2 :
    l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ ✓ (q1 + q2)%Qp.
  Proof. rewrite heap_mapsto_op heap_mapsto_valid. auto with I. Qed.

  (** Weakest precondition *)
  Lemma wp_alloc E e v :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx }}} Alloc e @ E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "#Hinv HΦ". rewrite /heap_ctx.
    iMod (auth_empty heap_name) as "Ha".
    iMod (auth_open with "[$Hinv $Ha]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_alloc_pst with "Hσ"). iNext. iIntros (l) "[% Hσ]".
    iMod ("Hcl" with "* [Hσ]") as "Ha".
    { iFrame. iPureIntro. rewrite to_heap_insert.
      eapply alloc_singleton_local_update; by auto using lookup_to_heap_None. }
    iApply "HΦ". by rewrite heap_mapsto_eq /heap_mapsto_def.
  Qed.

  Lemma wp_load E l q v :
    ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦{q} v }}} Load (Lit (LitLoc l)) @ E
    {{{ RET v; l ↦{q} v }}}.
  Proof.
    iIntros (? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iMod (auth_open with "[$Hinv $Hl]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_load_pst _ σ with "Hσ"); first eauto using heap_singleton_included.
    iNext; iIntros "Hσ".
    iMod ("Hcl" with "* [Hσ]") as "Ha"; first eauto. by iApply "HΦ".
  Qed.

  Lemma wp_store E l v' e v :
    to_val e = Some v → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦ v' }}} Store (Lit (LitLoc l)) e @ E
    {{{ RET LitV LitUnit; l ↦ v }}}.
  Proof.
    iIntros (<-%of_to_val ? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iMod (auth_open with "[$Hinv $Hl]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_store_pst _ σ with "Hσ"); first eauto using heap_singleton_included.
    iNext; iIntros "Hσ". iMod ("Hcl" with "* [Hσ]") as "Ha".
    { iFrame. iPureIntro. rewrite to_heap_insert.
      eapply singleton_local_update, exclusive_local_update; last done.
      by eapply heap_singleton_included'. }
    by iApply "HΦ".
  Qed.

  Lemma wp_cas_fail E l q v' e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦{q} v' }}} CAS (Lit (LitLoc l)) e1 e2 @ E
    {{{ RET LitV (LitBool false); l ↦{q} v' }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ?? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iMod (auth_open with "[$Hinv $Hl]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_cas_fail_pst _ σ with "Hσ"); [eauto using heap_singleton_included|done|].
    iNext; iIntros "Hσ".
    iMod ("Hcl" with "* [Hσ]") as "Ha"; first eauto. by iApply "HΦ".
  Qed.

  Lemma wp_cas_suc E l e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦ v1 }}} CAS (Lit (LitLoc l)) e1 e2 @ E
    {{{ RET LitV (LitBool true); l ↦ v2 }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ? Φ) "[#Hinv >Hl] HΦ".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iMod (auth_open with "[$Hinv $Hl]") as (σ) "(%&Hσ&Hcl)"; first done.
    iApply (wp_cas_suc_pst _ σ with "Hσ"); first by eauto using heap_singleton_included.
    iNext. iIntros "Hσ". iMod ("Hcl" with "* [Hσ]") as "Ha".
    { iFrame. iPureIntro. rewrite to_heap_insert.
      eapply singleton_local_update, exclusive_local_update; last done.
      by eapply heap_singleton_included'. }
    by iApply "HΦ".
  Qed.
End heap.
