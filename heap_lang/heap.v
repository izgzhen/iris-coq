From iris.heap_lang Require Export lifting.
From iris.algebra Require Import auth gmap frac dec_agree.
From iris.base_logic.lib Require Export invariants.
From iris.base_logic.lib Require Import fractional.
From iris.program_logic Require Import ectx_lifting.
From iris.proofmode Require Import tactics.
Import uPred.
(* TODO: The entire construction could be generalized to arbitrary languages that have
   a finmap as their state. Or maybe even beyond "as their state", i.e. arbitrary
   predicates over finmaps instead of just ownP. *)

Definition heapUR : ucmraT := gmapUR loc (prodR fracR (dec_agreeR val)).
Definition to_heap : state → heapUR := fmap (λ v, (1%Qp, DecAgree v)).

(** The CMRA we need. *)
Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heap_inG :> inG Σ (authR heapUR);
  heap_name : gname
}.
Instance heapG_irisG `{heapG Σ} : irisG heap_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ := own heap_name (● to_heap σ)
}.

Section definitions.
  Context `{heapG Σ}.

  Definition heap_mapsto_def (l : loc) (q : Qp) (v: val) : iProp Σ :=
    own heap_name (◯ {[ l := (q, DecAgree v) ]}).
  Definition heap_mapsto_aux : { x | x = @heap_mapsto_def }. by eexists. Qed.
  Definition heap_mapsto := proj1_sig heap_mapsto_aux.
  Definition heap_mapsto_eq : @heap_mapsto = @heap_mapsto_def :=
    proj2_sig heap_mapsto_aux.
End definitions.

Typeclasses Opaque heap_mapsto.

Notation "l ↦{ q } v" := (heap_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : uPred_scope.

Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : uPred_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : uPred_scope.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl.
Local Hint Constructors head_step.
Local Hint Resolve alloc_fresh.
Local Hint Resolve to_of_val.

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
  Lemma to_heap_insert l v σ :
    to_heap (<[l:=v]> σ) = <[l:=(1%Qp, DecAgree v)]> (to_heap σ).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Context `{heapG Σ}.

  (** General properties of mapsto *)
  Global Instance heap_mapsto_timeless l q v : TimelessP (l ↦{q} v).
  Proof. rewrite heap_mapsto_eq /heap_mapsto_def. apply _. Qed.
  Global Instance heap_mapsto_fractional l v : Fractional (λ q, l ↦{q} v)%I.
  Proof.
    intros p q. by rewrite heap_mapsto_eq -own_op -auth_frag_op
      op_singleton pair_op dec_agree_idemp.
  Qed.
  Global Instance heap_mapsto_as_fractional l q v :
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. done. Qed.

  Lemma heap_mapsto_agree l q1 q2 v1 v2 : l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite heap_mapsto_eq -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=. rewrite op_singleton singleton_valid pair_op.
    by move=> [_ /= /dec_agree_op_inv [?]].
  Qed.

  Global Instance heap_ex_mapsto_fractional l : Fractional (λ q, l ↦{q} -)%I.
  Proof.
    intros p q. iSplit.
    - iDestruct 1 as (v) "[H1 H2]". iSplitL "H1"; eauto.
    - iIntros "[H1 H2]". iDestruct "H1" as (v1) "H1". iDestruct "H2" as (v2) "H2".
      iDestruct (heap_mapsto_agree with "[$H1 $H2]") as %->. iExists v2. by iFrame.
  Qed.
  Global Instance heap_ex_mapsto_as_fractional l q :
    AsFractional (l ↦{q} -) (λ q, l ↦{q} -)%I q.
  Proof. done. Qed.

  Lemma heap_mapsto_valid l q v : l ↦{q} v ⊢ ✓ q.
  Proof.
    rewrite heap_mapsto_eq /heap_mapsto_def own_valid !discrete_valid.
    by apply pure_mono=> /auth_own_valid /singleton_valid [??].
  Qed.
  Lemma heap_mapsto_valid_2 l q1 q2 v1 v2 :
    l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "[H1 H2]". iDestruct (heap_mapsto_agree with "[$H1 $H2]") as %->.
    iApply (heap_mapsto_valid l _ v2). by iFrame.
  Qed.

  (** Weakest precondition *)
  Lemma wp_alloc E e v :
    to_val e = Some v →
    {{{ True }}} Alloc e @ E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
  Proof.
    iIntros (<-%of_to_val Φ) "HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1) "Hσ !>"; iSplit; first by auto.
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (1%Qp, DecAgree _))=> //.
      by apply lookup_to_heap_None. }
    iModIntro; iSplit=> //. rewrite to_heap_insert. iFrame.
    iApply "HΦ". by rewrite heap_mapsto_eq /heap_mapsto_def.
  Qed.

  Lemma wp_load E l q v :
    {{{ ▷ l ↦{q} v }}} Load (Lit (LitLoc l)) @ E {{{ RET v; l ↦{q} v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". rewrite heap_mapsto_eq /heap_mapsto_def.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1) "Hσ !>". iDestruct (own_valid_2 with "Hσ Hl")
      as %[?%heap_singleton_included _]%auth_valid_discrete_2.
    iSplit; first by eauto.
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_store E l v' e v :
    to_val e = Some v →
    {{{ ▷ l ↦ v' }}} Store (Lit (LitLoc l)) e @ E {{{ RET LitV LitUnit; l ↦ v }}}.
  Proof.
    iIntros (<-%of_to_val Φ) ">Hl HΦ". rewrite heap_mapsto_eq /heap_mapsto_def.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1) "Hσ !>". iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%heap_singleton_included _]%auth_valid_discrete_2.
    iSplit; first by eauto.
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ1 Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (1%Qp, DecAgree _))=> //.
      by rewrite /to_heap lookup_fmap Hl. }
    iModIntro. iSplit=>//. rewrite to_heap_insert. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_cas_fail E l q v' e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 →
    {{{ ▷ l ↦{q} v' }}} CAS (Lit (LitLoc l)) e1 e2 @ E
    {{{ RET LitV (LitBool false); l ↦{q} v' }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ? Φ) ">Hl HΦ".
    rewrite heap_mapsto_eq /heap_mapsto_def.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1) "Hσ !>". iDestruct (own_valid_2 with "Hσ Hl")
      as %[?%heap_singleton_included _]%auth_valid_discrete_2.
    iSplit; first by eauto.
    iNext; iIntros (v2' σ2 efs Hstep); inv_head_step. (* FIXME: this inversion is slow *)
    iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_cas_suc E l e1 v1 e2 v2 :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    {{{ ▷ l ↦ v1 }}} CAS (Lit (LitLoc l)) e1 e2 @ E
    {{{ RET LitV (LitBool true); l ↦ v2 }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val Φ) ">Hl HΦ".
    rewrite heap_mapsto_eq /heap_mapsto_def.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1) "Hσ !>". iDestruct (own_valid_2 with "Hσ Hl")
      as %[Hl%heap_singleton_included _]%auth_valid_discrete_2.
    iSplit; first by eauto.
    iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ1 Hl]".
    { eapply auth_update, singleton_local_update,
        (exclusive_local_update _ (1%Qp, DecAgree _))=> //.
      by rewrite /to_heap lookup_fmap Hl. }
    iModIntro. iSplit=>//. rewrite to_heap_insert. iFrame. by iApply "HΦ".
  Qed.
End heap.
