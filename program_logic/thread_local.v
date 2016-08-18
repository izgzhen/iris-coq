From iris.algebra Require Export gmap gset coPset.
From iris.proofmode Require Import invariants tactics.
Import uPred.

Definition thread_id := positive.

Class thread_localG Σ := {
  tl_enabled_inG :> inG Σ (gmapUR thread_id coPset_disjR);
  tl_disabled_inG :> inG Σ (gmapUR thread_id (gset_disjR positive));
  tl_enabled_name : gname;
  tl_disabled_name : gname
}.

Definition tlN : namespace := nroot .@ "tl".

Section defs.
  Context `{irisG Λ Σ, thread_localG Σ}.

  Definition tl_tokens (tid : thread_id) (E : coPset) : iProp Σ :=
    own tl_enabled_name {[ tid := CoPset E ]}.

  Definition tl_inv (tid : thread_id) (N : namespace) (P : iProp Σ) : iProp Σ :=
    (∃ i, ■ (i ∈ nclose N) ∧
          inv tlN (P ★ own tl_disabled_name {[ tid := GSet {[i]} ]}
                   ∨ tl_tokens tid {[i]}))%I.
End defs.

Instance: Params (@tl_tokens) 2.
Instance: Params (@tl_inv) 4.

Section proofs.
  Context `{irisG Λ Σ, thread_localG Σ}.

  Lemma tid_alloc :
    True =r=> ∃ tid, tl_tokens tid ⊤.
  Proof.
    iIntros.
    iVs (own_empty (A:=gmapUR thread_id coPset_disjR) tl_enabled_name) as "Hempty".
    iVs (own_updateP with "Hempty") as (m) "[Hm Hown]".
      by apply alloc_updateP' with (x:=CoPset ⊤).
    iDestruct "Hm" as %(tid & -> & _). eauto.
  Qed.

  Lemma tl_tokens_disj tid E1 E2 :
    tl_tokens tid E1 ★ tl_tokens tid E2 ⊢ ■ (E1 ⊥ E2).
  Proof.
    by rewrite /tl_tokens -own_op op_singleton own_valid -coPset_disj_valid_op
               discrete_valid singleton_valid.
  Qed.

  Lemma tl_tokens_union tid E1 E2 :
    E1 ⊥ E2 → tl_tokens tid (E1 ∪ E2) ⊣⊢ tl_tokens tid E1 ★ tl_tokens tid E2.
  Proof.
    intros ?. by rewrite /tl_tokens -own_op op_singleton coPset_disj_union.
  Qed.

  Lemma tl_inv_alloc tid E N P : ▷ P ={E}=> tl_inv tid N P.
  Proof.
    iIntros "HP".
    iVs (own_empty (A:=gmapUR thread_id (gset_disjR positive)) tl_disabled_name)
      as "Hempty".
    iVs (own_updateP with "Hempty") as (m) "[Hm Hown]".
    { eapply alloc_unit_singleton_updateP' with (u:=∅) (i:=tid). done. apply _.
      apply (gset_alloc_empty_updateP_strong' (λ i, i ∈ nclose N)).
      intros Ef. exists (coPpick (nclose N ∖ coPset.of_gset Ef)).
      rewrite -coPset.elem_of_of_gset comm -elem_of_difference.
      apply coPpick_elem_of=> Hfin.
      eapply nclose_infinite, (difference_finite_inv _ _), Hfin.
      apply of_gset_finite. }
    iDestruct "Hm" as %(? & -> & i & -> & ?).
    iVs (inv_alloc tlN with "[-]"). 2:iVsIntro; iExists i; eauto.
    iNext. iLeft. by iFrame.
  Qed.

  Lemma tl_inv_open tid tlE E N P :
    nclose tlN ⊆ tlE → nclose N ⊆ E →
    tl_inv tid N P ⊢ tl_tokens tid E ={tlE}=★ ▷ P ★ tl_tokens tid (E ∖ N) ★
                       (▷ P ★ tl_tokens tid (E ∖ N) ={tlE}=★ tl_tokens tid E).
  Proof.
    iIntros (??) "#Htlinv Htoks".
    iDestruct "Htlinv" as (i) "[% #Hinv]".
    rewrite {1 4}(union_difference_L (nclose N) E) //.
    rewrite {1 5}(union_difference_L {[i]} (nclose N)) ?tl_tokens_union; try set_solver.
    iDestruct "Htoks" as "[[Htoki Htoks0] Htoks1]". iFrame "Htoks0 Htoks1".
    iInv tlN as "[[HP >Hdis]|>Htoki2]" "Hclose".
    - iVs ("Hclose" with "[Htoki]") as "_". auto. iFrame.
      iIntros "!==>[HP ?]". iFrame.
      iInv tlN as "[[_ >Hdis2]|>Hitok]" "Hclose".
      + iCombine "Hdis" "Hdis2" as "Hdis".
        iDestruct (own_valid with "Hdis") as %Hval.
        revert Hval. rewrite op_singleton singleton_valid gset_disj_valid_op.
        set_solver.
      + iFrame. iApply "Hclose". iNext. iLeft. by iFrame.
    - iDestruct (tl_tokens_disj tid {[i]} {[i]} with "[-]") as %?. by iFrame.
      set_solver.
  Qed.

End proofs.