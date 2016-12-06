From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Export gmap gset coPset.
From iris.proofmode Require Import tactics.
Import uPred.

Definition thread_id := gname.

Class thread_localG Σ :=
  tl_inG :> inG Σ (prodR coPset_disjR (gset_disjR positive)).

Section defs.
  Context `{invG Σ, thread_localG Σ}.

  Definition tl_own (tid : thread_id) (E : coPset) : iProp Σ :=
    own tid (CoPset E, ∅).

  Definition tl_inv (tid : thread_id) (N : namespace) (P : iProp Σ) : iProp Σ :=
    (∃ i, ⌜i ∈ ↑N⌝ ∧
          inv N (P ∗ own tid (∅, GSet {[i]}) ∨ tl_own tid {[i]}))%I.
End defs.

Instance: Params (@tl_inv) 3.
Typeclasses Opaque tl_own tl_inv.

Section proofs.
  Context `{invG Σ, thread_localG Σ}.

  Global Instance tl_own_timeless tid E : TimelessP (tl_own tid E).
  Proof. rewrite /tl_own; apply _. Qed.

  Global Instance tl_inv_ne tid N n : Proper (dist n ==> dist n) (tl_inv tid N).
  Proof. rewrite /tl_inv. solve_proper. Qed.
  Global Instance tl_inv_proper tid N : Proper ((≡) ==> (≡)) (tl_inv tid N).
  Proof. apply (ne_proper _). Qed.

  Global Instance tl_inv_persistent tid N P : PersistentP (tl_inv tid N P).
  Proof. rewrite /tl_inv; apply _. Qed.

  Lemma tl_alloc : (|==> ∃ tid, tl_own tid ⊤)%I.
  Proof. by apply own_alloc. Qed.

  Lemma tl_own_disjoint tid E1 E2 : tl_own tid E1 -∗ tl_own tid E2 -∗ ⌜E1 ⊥ E2⌝.
  Proof.
    apply wand_intro_r.
    rewrite /tl_own -own_op own_valid -coPset_disj_valid_op. by iIntros ([? _]).
  Qed.

  Lemma tl_own_union tid E1 E2 :
    E1 ⊥ E2 → tl_own tid (E1 ∪ E2) ⊣⊢ tl_own tid E1 ∗ tl_own tid E2.
  Proof.
    intros ?. by rewrite /tl_own -own_op pair_op left_id coPset_disj_union.
  Qed.

  Lemma tl_inv_alloc tid E N P : ▷ P ={E}=∗ tl_inv tid N P.
  Proof.
    iIntros "HP".
    iMod (own_empty (prodUR coPset_disjUR (gset_disjUR positive)) tid) as "Hempty".
    iMod (own_updateP with "Hempty") as ([m1 m2]) "[Hm Hown]".
    { apply prod_updateP'. apply cmra_updateP_id, (reflexivity (R:=eq)).
      apply (gset_disj_alloc_empty_updateP_strong' (λ i, i ∈ ↑N)).
      intros Ef. exists (coPpick (↑ N ∖ coPset.of_gset Ef)).
      rewrite -coPset.elem_of_of_gset comm -elem_of_difference.
      apply coPpick_elem_of=> Hfin.
      eapply nclose_infinite, (difference_finite_inv _ _), Hfin.
      apply of_gset_finite. }
    simpl. iDestruct "Hm" as %(<- & i & -> & ?).
    rewrite /tl_inv.
    iMod (inv_alloc N with "[-]"); last (iModIntro; iExists i; eauto).
    iNext. iLeft. by iFrame.
  Qed.

  Lemma tl_inv_open tid E N P :
    ↑N ⊆ E →
    tl_inv tid N P -∗ tl_own tid E ={E}=∗ ▷ P ∗ tl_own tid (E∖↑N) ∗
                       (▷ P ∗ tl_own tid (E∖↑N) ={E}=∗ tl_own tid E).
  Proof.
    rewrite /tl_inv. iIntros (?) "#Htlinv Htoks".
    iDestruct "Htlinv" as (i) "[% Hinv]".
    rewrite [E as X in tl_own tid X](union_difference_L (↑N) E) //.
    rewrite [X in (X ∪ _)](union_difference_L {[i]} (↑N)) ?tl_own_union; [|set_solver..].
    iDestruct "Htoks" as "[[Htoki $] $]".
    iInv N as "[[$ >Hdis]|>Htoki2]" "Hclose".
    - iMod ("Hclose" with "[Htoki]") as "_"; first auto.
      iIntros "!> [HP $]".
      iInv N as "[[_ >Hdis2]|>Hitok]" "Hclose".
      + iDestruct (own_valid_2 with "Hdis Hdis2") as %[_ Hval%gset_disj_valid_op].
        set_solver.
      + iFrame. iApply "Hclose". iNext. iLeft. by iFrame.
    - iDestruct (tl_own_disjoint with "Htoki Htoki2") as %?. set_solver.
  Qed.
End proofs.
