From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Export gmap gset coPset.
From iris.proofmode Require Import tactics.
Import uPred.

(* Non-atomic ("thread-local") invariants. *)

Definition thread_id := gname.

Class na_invG Σ :=
  tl_inG :> inG Σ (prodR coPset_disjR (gset_disjR positive)).

Section defs.
  Context `{invG Σ, na_invG Σ}.

  Definition na_own (tid : thread_id) (E : coPset) : iProp Σ :=
    own tid (CoPset E, ∅).

  Definition na_inv (tid : thread_id) (N : namespace) (P : iProp Σ) : iProp Σ :=
    (∃ i, ⌜i ∈ ↑N⌝ ∧
          inv N (P ∗ own tid (∅, GSet {[i]}) ∨ na_own tid {[i]}))%I.
End defs.

Instance: Params (@na_inv) 3.
Typeclasses Opaque na_own na_inv.

Section proofs.
  Context `{invG Σ, na_invG Σ}.

  Global Instance na_own_timeless tid E : TimelessP (na_own tid E).
  Proof. rewrite /na_own; apply _. Qed.

  Global Instance na_inv_ne tid N n : Proper (dist n ==> dist n) (na_inv tid N).
  Proof. rewrite /na_inv. solve_proper. Qed.
  Global Instance na_inv_proper tid N : Proper ((≡) ==> (≡)) (na_inv tid N).
  Proof. apply (ne_proper _). Qed.

  Global Instance na_inv_persistent tid N P : PersistentP (na_inv tid N P).
  Proof. rewrite /na_inv; apply _. Qed.

  Lemma na_alloc : (|==> ∃ tid, na_own tid ⊤)%I.
  Proof. by apply own_alloc. Qed.

  Lemma na_own_disjoint tid E1 E2 : na_own tid E1 -∗ na_own tid E2 -∗ ⌜E1 ⊥ E2⌝.
  Proof.
    apply wand_intro_r.
    rewrite /na_own -own_op own_valid -coPset_disj_valid_op. by iIntros ([? _]).
  Qed.

  Lemma na_own_union tid E1 E2 :
    E1 ⊥ E2 → na_own tid (E1 ∪ E2) ⊣⊢ na_own tid E1 ∗ na_own tid E2.
  Proof.
    intros ?. by rewrite /na_own -own_op pair_op left_id coPset_disj_union.
  Qed.

  Lemma na_inv_alloc tid E N P : ▷ P ={E}=∗ na_inv tid N P.
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
    rewrite /na_inv.
    iMod (inv_alloc N with "[-]"); last (iModIntro; iExists i; eauto).
    iNext. iLeft. by iFrame.
  Qed.

  Lemma na_inv_open tid E F N P :
    ↑N ⊆ E → ↑N ⊆ F →
    na_inv tid N P -∗ na_own tid F ={E}=∗ ▷ P ∗ na_own tid (F∖↑N) ∗
                       (▷ P ∗ na_own tid (F∖↑N) ={E}=∗ na_own tid F).
  Proof.
    rewrite /na_inv. iIntros (??) "#Htlinv Htoks".
    iDestruct "Htlinv" as (i) "[% Hinv]".
    rewrite [F as X in na_own tid X](union_difference_L (↑N) F) //.
    rewrite [X in (X ∪ _)](union_difference_L {[i]} (↑N)) ?na_own_union; [|set_solver..].
    iDestruct "Htoks" as "[[Htoki $] $]".
    iInv N as "[[$ >Hdis]|>Htoki2]" "Hclose".
    - iMod ("Hclose" with "[Htoki]") as "_"; first auto.
      iIntros "!> [HP $]".
      iInv N as "[[_ >Hdis2]|>Hitok]" "Hclose".
      + iDestruct (own_valid_2 with "Hdis Hdis2") as %[_ Hval%gset_disj_valid_op].
        set_solver.
      + iFrame. iApply "Hclose". iNext. iLeft. by iFrame.
    - iDestruct (na_own_disjoint with "Htoki Htoki2") as %?. set_solver.
  Qed.
End proofs.
