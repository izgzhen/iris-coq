(** This file is essentially a bunch of testcases. *)
From program_logic Require Import ownership hoare auth.
From heap_lang Require Import wp_tactics heap notation.
Import uPred.

Section LangTests.
  Definition add := ('21 + '21)%L.
  Goal ∀ σ, prim_step add σ ('42) σ None.
  Proof. intros; do_step done. Qed.
  Definition rec_app : expr := ((rec: "f" "x" := "f" "x") '0).
  Goal ∀ σ, prim_step rec_app σ rec_app σ None.
  Proof.
    intros. rewrite /rec_app. (* FIXME: do_step does not work here *)
    by eapply (Ectx_step  _ _ _ _ _ []), (BetaS _ _ _ _ '0).
  Qed.
  Definition lam : expr := λ: "x", "x" + '21.
  Goal ∀ σ, prim_step (lam '21)%L σ add σ None.
  Proof.
    intros. rewrite /lam. (* FIXME: do_step does not work here *)
    by eapply (Ectx_step  _ _ _ _ _ []), (BetaS "" "x" ("x" + '21) _ '21).
  Qed.
End LangTests.

Section LiftingTests.
  Context `{heapG Σ}.
  Local Notation iProp := (iPropG heap_lang Σ).
  Implicit Types P Q : iPropG heap_lang Σ.
  Implicit Types Φ : val → iPropG heap_lang Σ.

  Definition heap_e  : expr :=
    let: "x" := ref '1 in "x" <- !"x" + '1;; !"x".
  Lemma heap_e_spec E N :
     nclose N ⊆ E → heap_ctx N ⊑ || heap_e @ E {{ λ v, v = '2 }}.
  Proof.
    rewrite /heap_e=>HN. rewrite -(wp_mask_weaken N E) //.
    wp eapply wp_alloc; eauto. apply forall_intro=>l; apply wand_intro_l.
    wp_let. wp eapply wp_load; eauto with I. apply sep_mono_r, wand_intro_l.
    wp_op. wp eapply wp_store; eauto with I. apply sep_mono_r, wand_intro_l.
    wp_seq. wp eapply wp_load; eauto with I. apply sep_mono_r, wand_intro_l.
      by apply const_intro.
  Qed.

  Definition FindPred : val :=
    rec: "pred" "x" "y" :=
      let: "yp" := "y" + '1 in
      if: "yp" < "x" then "pred" "x" "yp" else "y".
  Definition Pred : val :=
    λ: "x",
      if: "x" ≤ '0 then -FindPred (-"x" + '2) '0 else FindPred "x" '0.

  Lemma FindPred_spec n1 n2 E Φ :
    n1 < n2 → 
    Φ '(n2 - 1) ⊑ || FindPred 'n2 'n1 @ E {{ Φ }}.
  Proof.
    revert n1. wp_rec=>n1 Hn.
    wp_let. wp_op. wp_let. wp_op=> ?; wp_if.
    - rewrite (forall_elim (n1 + 1)) const_equiv; last omega.
      by rewrite left_id -always_wand_impl always_elim wand_elim_r.
    - assert (n1 = n2 - 1) as -> by omega; auto with I.
  Qed.

  Lemma Pred_spec n E Φ : ▷ Φ (LitV (n - 1)) ⊑ || Pred 'n @ E {{ Φ }}.
  Proof.
    wp_lam. wp_op=> ?; wp_if.
    - wp_op. wp_op.
      ewp apply FindPred_spec; last omega.
      wp_op. by replace (n - 1) with (- (-n + 2 - 1)) by omega.
    - by ewp apply FindPred_spec; eauto with omega.
  Qed.

  Lemma Pred_user E :
    (True : iProp) ⊑ || let: "x" := Pred '42 in Pred "x" @ E {{ λ v, v = '40 }}.
  Proof.
    intros. ewp apply Pred_spec. wp_let. ewp apply Pred_spec. auto with I.
  Qed.
End LiftingTests.

Section ClosedProofs.
  Definition Σ : iFunctorG := #[ heapGF ].
  Notation iProp := (iPropG heap_lang Σ).

  Lemma heap_e_closed σ : {{ ownP σ : iProp }} heap_e {{ λ v, v = '2 }}.
  Proof.
    apply ht_alt. rewrite (heap_alloc ⊤ nroot); last by rewrite nclose_nroot.
    apply wp_strip_pvs, exist_elim=> ?. rewrite and_elim_l.
    rewrite -heap_e_spec; first by eauto with I. by rewrite nclose_nroot.
  Qed.

  Print Assumptions heap_e_closed.
End ClosedProofs.
