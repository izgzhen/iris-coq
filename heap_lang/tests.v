(** This file is essentially a bunch of testcases. *)
From program_logic Require Import ownership.
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
  Context {Σ : iFunctorG} (HeapI : gid) `{!HeapInG Σ HeapI}.
  Implicit Types P : iPropG heap_lang Σ.
  Implicit Types Q : val → iPropG heap_lang Σ.

  Definition e  : expr :=
    let: "x" := ref '1 in "x" <- !"x" + '1;; !"x".
  Goal ∀ γh N, heap_ctx HeapI γh N ⊑ wp N e (λ v, v = '2).
  Proof.
    move=> γh N. rewrite /e.
    wp_focus (ref '1)%L. eapply wp_alloc; eauto; [].
    rewrite -later_intro; apply forall_intro=>l; apply wand_intro_l.
    wp_rec.
    wp_focus (! LocV l)%L.
    eapply wp_load; eauto with I; []. apply sep_mono_r.
    rewrite -later_intro; apply wand_intro_l.
    wp_bin_op.
    wp_focus (_ <- _)%L.
    eapply wp_store; eauto with I; []. apply sep_mono_r.
    rewrite -later_intro. apply wand_intro_l.
    wp_rec.
    eapply wp_load; eauto with I; []. apply sep_mono; first done.
    rewrite -later_intro. apply wand_intro_l.
    by apply const_intro.
  Qed.

  Definition FindPred : val :=
    rec: "pred" "x" "y" :=
      let: "yp" := "y" + '1 in
      if: "yp" < "x" then "pred" "x" "yp" else "y".
  Definition Pred : val :=
    λ: "x",
      if: "x" ≤ '0 then -FindPred (-"x" + '2) '0 else FindPred "x" '0.

  Lemma FindPred_spec n1 n2 E Q :
    (■ (n1 < n2) ∧ Q '(n2 - 1)) ⊑ wp E (FindPred 'n2 'n1) Q.
  Proof.
    revert n1; apply löb_all_1=>n1.
    rewrite (comm uPred_and (■ _)%I) assoc; apply const_elim_r=>?.
    (* first need to do the rec to get a later *)
    wp_rec>.
    (* FIXME: ssr rewrite fails with "Error: _pattern_value_ is used in conclusion." *)
    rewrite ->(later_intro (Q _)); rewrite -!later_and; apply later_mono.
    wp_rec. wp_bin_op. wp_rec. wp_bin_op=> ?; wp_if.
    - rewrite (forall_elim (n1 + 1)) const_equiv; last omega.
      by rewrite left_id impl_elim_l.
    - wp_value. assert (n1 = n2 - 1) as -> by omega; auto with I.
  Qed.

  Lemma Pred_spec n E Q : ▷ Q (LitV (n - 1)) ⊑ wp E (Pred 'n)%L Q.
  Proof.
    wp_rec>; apply later_mono; wp_bin_op=> ?; wp_if.
    - wp_un_op. wp_bin_op.
      wp_focus (FindPred _ _); rewrite -FindPred_spec.
      apply and_intro; first auto with I omega.
      wp_un_op. by replace (n - 1) with (- (-n + 2 - 1)) by omega.
    - rewrite -FindPred_spec. auto with I omega.
  Qed.

  Goal ∀ E,
    True ⊑ wp (Σ:=globalF Σ) E (let: "x" := Pred '42 in Pred "x") (λ v, v = '40).
  Proof.
    intros E.
    wp_focus (Pred _); rewrite -Pred_spec -later_intro.
    wp_rec. rewrite -Pred_spec -later_intro; auto with I.
  Qed.
End LiftingTests.
