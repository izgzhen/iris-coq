(** This file is essentially a bunch of testcases. *)
Require Import program_logic.ownership.
Require Import heap_lang.lifting heap_lang.sugar.
Import heap_lang uPred notations.

Module LangTests.
  Definition add := (Lit 21 + Lit 21)%L.
  Goal ∀ σ, prim_step add σ (Lit 42) σ None.
  Proof. intros; do_step done. Qed.
  Definition rec_app : expr := (rec: "f" "x" := "f" "x") (Lit 0).
  Goal ∀ σ, prim_step rec_app σ rec_app σ None.
  Proof.
    intros. rewrite /rec_app. (* FIXME: do_step does not work here *)
    by eapply (Ectx_step  _ _ _ _ _ []), (BetaS _ _ _ _ (LitV (LitNat 0))).
  Qed.
  Definition lam : expr := λ: "x", "x" + Lit 21.
  Goal ∀ σ, prim_step (lam (Lit 21)) σ add σ None.
  Proof.
    intros. rewrite /lam. (* FIXME: do_step does not work here *)
    by eapply (Ectx_step  _ _ _ _ _ []), (BetaS "" "x" ("x" + Lit 21) _ (LitV 21)).
  Qed.
End LangTests.

Module LiftingTests.
  Context {Σ : iFunctor}.
  Implicit Types P : iProp heap_lang Σ.
  Implicit Types Q : val → iProp heap_lang Σ.

  Definition e  : expr :=
    let: "x" := ref (Lit 1) in "x" <- !"x" + Lit 1; !"x".
  Goal ∀ σ E, ownP (Σ:=Σ) σ ⊑ wp E e (λ v, v = LitV 2).
  Proof.
    move=> σ E. rewrite /e.
    rewrite -(wp_bindi (LetCtx _ _)) -wp_alloc_pst //=.
    apply sep_intro_True_r; first done.
    rewrite -later_intro; apply forall_intro=>l; apply wand_intro_l.
    rewrite right_id; apply const_elim_l=> _.
    rewrite -wp_let //= -later_intro.
    rewrite -(wp_bindi (SeqCtx (Load (Loc _)))) /=. 
    rewrite -(wp_bindi (StoreRCtx (LocV _))) /=.
    rewrite -(wp_bindi (BinOpLCtx PlusOp _)) /=.
    rewrite -wp_load_pst; first (apply sep_intro_True_r; first done); last first.
    { by rewrite lookup_insert. } (* RJ FIXME: figure out why apply and eapply fail. *)
    rewrite -later_intro; apply wand_intro_l; rewrite right_id.
    rewrite -wp_bin_op // -later_intro.
    rewrite -wp_store_pst; first (apply sep_intro_True_r; first done); last first.
    { by rewrite lookup_insert. }
    { done. }
    rewrite -later_intro. apply wand_intro_l. rewrite right_id.
    rewrite -wp_seq -wp_value -later_intro.
    rewrite -wp_load_pst; first (apply sep_intro_True_r; first done); last first.
    { by rewrite lookup_insert. }
    rewrite -later_intro. apply wand_intro_l. rewrite right_id.
    by apply const_intro.
  Qed.

  Definition FindPred (n2 : expr) : expr :=
    rec: "pred" "y" :=
      let: "yp" := "y" + Lit 1 in
      if "yp" < n2 then "pred" "yp" else "y".
  Definition Pred : expr :=
    λ: "x", if "x" ≤ Lit 0 then Lit 0 else FindPred "x" (Lit 0).

  Lemma FindPred_spec n1 n2 E Q :
    (■ (n1 < n2) ∧ Q (LitV (pred n2))) ⊑ wp E (FindPred (Lit n2) (Lit n1)) Q.
  Proof.
    revert n1. apply löb_all_1=>n1.
    rewrite (commutative uPred_and (■ _)%I) associative; apply const_elim_r=>?.
    rewrite -wp_rec //=.
    (* FIXME: ssr rewrite fails with "Error: _pattern_value_ is used in conclusion." *)
    rewrite ->(later_intro (Q _)).
    rewrite -!later_and; apply later_mono.
    (* Go on *)
    rewrite -(wp_bindi (LetCtx _ _)) -wp_bin_op //= -wp_let //=.
    rewrite -(wp_bindi (IfCtx _ _)) /= -!later_intro.
    apply wp_lt=> ?.
    - rewrite -wp_if_true.
      rewrite -!later_intro (forall_elim (n1 + 1)) const_equiv; last omega.
      by rewrite left_id impl_elim_l.
    - assert (n1 = pred n2) as -> by omega.
      rewrite -wp_if_false.
      by rewrite -!later_intro -wp_value' // and_elim_r.
  Qed.

  Lemma Pred_spec n E Q : ▷ Q (LitV (pred n)) ⊑ wp E (Pred (Lit n)) Q.
  Proof.
    rewrite -wp_lam //=.
    rewrite -(wp_bindi (IfCtx _ _)).
    apply later_mono, wp_le=> Hn.
    - rewrite -wp_if_true.
      rewrite -!later_intro -wp_value' //=.
      auto with f_equal omega.
    - rewrite -wp_if_false.
      rewrite -!later_intro -FindPred_spec.
      auto using and_intro, const_intro with omega.
  Qed.

  Goal ∀ E,
    True ⊑ wp (Σ:=Σ) E (let: "x" := Pred (Lit 42) in Pred "x")
                       (λ v, v = LitV 40).
  Proof.
    intros E.
    rewrite -(wp_bindi (LetCtx _ _)) -Pred_spec //= -wp_let //=.
    rewrite -Pred_spec -!later_intro /=. by apply const_intro.
  Qed.
End LiftingTests.
