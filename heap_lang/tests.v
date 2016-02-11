(** This file is essentially a bunch of testcases. *)
Require Import program_logic.ownership.
Require Import heap_lang.notation.
Import uPred.

Module LangTests.
  Definition add := ('21 + '21)%L.
  Goal ∀ σ, prim_step add σ ('42) σ None.
  Proof. intros; do_step done. Qed.
  Definition rec_app : expr := ((rec: "f" "x" := "f" "x") '0)%L.
  Goal ∀ σ, prim_step rec_app σ rec_app σ None.
  Proof.
    intros. rewrite /rec_app. (* FIXME: do_step does not work here *)
    by eapply (Ectx_step  _ _ _ _ _ []), (BetaS _ _ _ _ '0)%L.
  Qed.
  Definition lam : expr := λ: "x", "x" + '21.
  Goal ∀ σ, prim_step (lam '21)%L σ add σ None.
  Proof.
    intros. rewrite /lam. (* FIXME: do_step does not work here *)
    by eapply (Ectx_step  _ _ _ _ _ []), (BetaS "" "x" ("x" + '21) _ '21)%L.
  Qed.
End LangTests.

Module LiftingTests.
  Context {Σ : iFunctor}.
  Implicit Types P : iProp heap_lang Σ.
  Implicit Types Q : val → iProp heap_lang Σ.

  Definition e  : expr :=
    let: "x" := ref '1 in "x" <- !"x" + '1;; !"x".
  Goal ∀ σ E, ownP (Σ:=Σ) σ ⊑ wp E e (λ v, v = ('2)%L).
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

  Definition FindPred : val :=
    rec: "pred" "x" "y" :=
      let: "yp" := "y" + '1 in
      if "yp" < "x" then "pred" "x" "yp" else "y".
  Definition Pred : val :=
    λ: "x", if "x" ≤ '0 then -FindPred (-"x" + '2) '0 else FindPred "x" '0.

  Lemma FindPred_spec n1 n2 E Q :
    (■ (n1 < n2) ∧ Q (LitV (n2 - 1))) ⊑ wp E (FindPred 'n2 'n1)%L Q.
  Proof.
    (* FIXME there are some annoying scopes shown here: %Z, %L. *)
    revert n1; apply löb_all_1=>n1.
    rewrite (comm uPred_and (■ _)%I) assoc; apply const_elim_r=>?.
    (* first need to do the rec to get a later *)
    rewrite -(wp_bindi (AppLCtx _)).
    rewrite -wp_rec' // =>-/=; rewrite -wp_value' //=.
    (* FIXME: ssr rewrite fails with "Error: _pattern_value_ is used in conclusion." *)
    rewrite ->(later_intro (Q _)).
    rewrite -!later_and; apply later_mono.
    (* Go on *)
    rewrite -wp_let //= -later_intro.
    rewrite -(wp_bindi (LetCtx _ _)) -wp_bin_op //= -wp_let //=.
    rewrite -(wp_bindi (IfCtx _ _)) /= -!later_intro.
    apply wp_lt=> ?.
    - rewrite -wp_if_true.
      rewrite -!later_intro (forall_elim (n1 + 1)) const_equiv; last omega.
      by rewrite left_id impl_elim_l.
    - assert (n1 = n2 - 1) as -> by omega.
      rewrite -wp_if_false.
      by rewrite -!later_intro -wp_value' // and_elim_r.
  Qed.

  Lemma Pred_spec n E Q : ▷ Q (LitV (n - 1)) ⊑ wp E (Pred 'n)%L Q.
  Proof.
    rewrite -wp_lam //=.
    rewrite -(wp_bindi (IfCtx _ _)) /=.
    apply later_mono, wp_le=> Hn.
    - rewrite -wp_if_true.
      rewrite -(wp_bindi (UnOpCtx _)) /=.
      rewrite -(wp_bind [AppLCtx _; AppRCtx _]) /=.
      rewrite -(wp_bindi (BinOpLCtx _ _)) /=.
      rewrite -wp_un_op //=.
      rewrite -wp_bin_op //= -!later_intro.
      rewrite -FindPred_spec. apply and_intro; first by (apply const_intro; omega).
      rewrite -wp_un_op //= -later_intro.
      by assert (n - 1 = - (- n + 2 - 1)) as -> by omega.
    - rewrite -wp_if_false.
      rewrite -!later_intro -FindPred_spec.
      auto using and_intro, const_intro with omega.
  Qed.

  Goal ∀ E,
    True ⊑ wp (Σ:=Σ) E (let: "x" := Pred '42 in Pred "x")
                       (λ v, v = ('40)%L).
  Proof.
    intros E.
    rewrite -(wp_bindi (LetCtx _ _)) -Pred_spec //= -wp_let //=.
    by rewrite -Pred_spec -!later_intro /=.
  Qed.
End LiftingTests.
