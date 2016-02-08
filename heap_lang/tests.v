(** This file is essentially a bunch of testcases. *)
Require Import program_logic.upred.
Require Import heap_lang.lifting heap_lang.sugar.
Import heap_lang uPred notations.

Module LangTests.
  Definition add := (21 + 21)%L.
  Goal ∀ σ, prim_step add σ 42 σ None.
  Proof. intros; do_step done. Qed.
  Definition rec : expr := rec:: #0 #1. (* fix f x => f x *)
  Definition rec_app : expr := rec 0.
  Goal ∀ σ, prim_step rec_app σ rec_app σ None.
  Proof. Set Printing All. intros; do_step done. Qed.
  Definition lam : expr := λ: #0 + 21.
  Goal ∀ σ, prim_step (App lam (LitNat 21)) σ add σ None.
  Proof. intros; do_step done. Qed.
End LangTests.

Module LiftingTests.
  Context {Σ : iFunctor}.
  Implicit Types P : iProp heap_lang Σ.
  Implicit Types Q : val → iProp heap_lang Σ.

  (* FIXME: Fix levels so that we do not need the parenthesis here. *)
  Definition e  : expr := let: ref 1 in #0 <- !#0 + 1; !#0.
  Goal ∀ σ E, (ownP σ : iProp heap_lang Σ) ⊑ (wp E e (λ v, ■(v = 2))).
  Proof.
    move=> σ E. rewrite /e.
    rewrite -wp_let. rewrite -wp_alloc_pst; last done.
    apply sep_intro_True_r; first done.
    rewrite -later_intro. apply forall_intro=>l.
    apply wand_intro_l. rewrite right_id. apply const_elim_l; move=>_.
    rewrite -later_intro. asimpl.
    (* TODO RJ: If you go here, you can see how the sugar does not print
       all so nicely. *)
    rewrite -(wp_bindi (SeqCtx (Load (Loc _)))).
    rewrite -(wp_bindi (StoreRCtx (LocV _))).
    rewrite -(wp_bindi (PlusLCtx _)).
    rewrite -wp_load_pst; first (apply sep_intro_True_r; first done); last first.
    { by rewrite lookup_insert. } (* RJ FIXME: figure out why apply and eapply fail. *)
    rewrite -later_intro. apply wand_intro_l. rewrite right_id.
    rewrite -wp_plus -later_intro.
    rewrite -wp_store_pst; first (apply sep_intro_True_r; first done); last first.
    { by rewrite lookup_insert. }
    { done. }
    rewrite -later_intro. apply wand_intro_l. rewrite right_id.
    rewrite -wp_lam // -later_intro. asimpl.
    rewrite -wp_load_pst; first (apply sep_intro_True_r; first done); last first.
    { by rewrite lookup_insert. }
    rewrite -later_intro. apply wand_intro_l. rewrite right_id.
    by apply const_intro.
  Qed.

  (* TODO: once asimpl preserves notation, we don't need
     FindPred' anymore. *)
  (* FIXME: fix notation so that we do not need parenthesis or %L *)
  Definition FindPred' n1 Sn1 n2 f : expr :=
    if Sn1 < n2 then f Sn1 else n1.
  Definition FindPred n2 : expr :=
    rec:: (let: #1 + 1 in FindPred' #2 #0 n2.[ren(+3)] #1)%L.
  Definition Pred : expr :=
    λ: (if #0 ≤ 0 then 0 else FindPred #0 0)%L.

  Lemma FindPred_spec n1 n2 E Q :
    (■(n1 < n2) ∧ Q (pred n2)) ⊑
       wp E (FindPred n2 n1) Q.
  Proof.
    revert n1. apply löb_all_1=>n1.
    rewrite -wp_rec //. asimpl.
    (* Get rid of the ▷ in the premise. *)
    etransitivity; first (etransitivity; last eapply equiv_spec, later_and).
    { apply and_mono; first done. by rewrite -later_intro. }
    apply later_mono.
    (* Go on. *)
    rewrite -(wp_let _ _ (FindPred' n1 #0 n2 (FindPred n2))).
    rewrite -wp_plus. asimpl.
    rewrite -(wp_bindi (CaseCtx _ _)).
    rewrite -!later_intro /=.
    apply wp_lt; intros Hn12.
    * (* TODO RJ: It would be better if we could use wp_if_true here
         (and below). But we cannot, because the substitutions in there
         got already unfolded. *)
      rewrite -wp_case_inl //.
      rewrite -!later_intro. asimpl.
      rewrite (forall_elim (S n1)).
      eapply impl_elim; first by eapply and_elim_l. apply and_intro.
      + apply const_intro; omega.
      + by rewrite !and_elim_r.
    * rewrite -wp_case_inr //.
      rewrite -!later_intro -wp_value' //.
      rewrite and_elim_r. apply const_elim_l=>Hle.
      by replace n1 with (pred n2) by omega.
  Qed.

  Lemma Pred_spec n E Q :
    ▷Q (pred n) ⊑ wp E (Pred n) Q.
  Proof.
    rewrite -wp_lam //. asimpl.
    rewrite -(wp_bindi (CaseCtx _ _)).
    apply later_mono, wp_le=> Hn.
    - rewrite -wp_case_inl //.
      rewrite -!later_intro -wp_value' //.
      by replace n with 0 by omega.
    - rewrite -wp_case_inr //.
      rewrite -!later_intro -FindPred_spec.
      auto using and_intro, const_intro with omega.
  Qed.

  Goal ∀ E,
    True ⊑ wp (Σ:=Σ) E (let: Pred 42 in Pred #0) (λ v, ■(v = 40)).
  Proof.
    intros E. rewrite -wp_let. rewrite -Pred_spec -!later_intro.
    asimpl. (* TODO RJ: Can we somehow make it so that Pred gets folded again? *)
    rewrite -Pred_spec -later_intro. by apply const_intro.
  Qed.
End LiftingTests.
