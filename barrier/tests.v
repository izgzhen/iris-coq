(** This file is essentially a bunch of testcases. *)
Require Import modures.logic.
Require Import barrier.lifting.
Import uPred.

Module LangTests.
  Definition add :=  Plus (LitNat 21) (LitNat 21).
  Goal ∀ σ, prim_step add σ (LitNat 42) σ None.
  Proof.
    constructor.
  Qed.

  Definition rec := Rec (App (Var 0) (Var 1)). (* fix f x => f x *)
  Definition rec_app := App rec (LitNat 0).
  Goal ∀ σ, prim_step rec_app σ rec_app σ None.
  Proof.
    move=>?. eapply BetaS.
    reflexivity.
  Qed.

  Definition lam := Lam (Plus (Var 0) (LitNat 21)).
  Goal ∀ σ, prim_step (App lam (LitNat 21)) σ add σ None.
  Proof.
    move=>?. eapply BetaS. reflexivity.
  Qed.
End LangTests.

Module ParamTests.
  Print Assumptions Σ.
End ParamTests.

Module LiftingTests.
  (* TODO RJ: Some syntactic sugar for language expressions would be nice. *)
  Definition e3 := Load (Var 0).
  Definition e2 := Seq (Store (Var 0) (Plus (Load $ Var 0) (LitNat 1))) e3.
  Definition e := Let (Alloc (LitNat 1)) e2.
  Goal ∀ σ E, (ownP (Σ:=Σ) σ) ⊑ (wp (Σ:=Σ) E e (λ v, ■(v = LitNatV 2))).
  Proof.
    move=> σ E. rewrite /e.
    rewrite -wp_let. rewrite -wp_alloc_pst; last done.
    apply sep_intro_True_r; first done.
    rewrite -later_intro. apply forall_intro=>l.
    apply wand_intro_l. rewrite right_id. apply const_elim_l; move=>_.
    rewrite -later_intro. asimpl.
    rewrite -(wp_bind (SeqCtx EmptyCtx (Load (Loc _)))).
    rewrite -(wp_bind (StoreRCtx (LocV _) EmptyCtx)).
    rewrite -(wp_bind (PlusLCtx EmptyCtx _)).
    rewrite -wp_load_pst; first (apply sep_intro_True_r; first done); last first.
    { apply: lookup_insert. } (* RJ TODO: figure out why apply and eapply fail. *)
    rewrite -later_intro. apply wand_intro_l. rewrite right_id.
    rewrite -wp_plus -later_intro.
    rewrite -wp_store_pst; first (apply sep_intro_True_r; first done); last first.
    { apply: lookup_insert. }
    { reflexivity. }
    rewrite -later_intro. apply wand_intro_l. rewrite right_id.
    rewrite -wp_lam // -later_intro. asimpl.
    rewrite -wp_load_pst; first (apply sep_intro_True_r; first done); last first.
    { apply: lookup_insert. }
    rewrite -later_intro. apply wand_intro_l. rewrite right_id.
    by apply const_intro.
  Qed.

  Import Nat.

  Definition Lt e1 e2 := Le (Plus e1 $ LitNat 1) e2.
  Definition FindPred' n1 Sn1 n2 f := If (Lt Sn1 n2)
                                      (App f Sn1)
                                      n1.
  Definition FindPred n2 := Rec (Let (Plus (Var 1) (LitNat 1))
                                     (FindPred' (Var 2) (Var 0) n2.[ren(+3)] (Var 1))).
  Lemma FindPred_spec n1 n2 E Q :
    (■(n1 < n2) ∧ Q (LitNatV $ pred n2)) ⊑
       wp (Σ:=Σ) E (App (FindPred (LitNat n2)) (LitNat n1)) Q.
  Proof.
    revert n1. apply löb_all_1=>n1.
    rewrite -wp_rec //. asimpl.
    (* Get rid of the ▷ in the premise. *)
    etransitivity; first (etransitivity; last eapply equiv_spec, later_and).
    { apply and_mono; first done. by rewrite -later_intro. }
    apply later_mono.
    (* Go on. *)
    rewrite -(wp_let _ (FindPred' (LitNat n1) (Var 0) (LitNat n2) (FindPred $ LitNat n2))).
    rewrite -wp_plus. asimpl.
    rewrite -(wp_bind (CaseCtx EmptyCtx _ _)).
    rewrite -(wp_bind (LeLCtx EmptyCtx _)).
    rewrite -wp_plus -!later_intro. simpl.
    assert (Decision (S n1 + 1 ≤ n2)) as Hn12 by apply _.
    destruct Hn12 as [Hle|Hgt].
    - rewrite -wp_le_true /= //. rewrite -wp_case_inl //.
      rewrite -!later_intro. asimpl.
      rewrite (forall_elim (S n1)).
      eapply impl_elim; first by eapply and_elim_l. apply and_intro.
      + apply const_intro; omega.
      + by rewrite !and_elim_r.
    - rewrite -wp_le_false /= // -wp_case_inr //.
      rewrite -!later_intro -wp_value' //.
      rewrite and_elim_r. apply const_elim_l=>Hle.
      assert (Heq: n1 = pred n2) by omega. by subst n1.
  Qed.

  Definition Pred := Lam (If (Le (Var 0) (LitNat 0))
                             (LitNat 0)
                             (App (FindPred (Var 0)) (LitNat 0))
                         ).
  Lemma Pred_spec n E Q :
    ▷Q (LitNatV $ pred n) ⊑ wp (Σ:=Σ) E (App Pred (LitNat n)) Q.
  Proof.
    rewrite -wp_lam //. asimpl.
    rewrite -(wp_bind (CaseCtx EmptyCtx _ _)).
    assert (Decision (n ≤ 0)) as Hn by apply _.
    destruct Hn as [Hle|Hgt].
    - rewrite -wp_le_true /= //. rewrite -wp_case_inl //.
      apply later_mono. rewrite -!later_intro -wp_value' //.
      assert (Heq: n = 0) by omega. by subst n.
    - rewrite -wp_le_false /= // -wp_case_inr //.
      apply later_mono. rewrite -!later_intro -FindPred_spec. apply and_intro.
      + by apply const_intro; omega.
      + done.
  Qed.
End LiftingTests.
