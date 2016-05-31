From iris.algebra Require Export agree one_shot.
From iris.program_logic Require Export ghost_ownership.
Import uPred.

Class oneShotG (Λ : language) (Σ : gFunctors) (F : cFunctor) :=
  one_shot_inG :> inG Λ Σ (one_shotR $ agreeR $ laterC $ F (iPrePropG Λ Σ)).
Definition oneShotGF (F : cFunctor) : gFunctor :=
  GFunctor (one_shotRF (agreeRF (▶ F))).
Instance inGF_oneShotG  `{inGF Λ Σ (oneShotGF F)} : oneShotG Λ Σ F.
Proof. apply: inGF_inG. Qed.

Definition one_shot_pending `{oneShotG Λ Σ F} (γ : gname) : iPropG Λ Σ :=
  own γ OneShotPending.
Definition one_shot_own `{oneShotG Λ Σ F}
    (γ : gname) (x : F (iPropG Λ Σ)) : iPropG Λ Σ :=
  own γ (Shot $ to_agree $ Next (cFunctor_map F (iProp_fold, iProp_unfold) x)).
Typeclasses Opaque one_shot_pending one_shot_own.
Instance: Params (@one_shot_own) 4.

Section one_shot.
  Context `{oneShotG Λ Σ F}.
  Implicit Types x y : F (iPropG Λ Σ).
  Implicit Types γ : gname.

  Global Instance ne_shot_own_persistent γ x : PersistentP (one_shot_own γ x).
  Proof. rewrite /one_shot_own; apply _. Qed.

  Lemma one_shot_alloc_strong E (G : gset gname) :
    True ={E}=> ∃ γ, ■ (γ ∉ G) ∧ one_shot_pending γ.
  Proof. by apply own_alloc_strong. Qed.

  Lemma one_shot_alloc E : True ={E}=> ∃ γ, one_shot_pending γ.
  Proof. by apply own_alloc. Qed.

  Lemma one_shot_init E γ x : one_shot_pending γ ={E}=> one_shot_own γ x.
  Proof. by apply own_update, one_shot_update_shoot. Qed.

  Lemma one_shot_alloc_init E x : True ={E}=> ∃ γ, one_shot_own γ x.
  Proof.
    rewrite (one_shot_alloc E). apply pvs_strip_pvs.
    apply exist_elim=>γ. rewrite -(exist_intro γ).
    apply one_shot_init.
  Qed.

  Lemma one_shot_agree γ x y : (one_shot_own γ x ★ one_shot_own γ y) ⊢ ▷(x ≡ y).
  Proof.
    rewrite -own_op own_valid one_shot_validI /= agree_validI.
    rewrite agree_equivI later_equivI.
    set (G1 := cFunctor_map F (iProp_fold, iProp_unfold)).
    set (G2 := cFunctor_map F (@iProp_unfold Λ (globalF Σ),
                               @iProp_fold Λ (globalF Σ))).
    assert (∀ z, G2 (G1 z) ≡ z) as help.
    { intros z. rewrite /G1 /G2 -cFunctor_compose -{2}[z]cFunctor_id.
      apply (ne_proper (cFunctor_map F)); split=>?; apply iProp_fold_unfold. }
    rewrite -{2}[x]help -{2}[y]help. apply later_mono.
    apply (eq_rewrite (G1 x) (G1 y) (λ z, G2 (G1 x) ≡ G2 z))%I;
      first solve_proper; auto with I.
  Qed.
End one_shot.
