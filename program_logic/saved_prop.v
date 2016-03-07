From algebra Require Export agree.
From program_logic Require Export ghost_ownership.
Import uPred.

Class savedPropG (Λ : language) (Σ : gFunctors) (F : cFunctor) :=
  saved_prop_inG :> inG Λ Σ (agreeR (laterC (F (iPreProp Λ (globalF Σ))))).
Definition savedPropGF (F : cFunctor) : gFunctor :=
  GFunctor (agreeRF (▶ F)).
Instance inGF_savedPropG  `{inGF Λ Σ (savedPropGF F)} : savedPropG Λ Σ F.
Proof. apply: inGF_inG. Qed.

Definition saved_prop_own `{savedPropG Λ Σ F}
    (γ : gname) (x : F (iPropG Λ Σ)) : iPropG Λ Σ :=
  own γ (to_agree $ Next (cFunctor_map F (iProp_fold, iProp_unfold) x)).
Typeclasses Opaque saved_prop_own.
Instance: Params (@saved_prop_own) 4.

Section saved_prop.
  Context `{savedPropG Λ Σ F}.
  Implicit Types x y : F (iPropG Λ Σ).
  Implicit Types γ : gname.

  Global Instance saved_prop_always_stable γ x :
    AlwaysStable (saved_prop_own γ x).
  Proof. by rewrite /AlwaysStable always_own. Qed.

  Lemma saved_prop_alloc_strong N x (G : gset gname) :
    True ⊑ pvs N N (∃ γ, ■ (γ ∉ G) ∧ saved_prop_own γ x).
  Proof. by apply own_alloc_strong. Qed.

  Lemma saved_prop_alloc N x : True ⊑ pvs N N (∃ γ, saved_prop_own γ x).
  Proof. by apply own_alloc. Qed.

  Lemma saved_prop_agree γ x y :
    (saved_prop_own γ x ★ saved_prop_own γ y) ⊑ ▷(x ≡ y).
  Proof.
    rewrite -own_op own_valid agree_validI agree_equivI later_equivI.
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
End saved_prop.
