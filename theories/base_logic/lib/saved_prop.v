From iris.base_logic Require Export own.
From iris.algebra Require Import agree.
From stdpp Require Import gmap.
Set Default Proof Using "Type".
Import uPred.

Class savedPropG (Σ : gFunctors) (F : cFunctor) :=
  saved_prop_inG :> inG Σ (agreeR (laterC (F (iPreProp Σ)))).
Definition savedPropΣ (F : cFunctor) : gFunctors :=
  #[ GFunctor (agreeRF (▶ F)) ].

Instance subG_savedPropΣ  {Σ F} : subG (savedPropΣ F) Σ → savedPropG Σ F.
Proof. solve_inG. Qed.

Definition saved_prop_own `{savedPropG Σ F}
    (γ : gname) (x : F (iProp Σ)) : iProp Σ :=
  own γ (to_agree $ Next (cFunctor_map F (iProp_fold, iProp_unfold) x)).
Typeclasses Opaque saved_prop_own.
Instance: Params (@saved_prop_own) 3.

Section saved_prop.
  Context `{savedPropG Σ F}.
  Implicit Types x y : F (iProp Σ).
  Implicit Types γ : gname.

  Global Instance saved_prop_persistent γ x : Persistent (saved_prop_own γ x).
  Proof. rewrite /saved_prop_own; apply _. Qed.

  Lemma saved_prop_alloc_strong x (G : gset gname) :
    (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_prop_own γ x)%I.
  Proof. by apply own_alloc_strong. Qed.

  Lemma saved_prop_alloc x : (|==> ∃ γ, saved_prop_own γ x)%I.
  Proof. by apply own_alloc. Qed.

  Lemma saved_prop_agree γ x y :
    saved_prop_own γ x -∗ saved_prop_own γ y -∗ ▷ (x ≡ y).
  Proof.
    apply wand_intro_r.
    rewrite -own_op own_valid agree_validI agree_equivI later_equivI.
    set (G1 := cFunctor_map F (iProp_fold, iProp_unfold)).
    set (G2 := cFunctor_map F (@iProp_unfold Σ, @iProp_fold Σ)).
    assert (∀ z, G2 (G1 z) ≡ z) as help.
    { intros z. rewrite /G1 /G2 -cFunctor_compose -{2}[z]cFunctor_id.
      apply (ne_proper (cFunctor_map F)); split=>?; apply iProp_fold_unfold. }
    rewrite -{2}[x]help -{2}[y]help. apply later_mono.
    apply (internal_eq_rewrite (G1 x) (G1 y) (λ z, G2 (G1 x) ≡ G2 z))%I;
      first solve_proper; auto with I.
  Qed.
End saved_prop.
