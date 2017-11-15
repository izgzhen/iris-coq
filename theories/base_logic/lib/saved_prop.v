From iris.base_logic Require Export own.
From iris.algebra Require Import agree.
From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(* "Saved anything" -- this can give you saved propositions, saved predicates,
   saved whatever-you-like. *)

Class savedAnythingG (Σ : gFunctors) (F : cFunctor) :=
  saved_anything_inG :> inG Σ (agreeR (F (iPreProp Σ))).
Definition savedAnythingΣ (F : cFunctor) `{!cFunctorContractive F} : gFunctors :=
  #[ GFunctor (agreeRF F) ].

Instance subG_savedAnythingΣ {Σ F} `{!cFunctorContractive F} :
  subG (savedAnythingΣ F) Σ → savedAnythingG Σ F.
Proof. solve_inG. Qed.

Definition saved_anything_own `{savedAnythingG Σ F}
    (γ : gname) (x : F (iProp Σ)) : iProp Σ :=
  own γ (to_agree $ (cFunctor_map F (iProp_fold, iProp_unfold) x)).
Typeclasses Opaque saved_anything_own.
Instance: Params (@saved_anything_own) 3.

Section saved_anything.
  Context `{savedAnythingG Σ F}.
  Implicit Types x y : F (iProp Σ).
  Implicit Types γ : gname.

  Global Instance saved_anything_persistent γ x :
    Persistent (saved_anything_own γ x).
  Proof. rewrite /saved_anything_own; apply _. Qed.

  Lemma saved_anything_alloc_strong x (G : gset gname) :
    (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_anything_own γ x)%I.
  Proof. by apply own_alloc_strong. Qed.

  Lemma saved_anything_alloc x : (|==> ∃ γ, saved_anything_own γ x)%I.
  Proof. by apply own_alloc. Qed.

  Lemma saved_anything_agree γ x y :
    saved_anything_own γ x -∗ saved_anything_own γ y -∗ x ≡ y.
  Proof.
    iIntros "Hx Hy". rewrite /saved_anything_own.
    iDestruct (own_valid_2 with "Hx Hy") as "Hv".
    rewrite agree_validI agree_equivI.
    set (G1 := cFunctor_map F (iProp_fold, iProp_unfold)).
    set (G2 := cFunctor_map F (@iProp_unfold Σ, @iProp_fold Σ)).
    assert (∀ z, G2 (G1 z) ≡ z) as help.
    { intros z. rewrite /G1 /G2 -cFunctor_compose -{2}[z]cFunctor_id.
      apply (ne_proper (cFunctor_map F)); split=>?; apply iProp_fold_unfold. }
    rewrite -{2}[x]help -{2}[y]help. by iApply f_equiv.
  Qed.
End saved_anything.

(** Provide specialized versions of this for convenience. **)

(* Saved propositions. *)
Notation savedPropG Σ := (savedAnythingG Σ (▶ ∙)).
Notation savedPropΣ := (savedAnythingΣ (▶ ∙)).

Definition saved_prop_own `{savedPropG Σ} (γ : gname) (P: iProp Σ) :=
  saved_anything_own (F := ▶ ∙) γ (Next P).

Lemma saved_prop_alloc_strong `{savedPropG Σ} (G : gset gname) (P: iProp Σ) :
  (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_prop_own γ P)%I.
Proof. iApply saved_anything_alloc_strong. Qed.

Lemma saved_prop_alloc `{savedPropG Σ} (P: iProp Σ) :
  (|==> ∃ γ, saved_prop_own γ P)%I.
Proof. iApply saved_anything_alloc. Qed.

Lemma saved_prop_agree `{savedPropG Σ} γ P Q :
  saved_prop_own γ P -∗ saved_prop_own γ Q -∗ ▷ (P ≡ Q).
Proof.
  iIntros "HP HQ". iApply later_equivI. iApply (saved_anything_agree with "HP HQ").
Qed.

(* Saved predicates. *)
Notation savedPredG Σ A := (savedAnythingG Σ (constCF A -n> ▶ ∙)).
Notation savedPredΣ A := (savedAnythingΣ (constCF A -n> ▶ ∙)).

Definition saved_pred_own `{savedPredG Σ A} (γ : gname) (f: A -n> iProp Σ) :=
  saved_anything_own (F := A -n> ▶ ∙) γ (CofeMor Next ◎ f).

Lemma saved_pred_alloc_strong `{savedPredG Σ A} (G : gset gname) (f: A -n> iProp Σ) :
  (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_pred_own γ f)%I.
Proof. iApply saved_anything_alloc_strong. Qed.

Lemma saved_pred_alloc `{savedPredG Σ A} (f: A -n> iProp Σ) :
  (|==> ∃ γ, saved_pred_own γ f)%I.
Proof. iApply saved_anything_alloc. Qed.

(* We put the `x` on the outside to make this lemma easier to apply. *)
Lemma saved_pred_agree `{savedPredG Σ A} γ f g x :
  saved_pred_own γ f -∗ saved_pred_own γ g -∗ ▷ (f x ≡ g x).
Proof.
  iIntros "Hx Hy". unfold saved_pred_own. iApply later_equivI.
  iDestruct (ofe_morC_equivI (CofeMor Next ◎ f) (CofeMor Next ◎ g)) as "[FE _]".
  simpl. iApply ("FE" with "[-]").
  iApply (saved_anything_agree with "Hx Hy").
Qed.
