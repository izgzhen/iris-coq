(** This file tests a bunch of things. *)
From program_logic Require Import model saved_prop.

Module ModelTest. (* Make sure we got the notations right. *)
  Definition iResTest {Λ : language} {Σ : rFunctor}
    (w : iWld Λ Σ) (p : iPst Λ) (g : iGst Λ Σ) : iRes Λ Σ := Res w p (Some g).
End ModelTest.

Module SavedPropTest.
  (* Test if we can really go "crazy higher order" *)
  Section sec.
    Definition Σ : rFunctorG := #[ agreeRF (cofe_morCF laterCF laterCF) ].
    Context {Λ : language}.
    Notation iProp := (iPropG Λ Σ).

    Local Instance : savedPropG Λ Σ (cofe_morCF laterCF laterCF) := _.

    Definition own_pred γ (φ : laterC iProp -n> laterC iProp) : iProp :=
      saved_prop_own γ φ.
  End sec.
End SavedPropTest.
