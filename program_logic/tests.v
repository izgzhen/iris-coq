(** This file tests a bunch of things. *)
From program_logic Require Import model saved_prop.

Module ModelTest. (* Make sure we got the notations right. *)
  Definition iResTest {Λ : language} {Σ : iFunctor}
    (w : iWld Λ Σ) (p : iPst Λ) (g : iGst Λ Σ) : iRes Λ Σ := Res w p g.
End ModelTest.

Module SavedPropTest.
  (* Test if we can really go "crazy higher order" *)
  Section sec.
    Definition F : cFunctor := ( ∙ -n> ∙ ).
    Definition Σ : gFunctors := #[ savedPropGF F ].
    Context {Λ : language}.
    Notation iProp := (iPropG Λ Σ).

    Local Instance : savedPropG Λ Σ F := _.

    Definition own_pred γ (φ : iProp -n> iProp) : iProp :=
      saved_prop_own γ φ.
  End sec.
End SavedPropTest.
