From algebra Require Export agree.
From program_logic Require Export ghost_ownership.
Import uPred.

Notation savedPropG Λ Σ :=
  (inG Λ Σ (agreeRA (laterC (iPreProp Λ (globalF Σ))))).

Definition saved_prop_own `{savedPropG Λ Σ}
    (γ : gname) (P : iPropG Λ Σ) : iPropG Λ Σ :=
  own γ (to_agree (Next (iProp_unfold P))).
Instance: Params (@saved_prop_own) 4.

Section saved_prop.
  Context `{savedPropG Λ Σ}.
  Implicit Types P Q : iPropG Λ Σ.
  Implicit Types γ : gname.

  Lemma saved_prop_alloc_strong N P (G : gset gname) :
    True ⊑ pvs N N (∃ γ, ■ (γ ∉ G) ∧ saved_prop_own γ P).
  Proof. by apply own_alloc_strong. Qed.

  Lemma saved_prop_alloc N P :
    True ⊑ pvs N N (∃ γ, saved_prop_own γ P).
  Proof. by apply own_alloc. Qed.

  Lemma saved_prop_agree γ P Q :
    (saved_prop_own γ P ★ saved_prop_own γ Q) ⊑ ▷ (P ≡ Q).
  Proof.
    rewrite /saved_prop_own -own_op own_valid agree_validI.
    rewrite agree_equivI later_equivI /=; apply later_mono.
    rewrite -{2}(iProp_fold_unfold P) -{2}(iProp_fold_unfold Q).
    apply (eq_rewrite (iProp_unfold P) (iProp_unfold Q) (λ Q' : iPreProp Λ _,
      iProp_fold (iProp_unfold P) ≡ iProp_fold Q')%I); solve_ne || auto with I.
  Qed.
End saved_prop.
