From algebra Require Export agree.
From program_logic Require Export ghost_ownership.
Import uPred.

Class SavedPropInG Λ Σ (i : gid) :=
  saved_prop_inG :> InG Λ Σ i (agreeRA (laterC (iPreProp Λ (globalF Σ)))).

Definition saved_prop_own {Λ Σ} (i : gid) `{SavedPropInG Λ Σ i}
    (γ : gname) (P : iPropG Λ Σ) : iPropG Λ Σ :=
  own i γ (to_agree (Next (iProp_unfold P))).
Instance: Params (@saved_prop_own) 5.

Section saved_prop.
  Context `{SavedPropInG Λ Σ SPI}.
  Implicit Types P Q : iPropG Λ Σ.
  Implicit Types γ : gname.

  Lemma saved_prop_alloc N P :
    True ⊑ pvs N N (∃ γ, saved_prop_own SPI γ P).
  Proof. by apply own_alloc. Qed.

  Lemma saved_prop_twice γ P Q :
    (saved_prop_own SPI γ P ★ saved_prop_own SPI γ Q) ⊑ ▷ (P ↔ Q).
  Proof.
    rewrite /saved_prop_own -own_op own_valid agree_validI.
    rewrite agree_equivI later_equivI /=; apply later_mono.
    rewrite -{2}(iProp_fold_unfold P) -{2}(iProp_fold_unfold Q).
    apply (eq_rewrite (iProp_unfold P) (iProp_unfold Q) (λ Q' : iPreProp Λ _,
      iProp_fold (iProp_unfold P) ↔ iProp_fold Q')%I); solve_ne || auto with I.
  Qed.
End saved_prop.
