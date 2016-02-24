From algebra Require Export agree.
From program_logic Require Export global_functor.
Import uPred.

Notation savedPropG Λ Σ :=
  (inG Λ Σ (agreeRA (laterC (iPreProp Λ (globalF Σ))))).

Instance inGF_savedPropG `{inGF Λ Σ agreeF} : savedPropG Λ Σ.
Proof. apply: inGF_inG. Qed.

Definition saved_prop_own_def `{savedPropG Λ Σ}
    (γ : gname) (P : iPropG Λ Σ) : iPropG Λ Σ :=
  own γ (to_agree (Next (iProp_unfold P))).
(* Perform sealing. *)
Module Type SavedPropOwnSig.
  Parameter saved_prop_own : ∀ `{savedPropG Λ Σ} (γ : gname) (P : iPropG Λ Σ),
    iPropG Λ Σ.
  Axiom saved_prop_own_eq : @saved_prop_own = @saved_prop_own_def.
End SavedPropOwnSig.
Module Export SavedPropOwn : SavedPropOwnSig.
  Definition saved_prop_own := @saved_prop_own_def.
  Definition saved_prop_own_eq := Logic.eq_refl (@saved_prop_own).
End SavedPropOwn. 
Instance: Params (@saved_prop_own) 4.

Section saved_prop.
  Context `{savedPropG Λ Σ}.
  Implicit Types P Q : iPropG Λ Σ.
  Implicit Types γ : gname.

  Global Instance saved_prop_always_stable γ P :
    AlwaysStable (saved_prop_own γ P).
  Proof. by rewrite /AlwaysStable saved_prop_own_eq always_own. Qed.

  Lemma saved_prop_alloc_strong N P (G : gset gname) :
    True ⊑ pvs N N (∃ γ, ■ (γ ∉ G) ∧ saved_prop_own γ P).
  Proof. by rewrite saved_prop_own_eq; apply own_alloc_strong. Qed.

  Lemma saved_prop_alloc N P :
    True ⊑ pvs N N (∃ γ, saved_prop_own γ P).
  Proof. by rewrite saved_prop_own_eq; apply own_alloc. Qed.

  Lemma saved_prop_agree γ P Q :
    (saved_prop_own γ P ★ saved_prop_own γ Q) ⊑ ▷ (P ≡ Q).
  Proof.
    rewrite saved_prop_own_eq -own_op own_valid agree_validI.
    rewrite agree_equivI later_equivI /=; apply later_mono.
    rewrite -{2}(iProp_fold_unfold P) -{2}(iProp_fold_unfold Q).
    apply (eq_rewrite (iProp_unfold P) (iProp_unfold Q) (λ Q' : iPreProp Λ _,
      iProp_fold (iProp_unfold P) ≡ iProp_fold Q')%I); solve_ne || auto with I.
  Qed.
End saved_prop.
