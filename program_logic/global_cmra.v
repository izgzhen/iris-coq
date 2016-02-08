Require Export algebra.iprod program_logic.ownership program_logic.pviewshifts.
Import uPred.

Definition gid := positive.
Definition globalC (Δ : gid → iFunctor) : iFunctor :=
  iprodF (λ i, mapF gid (Δ i)).

Class InG Λ (Δ : gid → iFunctor) (i : gid) (A : cmraT) :=
  inG : A = Δ i (laterC (iPreProp Λ (globalC Δ))).
Definition to_funC {Λ} {Δ : gid → iFunctor} (i : gid) 
           `{!InG Λ Δ i A} (a : A) : Δ i (laterC (iPreProp Λ (globalC Δ))) :=
  eq_rect A id a _ inG.
Definition to_globalC {Λ} {Δ : gid → iFunctor}
           (i : gid) (γ : gid) `{!InG Λ Δ i A} (a : A) : iGst Λ (globalC Δ) :=
  iprod_singleton i {[ γ ↦ to_funC _ a ]}.
Definition own {Λ} {Δ : gid → iFunctor}
    (i : gid) `{!InG Λ Δ i A} (γ : gid) (a : A) : iProp Λ (globalC Δ) :=
  ownG (Σ:=globalC Δ) (to_globalC i γ a).

Section global.
Context {Λ : language} {Δ : gid → iFunctor} (i : gid) `{!InG Λ Δ i A}.
Implicit Types a : A.

(* Proeprties of to_globalC *)
Lemma globalC_op γ a1 a2 :
  to_globalC i γ (a1 ⋅ a2) ≡ to_globalC i γ a1 ⋅ to_globalC i γ a2.
Proof.
  rewrite /to_globalC iprod_op_singleton map_op_singleton.
  apply iprod_singleton_proper, (fin_maps.singleton_proper (M:=gmap _)).
  by rewrite /to_funC; destruct inG.
Qed.

Lemma globalC_validN n γ a :
  ✓{n} (to_globalC i γ a) <-> ✓{n} a.
Proof.
  rewrite /to_globalC.
  rewrite -iprod_validN_singleton -map_validN_singleton.
  by rewrite /to_funC; destruct inG.
Qed.

(* Properties of own *)

Global Instance own_ne γ n : Proper (dist n ==> dist n) (own i γ).
Proof.
  intros m m' Hm; apply ownG_ne, iprod_singleton_ne, singleton_ne.
  by rewrite /to_globalC /to_funC; destruct inG.
Qed.

Global Instance own_proper γ : Proper ((≡) ==> (≡)) (own i γ) := ne_proper _.

Lemma own_op γ a1 a2 : own i γ (a1 ⋅ a2) ≡ (own i γ a1 ★ own i γ a2)%I.
Proof. rewrite /own -ownG_op. apply ownG_proper, globalC_op. Qed.

(* TODO: This also holds if we just have ✓a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc E a :
  ✓a → True ⊑ pvs E E (∃ γ, own (Δ:=Δ) i γ a).
Proof.
  intros Hm. set (P m := ∃ γ, m = to_globalC (Δ:=Δ) i γ a).
  rewrite -(pvs_mono _ _ (∃ m, ■P m ∧ ownG m)%I).
  - rewrite -pvs_updateP_empty //; [].
    subst P. eapply (iprod_singleton_updateP_empty i).
    + eapply map_updateP_alloc' with (x:=to_funC i a).
      by rewrite /to_funC; destruct inG.
    + simpl. move=>? [γ [-> ?]]. exists γ. done.
  - apply exist_elim=>m. apply const_elim_l.
    move=>[p ->] {P}. by rewrite -(exist_intro p).
Qed.

Lemma always_own_unit γ m : (□ own i γ (unit m))%I ≡ own i γ (unit m).
Proof.
  rewrite /own.
Admitted.

Lemma own_valid γ m : (own i γ m) ⊑ (✓ m).
Proof.
  rewrite /own ownG_valid. apply uPred.valid_mono=>n.
  by apply globalC_validN.
Qed.

Lemma own_valid_r' γ m : (own i γ m) ⊑ (own i γ m ★ ✓ m).
Proof. apply (uPred.always_entails_r' _ _), own_valid. Qed.

Global Instance ownG_timeless γ m : Timeless m → TimelessP (own i γ m).
Proof.
  intros. apply ownG_timeless.
Admitted.

End global.
