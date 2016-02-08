Require Export algebra.iprod program_logic.pviewshifts.
Require Import program_logic.ownership.
Import uPred.

Definition gid := positive.
Definition globalC (Σ : gid → iFunctor) : iFunctor :=
  iprodF (λ i, mapF gid (Σ i)).

Class InG Λ (Σ : gid → iFunctor) (i : gid) (A : cmraT) :=
  inG : A = Σ i (laterC (iPreProp Λ (globalC Σ))).
Definition to_Σ {Λ} {Σ : gid → iFunctor} (i : gid) 
           `{!InG Λ Σ i A} (a : A) : Σ i (laterC (iPreProp Λ (globalC Σ))) :=
  eq_rect A id a _ inG.
Definition to_globalC {Λ} {Σ : gid → iFunctor}
           (i : gid) (γ : gid) `{!InG Λ Σ i A} (a : A) : iGst Λ (globalC Σ) :=
  iprod_singleton i {[ γ ↦ to_Σ _ a ]}.
Definition own {Λ} {Σ : gid → iFunctor}
    (i : gid) `{!InG Λ Σ i A} (γ : gid) (a : A) : iProp Λ (globalC Σ) :=
  ownG (to_globalC i γ a).

Section global.
Context {Λ : language} {Σ : gid → iFunctor} (i : gid) `{!InG Λ Σ i A}.
Implicit Types a : A.

(* Proeprties of to_globalC *)
Lemma globalC_op γ a1 a2 :
  to_globalC i γ (a1 ⋅ a2) ≡ to_globalC i γ a1 ⋅ to_globalC i γ a2.
Proof.
  rewrite /to_globalC iprod_op_singleton map_op_singleton.
  apply iprod_singleton_proper, (fin_maps.singleton_proper (M:=gmap _)).
  by rewrite /to_Σ; destruct inG.
Qed.

Lemma globalC_validN n γ a :
  ✓{n} (to_globalC i γ a) <-> ✓{n} a.
Proof.
  rewrite /to_globalC.
  rewrite -iprod_validN_singleton -map_validN_singleton.
  by rewrite /to_Σ; destruct inG.
Qed.

Lemma globalC_unit γ a :
  unit (to_globalC i γ a) ≡ to_globalC i γ (unit a).
Proof.
  rewrite /to_globalC.
  rewrite iprod_unit_singleton map_unit_singleton.
  apply iprod_singleton_proper, (fin_maps.singleton_proper (M:=gmap _)).
  by rewrite /to_Σ; destruct inG.
Qed.

Global Instance globalC_timeless γ m : Timeless m → Timeless (to_globalC i γ m).
Proof.
  rewrite /to_globalC => ?.
  apply iprod_singleton_timeless, map_singleton_timeless.
  by rewrite /to_Σ; destruct inG.
Qed.

(* Properties of own *)

Global Instance own_ne γ n : Proper (dist n ==> dist n) (own i γ).
Proof.
  intros m m' Hm; apply ownG_ne, iprod_singleton_ne, singleton_ne.
  by rewrite /to_globalC /to_Σ; destruct inG.
Qed.

Global Instance own_proper γ : Proper ((≡) ==> (≡)) (own i γ) := ne_proper _.

Lemma own_op γ a1 a2 : own i γ (a1 ⋅ a2) ≡ (own i γ a1 ★ own i γ a2)%I.
Proof. rewrite /own -ownG_op. apply ownG_proper, globalC_op. Qed.

(* TODO: This also holds if we just have ✓a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc E a :
  ✓a → True ⊑ pvs E E (∃ γ, own i γ a).
Proof.
  intros Hm. set (P m := ∃ γ, m = to_globalC i γ a).
  rewrite -(pvs_mono _ _ (∃ m, ■P m ∧ ownG m)%I).
  - rewrite -pvs_updateP_empty //; [].
    subst P. eapply (iprod_singleton_updateP_empty i).
    + eapply map_updateP_alloc' with (x:=to_Σ i a).
      by rewrite /to_Σ; destruct inG.
    + simpl. move=>? [γ [-> ?]]. exists γ. done.
  - apply exist_elim=>m. apply const_elim_l.
    move=>[p ->] {P}. by rewrite -(exist_intro p).
Qed.

Lemma always_own_unit γ m : (□ own i γ (unit m))%I ≡ own i γ (unit m).
Proof. rewrite /own -globalC_unit. by apply always_ownG_unit. Qed.

Lemma own_valid γ m : (own i γ m) ⊑ (✓ m).
Proof.
  rewrite /own ownG_valid. apply uPred.valid_mono=>n.
  by apply globalC_validN.
Qed.

Lemma own_valid_r' γ m : (own i γ m) ⊑ (own i γ m ★ ✓ m).
Proof. apply (uPred.always_entails_r' _ _), own_valid. Qed.

Global Instance ownG_timeless γ m : Timeless m → TimelessP (own i γ m).
Proof.
  intros. apply ownG_timeless. apply _.
Qed.

End global.
