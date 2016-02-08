Require Export algebra.iprod program_logic.pviewshifts.
Require Import program_logic.ownership.
Import uPred.

Definition gid := positive.
Definition globalC (Σ : gid → iFunctor) : iFunctor :=
  iprodF (λ i, mapF gid (Σ i)).

Class InG (Λ : language) (Σ : gid → iFunctor) (i : gid) (A : cmraT) :=
  inG : A = Σ i (laterC (iPreProp Λ (globalC Σ))).

Section global.
Context {Λ : language} {Σ : gid → iFunctor} (i : gid) `{!InG Λ Σ i A}.
Implicit Types a : A.

Definition to_Σ (a : A) : Σ i (laterC (iPreProp Λ (globalC Σ))) :=
  eq_rect A id a _ inG.
Definition to_globalC (γ : gid) `{!InG Λ Σ i A} (a : A) : iGst Λ (globalC Σ) :=
  iprod_singleton i {[ γ ↦ to_Σ a ]}.
Definition own (γ : gid) (a : A) : iProp Λ (globalC Σ) :=
  ownG (to_globalC γ a).

Definition from_Σ (b : Σ i (laterC (iPreProp Λ (globalC Σ)))) : A  :=
  eq_rect (Σ i _) id b _ (Logic.eq_sym inG).
Definition P_to_Σ (P : A → Prop) (b : Σ i (laterC (iPreProp Λ (globalC Σ)))) : Prop
  := P (from_Σ b).

(* Properties of the transport. *)
Lemma to_from_Σ b :
  to_Σ (from_Σ b) = b.
Proof.
  rewrite /to_Σ /from_Σ. by destruct inG.
Qed.

(* Properties of to_globalC *)
Lemma globalC_op γ a1 a2 :
  to_globalC γ (a1 ⋅ a2) ≡ to_globalC γ a1 ⋅ to_globalC γ a2.
Proof.
  rewrite /to_globalC iprod_op_singleton map_op_singleton.
  apply iprod_singleton_proper, (fin_maps.singleton_proper (M:=gmap _)).
  by rewrite /to_Σ; destruct inG.
Qed.

Lemma globalC_validN n γ a : ✓{n} (to_globalC γ a) ↔ ✓{n} a.
Proof.
  rewrite /to_globalC iprod_singleton_validN map_singleton_validN.
  by rewrite /to_Σ; destruct inG.
Qed.

Lemma globalC_unit γ a :
  unit (to_globalC γ a) ≡ to_globalC γ (unit a).
Proof.
  rewrite /to_globalC.
  rewrite iprod_unit_singleton map_unit_singleton.
  apply iprod_singleton_proper, (fin_maps.singleton_proper (M:=gmap _)).
  by rewrite /to_Σ; destruct inG.
Qed.

Global Instance globalC_timeless γ m : Timeless m → Timeless (to_globalC γ m).
Proof.
  rewrite /to_globalC => ?.
  apply (iprod_singleton_timeless _ _ _), map_singleton_timeless.
  by rewrite /to_Σ; destruct inG.
Qed.

(* Properties of the lifted frame-preserving updates *)
Lemma update_to_Σ a P :
  a ~~>: P → to_Σ a ~~>: P_to_Σ P.
Proof.
  move=>Hu gf n Hf. destruct (Hu (from_Σ gf) n) as [a' Ha'].
  { move: Hf. rewrite /to_Σ /from_Σ. by destruct inG. }
  exists (to_Σ a'). move:Hf Ha'.
  rewrite /P_to_Σ /to_Σ /from_Σ. destruct inG. done.
Qed. 

(* Properties of own *)

Global Instance own_ne γ n : Proper (dist n ==> dist n) (own γ).
Proof.
  intros m m' Hm; apply ownG_ne, iprod_singleton_ne, singleton_ne.
  by rewrite /to_globalC /to_Σ; destruct inG.
Qed.

Global Instance own_proper γ : Proper ((≡) ==> (≡)) (own γ) := ne_proper _.

Lemma own_op γ a1 a2 : own γ (a1 ⋅ a2) ≡ (own γ a1 ★ own γ a2)%I.
Proof. rewrite /own -ownG_op. apply ownG_proper, globalC_op. Qed.

(* TODO: This also holds if we just have ✓a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc E a :
  ✓a → True ⊑ pvs E E (∃ γ, own γ a).
Proof.
  intros Ha. set (P m := ∃ γ, m = to_globalC γ a).
  rewrite -(pvs_mono _ _ (∃ m, ■P m ∧ ownG m)%I).
  - rewrite -pvs_ownG_updateP_empty //; [].
    subst P. eapply (iprod_singleton_updateP_empty i).
    + apply map_updateP_alloc' with (x:=to_Σ a).
      by rewrite /to_Σ; destruct inG.
    + simpl. move=>? [γ [-> ?]]. exists γ. done.
  - apply exist_elim=>m. apply const_elim_l=>-[p ->] {P}.
    by rewrite -(exist_intro p).
Qed.

Lemma always_own_unit γ a : (□ own γ (unit a))%I ≡ own γ (unit a).
Proof. rewrite /own -globalC_unit. by apply always_ownG_unit. Qed.

Lemma own_valid γ a : (own γ a) ⊑ (✓ a).
Proof.
  rewrite /own ownG_valid. apply uPred.valid_mono=>n.
  by apply globalC_validN.
Qed.

Lemma own_valid_r' γ a : (own γ a) ⊑ (own γ a ★ ✓ a).
Proof. apply (uPred.always_entails_r' _ _), own_valid. Qed.

Global Instance ownG_timeless γ a : Timeless a → TimelessP (own γ a).
Proof.
  intros. apply ownG_timeless. apply _.
Qed.

Lemma pvs_updateP E γ a P :
  a ~~>: P → own γ a ⊑ pvs E E (∃ a', ■ P a' ∧ own γ a').
Proof.
  intros Ha. set (P' m := ∃ a', P a' ∧ m = to_globalC γ a').
  rewrite -(pvs_mono _ _ (∃ m, ■P' m ∧ ownG m)%I).
  - rewrite -pvs_ownG_updateP; first by rewrite /own.
    rewrite /to_globalC. eapply iprod_singleton_updateP.
    + (* FIXME RJ: I tried apply... with instead of instantiate, that
         does not work. *)
      apply map_singleton_updateP'. instantiate (1:=P_to_Σ P).
      by apply update_to_Σ.
    + simpl. move=>? [y [-> HP]]. exists (from_Σ y). split.
      * move: HP. rewrite /P_to_Σ /from_Σ. by destruct inG.
      * clear HP. rewrite /to_globalC to_from_Σ; done.
  - apply exist_elim=>m. apply const_elim_l=>-[a' [HP ->]].
    rewrite -(exist_intro a'). apply and_intro; last done.
    by apply const_intro.
Qed.

Lemma pvs_update E γ a a' : a ~~> a' → own γ a ⊑ pvs E E (own γ a').
Proof.
  intros; rewrite (pvs_updateP E _ _ (a' =)); last by apply cmra_update_updateP.
  by apply pvs_mono, uPred.exist_elim=> m''; apply uPred.const_elim_l=> ->.
Qed.

End global.
