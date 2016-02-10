Require Export algebra.iprod program_logic.pviewshifts.
Require Import program_logic.ownership.
Import uPred.

Definition gid := positive.
Definition globalC (Σ : gid → iFunctor) : iFunctor :=
  iprodF (λ i, mapF gid (Σ i)).

Class InG (Λ : language) (Σ : gid → iFunctor) (i : gid) (A : cmraT) :=
  inG : A = Σ i (laterC (iPreProp Λ (globalC Σ))).

Definition to_globalC {Λ Σ A}
    (i : gid) `{!InG Λ Σ i A} (γ : gid) (a : A) : iGst Λ (globalC Σ) :=
  iprod_singleton i {[ γ ↦ cmra_transport inG a ]}.
Definition own {Λ Σ A}
    (i : gid) `{!InG Λ Σ i A} (γ : gid) (a : A) : iProp Λ (globalC Σ) :=
  ownG (to_globalC i γ a).
Instance: Params (@to_globalC) 6.
Instance: Params (@own) 6.
Typeclasses Opaque to_globalC own.

Section global.
Context {Λ : language} {Σ : gid → iFunctor} (i : gid) `{!InG Λ Σ i A}.
Implicit Types a : A.

(** * Properties of to_globalC *)
Instance to_globalC_ne γ n : Proper (dist n ==> dist n) (to_globalC i γ).
Proof. by intros a a' Ha; apply iprod_singleton_ne; rewrite Ha. Qed.
Lemma to_globalC_validN n γ a : ✓{n} (to_globalC i γ a) ↔ ✓{n} a.
Proof.
  by rewrite /to_globalC
    iprod_singleton_validN map_singleton_validN cmra_transport_validN.
Qed.
Lemma to_globalC_op γ a1 a2 :
  to_globalC i γ (a1 ⋅ a2) ≡ to_globalC i γ a1 ⋅ to_globalC i γ a2.
Proof.
  by rewrite /to_globalC iprod_op_singleton map_op_singleton cmra_transport_op.
Qed.
Lemma to_globalC_unit γ a : unit (to_globalC i γ a) ≡ to_globalC i γ (unit a).
Proof.
  by rewrite /to_globalC
    iprod_unit_singleton map_unit_singleton cmra_transport_unit.
Qed.
Instance to_globalC_timeless γ m : Timeless m → Timeless (to_globalC i γ m).
Proof. rewrite /to_globalC; apply _. Qed.

(** * Transport empty *)
Instance inG_empty `{Empty A} : Empty (Σ i (laterC (iPreProp Λ (globalC Σ)))) :=
  cmra_transport inG ∅.
Instance inG_empty_spec `{Empty A} :
  CMRAIdentity A → CMRAIdentity (Σ i (laterC (iPreProp Λ (globalC Σ)))).
Proof.
  split.
  * apply cmra_transport_valid, cmra_empty_valid.
  * intros x; rewrite /empty /inG_empty; destruct inG. by rewrite left_id.
  * apply _.
Qed.

(** * Properties of own *)
Global Instance own_ne γ n : Proper (dist n ==> dist n) (own i γ).
Proof. by intros m m' Hm; rewrite /own Hm. Qed.
Global Instance own_proper γ : Proper ((≡) ==> (≡)) (own i γ) := ne_proper _.

Lemma own_op γ a1 a2 : own i γ (a1 ⋅ a2) ≡ (own i γ a1 ★ own i γ a2)%I.
Proof. by rewrite /own -ownG_op to_globalC_op. Qed.
Lemma always_own_unit γ a : (□ own i γ (unit a))%I ≡ own i γ (unit a).
Proof. by rewrite /own -to_globalC_unit always_ownG_unit. Qed.
Lemma own_valid γ a : own i γ a ⊑ ✓ a.
Proof.
  rewrite /own ownG_valid; apply valid_mono=> ?; apply to_globalC_validN.
Qed.
Lemma own_valid_r' γ a : own i γ a ⊑ (own i γ a ★ ✓ a).
Proof. apply (uPred.always_entails_r' _ _), own_valid. Qed.
Global Instance own_timeless γ a : Timeless a → TimelessP (own i γ a).
Proof. unfold own; apply _. Qed.

(* TODO: This also holds if we just have ✓ a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc E a : ✓ a → True ⊑ pvs E E (∃ γ, own i γ a).
Proof.
  intros Ha.
  rewrite -(pvs_mono _ _ (∃ m, ■ (∃ γ, m = to_globalC i γ a) ∧ ownG m)%I).
  * eapply pvs_ownG_updateP_empty, (iprod_singleton_updateP_empty i);
      first (eapply map_updateP_alloc', cmra_transport_valid, Ha); naive_solver.
  * apply exist_elim=>m; apply const_elim_l=>-[γ ->].
    by rewrite -(exist_intro γ).
Qed.

Lemma own_updateP E γ a P :
  a ~~>: P → own i γ a ⊑ pvs E E (∃ a', ■ P a' ∧ own i γ a').
Proof.
  intros Ha.
  rewrite -(pvs_mono _ _ (∃ m, ■ (∃ a', m = to_globalC i γ a' ∧ P a') ∧ ownG m)%I).
  * eapply pvs_ownG_updateP, iprod_singleton_updateP;
      first by (eapply map_singleton_updateP', cmra_transport_updateP', Ha).
    naive_solver.
  * apply exist_elim=>m; apply const_elim_l=>-[a' [-> HP]].
    rewrite -(exist_intro a'). by apply and_intro; [apply const_intro|].
Qed.

Lemma own_updateP_empty `{Empty A, !CMRAIdentity A} E γ a P :
  ∅ ~~>: P → True ⊑ pvs E E (∃ a, ■ P a ∧ own i γ a).
Proof.
  intros Hemp.
  rewrite -(pvs_mono _ _ (∃ m, ■ (∃ a', m = to_globalC i γ a' ∧ P a') ∧ ownG m)%I).
  * eapply pvs_ownG_updateP_empty, iprod_singleton_updateP_empty;
      first eapply map_singleton_updateP_empty', cmra_transport_updateP', Hemp.
    naive_solver.
  * apply exist_elim=>m; apply const_elim_l=>-[a' [-> HP]].
    rewrite -(exist_intro a'). by apply and_intro; [apply const_intro|].
Qed.

Lemma own_update E γ a a' : a ~~> a' → own i γ a ⊑ pvs E E (own i γ a').
Proof.
  intros; rewrite (own_updateP E _ _ (a' =)); last by apply cmra_update_updateP.
  by apply pvs_mono, uPred.exist_elim=> m''; apply uPred.const_elim_l=> ->.
Qed.
End global.
