From algebra Require Export iprod.
From program_logic Require Export pviewshifts.
From program_logic Require Import ownership.
Import uPred.

(** Index of a CMRA in the product of global CMRAs. *)
Definition gid := nat.
(** Name of one instance of a particular CMRA in the ghost state. *)
Definition gname := positive.
(** The global CMRA: Indexed product over a gid i to (gname --fin--> Σ i) *)
Definition globalF (Σ : gid → iFunctor) : iFunctor :=
  iprodF (λ i, mapF gname (Σ i)).

Class InG (Λ : language) (Σ : gid → iFunctor) (i : gid) (A : cmraT) :=
  inG : A = Σ i (laterC (iPreProp Λ (globalF Σ))).

Definition to_globalF {Λ Σ A}
    (i : gid) `{!InG Λ Σ i A} (γ : gname) (a : A) : iGst Λ (globalF Σ) :=
  iprod_singleton i {[ γ ↦ cmra_transport inG a ]}.
Definition own {Λ Σ A}
    (i : gid) `{!InG Λ Σ i A} (γ : gname) (a : A) : iProp Λ (globalF Σ) :=
  ownG (to_globalF i γ a).
Instance: Params (@to_globalF) 6.
Instance: Params (@own) 6.
Typeclasses Opaque to_globalF own.

Notation iPropG Λ Σ := (iProp Λ (globalF Σ)).
Notation iFunctorG := (gid → iFunctor).

Section global.
Context {Λ : language} {Σ : iFunctorG} (i : gid) `{!InG Λ Σ i A}.
Implicit Types a : A.

(** * Properties of to_globalC *)
Instance to_globalF_ne γ n : Proper (dist n ==> dist n) (to_globalF i γ).
Proof. by intros a a' Ha; apply iprod_singleton_ne; rewrite Ha. Qed.
Lemma to_globalF_op γ a1 a2 :
  to_globalF i γ (a1 ⋅ a2) ≡ to_globalF i γ a1 ⋅ to_globalF i γ a2.
Proof.
  by rewrite /to_globalF iprod_op_singleton map_op_singleton cmra_transport_op.
Qed.
Lemma to_globalF_unit γ a : unit (to_globalF i γ a) ≡ to_globalF i γ (unit a).
Proof.
  by rewrite /to_globalF
    iprod_unit_singleton map_unit_singleton cmra_transport_unit.
Qed.
Instance to_globalF_timeless γ m : Timeless m → Timeless (to_globalF i γ m).
Proof. rewrite /to_globalF; apply _. Qed.

(** * Transport empty *)
Instance inG_empty `{Empty A} : Empty (Σ i (laterC (iPreProp Λ (globalF Σ)))) :=
  cmra_transport inG ∅.
Instance inG_empty_spec `{Empty A} :
  CMRAIdentity A → CMRAIdentity (Σ i (laterC (iPreProp Λ (globalF Σ)))).
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
Proof. by rewrite /own -ownG_op to_globalF_op. Qed.
Lemma always_own_unit γ a : (□ own i γ (unit a))%I ≡ own i γ (unit a).
Proof. by rewrite /own -to_globalF_unit always_ownG_unit. Qed.
Lemma own_valid γ a : own i γ a ⊑ ✓ a.
Proof.
  rewrite /own ownG_valid /to_globalF.
  rewrite iprod_validI (forall_elim i) iprod_lookup_singleton.
  rewrite map_validI (forall_elim γ) lookup_singleton option_validI.
  by destruct inG.
Qed.
Lemma own_valid_r γ a : own i γ a ⊑ (own i γ a ★ ✓ a).
Proof. apply (uPred.always_entails_r _ _), own_valid. Qed.
Global Instance own_timeless γ a : Timeless a → TimelessP (own i γ a).
Proof. unfold own; apply _. Qed.

(* TODO: This also holds if we just have ✓ a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc_strong a E (G : gset gname) : ✓ a → True ⊑ pvs E E (∃ γ, ■(γ ∉ G) ∧ own i γ a).
Proof.
  intros Ha.
  rewrite -(pvs_mono _ _ (∃ m, ■ (∃ γ, γ ∉ G ∧ m = to_globalF i γ a) ∧ ownG m)%I).
  * eapply pvs_ownG_updateP_empty, (iprod_singleton_updateP_empty i);
      first (eapply map_updateP_alloc_strong', cmra_transport_valid, Ha); naive_solver.
  * apply exist_elim=>m; apply const_elim_l=>-[γ [Hfresh ->]].
    by rewrite -(exist_intro γ) const_equiv.
Qed.
Lemma own_alloc a E : ✓ a → True ⊑ pvs E E (∃ γ, own i γ a).
Proof.
  intros Ha. rewrite (own_alloc_strong a E ∅) //; []. apply pvs_mono.
  apply exist_mono=>?. eauto with I.
Qed.

Lemma own_updateP P γ a E :
  a ~~>: P → own i γ a ⊑ pvs E E (∃ a', ■ P a' ∧ own i γ a').
Proof.
  intros Ha.
  rewrite -(pvs_mono _ _ (∃ m, ■ (∃ a', m = to_globalF i γ a' ∧ P a') ∧ ownG m)%I).
  * eapply pvs_ownG_updateP, iprod_singleton_updateP;
      first by (eapply map_singleton_updateP', cmra_transport_updateP', Ha).
    naive_solver.
  * apply exist_elim=>m; apply const_elim_l=>-[a' [-> HP]].
    rewrite -(exist_intro a'). by apply and_intro; [apply const_intro|].
Qed.

Lemma own_updateP_empty `{Empty A, !CMRAIdentity A} P γ E :
  ∅ ~~>: P → True ⊑ pvs E E (∃ a, ■ P a ∧ own i γ a).
Proof.
  intros Hemp.
  rewrite -(pvs_mono _ _ (∃ m, ■ (∃ a', m = to_globalF i γ a' ∧ P a') ∧ ownG m)%I).
  * eapply pvs_ownG_updateP_empty, iprod_singleton_updateP_empty;
      first eapply map_singleton_updateP_empty', cmra_transport_updateP', Hemp.
    naive_solver.
  * apply exist_elim=>m; apply const_elim_l=>-[a' [-> HP]].
    rewrite -(exist_intro a'). by apply and_intro; [apply const_intro|].
Qed.

Lemma own_update γ a a' E : a ~~> a' → own i γ a ⊑ pvs E E (own i γ a').
Proof.
  intros; rewrite (own_updateP (a' =)); last by apply cmra_update_updateP.
  by apply pvs_mono, exist_elim=> a''; apply const_elim_l=> ->.
Qed.

Lemma own_update_empty `{Empty A, !CMRAIdentity A} γ E :
  True ⊑ pvs E E (own i γ ∅).
Proof.
  rewrite (own_updateP_empty (∅ =)); last by apply cmra_updateP_id.
  apply pvs_mono, exist_elim=>a. by apply const_elim_l=>->.
Qed.
End global.
