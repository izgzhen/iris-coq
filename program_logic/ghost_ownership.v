From prelude Require Export functions.
From algebra Require Export iprod.
From program_logic Require Export pviewshifts global_functor.
From program_logic Require Import ownership.
Import uPred.

Definition own `{inG Λ Σ A} (γ : gname) (a : A) : iPropG Λ Σ :=
  ownG (to_globalF γ a).
Instance: Params (@to_globalF) 5.
Instance: Params (@own) 5.
Typeclasses Opaque to_globalF own.

(** Properties about ghost ownership *)
Section global.
Context `{i : inG Λ Σ A}.
Implicit Types a : A.

(** * Transport empty *)
Instance inG_empty `{Empty A} :
  Empty (Σ inG_id (iPreProp Λ (globalF Σ))) := cmra_transport inG_prf ∅.
Instance inG_empty_spec `{Empty A} :
  CMRAUnit A → CMRAUnit (Σ inG_id (iPreProp Λ (globalF Σ))).
Proof.
  split.
  - apply cmra_transport_valid, cmra_unit_valid.
  - intros x; rewrite /empty /inG_empty; destruct inG_prf. by rewrite left_id.
  - apply _.
Qed.

(** * Properties of own *)
Global Instance own_ne γ n : Proper (dist n ==> dist n) (own γ).
Proof. solve_proper. Qed.
Global Instance own_proper γ : Proper ((≡) ==> (≡)) (own γ) := ne_proper _.

Lemma own_op γ a1 a2 : own γ (a1 ⋅ a2) ≡ (own γ a1 ★ own γ a2)%I.
Proof. by rewrite /own -ownG_op to_globalF_op. Qed.
Global Instance own_mono γ : Proper (flip (≼) ==> (⊑)) (own γ).
Proof. move=>a b [c H]. rewrite H own_op. eauto with I. Qed.
Lemma always_own_core γ a : (□ own γ (core a))%I ≡ own γ (core a).
Proof. by rewrite /own -to_globalF_core always_ownG_core. Qed.
Lemma always_own γ a : core a ≡ a → (□ own γ a)%I ≡ own γ a.
Proof. by intros <-; rewrite always_own_core. Qed.
Lemma own_valid γ a : own γ a ⊑ ✓ a.
Proof.
  rewrite /own ownG_valid /to_globalF.
  rewrite iprod_validI (forall_elim inG_id) iprod_lookup_singleton.
  rewrite map_validI (forall_elim γ) lookup_singleton option_validI.
  (* implicit arguments differ a bit *)
  by trans (✓ cmra_transport inG_prf a : iPropG Λ Σ)%I; last destruct inG_prf.
Qed.
Lemma own_valid_r γ a : own γ a ⊑ (own γ a ★ ✓ a).
Proof. apply: uPred.always_entails_r. apply own_valid. Qed.
Lemma own_valid_l γ a : own γ a ⊑ (✓ a ★ own γ a).
Proof. by rewrite comm -own_valid_r. Qed.
Lemma own_empty `{CMRAUnit A} γ : True ⊑ own γ ∅.
Proof.
  rewrite ownG_empty /own. apply equiv_spec, ownG_proper.
  (* FIXME: rewrite to_globalF_empty. *)
Abort.
Global Instance own_timeless γ a : Timeless a → TimelessP (own γ a).
Proof. unfold own; apply _. Qed.
Global Instance own_core_always_stable γ a : AlwaysStable (own γ (core a)).
Proof. by rewrite /AlwaysStable always_own_core. Qed.

(* TODO: This also holds if we just have ✓ a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc_strong a E (G : gset gname) :
  ✓ a → True ⊑ (|={E}=> ∃ γ, ■(γ ∉ G) ∧ own γ a).
Proof.
  intros Ha.
  rewrite -(pvs_mono _ _ (∃ m, ■ (∃ γ, γ ∉ G ∧ m = to_globalF γ a) ∧ ownG m)%I).
  - rewrite ownG_empty. eapply pvs_ownG_updateP, (iprod_singleton_updateP_empty inG_id);
      first (eapply map_updateP_alloc_strong', cmra_transport_valid, Ha);
      naive_solver.
  - apply exist_elim=>m; apply const_elim_l=>-[γ [Hfresh ->]].
    by rewrite -(exist_intro γ) const_equiv // left_id.
Qed.
Lemma own_alloc a E : ✓ a → True ⊑ (|={E}=> ∃ γ, own γ a).
Proof.
  intros Ha. rewrite (own_alloc_strong a E ∅) //; []. apply pvs_mono.
  apply exist_mono=>?. eauto with I.
Qed.

Lemma own_updateP P γ a E :
  a ~~>: P → own γ a ⊑ (|={E}=> ∃ a', ■ P a' ∧ own γ a').
Proof.
  intros Ha.
  rewrite -(pvs_mono _ _ (∃ m, ■ (∃ a', m = to_globalF γ a' ∧ P a') ∧ ownG m)%I).
  - eapply pvs_ownG_updateP, iprod_singleton_updateP;
      first by (eapply map_singleton_updateP', cmra_transport_updateP', Ha).
    naive_solver.
  - apply exist_elim=>m; apply const_elim_l=>-[a' [-> HP]].
    rewrite -(exist_intro a'). by apply and_intro; [apply const_intro|].
Qed.

Lemma own_update γ a a' E : a ~~> a' → own γ a ⊑ (|={E}=> own γ a').
Proof.
  intros; rewrite (own_updateP (a' =)); last by apply cmra_update_updateP.
  by apply pvs_mono, exist_elim=> a''; apply const_elim_l=> ->.
Qed.

Lemma own_empty `{Empty A, !CMRAUnit A} γ E :
  True ⊑ (|={E}=> own γ ∅).
Proof.
  rewrite ownG_empty /own. apply pvs_ownG_update, cmra_update_updateP.
  eapply iprod_singleton_updateP_empty;
      first by eapply map_singleton_updateP_empty', cmra_transport_updateP',
               cmra_update_updateP, cmra_update_unit.
  naive_solver.
Qed.
End global.
