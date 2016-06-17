From iris.prelude Require Export functions.
From iris.algebra Require Export iprod.
From iris.program_logic Require Export pviewshifts global_functor.
From iris.program_logic Require Import ownership.
Import uPred.

Definition own `{inG Λ Σ A} (γ : gname) (a : A) : iPropG Λ Σ :=
  ownG (to_globalF γ a).
Instance: Params (@own) 5.
Typeclasses Opaque own.

(** Properties about ghost ownership *)
Section global.
Context `{i : inG Λ Σ A}.
Implicit Types a : A.

(** * Properties of own *)
Global Instance own_ne γ n : Proper (dist n ==> dist n) (own γ).
Proof. solve_proper. Qed.
Global Instance own_proper γ : Proper ((≡) ==> (⊣⊢)) (own γ) := ne_proper _.

Lemma own_op γ a1 a2 : own γ (a1 ⋅ a2) ⊣⊢ own γ a1 ★ own γ a2.
Proof. by rewrite /own -ownG_op to_globalF_op. Qed.
Global Instance own_mono γ : Proper (flip (≼) ==> (⊢)) (own γ).
Proof. move=>a b [c ->]. rewrite own_op. eauto with I. Qed.
Lemma own_valid γ a : own γ a ⊢ ✓ a.
Proof.
  rewrite /own ownG_valid /to_globalF.
  rewrite iprod_validI (forall_elim (inG_id i)) iprod_lookup_singleton.
  rewrite gmap_validI (forall_elim γ) lookup_singleton option_validI.
  (* implicit arguments differ a bit *)
  by trans (✓ cmra_transport inG_prf a : iPropG Λ Σ)%I; last destruct inG_prf.
Qed.
Lemma own_valid_r γ a : own γ a ⊢ own γ a ★ ✓ a.
Proof. apply: uPred.always_entails_r. apply own_valid. Qed.
Lemma own_valid_l γ a : own γ a ⊢ ✓ a ★ own γ a.
Proof. by rewrite comm -own_valid_r. Qed.
Global Instance own_timeless γ a : Timeless a → TimelessP (own γ a).
Proof. rewrite /own; apply _. Qed.
Global Instance own_core_persistent γ a : Persistent a → PersistentP (own γ a).
Proof. rewrite /own; apply _. Qed.

(* TODO: This also holds if we just have ✓ a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc_strong a E (G : gset gname) :
  ✓ a → True ={E}=> ∃ γ, ■(γ ∉ G) ∧ own γ a.
Proof.
  intros Ha.
  rewrite -(pvs_mono _ _ (∃ m, ■ (∃ γ, γ ∉ G ∧ m = to_globalF γ a) ∧ ownG m)%I).
  - rewrite ownG_empty.
    eapply pvs_ownG_updateP, (iprod_singleton_updateP_empty (inG_id i));
      first (eapply alloc_updateP_strong', cmra_transport_valid, Ha);
      naive_solver.
  - apply exist_elim=>m; apply const_elim_l=>-[γ [Hfresh ->]].
    by rewrite -(exist_intro γ) const_equiv // left_id.
Qed.
Lemma own_alloc a E : ✓ a → True ={E}=> ∃ γ, own γ a.
Proof.
  intros Ha. rewrite (own_alloc_strong a E ∅) //; [].
  apply pvs_mono, exist_mono=>?. eauto with I.
Qed.

Lemma own_updateP P γ a E :
  a ~~>: P → own γ a ={E}=> ∃ a', ■ P a' ∧ own γ a'.
Proof.
  intros Ha.
  rewrite -(pvs_mono _ _ (∃ m, ■ (∃ a', m = to_globalF γ a' ∧ P a') ∧ ownG m)%I).
  - eapply pvs_ownG_updateP, iprod_singleton_updateP;
      first by (eapply singleton_updateP', cmra_transport_updateP', Ha).
    naive_solver.
  - apply exist_elim=>m; apply const_elim_l=>-[a' [-> HP]].
    rewrite -(exist_intro a'). by apply and_intro; [apply const_intro|].
Qed.

Lemma own_update γ a a' E : a ~~> a' → own γ a ={E}=> own γ a'.
Proof.
  intros; rewrite (own_updateP (a' =)); last by apply cmra_update_updateP.
  by apply pvs_mono, exist_elim=> a''; apply const_elim_l=> ->.
Qed.
End global.

Section global_empty.
Context `{i : inG Λ Σ (A:ucmraT)}.
Implicit Types a : A.

Lemma own_empty γ E : True ={E}=> own γ ∅.
Proof.
  rewrite ownG_empty /own. apply pvs_ownG_update, iprod_singleton_update_empty.
  apply (singleton_update_unit (cmra_transport inG_prf ∅)); last done.
  - apply cmra_transport_valid, ucmra_unit_valid.
  - intros x; destruct inG_prf. by rewrite left_id.
Qed.
End global_empty.
