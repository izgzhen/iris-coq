From program_logic Require Export model.

Definition ownI {Λ Σ} (i : positive) (P : iProp Λ Σ) : iProp Λ Σ :=
  uPred_ownM (Res {[ i := to_agree (Next (iProp_unfold P)) ]} ∅ ∅).
Arguments ownI {_ _} _ _%I.
Definition ownP {Λ Σ} (σ: state Λ) : iProp Λ Σ := uPred_ownM (Res ∅ (Excl σ) ∅).
Definition ownG {Λ Σ} (m: iGst Λ Σ) : iProp Λ Σ := uPred_ownM (Res ∅ ∅ m).
Instance: Params (@ownI) 3.
Instance: Params (@ownP) 2.
Instance: Params (@ownG) 2.

Typeclasses Opaque ownI ownG ownP.

Section ownership.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types r : iRes Λ Σ.
Implicit Types σ : state Λ.
Implicit Types P : iProp Λ Σ.
Implicit Types m : iGst Λ Σ.

(* Invariants *)
Global Instance ownI_contractive i : Contractive (@ownI Λ Σ i).
Proof.
  intros n P Q HPQ. rewrite /ownI.
  apply uPred.ownM_ne, Res_ne; auto; apply singleton_ne, to_agree_ne.
  by apply Next_contractive=> j ?; rewrite (HPQ j).
Qed.
Lemma always_ownI i P : (□ ownI i P)%I ≡ ownI i P.
Proof.
  apply uPred.always_ownM.
  by rewrite Res_core !cmra_core_unit map_core_singleton.
Qed.
Global Instance ownI_always_stable i P : AlwaysStable (ownI i P).
Proof. by rewrite /AlwaysStable always_ownI. Qed.
Lemma ownI_sep_dup i P : ownI i P ≡ (ownI i P ★ ownI i P)%I.
Proof. apply (uPred.always_sep_dup _). Qed.

(* physical state *)
Lemma ownP_twice σ1 σ2 : (ownP σ1 ★ ownP σ2 : iProp Λ Σ) ⊑ False.
Proof.
  rewrite /ownP -uPred.ownM_op Res_op.
  by apply uPred.ownM_invalid; intros (_&?&_).
Qed.
Global Instance ownP_timeless σ : TimelessP (@ownP Λ Σ σ).
Proof. rewrite /ownP; apply _. Qed.

(* ghost state *)
Global Instance ownG_ne n : Proper (dist n ==> dist n) (@ownG Λ Σ).
Proof. solve_proper. Qed.
Global Instance ownG_proper : Proper ((≡) ==> (≡)) (@ownG Λ Σ) := ne_proper _.
Lemma ownG_op m1 m2 : ownG (m1 ⋅ m2) ≡ (ownG m1 ★ ownG m2)%I.
Proof. by rewrite /ownG -uPred.ownM_op Res_op !left_id. Qed.
Global Instance ownG_mono : Proper (flip (≼) ==> (⊑)) (@ownG Λ Σ).
Proof. move=>a b [c H]. rewrite H ownG_op. eauto with I. Qed.
Lemma always_ownG_core m : (□ ownG (core m))%I ≡ ownG (core m).
Proof.
  apply uPred.always_ownM.
  by rewrite Res_core !cmra_core_unit -{2}(cmra_core_idemp m).
Qed.
Lemma always_ownG m : core m ≡ m → (□ ownG m)%I ≡ ownG m.
Proof. by intros <-; rewrite always_ownG_core. Qed.
Lemma ownG_valid m : ownG m ⊑ ✓ m.
Proof.
  rewrite /ownG uPred.ownM_valid res_validI /=; auto with I.
Qed.
Lemma ownG_valid_r m : ownG m ⊑ (ownG m ★ ✓ m).
Proof. apply (uPred.always_entails_r _ _), ownG_valid. Qed.
Lemma ownG_empty : True ⊑ (ownG ∅ : iProp Λ Σ).
Proof. apply uPred.ownM_empty. Qed.
Global Instance ownG_timeless m : Timeless m → TimelessP (ownG m).
Proof. rewrite /ownG; apply _. Qed.
Global Instance ownG_core_always_stable m : AlwaysStable (ownG (core m)).
Proof. by rewrite /AlwaysStable always_ownG_core. Qed.

(* inversion lemmas *)
Lemma ownI_spec n r i P :
  ✓{n} r →
  (ownI i P) n r ↔ wld r !! i ≡{n}≡ Some (to_agree (Next (iProp_unfold P))).
Proof.
  intros (?&?&?). rewrite /ownI; uPred.unseal.
  rewrite /uPred_holds/=res_includedN/=singleton_includedN; split.
  - intros [(P'&Hi&HP) _]; rewrite Hi.
    by apply Some_dist, symmetry, agree_valid_includedN,
      (cmra_included_includedN _ P'),HP; apply map_lookup_validN with (wld r) i.
  - intros ?; split_and?; try apply cmra_unit_leastN; eauto.
Qed.
Lemma ownP_spec n r σ : ✓{n} r → (ownP σ) n r ↔ pst r ≡ Excl σ.
Proof.
  intros (?&?&?). rewrite /ownP; uPred.unseal.
  rewrite /uPred_holds /= res_includedN /= Excl_includedN //.
  rewrite (timeless_iff n). naive_solver (apply cmra_unit_leastN).
Qed.
Lemma ownG_spec n r m : (ownG m) n r ↔ m ≼{n} gst r.
Proof.
  rewrite /ownG; uPred.unseal.
  rewrite /uPred_holds /= res_includedN; naive_solver (apply cmra_unit_leastN).
Qed.
End ownership.
