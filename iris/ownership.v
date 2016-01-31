Require Export iris.model.

Definition inv {Σ} (i : positive) (P : iProp Σ) : iProp Σ :=
  uPred_own (Res {[ i ↦ to_agree (Later (iProp_unfold P)) ]} ∅ ∅).
Arguments inv {_} _ _%I.
Definition ownP {Σ} (σ : istate Σ) : iProp Σ := uPred_own (Res ∅ (Excl σ) ∅).
Definition ownG {Σ} (m : iGst Σ) : iProp Σ := uPred_own (Res ∅ ∅ m).
Instance: Params (@inv) 2.
Instance: Params (@ownP) 1.
Instance: Params (@ownG) 1.

Typeclasses Opaque inv ownG ownP.

Section ownership.
Context {Σ : iParam}.
Implicit Types r : iRes Σ.
Implicit Types σ : istate Σ.
Implicit Types P : iProp Σ.
Implicit Types m : iGst Σ.

(* Invariants *)
Global Instance inv_contractive i : Contractive (@inv Σ i).
Proof.
  intros n P Q HPQ.
  apply (_: Proper (_ ==> _) iProp_unfold), Later_contractive in HPQ.
  by unfold inv; rewrite HPQ.
Qed.
Lemma always_inv i P : (□ inv i P)%I ≡ inv i P.
Proof.
  by apply uPred.always_own; rewrite Res_unit !ra_unit_empty map_unit_singleton.
Qed.
Global Instance inv_always_stable i P : AlwaysStable (inv i P).
Proof. by rewrite /AlwaysStable always_inv. Qed.
Lemma inv_sep_dup i P : inv i P ≡ (inv i P ★ inv i P)%I.
Proof. apply (uPred.always_sep_dup' _). Qed.

(* physical state *)
Lemma ownP_twice σ1 σ2 : (ownP σ1 ★ ownP σ2 : iProp Σ) ⊑ False.
Proof.
  rewrite /ownP -uPred.own_op Res_op.
  by apply uPred.own_invalid; intros (_&?&_).
Qed.
Global Instance ownP_timeless σ : TimelessP (ownP σ).
Proof. rewrite /ownP; apply _. Qed.

(* ghost state *)
Global Instance ownG_ne n : Proper (dist n ==> dist n) (@ownG Σ).
Proof. by intros m m' Hm; unfold ownG; rewrite Hm. Qed.
Global Instance ownG_proper : Proper ((≡) ==> (≡)) (@ownG Σ) := ne_proper _.
Lemma ownG_op m1 m2 : ownG (m1 ⋅ m2) ≡ (ownG m1 ★ ownG m2)%I.
Proof. by rewrite /ownG -uPred.own_op Res_op !(left_id _ _). Qed.
Lemma always_ownG_unit m : (□ ownG (unit m))%I ≡ ownG (unit m).
Proof.
  by apply uPred.always_own; rewrite Res_unit !ra_unit_empty ra_unit_idempotent.
Qed.
Lemma ownG_valid m : (ownG m) ⊑ (✓ m).
Proof. by rewrite /ownG uPred.own_valid; apply uPred.valid_mono=> n [? []]. Qed.
Lemma ownG_valid_r m : (ownG m) ⊑ (ownG m ★ ✓ m).
Proof. apply (uPred.always_entails_r' _ _), ownG_valid. Qed.
Global Instance ownG_timeless m : Timeless m → TimelessP (ownG m).
Proof. rewrite /ownG; apply _. Qed.

(* inversion lemmas *)
Lemma inv_spec r n i P :
  ✓{n} r →
  (inv i P) n r ↔ wld r !! i ={n}= Some (to_agree (Later (iProp_unfold P))).
Proof.
  intros [??]; rewrite /uPred_holds/=res_includedN/=singleton_includedN; split.
  * intros [(P'&Hi&HP) _]; rewrite Hi.
    by apply Some_dist, symmetry, agree_valid_includedN,
      (cmra_included_includedN _ P'),HP; apply map_lookup_validN with (wld r) i.
  * intros ?; split_ands; try apply cmra_empty_least; eauto.
Qed.
Lemma ownP_spec r n σ : ✓{n} r → (ownP σ) n r ↔ pst r ={n}= Excl σ.
Proof.
  intros (?&?&?); rewrite /uPred_holds /= res_includedN /= Excl_includedN //.
  naive_solver (apply cmra_empty_least).
Qed.
Lemma ownG_spec r n m : (ownG m) n r ↔ m ≼{n} gst r.
Proof.
  rewrite /uPred_holds /= res_includedN; naive_solver (apply cmra_empty_least).
Qed.
End ownership.
