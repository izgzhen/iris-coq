From iris.program_logic Require Export model.

Definition ownI {Λ Σ} (i : positive) (P : iProp Λ Σ) : iProp Λ Σ :=
  uPred_ownM (Res {[ i := to_agree (Next (iProp_unfold P)) ]} ∅ ∅).
Arguments ownI {_ _} _ _%I.
Definition ownP {Λ Σ} (σ: state Λ) : iProp Λ Σ := uPred_ownM (Res ∅ (Excl' σ) ∅).
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
Global Instance ownI_persistent i P : PersistentP (ownI i P).
Proof. rewrite /ownI. apply _. Qed.

(* physical state *)
Lemma ownP_twice σ1 σ2 : (ownP σ1 ★ ownP σ2 : iProp Λ Σ) ⊢ False.
Proof.
  rewrite /ownP -uPred.ownM_op Res_op.
  by apply uPred.ownM_invalid; intros (_&?&_).
Qed.
Global Instance ownP_timeless σ : TimelessP (@ownP Λ Σ σ).
Proof. rewrite /ownP; apply _. Qed.

(* ghost state *)
Global Instance ownG_ne n : Proper (dist n ==> dist n) (@ownG Λ Σ).
Proof. solve_proper. Qed.
Global Instance ownG_proper : Proper ((≡) ==> (⊣⊢)) (@ownG Λ Σ) := ne_proper _.
Lemma ownG_op m1 m2 : ownG (m1 ⋅ m2) ⊣⊢ (ownG m1 ★ ownG m2).
Proof. by rewrite /ownG -uPred.ownM_op Res_op !left_id. Qed.
Global Instance ownG_mono : Proper (flip (≼) ==> (⊢)) (@ownG Λ Σ).
Proof. move=>a b [c H]. rewrite H ownG_op. eauto with I. Qed.
Lemma ownG_valid m : ownG m ⊢ ✓ m.
Proof. rewrite /ownG uPred.ownM_valid res_validI /=; auto with I. Qed.
Lemma ownG_valid_r m : ownG m ⊢ (ownG m ★ ✓ m).
Proof. apply (uPred.always_entails_r _ _), ownG_valid. Qed.
Lemma ownG_empty : True ⊢ (ownG ∅ : iProp Λ Σ).
Proof. apply: uPred.ownM_empty. Qed.
Global Instance ownG_timeless m : Timeless m → TimelessP (ownG m).
Proof. rewrite /ownG; apply _. Qed.
Global Instance ownG_persistent m : Persistent m → PersistentP (ownG m).
Proof. rewrite /ownG; apply _. Qed.

(* inversion lemmas *)
Lemma ownI_spec n r i P :
  ✓{n} r →
  (ownI i P) n r ↔ wld r !! i ≡{n}≡ Some (to_agree (Next (iProp_unfold P))).
Proof.
  intros (?&?&?). rewrite /ownI; uPred.unseal.
  rewrite /uPred_holds/=res_includedN/= singleton_includedN; split.
  - intros [(P'&Hi&HP) _]; rewrite Hi.
    constructor; symmetry; apply agree_valid_includedN.
    + by apply lookup_validN_Some with (wld r) i.
    + by destruct HP as [?| ->].
  - intros ?; split_and?; try apply ucmra_unit_leastN; eauto.
Qed.
Lemma ownP_spec n r σ : ✓{n} r → (ownP σ) n r ↔ pst r ≡ Excl' σ.
Proof.
  intros (?&?&?). rewrite /ownP; uPred.unseal.
  rewrite /uPred_holds /= res_includedN /= Excl_includedN //.
  rewrite (timeless_iff n). naive_solver (apply ucmra_unit_leastN).
Qed.
Lemma ownG_spec n r m : (ownG m) n r ↔ m ≼{n} gst r.
Proof.
  rewrite /ownG; uPred.unseal.
  rewrite /uPred_holds /= res_includedN; naive_solver (apply ucmra_unit_leastN).
Qed.
End ownership.
