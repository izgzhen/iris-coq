From algebra Require Export fin_maps agree excl.
From algebra Require Import upred.
From program_logic Require Export language.

Record res (Λ : language) (A : cofeT) (M : cmraT) := Res {
  wld : mapR positive (agreeR A);
  pst : exclR (stateC Λ);
  gst : M;
}.
Add Printing Constructor res.
Arguments Res {_ _ _} _ _ _.
Arguments wld {_ _ _} _.
Arguments pst {_ _ _} _.
Arguments gst {_ _ _} _.
Instance: Params (@Res) 3.
Instance: Params (@wld) 3.
Instance: Params (@pst) 3.
Instance: Params (@gst) 3.

Section res.
Context {Λ : language} {A : cofeT} {M : cmraT}.
Implicit Types r : res Λ A M.

Inductive res_equiv' (r1 r2 : res Λ A M) := Res_equiv :
  wld r1 ≡ wld r2 → pst r1 ≡ pst r2 → gst r1 ≡ gst r2 → res_equiv' r1 r2.
Instance res_equiv : Equiv (res Λ A M) := res_equiv'.
Inductive res_dist' (n : nat) (r1 r2 : res Λ A M) := Res_dist :
  wld r1 ≡{n}≡ wld r2 → pst r1 ≡{n}≡ pst r2 → gst r1 ≡{n}≡ gst r2 →
  res_dist' n r1 r2.
Instance res_dist : Dist (res Λ A M) := res_dist'.
Global Instance Res_ne n :
  Proper (dist n ==> dist n ==> dist n ==> dist n) (@Res Λ A M).
Proof. done. Qed.
Global Instance Res_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (@Res Λ A M).
Proof. done. Qed.
Global Instance wld_ne n : Proper (dist n ==> dist n) (@wld Λ A M).
Proof. by destruct 1. Qed.
Global Instance wld_proper : Proper ((≡) ==> (≡)) (@wld Λ A M).
Proof. by destruct 1. Qed.
Global Instance pst_ne n : Proper (dist n ==> dist n) (@pst Λ A M).
Proof. by destruct 1. Qed.
Global Instance pst_ne' n : Proper (dist n ==> (≡)) (@pst Λ A M).
Proof. destruct 1; apply: timeless; apply dist_le with n; auto with lia. Qed.
Global Instance pst_proper : Proper ((≡) ==> (=)) (@pst Λ A M).
Proof. by destruct 1; unfold_leibniz. Qed.
Global Instance gst_ne n : Proper (dist n ==> dist n) (@gst Λ A M).
Proof. by destruct 1. Qed.
Global Instance gst_proper : Proper ((≡) ==> (≡)) (@gst Λ A M).
Proof. by destruct 1. Qed.
Instance res_compl : Compl (res Λ A M) := λ c,
  Res (compl (chain_map wld c))
      (compl (chain_map pst c)) (compl (chain_map gst c)).
Definition res_cofe_mixin : CofeMixin (res Λ A M).
Proof.
  split.
  - intros w1 w2; split.
    + by destruct 1; constructor; apply equiv_dist.
    + by intros Hw; constructor; apply equiv_dist=>n; destruct (Hw n).
  - intros n; split.
    + done.
    + by destruct 1; constructor.
    + do 2 destruct 1; constructor; etrans; eauto.
  - by destruct 1; constructor; apply dist_S.
  - intros n c; constructor.
    + apply (conv_compl n (chain_map wld c)).
    + apply (conv_compl n (chain_map pst c)).
    + apply (conv_compl n (chain_map gst c)).
Qed.
Canonical Structure resC : cofeT := CofeT res_cofe_mixin.
Global Instance res_timeless r :
  Timeless (wld r) → Timeless (gst r) → Timeless r.
Proof. by destruct 3; constructor; try apply: timeless. Qed.

Instance res_op : Op (res Λ A M) := λ r1 r2,
  Res (wld r1 ⋅ wld r2) (pst r1 ⋅ pst r2) (gst r1 ⋅ gst r2).
Global Instance res_empty `{Empty M} : Empty (res Λ A M) := Res ∅ ∅ ∅.
Instance res_core : Core (res Λ A M) := λ r,
  Res (core (wld r)) (core (pst r)) (core (gst r)).
Instance res_valid : Valid (res Λ A M) := λ r, ✓ wld r ∧ ✓ pst r ∧ ✓ gst r.
Instance res_validN : ValidN (res Λ A M) := λ n r,
  ✓{n} wld r ∧ ✓{n} pst r ∧ ✓{n} gst r.
Instance res_minus : Div (res Λ A M) := λ r1 r2,
  Res (wld r1 ÷ wld r2) (pst r1 ÷ pst r2) (gst r1 ÷ gst r2).

Lemma res_included (r1 r2 : res Λ A M) :
  r1 ≼ r2 ↔ wld r1 ≼ wld r2 ∧ pst r1 ≼ pst r2 ∧ gst r1 ≼ gst r2.
Proof.
  split; [|by intros ([w ?]&[σ ?]&[m ?]); exists (Res w σ m)].
  intros [r Hr]; split_and?;
    [exists (wld r)|exists (pst r)|exists (gst r)]; apply Hr.
Qed.
Lemma res_includedN (r1 r2 : res Λ A M) n :
  r1 ≼{n} r2 ↔ wld r1 ≼{n} wld r2 ∧ pst r1 ≼{n} pst r2 ∧ gst r1 ≼{n} gst r2.
Proof.
  split; [|by intros ([w ?]&[σ ?]&[m ?]); exists (Res w σ m)].
  intros [r Hr]; split_and?;
    [exists (wld r)|exists (pst r)|exists (gst r)]; apply Hr.
Qed.
Definition res_cmra_mixin : CMRAMixin (res Λ A M).
Proof.
  split.
  - by intros n x [???] ? [???]; constructor; cofe_subst.
  - by intros n [???] ? [???]; constructor; cofe_subst.
  - by intros n [???] ? [???] (?&?&?); split_and!; cofe_subst.
  - by intros n [???] ? [???] [???] ? [???]; constructor; cofe_subst.
  - intros r; split.
    + intros (?&?&?) n; split_and!; by apply cmra_valid_validN.
    + intros Hr; split_and!; apply cmra_valid_validN=> n; apply Hr.
  - by intros n ? (?&?&?); split_and!; apply cmra_validN_S.
  - by intros ???; constructor; rewrite /= assoc.
  - by intros ??; constructor; rewrite /= comm.
  - by intros ?; constructor; rewrite /= cmra_core_l.
  - by intros ?; constructor; rewrite /= cmra_core_idemp.
  - intros r1 r2; rewrite !res_included.
    by intros (?&?&?); split_and!; apply cmra_core_preserving.
  - intros n r1 r2 (?&?&?);
      split_and!; simpl in *; eapply cmra_validN_op_l; eauto.
  - intros r1 r2; rewrite res_included; intros (?&?&?).
    by constructor; apply cmra_op_div.
  - intros n r r1 r2 (?&?&?) [???]; simpl in *.
    destruct (cmra_extend n (wld r) (wld r1) (wld r2)) as ([w w']&?&?&?),
      (cmra_extend n (pst r) (pst r1) (pst r2)) as ([σ σ']&?&?&?),
      (cmra_extend n (gst r) (gst r1) (gst r2)) as ([m m']&?&?&?); auto.
    by exists (Res w σ m, Res w' σ' m').
Qed.
Canonical Structure resR : cmraT := CMRAT res_cofe_mixin res_cmra_mixin.
Global Instance res_cmra_unit `{CMRAUnit M} : CMRAUnit resR.
Proof.
  split.
  - split_and!; apply cmra_unit_valid.
  - by split; rewrite /= left_id.
  - apply _.
Qed.

Definition update_pst (σ : state Λ) (r : res Λ A M) : res Λ A M :=
  Res (wld r) (Excl σ) (gst r).
Definition update_gst (m : M) (r : res Λ A M) : res Λ A M :=
  Res (wld r) (pst r) m.

Lemma wld_validN n r : ✓{n} r → ✓{n} wld r.
Proof. by intros (?&?&?). Qed.
Lemma gst_validN n r : ✓{n} r → ✓{n} gst r.
Proof. by intros (?&?&?). Qed.
Lemma Res_op w1 w2 σ1 σ2 m1 m2 :
  Res w1 σ1 m1 ⋅ Res w2 σ2 m2 = Res (w1 ⋅ w2) (σ1 ⋅ σ2) (m1 ⋅ m2).
Proof. done. Qed.
Lemma Res_core w σ m : core (Res w σ m) = Res (core w) (core σ) (core m).
Proof. done. Qed.
Lemma lookup_wld_op_l n r1 r2 i P :
  ✓{n} (r1⋅r2) → wld r1 !! i ≡{n}≡ Some P → (wld r1 ⋅ wld r2) !! i ≡{n}≡ Some P.
Proof.
  move=>/wld_validN /(_ i) Hval Hi1P; move: Hi1P Hval; rewrite lookup_op.
  destruct (wld r2 !! i) as [P'|] eqn:Hi; rewrite !Hi ?right_id // =>-> ?.
  by constructor; rewrite (agree_op_inv _ P P') // agree_idemp.
Qed.
Lemma lookup_wld_op_r n r1 r2 i P :
  ✓{n} (r1⋅r2) → wld r2 !! i ≡{n}≡ Some P → (wld r1 ⋅ wld r2) !! i ≡{n}≡ Some P.
Proof. rewrite (comm _ r1) (comm _ (wld r1)); apply lookup_wld_op_l. Qed.
Global Instance Res_timeless eσ m : Timeless m → Timeless (@Res Λ A M ∅ eσ m).
Proof. by intros ? ? [???]; constructor; apply: timeless. Qed.

(** Internalized properties *)
Lemma res_equivI {M'} r1 r2 :
  (r1 ≡ r2)%I
  ≡ (wld r1 ≡ wld r2 ∧ pst r1 ≡ pst r2 ∧ gst r1 ≡ gst r2: uPred M')%I.
Proof.
  uPred.unseal. do 2 split. by destruct 1. by intros (?&?&?); by constructor.
Qed.
Lemma res_validI {M'} r : (✓ r)%I ≡ (✓ wld r ∧ ✓ pst r ∧ ✓ gst r : uPred M')%I.
Proof. by uPred.unseal. Qed.
End res.

Arguments resC : clear implicits.
Arguments resR : clear implicits.

(* Functor *)
Definition res_map {Λ} {A A' : cofeT} {M M' : cmraT}
    (f : A → A') (g : M → M') (r : res Λ A M) : res Λ A' M' :=
  Res (agree_map f <$> wld r) (pst r) (g $ gst r).
Instance res_map_ne {Λ} {A A': cofeT} {M M' : cmraT} (f : A → A') (g : M → M') :
  (∀ n, Proper (dist n ==> dist n) f) → (∀ n, Proper (dist n ==> dist n) g) →
  ∀ n, Proper (dist n ==> dist n) (@res_map Λ _ _ _ _ f g).
Proof. intros Hf n [] ? [???]; constructor; by cofe_subst. Qed.
Lemma res_map_id {Λ A M} (r : res Λ A M) : res_map id id r ≡ r.
Proof.
  constructor; rewrite /res_map /=; f_equal.
  - rewrite -{2}(map_fmap_id (wld r)). apply map_fmap_setoid_ext=> i y ? /=.
    by rewrite -{2}(agree_map_id y).
Qed.
Lemma res_map_compose {Λ} {A1 A2 A3 : cofeT} {M1 M2 M3 : cmraT}
   (f : A1 → A2) (f' : A2 → A3) (g : M1 → M2) (g' : M2 → M3) (r : res Λ A1 M1) :
  res_map (f' ∘ f) (g' ∘ g) r ≡ res_map f' g' (res_map f g r).
Proof.
  constructor; rewrite /res_map /=; f_equal.
  - rewrite -map_fmap_compose; apply map_fmap_setoid_ext=> i y _ /=.
    by rewrite -agree_map_compose.
Qed.
Lemma res_map_ext {Λ} {A A' : cofeT} {M M' : cmraT}
    (f f' : A → A') (g g' : M → M') (r : res Λ A M) :
  (∀ x, f x ≡ f' x) → (∀ m, g m ≡ g' m) → res_map f g r ≡ res_map f' g' r.
Proof.
  intros Hf Hg; split; simpl; auto.
  - by apply map_fmap_setoid_ext=>i x ?; apply agree_map_ext.
Qed.
Instance res_map_cmra_monotone {Λ}
    {A A' : cofeT} {M M': cmraT} (f: A → A') (g: M → M') :
  (∀ n, Proper (dist n ==> dist n) f) → CMRAMonotone g →
  CMRAMonotone (@res_map Λ _ _ _ _ f g).
Proof.
  split; first apply _.
  - intros n r (?&?&?); split_and!; simpl; by try apply: validN_preserving.
  - by intros r1 r2; rewrite !res_included;
      intros (?&?&?); split_and!; simpl; try apply: included_preserving.
Qed.
Definition resC_map {Λ} {A A' : cofeT} {M M' : cmraT}
    (f : A -n> A') (g : M -n> M') : resC Λ A M -n> resC Λ A' M' :=
  CofeMor (res_map f g : resC Λ A M → resC Λ A' M').
Instance resC_map_ne {Λ A A' M M'} n :
  Proper (dist n ==> dist n ==> dist n) (@resC_map Λ A A' M M').
Proof.
  intros f g Hfg r; split; simpl; auto.
  - by apply (mapC_map_ne _ (agreeC_map f) (agreeC_map g)), agreeC_map_ne.
Qed.

Program Definition resRF (Λ : language)
    (F1 : cFunctor) (F2 : rFunctor) : rFunctor := {|
  rFunctor_car A B := resR Λ (cFunctor_car F1 A B) (rFunctor_car F2 A B);
  rFunctor_map A1 A2 B1 B2 fg :=resC_map (cFunctor_map F1 fg) (rFunctor_map F2 fg)
|}.
Next Obligation.
  intros Λ F1 F2 A1 A2 B1 B2 n f g Hfg; apply resC_map_ne.
  - by apply cFunctor_ne.
  - by apply rFunctor_ne.
Qed.
Next Obligation.
  intros Λ F Σ A B x. rewrite /= -{2}(res_map_id x).
  apply res_map_ext=>y. apply cFunctor_id. apply rFunctor_id.
Qed.
Next Obligation.
  intros Λ F Σ A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -res_map_compose.
  apply res_map_ext=>y. apply cFunctor_compose. apply rFunctor_compose.
Qed.

Instance resRF_contractive Λ F1 F2 :
  cFunctorContractive F1 → rFunctorContractive F2 →
  rFunctorContractive (resRF Λ F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n f g Hfg; apply resC_map_ne.
  - by apply cFunctor_contractive.
  - by apply rFunctor_contractive.
Qed.
