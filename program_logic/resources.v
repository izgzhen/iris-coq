From algebra Require Export fin_maps agree excl functor.
From algebra Require Import upred.
From program_logic Require Export language.

Record res (Λ : language) (Σ : iFunctor) (A : cofeT) := Res {
  wld : mapRA positive (agreeRA A);
  pst : exclRA (istateC Λ);
  gst : optionRA (Σ A);
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
Context {Λ : language} {Σ : iFunctor} {A : cofeT}.
Implicit Types r : res Λ Σ A.

Inductive res_equiv' (r1 r2 : res Λ Σ A) := Res_equiv :
  wld r1 ≡ wld r2 → pst r1 ≡ pst r2 → gst r1 ≡ gst r2 → res_equiv' r1 r2.
Instance res_equiv : Equiv (res Λ Σ A) := res_equiv'.
Inductive res_dist' (n : nat) (r1 r2 : res Λ Σ A) := Res_dist :
  wld r1 ≡{n}≡ wld r2 → pst r1 ≡{n}≡ pst r2 → gst r1 ≡{n}≡ gst r2 →
  res_dist' n r1 r2.
Instance res_dist : Dist (res Λ Σ A) := res_dist'.
Global Instance Res_ne n :
  Proper (dist n ==> dist n ==> dist n ==> dist n) (@Res Λ Σ A).
Proof. done. Qed.
Global Instance Res_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (@Res Λ Σ A).
Proof. done. Qed.
Global Instance wld_ne n : Proper (dist n ==> dist n) (@wld Λ Σ A).
Proof. by destruct 1. Qed.
Global Instance wld_proper : Proper ((≡) ==> (≡)) (@wld Λ Σ A).
Proof. by destruct 1. Qed.
Global Instance pst_ne n : Proper (dist n ==> dist n) (@pst Λ Σ A).
Proof. by destruct 1. Qed.
Global Instance pst_ne' n : Proper (dist n ==> (≡)) (@pst Λ Σ A).
Proof. destruct 1; apply: timeless; apply dist_le with n; auto with lia. Qed.
Global Instance pst_proper : Proper ((≡) ==> (=)) (@pst Λ Σ A).
Proof. by destruct 1; unfold_leibniz. Qed.
Global Instance gst_ne n : Proper (dist n ==> dist n) (@gst Λ Σ A).
Proof. by destruct 1. Qed.
Global Instance gst_proper : Proper ((≡) ==> (≡)) (@gst Λ Σ A).
Proof. by destruct 1. Qed.
Instance res_compl : Compl (res Λ Σ A) := λ c,
  Res (compl (chain_map wld c))
      (compl (chain_map pst c)) (compl (chain_map gst c)).
Definition res_cofe_mixin : CofeMixin (res Λ Σ A).
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

Instance res_op : Op (res Λ Σ A) := λ r1 r2,
  Res (wld r1 ⋅ wld r2) (pst r1 ⋅ pst r2) (gst r1 ⋅ gst r2).
Global Instance res_empty : Empty (res Λ Σ A) := Res ∅ ∅ ∅.
Instance res_unit : Unit (res Λ Σ A) := λ r,
  Res (unit (wld r)) (unit (pst r)) (unit (gst r)).
Instance res_validN : ValidN (res Λ Σ A) := λ n r,
  ✓{n} wld r ∧ ✓{n} pst r ∧ ✓{n} gst r.
Instance res_minus : Minus (res Λ Σ A) := λ r1 r2,
  Res (wld r1 ⩪ wld r2) (pst r1 ⩪ pst r2) (gst r1 ⩪ gst r2).
Lemma res_included (r1 r2 : res Λ Σ A) :
  r1 ≼ r2 ↔ wld r1 ≼ wld r2 ∧ pst r1 ≼ pst r2 ∧ gst r1 ≼ gst r2.
Proof.
  split; [|by intros ([w ?]&[σ ?]&[m ?]); exists (Res w σ m)].
  intros [r Hr]; split_and?;
    [exists (wld r)|exists (pst r)|exists (gst r)]; apply Hr.
Qed.
Lemma res_includedN (r1 r2 : res Λ Σ A) n :
  r1 ≼{n} r2 ↔ wld r1 ≼{n} wld r2 ∧ pst r1 ≼{n} pst r2 ∧ gst r1 ≼{n} gst r2.
Proof.
  split; [|by intros ([w ?]&[σ ?]&[m ?]); exists (Res w σ m)].
  intros [r Hr]; split_and?;
    [exists (wld r)|exists (pst r)|exists (gst r)]; apply Hr.
Qed.
Definition res_cmra_mixin : CMRAMixin (res Λ Σ A).
Proof.
  split.
  - by intros n x [???] ? [???]; constructor; simpl in *; cofe_subst.
  - by intros n [???] ? [???]; constructor; simpl in *; cofe_subst.
  - by intros n [???] ? [???] (?&?&?); split_and!; simpl in *; cofe_subst.
  - by intros n [???] ? [???] [???] ? [???];
      constructor; simpl in *; cofe_subst.
  - by intros n ? (?&?&?); split_and!; apply cmra_validN_S.
  - by intros ???; constructor; rewrite /= assoc.
  - by intros ??; constructor; rewrite /= comm.
  - by intros ?; constructor; rewrite /= cmra_unit_l.
  - by intros ?; constructor; rewrite /= cmra_unit_idemp.
  - intros n r1 r2; rewrite !res_includedN.
    by intros (?&?&?); split_and!; apply cmra_unit_preservingN.
  - intros n r1 r2 (?&?&?);
      split_and!; simpl in *; eapply cmra_validN_op_l; eauto.
  - intros n r1 r2; rewrite res_includedN; intros (?&?&?).
    by constructor; apply cmra_op_minus.
Qed.
Definition res_cmra_extend_mixin : CMRAExtendMixin (res Λ Σ A).
Proof.
  intros n r r1 r2 (?&?&?) [???]; simpl in *.
  destruct (cmra_extend_op n (wld r) (wld r1) (wld r2)) as ([w w']&?&?&?),
    (cmra_extend_op n (pst r) (pst r1) (pst r2)) as ([σ σ']&?&?&?),
    (cmra_extend_op n (gst r) (gst r1) (gst r2)) as ([m m']&?&?&?); auto.
  by exists (Res w σ m, Res w' σ' m').
Qed.
Canonical Structure resRA : cmraT :=
  CMRAT res_cofe_mixin res_cmra_mixin res_cmra_extend_mixin.
Global Instance res_cmra_identity : CMRAIdentity resRA.
Proof.
  split.
  - intros n; split_and!; apply cmra_empty_valid.
  - by split; rewrite /= left_id.
  - apply _.
Qed.

Definition update_pst (σ : state Λ) (r : res Λ Σ A) : res Λ Σ A :=
  Res (wld r) (Excl σ) (gst r).
Definition update_gst (m : Σ A) (r : res Λ Σ A) : res Λ Σ A :=
  Res (wld r) (pst r) (Some m).

Lemma wld_validN n r : ✓{n} r → ✓{n} wld r.
Proof. by intros (?&?&?). Qed.
Lemma gst_validN n r : ✓{n} r → ✓{n} gst r.
Proof. by intros (?&?&?). Qed.
Lemma Res_op w1 w2 σ1 σ2 m1 m2 :
  Res w1 σ1 m1 ⋅ Res w2 σ2 m2 = Res (w1 ⋅ w2) (σ1 ⋅ σ2) (m1 ⋅ m2).
Proof. done. Qed.
Lemma Res_unit w σ m : unit (Res w σ m) = Res (unit w) (unit σ) (unit m).
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
Global Instance Res_timeless eσ m : Timeless m → Timeless (Res ∅ eσ m).
Proof. by intros ? ? [???]; constructor; apply: timeless. Qed.

(** Internalized properties *)
Lemma res_equivI {M} r1 r2 :
  (r1 ≡ r2)%I ≡ (wld r1 ≡ wld r2 ∧ pst r1 ≡ pst r2 ∧ gst r1 ≡ gst r2: uPred M)%I.
Proof. do 2 split. by destruct 1. by intros (?&?&?); constructor. Qed.
Lemma res_validI {M} r : (✓ r)%I ≡ (✓ wld r ∧ ✓ pst r ∧ ✓ gst r : uPred M)%I.
Proof. done. Qed.
End res.

Arguments resC : clear implicits.
Arguments resRA : clear implicits.

Definition res_map {Λ Σ A B} (f : A -n> B) (r : res Λ Σ A) : res Λ Σ B :=
  Res (agree_map f <$> wld r) (pst r) (ifunctor_map Σ f <$> gst r).
Instance res_map_ne Λ Σ (A B : cofeT) (f : A -n> B) :
  (∀ n, Proper (dist n ==> dist n) f) →
  ∀ n, Proper (dist n ==> dist n) (@res_map Λ Σ _ _ f).
Proof. by intros Hf n [] ? [???]; constructor; simpl in *; cofe_subst. Qed.
Lemma res_map_id {Λ Σ A} (r : res Λ Σ A) : res_map cid r ≡ r.
Proof.
  constructor; simpl; [|done|].
  - rewrite -{2}(map_fmap_id (wld r)); apply map_fmap_setoid_ext=> i y ? /=.
    by rewrite -{2}(agree_map_id y); apply agree_map_ext.
  - rewrite -{2}(option_fmap_id (gst r)); apply option_fmap_setoid_ext=> m /=.
    by rewrite -{2}(ifunctor_map_id Σ m); apply ifunctor_map_ext.
Qed.
Lemma res_map_compose {Λ Σ A B C} (f : A -n> B) (g : B -n> C) (r : res Λ Σ A) :
  res_map (g ◎ f) r ≡ res_map g (res_map f r).
Proof.
  constructor; simpl; [|done|].
  - rewrite -map_fmap_compose; apply map_fmap_setoid_ext=> i y _ /=.
    by rewrite -agree_map_compose; apply agree_map_ext.
  - rewrite -option_fmap_compose; apply option_fmap_setoid_ext=> m /=.
    by rewrite -ifunctor_map_compose; apply ifunctor_map_ext.
Qed.
Lemma res_map_ext {Λ Σ A B} (f g : A -n> B) (r : res Λ Σ A) :
  (∀ x, f x ≡ g x) → res_map f r ≡ res_map g r.
Proof.
  intros Hfg; split; simpl; auto.
  - by apply map_fmap_setoid_ext=>i x ?; apply agree_map_ext.
  - by apply option_fmap_setoid_ext=>m; apply ifunctor_map_ext.
Qed.
Instance res_map_cmra_monotone {Λ Σ} {A B : cofeT} (f : A -n> B) :
  CMRAMonotone (@res_map Λ Σ _ _ f).
Proof.
  split.
  - by intros n r1 r2; rewrite !res_includedN;
      intros (?&?&?); split_and!; simpl; try apply includedN_preserving.
  - by intros n r (?&?&?); split_and!; simpl; try apply validN_preserving.
Qed.
Definition resC_map {Λ Σ A B} (f : A -n> B) : resC Λ Σ A -n> resC Λ Σ B :=
  CofeMor (res_map f : resRA Λ Σ A → resRA Λ Σ B).
Instance resC_map_ne {Λ Σ A B} n :
  Proper (dist n ==> dist n) (@resC_map Λ Σ A B).
Proof.
  intros f g Hfg r; split; simpl; auto.
  - by apply (mapC_map_ne _ (agreeC_map f) (agreeC_map g)), agreeC_map_ne.
  - by apply optionC_map_ne, ifunctor_map_ne.
Qed.

Program Definition resF {Λ Σ} : iFunctor := {|
  ifunctor_car := resRA Λ Σ;
  ifunctor_map A B := resC_map
|}.
Next Obligation. intros Λ Σ A x. by rewrite /= res_map_id. Qed.
Next Obligation. intros Λ Σ A B C f g x. by rewrite /= res_map_compose. Qed.
