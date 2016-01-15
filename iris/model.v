Require Export modures.logic modures.cmra.
Require Export modures.fin_maps modures.agree modures.excl.
Require Import modures.cofe_solver.

(* Parameter *)
Record iParam := IParam {
  istate : Type;
  icmra : cofeT → cmraT;
  icmra_empty A : Empty (icmra A);
  icmra_empty_spec A : RAIdentity (icmra A);
  icmra_map {A B} (f : A -n> B) : icmra A -n> icmra B;
  icmra_map_ne {A B} n : Proper (dist n ==> dist n) (@icmra_map A B);
  icmra_map_id {A : cofeT} (x : icmra A) : icmra_map cid x ≡ x;
  icmra_map_compose {A B C} (f : A -n> B) (g : B -n> C) x :
    icmra_map (g ◎ f) x ≡ icmra_map g (icmra_map f x);
  icmra_map_mono {A B} (f : A -n> B) : CMRAMonotone (icmra_map f)
}.
Existing Instances icmra_empty icmra_empty_spec icmra_map_ne icmra_map_mono.

Lemma icmra_map_ext (Σ : iParam) {A B} (f g : A -n> B) m :
  (∀ x, f x ≡ g x) → icmra_map Σ f m ≡ icmra_map Σ g m.
Proof.
  by intros ?; apply equiv_dist=> n; apply icmra_map_ne=> ?; apply equiv_dist.
Qed.

(* Resources *)
Record res (Σ : iParam) (A : cofeT) := Res {
  wld : mapRA positive (agreeRA (laterC A));
  pst : exclRA (leibnizC (istate Σ));
  gst : icmra Σ (laterC A);
}.
Add Printing Constructor res.
Arguments Res {_ _} _ _ _.
Arguments wld {_ _} _.
Arguments pst {_ _} _.
Arguments gst {_ _} _.
Instance: Params (@Res) 2.
Instance: Params (@wld) 2.
Instance: Params (@pst) 2.
Instance: Params (@gst) 2.

Section res.
Context (Σ : iParam) (A : cofeT).
Implicit Types r : res Σ A.

Inductive res_equiv' (r1 r2 : res Σ A) := Res_equiv :
  wld r1 ≡ wld r2 → pst r1 ≡ pst r2 → gst r1 ≡ gst r2 → res_equiv' r1 r2.
Instance res_equiv : Equiv (res Σ A) := res_equiv'.
Inductive res_dist' (n : nat) (r1 r2 : res Σ A) := Res_dist :
  wld r1 ={n}= wld r2 → pst r1 ={n}= pst r2 → gst r1 ={n}= gst r2 →
  res_dist' n r1 r2.
Instance res_dist : Dist (res Σ A) := res_dist'.
Global Instance Res_ne n :
  Proper (dist n ==> dist n ==> dist n ==> dist n) (@Res Σ A).
Proof. done. Qed.
Global Instance Res_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (@Res Σ A).
Proof. done. Qed.
Global Instance wld_ne n : Proper (dist n ==> dist n) (@wld Σ A).
Proof. by destruct 1. Qed.
Global Instance wld_proper : Proper ((≡) ==> (≡)) (@wld Σ A).
Proof. by destruct 1. Qed.
Global Instance pst_ne n : Proper (dist n ==> dist n) (@pst Σ A).
Proof. by destruct 1. Qed.
Global Instance pst_ne' n : Proper (dist (S n) ==> (≡)) (@pst Σ A).
Proof.
  intros σ σ' [???]; apply (timeless _), dist_le with (S n); auto with lia.
Qed.
Global Instance pst_proper : Proper ((≡) ==> (≡)) (@pst Σ A).
Proof. by destruct 1. Qed.
Global Instance gst_ne n : Proper (dist n ==> dist n) (@gst Σ A).
Proof. by destruct 1. Qed.
Global Instance gst_proper : Proper ((≡) ==> (≡)) (@gst Σ A).
Proof. by destruct 1. Qed.
Instance res_compl : Compl (res Σ A) := λ c,
  Res (compl (chain_map wld c))
      (compl (chain_map pst c)) (compl (chain_map gst c)).
Definition res_cofe_mixin : CofeMixin (res Σ A).
Proof.
  split.
  * intros w1 w2; split.
    + by destruct 1; constructor; apply equiv_dist.
    + by intros Hw; constructor; apply equiv_dist=>n; destruct (Hw n).
  * intros n; split.
    + done.
    + by destruct 1; constructor.
    + do 2 destruct 1; constructor; etransitivity; eauto.
  * by destruct 1; constructor; apply dist_S.
  * done.
  * intros c n; constructor.
    + apply (conv_compl (chain_map wld c) n).
    + apply (conv_compl (chain_map pst c) n).
    + apply (conv_compl (chain_map gst c) n).
Qed.
Canonical Structure resC : cofeT := CofeT res_cofe_mixin.
Global Instance res_timeless r :
  Timeless (wld r) → Timeless (gst r) → Timeless r.
Proof. by destruct 3; constructor; try apply (timeless _). Qed.

Instance res_op : Op (res Σ A) := λ r1 r2,
  Res (wld r1 ⋅ wld r2) (pst r1 ⋅ pst r2) (gst r1 ⋅ gst r2).
Global Instance res_empty : Empty (res Σ A) := Res ∅ ∅ ∅.
Instance res_unit : Unit (res Σ A) := λ r,
  Res (unit (wld r)) (unit (pst r)) (unit (gst r)).
Instance res_valid : Valid (res Σ A) := λ r, ✓ (wld r) ∧ ✓ (pst r) ∧ ✓ (gst r).
Instance res_validN : ValidN (res Σ A) := λ n r,
  ✓{n} (wld r) ∧ ✓{n} (pst r) ∧ ✓{n} (gst r).
Instance res_minus : Minus (res Σ A) := λ r1 r2,
  Res (wld r1 ⩪ wld r2) (pst r1 ⩪ pst r2) (gst r1 ⩪ gst r2).
Lemma res_included (r1 r2 : res Σ A) :
  r1 ≼ r2 ↔ wld r1 ≼ wld r2 ∧ pst r1 ≼ pst r2 ∧ gst r1 ≼ gst r2.
Proof.
  split; [|by intros ([w ?]&[σ ?]&[m ?]); exists (Res w σ m)].
  intros [r Hr]; split_ands;
    [exists (wld r)|exists (pst r)|exists (gst r)]; apply Hr.
Qed.
Lemma res_includedN (r1 r2 : res Σ A) n :
  r1 ≼{n} r2 ↔ wld r1 ≼{n} wld r2 ∧ pst r1 ≼{n} pst r2 ∧ gst r1 ≼{n} gst r2.
Proof.
  split; [|by intros ([w ?]&[σ ?]&[m ?]); exists (Res w σ m)].
  intros [r Hr]; split_ands;
    [exists (wld r)|exists (pst r)|exists (gst r)]; apply Hr.
Qed.
Definition res_cmra_mixin : CMRAMixin (res Σ A).
Proof.
  split.
  * by intros n x [???] ? [???]; constructor; simpl in *; cofe_subst.
  * by intros n [???] ? [???]; constructor; simpl in *; cofe_subst.
  * by intros n [???] ? [???] (?&?&?); split_ands'; simpl in *; cofe_subst.
  * by intros n [???] ? [???] [???] ? [???];
      constructor; simpl in *; cofe_subst.
  * done.
  * by intros n ? (?&?&?); split_ands'; apply cmra_valid_S.
  * intros r; unfold valid, res_valid, validN, res_validN.
    rewrite !cmra_valid_validN; naive_solver.
  * intros ???; constructor; simpl; apply (associative _).
  * intros ??; constructor; simpl; apply (commutative _).
  * intros ?; constructor; simpl; apply ra_unit_l.
  * intros ?; constructor; simpl; apply ra_unit_idempotent.
  * intros n r1 r2; rewrite !res_includedN.
    by intros (?&?&?); split_ands'; apply cmra_unit_preserving.
  * intros n r1 r2 (?&?&?);
      split_ands'; simpl in *; eapply cmra_valid_op_l; eauto.
  * intros n r1 r2; rewrite res_includedN; intros (?&?&?).
    by constructor; apply cmra_op_minus.
Qed.
Global Instance res_ra_empty : RAIdentity (res Σ A).
Proof.
  by repeat split; simpl; repeat apply ra_empty_valid; rewrite (left_id _ _).
Qed.

Definition res_cmra_extend_mixin : CMRAExtendMixin (res Σ A).
Proof.
  intros n r r1 r2 (?&?&?) [???]; simpl in *.
  destruct (cmra_extend_op n (wld r) (wld r1) (wld r2)) as ([w w']&?&?&?),
    (cmra_extend_op n (pst r) (pst r1) (pst r2)) as ([σ σ']&?&?&?),
    (cmra_extend_op n (gst r) (gst r1) (gst r2)) as ([m m']&?&?&?); auto.
  by exists (Res w σ m, Res w' σ' m').
Qed.
Canonical Structure resRA : cmraT :=
  CMRAT res_cofe_mixin res_cmra_mixin res_cmra_extend_mixin.
Lemma Res_op w1 w2 σ1 σ2 m1 m2 :
  Res w1 σ1 m1 ⋅ Res w2 σ2 m2 = Res (w1 ⋅ w2) (σ1 ⋅ σ2) (m1 ⋅ m2).
Proof. done. Qed.
Lemma Res_unit w σ m : unit (Res w σ m) = Res (unit w) (unit σ) (unit m).
Proof. done. Qed.
End res.

Definition res_map {Σ A B} (f : A -n> B) (r : res Σ A) : res Σ B :=
  Res (agree_map (later_map f) <$> (wld r))
      (pst r)
      (icmra_map Σ (laterC_map f) (gst r)).
Instance res_map_ne Σ (A B : cofeT) (f : A -n> B) :
  (∀ n, Proper (dist n ==> dist n) f) →
  ∀ n, Proper (dist n ==> dist n) (@res_map Σ _ _ f).
Proof. by intros Hf n [] ? [???]; constructor; simpl in *; cofe_subst. Qed.
Lemma res_map_id {Σ A} (r : res Σ A) : res_map cid r ≡ r.
Proof.
  constructor; simpl; [|done|].
  * rewrite -{2}(map_fmap_id (wld r)); apply map_fmap_setoid_ext=> i y ? /=.
    rewrite -{2}(agree_map_id y); apply agree_map_ext=> y' /=.
    by rewrite later_map_id.
  * rewrite -{2}(icmra_map_id Σ (gst r)); apply icmra_map_ext=> m /=.
    by rewrite later_map_id.
Qed.
Lemma res_map_compose {Σ A B C} (f : A -n> B) (g : B -n> C) (r : res Σ A) :
  res_map (g ◎ f) r ≡ res_map g (res_map f r).
Proof.
  constructor; simpl; [|done|].
  * rewrite -map_fmap_compose; apply map_fmap_setoid_ext=> i y _ /=.
    rewrite -agree_map_compose; apply agree_map_ext=> y' /=.
    by rewrite later_map_compose.
  * rewrite -icmra_map_compose; apply icmra_map_ext=> m /=.
    by rewrite later_map_compose.
Qed.
Definition resRA_map {Σ A B} (f : A -n> B) : resRA Σ A -n> resRA Σ B :=
  CofeMor (res_map f : resRA Σ A → resRA Σ B).
Instance res_map_cmra_monotone {Σ} {A B : cofeT} (f : A -n> B) :
  CMRAMonotone (@res_map Σ _ _ f).
Proof.
  split.
  * by intros n r1 r2; rewrite !res_includedN;
      intros (?&?&?); split_ands'; simpl; try apply includedN_preserving.
  * by intros n r (?&?&?); split_ands'; simpl; try apply validN_preserving.
Qed.
Instance resRA_map_contractive {Σ A B} : Contractive (@resRA_map Σ A B).
Proof.
  intros n f g ? r; constructor; simpl; [|done|].
  * by apply (mapRA_map_ne _ (agreeRA_map (laterC_map f))
      (agreeRA_map (laterC_map g))), agreeRA_map_ne, laterC_map_contractive.
  * by apply icmra_map_ne, laterC_map_contractive.
Qed.

(* Functor for the solution *)
Module iProp.
Definition F (Σ : iParam) (A B : cofeT) : cofeT := uPredC (resRA Σ A).
Definition map {Σ : iParam} {A1 A2 B1 B2 : cofeT}
    (f : (A2 -n> A1) * (B1 -n> B2)) : F Σ A1 B1 -n> F Σ A2 B2 :=
  uPredC_map (resRA_map (f.1)).
Definition result Σ : solution (F Σ).
Proof.
  apply (solver.result _ (@map Σ)).
  * by intros A B r n ?; rewrite /uPred_holds /= res_map_id.
  * by intros A1 A2 A3 B1 B2 B3 f g f' g' P r n ?;
      rewrite /= /uPred_holds /= res_map_compose.
  * by intros A1 A2 B1 B2 n f f' [??] r;
      apply upredC_map_ne, resRA_map_contractive.
Qed.
End iProp.

(* Solution *)
Definition iPreProp (Σ : iParam) : cofeT := iProp.result Σ.
Notation res' Σ := (res Σ (iPreProp Σ)).
Notation icmra' Σ := (icmra Σ (laterC (iPreProp Σ))).
Definition iProp (Σ : iParam) : cofeT := uPredC (resRA Σ (iPreProp Σ)).
Definition iProp_unfold {Σ} : iProp Σ -n> iPreProp Σ := solution_fold _.
Definition iProp_fold {Σ} : iPreProp Σ -n> iProp Σ := solution_unfold _.
Lemma iProp_fold_unfold {Σ} (P : iProp Σ) : iProp_fold (iProp_unfold P) ≡ P.
Proof. apply solution_unfold_fold. Qed.
Lemma iProp_unfold_fold {Σ} (P : iPreProp Σ) : iProp_unfold (iProp_fold P) ≡ P.
Proof. apply solution_fold_unfold. Qed.
Bind Scope uPred_scope with iProp.
