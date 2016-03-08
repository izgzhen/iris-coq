From algebra Require Export cmra.
From algebra Require Import upred.

(* COFE *)
Section cofe.
Context {A : cofeT}.
Inductive option_dist : Dist (option A) :=
  | Some_dist n x y : x ≡{n}≡ y → Some x ≡{n}≡ Some y
  | None_dist n : None ≡{n}≡ None.
Existing Instance option_dist.
Program Definition option_chain
    (c : chain (option A)) (x : A) (H : c 0 = Some x) : chain A :=
  {| chain_car n := from_option x (c n) |}.
Next Obligation.
  intros c x ? n i ?; simpl.
  destruct (c 0) eqn:?; simplify_eq/=.
  by feed inversion (chain_cauchy c n i).
Qed.
Instance option_compl : Compl (option A) := λ c,
  match Some_dec (c 0) with
  | inleft (exist x H) => Some (compl (option_chain c x H)) | inright _ => None
  end.
Definition option_cofe_mixin : CofeMixin (option A).
Proof.
  split.
  - intros mx my; split; [by destruct 1; constructor; apply equiv_dist|].
    intros Hxy; feed inversion (Hxy 1); subst; constructor; apply equiv_dist.
    by intros n; feed inversion (Hxy n).
  - intros n; split.
    + by intros [x|]; constructor.
    + by destruct 1; constructor.
    + destruct 1; inversion_clear 1; constructor; etrans; eauto.
  - by inversion_clear 1; constructor; apply dist_S.
  - intros n c; unfold compl, option_compl.
    destruct (Some_dec (c 0)) as [[x Hx]|].
    { assert (is_Some (c n)) as [y Hy].
      { feed inversion (chain_cauchy c 0 n); eauto with lia congruence. }
      rewrite Hy; constructor.
      by rewrite (conv_compl n (option_chain c x Hx)) /= Hy. }
    feed inversion (chain_cauchy c 0 n); eauto with lia congruence.
    constructor.
Qed.
Canonical Structure optionC := CofeT option_cofe_mixin.
Global Instance option_discrete : Discrete A → Discrete optionC.
Proof. inversion_clear 2; constructor; by apply (timeless _). Qed.

Global Instance Some_ne : Proper (dist n ==> dist n) (@Some A).
Proof. by constructor. Qed.
Global Instance is_Some_ne n : Proper (dist n ==> iff) (@is_Some A).
Proof. inversion_clear 1; split; eauto. Qed.
Global Instance Some_dist_inj : Inj (dist n) (dist n) (@Some A).
Proof. by inversion_clear 1. Qed.
Global Instance None_timeless : Timeless (@None A).
Proof. inversion_clear 1; constructor. Qed.
Global Instance Some_timeless x : Timeless x → Timeless (Some x).
Proof. by intros ?; inversion_clear 1; constructor; apply timeless. Qed.
End cofe.

Arguments optionC : clear implicits.

(* CMRA *)
Section cmra.
Context {A : cmraT}.

Instance option_valid : Valid (option A) := λ mx,
  match mx with Some x => ✓ x | None => True end.
Instance option_validN : ValidN (option A) := λ n mx,
  match mx with Some x => ✓{n} x | None => True end.
Global Instance option_empty : Empty (option A) := None.
Instance option_core : Core (option A) := fmap core.
Instance option_op : Op (option A) := union_with (λ x y, Some (x ⋅ y)).
Instance option_div : Div (option A) :=
  difference_with (λ x y, Some (x ÷ y)).

Definition Some_valid a : ✓ Some a ↔ ✓ a := reflexivity _.
Definition Some_op a b : Some (a ⋅ b) = Some a ⋅ Some b := eq_refl.

Lemma option_included (mx my : option A) :
  mx ≼ my ↔ mx = None ∨ ∃ x y, mx = Some x ∧ my = Some y ∧ x ≼ y.
Proof.
  split.
  - intros [mz Hmz].
    destruct mx as [x|]; [right|by left].
    destruct my as [y|]; [exists x, y|destruct mz; inversion_clear Hmz].
    destruct mz as [z|]; inversion_clear Hmz; split_and?; auto;
      setoid_subst; eauto using cmra_included_l.
  - intros [->|(x&y&->&->&z&Hz)]; try (by exists my; destruct my; constructor).
    by exists (Some z); constructor.
Qed.

Definition option_cmra_mixin  : CMRAMixin (option A).
Proof.
  split.
  - by intros n [x|]; destruct 1; constructor; cofe_subst.
  - by destruct 1; constructor; cofe_subst.
  - by destruct 1; rewrite /validN /option_validN //=; cofe_subst.
  - by destruct 1; inversion_clear 1; constructor; cofe_subst.
  - intros [x|]; [apply cmra_valid_validN|done].
  - intros n [x|]; unfold validN, option_validN; eauto using cmra_validN_S.
  - intros [x|] [y|] [z|]; constructor; rewrite ?assoc; auto.
  - intros [x|] [y|]; constructor; rewrite 1?comm; auto.
  - by intros [x|]; constructor; rewrite cmra_core_l.
  - by intros [x|]; constructor; rewrite cmra_core_idemp.
  - intros mx my; rewrite !option_included ;intros [->|(x&y&->&->&?)]; auto.
    right; exists (core x), (core y); eauto using cmra_core_preserving.
  - intros n [x|] [y|]; rewrite /validN /option_validN /=;
      eauto using cmra_validN_op_l.
  - intros mx my; rewrite option_included.
    intros [->|(x&y&->&->&?)]; [by destruct my|].
    by constructor; apply cmra_op_div.
  - intros n mx my1 my2.
    destruct mx as [x|], my1 as [y1|], my2 as [y2|]; intros Hx Hx';
      try (by exfalso; inversion Hx'; auto).
    + destruct (cmra_extend n x y1 y2) as ([z1 z2]&?&?&?); auto.
      { by inversion_clear Hx'. }
      by exists (Some z1, Some z2); repeat constructor.
    + by exists (Some x,None); inversion Hx'; repeat constructor.
    + by exists (None,Some x); inversion Hx'; repeat constructor.
    + exists (None,None); repeat constructor.
Qed.
Canonical Structure optionR := CMRAT option_cofe_mixin option_cmra_mixin.
Global Instance option_cmra_unit : CMRAUnit optionR.
Proof. split. done. by intros []. by inversion_clear 1. Qed.
Global Instance option_cmra_discrete : CMRADiscrete A → CMRADiscrete optionR.
Proof. split; [apply _|]. by intros [x|]; [apply (cmra_discrete_valid x)|]. Qed.

(** Misc *)
Global Instance Some_cmra_monotone : CMRAMonotone Some.
Proof. split; [apply _|done|intros x y [z ->]; by exists (Some z)]. Qed.
Lemma op_is_Some mx my : is_Some (mx ⋅ my) ↔ is_Some mx ∨ is_Some my.
Proof.
  destruct mx, my; rewrite /op /option_op /= -!not_eq_None_Some; naive_solver.
Qed.
Lemma option_op_positive_dist_l n mx my : mx ⋅ my ≡{n}≡ None → mx ≡{n}≡ None.
Proof. by destruct mx, my; inversion_clear 1. Qed.
Lemma option_op_positive_dist_r n mx my : mx ⋅ my ≡{n}≡ None → my ≡{n}≡ None.
Proof. by destruct mx, my; inversion_clear 1. Qed.

(** Internalized properties *)
Lemma option_equivI {M} (x y : option A) :
  (x ≡ y)%I ≡ (match x, y with
               | Some a, Some b => a ≡ b | None, None => True | _, _ => False
               end : uPred M)%I.
Proof.
  uPred.unseal. do 2 split. by destruct 1. by destruct x, y; try constructor.
Qed.
Lemma option_validI {M} (x : option A) :
  (✓ x)%I ≡ (match x with Some a => ✓ a | None => True end : uPred M)%I.
Proof. uPred.unseal. by destruct x. Qed.

(** Updates *)
Lemma option_updateP (P : A → Prop) (Q : option A → Prop) x :
  x ~~>: P → (∀ y, P y → Q (Some y)) → Some x ~~>: Q.
Proof.
  intros Hx Hy n [y|] ?.
  { destruct (Hx n y) as (y'&?&?); auto. exists (Some y'); auto. }
  destruct (Hx n (core x)) as (y'&?&?); rewrite ?cmra_core_r; auto.
  by exists (Some y'); split; [auto|apply cmra_validN_op_l with (core x)].
Qed.
Lemma option_updateP' (P : A → Prop) x :
  x ~~>: P → Some x ~~>: λ y, default False y P.
Proof. eauto using option_updateP. Qed.
Lemma option_update x y : x ~~> y → Some x ~~> Some y.
Proof.
  rewrite !cmra_update_updateP; eauto using option_updateP with congruence.
Qed.
Lemma option_update_None `{Empty A, !CMRAUnit A} : ∅ ~~> Some ∅.
Proof.
  intros n [x|] ?; rewrite /op /cmra_op /validN /cmra_validN /= ?left_id;
    auto using cmra_unit_validN.
Qed.
End cmra.
Arguments optionR : clear implicits.

(** Functor *)
Instance option_fmap_ne {A B : cofeT} (f : A → B) n:
  Proper (dist n ==> dist n) f → Proper (dist n==>dist n) (fmap (M:=option) f).
Proof. by intros Hf; destruct 1; constructor; apply Hf. Qed.
Instance option_fmap_cmra_monotone {A B : cmraT} (f: A → B) `{!CMRAMonotone f} :
  CMRAMonotone (fmap f : option A → option B).
Proof.
  split; first apply _.
  - intros n [x|] ?; rewrite /cmra_validN //=. by apply (validN_preserving f).
  - intros mx my; rewrite !option_included.
    intros [->|(x&y&->&->&?)]; simpl; eauto 10 using @included_preserving.
Qed.
Definition optionC_map {A B} (f : A -n> B) : optionC A -n> optionC B :=
  CofeMor (fmap f : optionC A → optionC B).
Instance optionC_map_ne A B n : Proper (dist n ==> dist n) (@optionC_map A B).
Proof. by intros f f' Hf []; constructor; apply Hf. Qed.

Program Definition optionCF (F : cFunctor) : cFunctor := {|
  cFunctor_car A B := optionC (cFunctor_car F A B);
  cFunctor_map A1 A2 B1 B2 fg := optionC_map (cFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_setoid_ext=>y; apply cFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_setoid_ext=>y; apply cFunctor_compose.
Qed.

Instance optionCF_contractive F :
  cFunctorContractive F → cFunctorContractive (optionCF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, cFunctor_contractive.
Qed.

Program Definition optionRF (F : rFunctor) : rFunctor := {|
  rFunctor_car A B := optionR (rFunctor_car F A B);
  rFunctor_map A1 A2 B1 B2 fg := optionC_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_setoid_ext=>y; apply rFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_setoid_ext=>y; apply rFunctor_compose.
Qed.

Instance optionRF_contractive F :
  rFunctorContractive F → rFunctorContractive (optionRF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_contractive.
Qed.
