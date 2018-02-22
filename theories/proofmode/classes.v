From iris.bi Require Export bi.
From stdpp Require Import namespaces.
Set Default Proof Using "Type".
Import bi.

Class FromAssumption {PROP : bi} (p : bool) (P Q : PROP) :=
  from_assumption : □?p P ⊢ Q.
Arguments FromAssumption {_} _ _%I _%I : simpl never.
Arguments from_assumption {_} _ _%I _%I {_}.
(* No need to restrict Hint Mode, we have a default instance that will always
be used in case of evars *)
Hint Mode FromAssumption + + - - : typeclass_instances.

Class IntoPure {PROP : bi} (P : PROP) (φ : Prop) :=
  into_pure : P ⊢ ⌜φ⌝.
Arguments IntoPure {_} _%I _%type_scope : simpl never.
Arguments into_pure {_} _%I _%type_scope {_}.
Hint Mode IntoPure + ! - : typeclass_instances.

(* [IntoPureT] is a variant of [IntoPure] with the argument in [Type] to avoid
some shortcoming of unification in Coq's type class search. An example where we
use this workaround is to repair the following instance:

  Global Instance into_exist_and_pure P Q (φ : Prop) :
    IntoPure P φ → IntoExist (P ∧ Q) (λ _ : φ, Q).

Coq is unable to use this instance: [class_apply] -- which is used by type class
search -- fails with the error that it cannot unify [Prop] and [Type]. This is
probably caused because [class_apply] uses an ancient unification algorith. The
[refine] tactic -- which uses a better unification algorithm -- succeeds to
apply the above instance.

Since we do not want to define [Hint Extern] declarations using [refine] for
any instance like [into_exist_and_pure], we factor this out in the class
[IntoPureT]. This way, we only have to declare a [Hint Extern] using [refine]
once, and use [IntoPureT] in any instance like [into_exist_and_pure].

TODO: Report this as a Coq bug, or wait for https://github.com/coq/coq/pull/991
to be finished and merged someday. *)
Class IntoPureT {PROP : bi} (P : PROP) (φ : Type) :=
  into_pureT : ∃ ψ : Prop, φ = ψ ∧ IntoPure P ψ.
Lemma into_pureT_hint {PROP : bi} (P : PROP) (φ : Prop) : IntoPure P φ → IntoPureT P φ.
Proof. by exists φ. Qed.
Hint Extern 0 (IntoPureT _ _) =>
  notypeclasses refine (into_pureT_hint _ _ _) : typeclass_instances.

(** [FromPure] is used when introducing a pure assertion. It is used
    by iPure, the "[%]" specialization pattern, and the [with "[%]"]
    pattern when using [iAssert].

    The [a] Boolean asserts whether we introduce the pure assertion in
    an affine way or in an absorbing way. When [FromPure true P φ] is
    derived, then [FromPure false P φ] can always be derived too. We
    use [true] for specialization patterns and [false] for the
    [iPureIntro] tactic.

    This Boolean is not needed for [IntoPure], because in the case of
    [IntoPure], we can have the same behavior by asking that [P] be
    [Affine]. *)
Class FromPure {PROP : bi} (a : bool) (P : PROP) (φ : Prop) :=
  from_pure : bi_affinely_if a ⌜φ⌝ ⊢ P.
Arguments FromPure {_} _ _%I _%type_scope : simpl never.
Arguments from_pure {_} _ _%I _%type_scope {_}.
Hint Mode FromPure + + ! - : typeclass_instances.

Class FromPureT {PROP : bi} (a : bool) (P : PROP) (φ : Type) :=
  from_pureT : ∃ ψ : Prop, φ = ψ ∧ FromPure a P ψ.
Lemma from_pureT_hint {PROP : bi} (a : bool) (P : PROP) (φ : Prop) :
  FromPure a P φ → FromPureT a P φ.
Proof. by exists φ. Qed.
Hint Extern 0 (FromPureT _ _ _) =>
  notypeclasses refine (from_pureT_hint _ _ _ _) : typeclass_instances.

Class IntoInternalEq {PROP : sbi} {A : ofeT} (P : PROP) (x y : A) :=
  into_internal_eq : P ⊢ x ≡ y.
Arguments IntoInternalEq {_ _} _%I _%type_scope _%type_scope : simpl never.
Arguments into_internal_eq {_ _} _%I _%type_scope _%type_scope {_}.
Hint Mode IntoInternalEq + - ! - - : typeclass_instances.

Class IntoPersistent {PROP : bi} (p : bool) (P Q : PROP) :=
  into_persistent : bi_persistently_if p P ⊢ bi_persistently Q.
Arguments IntoPersistent {_} _ _%I _%I : simpl never.
Arguments into_persistent {_} _ _%I _%I {_}.
Hint Mode IntoPersistent + + ! - : typeclass_instances.

(* The `iAlways` tactic is not tied to `persistently` and `affinely`, but can be
instantiated with a variety of comonadic (always-style) modalities.

In order to plug in an always-style modality, one has to decide for both the
persistent and spatial what action should be performed upon introducing the
modality:

- Introduction is only allowed when the context is empty.
- Introduction is only allowed when all hypotheses satisfy some predicate
  `C : PROP → Prop` (where `C` should be a type class).
- Introduction will transform each hypotheses using a type class
  `C : PROP → PROP → Prop`, where the first parameter is the input and the
  second parameter is the output. Hypotheses that cannot be transformed (i.e.
  for which no instance of `C` can be found) will be cleared.
- Introduction will clear the context.
- Introduction will keep the context as-if.

Formally, these actions correspond to the following inductive type: *)

Inductive always_intro_spec (PROP : bi) :=
  | AIEnvIsEmpty
  | AIEnvForall (C : PROP → Prop)
  | AIEnvTransform (C : PROP → PROP → Prop)
  | AIEnvClear
  | AIEnvId.
Arguments AIEnvIsEmpty {_}.
Arguments AIEnvForall {_} _.
Arguments AIEnvTransform {_} _.
Arguments AIEnvClear {_}.
Arguments AIEnvId {_}.

Notation AIEnvFilter C := (AIEnvTransform (TCDiag C)).

(* An always-style modality is then a record packing together the modality with
the laws it should satisfy to justify the given actions for both contexts: *)
Record always_modality_mixin {PROP : bi} (M : PROP → PROP)
    (pspec sspec : always_intro_spec PROP) := {
  always_modality_mixin_persistent :
    match pspec with
    | AIEnvIsEmpty => True
    | AIEnvForall C => ∀ P, C P → □ P ⊢ M (□ P)
    | AIEnvTransform C => ∀ P Q, C P Q → □ P ⊢ M (□ Q)
    | AIEnvClear => True
    | AIEnvId => ∀ P, □ P ⊢ M (□ P)
    end;
  always_modality_mixin_spatial :
    match sspec with
    | AIEnvIsEmpty => True
    | AIEnvForall C => ∀ P, C P → P ⊢ M P
    | AIEnvTransform C => (∀ P Q, C P Q → P ⊢ M Q)
    | AIEnvClear => ∀ P, Absorbing (M P)
    | AIEnvId => ∀ P, P ⊢ M P
    end;
  always_modality_mixin_emp : emp ⊢ M emp;
  always_modality_mixin_mono P Q : (P ⊢ Q) → M P ⊢ M Q;
  always_modality_mixin_and P Q : M P ∧ M Q ⊢ M (P ∧ Q);
  always_modality_mixin_sep P Q : M P ∗ M Q ⊢ M (P ∗ Q)
}.

Record always_modality (PROP : bi) := AlwaysModality {
  always_modality_car :> PROP → PROP;
  always_modality_persistent_spec : always_intro_spec PROP;
  always_modality_spatial_spec : always_intro_spec PROP;
  always_modality_mixin_of : always_modality_mixin
    always_modality_car
    always_modality_persistent_spec always_modality_spatial_spec
}.
Arguments AlwaysModality {_} _ {_ _} _.
Arguments always_modality_persistent_spec {_} _.
Arguments always_modality_spatial_spec {_} _.

Section always_modality.
  Context {PROP} (M : always_modality PROP).

  Lemma always_modality_persistent_forall C P :
    always_modality_persistent_spec M = AIEnvForall C → C P → □ P ⊢ M (□ P).
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma always_modality_persistent_transform C P Q :
    always_modality_persistent_spec M = AIEnvTransform C → C P Q → □ P ⊢ M (□ Q).
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma always_modality_persistent_id P :
    always_modality_persistent_spec M = AIEnvId → □ P ⊢ M (□ P).
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma always_modality_spatial_forall C P :
    always_modality_spatial_spec M = AIEnvForall C → C P → P ⊢ M P.
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma always_modality_spatial_transform C P Q :
    always_modality_spatial_spec M = AIEnvTransform C → C P Q → P ⊢ M Q.
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma always_modality_spatial_clear P :
    always_modality_spatial_spec M = AIEnvClear → Absorbing (M P).
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma always_modality_spatial_id P :
    always_modality_spatial_spec M = AIEnvId → P ⊢ M P.
  Proof. destruct M as [??? []]; naive_solver. Qed.

  Lemma always_modality_emp : emp ⊢ M emp.
  Proof. eapply always_modality_mixin_emp, always_modality_mixin_of. Qed.
  Lemma always_modality_mono P Q : (P ⊢ Q) → M P ⊢ M Q.
  Proof. eapply always_modality_mixin_mono, always_modality_mixin_of. Qed.
  Lemma always_modality_and P Q : M P ∧ M Q ⊢ M (P ∧ Q).
  Proof. eapply always_modality_mixin_and, always_modality_mixin_of. Qed.
  Lemma always_modality_sep P Q : M P ∗ M Q ⊢ M (P ∗ Q).
  Proof. eapply always_modality_mixin_sep, always_modality_mixin_of. Qed.
  Global Instance always_modality_mono' : Proper ((⊢) ==> (⊢)) M.
  Proof. intros P Q. apply always_modality_mono. Qed.
  Global Instance always_modality_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) M.
  Proof. intros P Q. apply always_modality_mono. Qed.
  Global Instance always_modality_proper : Proper ((≡) ==> (≡)) M.
  Proof. intros P Q. rewrite !equiv_spec=> -[??]; eauto using always_modality_mono. Qed.

  Lemma always_modality_persistent_forall_big_and C Ps :
    always_modality_persistent_spec M = AIEnvForall C →
    Forall C Ps → □ [∧] Ps ⊢ M (□ [∧] Ps).
  Proof.
    induction 2 as [|P Ps ? _ IH]; simpl.
    - by rewrite persistently_pure affinely_True_emp affinely_emp -always_modality_emp.
    - rewrite affinely_persistently_and -always_modality_and -IH.
      by rewrite {1}(always_modality_persistent_forall _ P).
  Qed.
  Lemma always_modality_spatial_forall_big_sep C Ps :
    always_modality_spatial_spec M = AIEnvForall C →
    Forall C Ps → [∗] Ps ⊢ M ([∗] Ps).
  Proof.
    induction 2 as [|P Ps ? _ IH]; simpl.
    - by rewrite -always_modality_emp.
    - by rewrite -always_modality_sep -IH {1}(always_modality_spatial_forall _ P).
  Qed.
End always_modality.

Class FromAlways {PROP : bi} (M : always_modality PROP) (P Q : PROP) :=
  from_always : M Q ⊢ P.
Arguments FromAlways {_} _ _%I _%I : simpl never.
Arguments from_always {_} _ _%I _%I {_}.
Hint Mode FromAlways + - ! - : typeclass_instances.

Class FromAffinely {PROP : bi} (P Q : PROP) :=
  from_affinely : bi_affinely Q ⊢ P.
Arguments FromAffinely {_} _%I _%type_scope : simpl never.
Arguments from_affinely {_} _%I _%type_scope {_}.
Hint Mode FromAffinely + ! - : typeclass_instances.
Hint Mode FromAffinely + - ! : typeclass_instances.

Class IntoAbsorbingly {PROP : bi} (P Q : PROP) :=
  into_absorbingly : P ⊢ bi_absorbingly Q.
Arguments IntoAbsorbingly {_} _%I _%I.
Arguments into_absorbingly {_} _%I _%I {_}.
Hint Mode IntoAbsorbingly + ! -  : typeclass_instances.
Hint Mode IntoAbsorbingly + - ! : typeclass_instances.

(*
Converting an assumption [R] into a wand [P -∗ Q] is done in three stages:

- Strip modalities and universal quantifiers of [R] until an arrow or a wand
  has been obtained.
- Balance modalities in the arguments [P] and [Q] to match the goal (which used
  for [iApply]) or the premise (when used with [iSpecialize] and a specific
  hypothesis).
- Instantiate the premise of the wand or implication.
*)

Class IntoWand {PROP : bi} (p q : bool) (R P Q : PROP) :=
  into_wand : □?p R ⊢ □?q P -∗ Q.
Arguments IntoWand {_} _ _ _%I _%I _%I : simpl never.
Arguments into_wand {_} _ _ _%I _%I _%I {_}.
Hint Mode IntoWand + + + ! - - : typeclass_instances.

Class IntoWand' {PROP : bi} (p q : bool) (R P Q : PROP) :=
  into_wand' : IntoWand p q R P Q.
Arguments IntoWand' {_} _ _ _%I _%I _%I : simpl never.
Hint Mode IntoWand' + + + ! ! - : typeclass_instances.
Hint Mode IntoWand' + + + ! - ! : typeclass_instances.

Instance into_wand_wand' {PROP : bi} p q (P Q P' Q' : PROP) :
  IntoWand' p q (P -∗ Q) P' Q' → IntoWand p q (P -∗ Q) P' Q' | 100.
Proof. done. Qed.
Instance into_wand_impl' {PROP : bi} p q (P Q P' Q' : PROP) :
  IntoWand' p q (P → Q) P' Q' → IntoWand p q (P → Q) P' Q' | 100.
Proof. done. Qed.

Class FromWand {PROP : bi} (P Q1 Q2 : PROP) := from_wand : (Q1 -∗ Q2) ⊢ P.
Arguments FromWand {_} _%I _%I _%I : simpl never.
Arguments from_wand {_} _%I _%I _%I {_}.
Hint Mode FromWand + ! - - : typeclass_instances.

Class FromImpl {PROP : bi} (P Q1 Q2 : PROP) := from_impl : (Q1 → Q2) ⊢ P.
Arguments FromImpl {_} _%I _%I _%I : simpl never.
Arguments from_impl {_} _%I _%I _%I {_}.
Hint Mode FromImpl + ! - - : typeclass_instances.

Class FromSep {PROP : bi} (P Q1 Q2 : PROP) := from_sep : Q1 ∗ Q2 ⊢ P.
Arguments FromSep {_} _%I _%I _%I : simpl never.
Arguments from_sep {_} _%I _%I _%I {_}.
Hint Mode FromSep + ! - - : typeclass_instances.
Hint Mode FromSep + - ! ! : typeclass_instances. (* For iCombine *)

Class FromAnd {PROP : bi} (P Q1 Q2 : PROP) := from_and : Q1 ∧ Q2 ⊢ P.
Arguments FromAnd {_} _%I _%I _%I : simpl never.
Arguments from_and {_} _%I _%I _%I {_}.
Hint Mode FromAnd + ! - - : typeclass_instances.
Hint Mode FromAnd + - ! ! : typeclass_instances. (* For iCombine *)

Class IntoAnd {PROP : bi} (p : bool) (P Q1 Q2 : PROP) :=
  into_and : □?p P ⊢ □?p (Q1 ∧ Q2).
Arguments IntoAnd {_} _ _%I _%I _%I : simpl never.
Arguments into_and {_} _ _%I _%I _%I {_}.
Hint Mode IntoAnd + + ! - - : typeclass_instances.

Class IntoSep {PROP : bi} (P Q1 Q2 : PROP) :=
  into_sep : P ⊢ Q1 ∗ Q2.
Arguments IntoSep {_} _%I _%I _%I : simpl never.
Arguments into_sep {_} _%I _%I _%I {_}.
Hint Mode IntoSep + ! - - : typeclass_instances.

Class FromOr {PROP : bi} (P Q1 Q2 : PROP) := from_or : Q1 ∨ Q2 ⊢ P.
Arguments FromOr {_} _%I _%I _%I : simpl never.
Arguments from_or {_} _%I _%I _%I {_}.
Hint Mode FromOr + ! - - : typeclass_instances.

Class IntoOr {PROP : bi} (P Q1 Q2 : PROP) := into_or : P ⊢ Q1 ∨ Q2.
Arguments IntoOr {_} _%I _%I _%I : simpl never.
Arguments into_or {_} _%I _%I _%I {_}.
Hint Mode IntoOr + ! - - : typeclass_instances.

Class FromExist {PROP : bi} {A} (P : PROP) (Φ : A → PROP) :=
  from_exist : (∃ x, Φ x) ⊢ P.
Arguments FromExist {_ _} _%I _%I : simpl never.
Arguments from_exist {_ _} _%I _%I {_}.
Hint Mode FromExist + - ! - : typeclass_instances.

Class IntoExist {PROP : bi} {A} (P : PROP) (Φ : A → PROP) :=
  into_exist : P ⊢ ∃ x, Φ x.
Arguments IntoExist {_ _} _%I _%I : simpl never.
Arguments into_exist {_ _} _%I _%I {_}.
Hint Mode IntoExist + - ! - : typeclass_instances.

Class IntoForall {PROP : bi} {A} (P : PROP) (Φ : A → PROP) :=
  into_forall : P ⊢ ∀ x, Φ x.
Arguments IntoForall {_ _} _%I _%I : simpl never.
Arguments into_forall {_ _} _%I _%I {_}.
Hint Mode IntoForall + - ! - : typeclass_instances.

Class FromForall {PROP : bi} {A} (P : PROP) (Φ : A → PROP) :=
  from_forall : (∀ x, Φ x) ⊢ P.
Arguments from_forall {_ _} _ _ {_}.
Hint Mode FromForall + - ! - : typeclass_instances.

Class IsExcept0 {PROP : sbi} (Q : PROP) := is_except_0 : ◇ Q ⊢ Q.
Arguments IsExcept0 {_} _%I : simpl never.
Arguments is_except_0 {_} _%I {_}.
Hint Mode IsExcept0 + ! : typeclass_instances.

Class FromModal {PROP : bi} (P Q : PROP) := from_modal : Q ⊢ P.
Arguments FromModal {_} _%I _%I : simpl never.
Arguments from_modal {_} _%I _%I {_}.
Hint Mode FromModal + ! - : typeclass_instances.

Class ElimModal {PROP : bi} (φ : Prop) (P P' : PROP) (Q Q' : PROP) :=
  elim_modal : φ → P ∗ (P' -∗ Q') ⊢ Q.
Arguments ElimModal {_} _ _%I _%I _%I _%I : simpl never.
Arguments elim_modal {_} _ _%I _%I _%I _%I {_}.
Hint Mode ElimModal + - ! - ! - : typeclass_instances.

(* Used by the specialization pattern [ > ] in [iSpecialize] and [iAssert] to
add a modality to the goal corresponding to a premise/asserted proposition. *)
Class AddModal {PROP : bi} (P P' : PROP) (Q : PROP) :=
  add_modal : P ∗ (P' -∗ Q) ⊢ Q.
Arguments AddModal {_} _%I _%I _%I : simpl never.
Arguments add_modal {_} _%I _%I _%I {_}.
Hint Mode AddModal + - ! ! : typeclass_instances.

Lemma add_modal_id {PROP : bi} (P Q : PROP) : AddModal P P Q.
Proof. by rewrite /AddModal wand_elim_r. Qed.

Class IsCons {A} (l : list A) (x : A) (k : list A) := is_cons : l = x :: k.
Class IsApp {A} (l k1 k2 : list A) := is_app : l = k1 ++ k2.
Global Hint Mode IsCons + ! - - : typeclass_instances.
Global Hint Mode IsApp + ! - - : typeclass_instances.

Instance is_cons_cons {A} (x : A) (l : list A) : IsCons (x :: l) x l.
Proof. done. Qed.
Instance is_app_app {A} (l1 l2 : list A) : IsApp (l1 ++ l2) l1 l2.
Proof. done. Qed.

Class Frame {PROP : bi} (p : bool) (R P Q : PROP) := frame : □?p R ∗ Q ⊢ P.
Arguments Frame {_} _ _%I _%I _%I.
Arguments frame {_ _} _%I _%I _%I {_}.
Hint Mode Frame + + ! ! - : typeclass_instances.

(* The boolean [progress] indicates whether actual framing has been performed.
If it is [false], then the default instance [maybe_frame_default] below has been
used. *)
Class MaybeFrame {PROP : bi} (p : bool) (R P Q : PROP) (progress : bool) :=
  maybe_frame : □?p R ∗ Q ⊢ P.
Arguments MaybeFrame {_} _ _%I _%I _%I _.
Arguments maybe_frame {_} _ _%I _%I _%I _ {_}.
Hint Mode MaybeFrame + + ! ! - - : typeclass_instances.

Instance maybe_frame_frame {PROP : bi} p (R P Q : PROP) :
  Frame p R P Q → MaybeFrame p R P Q true.
Proof. done. Qed.

Instance maybe_frame_default_persistent {PROP : bi} (R P : PROP) :
  MaybeFrame true R P P false | 100.
Proof. intros. rewrite /MaybeFrame /=. by rewrite sep_elim_r. Qed.
Instance maybe_frame_default {PROP : bi} (R P : PROP) :
  TCOr (Affine R) (Absorbing P) → MaybeFrame false R P P false | 100.
Proof. intros. rewrite /MaybeFrame /=. apply: sep_elim_r. Qed.

(* For each of the [MakeXxxx] class, there is a [KnownMakeXxxx]
   variant, that only succeeds if the parameter(s) is not an evar. In
   the case the parameter(s) is an evar, then [MakeXxxx] will not
   instantiate it arbitrarily.

   The reason for this is that if given an evar, these typeclasses
   would typically try to instantiate this evar with some arbitrary
   logical constructs such as emp or True. Therefore, we use an Hint
   Mode to disable all the instances that would have this behavior. *)
Class MakeEmbed `{BiEmbedding PROP PROP'} (P : PROP) (Q : PROP') :=
  make_embed : ⎡P⎤ ⊣⊢ Q.
Arguments MakeEmbed {_ _ _ _} _%I _%I.
Hint Mode MakeEmbed + + + + - - : typeclass_instances.
Class KnownMakeEmbed `{BiEmbedding PROP PROP'} (P : PROP) (Q : PROP') :=
  go_make_embed :> MakeEmbed P Q.
Arguments KnownMakeEmbed {_ _ _ _} _%I _%I.
Hint Mode KnownMakeEmbed + + + + ! - : typeclass_instances.

Class MakeSep {PROP : bi} (P Q PQ : PROP) := make_sep : P ∗ Q ⊣⊢ PQ .
Arguments MakeSep {_} _%I _%I _%I.
Hint Mode MakeSep + - - - : typeclass_instances.
Class KnownLMakeSep {PROP : bi} (P Q PQ : PROP) := gol_make_sep :> MakeSep P Q PQ.
Arguments KnownLMakeSep {_} _%I _%I _%I.
Hint Mode KnownLMakeSep + ! - - : typeclass_instances.
Class KnownRMakeSep {PROP : bi} (P Q PQ : PROP) := gor_make_sep :> MakeSep P Q PQ.
Arguments KnownRMakeSep {_} _%I _%I _%I.
Hint Mode KnownRMakeSep + - ! - : typeclass_instances.

Class MakeAnd {PROP : bi} (P Q PQ : PROP) :=  make_and_l : P ∧ Q ⊣⊢ PQ.
Arguments MakeAnd {_} _%I _%I _%I.
Hint Mode MakeAnd + - - - : typeclass_instances.
Class KnownLMakeAnd {PROP : bi} (P Q PQ : PROP) := gol_make_and :> MakeAnd P Q PQ.
Arguments KnownLMakeAnd {_} _%I _%I _%I.
Hint Mode KnownLMakeAnd + ! - - : typeclass_instances.
Class KnownRMakeAnd {PROP : bi} (P Q PQ : PROP) := gor_make_and :> MakeAnd P Q PQ.
Arguments KnownRMakeAnd {_} _%I _%I _%I.
Hint Mode KnownRMakeAnd + - ! - : typeclass_instances.

Class MakeOr {PROP : bi} (P Q PQ : PROP) := make_or_l : P ∨ Q ⊣⊢ PQ.
Arguments MakeOr {_} _%I _%I _%I.
Hint Mode MakeOr + - - - : typeclass_instances.
Class KnownLMakeOr {PROP : bi} (P Q PQ : PROP) := gol_make_or :> MakeOr P Q PQ.
Arguments KnownLMakeOr {_} _%I _%I _%I.
Hint Mode KnownLMakeOr + ! - - : typeclass_instances.
Class KnownRMakeOr {PROP : bi} (P Q PQ : PROP) := gor_make_or :> MakeOr P Q PQ.
Arguments KnownRMakeOr {_} _%I _%I _%I.
Hint Mode KnownRMakeOr + - ! - : typeclass_instances.

Class MakeAffinely {PROP : bi} (P Q : PROP) :=
  make_affinely :> bi_affinely P ⊣⊢ Q.
Arguments MakeAffinely {_} _%I _%I.
Hint Mode MakeAffinely + - - : typeclass_instances.
Class KnownMakeAffinely {PROP : bi} (P Q : PROP) :=
  go_make_affinely : MakeAffinely P Q.
Arguments KnownMakeAffinely {_} _%I _%I.
Hint Mode KnownMakeAffinely + ! - : typeclass_instances.

Class MakeAbsorbingly {PROP : bi} (P Q : PROP) :=
  make_absorbingly : bi_absorbingly P ⊣⊢ Q.
Arguments MakeAbsorbingly {_} _%I _%I.
Hint Mode MakeAbsorbingly + - - : typeclass_instances.
Class KnownMakeAbsorbingly {PROP : bi} (P Q : PROP) :=
  go_make_absorbingly :> MakeAbsorbingly P Q.
Arguments KnownMakeAbsorbingly {_} _%I _%I.
Hint Mode KnownMakeAbsorbingly + ! - : typeclass_instances.

Class MakePersistently {PROP : bi} (P Q : PROP) :=
  make_persistently : bi_persistently P ⊣⊢ Q.
Arguments MakePersistently {_} _%I _%I.
Hint Mode MakePersistently + - - : typeclass_instances.
Class KnownMakePersistently {PROP : bi} (P Q : PROP) :=
  go_make_persistently :> MakePersistently P Q.
Arguments KnownMakePersistently {_} _%I _%I.
Hint Mode KnownMakePersistently + ! - : typeclass_instances.

Class MakeLaterN {PROP : sbi} (n : nat) (P lP : PROP) :=
  make_laterN : ▷^n P ⊣⊢ lP.
Arguments MakeLaterN {_} _%nat _%I _%I.
Hint Mode MakeLaterN + + - - : typeclass_instances.
Class KnownMakeLaterN {PROP : sbi} (n : nat) (P lP : PROP) :=
  go_make_laterN :> MakeLaterN n P lP.
Arguments KnownMakeLaterN {_} _%nat _%I _%I.
Hint Mode KnownMakeLaterN + + ! - : typeclass_instances.

Class MakeExcept0 {PROP : sbi} (P Q : PROP) :=
  make_except_0 : sbi_except_0 P ⊣⊢ Q.
Arguments MakeExcept0 {_} _%I _%I.
Hint Mode MakeExcept0 + - - : typeclass_instances.
Class KnownMakeExcept0 {PROP : sbi} (P Q : PROP) :=
  go_make_except_0 :> MakeExcept0 P Q.
Arguments KnownMakeExcept0 {_} _%I _%I.
Hint Mode KnownMakeExcept0 + ! - : typeclass_instances.

Class IntoExcept0 {PROP : sbi} (P Q : PROP) := into_except_0 : P ⊢ ◇ Q.
Arguments IntoExcept0 {_} _%I _%I : simpl never.
Arguments into_except_0 {_} _%I _%I {_}.
Hint Mode IntoExcept0 + ! - : typeclass_instances.
Hint Mode IntoExcept0 + - ! : typeclass_instances.

(* The class [MaybeIntoLaterN] has only two instances:

- The default instance [MaybeIntoLaterN n P P], i.e. [▷^n P -∗ P]
- The instance [IntoLaterN n P Q → MaybeIntoLaterN n P Q], where [IntoLaterN]
  is identical to [MaybeIntoLaterN], but is supposed to make progress, i.e. it
  should actually strip a later.

The point of using the auxilary class [IntoLaterN] is to ensure that the
default instance is not applied deeply inside a term, which may result in too
many definitions being unfolded (see issue #55).

For binary connectives we have the following instances:

<<
IntoLaterN n P P'       MaybeIntoLaterN n Q Q'
------------------------------------------
     IntoLaterN n (P /\ Q) (P' /\ Q')


      IntoLaterN n Q Q'
-------------------------------
IntoLaterN n (P /\ Q) (P /\ Q')
>>

The Boolean [only_head] indicates whether laters should only be stripped in
head position or also below other logical connectives. For [iNext] it should
strip laters below other logical connectives, but this should not happen while
framing, e.g. the following should succeed:

<<
Lemma test_iFrame_later_1 P Q : P ∗ ▷ Q -∗ ▷ (P ∗ ▷ Q).
Proof. iIntros "H". iFrame "H". Qed.
>>
*)
Class MaybeIntoLaterN {PROP : sbi} (only_head : bool) (n : nat) (P Q : PROP) :=
  maybe_into_laterN : P ⊢ ▷^n Q.
Arguments MaybeIntoLaterN {_} _ _%nat_scope _%I _%I.
Arguments maybe_into_laterN {_} _ _%nat_scope _%I _%I {_}.
Hint Mode MaybeIntoLaterN + + + - - : typeclass_instances.

Class IntoLaterN {PROP : sbi} (only_head : bool) (n : nat) (P Q : PROP) :=
  into_laterN :> MaybeIntoLaterN only_head n P Q.
Arguments IntoLaterN {_} _ _%nat_scope _%I _%I.
Hint Mode IntoLaterN + + + ! - : typeclass_instances.

Instance maybe_into_laterN_default {PROP : sbi} only_head n (P : PROP) :
  MaybeIntoLaterN only_head n P P | 1000.
Proof. apply laterN_intro. Qed.
(* In the case both parameters are evars and n=0, we have to stop the
   search and unify both evars immediately instead of looping using
   other instances. *)
Instance maybe_into_laterN_default_0 {PROP : sbi} only_head (P : PROP) :
  MaybeIntoLaterN only_head 0 P P | 0.
Proof. apply _. Qed.

Class FromLaterN {PROP : sbi} (n : nat) (P Q : PROP) := from_laterN : ▷^n Q ⊢ P.
Arguments FromLaterN {_} _%nat_scope _%I _%I.
Arguments from_laterN {_} _%nat_scope _%I _%I {_}.
Hint Mode FromLaterN + - ! - : typeclass_instances.

(* We use two type classes for [AsValid], in order to avoid loops in
   typeclass search. Indeed, the [as_valid_embed] instance would try
   to add an arbitrary number of embeddings. To avoid this, the
   [AsValid0] type class cannot handle embeddings, and therefore
   [as_valid_embed] only tries to add one embedding, and we never try
   to insert nested embeddings. This has the additional advantage of
   always trying [as_valid_embed] as a second option, so that this
   instance is never used when the BI is unknown.

   No Hint Modes are declared here. The appropriate one would be
   [Hint Mode - ! -], but the fact that Coq ignores primitive
   projections for hints modes would make this fail.*)
Class AsValid {PROP : bi} (φ : Prop) (P : PROP) := as_valid : φ ↔ P.
Arguments AsValid {_} _%type _%I.
Class AsValid0 {PROP : bi} (φ : Prop) (P : PROP) :=
  as_valid_here : AsValid φ P.
Arguments AsValid0 {_} _%type _%I.
Existing Instance as_valid_here | 0.

Lemma as_valid_1 (φ : Prop) {PROP : bi} (P : PROP) `{!AsValid φ P} : φ → P.
Proof. by apply as_valid. Qed.
Lemma as_valid_2 (φ : Prop) {PROP : bi} (P : PROP) `{!AsValid φ P} : P → φ.
Proof. by apply as_valid. Qed.

(* Input: [P]; Outputs: [N],
   Extracts the namespace associated with an invariant assertion. Used for [iInv]. *)
Class IntoInv {PROP : bi} (P: PROP) (N: namespace).
Arguments IntoInv {_} _%I _.
Hint Mode IntoInv + ! - : typeclass_instances.

(* Input: [Pinv]
   Arguments:
   - [Pinv] is an invariant assertion
   - [Pin] is an additional assertion needed for opening an invariant
   - [Pout] is the assertion obtained by opening the invariant
   - [Pclose] is the assertion which contains an update modality to close the invariant
   - [Q] is a goal on which iInv may be invoked
   - [Q'] is the transformed goal that must be proved after opening the invariant.

   There are similarities to the definition of ElimModal, however we
   want to be general enough to support uses in settings where there
   is not a clearly associated instance of ElimModal of the right form
   (e.g. to handle Iris 2.0 usage of iInv).
*)
Class ElimInv {PROP : bi} (φ : Prop) (Pinv Pin Pout Pclose Q Q' : PROP) :=
  elim_inv : φ → Pinv ∗ Pin ∗ (Pout ∗ Pclose -∗ Q') ⊢ Q.
Arguments ElimInv {_} _ _%I _%I _%I _%I _%I : simpl never.
Arguments elim_inv {_} _ _%I _%I _%I _%I _%I _%I _%I.
Hint Mode ElimInv + - ! - - - ! - : typeclass_instances.

(* We make sure that tactics that perform actions on *specific* hypotheses or
parts of the goal look through the [tc_opaque] connective, which is used to make
definitions opaque for type class search. For example, when using `iDestruct`,
an explicit hypothesis is affected, and as such, we should look through opaque
definitions. However, when using `iFrame` or `iNext`, arbitrary hypotheses or
parts of the goal are affected, and as such, type class opacity should be
respected.

This means that there are [tc_opaque] instances for all proofmode type classes
with the exception of:

- [FromAssumption] used by [iAssumption]
- [Frame] and [MaybeFrame] used by [iFrame]
- [MaybeIntoLaterN] and [FromLaterN] used by [iNext]
- [IntoPersistent] used by [iPersistent]
*)
Instance into_pure_tc_opaque {PROP : bi} (P : PROP) φ :
  IntoPure P φ → IntoPure (tc_opaque P) φ := id.
Instance from_pure_tc_opaque {PROP : bi} (a : bool) (P : PROP) φ :
  FromPure a P φ → FromPure a (tc_opaque P) φ := id.
Instance from_laterN_tc_opaque {PROP : sbi} n (P Q : PROP) :
  FromLaterN n P Q → FromLaterN n (tc_opaque P) Q := id.
Instance from_wand_tc_opaque {PROP : bi} (P Q1 Q2 : PROP) :
  FromWand P Q1 Q2 → FromWand (tc_opaque P) Q1 Q2 := id.
Instance into_wand_tc_opaque {PROP : bi} p q (R P Q : PROP) :
  IntoWand p q R P Q → IntoWand p q (tc_opaque R) P Q := id.
(* Higher precedence than [from_and_sep] so that [iCombine] does not loop. *)
Instance from_and_tc_opaque {PROP : bi} (P Q1 Q2 : PROP) :
  FromAnd P Q1 Q2 → FromAnd (tc_opaque P) Q1 Q2 | 102 := id.
Instance into_and_tc_opaque {PROP : bi} p (P Q1 Q2 : PROP) :
  IntoAnd p P Q1 Q2 → IntoAnd p (tc_opaque P) Q1 Q2 := id.
Instance from_or_tc_opaque {PROP : bi} (P Q1 Q2 : PROP) :
  FromOr P Q1 Q2 → FromOr (tc_opaque P) Q1 Q2 := id.
Instance into_or_tc_opaque {PROP : bi} (P Q1 Q2 : PROP) :
  IntoOr P Q1 Q2 → IntoOr (tc_opaque P) Q1 Q2 := id.
Instance from_exist_tc_opaque {PROP : bi} {A} (P : PROP) (Φ : A → PROP) :
  FromExist P Φ → FromExist (tc_opaque P) Φ := id.
Instance into_exist_tc_opaque {PROP : bi} {A} (P : PROP) (Φ : A → PROP) :
  IntoExist P Φ → IntoExist (tc_opaque P) Φ := id.
Instance into_forall_tc_opaque {PROP : bi} {A} (P : PROP) (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (tc_opaque P) Φ := id.
Instance from_modal_tc_opaque {PROP : bi} (P Q : PROP) :
  FromModal P Q → FromModal (tc_opaque P) Q := id.
Instance elim_modal_tc_opaque {PROP : bi} φ (P P' Q Q' : PROP) :
  ElimModal φ P P' Q Q' → ElimModal φ (tc_opaque P) P' Q Q' := id.
Instance into_inv_tc_opaque {PROP : bi} (P : PROP) N :
  IntoInv P N → IntoInv (tc_opaque P) N := id.
Instance elim_inv_tc_opaque {PROP : bi} φ (Pinv Pin Pout Pclose Q Q' : PROP) :
  ElimInv φ Pinv Pin Pout Pclose Q Q' →
  ElimInv φ (tc_opaque Pinv) Pin Pout Pclose Q Q' := id.
