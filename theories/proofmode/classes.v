From iris.bi Require Export bi.
Set Default Proof Using "Type".
Import bi.

Class FromAssumption {PROP : bi} (p : bool) (P Q : PROP) :=
  from_assumption : ⬕?p P ⊢ Q.
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

Class FromPure {PROP : bi} (P : PROP) (φ : Prop) :=
  from_pure : ⌜φ⌝ ⊢ P.
Arguments FromPure {_} _%I _%type_scope : simpl never.
Arguments from_pure {_} _%I _%type_scope {_}.
Hint Mode FromPure + ! - : typeclass_instances.

Class IntoPersistent {PROP : bi} (p : bool) (P Q : PROP) :=
  into_persistent : □?p P ⊢ □ Q.
Arguments IntoPersistent {_} _ _%I _%I : simpl never.
Arguments into_persistent {_} _ _%I _%I {_}.
Hint Mode IntoPersistent + + ! - : typeclass_instances.

Class FromPersistent {PROP : bi} (P Q : PROP) :=
  from_persistent : □ Q ⊢ P.
Arguments FromPersistent {_} _%I _%I : simpl never.
Arguments from_persistent {_} _%I _%I {_}.
Hint Mode FromPersistent + ! - : typeclass_instances.

Class FromBare {PROP : bi} (P Q : PROP) :=
  from_bare : ■ Q ⊢ P.
Arguments FromBare {_} _%I _%type_scope : simpl never.
Arguments from_bare {_} _%I _%type_scope {_}.
Hint Mode FromBare + ! - : typeclass_instances.
Hint Mode FromBare + - ! : typeclass_instances.

Class IntoInternalEq {PROP : bi} {A : ofeT} (P : PROP) (x y : A) :=
  into_internal_eq : P ⊢ x ≡ y.
Arguments IntoInternalEq {_ _} _%I _%type_scope _%type_scope : simpl never.
Arguments into_internal_eq {_ _} _%I _%type_scope _%type_scope {_}.
Hint Mode IntoInternalEq + - ! - - : typeclass_instances.

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
  into_wand : ⬕?p R ⊢ ⬕?q P -∗ Q.
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
  into_and : ⬕?p P ⊢ ⬕?p (Q1 ∧ Q2).
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

Class ElimModal {PROP : bi} (P P' : PROP) (Q Q' : PROP) :=
  elim_modal : P ∗ (P' -∗ Q') ⊢ Q.
Arguments ElimModal {_} _%I _%I _%I _%I : simpl never.
Arguments elim_modal {_} _%I _%I _%I _%I {_}.
Hint Mode ElimModal + ! - ! - : typeclass_instances.
Hint Mode ElimModal + - ! - ! : typeclass_instances.

Lemma elim_modal_dummy {PROP : bi} (P Q : PROP) : ElimModal P P Q Q.
Proof. by rewrite /ElimModal wand_elim_r. Qed.

Class IsCons {A} (l : list A) (x : A) (k : list A) := is_cons : l = x :: k.
Class IsApp {A} (l k1 k2 : list A) := is_app : l = k1 ++ k2.
Global Hint Mode IsCons + ! - - : typeclass_instances.
Global Hint Mode IsApp + ! - - : typeclass_instances.

Instance is_cons_cons {A} (x : A) (l : list A) : IsCons (x :: l) x l.
Proof. done. Qed.
Instance is_app_app {A} (l1 l2 : list A) : IsApp (l1 ++ l2) l1 l2.
Proof. done. Qed.

Class Frame {PROP : bi} (p : bool) (R P Q : PROP) := frame : ⬕?p R ∗ Q ⊢ P.
Arguments Frame {_} _ _%I _%I _%I.
Arguments frame {_ _} _%I _%I _%I {_}.
Hint Mode Frame + + ! ! - : typeclass_instances.

Class MaybeFrame {PROP : bi} (p : bool) (R P Q : PROP) :=
  maybe_frame : ⬕?p R ∗ Q ⊢ P.
Arguments MaybeFrame {_} _ _%I _%I _%I.
Arguments maybe_frame {_} _%I _%I _%I {_}.
Hint Mode MaybeFrame + + ! ! - : typeclass_instances.

Instance maybe_frame_frame {PROP : bi} p (R P Q : PROP) :
  Frame p R P Q → MaybeFrame p R P Q.
Proof. done. Qed.
Instance maybe_frame_default_persistent {PROP : bi} (R P : PROP) :
  MaybeFrame true R P P | 100.
Proof. intros. rewrite /MaybeFrame /=. by rewrite sep_elim_r. Qed.
Instance maybe_frame_default {PROP : bi} (R P : PROP) :
  TCOr (Affine R) (Absorbing P) → MaybeFrame false R P P | 100.
Proof. intros. rewrite /MaybeFrame /=. apply: sep_elim_r. Qed.

(* The class [IntoLaterN] has only two instances:

- The default instance [IntoLaterN n P P], i.e. [▷^n P -∗ P]
- The instance [IntoLaterN' n P Q → IntoLaterN n P Q], where [IntoLaterN']
  is identical to [IntoLaterN], but computationally is supposed to make
  progress, i.e. its instances should actually strip a later.

The point of using the auxilary class [IntoLaterN'] is to ensure that the
default instance is not applied deeply in the term, which may cause in too many
definitions being unfolded (see issue #55).

For binary connectives we have the following instances:

<<
IntoLaterN' n P P'       IntoLaterN n Q Q'
------------------------------------------
     IntoLaterN' n (P /\ Q) (P' /\ Q')


      IntoLaterN' n Q Q'
-------------------------------
IntoLaterN n (P /\ Q) (P /\ Q')
>>
*)
Class IntoLaterN {PROP : sbi} (n : nat) (P Q : PROP) := into_laterN : P ⊢ ▷^n Q.
Arguments IntoLaterN {_} _%nat_scope _%I _%I.
Arguments into_laterN {_} _%nat_scope _%I _%I {_}.
Hint Mode IntoLaterN + - - - : typeclass_instances.

Class IntoLaterN' {PROP : sbi} (n : nat) (P Q : PROP) :=
  into_laterN' :> IntoLaterN n P Q.
Arguments IntoLaterN' {_} _%nat_scope _%I _%I.
Hint Mode IntoLaterN' + - ! - : typeclass_instances.

Instance into_laterN_default {PROP : sbi} n (P : PROP) : IntoLaterN n P P | 1000.
Proof. apply laterN_intro. Qed.

Class FromLaterN {PROP : sbi} (n : nat) (P Q : PROP) := from_laterN : ▷^n Q ⊢ P.
Arguments FromLaterN {_} _%nat_scope _%I _%I.
Arguments from_laterN {_} _%nat_scope _%I _%I {_}.
Hint Mode FromLaterN + - ! - : typeclass_instances.

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
- [IntoLaterN] and [FromLaterN] used by [iNext]
- [IntoPersistent] used by [iPersistent]
*)
Instance into_pure_tc_opaque {PROP : bi} (P : PROP) φ :
  IntoPure P φ → IntoPure (tc_opaque P) φ := id.
Instance from_pure_tc_opaque {PROP : bi} (P : PROP) φ :
  FromPure P φ → FromPure (tc_opaque P) φ := id.
Instance from_laterN_tc_opaque {PROP : sbi} n (P Q : PROP) :
  FromLaterN n P Q → FromLaterN n (tc_opaque P) Q := id.
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
Instance elim_modal_tc_opaque {PROP : bi} (P P' Q Q' : PROP) :
  ElimModal P P' Q Q' → ElimModal (tc_opaque P) P' Q Q' := id.
