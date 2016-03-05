(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects definitions and theorems on collections. Most
importantly, it implements some tactics to automatically solve goals involving
collections. *)
From prelude Require Export base tactics orders.

Instance collection_subseteq `{ElemOf A C} : SubsetEq C := λ X Y,
  ∀ x, x ∈ X → x ∈ Y.
Typeclasses Opaque collection_subseteq.

(** * Basic theorems *)
Section simple_collection.
  Context `{SimpleCollection A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.

  Lemma elem_of_empty x : x ∈ ∅ ↔ False.
  Proof. split. apply not_elem_of_empty. done. Qed.
  Lemma elem_of_union_l x X Y : x ∈ X → x ∈ X ∪ Y.
  Proof. intros. apply elem_of_union. auto. Qed.
  Lemma elem_of_union_r x X Y : x ∈ Y → x ∈ X ∪ Y.
  Proof. intros. apply elem_of_union. auto. Qed.
  Global Instance: EmptySpec C.
  Proof. firstorder auto. Qed.
  Global Instance: JoinSemiLattice C.
  Proof. firstorder auto. Qed.
  Global Instance: AntiSymm (≡) (@collection_subseteq A C _).
  Proof. done. Qed.
  Lemma elem_of_subseteq X Y : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y.
  Proof. done. Qed.
  Lemma elem_of_equiv X Y : X ≡ Y ↔ ∀ x, x ∈ X ↔ x ∈ Y.
  Proof. firstorder. Qed.
  Lemma elem_of_equiv_alt X Y :
    X ≡ Y ↔ (∀ x, x ∈ X → x ∈ Y) ∧ (∀ x, x ∈ Y → x ∈ X).
  Proof. firstorder. Qed.
  Lemma elem_of_equiv_empty X : X ≡ ∅ ↔ ∀ x, x ∉ X.
  Proof. firstorder. Qed.
  Lemma collection_positive_l X Y : X ∪ Y ≡ ∅ → X ≡ ∅.
  Proof.
    rewrite !elem_of_equiv_empty. setoid_rewrite elem_of_union. naive_solver.
  Qed.
  Lemma collection_positive_l_alt X Y : X ≢ ∅ → X ∪ Y ≢ ∅.
  Proof. eauto using collection_positive_l. Qed.
  Lemma elem_of_singleton_1 x y : x ∈ {[y]} → x = y.
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma elem_of_singleton_2 x y : x = y → x ∈ {[y]}.
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma elem_of_subseteq_singleton x X : x ∈ X ↔ {[ x ]} ⊆ X.
  Proof.
    split.
    - intros ??. rewrite elem_of_singleton. by intros ->.
    - intros Ex. by apply (Ex x), elem_of_singleton.
  Qed.
  Global Instance singleton_proper : Proper ((=) ==> (≡)) (singleton (B:=C)).
  Proof. by repeat intro; subst. Qed.
  Global Instance elem_of_proper :
    Proper ((=) ==> (≡) ==> iff) ((∈) : A → C → Prop) | 5.
  Proof. intros ???; subst. firstorder. Qed.
  Lemma elem_of_union_list Xs x : x ∈ ⋃ Xs ↔ ∃ X, X ∈ Xs ∧ x ∈ X.
  Proof.
    split.
    - induction Xs; simpl; intros HXs; [by apply elem_of_empty in HXs|].
      setoid_rewrite elem_of_cons. apply elem_of_union in HXs. naive_solver.
    - intros [X []]. induction 1; simpl; [by apply elem_of_union_l |].
      intros. apply elem_of_union_r; auto.
  Qed.
  Lemma non_empty_singleton x : ({[ x ]} : C) ≢ ∅.
  Proof. intros [E _]. by apply (elem_of_empty x), E, elem_of_singleton. Qed.
  Lemma not_elem_of_singleton x y : x ∉ {[ y ]} ↔ x ≠ y.
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma not_elem_of_union x X Y : x ∉ X ∪ Y ↔ x ∉ X ∧ x ∉ Y.
  Proof. rewrite elem_of_union. tauto. Qed.

  Section leibniz.
    Context `{!LeibnizEquiv C}.
    Lemma elem_of_equiv_L X Y : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y.
    Proof. unfold_leibniz. apply elem_of_equiv. Qed.
    Lemma elem_of_equiv_alt_L X Y :
      X = Y ↔ (∀ x, x ∈ X → x ∈ Y) ∧ (∀ x, x ∈ Y → x ∈ X).
    Proof. unfold_leibniz. apply elem_of_equiv_alt. Qed.
    Lemma elem_of_equiv_empty_L X : X = ∅ ↔ ∀ x, x ∉ X.
    Proof. unfold_leibniz. apply elem_of_equiv_empty. Qed.
    Lemma collection_positive_l_L X Y : X ∪ Y = ∅ → X = ∅.
    Proof. unfold_leibniz. apply collection_positive_l. Qed.
    Lemma collection_positive_l_alt_L X Y : X ≠ ∅ → X ∪ Y ≠ ∅.
    Proof. unfold_leibniz. apply collection_positive_l_alt. Qed.
    Lemma non_empty_singleton_L x : {[ x ]} ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_singleton. Qed.
  End leibniz.

  Section dec.
    Context `{∀ X Y : C, Decision (X ⊆ Y)}.
    Global Instance elem_of_dec_slow (x : A) (X : C) : Decision (x ∈ X) | 100.
    Proof.
      refine (cast_if (decide_rel (⊆) {[ x ]} X));
        by rewrite elem_of_subseteq_singleton.
    Defined.
  End dec.
End simple_collection.

(** * Tactics *)
(** The tactic [set_unfold] transforms all occurrences of [(∪)], [(∩)], [(∖)],
[(<$>)], [∅], [{[_]}], [(≡)], and [(⊆)] into logically equivalent propositions
involving just [∈]. For example, [A → x ∈ X ∪ ∅] becomes [A → x ∈ X ∨ False].

This transformation is implemented using type classes instead of [rewrite]ing
to ensure that we traverse each term at most once. *)
Class SetUnfold (P Q : Prop) := { set_unfold : P ↔ Q }.
Arguments set_unfold _ _ {_}.
Hint Mode SetUnfold + - : typeclass_instances.

Class SetUnfoldSimpl (P Q : Prop) := { set_unfold_simpl : SetUnfold P Q }.
Hint Extern 0 (SetUnfoldSimpl _ _) => csimpl; constructor : typeclass_instances.

Instance set_unfold_fallthrough P : SetUnfold P P | 1000. done. Qed.
Definition set_unfold_1 `{SetUnfold P Q} : P → Q := proj1 (set_unfold P Q).
Definition set_unfold_2 `{SetUnfold P Q} : Q → P := proj2 (set_unfold P Q).

Lemma set_unfold_impl P Q P' Q' :
  SetUnfold P P' → SetUnfold Q Q' → SetUnfold (P → Q) (P' → Q').
Proof. constructor. by rewrite (set_unfold P P'), (set_unfold Q Q'). Qed.
Lemma set_unfold_and P Q P' Q' :
  SetUnfold P P' → SetUnfold Q Q' → SetUnfold (P ∧ Q) (P' ∧ Q').
Proof. constructor. by rewrite (set_unfold P P'), (set_unfold Q Q'). Qed.
Lemma set_unfold_or P Q P' Q' :
  SetUnfold P P' → SetUnfold Q Q' → SetUnfold (P ∨ Q) (P' ∨ Q').
Proof. constructor. by rewrite (set_unfold P P'), (set_unfold Q Q'). Qed.
Lemma set_unfold_iff P Q P' Q' :
  SetUnfold P P' → SetUnfold Q Q' → SetUnfold (P ↔ Q) (P' ↔ Q').
Proof. constructor. by rewrite (set_unfold P P'), (set_unfold Q Q'). Qed.
Lemma set_unfold_not P P' : SetUnfold P P' → SetUnfold (¬P) (¬P').
Proof. constructor. by rewrite (set_unfold P P'). Qed.
Lemma set_unfold_forall {A} (P P' : A → Prop) :
  (∀ x, SetUnfold (P x) (P' x)) → SetUnfold (∀ x, P x) (∀ x, P' x).
Proof. constructor. naive_solver. Qed.
Lemma set_unfold_exist {A} (P P' : A → Prop) :
  (∀ x, SetUnfold (P x) (P' x)) → SetUnfold (∃ x, P x) (∃ x, P' x).
Proof. constructor. naive_solver. Qed.

(* Avoid too eager application of the above instances (and thus too eager
unfolding of type class transparent definitions). *)
Hint Extern 0 (SetUnfold (_ → _) _) =>
  class_apply set_unfold_impl : typeclass_instances.
Hint Extern 0 (SetUnfold (_ ∧ _) _) =>
  class_apply set_unfold_and : typeclass_instances.
Hint Extern 0 (SetUnfold (_ ∨ _) _) =>
  class_apply set_unfold_or : typeclass_instances.
Hint Extern 0 (SetUnfold (_ ↔ _) _) =>
  class_apply set_unfold_iff : typeclass_instances.
Hint Extern 0 (SetUnfold (¬ _) _) =>
  class_apply set_unfold_not : typeclass_instances.
Hint Extern 1 (SetUnfold (∀ _, _) _) =>
  class_apply set_unfold_forall : typeclass_instances.
Hint Extern 0 (SetUnfold (∃ _, _) _) =>
  class_apply set_unfold_exist : typeclass_instances.

Section set_unfold_simple.
  Context `{SimpleCollection A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.

  Global Instance set_unfold_empty x : SetUnfold (x ∈ ∅) False.
  Proof. constructor; apply elem_of_empty. Qed.
  Global Instance set_unfold_singleton x y : SetUnfold (x ∈ {[ y ]}) (x = y).
  Proof. constructor; apply elem_of_singleton. Qed.
  Global Instance set_unfold_union x X Y P Q :
    SetUnfold (x ∈ X) P → SetUnfold (x ∈ Y) Q → SetUnfold (x ∈ X ∪ Y) (P ∨ Q).
  Proof.
    intros ??; constructor.
    by rewrite elem_of_union, (set_unfold (x ∈ X) P), (set_unfold (x ∈ Y) Q).
  Qed.
  Global Instance set_unfold_equiv_same X : SetUnfold (X ≡ X) True | 1.
  Proof. done. Qed.
  Global Instance set_unfold_equiv_empty_l X (P : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → SetUnfold (∅ ≡ X) (∀ x, ¬P x) | 5.
  Proof.
    intros ?; constructor.
    rewrite (symmetry_iff equiv), elem_of_equiv_empty; naive_solver.
  Qed.
  Global Instance set_unfold_equiv_empty_r (P : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → SetUnfold (X ≡ ∅) (∀ x, ¬P x) | 5.
  Proof. constructor. rewrite elem_of_equiv_empty; naive_solver. Qed.
  Global Instance set_unfold_equiv (P Q : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → (∀ x, SetUnfold (x ∈ Y) (Q x)) →
    SetUnfold (X ≡ Y) (∀ x, P x ↔ Q x) | 10.
  Proof. constructor. rewrite elem_of_equiv; naive_solver. Qed.
  Global Instance set_unfold_subseteq (P Q : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → (∀ x, SetUnfold (x ∈ Y) (Q x)) →
    SetUnfold (X ⊆ Y) (∀ x, P x → Q x).
  Proof. constructor. rewrite elem_of_subseteq; naive_solver. Qed.
  Global Instance set_unfold_subset (P Q : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → (∀ x, SetUnfold (x ∈ Y) (Q x)) →
    SetUnfold (X ⊂ Y) ((∀ x, P x → Q x) ∧ ¬∀ x, P x ↔ Q x).
  Proof.
    constructor. rewrite subset_spec, elem_of_subseteq, elem_of_equiv.
    repeat f_equiv; naive_solver.
  Qed.

  Context `{!LeibnizEquiv C}.
  Global Instance set_unfold_equiv_same_L X : SetUnfold (X = X) True | 1.
  Proof. done. Qed.
  Global Instance set_unfold_equiv_empty_l_L X (P : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → SetUnfold (∅ = X) (∀ x, ¬P x) | 5.
  Proof.
    constructor. rewrite (symmetry_iff eq), elem_of_equiv_empty_L; naive_solver.
  Qed.
  Global Instance set_unfold_equiv_empty_r_L (P : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → SetUnfold (X = ∅) (∀ x, ¬P x) | 5.
  Proof. constructor. rewrite elem_of_equiv_empty_L; naive_solver. Qed.
  Global Instance set_unfold_equiv_L (P Q : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → (∀ x, SetUnfold (x ∈ Y) (Q x)) →
    SetUnfold (X = Y) (∀ x, P x ↔ Q x) | 10.
  Proof. constructor. rewrite elem_of_equiv_L; naive_solver. Qed.
End set_unfold_simple.

Section set_unfold.
  Context `{Collection A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.

  Global Instance set_unfold_intersection x X Y P Q :
    SetUnfold (x ∈ X) P → SetUnfold (x ∈ Y) Q → SetUnfold (x ∈ X ∩ Y) (P ∧ Q).
  Proof.
    intros ??; constructor. by rewrite elem_of_intersection,
      (set_unfold (x ∈ X) P), (set_unfold (x ∈ Y) Q).
  Qed.
  Global Instance set_unfold_difference x X Y P Q :
    SetUnfold (x ∈ X) P → SetUnfold (x ∈ Y) Q → SetUnfold (x ∈ X ∖ Y) (P ∧ ¬Q).
  Proof.
    intros ??; constructor. by rewrite elem_of_difference,
      (set_unfold (x ∈ X) P), (set_unfold (x ∈ Y) Q).
  Qed.
End set_unfold.

Section set_unfold_monad.
  Context `{CollectionMonad M} {A : Type}.
  Implicit Types x y : A.

  Global Instance set_unfold_ret x y : SetUnfold (x ∈ mret y) (x = y).
  Proof. constructor; apply elem_of_ret. Qed.
  Global Instance set_unfold_bind {B} (f : A → M B) X (P Q : A → Prop) :
    (∀ y, SetUnfold (y ∈ X) (P y)) → (∀ y, SetUnfold (x ∈ f y) (Q y)) →
    SetUnfold (x ∈ X ≫= f) (∃ y, Q y ∧ P y).
  Proof. constructor. rewrite elem_of_bind; naive_solver. Qed.
  Global Instance set_unfold_fmap {B} (f : A → B) X (P : A → Prop) :
    (∀ y, SetUnfold (y ∈ X) (P y)) →
    SetUnfold (x ∈ f <$> X) (∃ y, x = f y ∧ P y).
  Proof. constructor. rewrite elem_of_fmap; naive_solver. Qed.
  Global Instance set_unfold_join (X : M (M A)) (P : M A → Prop) :
    (∀ Y, SetUnfold (Y ∈ X) (P Y)) → SetUnfold (x ∈ mjoin X) (∃ Y, x ∈ Y ∧ P Y).
  Proof. constructor. rewrite elem_of_join; naive_solver. Qed.
End set_unfold_monad.

Ltac set_unfold :=
  let rec unfold_hyps :=
    try match goal with
    | H : _ |- _ =>
       apply set_unfold_1 in H; revert H;
       first [unfold_hyps; intros H | intros H; fail 1]
    end in
  apply set_unfold_2; unfold_hyps; csimpl in *.

(** Since [firstorder] fails or loops on very small goals generated by
[set_solver] already. We use the [naive_solver] tactic as a substitute.
This tactic either fails or proves the goal. *)
Tactic Notation "set_solver" "by" tactic3(tac) :=
  try fast_done;
  intros; setoid_subst;
  set_unfold;
  intros; setoid_subst;
  try match goal with |- _ ∈ _ => apply dec_stable end;
  naive_solver tac.
Tactic Notation "set_solver" "-" hyp_list(Hs) "by" tactic3(tac) :=
  clear Hs; set_solver by tac.
Tactic Notation "set_solver" "+" hyp_list(Hs) "by" tactic3(tac) :=
  clear -Hs; set_solver by tac.
Tactic Notation "set_solver" := set_solver by idtac.
Tactic Notation "set_solver" "-" hyp_list(Hs) := clear Hs; set_solver.
Tactic Notation "set_solver" "+" hyp_list(Hs) := clear -Hs; set_solver.

Hint Extern 1000 (_ ∉ _) => set_solver : set_solver.
Hint Extern 1000 (_ ∈ _) => set_solver : set_solver.
Hint Extern 1000 (_ ⊆ _) => set_solver : set_solver.

(** * Conversion of option and list *)
Definition of_option `{Singleton A C, Empty C} (mx : option A) : C :=
  match mx with None => ∅ | Some x => {[ x ]} end.
Fixpoint of_list `{Singleton A C, Empty C, Union C} (l : list A) : C :=
  match l with [] => ∅ | x :: l => {[ x ]} ∪ of_list l end.

Section of_option_list.
  Context `{SimpleCollection A C}.
  Lemma elem_of_of_option (x : A) mx: x ∈ of_option mx ↔ mx = Some x.
  Proof. destruct mx; set_solver. Qed.
  Lemma elem_of_of_list (x : A) l : x ∈ of_list l ↔ x ∈ l.
  Proof.
    split.
    - induction l; simpl; [by rewrite elem_of_empty|].
      rewrite elem_of_union,elem_of_singleton; intros [->|?]; constructor; auto.
    - induction 1; simpl; rewrite elem_of_union, elem_of_singleton; auto.
  Qed.
  Global Instance set_unfold_of_option (mx : option A) x :
    SetUnfold (x ∈ of_option mx) (mx = Some x).
  Proof. constructor; apply elem_of_of_option. Qed.
  Global Instance set_unfold_of_list (l : list A) x P :
    SetUnfold (x ∈ l) P → SetUnfold (x ∈ of_list l) P.
  Proof. constructor. by rewrite elem_of_of_list, (set_unfold (x ∈ l) P). Qed.
End of_option_list.

Section list_unfold.
  Context {A : Type}.
  Implicit Types x : A.
  Implicit Types l : list A.

  Global Instance set_unfold_nil x : SetUnfold (x ∈ []) False.
  Proof. constructor; apply elem_of_nil. Qed.
  Global Instance set_unfold_cons x y l P :
    SetUnfold (x ∈ l) P → SetUnfold (x ∈ y :: l) (x = y ∨ P).
  Proof. constructor. by rewrite elem_of_cons, (set_unfold (x ∈ l) P). Qed.
  Global Instance set_unfold_app x l k P Q :
    SetUnfold (x ∈ l) P → SetUnfold (x ∈ k) Q → SetUnfold (x ∈ l ++ k) (P ∨ Q).
  Proof.
    intros ??; constructor.
    by rewrite elem_of_app, (set_unfold (x ∈ l) P), (set_unfold (x ∈ k) Q).
  Qed.
  Global Instance set_unfold_included l k (P Q : A → Prop) :
    (∀ x, SetUnfold (x ∈ l) (P x)) → (∀ x, SetUnfold (x ∈ k) (Q x)) →
    SetUnfold (l `included` k) (∀ x, P x → Q x).
  Proof. by constructor; unfold included; set_unfold. Qed.
End list_unfold.

(** * Guard *)
Global Instance collection_guard `{CollectionMonad M} : MGuard M :=
  λ P dec A x, match dec with left H => x H | _ => ∅ end.

Section collection_monad_base.
  Context `{CollectionMonad M}.
  Lemma elem_of_guard `{Decision P} {A} (x : A) (X : M A) :
    x ∈ guard P; X ↔ P ∧ x ∈ X.
  Proof.
    unfold mguard, collection_guard; simpl; case_match;
      rewrite ?elem_of_empty; naive_solver.
  Qed.
  Lemma elem_of_guard_2 `{Decision P} {A} (x : A) (X : M A) :
    P → x ∈ X → x ∈ guard P; X.
  Proof. by rewrite elem_of_guard. Qed.
  Lemma guard_empty `{Decision P} {A} (X : M A) : guard P; X ≡ ∅ ↔ ¬P ∨ X ≡ ∅.
  Proof.
    rewrite !elem_of_equiv_empty; setoid_rewrite elem_of_guard.
    destruct (decide P); naive_solver.
  Qed.
  Global Instance set_unfold_guard `{Decision P} {A} (x : A) X Q :
    SetUnfold (x ∈ X) Q → SetUnfold (x ∈ guard P; X) (P ∧ Q).
  Proof. constructor. by rewrite elem_of_guard, (set_unfold (x ∈ X) Q). Qed.
  Lemma bind_empty {A B} (f : A → M B) X :
    X ≫= f ≡ ∅ ↔ X ≡ ∅ ∨ ∀ x, x ∈ X → f x ≡ ∅.
  Proof. set_solver. Qed.
End collection_monad_base.

(** * More theorems *)
Section collection.
  Context `{Collection A C}.
  Implicit Types X Y : C.

  Global Instance: Lattice C.
  Proof. split. apply _. firstorder auto. set_solver. Qed.
  Global Instance difference_proper :
     Proper ((≡) ==> (≡) ==> (≡)) (@difference C _).
  Proof.
    intros X1 X2 HX Y1 Y2 HY; apply elem_of_equiv; intros x.
    by rewrite !elem_of_difference, HX, HY.
  Qed.
  Lemma non_empty_inhabited x X : x ∈ X → X ≢ ∅.
  Proof. set_solver. Qed.
  Lemma intersection_singletons x : ({[x]} : C) ∩ {[x]} ≡ {[x]}.
  Proof. set_solver. Qed.
  Lemma difference_twice X Y : (X ∖ Y) ∖ Y ≡ X ∖ Y.
  Proof. set_solver. Qed.
  Lemma subseteq_empty_difference X Y : X ⊆ Y → X ∖ Y ≡ ∅.
  Proof. set_solver. Qed.
  Lemma difference_diag X : X ∖ X ≡ ∅.
  Proof. set_solver. Qed.
  Lemma difference_union_distr_l X Y Z : (X ∪ Y) ∖ Z ≡ X ∖ Z ∪ Y ∖ Z.
  Proof. set_solver. Qed.
  Lemma difference_union_distr_r X Y Z : Z ∖ (X ∪ Y) ≡ (Z ∖ X) ∩ (Z ∖ Y).
  Proof. set_solver. Qed.
  Lemma difference_intersection_distr_l X Y Z : (X ∩ Y) ∖ Z ≡ X ∖ Z ∩ Y ∖ Z.
  Proof. set_solver. Qed.
  Lemma disjoint_union_difference X Y : X ∩ Y ≡ ∅ → (X ∪ Y) ∖ X ≡ Y.
  Proof. set_solver. Qed.

  Section leibniz.
    Context `{!LeibnizEquiv C}.
    Lemma intersection_singletons_L x : {[x]} ∩ {[x]} = {[x]}.
    Proof. unfold_leibniz. apply intersection_singletons. Qed.
    Lemma difference_twice_L X Y : (X ∖ Y) ∖ Y = X ∖ Y.
    Proof. unfold_leibniz. apply difference_twice. Qed.
    Lemma subseteq_empty_difference_L X Y : X ⊆ Y → X ∖ Y = ∅.
    Proof. unfold_leibniz. apply subseteq_empty_difference. Qed.
    Lemma difference_diag_L X : X ∖ X = ∅.
    Proof. unfold_leibniz. apply difference_diag. Qed.
    Lemma difference_union_distr_l_L X Y Z : (X ∪ Y) ∖ Z = X ∖ Z ∪ Y ∖ Z.
    Proof. unfold_leibniz. apply difference_union_distr_l. Qed.
    Lemma difference_union_distr_r_L X Y Z : Z ∖ (X ∪ Y) = (Z ∖ X) ∩ (Z ∖ Y).
    Proof. unfold_leibniz. apply difference_union_distr_r. Qed.
    Lemma difference_intersection_distr_l_L X Y Z :
      (X ∩ Y) ∖ Z = X ∖ Z ∩ Y ∖ Z.
    Proof. unfold_leibniz. apply difference_intersection_distr_l. Qed.
    Lemma disjoint_union_difference_L X Y : X ∩ Y = ∅ → (X ∪ Y) ∖ X = Y.
    Proof. unfold_leibniz. apply disjoint_union_difference. Qed.
  End leibniz.

  Section dec.
    Context `{∀ (x : A) (X : C), Decision (x ∈ X)}.
    Lemma not_elem_of_intersection x X Y : x ∉ X ∩ Y ↔ x ∉ X ∨ x ∉ Y.
    Proof. rewrite elem_of_intersection. destruct (decide (x ∈ X)); tauto. Qed.
    Lemma not_elem_of_difference x X Y : x ∉ X ∖ Y ↔ x ∉ X ∨ x ∈ Y.
    Proof. rewrite elem_of_difference. destruct (decide (x ∈ Y)); tauto. Qed.
    Lemma union_difference X Y : X ⊆ Y → Y ≡ X ∪ Y ∖ X.
    Proof.
      split; intros x; rewrite !elem_of_union, elem_of_difference; [|intuition].
      destruct (decide (x ∈ X)); intuition.
    Qed.
    Lemma non_empty_difference X Y : X ⊂ Y → Y ∖ X ≢ ∅.
    Proof. intros [HXY1 HXY2] Hdiff. destruct HXY2. set_solver. Qed.
    Lemma empty_difference_subseteq X Y : X ∖ Y ≡ ∅ → X ⊆ Y.
    Proof. set_solver. Qed.
    Context `{!LeibnizEquiv C}.
    Lemma union_difference_L X Y : X ⊆ Y → Y = X ∪ Y ∖ X.
    Proof. unfold_leibniz. apply union_difference. Qed.
    Lemma non_empty_difference_L X Y : X ⊂ Y → Y ∖ X ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_difference. Qed.
    Lemma empty_difference_subseteq_L X Y : X ∖ Y = ∅ → X ⊆ Y.
    Proof. unfold_leibniz. apply empty_difference_subseteq. Qed.
  End dec.
End collection.

Section collection_ops.
  Context `{CollectionOps A C}.

  Lemma elem_of_intersection_with_list (f : A → A → option A) Xs Y x :
    x ∈ intersection_with_list f Y Xs ↔ ∃ xs y,
      Forall2 (∈) xs Xs ∧ y ∈ Y ∧ foldr (λ x, (≫= f x)) (Some y) xs = Some x.
  Proof.
    split.
    - revert x. induction Xs; simpl; intros x HXs; [eexists [], x; intuition|].
      rewrite elem_of_intersection_with in HXs; destruct HXs as (x1&x2&?&?&?).
      destruct (IHXs x2) as (xs & y & hy & ? & ?); trivial.
      eexists (x1 :: xs), y. intuition (simplify_option_eq; auto).
    - intros (xs & y & Hxs & ? & Hx). revert x Hx.
      induction Hxs; intros; simplify_option_eq; [done |].
      rewrite elem_of_intersection_with. naive_solver.
  Qed.

  Lemma intersection_with_list_ind (P Q : A → Prop) f Xs Y :
    (∀ y, y ∈ Y → P y) →
    Forall (λ X, ∀ x, x ∈ X → Q x) Xs →
    (∀ x y z, Q x → P y → f x y = Some z → P z) →
    ∀ x, x ∈ intersection_with_list f Y Xs → P x.
  Proof.
    intros HY HXs Hf. induction Xs; simplify_option_eq; [done |].
    intros x Hx. rewrite elem_of_intersection_with in Hx.
    decompose_Forall. destruct Hx as (? & ? & ? & ? & ?). eauto.
  Qed.
End collection_ops.

(** * Sets without duplicates up to an equivalence *)
Section NoDup.
  Context `{SimpleCollection A B} (R : relation A) `{!Equivalence R}.

  Definition elem_of_upto (x : A) (X : B) := ∃ y, y ∈ X ∧ R x y.
  Definition set_NoDup (X : B) := ∀ x y, x ∈ X → y ∈ X → R x y → x = y.

  Global Instance: Proper ((≡) ==> iff) (elem_of_upto x).
  Proof. intros ??? E. unfold elem_of_upto. by setoid_rewrite E. Qed.
  Global Instance: Proper (R ==> (≡) ==> iff) elem_of_upto.
  Proof.
    intros ?? E1 ?? E2. split; intros [z [??]]; exists z.
    - rewrite <-E1, <-E2; intuition.
    - rewrite E1, E2; intuition.
  Qed.
  Global Instance: Proper ((≡) ==> iff) set_NoDup.
  Proof. firstorder. Qed.

  Lemma elem_of_upto_elem_of x X : x ∈ X → elem_of_upto x X.
  Proof. unfold elem_of_upto. set_solver. Qed.
  Lemma elem_of_upto_empty x : ¬elem_of_upto x ∅.
  Proof. unfold elem_of_upto. set_solver. Qed.
  Lemma elem_of_upto_singleton x y : elem_of_upto x {[ y ]} ↔ R x y.
  Proof. unfold elem_of_upto. set_solver. Qed.

  Lemma elem_of_upto_union X Y x :
    elem_of_upto x (X ∪ Y) ↔ elem_of_upto x X ∨ elem_of_upto x Y.
  Proof. unfold elem_of_upto. set_solver. Qed.
  Lemma not_elem_of_upto x X : ¬elem_of_upto x X → ∀ y, y ∈ X → ¬R x y.
  Proof. unfold elem_of_upto. set_solver. Qed.

  Lemma set_NoDup_empty: set_NoDup ∅.
  Proof. unfold set_NoDup. set_solver. Qed.
  Lemma set_NoDup_add x X :
    ¬elem_of_upto x X → set_NoDup X → set_NoDup ({[ x ]} ∪ X).
  Proof. unfold set_NoDup, elem_of_upto. set_solver. Qed.
  Lemma set_NoDup_inv_add x X :
    x ∉ X → set_NoDup ({[ x ]} ∪ X) → ¬elem_of_upto x X.
  Proof.
    intros Hin Hnodup [y [??]].
    rewrite (Hnodup x y) in Hin; set_solver.
  Qed.
  Lemma set_NoDup_inv_union_l X Y : set_NoDup (X ∪ Y) → set_NoDup X.
  Proof. unfold set_NoDup. set_solver. Qed.
  Lemma set_NoDup_inv_union_r X Y : set_NoDup (X ∪ Y) → set_NoDup Y.
  Proof. unfold set_NoDup. set_solver. Qed.
End NoDup.

(** * Quantifiers *)
Section quantifiers.
  Context `{SimpleCollection A B} (P : A → Prop).

  Definition set_Forall X := ∀ x, x ∈ X → P x.
  Definition set_Exists X := ∃ x, x ∈ X ∧ P x.

  Lemma set_Forall_empty : set_Forall ∅.
  Proof. unfold set_Forall. set_solver. Qed.
  Lemma set_Forall_singleton x : set_Forall {[ x ]} ↔ P x.
  Proof. unfold set_Forall. set_solver. Qed.
  Lemma set_Forall_union X Y : set_Forall X → set_Forall Y → set_Forall (X ∪ Y).
  Proof. unfold set_Forall. set_solver. Qed.
  Lemma set_Forall_union_inv_1 X Y : set_Forall (X ∪ Y) → set_Forall X.
  Proof. unfold set_Forall. set_solver. Qed.
  Lemma set_Forall_union_inv_2 X Y : set_Forall (X ∪ Y) → set_Forall Y.
  Proof. unfold set_Forall. set_solver. Qed.

  Lemma set_Exists_empty : ¬set_Exists ∅.
  Proof. unfold set_Exists. set_solver. Qed.
  Lemma set_Exists_singleton x : set_Exists {[ x ]} ↔ P x.
  Proof. unfold set_Exists. set_solver. Qed.
  Lemma set_Exists_union_1 X Y : set_Exists X → set_Exists (X ∪ Y).
  Proof. unfold set_Exists. set_solver. Qed.
  Lemma set_Exists_union_2 X Y : set_Exists Y → set_Exists (X ∪ Y).
  Proof. unfold set_Exists. set_solver. Qed.
  Lemma set_Exists_union_inv X Y :
    set_Exists (X ∪ Y) → set_Exists X ∨ set_Exists Y.
  Proof. unfold set_Exists. set_solver. Qed.
End quantifiers.

Section more_quantifiers.
  Context `{SimpleCollection A B}.

  Lemma set_Forall_weaken (P Q : A → Prop) (Hweaken : ∀ x, P x → Q x) X :
    set_Forall P X → set_Forall Q X.
  Proof. unfold set_Forall. naive_solver. Qed.
  Lemma set_Exists_weaken (P Q : A → Prop) (Hweaken : ∀ x, P x → Q x) X :
    set_Exists P X → set_Exists Q X.
  Proof. unfold set_Exists. naive_solver. Qed.
End more_quantifiers.

(** * Fresh elements *)
(** We collect some properties on the [fresh] operation. In particular we
generalize [fresh] to generate lists of fresh elements. *)
Fixpoint fresh_list `{Fresh A C, Union C, Singleton A C}
    (n : nat) (X : C) : list A :=
  match n with
  | 0 => []
  | S n => let x := fresh X in x :: fresh_list n ({[ x ]} ∪ X)
  end.
Inductive Forall_fresh `{ElemOf A C} (X : C) : list A → Prop :=
  | Forall_fresh_nil : Forall_fresh X []
  | Forall_fresh_cons x xs :
     x ∉ xs → x ∉ X → Forall_fresh X xs → Forall_fresh X (x :: xs).

Section fresh.
  Context `{FreshSpec A C}.
  Implicit Types X Y : C.

  Global Instance fresh_proper: Proper ((≡) ==> (=)) (fresh (C:=C)).
  Proof. intros ???. by apply fresh_proper_alt, elem_of_equiv. Qed.
  Global Instance fresh_list_proper:
    Proper ((=) ==> (≡) ==> (=)) (fresh_list (C:=C)).
  Proof.
    intros ? n ->. induction n as [|n IH]; intros ?? E; f_equal/=; [by rewrite E|].
    apply IH. by rewrite E.
  Qed.

  Lemma Forall_fresh_NoDup X xs : Forall_fresh X xs → NoDup xs.
  Proof. induction 1; by constructor. Qed.
  Lemma Forall_fresh_elem_of X xs x : Forall_fresh X xs → x ∈ xs → x ∉ X.
  Proof.
    intros HX; revert x; rewrite <-Forall_forall.
    by induction HX; constructor.
  Qed.
  Lemma Forall_fresh_alt X xs :
    Forall_fresh X xs ↔ NoDup xs ∧ ∀ x, x ∈ xs → x ∉ X.
  Proof.
    split; eauto using Forall_fresh_NoDup, Forall_fresh_elem_of.
    rewrite <-Forall_forall.
    intros [Hxs Hxs']. induction Hxs; decompose_Forall_hyps; constructor; auto.
  Qed.
  Lemma Forall_fresh_subseteq X Y xs :
    Forall_fresh X xs → Y ⊆ X → Forall_fresh Y xs.
  Proof. rewrite !Forall_fresh_alt; set_solver. Qed.

  Lemma fresh_list_length n X : length (fresh_list n X) = n.
  Proof. revert X. induction n; simpl; auto. Qed.
  Lemma fresh_list_is_fresh n X x : x ∈ fresh_list n X → x ∉ X.
  Proof.
    revert X. induction n as [|n IH]; intros X; simpl;[by rewrite elem_of_nil|].
    rewrite elem_of_cons; intros [->| Hin]; [apply is_fresh|].
    apply IH in Hin; set_solver.
  Qed.
  Lemma NoDup_fresh_list n X : NoDup (fresh_list n X).
  Proof.
    revert X. induction n; simpl; constructor; auto.
    intros Hin; apply fresh_list_is_fresh in Hin; set_solver.
  Qed.
  Lemma Forall_fresh_list X n : Forall_fresh X (fresh_list n X).
  Proof.
    rewrite Forall_fresh_alt; eauto using NoDup_fresh_list, fresh_list_is_fresh.
  Qed.
End fresh.

(** * Properties of implementations of collections that form a monad *)
Section collection_monad.
  Context `{CollectionMonad M}.

  Global Instance collection_fmap_mono {A B} :
    Proper (pointwise_relation _ (=) ==> (⊆) ==> (⊆)) (@fmap M _ A B).
  Proof. intros f g ? X Y ?; set_solver by eauto. Qed.
  Global Instance collection_fmap_proper {A B} :
    Proper (pointwise_relation _ (=) ==> (≡) ==> (≡)) (@fmap M _ A B).
  Proof. intros f g ? X Y [??]; split; set_solver by eauto. Qed.
  Global Instance collection_bind_mono {A B} :
    Proper (((=) ==> (⊆)) ==> (⊆) ==> (⊆)) (@mbind M _ A B).
  Proof. unfold respectful; intros f g Hfg X Y ?; set_solver. Qed.
  Global Instance collection_bind_proper {A B} :
    Proper (((=) ==> (≡)) ==> (≡) ==> (≡)) (@mbind M _ A B).
  Proof. unfold respectful; intros f g Hfg X Y [??]; split; set_solver. Qed.
  Global Instance collection_join_mono {A} :
    Proper ((⊆) ==> (⊆)) (@mjoin M _ A).
  Proof. intros X Y ?; set_solver. Qed.
  Global Instance collection_join_proper {A} :
    Proper ((≡) ==> (≡)) (@mjoin M _ A).
  Proof. intros X Y [??]; split; set_solver. Qed.

  Lemma collection_bind_singleton {A B} (f : A → M B) x : {[ x ]} ≫= f ≡ f x.
  Proof. set_solver. Qed.
  Lemma collection_guard_True {A} `{Decision P} (X : M A) : P → guard P; X ≡ X.
  Proof. set_solver. Qed.
  Lemma collection_fmap_compose {A B C} (f : A → B) (g : B → C) (X : M A) :
    g ∘ f <$> X ≡ g <$> (f <$> X).
  Proof. set_solver. Qed.
  Lemma elem_of_fmap_1 {A B} (f : A → B) (X : M A) (y : B) :
    y ∈ f <$> X → ∃ x, y = f x ∧ x ∈ X.
  Proof. set_solver. Qed.
  Lemma elem_of_fmap_2 {A B} (f : A → B) (X : M A) (x : A) :
    x ∈ X → f x ∈ f <$> X.
  Proof. set_solver. Qed.
  Lemma elem_of_fmap_2_alt {A B} (f : A → B) (X : M A) (x : A) (y : B) :
    x ∈ X → y = f x → y ∈ f <$> X.
  Proof. set_solver. Qed.

  Lemma elem_of_mapM {A B} (f : A → M B) l k :
    l ∈ mapM f k ↔ Forall2 (λ x y, x ∈ f y) l k.
  Proof.
    split.
    - revert l. induction k; set_solver by eauto.
    - induction 1; set_solver.
  Qed.
  Lemma collection_mapM_length {A B} (f : A → M B) l k :
    l ∈ mapM f k → length l = length k.
  Proof. revert l; induction k; set_solver by eauto. Qed.
  Lemma elem_of_mapM_fmap {A B} (f : A → B) (g : B → M A) l k :
    Forall (λ x, ∀ y, y ∈ g x → f y = x) l → k ∈ mapM g l → fmap f k = l.
  Proof. intros Hl. revert k. induction Hl; set_solver. Qed.
  Lemma elem_of_mapM_Forall {A B} (f : A → M B) (P : B → Prop) l k :
    l ∈ mapM f k → Forall (λ x, ∀ y, y ∈ f x → P y) k → Forall P l.
  Proof. rewrite elem_of_mapM. apply Forall2_Forall_l. Qed.
  Lemma elem_of_mapM_Forall2_l {A B C} (f : A → M B) (P: B → C → Prop) l1 l2 k :
    l1 ∈ mapM f k → Forall2 (λ x y, ∀ z, z ∈ f x → P z y) k l2 →
    Forall2 P l1 l2.
  Proof.
    rewrite elem_of_mapM. intros Hl1. revert l2.
    induction Hl1; inversion_clear 1; constructor; auto.
  Qed.
End collection_monad.

(** Finite collections *)
Definition set_finite `{ElemOf A B} (X : B) := ∃ l : list A, ∀ x, x ∈ X → x ∈ l.

Section finite.
  Context `{SimpleCollection A B}.
  Global Instance set_finite_subseteq :
     Proper (flip (⊆) ==> impl) (@set_finite A B _).
  Proof. intros X Y HX [l Hl]; exists l; set_solver. Qed.
  Global Instance set_finite_proper : Proper ((≡) ==> iff) (@set_finite A B _).
  Proof. by intros X Y [??]; split; apply set_finite_subseteq. Qed.
  Lemma empty_finite : set_finite ∅.
  Proof. by exists []; intros ?; rewrite elem_of_empty. Qed.
  Lemma singleton_finite (x : A) : set_finite {[ x ]}.
  Proof. exists [x]; intros y ->%elem_of_singleton; left. Qed.
  Lemma union_finite X Y : set_finite X → set_finite Y → set_finite (X ∪ Y).
  Proof.
    intros [lX ?] [lY ?]; exists (lX ++ lY); intros x.
    rewrite elem_of_union, elem_of_app; naive_solver.
  Qed.
  Lemma union_finite_inv_l X Y : set_finite (X ∪ Y) → set_finite X.
  Proof. intros [l ?]; exists l; set_solver. Qed.
  Lemma union_finite_inv_r X Y : set_finite (X ∪ Y) → set_finite Y.
  Proof. intros [l ?]; exists l; set_solver. Qed.
End finite.

Section more_finite.
  Context `{Collection A B}.
  Lemma intersection_finite_l X Y : set_finite X → set_finite (X ∩ Y).
  Proof. intros [l ?]; exists l; intros x [??]%elem_of_intersection; auto. Qed.
  Lemma intersection_finite_r X Y : set_finite Y → set_finite (X ∩ Y).
  Proof. intros [l ?]; exists l; intros x [??]%elem_of_intersection; auto. Qed.
  Lemma difference_finite X Y : set_finite X → set_finite (X ∖ Y).
  Proof. intros [l ?]; exists l; intros x [??]%elem_of_difference; auto. Qed.
  Lemma difference_finite_inv X Y `{∀ x, Decision (x ∈ Y)} :
    set_finite Y → set_finite (X ∖ Y) → set_finite X.
  Proof.
    intros [l ?] [k ?]; exists (l ++ k).
    intros x ?; destruct (decide (x ∈ Y)); rewrite elem_of_app; set_solver.
  Qed.
End more_finite.
