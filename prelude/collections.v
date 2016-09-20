(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects definitions and theorems on collections. Most
importantly, it implements some tactics to automatically solve goals involving
collections. *)
From iris.prelude Require Export orders list.

Instance collection_equiv `{ElemOf A C} : Equiv C := λ X Y,
  ∀ x, x ∈ X ↔ x ∈ Y.
Instance collection_subseteq `{ElemOf A C} : SubsetEq C := λ X Y,
  ∀ x, x ∈ X → x ∈ Y.
Instance collection_disjoint `{ElemOf A C} : Disjoint C := λ X Y,
  ∀ x, x ∈ X → x ∈ Y → False.
Typeclasses Opaque collection_equiv collection_subseteq collection_disjoint.

(** * Setoids *)
Section setoids_simple.
  Context `{SimpleCollection A C}.

  Global Instance collection_equivalence: @Equivalence C (≡).
  Proof.
    split.
    - done.
    - intros X Y ? x. by symmetry.
    - intros X Y Z ?? x; by trans (x ∈ Y).
  Qed.
  Global Instance singleton_proper : Proper ((=) ==> (≡)) (singleton (B:=C)).
  Proof. apply _. Qed.
  Global Instance elem_of_proper :
    Proper ((=) ==> (≡) ==> iff) (@elem_of A C _) | 5.
  Proof. by intros x ? <- X Y. Qed.
  Global Instance disjoint_proper: Proper ((≡) ==> (≡) ==> iff) (@disjoint C _).
  Proof.
    intros X1 X2 HX Y1 Y2 HY; apply forall_proper; intros x. by rewrite HX, HY.
  Qed.
  Global Instance union_proper : Proper ((≡) ==> (≡) ==> (≡)) (@union C _).
  Proof. intros X1 X2 HX Y1 Y2 HY x. rewrite !elem_of_union. f_equiv; auto. Qed.
  Global Instance union_list_proper: Proper ((≡) ==> (≡)) (union_list (A:=C)).
  Proof. by induction 1; simpl; try apply union_proper. Qed.
  Global Instance subseteq_proper : Proper ((≡) ==> (≡) ==> iff) ((⊆) : relation C).
  Proof.
    intros X1 X2 HX Y1 Y2 HY. apply forall_proper; intros x. by rewrite HX, HY.
  Qed.
End setoids_simple.

Section setoids.
  Context `{Collection A C}.

  (** * Setoids *)
  Global Instance intersection_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@intersection C _).
  Proof.
    intros X1 X2 HX Y1 Y2 HY x. by rewrite !elem_of_intersection, HX, HY.
  Qed.
  Global Instance difference_proper :
     Proper ((≡) ==> (≡) ==> (≡)) (@difference C _).
  Proof.
    intros X1 X2 HX Y1 Y2 HY x. by rewrite !elem_of_difference, HX, HY.
  Qed.
End setoids.

Section setoids_monad.
  Context `{CollectionMonad M}.

  Global Instance collection_fmap_proper {A B} :
    Proper (pointwise_relation _ (=) ==> (≡) ==> (≡)) (@fmap M _ A B).
  Proof.
    intros f1 f2 Hf X1 X2 HX x. rewrite !elem_of_fmap. f_equiv; intros z.
    by rewrite HX, Hf.
  Qed.
  Global Instance collection_bind_proper {A B} :
    Proper (((=) ==> (≡)) ==> (≡) ==> (≡)) (@mbind M _ A B).
  Proof.
    intros f1 f2 Hf X1 X2 HX x. rewrite !elem_of_bind. f_equiv; intros z.
    by rewrite HX, (Hf z z).
  Qed.
  Global Instance collection_join_proper {A} :
    Proper ((≡) ==> (≡)) (@mjoin M _ A).
  Proof.
    intros X1 X2 HX x. rewrite !elem_of_join. f_equiv; intros z. by rewrite HX.
  Qed.
End setoids_monad.

(** * Tactics *)
(** The tactic [set_unfold] transforms all occurrences of [(∪)], [(∩)], [(∖)],
[(<$>)], [∅], [{[_]}], [(≡)], and [(⊆)] into logically equivalent propositions
involving just [∈]. For example, [A → x ∈ X ∪ ∅] becomes [A → x ∈ X ∨ False].

This transformation is implemented using type classes instead of setoid
rewriting to ensure that we traverse each term at most once and to be able to
deal with occurences of the set operations under binders. *)
Class SetUnfold (P Q : Prop) := { set_unfold : P ↔ Q }.
Arguments set_unfold _ _ {_}.
Hint Mode SetUnfold + - : typeclass_instances.

Class SetUnfoldSimpl (P Q : Prop) := { set_unfold_simpl : SetUnfold P Q }.
Hint Extern 0 (SetUnfoldSimpl _ _) => csimpl; constructor : typeclass_instances.

Instance set_unfold_default P : SetUnfold P P | 1000. done. Qed.
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
  Proof. constructor. split. apply not_elem_of_empty. done. Qed.
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
    intros ?; constructor. unfold equiv, collection_equiv.
    pose proof not_elem_of_empty; naive_solver.
  Qed.
  Global Instance set_unfold_equiv_empty_r (P : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → SetUnfold (X ≡ ∅) (∀ x, ¬P x) | 5.
  Proof.
    intros ?; constructor. unfold equiv, collection_equiv.
    pose proof not_elem_of_empty; naive_solver.
  Qed.
  Global Instance set_unfold_equiv (P Q : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → (∀ x, SetUnfold (x ∈ Y) (Q x)) →
    SetUnfold (X ≡ Y) (∀ x, P x ↔ Q x) | 10.
  Proof. constructor. apply forall_proper; naive_solver. Qed.
  Global Instance set_unfold_subseteq (P Q : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → (∀ x, SetUnfold (x ∈ Y) (Q x)) →
    SetUnfold (X ⊆ Y) (∀ x, P x → Q x).
  Proof. constructor. apply forall_proper; naive_solver. Qed.
  Global Instance set_unfold_subset (P Q : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → (∀ x, SetUnfold (x ∈ Y) (Q x)) →
    SetUnfold (X ⊂ Y) ((∀ x, P x → Q x) ∧ ¬∀ x, Q x → P x).
  Proof.
    constructor. unfold strict.
    repeat f_equiv; apply forall_proper; naive_solver.
  Qed.
  Global Instance set_unfold_disjoint (P Q : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → (∀ x, SetUnfold (x ∈ Y) (Q x)) →
    SetUnfold (X ⊥ Y) (∀ x, P x → Q x → False).
  Proof. constructor. unfold disjoint, collection_disjoint. naive_solver. Qed.

  Context `{!LeibnizEquiv C}.
  Global Instance set_unfold_equiv_same_L X : SetUnfold (X = X) True | 1.
  Proof. done. Qed.
  Global Instance set_unfold_equiv_empty_l_L X (P : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → SetUnfold (∅ = X) (∀ x, ¬P x) | 5.
  Proof. constructor. unfold_leibniz. by apply set_unfold_equiv_empty_l. Qed.
  Global Instance set_unfold_equiv_empty_r_L (P : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → SetUnfold (X = ∅) (∀ x, ¬P x) | 5.
  Proof. constructor. unfold_leibniz. by apply set_unfold_equiv_empty_r. Qed.
  Global Instance set_unfold_equiv_L (P Q : A → Prop) :
    (∀ x, SetUnfold (x ∈ X) (P x)) → (∀ x, SetUnfold (x ∈ Y) (Q x)) →
    SetUnfold (X = Y) (∀ x, P x ↔ Q x) | 10.
  Proof. constructor. unfold_leibniz. by apply set_unfold_equiv. Qed.
End set_unfold_simple.

Section set_unfold.
  Context `{Collection A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.

  Global Instance set_unfold_intersection x X Y P Q :
    SetUnfold (x ∈ X) P → SetUnfold (x ∈ Y) Q → SetUnfold (x ∈ X ∩ Y) (P ∧ Q).
  Proof.
    intros ??; constructor. rewrite elem_of_intersection.
    by rewrite (set_unfold (x ∈ X) P), (set_unfold (x ∈ Y) Q).
  Qed.
  Global Instance set_unfold_difference x X Y P Q :
    SetUnfold (x ∈ X) P → SetUnfold (x ∈ Y) Q → SetUnfold (x ∈ X ∖ Y) (P ∧ ¬Q).
  Proof.
    intros ??; constructor. rewrite elem_of_difference.
    by rewrite (set_unfold (x ∈ X) P), (set_unfold (x ∈ Y) Q).
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

(** Since [firstorder] already fails or loops on very small goals generated by
[set_solver], we use the [naive_solver] tactic as a substitute. *)
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


(** * Collections with [∪], [∅] and [{[_]}] *)
Section simple_collection.
  Context `{SimpleCollection A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.
  Implicit Types Xs Ys : list C.

  (** Equality *)
  Lemma elem_of_equiv X Y : X ≡ Y ↔ ∀ x, x ∈ X ↔ x ∈ Y.
  Proof. set_solver. Qed.
  Lemma collection_equiv_spec X Y : X ≡ Y ↔ X ⊆ Y ∧ Y ⊆ X.
  Proof. set_solver. Qed.

  (** Subset relation *)
  Global Instance collection_subseteq_antisymm: AntiSymm (≡) ((⊆) : relation C).
  Proof. intros ??. set_solver. Qed.

  Global Instance collection_subseteq_preorder: PreOrder ((⊆) : relation C).
  Proof. split. by intros ??. intros ???; set_solver. Qed.

  Lemma subseteq_union X Y : X ⊆ Y ↔ X ∪ Y ≡ Y.
  Proof. set_solver. Qed.
  Lemma subseteq_union_1 X Y : X ⊆ Y → X ∪ Y ≡ Y.
  Proof. by rewrite subseteq_union. Qed.
  Lemma subseteq_union_2 X Y : X ∪ Y ≡ Y → X ⊆ Y.
  Proof. by rewrite subseteq_union. Qed.

  Lemma union_subseteq_l X Y : X ⊆ X ∪ Y.
  Proof. set_solver. Qed.
  Lemma union_subseteq_r X Y : Y ⊆ X ∪ Y.
  Proof. set_solver. Qed.
  Lemma union_least X Y Z : X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z.
  Proof. set_solver. Qed.

  Lemma elem_of_subseteq X Y : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y.
  Proof. done. Qed.
  Lemma elem_of_subset X Y : X ⊂ Y ↔ (∀ x, x ∈ X → x ∈ Y) ∧ ¬(∀ x, x ∈ Y → x ∈ X).
  Proof. set_solver. Qed.

  (** Union *)
  Lemma not_elem_of_union x X Y : x ∉ X ∪ Y ↔ x ∉ X ∧ x ∉ Y.
  Proof. set_solver. Qed.
  Lemma elem_of_union_l x X Y : x ∈ X → x ∈ X ∪ Y.
  Proof. set_solver. Qed.
  Lemma elem_of_union_r x X Y : x ∈ Y → x ∈ X ∪ Y.
  Proof. set_solver. Qed.

  Lemma union_preserving_l X Y1 Y2 : Y1 ⊆ Y2 → X ∪ Y1 ⊆ X ∪ Y2.
  Proof. set_solver. Qed.
  Lemma union_preserving_r X1 X2 Y : X1 ⊆ X2 → X1 ∪ Y ⊆ X2 ∪ Y.
  Proof. set_solver. Qed.
  Lemma union_preserving X1 X2 Y1 Y2 : X1 ⊆ X2 → Y1 ⊆ Y2 → X1 ∪ Y1 ⊆ X2 ∪ Y2.
  Proof. set_solver. Qed.

  Global Instance union_idemp : IdemP ((≡) : relation C) (∪).
  Proof. intros X. set_solver. Qed.
  Global Instance union_empty_l : LeftId ((≡) : relation C) ∅ (∪).
  Proof. intros X. set_solver. Qed.
  Global Instance union_empty_r : RightId ((≡) : relation C) ∅ (∪).
  Proof. intros X. set_solver. Qed.
  Global Instance union_comm : Comm ((≡) : relation C) (∪).
  Proof. intros X Y. set_solver. Qed.
  Global Instance union_assoc : Assoc ((≡) : relation C) (∪).
  Proof. intros X Y Z. set_solver. Qed.

  Lemma empty_union X Y : X ∪ Y ≡ ∅ ↔ X ≡ ∅ ∧ Y ≡ ∅.
  Proof. set_solver. Qed.

  (** Empty *)
  Lemma elem_of_equiv_empty X : X ≡ ∅ ↔ ∀ x, x ∉ X.
  Proof. set_solver. Qed.
  Lemma elem_of_empty x : x ∈ ∅ ↔ False.
  Proof. set_solver. Qed.
  Lemma equiv_empty X : X ⊆ ∅ → X ≡ ∅.
  Proof. set_solver. Qed.
  Lemma union_positive_l X Y : X ∪ Y ≡ ∅ → X ≡ ∅.
  Proof. set_solver. Qed.
  Lemma union_positive_l_alt X Y : X ≢ ∅ → X ∪ Y ≢ ∅.
  Proof. set_solver. Qed.
  Lemma non_empty_inhabited x X : x ∈ X → X ≢ ∅.
  Proof. set_solver. Qed.

  (** Singleton *)
  Lemma elem_of_singleton_1 x y : x ∈ {[y]} → x = y.
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma elem_of_singleton_2 x y : x = y → x ∈ {[y]}.
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma elem_of_subseteq_singleton x X : x ∈ X ↔ {[ x ]} ⊆ X.
  Proof. set_solver. Qed.
  Lemma non_empty_singleton x : ({[ x ]} : C) ≢ ∅.
  Proof. set_solver. Qed.
  Lemma not_elem_of_singleton x y : x ∉ {[ y ]} ↔ x ≠ y.
  Proof. by rewrite elem_of_singleton. Qed.

  (** Disjointness *)
  Lemma elem_of_disjoint X Y : X ⊥ Y ↔ ∀ x, x ∈ X → x ∈ Y → False.
  Proof. done. Qed.

  Global Instance disjoint_sym : Symmetric (@disjoint C _).
  Proof. intros X Y. set_solver. Qed.
  Lemma disjoint_empty_l Y : ∅ ⊥ Y.
  Proof. set_solver. Qed.
  Lemma disjoint_empty_r X : X ⊥ ∅.
  Proof. set_solver. Qed.
  Lemma disjoint_singleton_l x Y : {[ x ]} ⊥ Y ↔ x ∉ Y.
  Proof. set_solver. Qed.
  Lemma disjoint_singleton_r y X : X ⊥ {[ y ]} ↔ y ∉ X.
  Proof. set_solver. Qed.
  Lemma disjoint_union_l X1 X2 Y : X1 ∪ X2 ⊥ Y ↔ X1 ⊥ Y ∧ X2 ⊥ Y.
  Proof. set_solver. Qed.
  Lemma disjoint_union_r X Y1 Y2 : X ⊥ Y1 ∪ Y2 ↔ X ⊥ Y1 ∧ X ⊥ Y2.
  Proof. set_solver. Qed.

  (** Big unions *)
  Lemma elem_of_union_list Xs x : x ∈ ⋃ Xs ↔ ∃ X, X ∈ Xs ∧ x ∈ X.
  Proof.
    split.
    - induction Xs; simpl; intros HXs; [by apply elem_of_empty in HXs|].
      setoid_rewrite elem_of_cons. apply elem_of_union in HXs. naive_solver.
    - intros [X [Hx]]. induction Hx; simpl; [by apply elem_of_union_l |].
      intros. apply elem_of_union_r; auto.
  Qed.

  Lemma union_list_nil : ⋃ @nil C = ∅.
  Proof. done. Qed.
  Lemma union_list_cons X Xs : ⋃ (X :: Xs) = X ∪ ⋃ Xs.
  Proof. done. Qed.
  Lemma union_list_singleton X : ⋃ [X] ≡ X.
  Proof. simpl. by rewrite (right_id ∅ _). Qed.
  Lemma union_list_app Xs1 Xs2 : ⋃ (Xs1 ++ Xs2) ≡ ⋃ Xs1 ∪ ⋃ Xs2.
  Proof.
    induction Xs1 as [|X Xs1 IH]; simpl; [by rewrite (left_id ∅ _)|].
    by rewrite IH, (assoc _).
  Qed.
  Lemma union_list_reverse Xs : ⋃ (reverse Xs) ≡ ⋃ Xs.
  Proof.
    induction Xs as [|X Xs IH]; simpl; [done |].
    by rewrite reverse_cons, union_list_app,
      union_list_singleton, (comm _), IH.
  Qed.
  Lemma union_list_preserving Xs Ys : Xs ⊆* Ys → ⋃ Xs ⊆ ⋃ Ys.
  Proof. induction 1; simpl; auto using union_preserving. Qed.
  Lemma empty_union_list Xs : ⋃ Xs ≡ ∅ ↔ Forall (≡ ∅) Xs.
  Proof.
    split.
    - induction Xs; simpl; rewrite ?empty_union; intuition.
    - induction 1 as [|?? E1 ? E2]; simpl. done. by apply empty_union.
  Qed.

  Section leibniz.
    Context `{!LeibnizEquiv C}.

    Lemma elem_of_equiv_L X Y : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y.
    Proof. unfold_leibniz. apply elem_of_equiv. Qed.
    Lemma collection_equiv_spec_L X Y : X = Y ↔ X ⊆ Y ∧ Y ⊆ X.
    Proof. unfold_leibniz. apply collection_equiv_spec. Qed.

    (** Subset relation *)
    Global Instance collection_subseteq_partialorder :
      PartialOrder ((⊆) : relation C).
    Proof. split. apply _. intros ??. unfold_leibniz. apply (anti_symm _). Qed.

    Lemma subseteq_union_L X Y : X ⊆ Y ↔ X ∪ Y = Y.
    Proof. unfold_leibniz. apply subseteq_union. Qed.
    Lemma subseteq_union_1_L X Y : X ⊆ Y → X ∪ Y = Y.
    Proof. unfold_leibniz. apply subseteq_union_1. Qed.
    Lemma subseteq_union_2_L X Y : X ∪ Y = Y → X ⊆ Y.
    Proof. unfold_leibniz. apply subseteq_union_2. Qed.

    (** Union *)
    Global Instance union_idemp_L : IdemP (@eq C) (∪).
    Proof. intros ?. unfold_leibniz. apply (idemp _). Qed.
    Global Instance union_empty_l_L : LeftId (@eq C) ∅ (∪).
    Proof. intros ?. unfold_leibniz. apply (left_id _ _). Qed.
    Global Instance union_empty_r_L : RightId (@eq C) ∅ (∪).
    Proof. intros ?. unfold_leibniz. apply (right_id _ _). Qed.
    Global Instance union_comm_L : Comm (@eq C) (∪).
    Proof. intros ??. unfold_leibniz. apply (comm _). Qed.
    Global Instance union_assoc_L : Assoc (@eq C) (∪).
    Proof. intros ???. unfold_leibniz. apply (assoc _). Qed.

    Lemma empty_union_L X Y : X ∪ Y = ∅ ↔ X = ∅ ∧ Y = ∅.
    Proof. unfold_leibniz. apply empty_union. Qed.

    (** Empty *)
    Lemma elem_of_equiv_empty_L X : X = ∅ ↔ ∀ x, x ∉ X.
    Proof. unfold_leibniz. apply elem_of_equiv_empty. Qed.
    Lemma equiv_empty_L X : X ⊆ ∅ → X = ∅.
    Proof. unfold_leibniz. apply equiv_empty. Qed.
    Lemma union_positive_l_L X Y : X ∪ Y = ∅ → X = ∅.
    Proof. unfold_leibniz. apply union_positive_l. Qed.
    Lemma union_positive_l_alt_L X Y : X ≠ ∅ → X ∪ Y ≠ ∅.
    Proof. unfold_leibniz. apply union_positive_l_alt. Qed.
    Lemma non_empty_inhabited_L x X : x ∈ X → X ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_inhabited. Qed.

    (** Singleton *)
    Lemma non_empty_singleton_L x : {[ x ]} ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_singleton. Qed.

    (** Big unions *)
    Lemma union_list_singleton_L X : ⋃ [X] = X.
    Proof. unfold_leibniz. apply union_list_singleton. Qed.
    Lemma union_list_app_L Xs1 Xs2 : ⋃ (Xs1 ++ Xs2) = ⋃ Xs1 ∪ ⋃ Xs2.
    Proof. unfold_leibniz. apply union_list_app. Qed.
    Lemma union_list_reverse_L Xs : ⋃ (reverse Xs) = ⋃ Xs.
    Proof. unfold_leibniz. apply union_list_reverse. Qed.
    Lemma empty_union_list_L Xs : ⋃ Xs = ∅ ↔ Forall (= ∅) Xs.
    Proof. unfold_leibniz. by rewrite empty_union_list. Qed. 
  End leibniz.

  Section dec.
    Context `{∀ (X Y : C), Decision (X ≡ Y)}.
    Lemma collection_subseteq_inv X Y : X ⊆ Y → X ⊂ Y ∨ X ≡ Y.
    Proof. destruct (decide (X ≡ Y)); [by right|left;set_solver]. Qed.
    Lemma collection_not_subset_inv X Y : X ⊄ Y → X ⊈ Y ∨ X ≡ Y.
    Proof. destruct (decide (X ≡ Y)); [by right|left;set_solver]. Qed.

    Lemma non_empty_union X Y : X ∪ Y ≢ ∅ ↔ X ≢ ∅ ∨ Y ≢ ∅.
    Proof. rewrite empty_union. destruct (decide (X ≡ ∅)); intuition. Qed.
    Lemma non_empty_union_list Xs : ⋃ Xs ≢ ∅ → Exists (≢ ∅) Xs.
    Proof. rewrite empty_union_list. apply (not_Forall_Exists _). Qed.

    Context `{!LeibnizEquiv C}.
    Lemma collection_subseteq_inv_L X Y : X ⊆ Y → X ⊂ Y ∨ X = Y.
    Proof. unfold_leibniz. apply collection_subseteq_inv. Qed.
    Lemma collection_not_subset_inv_L X Y : X ⊄ Y → X ⊈ Y ∨ X = Y.
    Proof. unfold_leibniz. apply collection_not_subset_inv. Qed.
    Lemma non_empty_union_L X Y : X ∪ Y ≠ ∅ ↔ X ≠ ∅ ∨ Y ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_union. Qed.
    Lemma non_empty_union_list_L Xs : ⋃ Xs ≠ ∅ → Exists (≠ ∅) Xs.
    Proof. unfold_leibniz. apply non_empty_union_list. Qed.
  End dec.
End simple_collection.


(** * Collections with [∪], [∩], [∖], [∅] and [{[_]}] *)
Section collection.
  Context `{Collection A C}.
  Implicit Types X Y : C.

  (** Intersection *)
  Lemma subseteq_intersection X Y : X ⊆ Y ↔ X ∩ Y ≡ X.
  Proof. set_solver. Qed. 
  Lemma subseteq_intersection_1 X Y : X ⊆ Y → X ∩ Y ≡ X.
  Proof. apply subseteq_intersection. Qed.
  Lemma subseteq_intersection_2 X Y : X ∩ Y ≡ X → X ⊆ Y.
  Proof. apply subseteq_intersection. Qed.

  Lemma intersection_subseteq_l X Y : X ∩ Y ⊆ X.
  Proof. set_solver. Qed.
  Lemma intersection_subseteq_r X Y : X ∩ Y ⊆ Y.
  Proof. set_solver. Qed.
  Lemma intersection_greatest X Y Z : Z ⊆ X → Z ⊆ Y → Z ⊆ X ∩ Y.
  Proof. set_solver. Qed.

  Lemma intersection_preserving_l X Y1 Y2 : Y1 ⊆ Y2 → X ∩ Y1 ⊆ X ∩ Y2.
  Proof. set_solver. Qed.
  Lemma intersection_preserving_r X1 X2 Y : X1 ⊆ X2 → X1 ∩ Y ⊆ X2 ∩ Y.
  Proof. set_solver. Qed.
  Lemma intersection_preserving X1 X2 Y1 Y2 :
    X1 ⊆ X2 → Y1 ⊆ Y2 → X1 ∩ Y1 ⊆ X2 ∩ Y2.
  Proof. set_solver. Qed.

  Global Instance intersection_idemp : IdemP ((≡) : relation C) (∩).
  Proof. intros X; set_solver. Qed.
  Global Instance intersection_comm : Comm ((≡) : relation C) (∩).
  Proof. intros X Y; set_solver. Qed.
  Global Instance intersection_assoc : Assoc ((≡) : relation C) (∩).
  Proof. intros X Y Z; set_solver. Qed.
  Global Instance intersection_empty_l : LeftAbsorb ((≡) : relation C) ∅ (∩).
  Proof. intros X; set_solver. Qed.
  Global Instance intersection_empty_r: RightAbsorb ((≡) : relation C) ∅ (∩).
  Proof. intros X; set_solver. Qed.

  Lemma intersection_singletons x : ({[x]} : C) ∩ {[x]} ≡ {[x]}.
  Proof. set_solver. Qed.

  Lemma union_intersection_l X Y Z : X ∪ (Y ∩ Z) ≡ (X ∪ Y) ∩ (X ∪ Z).
  Proof. set_solver. Qed.
  Lemma union_intersection_r X Y Z : (X ∩ Y) ∪ Z ≡ (X ∪ Z) ∩ (Y ∪ Z).
  Proof. set_solver. Qed.
  Lemma intersection_union_l X Y Z : X ∩ (Y ∪ Z) ≡ (X ∩ Y) ∪ (X ∩ Z).
  Proof. set_solver. Qed.
  Lemma intersection_union_r X Y Z : (X ∪ Y) ∩ Z ≡ (X ∩ Z) ∪ (Y ∩ Z).
  Proof. set_solver. Qed.

  (** Difference *)
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
  Lemma difference_disjoint X Y : X ⊥ Y → X ∖ Y ≡ X.
  Proof. set_solver. Qed.

  (** Disjointness *)
  Lemma disjoint_intersection X Y : X ⊥ Y ↔ X ∩ Y ≡ ∅.
  Proof. set_solver. Qed.

  Section leibniz.
    Context `{!LeibnizEquiv C}.

    (** Intersection *)
    Lemma subseteq_intersection_L X Y : X ⊆ Y ↔ X ∩ Y = X.
    Proof. unfold_leibniz. apply subseteq_intersection. Qed.
    Lemma subseteq_intersection_1_L X Y : X ⊆ Y → X ∩ Y = X.
    Proof. unfold_leibniz. apply subseteq_intersection_1. Qed.
    Lemma subseteq_intersection_2_L X Y : X ∩ Y = X → X ⊆ Y.
    Proof. unfold_leibniz. apply subseteq_intersection_2. Qed.

    Global Instance intersection_idemp_L : IdemP ((=) : relation C) (∩).
    Proof. intros ?. unfold_leibniz. apply (idemp _). Qed.
    Global Instance intersection_comm_L : Comm ((=) : relation C) (∩).
    Proof. intros ??. unfold_leibniz. apply (comm _). Qed.
    Global Instance intersection_assoc_L : Assoc ((=) : relation C) (∩).
    Proof. intros ???. unfold_leibniz. apply (assoc _). Qed.
    Global Instance intersection_empty_l_L: LeftAbsorb ((=) : relation C) ∅ (∩).
    Proof. intros ?. unfold_leibniz. apply (left_absorb _ _). Qed.
    Global Instance intersection_empty_r_L: RightAbsorb ((=) : relation C) ∅ (∩).
    Proof. intros ?. unfold_leibniz. apply (right_absorb _ _). Qed.

    Lemma intersection_singletons_L x : {[x]} ∩ {[x]} = {[x]}.
    Proof. unfold_leibniz. apply intersection_singletons. Qed.

    Lemma union_intersection_l_L X Y Z : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z).
    Proof. unfold_leibniz; apply union_intersection_l. Qed.
    Lemma union_intersection_r_L X Y Z : (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z).
    Proof. unfold_leibniz; apply union_intersection_r. Qed.
    Lemma intersection_union_l_L X Y Z : X ∩ (Y ∪ Z) ≡ (X ∩ Y) ∪ (X ∩ Z).
    Proof. unfold_leibniz; apply intersection_union_l. Qed.
    Lemma intersection_union_r_L X Y Z : (X ∪ Y) ∩ Z ≡ (X ∩ Z) ∪ (Y ∩ Z).
    Proof. unfold_leibniz; apply intersection_union_r. Qed.

    (** Difference *)
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
    Lemma difference_disjoint_L X Y : X ⊥ Y → X ∖ Y = X.
    Proof. unfold_leibniz. apply difference_disjoint. Qed.

    (** Disjointness *)
    Lemma disjoint_intersection_L X Y : X ⊥ Y ↔ X ∩ Y = ∅.
    Proof. unfold_leibniz. apply disjoint_intersection. Qed.
  End leibniz.

  Section dec.
    Context `{∀ (x : A) (X : C), Decision (x ∈ X)}.
    Lemma not_elem_of_intersection x X Y : x ∉ X ∩ Y ↔ x ∉ X ∨ x ∉ Y.
    Proof. rewrite elem_of_intersection. destruct (decide (x ∈ X)); tauto. Qed.
    Lemma not_elem_of_difference x X Y : x ∉ X ∖ Y ↔ x ∉ X ∨ x ∈ Y.
    Proof. rewrite elem_of_difference. destruct (decide (x ∈ Y)); tauto. Qed.
    Lemma union_difference X Y : X ⊆ Y → Y ≡ X ∪ Y ∖ X.
    Proof.
      intros ? x; split; rewrite !elem_of_union, elem_of_difference; [|intuition].
      destruct (decide (x ∈ X)); intuition.
    Qed.
    Lemma subseteq_disjoint_union X Y : X ⊆ Y ↔ ∃ Z, Y ≡ X ∪ Z ∧ X ⊥ Z.
    Proof.
      split; [|set_solver].
      exists (Y ∖ X); split; [auto using union_difference|set_solver].
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
    Lemma subseteq_disjoint_union_L X Y : X ⊆ Y ↔ ∃ Z, Y = X ∪ Z ∧ X ⊥ Z.
    Proof. unfold_leibniz. apply subseteq_disjoint_union. Qed.
  End dec.
End collection.


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
    SetUnfold (l ⊆ k) (∀ x, P x → Q x).
  Proof. by constructor; unfold subseteq, list_subseteq; set_unfold. Qed.
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

  Lemma exist_fresh X : ∃ x, x ∉ X.
  Proof. exists (fresh X). apply is_fresh. Qed.
  Lemma Forall_fresh_NoDup X xs : Forall_fresh X xs → NoDup xs.
  Proof. induction 1; by constructor. Qed.
  Lemma Forall_fresh_elem_of X xs x : Forall_fresh X xs → x ∈ xs → x ∉ X.
  Proof.
    intros HX; revert x; rewrite <-Forall_forall. by induction HX; constructor.
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
  Global Instance collection_bind_mono {A B} :
    Proper (((=) ==> (⊆)) ==> (⊆) ==> (⊆)) (@mbind M _ A B).
  Proof. unfold respectful; intros f g Hfg X Y ?; set_solver. Qed.
  Global Instance collection_join_mono {A} :
    Proper ((⊆) ==> (⊆)) (@mjoin M _ A).
  Proof. intros X Y ?; set_solver. Qed.

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
  Proof. intros X Y HX; apply exist_proper. by setoid_rewrite HX. Qed.
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

(** Sets of sequences of natural numbers *)
(* The set [seq_seq start len] of natural numbers contains the sequence
[start, start + 1, ..., start + (len-1)]. *)
Fixpoint seq_set `{Singleton nat C, Union C, Empty C} (start len : nat) : C :=
  match len with
  | O => ∅
  | S len' => {[ start ]} ∪ seq_set (S start) len'
  end.

Section seq_set.
  Context `{SimpleCollection nat C}.
  Implicit Types start len x : nat.

  Lemma elem_of_seq_set start len x :
    x ∈ seq_set start len ↔ start ≤ x < start + len.
  Proof.
    revert start. induction len as [|len IH]; intros start; simpl.
    - rewrite elem_of_empty. omega.
    - rewrite elem_of_union, elem_of_singleton, IH. omega.
  Qed.

  Lemma seq_set_S_disjoint start len : {[ start + len ]} ⊥ seq_set start len.
  Proof. intros x. rewrite elem_of_singleton, elem_of_seq_set. omega. Qed.

  Lemma seq_set_S_union start len :
    seq_set start (C:=C) (S len) ≡ {[ start + len ]} ∪ seq_set start len.
  Proof.
    intros x. rewrite elem_of_union, elem_of_singleton, !elem_of_seq_set. omega.
  Qed.

  Lemma seq_set_S_union_L `{!LeibnizEquiv C} start len :
    seq_set start (S len) = {[ start + len ]} ∪ seq_set start len.
  Proof. unfold_leibniz. apply seq_set_S_union. Qed.
End seq_set.
