(* Copyright (c) 2012-2017, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects definitions and theorems on finite collections. Most
importantly, it implements a fold and size function and some useful induction
principles on finite collections . *)
From iris.prelude Require Import relations.
From iris.prelude Require Export numbers collections.
Set Default Proof Using "Type*".

Instance collection_size `{Elements A C} : Size C := length ∘ elements.
Definition collection_fold `{Elements A C} {B}
  (f : A → B → B) (b : B) : C → B := foldr f b ∘ elements.

Instance collection_filter
    `{Elements A C, Empty C, Singleton A C, Union C} : Filter A C := λ P _ X,
  of_list (filter P (elements X)).
Typeclasses Opaque collection_filter.

Section fin_collection.
Context `{FinCollection A C}.
Implicit Types X Y : C.

Lemma fin_collection_finite X : set_finite X.
Proof. by exists (elements X); intros; rewrite elem_of_elements. Qed.

Instance elem_of_dec_slow (x : A) (X : C) : Decision (x ∈ X) | 100.
Proof.
  refine (cast_if (decide_rel (∈) x (elements X)));
    by rewrite <-(elem_of_elements _).
Defined.

(** * The [elements] operation *)
Global Instance elements_proper: Proper ((≡) ==> (≡ₚ)) (elements (C:=C)).
Proof.
  intros ?? E. apply NoDup_Permutation.
  - apply NoDup_elements.
  - apply NoDup_elements.
  - intros. by rewrite !elem_of_elements, E.
Qed.

Lemma elements_empty : elements (∅ : C) = [].
Proof.
  apply elem_of_nil_inv; intros x.
  rewrite elem_of_elements, elem_of_empty; tauto.
Qed.
Lemma elements_empty_inv X : elements X = [] → X ≡ ∅.
Proof.
  intros HX; apply elem_of_equiv_empty; intros x.
  rewrite <-elem_of_elements, HX, elem_of_nil. tauto.
Qed.
Lemma elements_empty' X : elements X = [] ↔ X ≡ ∅.
Proof.
  split; intros HX; [by apply elements_empty_inv|].
  by rewrite <-Permutation_nil, HX, elements_empty.
Qed.

Lemma elements_union_singleton (X : C) x :
  x ∉ X → elements ({[ x ]} ∪ X) ≡ₚ x :: elements X.
Proof.
  intros ?; apply NoDup_Permutation.
  { apply NoDup_elements. }
  { by constructor; rewrite ?elem_of_elements; try apply NoDup_elements. }
  intros y; rewrite elem_of_elements, elem_of_union, elem_of_singleton.
  by rewrite elem_of_cons, elem_of_elements.
Qed.
Lemma elements_singleton x : elements {[ x ]} = [x].
Proof.
  apply Permutation_singleton. by rewrite <-(right_id ∅ (∪) {[x]}),
    elements_union_singleton, elements_empty by set_solver.
Qed.
Lemma elements_submseteq X Y : X ⊆ Y → elements X ⊆+ elements Y.
Proof.
  intros; apply NoDup_submseteq; auto using NoDup_elements.
  intros x. rewrite !elem_of_elements; auto.
Qed.

(** * The [size] operation *)
Global Instance collection_size_proper: Proper ((≡) ==> (=)) (@size C _).
Proof. intros ?? E. apply Permutation_length. by rewrite E. Qed.

Lemma size_empty : size (∅ : C) = 0.
Proof. unfold size, collection_size. simpl. by rewrite elements_empty. Qed.
Lemma size_empty_inv (X : C) : size X = 0 → X ≡ ∅.
Proof.
  intros; apply equiv_empty; intros x; rewrite <-elem_of_elements.
  by rewrite (nil_length_inv (elements X)), ?elem_of_nil.
Qed.
Lemma size_empty_iff (X : C) : size X = 0 ↔ X ≡ ∅.
Proof. split. apply size_empty_inv. by intros ->; rewrite size_empty. Qed.
Lemma size_non_empty_iff (X : C) : size X ≠ 0 ↔ X ≢ ∅.
Proof. by rewrite size_empty_iff. Qed.

Lemma collection_choose_or_empty X : (∃ x, x ∈ X) ∨ X ≡ ∅.
Proof.
  destruct (elements X) as [|x l] eqn:HX; [right|left].
  - apply equiv_empty; intros x. by rewrite <-elem_of_elements, HX, elem_of_nil.
  - exists x. rewrite <-elem_of_elements, HX. by left.
Qed.
Lemma collection_choose X : X ≢ ∅ → ∃ x, x ∈ X.
Proof. intros. by destruct (collection_choose_or_empty X). Qed.
Lemma collection_choose_L `{!LeibnizEquiv C} X : X ≠ ∅ → ∃ x, x ∈ X.
Proof. unfold_leibniz. apply collection_choose. Qed.
Lemma size_pos_elem_of X : 0 < size X → ∃ x, x ∈ X.
Proof.
  intros Hsz. destruct (collection_choose_or_empty X) as [|HX]; [done|].
  contradict Hsz. rewrite HX, size_empty; lia.
Qed.

Lemma size_singleton (x : A) : size {[ x ]} = 1.
Proof. unfold size, collection_size. simpl. by rewrite elements_singleton. Qed.
Lemma size_singleton_inv X x y : size X = 1 → x ∈ X → y ∈ X → x = y.
Proof.
  unfold size, collection_size. simpl. rewrite <-!elem_of_elements.
  generalize (elements X). intros [|? l]; intro; simplify_eq/=.
  rewrite (nil_length_inv l), !elem_of_list_singleton by done; congruence.
Qed.
Lemma size_1_elem_of X : size X = 1 → ∃ x, X ≡ {[ x ]}.
Proof.
  intros E. destruct (size_pos_elem_of X); auto with lia.
  exists x. apply elem_of_equiv. split.
  - rewrite elem_of_singleton. eauto using size_singleton_inv.
  - set_solver.
Qed.

Lemma size_union X Y : X ⊥ Y → size (X ∪ Y) = size X + size Y.
Proof.
  intros. unfold size, collection_size. simpl. rewrite <-app_length.
  apply Permutation_length, NoDup_Permutation.
  - apply NoDup_elements.
  - apply NoDup_app; repeat split; try apply NoDup_elements.
    intros x; rewrite !elem_of_elements; set_solver.
  - intros. by rewrite elem_of_app, !elem_of_elements, elem_of_union.
Qed.
Lemma size_union_alt X Y : size (X ∪ Y) = size X + size (Y ∖ X).
Proof.
  rewrite <-size_union by set_solver.
  setoid_replace (Y ∖ X) with ((Y ∪ X) ∖ X) by set_solver.
  rewrite <-union_difference, (comm (∪)); set_solver.
Qed.

Lemma subseteq_size X Y : X ⊆ Y → size X ≤ size Y.
Proof. intros. rewrite (union_difference X Y), size_union_alt by done. lia. Qed.
Lemma subset_size X Y : X ⊂ Y → size X < size Y.
Proof.
  intros. rewrite (union_difference X Y) by set_solver.
  rewrite size_union_alt, difference_twice.
  cut (size (Y ∖ X) ≠ 0); [lia |].
  by apply size_non_empty_iff, non_empty_difference.
Qed.

(** * Induction principles *)
Lemma collection_wf : wf (strict (@subseteq C _)).
Proof. apply (wf_projected (<) size); auto using subset_size, lt_wf. Qed.
Lemma collection_ind (P : C → Prop) :
  Proper ((≡) ==> iff) P →
  P ∅ → (∀ x X, x ∉ X → P X → P ({[ x ]} ∪ X)) → ∀ X, P X.
Proof.
  intros ? Hemp Hadd. apply well_founded_induction with (⊂).
  { apply collection_wf. }
  intros X IH. destruct (collection_choose_or_empty X) as [[x ?]|HX].
  - rewrite (union_difference {[ x ]} X) by set_solver.
    apply Hadd. set_solver. apply IH; set_solver.
  - by rewrite HX.
Qed.
Lemma collection_ind_L `{!LeibnizEquiv C} (P : C → Prop) :
  P ∅ → (∀ x X, x ∉ X → P X → P ({[ x ]} ∪ X)) → ∀ X, P X.
Proof. apply collection_ind. by intros ?? ->%leibniz_equiv_iff. Qed.

(** * The [collection_fold] operation *)
Lemma collection_fold_ind {B} (P : B → C → Prop) (f : A → B → B) (b : B) :
  Proper ((=) ==> (≡) ==> iff) P →
  P b ∅ → (∀ x X r, x ∉ X → P r X → P (f x r) ({[ x ]} ∪ X)) →
  ∀ X, P (collection_fold f b X) X.
Proof.
  intros ? Hemp Hadd.
  cut (∀ l, NoDup l → ∀ X, (∀ x, x ∈ X ↔ x ∈ l) → P (foldr f b l) X).
  { intros help ?. apply help; [apply NoDup_elements|].
    symmetry. apply elem_of_elements. }
  induction 1 as [|x l ?? IH]; simpl.
  - intros X HX. setoid_rewrite elem_of_nil in HX.
    rewrite equiv_empty. done. set_solver.
  - intros X HX. setoid_rewrite elem_of_cons in HX.
    rewrite (union_difference {[ x ]} X) by set_solver.
    apply Hadd. set_solver. apply IH. set_solver.
Qed.
Lemma collection_fold_proper {B} (R : relation B) `{!Equivalence R}
    (f : A → B → B) (b : B) `{!Proper ((=) ==> R ==> R) f}
    (Hf : ∀ a1 a2 b, R (f a1 (f a2 b)) (f a2 (f a1 b))) :
  Proper ((≡) ==> R) (collection_fold f b : C → B).
Proof. intros ?? E. apply (foldr_permutation R f b); auto. by rewrite E. Qed.

(** * Minimal elements *)
Lemma minimal_exists R `{!Transitive R, ∀ x y, Decision (R x y)} (X : C) :
  X ≢ ∅ → ∃ x, x ∈ X ∧ minimal R x X.
Proof.
  pattern X; apply collection_ind; clear X.
  { by intros X X' HX; setoid_rewrite HX. }
  { done. }
  intros x X ? IH Hemp. destruct (collection_choose_or_empty X) as [[z ?]|HX].
  { destruct IH as (x' & Hx' & Hmin); [set_solver|].
    destruct (decide (R x x')).
    - exists x; split; [set_solver|].
      eauto using union_minimal, singleton_minimal, minimal_weaken.
    - exists x'; split; [set_solver|].
      auto using union_minimal, singleton_minimal_not_above. }
  exists x; split; [set_solver|].
  rewrite HX, (right_id _ (∪)). apply singleton_minimal.
Qed.
Lemma minimal_exists_L R `{!LeibnizEquiv C, !Transitive R,
    ∀ x y, Decision (R x y)} (X : C) :
  X ≠ ∅ → ∃ x, x ∈ X ∧ minimal R x X.
Proof. unfold_leibniz. apply (minimal_exists R). Qed.

(** * Filter *)
Section filter.
  Context (P : A → Prop) `{!∀ x, Decision (P x)}.

  Lemma elem_of_filter X x : x ∈ filter P X ↔ P x ∧ x ∈ X.
  Proof.
    unfold filter, collection_filter.
    by rewrite elem_of_of_list, elem_of_list_filter, elem_of_elements.
  Qed.
  Global Instance set_unfold_filter X Q :
    SetUnfold (x ∈ X) Q → SetUnfold (x ∈ filter P X) (P x ∧ Q).
  Proof.
    intros ??; constructor. by rewrite elem_of_filter, (set_unfold (x ∈ X) Q).
  Qed.

  Lemma filter_empty : filter P (∅:C) ≡ ∅.
  Proof. set_solver. Qed.
  Lemma filter_union X Y : filter P (X ∪ Y) ≡ filter P X ∪ filter P Y.
  Proof. set_solver. Qed.
  Lemma filter_singleton x : P x → filter P ({[ x ]} : C) ≡ {[ x ]}.
  Proof. set_solver. Qed.
  Lemma filter_singleton_not x : ¬P x → filter P ({[ x ]} : C) ≡ ∅.
  Proof. set_solver. Qed.

  Section leibniz_equiv.
    Context `{!LeibnizEquiv C}.
    Lemma filter_empty_L : filter P (∅:C) = ∅.
    Proof. set_solver. Qed.
    Lemma filter_union_L X Y : filter P (X ∪ Y) = filter P X ∪ filter P Y.
    Proof. set_solver. Qed.
    Lemma filter_singleton_L x : P x → filter P ({[ x ]} : C) = {[ x ]}.
    Proof. set_solver. Qed.
    Lemma filter_singleton_not_L x : ¬P x → filter P ({[ x ]} : C) = ∅.
    Proof. set_solver. Qed.
  End leibniz_equiv.
End filter.

(** * Decision procedures *)
Lemma set_Forall_elements P X : set_Forall P X ↔ Forall P (elements X).
Proof. rewrite Forall_forall. by setoid_rewrite elem_of_elements. Qed.
Lemma set_Exists_elements P X : set_Exists P X ↔ Exists P (elements X).
Proof. rewrite Exists_exists. by setoid_rewrite elem_of_elements. Qed.

Lemma set_Forall_Exists_dec (P Q : A → Prop) (dec : ∀ x, {P x} + {Q x}) X :
  {set_Forall P X} + {set_Exists Q X}.
Proof.
 refine (cast_if (Forall_Exists_dec P Q dec (elements X)));
   [by apply set_Forall_elements|by apply set_Exists_elements].
Defined.

Lemma not_set_Forall_Exists P `{dec : ∀ x, Decision (P x)} X :
  ¬set_Forall P X → set_Exists (not ∘ P) X.
Proof. intro. by destruct (set_Forall_Exists_dec P (not ∘ P) dec X). Qed.
Lemma not_set_Exists_Forall P `{dec : ∀ x, Decision (P x)} X :
  ¬set_Exists P X → set_Forall (not ∘ P) X.
Proof.
  by destruct (set_Forall_Exists_dec
    (not ∘ P) P (λ x, swap_if (decide (P x))) X).
Qed.

Global Instance set_Forall_dec (P : A → Prop) `{∀ x, Decision (P x)} X :
  Decision (set_Forall P X) | 100.
Proof.
 refine (cast_if (decide (Forall P (elements X))));
   by rewrite set_Forall_elements.
Defined.
Global Instance set_Exists_dec `(P : A → Prop) `{∀ x, Decision (P x)} X :
  Decision (set_Exists P X) | 100.
Proof.
 refine (cast_if (decide (Exists P (elements X))));
   by rewrite set_Exists_elements.
Defined.
End fin_collection.
