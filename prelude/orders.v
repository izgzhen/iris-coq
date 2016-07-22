(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects common properties of pre-orders and semi lattices. This
theory will mainly be used for the theory on collections and finite maps. *)
From Coq Require Export Sorted.
From iris.prelude Require Export tactics list.

(** * Arbitrary pre-, parial and total orders *)
(** Properties about arbitrary pre-, partial, and total orders. We do not use
the relation [⊆] because we often have multiple orders on the same structure *)
Section orders.
  Context {A} {R : relation A}.
  Implicit Types X Y : A.
  Infix "⊆" := R.
  Notation "X ⊈ Y" := (¬X ⊆ Y).
  Infix "⊂" := (strict R).

  Lemma reflexive_eq `{!Reflexive R} X Y : X = Y → X ⊆ Y.
  Proof. by intros <-. Qed.
  Lemma anti_symm_iff `{!PartialOrder R} X Y : X = Y ↔ R X Y ∧ R Y X.
  Proof. split. by intros ->. by intros [??]; apply (anti_symm _). Qed.
  Lemma strict_spec X Y : X ⊂ Y ↔ X ⊆ Y ∧ Y ⊈ X.
  Proof. done. Qed.
  Lemma strict_include X Y : X ⊂ Y → X ⊆ Y.
  Proof. by intros [? _]. Qed.
  Lemma strict_ne X Y : X ⊂ Y → X ≠ Y.
  Proof. by intros [??] <-. Qed.
  Lemma strict_ne_sym X Y : X ⊂ Y → Y ≠ X.
  Proof. by intros [??] <-. Qed.
  Lemma strict_transitive_l `{!Transitive R} X Y Z : X ⊂ Y → Y ⊆ Z → X ⊂ Z.
  Proof.
    intros [? HXY] ?. split; [by trans Y|].
    contradict HXY. by trans Z.
  Qed.
  Lemma strict_transitive_r `{!Transitive R} X Y Z : X ⊆ Y → Y ⊂ Z → X ⊂ Z.
  Proof.
    intros ? [? HYZ]. split; [by trans Y|].
    contradict HYZ. by trans X.
  Qed.
  Global Instance: Irreflexive (strict R).
  Proof. firstorder. Qed.
  Global Instance: Transitive R → StrictOrder (strict R).
  Proof.
    split; try apply _.
    eauto using strict_transitive_r, strict_include.
  Qed.
  Global Instance preorder_subset_dec_slow `{∀ X Y, Decision (X ⊆ Y)}
    (X Y : A) : Decision (X ⊂ Y) | 100 := _.
  Lemma strict_spec_alt `{!AntiSymm (=) R} X Y : X ⊂ Y ↔ X ⊆ Y ∧ X ≠ Y.
  Proof.
    split.
    - intros [? HYX]. split. done. by intros <-.
    - intros [? HXY]. split. done. by contradict HXY; apply (anti_symm R).
  Qed.
  Lemma po_eq_dec `{!PartialOrder R, ∀ X Y, Decision (X ⊆ Y)} (X Y : A) :
    Decision (X = Y).
  Proof.
    refine (cast_if_and (decide (X ⊆ Y)) (decide (Y ⊆ X)));
     abstract (rewrite anti_symm_iff; tauto).
  Defined.
  Lemma total_not `{!Total R} X Y : X ⊈ Y → Y ⊆ X.
  Proof. intros. destruct (total R X Y); tauto. Qed.
  Lemma total_not_strict `{!Total R} X Y : X ⊈ Y → Y ⊂ X.
  Proof. red; auto using total_not. Qed.
  Global Instance trichotomy_total
    `{!Trichotomy (strict R), !Reflexive R} : Total R.
  Proof.
    intros X Y.
    destruct (trichotomy (strict R) X Y) as [[??]|[<-|[??]]]; intuition.
  Qed.
End orders.

Section strict_orders.
  Context {A} {R : relation A}.
  Implicit Types X Y : A.
  Infix "⊂" := R.

  Lemma irreflexive_eq `{!Irreflexive R} X Y : X = Y → ¬X ⊂ Y.
  Proof. intros ->. apply (irreflexivity R). Qed.
  Lemma strict_anti_symm `{!StrictOrder R} X Y :
    X ⊂ Y → Y ⊂ X → False.
  Proof. intros. apply (irreflexivity R X). by trans Y. Qed.
  Global Instance trichotomyT_dec `{!TrichotomyT R, !StrictOrder R} X Y :
      Decision (X ⊂ Y) :=
    match trichotomyT R X Y with
    | inleft (left H) => left H
    | inleft (right H) => right (irreflexive_eq _ _ H)
    | inright H => right (strict_anti_symm _ _ H)
    end.
  Global Instance trichotomyT_trichotomy `{!TrichotomyT R} : Trichotomy R.
  Proof. intros X Y. destruct (trichotomyT R X Y) as [[|]|]; tauto. Qed.
End strict_orders.

Ltac simplify_order := repeat
  match goal with
  | _ => progress simplify_eq/=
  | H : ?R ?x ?x |- _ => by destruct (irreflexivity _ _ H)
  | H1 : ?R ?x ?y |- _ =>
    match goal with
    | H2 : R y x |- _ =>
      assert (x = y) by (by apply (anti_symm R)); clear H1 H2
    | H2 : R y ?z |- _ =>
      unless (R x z) by done;
      assert (R x z) by (by trans y)
    end
  end.

(** * Sorting *)
(** Merge sort. Adapted from the implementation of Hugo Herbelin in the Coq
standard library, but without using the module system. *)
Section merge_sort.
  Context  {A} (R : relation A) `{∀ x y, Decision (R x y)}.

  Fixpoint list_merge (l1 : list A) : list A → list A :=
    fix list_merge_aux l2 :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x1 :: l1, x2 :: l2 =>
       if decide_rel R x1 x2 then x1 :: list_merge l1 (x2 :: l2)
       else x2 :: list_merge_aux l2
    end.
  Global Arguments list_merge !_ !_ /.

  Local Notation stack := (list (option (list A))).
  Fixpoint merge_list_to_stack (st : stack) (l : list A) : stack :=
    match st with
    | [] => [Some l]
    | None :: st => Some l :: st
    | Some l' :: st => None :: merge_list_to_stack st (list_merge l' l)
    end.
  Fixpoint merge_stack (st : stack) : list A :=
    match st with
    | [] => []
    | None :: st => merge_stack st
    | Some l :: st => list_merge l (merge_stack st)
    end.
  Fixpoint merge_sort_aux (st : stack) (l : list A) : list A :=
    match l with
    | [] => merge_stack st
    | x :: l => merge_sort_aux (merge_list_to_stack st [x]) l
    end.
  Definition merge_sort : list A → list A := merge_sort_aux [].
End merge_sort.

(** ** Properties of the [Sorted] and [StronglySorted] predicate *)
Section sorted.
  Context {A} (R : relation A).

  Lemma Sorted_StronglySorted `{!Transitive R} l :
    Sorted R l → StronglySorted R l.
  Proof. by apply Sorted.Sorted_StronglySorted. Qed.
  Lemma StronglySorted_unique `{!AntiSymm (=) R} l1 l2 :
    StronglySorted R l1 → StronglySorted R l2 → l1 ≡ₚ l2 → l1 = l2.
  Proof.
    intros Hl1; revert l2. induction Hl1 as [|x1 l1 ? IH Hx1]; intros l2 Hl2 E.
    { symmetry. by apply Permutation_nil. }
    destruct Hl2 as [|x2 l2 ? Hx2].
    { by apply Permutation_nil in E. }
    assert (x1 = x2); subst.
    { rewrite Forall_forall in Hx1, Hx2.
      assert (x2 ∈ x1 :: l1) as Hx2' by (by rewrite E; left).
      assert (x1 ∈ x2 :: l2) as Hx1' by (by rewrite <-E; left).
      inversion Hx1'; inversion Hx2'; simplify_eq; auto. }
    f_equal. by apply IH, (inj (x2 ::)).
  Qed.
  Lemma Sorted_unique `{!Transitive R, !AntiSymm (=) R} l1 l2 :
    Sorted R l1 → Sorted R l2 → l1 ≡ₚ l2 → l1 = l2.
  Proof. auto using StronglySorted_unique, Sorted_StronglySorted. Qed.

  Global Instance HdRel_dec x `{∀ y, Decision (R x y)} l :
    Decision (HdRel R x l).
  Proof.
   refine
    match l with
    | [] => left _
    | y :: l => cast_if (decide (R x y))
    end; abstract first [by constructor | by inversion 1].
  Defined.
  Global Instance Sorted_dec `{∀ x y, Decision (R x y)} : ∀ l,
    Decision (Sorted R l).
  Proof.
   refine
    (fix go l :=
    match l return Decision (Sorted R l) with
    | [] => left _
    | x :: l => cast_if_and (decide (HdRel R x l)) (go l)
    end); clear go; abstract first [by constructor | by inversion 1].
  Defined.
  Global Instance StronglySorted_dec `{∀ x y, Decision (R x y)} : ∀ l,
    Decision (StronglySorted R l).
  Proof.
   refine
    (fix go l :=
    match l return Decision (StronglySorted R l) with
    | [] => left _
    | x :: l => cast_if_and (decide (Forall (R x) l)) (go l)
    end); clear go; abstract first [by constructor | by inversion 1].
  Defined.

  Context {B} (f : A → B).
  Lemma HdRel_fmap (R1 : relation A) (R2 : relation B) x l :
    (∀ y, R1 x y → R2 (f x) (f y)) → HdRel R1 x l → HdRel R2 (f x) (f <$> l).
  Proof. destruct 2; constructor; auto. Qed.
  Lemma Sorted_fmap (R1 : relation A) (R2 : relation B) l :
    (∀ x y, R1 x y → R2 (f x) (f y)) → Sorted R1 l → Sorted R2 (f <$> l).
  Proof. induction 2; simpl; constructor; eauto using HdRel_fmap. Qed.
  Lemma StronglySorted_fmap (R1 : relation A) (R2 : relation B) l :
    (∀ x y, R1 x y → R2 (f x) (f y)) →
    StronglySorted R1 l → StronglySorted R2 (f <$> l).
  Proof.
    induction 2; csimpl; constructor;
      rewrite ?Forall_fmap; eauto using Forall_impl.
  Qed.
End sorted.

(** ** Correctness of merge sort *)
Section merge_sort_correct.
  Context  {A} (R : relation A) `{∀ x y, Decision (R x y)} `{!Total R}.

  Lemma list_merge_cons x1 x2 l1 l2 :
    list_merge R (x1 :: l1) (x2 :: l2) =
      if decide (R x1 x2) then x1 :: list_merge R l1 (x2 :: l2)
      else x2 :: list_merge R (x1 :: l1) l2.
  Proof. done. Qed.
  Lemma HdRel_list_merge x l1 l2 :
    HdRel R x l1 → HdRel R x l2 → HdRel R x (list_merge R l1 l2).
  Proof.
    destruct 1 as [|x1 l1 IH1], 1 as [|x2 l2 IH2];
      rewrite ?list_merge_cons; simpl; repeat case_decide; auto.
  Qed.
  Lemma Sorted_list_merge l1 l2 :
    Sorted R l1 → Sorted R l2 → Sorted R (list_merge R l1 l2).
  Proof.
    intros Hl1. revert l2. induction Hl1 as [|x1 l1 IH1];
      induction 1 as [|x2 l2 IH2]; rewrite ?list_merge_cons; simpl;
      repeat case_decide;
      constructor; eauto using HdRel_list_merge, HdRel_cons, total_not.
  Qed.
  Lemma merge_Permutation l1 l2 : list_merge R l1 l2 ≡ₚ l1 ++ l2.
  Proof.
    revert l2. induction l1 as [|x1 l1 IH1]; intros l2;
      induction l2 as [|x2 l2 IH2]; rewrite ?list_merge_cons; simpl;
      repeat case_decide; auto.
    - by rewrite (right_id_L [] (++)).
    - by rewrite IH2, Permutation_middle.
  Qed.

  Local Notation stack := (list (option (list A))).
  Inductive merge_stack_Sorted : stack → Prop :=
    | merge_stack_Sorted_nil : merge_stack_Sorted []
    | merge_stack_Sorted_cons_None st :
       merge_stack_Sorted st → merge_stack_Sorted (None :: st)
    | merge_stack_Sorted_cons_Some l st :
       Sorted R l → merge_stack_Sorted st → merge_stack_Sorted (Some l :: st).
  Fixpoint merge_stack_flatten (st : stack) : list A :=
    match st with
    | [] => []
    | None :: st => merge_stack_flatten st
    | Some l :: st => l ++ merge_stack_flatten st
    end.

  Lemma Sorted_merge_list_to_stack st l :
    merge_stack_Sorted st → Sorted R l →
    merge_stack_Sorted (merge_list_to_stack R st l).
  Proof.
    intros Hst. revert l.
    induction Hst; repeat constructor; naive_solver auto using Sorted_list_merge.
  Qed.
  Lemma merge_list_to_stack_Permutation st l :
    merge_stack_flatten (merge_list_to_stack R st l) ≡ₚ
      l ++ merge_stack_flatten st.
  Proof.
    revert l. induction st as [|[l'|] st IH]; intros l; simpl; auto.
    by rewrite IH, merge_Permutation, (assoc_L _), (comm (++) l).
  Qed.
  Lemma Sorted_merge_stack st :
    merge_stack_Sorted st → Sorted R (merge_stack R st).
  Proof. induction 1; simpl; auto using Sorted_list_merge. Qed.
  Lemma merge_stack_Permutation st : merge_stack R st ≡ₚ merge_stack_flatten st.
  Proof.
    induction st as [|[] ? IH]; intros; simpl; auto.
    by rewrite merge_Permutation, IH.
  Qed.
  Lemma Sorted_merge_sort_aux st l :
    merge_stack_Sorted st → Sorted R (merge_sort_aux R st l).
  Proof.
    revert st. induction l; simpl;
      auto using Sorted_merge_stack, Sorted_merge_list_to_stack.
  Qed.
  Lemma merge_sort_aux_Permutation st l :
    merge_sort_aux R st l ≡ₚ merge_stack_flatten st ++ l.
  Proof.
    revert st. induction l as [|?? IH]; simpl; intros.
    - by rewrite (right_id_L [] (++)), merge_stack_Permutation.
    - rewrite IH, merge_list_to_stack_Permutation; simpl.
      by rewrite Permutation_middle.
  Qed.
  Lemma Sorted_merge_sort l : Sorted R (merge_sort R l).
  Proof. apply Sorted_merge_sort_aux. by constructor. Qed.
  Lemma merge_sort_Permutation l : merge_sort R l ≡ₚ l.
  Proof. unfold merge_sort. by rewrite merge_sort_aux_Permutation. Qed.
  Lemma StronglySorted_merge_sort `{!Transitive R} l :
    StronglySorted R (merge_sort R l).
  Proof. auto using Sorted_StronglySorted, Sorted_merge_sort. Qed.
End merge_sort_correct.
