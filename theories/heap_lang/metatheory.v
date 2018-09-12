From iris.heap_lang Require Export lang.
From stdpp Require Import gmap.

(* This file contains some metatheory about the heap_lang language,
  which is not needed for verifying programs. *)

(* Closed expressions and values. *)
Fixpoint is_closed_expr (X : list string) (e : expr) : bool :=
  match e with
  | Val v => is_closed_val v
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed_expr (f :b: x :b: X) e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Alloc e | Load e =>
     is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 | FAA e1 e2
  | ResolveProph e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2 | CAS e0 e1 e2 =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | NewProph => true
  end
with is_closed_val (v : val) : bool :=
  match v with
  | LitV _ => true
  | RecV f x e => is_closed_expr (f :b: x :b: []) e
  | PairV v1 v2 => is_closed_val v1 && is_closed_val v2
  | InjLV v | InjRV v => is_closed_val v
  end.

Lemma is_closed_weaken X Y e : is_closed_expr X e → X ⊆ Y → is_closed_expr Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma is_closed_weaken_nil X e : is_closed_expr [] e → is_closed_expr X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_subst X e x v :
  is_closed_val v → is_closed_expr (x :: X) e → is_closed_expr X (subst x v e).
Proof.
  intros Hv. revert X.
  induction e=> X /= ?; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
Qed.
Lemma is_closed_subst' X e x v :
  is_closed_val v → is_closed_expr (x :b: X) e → is_closed_expr X (subst' x v e).
Proof. destruct x; eauto using is_closed_subst. Qed.

(* Substitution *)
Lemma subst_is_closed X e x es : is_closed_expr X e → x ∉ X → subst x es e = e.
Proof.
  revert X. induction e=> X /=; rewrite ?bool_decide_spec ?andb_True=> ??;
    repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_nil e x v : is_closed_expr [] e → subst x v e = e.
Proof. intros. apply subst_is_closed with []; set_solver. Qed.

Lemma subst_subst e x v v' :
  subst x v (subst x v' e) = subst x v' e.
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst' e x v v' :
  subst' x v (subst' x v' e) = subst' x v' e.
Proof. destruct x; simpl; auto using subst_subst. Qed.

Lemma subst_subst_ne e x y v v' :
  x ≠ y → subst x v (subst y v' e) = subst y v' (subst x v e).
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using eq_sym, subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst_ne' e x y v v' :
  x ≠ y → subst' x v (subst' y v' e) = subst' y v' (subst' x v e).
Proof. destruct x, y; simpl; auto using subst_subst_ne with congruence. Qed.

Lemma subst_rec' f y e x v :
  x = f ∨ x = y ∨ x = BAnon →
  subst' x v (Rec f y e) = Rec f y e.
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.
Lemma subst_rec_ne' f y e x v :
  (x ≠ f ∨ f = BAnon) → (x ≠ y ∨ y = BAnon) →
  subst' x v (Rec f y e) = Rec f y (subst' x v e).
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.

(* The stepping relation preserves closedness *)
Lemma head_step_is_closed e1 σ1 obs e2 σ2 es :
  is_closed_expr [] e1 →
  (∀ x v, σ1.(heap) !! x = Some v → is_closed_val v) →
  head_step e1 σ1 obs e2 σ2 es →

  is_closed_expr [] e2 ∧ Forall (is_closed_expr []) es ∧
  (∀ x v, σ2.(heap) !! x = Some v → is_closed_val v).
Proof.
  intros Cl1 Clσ1 STEP.
  destruct STEP; simpl in *; split_and!; try by naive_solver.
  - subst. repeat apply is_closed_subst'; naive_solver.
  - unfold un_op_eval in *. repeat case_match; naive_solver.
  - unfold bin_op_eval, bin_op_eval_bool in *. repeat case_match; naive_solver.
  - intros ??.
    match goal with
    | |- context [<[?l1 := _]>_!! ?l2] => destruct (decide (l1 = l2)) as [->|]
    end; rewrite ?lookup_insert ?lookup_insert_ne; naive_solver.
  - intros ??.
    match goal with
    | |- context [<[?l1 := _]>_!! ?l2] => destruct (decide (l1 = l2)) as [->|]
    end; rewrite ?lookup_insert ?lookup_insert_ne; naive_solver.
  - intros ??.
    match goal with
    | |- context [<[?l1 := _]>_!! ?l2] => destruct (decide (l1 = l2)) as [->|]
    end; rewrite ?lookup_insert ?lookup_insert_ne; naive_solver.
  - intros ??.
    match goal with
    | |- context [<[?l1 := _]>_!! ?l2] => destruct (decide (l1 = l2)) as [->|]
    end; rewrite ?lookup_insert ?lookup_insert_ne; naive_solver.
Qed.
