From iris.heap_lang Require Export lang.
Import heap_lang.

(** The tactic [simpl_subst] performs substitutions in the goal. Its behavior
can be tuned by declaring [Subst] instances. *)
(** * Substitution *)
Class Subst (x : string) (es : expr) (e : expr) (er : expr) :=
  do_subst : subst x es e = er.
Hint Mode Subst + + + - : typeclass_instances.

(* Variables *)
Lemma do_subst_var_eq x er : Subst x er (Var x) er.
Proof. intros; red; simpl. by case_decide. Qed.
Lemma do_subst_var_neq x y er : bool_decide (x ≠ y) → Subst x er (Var y) (Var y).
Proof. rewrite bool_decide_spec. intros; red; simpl. by case_decide. Qed.

Hint Extern 0 (Subst ?x ?v (Var ?y) _) =>
  first [apply do_subst_var_eq
        |apply do_subst_var_neq, I] : typeclass_instances.

(** Rec *)
Lemma do_subst_rec_true {x es f y e er} :
  bool_decide (BNamed x ≠ f ∧ BNamed x ≠ y) →
  Subst x es e er → Subst x es (Rec f y e) (Rec f y er).
Proof. rewrite bool_decide_spec. intros; red; f_equal/=; by case_decide. Qed.
Lemma do_subst_rec_false {x es f y e} :
  bool_decide (¬(BNamed x ≠ f ∧ BNamed x ≠ y)) →
  Subst x es (Rec f y e) (Rec f y e).
Proof. rewrite bool_decide_spec. intros; red; f_equal/=; by case_decide. Qed.

Local Ltac bool_decide_no_check := vm_cast_no_check I.
Hint Extern 0 (Subst ?x ?v (Rec ?f ?y ?e) _) =>
  match eval vm_compute in (bool_decide (BNamed x ≠ f ∧ BNamed x ≠ y)) with
  | true => eapply (do_subst_rec_true ltac:(bool_decide_no_check))
  | false => eapply (do_subst_rec_false ltac:(bool_decide_no_check))
  end : typeclass_instances.

Lemma do_subst_closed x es e : Closed [] e → Subst x es e e.
Proof. apply closed_nil_subst. Qed.
Hint Extern 10 (Subst ?x ?v ?e _) =>
  is_var e; class_apply do_subst_closed : typeclass_instances.

(* Values *)
Instance do_subst_of_val x es v : Subst x es (of_val v) (of_val v) | 0.
Proof. eapply closed_nil_subst, of_val_closed. Qed.

(* Boring connectives *)
Section subst.
Context (x : string) (es : expr).
Notation Sub := (Subst x es).

(* Ground terms *)
Global Instance do_subst_lit l : Sub (Lit l) (Lit l).
Proof. done. Qed.
Global Instance do_subst_app e1 e2 e1r e2r :
  Sub e1 e1r → Sub e2 e2r → Sub (App e1 e2) (App e1r e2r).
Proof. intros; red; f_equal/=; apply: do_subst. Qed.
Global Instance do_subst_unop op e er : Sub e er → Sub (UnOp op e) (UnOp op er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_subst_binop op e1 e2 e1r e2r :
  Sub e1 e1r → Sub e2 e2r → Sub (BinOp op e1 e2) (BinOp op e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_subst_if e0 e1 e2 e0r e1r e2r :
  Sub e0 e0r → Sub e1 e1r → Sub e2 e2r → Sub (If e0 e1 e2) (If e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_subst_pair e1 e2 e1r e2r :
  Sub e1 e1r → Sub e2 e2r → Sub (Pair e1 e2) (Pair e1r e2r).
Proof. by intros ??; red; f_equal/=. Qed.
Global Instance do_subst_fst e er : Sub e er → Sub (Fst e) (Fst er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_subst_snd e er : Sub e er → Sub (Snd e) (Snd er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_subst_injL e er : Sub e er → Sub (InjL e) (InjL er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_subst_injR e er : Sub e er → Sub (InjR e) (InjR er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_subst_case e0 e1 e2 e0r e1r e2r :
  Sub e0 e0r → Sub e1 e1r → Sub e2 e2r → Sub (Case e0 e1 e2) (Case e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_subst_fork e er : Sub e er → Sub (Fork e) (Fork er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_subst_alloc e er : Sub e er → Sub (Alloc e) (Alloc er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_subst_load e er : Sub e er → Sub (Load e) (Load er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_subst_store e1 e2 e1r e2r :
  Sub e1 e1r → Sub e2 e2r → Sub (Store e1 e2) (Store e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_subst_cas e0 e1 e2 e0r e1r e2r :
  Sub e0 e0r → Sub e1 e1r → Sub e2 e2r → Sub (CAS e0 e1 e2) (CAS e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
End subst.

(** * The tactic *)
Ltac simpl_subst :=
  repeat match goal with
  | |- context [subst ?x ?es ?e] => progress rewrite (@do_subst x es e)
  | |- _ => progress csimpl
  end.
Arguments subst : simpl never.
