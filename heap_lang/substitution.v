From heap_lang Require Export lang.
From prelude Require Import stringmap.
Import heap_lang.

(** The tactic [simpl_subst] performs substitutions in the goal. Its behavior
can be tuned using instances of the type class [Closed e], which can be used
to mark that expressions are closed, and should thus not be substituted into. *)

Class Closed (e : expr) := closed : ∀ x v, subst e x v = e.
Class Subst (e : expr) (x : string) (v : val) (er : expr) :=
  do_subst : subst e x v = er.
Hint Mode Subst + + + - : typeclass_instances.

Ltac simpl_subst :=
  repeat match goal with
  | |- context [subst ?e ?x ?v] => progress rewrite (@do_subst e x v)
  | |- _ => progress csimpl
  end; fold of_val.

Arguments of_val : simpl never.
Hint Extern 10 (Subst (of_val _) _ _ _) => unfold of_val : typeclass_instances.
Hint Extern 10 (Closed (of_val _)) => unfold of_val : typeclass_instances.

Instance subst_fallthrough e x v : Subst e x v (subst e x v) | 1000.
Proof. done. Qed.

Class SubstIf (P : Prop) (e : expr) (x : string) (v : val) (er : expr) := {
  subst_if_true : P → subst e x v = er;
  subst_if_false : ¬P → e = er
}.
Hint Mode SubstIf + + + + - : typeclass_instances.
Definition subst_if_mk_true (P : Prop) x v e er :
  Subst e x v er → P → SubstIf P e x v er.
Proof. by split. Qed.
Definition subst_if_mk_false (P : Prop) x v e : ¬P → SubstIf P e x v e.
Proof. by split. Qed.

Ltac bool_decide_no_check := apply (bool_decide_unpack _); vm_cast_no_check I.

Hint Extern 0 (SubstIf ?P ?e ?x ?v _) =>
  match eval vm_compute in (bool_decide P) with
  | true => apply subst_if_mk_true; [|bool_decide_no_check]
  | false => apply subst_if_mk_false; bool_decide_no_check
  end : typeclass_instances.

Instance subst_closed e x v : Closed e → Subst e x v e | 0.
Proof. intros He; apply He. Qed.

Instance lit_closed l : Closed (Lit l).
Proof. done. Qed.
Instance loc_closed l : Closed (Loc l).
Proof. done. Qed.

Definition subst_var_eq y x v : x = y → Subst (Var y) x v (of_val v).
Proof. intros. by red; rewrite /= decide_True. Defined.
Definition subst_var_ne y x v : x ≠ y → Subst (Var y) x v (Var y).
Proof. intros. by red; rewrite /= decide_False. Defined.

Hint Extern 0 (Subst (Var ?y) ?x ?v _) =>
  match eval vm_compute in (bool_decide (x = y)) with
  | true => apply subst_var_eq; bool_decide_no_check
  | false => apply subst_var_ne; bool_decide_no_check
  end : typeclass_instances.

Instance subst_rec f y e x v er :
  SubstIf (BNamed x ≠ f ∧ BNamed x ≠ y) e x v er →
  Subst (Rec f y e) x v (Rec f y er).
Proof. intros [??]; red; f_equal/=; case_decide; auto. Qed.
Instance subst_case e0 x1 e1 x2 e2 x v e0r e1r e2r :
  Subst e0 x v e0r →
  SubstIf (BNamed x ≠ x1) e1 x v e1r → SubstIf (BNamed x ≠ x2) e2 x v e2r →
  Subst (Case e0 x1 e1 x2 e2) x v (Case e0r x1 e1r x2 e2r).
Proof. intros ? [??] [??]; red; f_equal/=; repeat case_decide; auto. Qed.

Instance subst_app e1 e2 x v e1r e2r :
  Subst e1 x v e1r → Subst e2 x v e2r → Subst (App e1 e2) x v (App e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Instance subst_unop op e x v er :
  Subst e x v er → Subst (UnOp op e) x v (UnOp op er).
Proof. by intros; red; f_equal/=. Qed.
Instance subst_binop op e1 e2 x v e1r e2r :
  Subst e1 x v e1r → Subst e2 x v e2r →
  Subst (BinOp op e1 e2) x v (BinOp op e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Instance subst_if e0 e1 e2 x v e0r e1r e2r :
  Subst e0 x v e0r → Subst e1 x v e1r → Subst e2 x v e2r →
  Subst (If e0 e1 e2) x v (If e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Instance subst_pair e1 e2 x v e1r e2r :
  Subst e1 x v e1r → Subst e2 x v e2r → Subst (Pair e1 e2) x v (Pair e1r e2r).
Proof. by intros ??; red; f_equal/=. Qed.
Instance subst_fst e x v er : Subst e x v er → Subst (Fst e) x v (Fst er).
Proof. by intros; red; f_equal/=. Qed.
Instance subst_snd e x v er : Subst e x v er → Subst (Snd e) x v (Snd er).
Proof. by intros; red; f_equal/=. Qed.
Instance subst_injL e x v er : Subst e x v er → Subst (InjL e) x v (InjL er).
Proof. by intros; red; f_equal/=. Qed.
Instance subst_injR e x v er : Subst e x v er → Subst (InjR e) x v (InjR er).
Proof. by intros; red; f_equal/=. Qed.
Instance subst_fork e x v er : Subst e x v er → Subst (Fork e) x v (Fork er).
Proof. by intros; red; f_equal/=. Qed.
Instance subst_alloc e x v er : Subst e x v er → Subst (Alloc e) x v (Alloc er).
Proof. by intros; red; f_equal/=. Qed.
Instance subst_load e x v er : Subst e x v er → Subst (Load e) x v (Load er).
Proof. by intros; red; f_equal/=. Qed.
Instance subst_store e1 e2 x v e1r e2r :
  Subst e1 x v e1r → Subst e2 x v e2r → Subst (Store e1 e2) x v (Store e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Instance subst_cas e0 e1 e2 x v e0r e1r e2r :
  Subst e0 x v e0r → Subst e1 x v e1r → Subst e2 x v e2r →
  Subst (Cas e0 e1 e2) x v (Cas e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.

Definition of_binder (mx : binder) : stringset :=
  match mx with BAnom => ∅ | BNamed x => {[ x ]} end.
Lemma elem_of_of_binder x mx: x ∈ of_binder mx ↔ mx = BNamed x.
Proof. destruct mx; set_solver. Qed.
Global Instance set_unfold_of_binder (mx : binder) x :
  SetUnfold (x ∈ of_binder mx) (mx = BNamed x).
Proof. constructor; destruct mx; set_solver. Qed.

(** * Solver for [Closed] *)
Fixpoint is_closed (X : stringset) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Rec f y e => is_closed (of_binder f ∪ of_binder y ∪ X) e
  | App e1 e2 => is_closed X e1 && is_closed X e2
  | Lit l => true
  | UnOp _ e => is_closed X e
  | BinOp _ e1 e2 => is_closed X e1 && is_closed X e2
  | If e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2
  | Pair e1 e2 => is_closed X e1 && is_closed X e2
  | Fst e => is_closed X e
  | Snd e => is_closed X e
  | InjL e => is_closed X e
  | InjR e => is_closed X e
  | Case e0 x1 e1 x2 e2 =>
     is_closed X e0 &&
     is_closed (of_binder x1 ∪ X) e1 && is_closed (of_binder x2 ∪ X) e2
  | Fork e => is_closed X e
  | Loc l => true
  | Alloc e => is_closed X e
  | Load e => is_closed X e
  | Store e1 e2 => is_closed X e1 && is_closed X e2
  | Cas e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2
  end.
Lemma is_closed_sound e : is_closed ∅ e → Closed e.
Proof.
  cut (∀ x v X, is_closed X e → x ∉ X → subst e x v = e).
  { intros help ? x v. by apply (help x v ∅). }
  intros x v; induction e; simpl; intros;
    repeat match goal with
    | _ => progress subst
    | _ => contradiction
    | H : Is_true (bool_decide _) |- _ => apply (bool_decide_unpack _) in H
    | H : Is_true (_ && _) |- _ => apply andb_True in H
    | H : _ ∧ _ |- _ => destruct H
    | _ => case_decide
    | _ => f_equal
    end; eauto;
    try match goal with
    | H : ∀ _, _ → _ ∉ _ → subst _ _ _ = _ |- _ =>
       eapply H; first done;
       rewrite !elem_of_union !elem_of_of_binder; intuition congruence
    end.
Qed.
Ltac solve_closed := apply is_closed_sound; vm_compute; exact I.

Global Opaque subst.
