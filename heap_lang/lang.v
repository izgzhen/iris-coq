From iris.program_logic Require Export ectx_language ectxi_language.
From iris.algebra Require Export cofe.
From iris.prelude Require Export strings.
From iris.prelude Require Import gmap.

Module heap_lang.
Open Scope Z_scope.

(** Expressions and vals. *)
Definition loc := positive. (* Really, any countable type. *)

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc).
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | LeOp | LtOp | EqOp.

Inductive binder := BAnon | BNamed : string → binder.
Delimit Scope binder_scope with bind.
Bind Scope binder_scope with binder.
Definition cons_binder (mx : binder) (X : list string) : list string :=
  match mx with BAnon => X | BNamed x => x :: X end.
Infix ":b:" := cons_binder (at level 60, right associativity).
Instance binder_dec_eq (x1 x2 : binder) : Decision (x1 = x2).
Proof. solve_decision. Defined.

Instance set_unfold_cons_binder x mx X P :
  SetUnfold (x ∈ X) P → SetUnfold (x ∈ mx :b: X) (BNamed x = mx ∨ P).
Proof.
  constructor. rewrite -(set_unfold (x ∈ X) P).
  destruct mx; rewrite /= ?elem_of_cons; naive_solver.
Qed.

Inductive expr :=
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | Lit (l : base_lit)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  (* Concurrency *)
  | Fork (e : expr)
  (* Heap *)
  | Alloc (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  | CAS (e0 : expr) (e1 : expr) (e2 : expr).

Bind Scope expr_scope with expr.
Delimit Scope expr_scope with E.
Arguments Rec _ _ _%E.
Arguments App _%E _%E.
Arguments Lit _.
Arguments UnOp _ _%E.
Arguments BinOp _ _%E _%E.
Arguments If _%E _%E _%E.
Arguments Pair _%E _%E.
Arguments Fst _%E.
Arguments Snd _%E.
Arguments InjL _%E.
Arguments InjR _%E.
Arguments Case _%E _%E _%E.
Arguments Fork _%E.
Arguments Alloc _%E.
Arguments Load _%E.
Arguments Store _%E _%E.
Arguments CAS _%E _%E _%E.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed (f :b: x :b: X) e
  | Lit _ => true
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Alloc e | Load e =>
     is_closed X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 =>
     is_closed X e1 && is_closed X e2
  | If e0 e1 e2 | Case e0 e1 e2 | CAS e0 e1 e2 =>
     is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
Proof. rewrite /Closed. apply _. Qed.
Instance closed_decision env e : Decision (Closed env e).
Proof. rewrite /Closed. apply _. Qed.

Inductive val :=
  | RecV (f x : binder) (e : expr) `{!Closed (f :b: x :b: []) e}
  | LitV (l : base_lit)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Bind Scope val_scope with val.
Delimit Scope val_scope with V.
Arguments PairV _%V _%V.
Arguments InjLV _%V.
Arguments InjRV _%V.

Fixpoint of_val (v : val) : expr :=
  match v with
  | RecV f x e _ => Rec f x e
  | LitV l => Lit l
  | PairV v1 v2 => Pair (of_val v1) (of_val v2)
  | InjLV v => InjL (of_val v)
  | InjRV v => InjR (of_val v)
  end.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | Rec f x e =>
     if decide (Closed (f :b: x :b: []) e) then Some (RecV f x e) else None
  | Lit l => Some (LitV l)
  | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
  | InjL e => InjLV <$> to_val e
  | InjR e => InjRV <$> to_val e
  | _ => None
  end.

(** The state: heaps of vals. *)
Definition state := gmap loc val.

(** Evaluation contexts *)
Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (e2 : expr)
  | BinOpRCtx (op : bin_op) (v1 : val)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : expr) (e2 : expr)
  | AllocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | CasLCtx (e1 : expr)  (e2 : expr)
  | CasMCtx (v0 : val) (e2 : expr)
  | CasRCtx (v0 : val) (v1 : val).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx e2 => App e e2
  | AppRCtx v1 => App (of_val v1) e
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (of_val v1) e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx e2 => Pair e e2
  | PairRCtx v1 => Pair (of_val v1) e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | AllocCtx => Alloc e
  | LoadCtx => Load e
  | StoreLCtx e2 => Store e e2 
  | StoreRCtx v1 => Store (of_val v1) e
  | CasLCtx e1 e2 => CAS e e1 e2
  | CasMCtx v0 e2 => CAS (of_val v0) e e2
  | CasRCtx v0 v1 => CAS (of_val v0) (of_val v1) e
  end.

(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Var y => if decide (x = y) then es else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x es e else e
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | Lit l => Lit l
  | UnOp op e => UnOp op (subst x es e)
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | If e0 e1 e2 => If (subst x es e0) (subst x es e1) (subst x es e2)
  | Pair e1 e2 => Pair (subst x es e1) (subst x es e2)
  | Fst e => Fst (subst x es e)
  | Snd e => Snd (subst x es e)
  | InjL e => InjL (subst x es e)
  | InjR e => InjR (subst x es e)
  | Case e0 e1 e2 => Case (subst x es e0) (subst x es e1) (subst x es e2)
  | Fork e => Fork (subst x es e)
  | Alloc e => Alloc (subst x es e)
  | Load e => Load (subst x es e)
  | Store e1 e2 => Store (subst x es e1) (subst x es e2)
  | CAS e0 e1 e2 => CAS (subst x es e0) (subst x es e1) (subst x es e2)
  end.

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (l : base_lit) : option base_lit :=
  match op, l with
  | NegOp, LitBool b => Some (LitBool (negb b))
  | MinusUnOp, LitInt n => Some (LitInt (- n))
  | _, _ => None
  end.

Definition bin_op_eval (op : bin_op) (l1 l2 : base_lit) : option base_lit :=
  match op, l1, l2 with
  | PlusOp, LitInt n1, LitInt n2 => Some $ LitInt (n1 + n2)
  | MinusOp, LitInt n1, LitInt n2 => Some $ LitInt (n1 - n2)
  | LeOp, LitInt n1, LitInt n2 => Some $ LitBool $ bool_decide (n1 ≤ n2)
  | LtOp, LitInt n1, LitInt n2 => Some $ LitBool $ bool_decide (n1 < n2)
  | EqOp, LitInt n1, LitInt n2 => Some $ LitBool $ bool_decide (n1 = n2)
  | _, _, _ => None
  end.

Inductive head_step : expr → state → expr → state → option (expr) → Prop :=
  | BetaS f x e1 e2 v2 e' σ :
     to_val e2 = Some v2 →
     Closed (f :b: x :b: []) e1 →
     e' = subst' x (of_val v2) (subst' f (Rec f x e1) e1) →
     head_step (App (Rec f x e1) e2) σ e' σ None
  | UnOpS op l l' σ :
     un_op_eval op l = Some l' → 
     head_step (UnOp op (Lit l)) σ (Lit l') σ None
  | BinOpS op l1 l2 l' σ :
     bin_op_eval op l1 l2 = Some l' → 
     head_step (BinOp op (Lit l1) (Lit l2)) σ (Lit l') σ None
  | IfTrueS e1 e2 σ :
     head_step (If (Lit $ LitBool true) e1 e2) σ e1 σ None
  | IfFalseS e1 e2 σ :
     head_step (If (Lit $ LitBool false) e1 e2) σ e2 σ None
  | FstS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Fst (Pair e1 e2)) σ e1 σ None
  | SndS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Snd (Pair e1 e2)) σ e2 σ None
  | CaseLS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case (InjL e0) e1 e2) σ (App e1 e0) σ None
  | CaseRS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case (InjR e0) e1 e2) σ (App e2 e0) σ None
  | ForkS e σ:
     head_step (Fork e) σ (Lit LitUnit) σ (Some e)
  | AllocS e v σ l :
     to_val e = Some v → σ !! l = None →
     head_step (Alloc e) σ (Lit $ LitLoc l) (<[l:=v]>σ) None
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load (Lit $ LitLoc l)) σ (of_val v) σ None
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store (Lit $ LitLoc l) e) σ (Lit LitUnit) (<[l:=v]>σ) None
  | CasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some vl → vl ≠ v1 →
     head_step (CAS (Lit $ LitLoc l) e1 e2) σ (Lit $ LitBool false) σ None
  | CasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some v1 →
     head_step (CAS (Lit $ LitLoc l) e1 e2) σ (Lit $ LitBool true) (<[l:=v2]>σ) None.

(** Atomic expressions *)
Definition atomic (e: expr) : bool :=
  match e with
  | Alloc e => bool_decide (is_Some (to_val e))
  | Load e => bool_decide (is_Some (to_val e))
  | Store e1 e2 => bool_decide (is_Some (to_val e1) ∧ is_Some (to_val e2))
  | CAS e0 e1 e2 =>
    bool_decide (is_Some (to_val e0) ∧ is_Some (to_val e1) ∧ is_Some (to_val e2))
  (* Make "skip" atomic *)
  | App (Rec _ _ (Lit _)) (Lit _) => true
  | _ => false
  end.

(** Basic properties about the language *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma val_stuck e1 σ1 e2 σ2 ef : head_step e1 σ1 e2 σ2 ef → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma atomic_not_val e : atomic e → to_val e = None.
Proof. by destruct e. Qed.

Lemma atomic_fill_item Ki e : atomic (fill_item Ki e) → is_Some (to_val e).
Proof.
  intros. destruct Ki; simplify_eq/=; destruct_and?;
    repeat (simpl || case_match || contradiction); eauto.
Qed.

Lemma atomic_step e1 σ1 e2 σ2 ef :
  atomic e1 → head_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
Proof.
  destruct 2; simpl; rewrite ?to_of_val; try by eauto. subst.
  unfold subst'; repeat (case_match || contradiction || simplify_eq/=); eauto.
Qed.

Lemma head_ctx_step_val Ki e σ1 e2 σ2 ef :
  head_step (fill_item Ki e) σ1 e2 σ2 ef → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; by eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq/=;
    repeat match goal with
    | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
    end; auto.
Qed.

Lemma alloc_fresh e v σ :
  let l := fresh (dom _ σ) in
  to_val e = Some v → head_step (Alloc e) σ (Lit (LitLoc l)) (<[l:=v]>σ) None.
Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset _)), is_fresh. Qed.

(** Value type class *)
Class IntoValue (e : expr) (v : val) := into_value : to_val e = Some v.
Instance into_value_of_val v : IntoValue (of_val v) v.
Proof. by rewrite /IntoValue to_of_val. Qed.
Instance into_value_rec f x e `{!Closed (f :b: x :b: []) e} :
  IntoValue (Rec f x e) (RecV f x e).
Proof.
  rewrite /IntoValue /=; case_decide; last done.
  do 2 f_equal. by apply (proof_irrel).
Qed.
Instance into_value_lit l : IntoValue (Lit l) (LitV l).
Proof. done. Qed.
Instance into_value_pair e1 e2 v1 v2 :
  IntoValue e1 v1 → IntoValue e2 v2 → IntoValue (Pair e1 e2) (PairV v1 v2).
Proof. by rewrite /IntoValue /= => -> /= ->. Qed.
Instance into_value_injl e v : IntoValue e v → IntoValue (InjL e) (InjLV v).
Proof. by rewrite /IntoValue /= => ->. Qed.
Instance into_value_injr e v : IntoValue e v → IntoValue (InjR e) (InjRV v).
Proof. by rewrite /IntoValue /= => ->. Qed.

(** Closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X `included` Y → is_closed Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Instance of_val_closed X v : Closed X (of_val v).
Proof.
  apply is_closed_weaken with []; last set_solver.
  induction v; simpl; auto.
Qed.

Lemma closed_subst X e x es : Closed X e → x ∉ X → subst x es e = e.
Proof.
  rewrite /Closed. revert X.
  induction e=> X /=; rewrite ?bool_decide_spec ?andb_True=> ??;
    repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
Qed.

Lemma closed_nil_subst e x es : Closed [] e → subst x es e = e.
Proof. intros. apply closed_subst with []; set_solver. Qed.

Lemma closed_nil_closed X e : Closed [] e → Closed X e.
Proof. intros. by apply is_closed_weaken with [], included_nil. Qed.
Hint Immediate closed_nil_closed : typeclass_instances.

Instance closed_of_val X v : Closed X (of_val v).
Proof. apply of_val_closed. Qed.
Instance closed_rec X f x e : Closed (f :b: x :b: X) e → Closed X (Rec f x e).
Proof. done. Qed.
Lemma closed_var X x : bool_decide (x ∈ X) → Closed X (Var x).
Proof. done. Qed.
Hint Extern 1000 (Closed _ (Var _)) =>
  apply closed_var; vm_compute; exact I : typeclass_instances.

Section closed.
  Context (X : list string).
  Notation C := (Closed X).

  Global Instance closed_lit l : C (Lit l).
  Proof. done. Qed.
  Global Instance closed_unop op e : C e → C (UnOp op e).
  Proof. done. Qed.
  Global Instance closed_fst e : C e → C (Fst e).
  Proof. done. Qed.
  Global Instance closed_snd e : C e → C (Snd e).
  Proof. done. Qed.
  Global Instance closed_injl e : C e → C (InjL e).
  Proof. done. Qed.
  Global Instance closed_injr e : C e → C (InjR e).
  Proof. done. Qed.
  Global Instance closed_fork e : C e → C (Fork e).
  Proof. done. Qed.
  Global Instance closed_load e : C e → C (Load e).
  Proof. done. Qed.
  Global Instance closed_alloc e : C e → C (Alloc e).
  Proof. done. Qed.
  Global Instance closed_app e1 e2 : C e1 → C e2 → C (App e1 e2).
  Proof. intros. by rewrite /Closed /= !andb_True. Qed.
  Global Instance closed_binop op e1 e2 : C e1 → C e2 → C (BinOp op e1 e2).
  Proof. intros. by rewrite /Closed /= !andb_True. Qed.
  Global Instance closed_pair e1 e2 : C e1 → C e2 → C (Pair e1 e2).
  Proof. intros. by rewrite /Closed /= !andb_True. Qed.
  Global Instance closed_store e1 e2 : C e1 → C e2 → C (Store e1 e2).
  Proof. intros. by rewrite /Closed /= !andb_True. Qed.
  Global Instance closed_if e0 e1 e2 : C e0 → C e1 → C e2 → C (If e0 e1 e2).
  Proof. intros. by rewrite /Closed /= !andb_True. Qed.
  Global Instance closed_case e0 e1 e2 : C e0 → C e1 → C e2 → C (Case e0 e1 e2).
  Proof. intros. by rewrite /Closed /= !andb_True. Qed.
  Global Instance closed_cas e0 e1 e2 : C e0 → C e1 → C e2 → C (CAS e0 e1 e2).
  Proof. intros. by rewrite /Closed /= !andb_True. Qed.
End closed.

(** Equality and other typeclass stuff *)
Instance base_lit_dec_eq (l1 l2 : base_lit) : Decision (l1 = l2).
Proof. solve_decision. Defined.
Instance un_op_dec_eq (op1 op2 : un_op) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance bin_op_dec_eq (op1 op2 : bin_op) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance expr_dec_eq (e1 e2 : expr) : Decision (e1 = e2).
Proof. solve_decision. Defined.
Instance val_dec_eq (v1 v2 : val) : Decision (v1 = v2).
Proof.
 refine (cast_if (decide (of_val v1 = of_val v2))); abstract naive_solver.
Defined.

Instance expr_inhabited : Inhabited (expr) := populate (Lit LitUnit).
Instance val_inhabited : Inhabited val := populate (LitV LitUnit).

Canonical Structure stateC := leibnizC state.
Canonical Structure valC := leibnizC val.
Canonical Structure exprC := leibnizC expr.
End heap_lang.

(** Language *)
Program Instance heap_ectxi_lang :
  EctxiLanguage
    (heap_lang.expr) heap_lang.val heap_lang.ectx_item heap_lang.state := {|
  of_val := heap_lang.of_val; to_val := heap_lang.to_val;
  fill_item := heap_lang.fill_item;
  atomic := heap_lang.atomic; head_step := heap_lang.head_step;
|}.
Solve Obligations with eauto using heap_lang.to_of_val, heap_lang.of_to_val,
  heap_lang.val_stuck, heap_lang.atomic_not_val, heap_lang.atomic_step,
  heap_lang.fill_item_val, heap_lang.atomic_fill_item,
  heap_lang.fill_item_no_val_inj, heap_lang.head_ctx_step_val.

Canonical Structure heap_lang := ectx_lang (heap_lang.expr).

(* Prefer heap_lang names over ectx_language names. *)
Export heap_lang.
