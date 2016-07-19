From iris.heap_lang Require Export lang.
Import heap_lang.

Module W.
Inductive expr :=
  | ClosedExpr (e : heap_lang.expr) `{!Closed [] e}
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

Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | ClosedExpr e H => @ClosedExpr e H
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

Fixpoint to_expr (e : expr) : heap_lang.expr :=
  match e with
  | ClosedExpr e _ => e
  | Var x => heap_lang.Var x
  | Rec f x e => heap_lang.Rec f x (to_expr e)
  | App e1 e2 => heap_lang.App (to_expr e1) (to_expr e2)
  | Lit l => heap_lang.Lit l
  | UnOp op e => heap_lang.UnOp op (to_expr e)
  | BinOp op e1 e2 => heap_lang.BinOp op (to_expr e1) (to_expr e2)
  | If e0 e1 e2 => heap_lang.If (to_expr e0) (to_expr e1) (to_expr e2)
  | Pair e1 e2 => heap_lang.Pair (to_expr e1) (to_expr e2)
  | Fst e => heap_lang.Fst (to_expr e)
  | Snd e => heap_lang.Snd (to_expr e)
  | InjL e => heap_lang.InjL (to_expr e)
  | InjR e => heap_lang.InjR (to_expr e)
  | Case e0 e1 e2 => heap_lang.Case (to_expr e0) (to_expr e1) (to_expr e2)
  | Fork e => heap_lang.Fork (to_expr e)
  | Alloc e => heap_lang.Alloc (to_expr e)
  | Load e => heap_lang.Load (to_expr e)
  | Store e1 e2 => heap_lang.Store (to_expr e1) (to_expr e2)
  | CAS e0 e1 e2 => heap_lang.CAS (to_expr e0) (to_expr e1) (to_expr e2)
  end.

Ltac of_expr e :=
  lazymatch e with
  | heap_lang.Var ?x => constr:(Var x)
  | heap_lang.Rec ?f ?x ?e => let e := of_expr e in constr:(Rec f x e)
  | heap_lang.App ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(App e1 e2)
  | heap_lang.Lit ?l => constr:(Lit l)
  | heap_lang.UnOp ?op ?e => let e := of_expr e in constr:(UnOp op e)
  | heap_lang.BinOp ?op ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(BinOp op e1 e2)
  | heap_lang.If ?e0 ?e1 ?e2 =>
     let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(If e0 e1 e2)
  | heap_lang.Pair ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Pair e1 e2)
  | heap_lang.Fst ?e => let e := of_expr e in constr:(Fst e)
  | heap_lang.Snd ?e => let e := of_expr e in constr:(Snd e)
  | heap_lang.InjL ?e => let e := of_expr e in constr:(InjL e)
  | heap_lang.InjR ?e => let e := of_expr e in constr:(InjR e)
  | heap_lang.Case ?e0 ?e1 ?e2 =>
     let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(Case e0 e1 e2)
  | heap_lang.Fork ?e => let e := of_expr e in constr:(Fork e)
  | heap_lang.Alloc ?e => let e := of_expr e in constr:(Alloc e)
  | heap_lang.Load ?e => let e := of_expr e in constr:(Load e)
  | heap_lang.Store ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Store e1 e2)
  | heap_lang.CAS ?e0 ?e1 ?e2 =>
     let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(CAS e0 e1 e2)
  | to_expr ?e => e
  | of_val ?v => constr:(ClosedExpr (of_val v))
  (* is_var e; constr:(Closed e) does not work *)
  | _ => constr:(ltac:(is_var e; exact (ClosedExpr e)))
  end.

Lemma to_expr_subst x er e :
  to_expr (subst x er e) = heap_lang.subst x (to_expr er) (to_expr e).
Proof.
  induction e; simpl;
    repeat case_decide; f_equal; auto using closed_nil_subst, eq_sym.
Qed.
End W.

(** * The tactic *)
Ltac simpl_subst :=
  csimpl;
  repeat match goal with
  | |- context [subst ?x ?er ?e] =>
      let er' := W.of_expr er in let e' := W.of_expr e in
      change (subst x er e) with (subst x (W.to_expr er') (W.to_expr e'));
      rewrite <-(W.to_expr_subst x); simpl (* ssr rewrite is slower *)
  end;
  unfold W.to_expr.
Arguments W.to_expr : simpl never.
Arguments subst : simpl never.
