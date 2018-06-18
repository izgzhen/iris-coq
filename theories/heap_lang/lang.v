From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.algebra Require Export ofe.
From stdpp Require Export strings.
From stdpp Require Import gmap.
Set Default Proof Using "Type".

Module heap_lang.
Open Scope Z_scope.

(** Expressions and vals. *)
Definition loc := positive. (* Really, any countable type. *)

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc).
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp. (* Relations *)

Inductive binder := BAnon | BNamed : string → binder.
Delimit Scope binder_scope with bind.
Bind Scope binder_scope with binder.
Definition cons_binder (mx : binder) (X : list string) : list string :=
  match mx with BAnon => X | BNamed x => x :: X end.
Infix ":b:" := cons_binder (at level 60, right associativity).
Instance binder_eq_dec_eq : EqDecision binder.
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
  | CAS (e0 : expr) (e1 : expr) (e2 : expr)
  | FAA (e1 : expr) (e2 : expr).

Bind Scope expr_scope with expr.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed (f :b: x :b: X) e
  | Lit _ => true
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Alloc e | Load e =>
     is_closed X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 | FAA e1 e2 =>
     is_closed X e1 && is_closed X e2
  | If e0 e1 e2 | Case e0 e1 e2 | CAS e0 e1 e2 =>
     is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
Instance closed_proof_irrel X e : ProofIrrel (Closed X e).
Proof. rewrite /Closed. apply _. Qed.
Instance closed_dec X e : Decision (Closed X e).
Proof. rewrite /Closed. apply _. Defined.

Inductive val :=
  | RecV (f x : binder) (e : expr) `{!Closed (f :b: x :b: []) e}
  | LitV (l : base_lit)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Bind Scope val_scope with val.

Fixpoint of_val (v : val) : expr :=
  match v with
  | RecV f x e => Rec f x e
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

(** Equality and other typeclass stuff *)
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

Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Instance expr_eq_dec : EqDecision expr.
Proof. solve_decision. Defined.
Instance val_eq_dec : EqDecision val.
Proof.
 refine (λ v v', cast_if (decide (of_val v = of_val v'))); abstract naive_solver.
Defined.

Instance base_lit_countable : Countable base_lit.
Proof.
 refine (inj_countable' (λ l, match l with
  | LitInt n => inl (inl n) | LitBool b => inl (inr b)
  | LitUnit => inr (inl ()) | LitLoc l => inr (inr l)
  end) (λ l, match l with
  | inl (inl n) => LitInt n | inl (inr b) => LitBool b
  | inr (inl ()) => LitUnit | inr (inr l) => LitLoc l
  end) _); by intros [].
Qed.
Instance un_op_finite : Countable un_op.
Proof.
 refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 end)
  (λ n, match n with 0 => NegOp | _ => MinusUnOp end) _); by intros [].
Qed.
Instance bin_op_countable : Countable bin_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
  | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
  | LeOp => 10 | LtOp => 11 | EqOp => 12
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | _ => EqOp
  end) _); by intros [].
Qed.
Instance binder_countable : Countable binder.
Proof.
 refine (inj_countable' (λ b, match b with BNamed s => Some s | BAnon => None end)
  (λ b, match b with Some s => BNamed s | None => BAnon end) _); by intros [].
Qed.
Instance expr_countable : Countable expr.
Proof.
 set (enc := fix go e :=
  match e with
  | Var x => GenLeaf (inl (inl x))
  | Rec f x e => GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
  | App e1 e2 => GenNode 1 [go e1; go e2]
  | Lit l => GenLeaf (inr (inl l))
  | UnOp op e => GenNode 2 [GenLeaf (inr (inr (inl op))); go e]
  | BinOp op e1 e2 => GenNode 3 [GenLeaf (inr (inr (inr op))); go e1; go e2]
  | If e0 e1 e2 => GenNode 4 [go e0; go e1; go e2]
  | Pair e1 e2 => GenNode 5 [go e1; go e2]
  | Fst e => GenNode 6 [go e]
  | Snd e => GenNode 7 [go e]
  | InjL e => GenNode 8 [go e]
  | InjR e => GenNode 9 [go e]
  | Case e0 e1 e2 => GenNode 10 [go e0; go e1; go e2]
  | Fork e => GenNode 11 [go e]
  | Alloc e => GenNode 12 [go e]
  | Load e => GenNode 13 [go e]
  | Store e1 e2 => GenNode 14 [go e1; go e2]
  | CAS e0 e1 e2 => GenNode 15 [go e0; go e1; go e2]
  | FAA e1 e2 => GenNode 16 [go e1; go e2]
  end).
 set (dec := fix go e :=
  match e with
  | GenLeaf (inl (inl x)) => Var x
  | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => Rec f x (go e)
  | GenNode 1 [e1; e2] => App (go e1) (go e2)
  | GenLeaf (inr (inl l)) => Lit l
  | GenNode 2 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
  | GenNode 3 [GenLeaf (inr (inr (inr op))); e1; e2] => BinOp op (go e1) (go e2)
  | GenNode 4 [e0; e1; e2] => If (go e0) (go e1) (go e2)
  | GenNode 5 [e1; e2] => Pair (go e1) (go e2)
  | GenNode 6 [e] => Fst (go e)
  | GenNode 7 [e] => Snd (go e)
  | GenNode 8 [e] => InjL (go e)
  | GenNode 9 [e] => InjR (go e)
  | GenNode 10 [e0; e1; e2] => Case (go e0) (go e1) (go e2)
  | GenNode 11 [e] => Fork (go e)
  | GenNode 12 [e] => Alloc (go e)
  | GenNode 13 [e] => Load (go e)
  | GenNode 14 [e1; e2] => Store (go e1) (go e2)
  | GenNode 15 [e0; e1; e2] => CAS (go e0) (go e1) (go e2)
  | GenNode 16 [e1; e2] => FAA (go e1) (go e2)
  | _ => Lit LitUnit (* dummy *)
  end).
 refine (inj_countable' enc dec _). intros e. induction e; f_equal/=; auto.
Qed.
Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

Instance expr_inhabited : Inhabited expr := populate (Lit LitUnit).
Instance val_inhabited : Inhabited val := populate (LitV LitUnit).

Canonical Structure stateC := leibnizC state.
Canonical Structure valC := leibnizC val.
Canonical Structure exprC := leibnizC expr.

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
  | CasLCtx (e1 : expr) (e2 : expr)
  | CasMCtx (v0 : val) (e2 : expr)
  | CasRCtx (v0 : val) (v1 : val)
  | FaaLCtx (e2 : expr)
  | FaaRCtx (v1 : val).

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
  | FaaLCtx e2 => FAA e e2
  | FaaRCtx v1 => FAA (of_val v1) e
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
  | FAA e1 e2 => FAA (subst x es e1) (subst x es e2)
  end.

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : base_lit :=
  match op with
  | PlusOp => LitInt (n1 + n2)
  | MinusOp => LitInt (n1 - n2)
  | MultOp => LitInt (n1 * n2)
  | QuotOp => LitInt (n1 `quot` n2)
  | RemOp => LitInt (n1 `rem` n2)
  | AndOp => LitInt (Z.land n1 n2)
  | OrOp => LitInt (Z.lor n1 n2)
  | XorOp => LitInt (Z.lxor n1 n2)
  | ShiftLOp => LitInt (n1 ≪ n2)
  | ShiftROp => LitInt (n1 ≫ n2)
  | LeOp => LitBool (bool_decide (n1 ≤ n2))
  | LtOp => LitBool (bool_decide (n1 < n2))
  | EqOp => LitBool (bool_decide (n1 = n2))
  end.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then Some $ LitV $ LitBool $ bool_decide (v1 = v2) else
  match v1, v2 with
  | LitV (LitInt n1), LitV (LitInt n2) => Some $ LitV $ bin_op_eval_int op n1 n2
  | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
  | _, _ => None
  end.

Inductive head_step : expr → state → expr → state → list (expr) → Prop :=
  | BetaS f x e1 e2 v2 e' σ :
     to_val e2 = Some v2 →
     Closed (f :b: x :b: []) e1 →
     e' = subst' x (of_val v2) (subst' f (Rec f x e1) e1) →
     head_step (App (Rec f x e1) e2) σ e' σ []
  | UnOpS op e v v' σ :
     to_val e = Some v →
     un_op_eval op v = Some v' →
     head_step (UnOp op e) σ (of_val v') σ []
  | BinOpS op e1 e2 v1 v2 v' σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     bin_op_eval op v1 v2 = Some v' →
     head_step (BinOp op e1 e2) σ (of_val v') σ []
  | IfTrueS e1 e2 σ :
     head_step (If (Lit $ LitBool true) e1 e2) σ e1 σ []
  | IfFalseS e1 e2 σ :
     head_step (If (Lit $ LitBool false) e1 e2) σ e2 σ []
  | FstS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Fst (Pair e1 e2)) σ e1 σ []
  | SndS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Snd (Pair e1 e2)) σ e2 σ []
  | CaseLS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case (InjL e0) e1 e2) σ (App e1 e0) σ []
  | CaseRS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case (InjR e0) e1 e2) σ (App e2 e0) σ []
  | ForkS e σ:
     head_step (Fork e) σ (Lit LitUnit) σ [e]
  | AllocS e v σ l :
     to_val e = Some v → σ !! l = None →
     head_step (Alloc e) σ (Lit $ LitLoc l) (<[l:=v]>σ) []
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load (Lit $ LitLoc l)) σ (of_val v) σ []
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store (Lit $ LitLoc l) e) σ (Lit LitUnit) (<[l:=v]>σ) []
  | CasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some vl → vl ≠ v1 →
     head_step (CAS (Lit $ LitLoc l) e1 e2) σ (Lit $ LitBool false) σ []
  | CasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some v1 →
     head_step (CAS (Lit $ LitLoc l) e1 e2) σ (Lit $ LitBool true) (<[l:=v2]>σ) []
   | FaaS l i1 e2 i2 σ :
     to_val e2 = Some (LitV (LitInt i2)) →
     σ !! l = Some (LitV (LitInt i1)) →
     head_step (FAA (Lit $ LitLoc l) e2) σ (Lit $ LitInt i1) (<[l:=LitV (LitInt (i1 + i2))]>σ) [].


(** Basic properties about the language *)
Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e1 σ1 e2 σ2 efs : head_step e1 σ1 e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 e2 σ2 efs :
  head_step (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_val e).
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
  let l := fresh (dom (gset loc) σ) in
  to_val e = Some v → head_step (Alloc e) σ (Lit (LitLoc l)) (<[l:=v]>σ) [].
Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset loc)), is_fresh. Qed.

(* Misc *)
Lemma to_val_rec f x e `{!Closed (f :b: x :b: []) e} :
  to_val (Rec f x e) = Some (RecV f x e).
Proof. rewrite /to_val. case_decide=> //. do 2 f_equal; apply proof_irrel. Qed.

(** Closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_of_val X v : is_closed X (of_val v).
Proof. apply is_closed_weaken_nil. induction v; simpl; auto. Qed.

Lemma is_closed_to_val X e v : to_val e = Some v → is_closed X e.
Proof. intros <-%of_to_val. apply is_closed_of_val. Qed.

Lemma is_closed_subst X e x es :
  is_closed [] es → is_closed (x :: X) e → is_closed X (subst x es e).
Proof.
  intros ?. revert X.
  induction e=> X /= ?; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
Qed.
Lemma is_closed_do_subst' X e x es :
  is_closed [] es → is_closed (x :b: X) e → is_closed X (subst' x es e).
Proof. destruct x; eauto using is_closed_subst. Qed.

(* Substitution *)
Lemma subst_is_closed X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  revert X. induction e=> X /=; rewrite ?bool_decide_spec ?andb_True=> ??;
    repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_nil e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply subst_is_closed with []; set_solver. Qed.

Lemma subst_subst e x es es' :
  Closed [] es' → subst x es (subst x es' e) = subst x es' e.
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst' e x es es' :
  Closed [] es' → subst' x es (subst' x es' e) = subst' x es' e.
Proof. destruct x; simpl; auto using subst_subst. Qed.

Lemma subst_subst_ne e x y es es' :
  Closed [] es → Closed [] es' → x ≠ y →
  subst x es (subst y es' e) = subst y es' (subst x es e).
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using eq_sym, subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst_ne' e x y es es' :
  Closed [] es → Closed [] es' → x ≠ y →
  subst' x es (subst' y es' e) = subst' y es' (subst' x es e).
Proof. destruct x, y; simpl; auto using subst_subst_ne with congruence. Qed.

Lemma subst_rec' f y e x es :
  x = f ∨ x = y ∨ x = BAnon →
  subst' x es (Rec f y e) = Rec f y e.
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.
Lemma subst_rec_ne' f y e x es :
  (x ≠ f ∨ f = BAnon) → (x ≠ y ∨ y = BAnon) →
  subst' x es (Rec f y e) = Rec f y (subst' x es e).
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.

Lemma heap_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.
End heap_lang.

(** Language *)
Canonical Structure heap_ectxi_lang := EctxiLanguage heap_lang.heap_lang_mixin.
Canonical Structure heap_ectx_lang := EctxLanguageOfEctxi heap_ectxi_lang.
Canonical Structure heap_lang := LanguageOfEctx heap_ectx_lang.

(* Prefer heap_lang names over ectx_language names. *)
Export heap_lang.

(** Define some derived forms *)
Notation Lam x e := (Rec BAnon x e) (only parsing).
Notation Let x e1 e2 := (App (Lam x e2) e1) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation LamV x e := (RecV BAnon x e) (only parsing).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)) (only parsing).
Notation SeqCtx e2 := (LetCtx BAnon e2) (only parsing).
Notation Match e0 x1 e1 x2 e2 := (Case e0 (Lam x1 e1) (Lam x2 e2)) (only parsing).

Notation Skip := (Seq (Lit LitUnit) (Lit LitUnit)).
