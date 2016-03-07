From program_logic Require Export language.
From prelude Require Export strings.
From prelude Require Import gmap.

Module heap_lang.
Open Scope Z_scope.

(** Expressions and vals. *)
Definition loc := positive. (* Really, any countable type. *)

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit.
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | LeOp | LtOp | EqOp.

Inductive binder := BAnon | BNamed : string → binder.

Definition cons_binder (mx : binder) (X : list string) : list string :=
  match mx with BAnon => X | BNamed x => x :: X end.
Infix ":b:" := cons_binder (at level 60, right associativity).
Delimit Scope binder_scope with bind.
Bind Scope binder_scope with binder.
Instance binder_dec_eq (x1 x2 : binder) : Decision (x1 = x2).
Proof. solve_decision. Defined.

Instance set_unfold_cons_binder x mx X P :
  SetUnfold (x ∈ X) P → SetUnfold (x ∈ mx :b: X) (BNamed x = mx ∨ P).
Proof.
  constructor. rewrite -(set_unfold (x ∈ X) P).
  destruct mx; rewrite /= ?elem_of_cons; naive_solver.
Qed.

(** A typeclass for whether a variable is bound in a given
   context. Making this a typeclass means we can use tpeclass search
   to program solving these constraints, so this becomes extensible.
   Also, since typeclass search runs *after* unification, Coq has already
   inferred the X for us; if we were to go for embedded proof terms ot
   tactics, Coq would do things in the wrong order. *)
Class VarBound (x : string) (X : list string) :=
  var_bound : bool_decide (x ∈ X).
(* There is no need to restrict this hint to terms without evars, [vm_compute]
will fail in case evars are arround. *)
Hint Extern 0 (VarBound _ _) => vm_compute; exact I : typeclass_instances. 

Instance var_bound_proof_irrel x X : ProofIrrel (VarBound x X).
Proof. rewrite /VarBound. apply _. Qed.
Instance set_unfold_var_bound x X P :
  SetUnfold (x ∈ X) P → SetUnfold (VarBound x X) P.
Proof.
  constructor. by rewrite /VarBound bool_decide_spec (set_unfold (x ∈ X) P).
Qed.

Inductive expr (X : list string) :=
  (* Base lambda calculus *)
      (* Var is the only place where the terms contain a proof. The fact that they
       contain a proof at all is suboptimal, since this means two seeminlgy
       convertible terms could differ in their proofs. However, this also has
       some advantages:
       * We can make the [X] an index, so we can do non-dependent match.
       * In expr_weaken, we can push the proof all the way into Var, making
         sure that proofs never block computation. *)
  | Var (x : string) `{VarBound x X}
  | Rec (f x : binder) (e : expr (f :b: x :b: X))
  | App (e1 e2 : expr X)
  (* Base types and their operations *)
  | Lit (l : base_lit)
  | UnOp (op : un_op) (e : expr X)
  | BinOp (op : bin_op) (e1 e2 : expr X)
  | If (e0 e1 e2 : expr X)
  (* Products *)
  | Pair (e1 e2 : expr X)
  | Fst (e : expr X)
  | Snd (e : expr X)
  (* Sums *)
  | InjL (e : expr X)
  | InjR (e : expr X)
  | Case (e0 : expr X) (e1 : expr X) (e2 : expr X)
  (* Concurrency *)
  | Fork (e : expr X)
  (* Heap *)
  | Loc (l : loc)
  | Alloc (e : expr X)
  | Load (e : expr X)
  | Store (e1 : expr X) (e2 : expr X)
  | CAS (e0 : expr X) (e1 : expr X) (e2 : expr X).

Bind Scope expr_scope with expr.
Delimit Scope expr_scope with E.
Arguments Var {_} _ {_}.
Arguments Rec {_} _ _ _%E.
Arguments App {_} _%E _%E.
Arguments Lit {_} _.
Arguments UnOp {_} _ _%E.
Arguments BinOp {_} _ _%E _%E.
Arguments If {_} _%E _%E _%E.
Arguments Pair {_} _%E _%E.
Arguments Fst {_} _%E.
Arguments Snd {_} _%E.
Arguments InjL {_} _%E.
Arguments InjR {_} _%E.
Arguments Case {_} _%E _%E _%E.
Arguments Fork {_} _%E.
Arguments Loc {_} _.
Arguments Alloc {_} _%E.
Arguments Load {_} _%E.
Arguments Store {_} _%E _%E.
Arguments CAS {_} _%E _%E _%E.

Inductive val :=
  | RecV (f x : binder) (e : expr (f :b: x :b: []))
  | LitV (l : base_lit)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | LocV (l : loc).

Bind Scope val_scope with val.
Delimit Scope val_scope with V.
Arguments PairV _%V _%V.
Arguments InjLV _%V.
Arguments InjRV _%V.

Definition signal : val := RecV BAnon (BNamed "x") (Store (Var "x") (Lit (LitInt 1))).

Fixpoint of_val (v : val) : expr [] :=
  match v with
  | RecV f x e => Rec f x e
  | LitV l => Lit l
  | PairV v1 v2 => Pair (of_val v1) (of_val v2)
  | InjLV v => InjL (of_val v)
  | InjRV v => InjR (of_val v)
  | LocV l => Loc l
  end.

Fixpoint to_val (e : expr []) : option val :=
  match e with
  | Rec f x e => Some (RecV f x e)
  | Lit l => Some (LitV l)
  | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
  | InjL e => InjLV <$> to_val e
  | InjR e => InjRV <$> to_val e
  | Loc l => Some (LocV l)
  | _ => None
  end.

(** The state: heaps of vals. *)
Definition state := gmap loc val.

(** Evaluation contexts *)
Inductive ectx_item :=
  | AppLCtx (e2 : expr [])
  | AppRCtx (v1 : val)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (e2 : expr [])
  | BinOpRCtx (op : bin_op) (v1 : val)
  | IfCtx (e1 e2 : expr [])
  | PairLCtx (e2 : expr [])
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : expr []) (e2 : expr [])
  | AllocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr [])
  | StoreRCtx (v1 : val)
  | CasLCtx (e1 : expr [])  (e2 : expr [])
  | CasMCtx (v0 : val) (e2 : expr [])
  | CasRCtx (v0 : val) (v1 : val).

Notation ectx := (list ectx_item).

Definition fill_item (Ki : ectx_item) (e : expr []) : expr [] :=
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
Definition fill (K : ectx) (e : expr []) : expr [] := fold_right fill_item e K.

(** Substitution *)
(** We have [subst' e BAnon v = e] to deal with anonymous binders *)
Lemma wexpr_rec_prf {X Y} (H : X `included` Y) {f x} :
  f :b: x :b: X `included` f :b: x :b: Y.
Proof. set_solver. Qed.

Program Fixpoint wexpr {X Y} (H : X `included` Y) (e : expr X) : expr Y :=
  match e return expr Y with
  | Var x _ => @Var _ x _
  | Rec f x e => Rec f x (wexpr (wexpr_rec_prf H) e)
  | App e1 e2 => App (wexpr H e1) (wexpr H e2)
  | Lit l => Lit l
  | UnOp op e => UnOp op (wexpr H e)
  | BinOp op e1 e2 => BinOp op (wexpr H e1) (wexpr H e2)
  | If e0 e1 e2 => If (wexpr H e0) (wexpr H e1) (wexpr H e2)
  | Pair e1 e2 => Pair (wexpr H e1) (wexpr H e2)
  | Fst e => Fst (wexpr H e)
  | Snd e => Snd (wexpr H e)
  | InjL e => InjL (wexpr H e)
  | InjR e => InjR (wexpr H e)
  | Case e0 e1 e2 => Case (wexpr H e0) (wexpr H e1) (wexpr H e2)
  | Fork e => Fork (wexpr H e)
  | Loc l => Loc l
  | Alloc e => Alloc (wexpr H e)
  | Load  e => Load (wexpr H e)
  | Store e1 e2 => Store (wexpr H e1) (wexpr H e2)
  | CAS e0 e1 e2 => CAS (wexpr H e0) (wexpr H e1) (wexpr H e2)
  end.
Solve Obligations with set_solver.

Definition of_val' {X} (v : val) : expr X := wexpr (included_nil _) (of_val v).

Lemma wsubst_rec_true_prf {X Y x} (H : X `included` x :: Y) {f y}
    (Hfy :BNamed x ≠ f ∧ BNamed x ≠ y) :
  f :b: y :b: X `included` x :: f :b: y :b: Y.
Proof. set_solver. Qed.
Lemma wsubst_rec_false_prf {X Y x} (H : X `included` x :: Y) {f y}
    (Hfy : ¬(BNamed x ≠ f ∧ BNamed x ≠ y)) :
  f :b: y :b: X `included` f :b: y :b: Y.
Proof. move: Hfy=>/not_and_l [/dec_stable|/dec_stable]; set_solver. Qed.

Program Fixpoint wsubst {X Y} (x : string) (es : expr [])
    (H : X `included` x :: Y) (e : expr X)  : expr Y :=
  match e return expr Y with
  | Var y _ => if decide (x = y) then wexpr _ es else @Var _ y _
  | Rec f y e =>
     Rec f y $ match decide (BNamed x ≠ f ∧ BNamed x ≠ y) return _ with
               | left Hfy => wsubst x es (wsubst_rec_true_prf H Hfy) e
               | right Hfy => wexpr (wsubst_rec_false_prf H Hfy) e
               end
  | App e1 e2 => App (wsubst x es H e1) (wsubst x es H e2)
  | Lit l => Lit l
  | UnOp op e => UnOp op (wsubst x es H e)
  | BinOp op e1 e2 => BinOp op (wsubst x es H e1) (wsubst x es H e2)
  | If e0 e1 e2 => If (wsubst x es H e0) (wsubst x es H e1) (wsubst x es H e2)
  | Pair e1 e2 => Pair (wsubst x es H e1) (wsubst x es H e2)
  | Fst e => Fst (wsubst x es H e)
  | Snd e => Snd (wsubst x es H e)
  | InjL e => InjL (wsubst x es H e)
  | InjR e => InjR (wsubst x es H e)
  | Case e0 e1 e2 =>
     Case (wsubst x es H e0) (wsubst x es H e1) (wsubst x es H e2)
  | Fork e => Fork (wsubst x es H e)
  | Loc l => Loc l
  | Alloc e => Alloc (wsubst x es H e)
  | Load e => Load (wsubst x es H e)
  | Store e1 e2 => Store (wsubst x es H e1) (wsubst x es H e2)
  | CAS e0 e1 e2 => CAS (wsubst x es H e0) (wsubst x es H e1) (wsubst x es H e2)
  end.
Solve Obligations with set_solver.

Definition subst {X} (x : string) (es : expr []) (e : expr (x :: X)) : expr X :=
  wsubst x es (λ z, id) e.
Definition subst' {X} (mx : binder) (es : expr []) : expr (mx :b: X) → expr X :=
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

Inductive head_step : expr [] → state → expr [] → state → option (expr []) → Prop :=
  | BetaS f x e1 e2 v2 e' σ :
     to_val e2 = Some v2 →
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
     head_step (Alloc e) σ (Loc l) (<[l:=v]>σ) None
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load (Loc l)) σ (of_val v) σ None
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store (Loc l) e) σ (Lit LitUnit) (<[l:=v]>σ) None
  | CasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some vl → vl ≠ v1 →
     head_step (CAS (Loc l) e1 e2) σ (Lit $ LitBool false) σ None
  | CasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some v1 →
     head_step (CAS (Loc l) e1 e2) σ (Lit $ LitBool true) (<[l:=v2]>σ) None.

(** Atomic expressions *)
Definition atomic (e: expr []) : Prop :=
  match e with
  | Alloc e => is_Some (to_val e)
  | Load e => is_Some (to_val e)
  | Store e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
  | CAS e0 e1 e2 => is_Some (to_val e0) ∧ is_Some (to_val e1) ∧ is_Some (to_val e2)
  (* Make "skip" atomic *)
  | App (Rec _ _ (Lit _)) (Lit _) => True
  | _ => False
  end.

(** Close reduction under evaluation contexts.
We could potentially make this a generic construction. *)
Inductive prim_step (e1 : expr []) (σ1 : state)
    (e2 : expr []) (σ2: state) (ef: option (expr [])) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    head_step e1' σ1 e2' σ2 ef → prim_step e1 σ1 e2 σ2 ef.

(** Substitution *)
Lemma var_proof_irrel X x H1 H2 : @Var X x H1 = @Var X x H2.
Proof. f_equal. by apply (proof_irrel _). Qed.

Lemma wexpr_id X (H : X `included` X) e : wexpr H e = e.
Proof. induction e; f_equal/=; auto. by apply (proof_irrel _). Qed.
Lemma wexpr_proof_irrel X Y (H1 H2 : X `included` Y) e : wexpr H1 e = wexpr H2 e.
Proof.
  revert Y H1 H2; induction e; simpl; auto using var_proof_irrel with f_equal.
Qed.
Lemma wexpr_wexpr X Y Z (H1 : X `included` Y) (H2 : Y `included` Z) H3 e :
  wexpr H2 (wexpr H1 e) = wexpr H3 e.
Proof.
  revert Y Z H1 H2 H3.
  induction e; simpl; auto using var_proof_irrel with f_equal.
Qed.
Lemma wexpr_wexpr' X Y Z (H1 : X `included` Y) (H2 : Y `included` Z) e :
  wexpr H2 (wexpr H1 e) = wexpr (transitivity H1 H2) e.
Proof. apply wexpr_wexpr. Qed.

Lemma wsubst_proof_irrel X Y x es (H1 H2 : X `included` x :: Y) e :
  wsubst x es H1 e = wsubst x es H2 e.
Proof.
  revert Y H1 H2; induction e; simpl; intros; repeat case_decide;
    auto using var_proof_irrel, wexpr_proof_irrel with f_equal.
Qed.
Lemma wexpr_wsubst X Y Z x es (H1: X `included` x::Y) (H2: Y `included` Z) H3 e:
  wexpr H2 (wsubst x es H1 e) = wsubst x es H3 e.
Proof.
  revert Y Z H1 H2 H3.
  induction e; intros; repeat (case_decide || simplify_eq/=);
    auto using var_proof_irrel, wexpr_wexpr with f_equal.
Qed.
Lemma wsubst_wexpr X Y Z x es (H1: X `included` Y) (H2: Y `included` x::Z) H3 e:
  wsubst x es H2 (wexpr H1 e) = wsubst x es H3 e.
Proof.
  revert Y Z H1 H2 H3.
  induction e; intros; repeat (case_decide || simplify_eq/=);
    auto using var_proof_irrel, wexpr_wexpr with f_equal.
Qed.
Lemma wsubst_wexpr' X Y Z x es (H1: X `included` Y) (H2: Y `included` x::Z) e:
  wsubst x es H2 (wexpr H1 e) = wsubst x es (transitivity H1 H2) e.
Proof. apply wsubst_wexpr. Qed.

Lemma wsubst_closed X Y x es (H1 : X `included` x :: Y) H2 (e : expr X) :
  x ∉ X → wsubst x es H1 e = wexpr H2 e.
Proof.
  revert Y H1 H2.
  induction e; intros; repeat (case_decide || simplify_eq/=);
    auto using var_proof_irrel, wexpr_proof_irrel with f_equal set_solver.
  exfalso; set_solver.
Qed.
Lemma wsubst_closed_nil x es H (e : expr []) : wsubst x es H e = e.
Proof.
  rewrite -{2}(wexpr_id _ (reflexivity []) e).
  apply wsubst_closed, not_elem_of_nil.
Qed.

Lemma of_val'_closed (v : val) :
  of_val' v = of_val v.
Proof. by rewrite /of_val' wexpr_id. Qed.

(** to_val propagation.
    TODO: automatically appliy in wp_tactics? *)
Lemma to_val_InjL e v : to_val e = Some v → to_val (InjL e) = Some (InjLV v).
Proof. move=>H. simpl. by rewrite H. Qed.
Lemma to_val_InjR e v : to_val e = Some v → to_val (InjR e) = Some (InjRV v).
Proof. move=>H. simpl. by rewrite H. Qed.
Lemma to_val_Pair e1 e2 v1 v2 :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  to_val (Pair e1 e2) = Some (PairV v1 v2).
Proof. move=>H1 H2. simpl. by rewrite H1 H2. Qed.

(** Basic properties about the language *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by induction v; simplify_option_eq. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert e v. cut (∀ X (e : expr X) (H : X = ∅) v,
    to_val (eq_rect _ expr e _ H) = Some v → of_val v = eq_rect _ expr e _ H).
  { intros help e v. apply (help ∅ e eq_refl). }
  intros X e; induction e; intros HX ??; simplify_option_eq;
    repeat match goal with
    | IH : ∀ _ : ∅ = ∅, _ |- _ => specialize (IH eq_refl); simpl in IH
    end; auto with f_equal.
Qed.

Instance: Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Instance ectx_fill_inj K : Inj (=) (=) (fill K).
Proof. red; induction K as [|Ki K IH]; naive_solver. Qed.

Lemma fill_app K1 K2 e : fill (K1 ++ K2) e = fill K1 (fill K2 e).
Proof. revert e; induction K1; simpl; auto with f_equal. Qed.

Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  intros [v' Hv']; revert v' Hv'.
  induction K as [|[]]; intros; simplify_option_eq; eauto.
Qed.

Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
Proof. rewrite !eq_None_not_Some; eauto using fill_val. Qed.

Lemma val_head_stuck e1 σ1 e2 σ2 ef :
  head_step e1 σ1 e2 σ2 ef → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma val_stuck e1 σ1 e2 σ2 ef : prim_step e1 σ1 e2 σ2 ef → to_val e1 = None.
Proof. intros [??? -> -> ?]; eauto using fill_not_val, val_head_stuck. Qed.

Lemma atomic_not_val e : atomic e → to_val e = None.
Proof. destruct e; naive_solver. Qed.

Lemma atomic_fill_item Ki e : atomic (fill_item Ki e) → is_Some (to_val e).
Proof.
  intros. destruct Ki; simplify_eq/=; destruct_and?;
    repeat (case_match || contradiction); eauto.
Qed.

Lemma atomic_fill K e : atomic (fill K e) → to_val e = None → K = [].
Proof.
  destruct K as [|Ki K]; [done|].
  rewrite eq_None_not_Some=> /= ? []; eauto using atomic_fill_item, fill_val.
Qed.

Lemma atomic_head_step e1 σ1 e2 σ2 ef :
  atomic e1 → head_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
Proof.
  destruct 2; simpl; rewrite ?to_of_val; try by eauto. subst.
  unfold subst'; repeat (case_match || contradiction || simplify_eq/=); eauto.
Qed.

Lemma atomic_step e1 σ1 e2 σ2 ef :
  atomic e1 → prim_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
Proof.
  intros Hatomic [K e1' e2' -> -> Hstep].
  assert (K = []) as -> by eauto 10 using atomic_fill, val_head_stuck.
  naive_solver eauto using atomic_head_step.
Qed.

Lemma head_ctx_step_val Ki e σ1 e2 σ2 ef :
  head_step (fill_item Ki e) σ1 e2 σ2 ef → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq/=;
    repeat match goal with
    | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
    end; auto.
Qed.

(* When something does a step, and another decomposition of the same expression
has a non-val [e] in the hole, then [K] is a left sub-context of [K'] - in
other words, [e] also contains the reducible expression *)
Lemma step_by_val K K' e1 e1' σ1 e2 σ2 ef :
  fill K e1 = fill K' e1' → to_val e1 = None → head_step e1' σ1 e2 σ2 ef →
  K `prefix_of` K'.
Proof.
  intros Hfill Hred Hnval; revert K' Hfill.
  induction K as [|Ki K IH]; simpl; intros K' Hfill; auto using prefix_of_nil.
  destruct K' as [|Ki' K']; simplify_eq/=.
  { exfalso; apply (eq_None_not_Some (to_val (fill K e1)));
      eauto using fill_not_val, head_ctx_step_val. }
  cut (Ki = Ki'); [naive_solver eauto using prefix_of_cons|].
  eauto using fill_item_no_val_inj, val_head_stuck, fill_not_val.
Qed.

Lemma alloc_fresh e v σ :
  let l := fresh (dom _ σ) in
  to_val e = Some v → head_step (Alloc e) σ (Loc l) (<[l:=v]>σ) None.
Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset _)), is_fresh. Qed.

(** Equality and other typeclass stuff *)
Instance base_lit_dec_eq (l1 l2 : base_lit) : Decision (l1 = l2).
Proof. solve_decision. Defined.
Instance un_op_dec_eq (op1 op2 : un_op) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance bin_op_dec_eq (op1 op2 : bin_op) : Decision (op1 = op2).
Proof. solve_decision. Defined.

Fixpoint expr_beq {X Y} (e : expr X) (e' : expr Y) : bool :=
  match e, e' with
  | Var x _, Var x' _ => bool_decide (x = x')
  | Rec f x e, Rec f' x' e' =>
     bool_decide (f = f') && bool_decide (x = x') && expr_beq e e'
  | App e1 e2, App e1' e2' | Pair e1 e2, Pair e1' e2' |
    Store e1 e2, Store e1' e2' => expr_beq e1 e1' && expr_beq e2 e2'
  | Lit l, Lit l' => bool_decide (l = l')
  | UnOp op e, UnOp op' e' => bool_decide (op = op') && expr_beq e e'
  | BinOp op e1 e2, BinOp op' e1' e2' =>
     bool_decide (op = op') && expr_beq e1 e1' && expr_beq e2 e2'
  | If e0 e1 e2, If e0' e1' e2' | Case e0 e1 e2, Case e0' e1' e2' |
    CAS e0 e1 e2, CAS e0' e1' e2' =>
     expr_beq e0 e0' && expr_beq e1 e1' && expr_beq e2 e2'
  | Fst e, Fst e' | Snd e, Snd e' | InjL e, InjL e' | InjR e, InjR e' |
    Fork e, Fork e' | Alloc e, Alloc e' | Load e, Load e' => expr_beq e e'
  | Loc l, Loc l' => bool_decide (l = l')
  | _, _ => false
  end.
Lemma expr_beq_correct {X} (e1 e2 : expr X) : expr_beq e1 e2 ↔ e1 = e2.
Proof.
  split.
  * revert e2; induction e1; intros [] * ?; simpl in *;
      destruct_and?; subst; repeat f_equal/=; auto; try apply proof_irrel.
  * intros ->. induction e2; naive_solver.
Qed.
Instance expr_dec_eq {X} (e1 e2 : expr X) : Decision (e1 = e2).
Proof.
 refine (cast_if (decide (expr_beq e1 e2))); by rewrite -expr_beq_correct.
Defined.
Instance val_dec_eq (v1 v2 : val) : Decision (v1 = v2).
Proof.
 refine (cast_if (decide (of_val v1 = of_val v2))); abstract naive_solver.
Defined.

Instance expr_inhabited X : Inhabited (expr X) := populate (Lit LitUnit).
Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
End heap_lang.

(** Language *)
Program Canonical Structure heap_lang : language := {|
  expr := heap_lang.expr []; val := heap_lang.val; state := heap_lang.state;
  of_val := heap_lang.of_val; to_val := heap_lang.to_val;
  atomic := heap_lang.atomic; prim_step := heap_lang.prim_step;
|}.
Solve Obligations with eauto using heap_lang.to_of_val, heap_lang.of_to_val,
  heap_lang.val_stuck, heap_lang.atomic_not_val, heap_lang.atomic_step.

Global Instance heap_lang_ctx K : LanguageCtx heap_lang (heap_lang.fill K).
Proof.
  split.
  - eauto using heap_lang.fill_not_val.
  - intros ????? [K' e1' e2' Heq1 Heq2 Hstep].
    by exists (K ++ K') e1' e2'; rewrite ?heap_lang.fill_app ?Heq1 ?Heq2.
  - intros e1 σ1 e2 σ2 ? Hnval [K'' e1'' e2'' Heq1 -> Hstep].
    destruct (heap_lang.step_by_val
      K K'' e1 e1'' σ1 e2'' σ2 ef) as [K' ->]; eauto.
    rewrite heap_lang.fill_app in Heq1; apply (inj _) in Heq1.
    exists (heap_lang.fill K' e2''); rewrite heap_lang.fill_app; split; auto.
    econstructor; eauto.
Qed.

Global Instance heap_lang_ctx_item Ki :
  LanguageCtx heap_lang (heap_lang.fill_item Ki).
Proof. change (LanguageCtx heap_lang (heap_lang.fill [Ki])). apply _. Qed.

(* Prefer heap_lang names over language names. *)
Export heap_lang.
