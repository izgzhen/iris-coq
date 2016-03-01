From program_logic Require Export language.
From prelude Require Export strings stringmap.
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

(* expr X is the type of expressions with free variables bounded by X.
   I removed the "empty binder" hack since it does not go well with
   proof irrelevance of the proof required for [Var]. If we really want
   that back, we should change the binders in [Rec] to "option string". *)
Inductive expr (X : stringset) : Type :=
  (* Base lambda calculus *)
  | Var (x : string) {H : x ∈ X} : expr X
  | Rec (f x : string) (e : expr (X ∪ {[ f ; x ]})) : expr X
  | App (e1 e2 : expr X) : expr X
  (* Base types and their operations *)
  | Lit (l : base_lit) : expr X
  | UnOp (op : un_op) (e : expr X) : expr X
  | BinOp (op : bin_op) (e1 e2 : expr X) : expr X
  | If (e0 e1 e2 : expr X) : expr X
  (* Products *)
  | Pair (e1 e2 : expr X) : expr X
  | Fst (e : expr X) : expr X
  | Snd (e : expr X) : expr X
  (* Sums *)
  | InjL (e : expr X) : expr X
  | InjR (e : expr X) : expr X
  | Case (e0 e1 e2 : expr X) : expr X
  (* Concurrency *)
  | Fork (e : expr X) : expr X
  (* Heap *)
  | Loc (l : loc) : expr X
  | Alloc (e : expr X) : expr X
  | Load (e : expr X) : expr X
  | Store (e1 e2 : expr X) : expr X
  | Cas (e0 e1 e2 : expr X) : expr X.

Inductive val :=
  | RecV (f x : string) (e : expr {[ f ; x ]})
  | LitV (l : base_lit)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | LocV (l : loc).

Global Instance base_lit_dec_eq (l1 l2 : base_lit) : Decision (l1 = l2).
Proof. solve_decision. Defined.
Global Instance un_op_dec_eq (op1 op2 : un_op) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Global Instance bin_op_dec_eq (op1 op2 : bin_op) : Decision (op1 = op2).
Proof. solve_decision. Defined.
(*Global Instance expr_dec_eq {X} (e1 e2 : expr X) : Decision (e1 = e2).
Proof. solve_decision. Defined.
Global Instance val_dec_eq (v1 v2 : val) : Decision (v1 = v2).
Proof. solve_decision. Defined.*)

Delimit Scope lang_scope with L.
Bind Scope lang_scope with expr val.

Definition expr_cast {X1 X2} {H : X1 = X2} (e : expr X1) : expr X2 :=
  eq_rect _ (λ X, expr X) e _ H.

Program Fixpoint expr_weaken_def {X1 X2 : stringset} (e : expr X1) :
  X1 ⊆ X2 → expr X2 :=
  match e in expr _ return X1 ⊆ X2 → expr X2 with
  | Var x Hx => λ H, Var X2 x
  | Rec f x e => λ H, Rec X2 f x (expr_weaken_def e _)
  | App e1 e2 => λ H, App X2 (expr_weaken_def e1 H) (expr_weaken_def e2 H)
  | Lit l => λ H, Lit X2 l
  | UnOp op e => λ H, UnOp X2 op (expr_weaken_def e H)
  | BinOp op e1 e2 => λ H, BinOp X2 op (expr_weaken_def e1 H) (expr_weaken_def e2 H)
  | If e0 e1 e2 => λ H, If X2 (expr_weaken_def e0 H) (expr_weaken_def e1 H) (expr_weaken_def e2 H)
  | Pair e1 e2 => λ H, Pair X2 (expr_weaken_def e1 H) (expr_weaken_def e2 H)
  | Fst e => λ H, Fst X2 (expr_weaken_def e H)
  | Snd e => λ H, Snd X2 (expr_weaken_def e H)
  | InjL e => λ H, InjL X2 (expr_weaken_def e H)
  | InjR e => λ H, InjR X2 (expr_weaken_def e H)
  | Case e0 e1 e2 => λ H, Case X2 (expr_weaken_def e0 H) (expr_weaken_def e1 H) (expr_weaken_def e2 H)
  | Fork e => λ H, Fork X2 (expr_weaken_def e H)
  | Loc l => λ H, Loc X2 l
  | Alloc e => λ H, Alloc X2 (expr_weaken_def e H)
  | Load  e => λ H, Load X2 (expr_weaken_def e H)
  | Store e1 e2 => λ H, Store X2 (expr_weaken_def e1 H) (expr_weaken_def e2 H)
  | Cas e0 e1 e2 => λ H, Cas X2 (expr_weaken_def e0 H) (expr_weaken_def e1 H) (expr_weaken_def e2 H)
  end.
Solve Obligations with set_solver.

Definition expr_weaken {X1 X2 : stringset} {H : X1 ⊆ X2} (e : expr X1) :=
  expr_weaken_def e H.

Program Fixpoint of_val (v : val) : expr ∅ :=
  match v return expr ∅ with
  | RecV f x e => Rec ∅ f x (expr_cast e)
  | LitV l => Lit ∅ l
  | PairV v1 v2 => Pair ∅ (of_val v1) (of_val v2)
  | InjLV v => InjL ∅ (of_val v)
  | InjRV v => InjR ∅ (of_val v)
  | LocV l => Loc ∅ l
  end.
Solve Obligations with set_solver.

Fixpoint to_val {X} (e : expr X) : option val :=
  match e return option val with
  | Rec f x e => match decide (X ∪ {[ f ; x ]} ⊆ {[ f ; x ]}) return _ with
                 | left H => Some (RecV f x (expr_weaken e (H:=H)))
                 | right _ => None
                 end
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
  | AppLCtx (e2 : expr ∅)
  | AppRCtx (v1 : val)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (e2 : expr ∅)
  | BinOpRCtx (op : bin_op) (v1 : val)
  | IfCtx (e1 e2 : expr ∅)
  | PairLCtx (e2 : expr ∅)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : expr ∅) (e2 : expr ∅)
  | AllocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr ∅)
  | StoreRCtx (v1 : val)
  | CasLCtx (e1 : expr ∅)  (e2 : expr ∅)
  | CasMCtx (v0 : val) (e2 : expr ∅)
  | CasRCtx (v0 : val) (v1 : val).

Notation ectx := (list ectx_item).

Definition fill_item (Ki : ectx_item) (e : expr ∅) : expr ∅ :=
  match Ki return expr ∅ with
  | AppLCtx e2 => App ∅ e e2
  | AppRCtx v1 => App ∅ (of_val v1) e
  | UnOpCtx op => UnOp ∅ op e
  | BinOpLCtx op e2 => BinOp ∅ op e e2
  | BinOpRCtx op v1 => BinOp ∅ op (of_val v1) e
  | IfCtx e1 e2 => If ∅ e e1 e2
  | PairLCtx e2 => Pair ∅ e e2
  | PairRCtx v1 => Pair ∅ (of_val v1) e
  | FstCtx => Fst ∅ e
  | SndCtx => Snd ∅ e
  | InjLCtx => InjL ∅ e
  | InjRCtx => InjR ∅ e
  | CaseCtx e1 e2 => Case ∅ e e1 e2
  | AllocCtx => Alloc ∅ e
  | LoadCtx => Load ∅ e
  | StoreLCtx e2 => Store ∅ e e2
  | StoreRCtx v1 => Store ∅ (of_val v1) e
  | CasLCtx e1 e2 => Cas ∅ e e1 e2
  | CasMCtx v0 e2 => Cas ∅ (of_val v0) e e2
  | CasRCtx v0 v1 => Cas ∅ (of_val v0) (of_val v1) e
  end.

Definition fill (K : ectx) (e : expr ∅) : expr ∅ := fold_right fill_item e K.

(** Substitution *)
Program Fixpoint subst {X} (x : string) (v : val) (e : expr X) :
    expr (X ∖ {[ x ]}) :=
  match e return _ with
  | Var y Hx => if decide (x = y) then expr_weaken $ of_val v
                                   else Var _ y
  | Rec f y e => Rec _ f y (if decide (x ≠ f ∧ x ≠ y)
                            then expr_cast (subst x v e)
                            else expr_cast e)
  | App e1 e2 => App _ (subst x v e1) (subst x v e2)
  | Lit l => Lit _ l
  | UnOp op e => UnOp _ op (subst x v e)
  | BinOp op e1 e2 => BinOp _ op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If _ (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair _ (subst x v e1) (subst x v e2)
  | Fst e => Fst _ (subst x v e)
  | Snd e => Snd _ (subst x v e)
  | InjL e => InjL _ (subst x v e)
  | InjR e => InjR _ (subst x v e)
  | Case e0 e1 e2 =>
     Case _ (subst x v e0) (subst x v e1) (subst x v e2)
  | Fork e => Fork _ (subst x v e)
  | Loc l => Loc _ l
  | Alloc e => Alloc _ (subst x v e)
  | Load e => Load _ (subst x v e)
  | Store e1 e2 => Store _ (subst x v e1) (subst x v e2)
  | Cas e0 e1 e2 => Cas _ (subst x v e0) (subst x v e1) (subst x v e2)
  end.
Next Obligation. set_solver. Qed.
Next Obligation. set_solver. Qed.
Next Obligation. set_solver. Qed.
(* FIXME fix this *)
Next Obligation.
  intros ??????? [H%dec_stable|H%dec_stable]%not_and_l; subst.
  - apply elem_of_equiv_L=>x. split; intro; last set_solver.
    destruct (decide (x = f)); set_solver.
  - apply elem_of_equiv_L=>x. split; intro; last set_solver.
    destruct (decide (x = y)); set_solver.
Qed.
                 
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

(* The equalities we need for substitution and some other lemmas. *)
Lemma stringset_eq_1 {X : stringset} :
  X = ∅ ∪ X.
Proof. set_solver. Qed.
Lemma stringset_eq_2 {f x : string} :
  (({[f; x]} ∖ {[f]}) ∖ {[x]}) = (∅ : stringset).
Proof. set_solver. Qed.
Lemma stringset_subseteq_1 {X : stringset} :
  ∅ ⊆ X.
Proof. set_solver. Qed.

Inductive head_step : expr ∅ → state → expr ∅ → state → option (expr ∅) → Prop :=
  | BetaS (f x : string) (e1 : expr {[ f ; x ]}) (e2 : expr ∅) v2 (σ : state) :
     to_val e2 = Some v2 →
     head_step (App ∅ (Rec _ f x (expr_cast (H:=stringset_eq_1) e1)) e2) σ
       (expr_cast (H:=stringset_eq_2) $ subst x v2 (subst f (RecV f x e1) e1)) σ None
  | UnOpS op l l' σ :
     un_op_eval op l = Some l' → 
     head_step (UnOp ∅ op (Lit ∅ l)) σ (Lit ∅ l') σ None
  | BinOpS op l1 l2 l' σ :
     bin_op_eval op l1 l2 = Some l' → 
     head_step (BinOp ∅ op (Lit ∅ l1) (Lit ∅ l2)) σ (Lit ∅ l') σ None
  | IfTrueS e1 e2 σ :
     head_step (If ∅ (Lit ∅ $ LitBool true) e1 e2) σ e1 σ None
  | IfFalseS e1 e2 σ :
     head_step (If ∅ (Lit ∅ $ LitBool false) e1 e2) σ e2 σ None
  | FstS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Fst ∅ (Pair ∅ e1 e2)) σ e1 σ None
  | SndS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Snd ∅ (Pair ∅ e1 e2)) σ e2 σ None
  | CaseLS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case ∅ (InjL ∅ e0) e1 e2) σ (App ∅ e1 (of_val v0)) σ None
  | CaseRS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case ∅ (InjR ∅ e0) e1 e2) σ (App ∅ e2 (of_val v0)) σ None
  | ForkS e σ:
     head_step (Fork ∅ e) σ (Lit ∅ LitUnit) σ (Some e)
  | AllocS e v σ l :
     to_val e = Some v → σ !! l = None →
     head_step (Alloc ∅ e) σ (Loc ∅ l) (<[l:=v]>σ) None
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load ∅ (Loc ∅ l)) σ (of_val v) σ None
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store ∅ (Loc ∅ l) e) σ (Lit ∅ LitUnit) (<[l:=v]>σ) None
  | CasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some vl → vl ≠ v1 →
     head_step (Cas ∅ (Loc ∅ l) e1 e2) σ (Lit ∅ $ LitBool false) σ None
  | CasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some v1 →
     head_step (Cas ∅ (Loc ∅ l) e1 e2) σ (Lit ∅ $ LitBool true) (<[l:=v2]>σ) None.

(** Atomic expressions *)
Definition atomic (e: expr ∅) : Prop :=
  match e with
  | Alloc e => is_Some (to_val e)
  | Load e => is_Some (to_val e)
  | Store e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
  | Cas e0 e1 e2 => is_Some (to_val e0) ∧ is_Some (to_val e1) ∧ is_Some (to_val e2)
  (* Make "skip" atomic *)
  | App (Rec _ _ (Lit _)) (Lit _) => True
  | _ => False
  end.

(** Close reduction under evaluation contexts.
We could potentially make this a generic construction. *)
Inductive prim_step
    (e1 : expr ∅) (σ1 : state) (e2 : expr ∅) (σ2: state) (ef: option (expr ∅)) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    head_step e1' σ1 e2' σ2 ef → prim_step e1 σ1 e2 σ2 ef.

(** Properties of the cast operators *)
Lemma not_or_l {P Q : Prop} `{Decision P} : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q.
Proof. destruct (decide P); tauto. Qed.
Lemma not_or_r {P Q : Prop} `{Decision Q} : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q.
Proof. destruct (decide Q); tauto. Qed.

Lemma expr_weaken_id {X : stringset} {H : X ⊆ X} (e : expr X) :
  expr_weaken (H:=H) e = e.
Proof.
  induction e; simpl; by (f_equal; try apply proof_irrel; eauto).
Qed.

Lemma expr_weaken_cast_id {X Y : stringset} {H1 : Y ⊆ X} {H2 : X = Y} (e : expr X) :
  expr_weaken (H:=H1) (expr_cast (H:=H2) e) = e.
Proof.
  destruct H2. by apply expr_weaken_id.
Qed.

Lemma expr_weaken_cast_weaken_id {X Y Z : stringset} {H1 : Z ⊆ X} {H2 : Y = Z} {H3 : X ⊆ Y} (e : expr X) :
  expr_weaken (H:=H1) (expr_cast (H:=H2) (expr_weaken (H:=H3) e)) = e.
Proof.
  destruct H2. assert (X = Y) by set_solver. subst Y. by rewrite !expr_weaken_id.
Qed.

Lemma expr_cast_val {X Y : stringset} {H : X = Y} e:
  to_val (expr_cast (H:=H) e) = to_val e.
Proof. destruct H. done. Qed.

(** Basic properties about the language *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  induction v; simpl; try case_match; simplify_option_eq; try done.
  - f_equiv. f_equiv. by rewrite expr_weaken_cast_id.
  - exfalso. apply H. set_solver+.
Qed.

Lemma of_to_val' X (e : expr X) v : to_val e = Some v → expr_weaken (H:=stringset_subseteq_1) (of_val v) = e.
Proof.
  revert v; induction e; intros; simplify_option_eq; auto with f_equal.
  f_equiv. by rewrite expr_weaken_cast_weaken_id.
Qed.

Instance: Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ?? H; simpl in *; inversion_clear H; done. Qed.

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

Lemma values_head_stuck e1 σ1 e2 σ2 ef :
  head_step e1 σ1 e2 σ2 ef → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma values_stuck e1 σ1 e2 σ2 ef : prim_step e1 σ1 e2 σ2 ef → to_val e1 = None.
Proof. intros [??? -> -> ?]; eauto using fill_not_val, values_head_stuck. Qed.

Lemma atomic_not_val e : atomic e → to_val e = None.
Proof. destruct e; naive_solver. Qed.

Lemma atomic_fill_item Ki e : atomic (fill_item Ki e) → is_Some (to_val e).
Proof.
  intros. destruct Ki; simplify_eq/=; destruct_conjs;
    repeat (case_match || contradiction); eauto.
  simpl. case_match; first by eauto. exfalso. apply n. set_solver+.
Qed.

Lemma atomic_fill K e : atomic (fill K e) → to_val e = None → K = [].
Proof.
  destruct K as [|Ki K]; [done|].
  rewrite eq_None_not_Some=> /= ? []; eauto using atomic_fill_item, fill_val.
Qed.

Lemma atomic_head_step e1 σ1 e2 σ2 ef :
  atomic e1 → head_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
Proof.
  destruct 2; simpl; rewrite ?to_of_val; try by eauto.
  repeat (case_match || contradiction || simplify_eq/=); eauto.
  rewrite expr_cast_val. 
Qed.

Lemma atomic_step e1 σ1 e2 σ2 ef :
  atomic e1 → prim_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
Proof.
  intros Hatomic [K e1' e2' -> -> Hstep].
  assert (K = []) as -> by eauto 10 using atomic_fill, values_head_stuck.
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
  eauto using fill_item_no_val_inj, values_head_stuck, fill_not_val.
Qed.

Lemma alloc_fresh e v σ :
  let l := fresh (dom _ σ) in
  to_val e = Some v → head_step (Alloc e) σ (Loc l) (<[l:=v]>σ) None.
Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset _)), is_fresh. Qed.

Lemma subst_empty e v : subst e "" v = e.
Proof. induction e; simpl; repeat case_decide; intuition auto with f_equal. Qed.
End heap_lang.

(** Language *)
Program Canonical Structure heap_lang : language := {|
  expr := heap_lang.expr; val := heap_lang.val; state := heap_lang.state;
  of_val := heap_lang.of_val; to_val := heap_lang.to_val;
  atomic := heap_lang.atomic; prim_step := heap_lang.prim_step;
|}.
Solve Obligations with eauto using heap_lang.to_of_val, heap_lang.of_to_val,
  heap_lang.values_stuck, heap_lang.atomic_not_val, heap_lang.atomic_step.

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
Proof.
  change (LanguageCtx heap_lang (heap_lang.fill [Ki])).
  by apply _.
Qed.
