Require Import Autosubst.Autosubst.

Inductive expr :=
| Var (x : var)
| Lit (T : Type) (t: T)  (* arbitrary Coq values become literals *)
| App (e1 e2 : expr)
| Lam (e : {bind expr})
| Pair (e1 e2 : expr)
| Fst (e : expr)
| Snd (e : expr)
| InjL (e : expr)
| InjR (e : expr)
| Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr}).

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Inductive value :=
| LitV (T : Type) (t : T)  (* arbitrary Coq values become literals *)
| LamV (e : {bind expr})
| PairV (v1 v2 : value)
| InjLV (v : value)
| InjRV (v : value).

Fixpoint v2e (v : value): expr :=
  match v with
  | LitV T t => Lit T t
  | LamV e   => Lam e
  | PairV v1 v2 => Pair (v2e v1) (v2e v2)
  | InjLV v => InjL (v2e v)
  | InjRV v => InjR (v2e v)
  end.

Inductive ectx :=
| EmptyCtx
| AppLCtx (K1 : ectx) (e2 : expr)
| AppRCtx (v1 : value) (K2 : ectx)
| PairLCtx (K1 : ectx) (e2 : expr)
| PairRCtx (v1 : value) (K2 : ectx)
| FstCtx (K : ectx)
| SndCtx (K : ectx)
| InjLCtx (K : ectx)
| InjRCtx (K : ectx)
| CaseCtx (K : ectx) (e1 : {bind expr}) (e2 : {bind expr}).

Fixpoint fill (K : ectx) (e : expr) :=
  match K with
  | EmptyCtx => e
  | AppLCtx K1 e2 => App (fill K1 e) e2
  | AppRCtx v1 K2 => App (v2e v1) (fill K2 e)
  | PairLCtx K1 e2 => Pair (fill K1 e) e2
  | PairRCtx v1 K2 => Pair (v2e v1) (fill K2 e)
  | FstCtx K => Fst (fill K e)
  | SndCtx K => Snd (fill K e)
  | InjLCtx K => InjL (fill K e)
  | InjRCtx K => InjR (fill K e)
  | CaseCtx K e1 e2 => Case (fill K e) e1 e2
  end.

Fixpoint comp_ctx (Ko : ectx) (Ki : ectx) :=
  match Ko with
  | EmptyCtx => Ki
  | AppLCtx K1 e2 => AppLCtx (comp_ctx K1 Ki) e2
  | AppRCtx v1 K2 => AppRCtx v1 (comp_ctx K2 Ki)
  | PairLCtx K1 e2 => PairLCtx (comp_ctx K1 Ki) e2
  | PairRCtx v1 K2 => PairRCtx v1 (comp_ctx K2 Ki)
  | FstCtx K => FstCtx (comp_ctx K Ki)
  | SndCtx K => SndCtx (comp_ctx K Ki)
  | InjLCtx K => InjLCtx (comp_ctx K Ki)
  | InjRCtx K => InjRCtx (comp_ctx K Ki)
  | CaseCtx K e1 e2 => CaseCtx (comp_ctx K Ki) e1 e2
  end.

Lemma fill_empty e :
  fill EmptyCtx e = e.
Proof.
  reflexivity.
Qed.

Lemma fill_comp K1 K2 e :
  fill K1 (fill K2 e) = fill (comp_ctx K1 K2) e.
Proof.
  revert K2 e; induction K1; intros K2 e; simpl; rewrite ?IHK1, ?IHK2; reflexivity.
Qed.

Lemma fill_inj_r K e1 e2 :
  fill K e1 = fill K e2 -> e1 = e2.
Proof.
  revert e1 e2; induction K; intros el er; simpl;
     intros Heq; try apply IHK; inversion Heq; reflexivity.
Qed.

Inductive step : expr -> expr -> Prop :=
| Beta e v : step (App (Lam e) (v2e v)) (e.[(v2e v)/])
| FstS v1 v2  : step (Fst (Pair (v2e v1) (v2e v2))) (v2e v1)
| SndS v1 v2  : step (Fst (Pair (v2e v1) (v2e v2))) (v2e v2)
| CaseL v0 e1 e2 : step (Case (InjL (v2e v0)) e1 e2) (e1.[(v2e v0)/])
| CaseR v0 e1 e2 : step (Case (InjR (v2e v0)) e1 e2) (e2.[(v2e v0)/]).
