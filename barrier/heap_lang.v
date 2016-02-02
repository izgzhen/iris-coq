Require Export Autosubst.Autosubst.
Require Export iris.language.
Require Import prelude.gmap.

Module heap_lang.
(** Expressions and vals. *)
Definition loc := positive. (* Really, any countable type. *)

Inductive expr :=
  (* Base lambda calculus *)
  | Var (x : var)
  | Rec (e : {bind 2 of expr}) (* These are recursive lambdas.
                                  The *inner* binder is the recursive call! *)
  | App (e1 e2 : expr)
  (* Natural numbers *)
  | LitNat (n : nat)
  | Plus (e1 e2 : expr)
  | Le (e1 e2 : expr)
  (* Unit *)
  | LitUnit
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})
  (* Concurrency *)
  | Fork (e : expr)
  (* Heap *)
  | Loc (l : loc)
  | Alloc (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  | Cas (e0 : expr) (e1 : expr) (e2 : expr).

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

(* This sugar is used by primitive reduction riles (<=, CAS) and hence
defined here. *)
Notation LitTrue := (InjL LitUnit).
Notation LitFalse := (InjR LitUnit).

Inductive val :=
  | RecV (e : {bind 2 of expr}) (* These are recursive lambdas.
                                   The *inner* binder is the recursive call! *)
  | LitNatV (n : nat)
  | LitUnitV
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | LocV (l : loc).

Definition LitTrueV := InjLV LitUnitV.
Definition LitFalseV := InjRV LitUnitV.

Fixpoint of_val (v : val) : expr :=
  match v with
  | RecV e => Rec e
  | LitNatV n => LitNat n
  | LitUnitV => LitUnit
  | PairV v1 v2 => Pair (of_val v1) (of_val v2)
  | InjLV v => InjL (of_val v)
  | InjRV v => InjR (of_val v)
  | LocV l => Loc l
  end.
Fixpoint to_val (e : expr) : option val :=
  match e with
  | Rec e => Some (RecV e)
  | LitNat n => Some (LitNatV n)
  | LitUnit => Some LitUnitV
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
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | PlusLCtx (e2 : expr)
  | PlusRCtx (v1 : val)
  | LeLCtx (e2 : expr)
  | LeRCtx (v1 : val)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
  | AllocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | CasLCtx (e1 : expr)  (e2 : expr)
  | CasMCtx (v0 : val) (e2 : expr)
  | CasRCtx (v0 : val) (v1 : val).

Notation ectx := (list ectx_item).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx e2 => App e e2
  | AppRCtx v1 => App (of_val v1) e
  | PlusLCtx e2 => Plus e e2
  | PlusRCtx v1 => Plus (of_val v1) e
  | LeLCtx e2 => Le e e2
  | LeRCtx v1 => Le (of_val v1) e
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
  | CasLCtx e1 e2 => Cas e e1 e2
  | CasMCtx v0 e2 => Cas (of_val v0) e e2
  | CasRCtx v0 v1 => Cas (of_val v0) (of_val v1) e
  end.
Definition fill (K : ectx) (e : expr) : expr := fold_right fill_item e K.

(** The stepping relation *)
Inductive head_step : expr -> state -> expr -> state -> option expr -> Prop :=
  | BetaS e1 e2 v2 σ :
     to_val e2 = Some v2 →
     head_step (App (Rec e1) e2) σ e1.[(Rec e1),e2/] σ None
  | PlusS n1 n2 σ:
     head_step (Plus (LitNat n1) (LitNat n2)) σ (LitNat (n1 + n2)) σ None
  | LeTrueS n1 n2 σ :
     n1 ≤ n2 →
     head_step (Le (LitNat n1) (LitNat n2)) σ LitTrue σ None
  | LeFalseS n1 n2 σ :
     n1 > n2 →
     head_step (Le (LitNat n1) (LitNat n2)) σ LitFalse σ None
  | FstS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Fst (Pair e1 e2)) σ e1 σ None
  | SndS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Snd (Pair e1 e2)) σ e2 σ None
  | CaseLS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case (InjL e0) e1 e2) σ e1.[e0/] σ None
  | CaseRS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case (InjR e0) e1 e2) σ e2.[e0/] σ None
  | ForkS e σ:
     head_step (Fork e) σ LitUnit σ (Some e)
  | AllocS e v σ l :
     to_val e = Some v → σ !! l = None →
     head_step (Alloc e) σ (Loc l) (<[l:=v]>σ) None
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load (Loc l)) σ (of_val v) σ None
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store (Loc l) e) σ LitUnit (<[l:=v]>σ) None
  | CasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some vl → vl ≠ v1 →
     head_step (Cas (Loc l) e1 e2) σ LitFalse σ None
  | CasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some v1 →
     head_step (Cas (Loc l) e1 e2) σ LitTrue (<[l:=v2]>σ) None.

(** Atomic expressions *)
Definition atomic (e: expr) :=
  match e with
  | Alloc e => is_Some (to_val e)
  | Load e => is_Some (to_val e)
  | Store e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
  | Cas e0 e1 e2 => is_Some (to_val e0) ∧ is_Some (to_val e1) ∧ is_Some (to_val e2)
  | _ => False
  end.

(** Close reduction under evaluation contexts.
We could potentially make this a generic construction. *)
Inductive prim_step
    (e1 : expr) (σ1 : state) (e2 : expr) (σ2: state) (ef: option expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    head_step e1' σ1 e2' σ2 ef → prim_step e1 σ1 e2 σ2 ef.

(** Basic properties about the language *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by induction v; simplify_option_equality. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros; simplify_option_equality; auto with f_equal.
Qed.

Instance: Injective (=) (=) of_val.
Proof. by intros ?? Hv; apply (injective Some); rewrite -!to_of_val Hv. Qed.

Instance fill_item_inj Ki : Injective (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_equality'; auto with f_equal. Qed.

Instance ectx_fill_inj K : Injective (=) (=) (fill K).
Proof. red; induction K as [|Ki K IH]; naive_solver. Qed.

Lemma fill_app K1 K2 e : fill (K1 ++ K2) e = fill K1 (fill K2 e).
Proof. revert e; induction K1; simpl; auto with f_equal. Qed.

Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  intros [v' Hv']; revert v' Hv'.
  induction K as [|[]]; intros; simplify_option_equality; eauto.
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

Lemma atomic_fill K e : atomic (fill K e) → to_val e = None → K = [].
Proof.
  rewrite eq_None_not_Some.
  destruct K as [|[]]; naive_solver eauto using fill_val.
Qed.

Lemma atomic_head_step e1 σ1 e2 σ2 ef :
  atomic e1 → head_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
Proof. destruct 2; simpl; rewrite ?to_of_val; naive_solver. Qed.

Lemma atomic_step e1 σ1 e2 σ2 ef :
  atomic e1 → prim_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
Proof.
  intros Hatomic [K e1' e2' -> -> Hstep].
  assert (K = []) as -> by eauto 10 using atomic_fill, values_head_stuck.
  naive_solver eauto using atomic_head_step.
Qed.

Lemma head_ctx_step_val Ki e σ1 e2 σ2 ef :
  head_step (fill_item Ki e) σ1 e2 σ2 ef → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_equality; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_equality';
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
  destruct K' as [|Ki' K']; simplify_equality'.
  { destruct (proj1 (eq_None_not_Some (to_val (fill K e1))));
      eauto using fill_not_val, head_ctx_step_val. }
  cut (Ki = Ki'); [naive_solver eauto using prefix_of_cons|].
  eauto using fill_item_no_val_inj, values_head_stuck, fill_not_val.
Qed.

Lemma alloc_fresh e v σ :
  let l := fresh (dom _ σ) in
  to_val e = Some v → head_step (Alloc e) σ (Loc l) (<[l:=v]>σ) None.
Proof.
  by intros; apply AllocS, (not_elem_of_dom (D:=gset positive)), is_fresh.
Qed.

End heap_lang.

(** Language *)
Program Canonical Structure heap_lang : language := {|
  expr := heap_lang.expr; val := heap_lang.val; state := heap_lang.state;
  of_val := heap_lang.of_val; to_val := heap_lang.to_val;
  atomic := heap_lang.atomic; prim_step := heap_lang.prim_step;
|}.
Solve Obligations with eauto using heap_lang.to_of_val, heap_lang.of_to_val,
  heap_lang.values_stuck, heap_lang.atomic_not_val, heap_lang.atomic_step.

Global Instance heap_lang_ctx K :
  LanguageCtx heap_lang (heap_lang.fill K).
Proof.
  split.
  * eauto using heap_lang.fill_not_val.
  * intros ????? [K' e1' e2' Heq1 Heq2 Hstep].
    by exists (K ++ K') e1' e2'; rewrite ?heap_lang.fill_app ?Heq1 ?Heq2.
  * intros e1 σ1 e2 σ2 ? Hnval [K'' e1'' e2'' Heq1 -> Hstep].
    destruct (heap_lang.step_by_val
      K K'' e1 e1'' σ1 e2'' σ2 ef) as [K' ->]; eauto.
    rewrite heap_lang.fill_app in Heq1; apply (injective _) in Heq1.
    exists (heap_lang.fill K' e2''); rewrite heap_lang.fill_app; split; auto.
    econstructor; eauto.
Qed.
