From iris.heap_lang Require Export lang.
Set Default Proof Using "Type".
Import heap_lang.

Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Instance alloc_atomic s v : Atomic s (Alloc (Val v)).
Proof.
  apply strongly_atomic_atomic, ectx_language_atomic.
  - intros σ e σ' ef obs Hstep; simpl in *. inversion Hstep; simplify_eq. eauto.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki e' Hfill.
    destruct Ki; simplify_eq/=. eauto.
Qed.
Instance load_atomic s v : Atomic s (Load (Val v)).
Proof.
  apply strongly_atomic_atomic, ectx_language_atomic.
  - intros σ e σ' ef obs Hstep; simpl in *. inversion Hstep; simplify_eq. eauto.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki e' Hfill.
    destruct Ki; simplify_eq/=. eauto.
Qed.
Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
Proof.
  apply strongly_atomic_atomic, ectx_language_atomic.
  - intros σ e σ' ef obs Hstep; simpl in *. inversion Hstep; simplify_eq. eauto.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki e' Hfill.
    destruct Ki; simplify_eq/=; eauto.
Qed.
Instance cas_atomic s v0 v1 v2 : Atomic s (CAS (Val v0) (Val v1) (Val v2)).
Proof.
  apply strongly_atomic_atomic, ectx_language_atomic.
  - intros σ e σ' ef obs Hstep; simpl in *. inversion Hstep; simplify_eq; eauto.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki e' Hfill.
    destruct Ki; simplify_eq/=; eauto.
Qed.
Instance faa_atomic s v1 v2 : Atomic s (FAA (Val v1) (Val v2)).
Proof.
  apply strongly_atomic_atomic, ectx_language_atomic.
  - intros σ e σ' ef obs Hstep; simpl in *. inversion Hstep; simplify_eq; eauto.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki e' Hfill.
    destruct Ki; simplify_eq/=; eauto.
Qed.
Instance fork_atomic s e : Atomic s (Fork e).
Proof.
  apply strongly_atomic_atomic, ectx_language_atomic.
  - intros σ e' σ' ef obs Hstep; simpl in *. inversion Hstep; simplify_eq; eauto.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki e' Hfill.
    destruct Ki; simplify_eq/=; eauto.
Qed.
Instance skip_atomic s : Atomic s Skip.
Proof.
  apply strongly_atomic_atomic, ectx_language_atomic.
  - intros σ e' σ' ef obs Hstep; simpl in *. inversion Hstep; simplify_eq; eauto.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki e' Hfill.
    destruct Ki; simplify_eq/=; eauto.
Qed.
Instance new_proph_atomic s : Atomic s NewProph.
Proof.
  apply strongly_atomic_atomic, ectx_language_atomic.
  - intros σ e' σ' ef obs Hstep; simpl in *. inversion Hstep; simplify_eq; eauto.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki e' Hfill.
    destruct Ki; simplify_eq/=; eauto.
Qed.
Instance resolve_proph_atomic s v1 v2 : Atomic s (ResolveProph (Val v1) (Val v2)).
Proof.
  apply strongly_atomic_atomic, ectx_language_atomic.
  - intros σ e σ' ef obs Hstep; simpl in *. inversion Hstep; simplify_eq. eauto.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki e' Hfill.
    destruct Ki; simplify_eq/=; eauto.
Qed.


(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
  match e with
  | _ => tac K e
  | App ?e (Val ?v) => go (AppLCtx v :: K) e
  | App ?e1 ?e2 => go (AppRCtx e1 :: K) e2
  | UnOp ?op ?e => go (UnOpCtx op :: K) e
  | BinOp ?op ?e (Val ?v) => go (BinOpLCtx op v :: K) e
  | BinOp ?op ?e1 ?e2 => go (BinOpRCtx op e1 :: K) e2
  | If ?e0 ?e1 ?e2 => go (IfCtx e1 e2 :: K) e0
  | Pair ?e (Val ?v) => go (PairLCtx v :: K) e
  | Pair ?e1 ?e2 => go (PairRCtx e1 :: K) e2
  | Fst ?e => go (FstCtx :: K) e
  | Snd ?e => go (SndCtx :: K) e
  | InjL ?e => go (InjLCtx :: K) e
  | InjR ?e => go (InjRCtx :: K) e
  | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0
  | Alloc ?e => go (AllocCtx :: K) e
  | Load ?e => go (LoadCtx :: K) e
  | Store ?e (Val ?v) => go (StoreLCtx v :: K) e
  | Store ?e1 ?e2 => go (StoreRCtx e1 :: K) e2
  | CAS ?e0 (Val ?v1) (Val ?v2) => go (CasLCtx v1 v2 :: K) e0
  | CAS ?e0 ?e1 (Val ?v2) => go (CasMCtx e0 v2 :: K) e1
  | CAS ?e0 ?e1 ?e2 => go (CasRCtx e0 e1 :: K) e2
  | FAA ?e (Val ?v) => go (FaaLCtx v :: K) e
  | FAA ?e1 ?e2 => go (FaaRCtx e1 :: K) e2
  | ResolveProph ?e (Val ?v) => go (ProphLCtx v :: K) e
  | ResolveProph ?e1 ?e2 => go (ProphRCtx e1 :: K) e2
  end in go (@nil ectx_item) e.
