From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Export tactics lifting.
Set Default Proof Using "Type".
Import uPred.

Lemma tac_wp_pure `{heapG Σ} K Δ Δ' E e1 e2 φ Φ :
  PureExec φ e1 e2 →
  φ →
  IntoLaterNEnvs 1 Δ Δ' →
  (Δ' ⊢ WP fill K e2 @ E {{ Φ }}) →
  (Δ ⊢ WP fill K e1 @ E {{ Φ }}).
Proof.
  intros ??? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite -lifting.wp_bind HΔ' -wp_pure_step_later //.
  by rewrite -ectx_lifting.wp_ectx_bind_inv.
Qed.

Ltac wp_value_head := etrans; [|eapply wp_value; apply _]; simpl.

Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    unify e' efoc;
    eapply (tac_wp_pure K);
    [simpl; apply _                 (* PureExec *)
    |try fast_done                  (* The pure condition for PureExec *)
    |apply _                        (* IntoLaters *)
    |simpl_subst; try wp_value_head (* new goal *)])
   || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a reduct"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_if_true" := wp_pure (If (Lit (LitBool true)) _ _).
Tactic Notation "wp_if_false" := wp_pure (If (Lit (LitBool false)) _ _).
Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" := wp_unop || wp_binop.
Tactic Notation "wp_rec" := wp_pure (App _ _).
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" := wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_case" := wp_pure (Case _ _ _).
Tactic Notation "wp_match" := wp_case; wp_let.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => etrans; [|fast_by apply (wp_bind K)]; simpl
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match e' with
    | efoc => unify e' efoc; wp_bind_core K
    end) || fail "wp_bind: cannot find" efoc "in" e
  | _ => fail "wp_bind: not a 'wp'"
  end.

(** Heap tactics *)
Section heap.
Context `{heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (iResUR Σ).

Lemma tac_wp_alloc Δ Δ' E j K e v Φ :
  IntoVal e v →
  IntoLaterNEnvs 1 Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (l ↦ v)) Δ' = Some Δ'' ∧
    (Δ'' ⊢ WP fill K (Lit (LitLoc l)) @ E {{ Φ }})) →
  Δ ⊢ WP fill K (Alloc e) @ E {{ Φ }}.
Proof.
  intros ?? HΔ. rewrite -wp_bind. eapply wand_apply; first exact: wp_alloc.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  by rewrite right_id HΔ'.
Qed.

Lemma tac_wp_load Δ Δ' E i K l q v Φ :
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  (Δ' ⊢ WP fill K (of_val v) @ E {{ Φ }}) →
  Δ ⊢ WP fill K (Load (Lit (LitLoc l))) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bind. eapply wand_apply; first exact: wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_store Δ Δ' Δ'' E i K l v e v' Φ :
  IntoVal e v' →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' = Some Δ'' →
  (Δ'' ⊢ WP fill K (Lit LitUnit) @ E {{ Φ }}) →
  Δ ⊢ WP fill K (Store (Lit (LitLoc l)) e) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bind. eapply wand_apply; first by eapply wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas_fail Δ Δ' E i K l q v e1 v1 e2 Φ :
  IntoVal e1 v1 → AsVal e2 →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I → v ≠ v1 →
  (Δ' ⊢ WP fill K (Lit (LitBool false)) @ E {{ Φ }}) →
  Δ ⊢ WP fill K (CAS (Lit (LitLoc l)) e1 e2) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bind. eapply wand_apply; first exact: wp_cas_fail.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas_suc Δ Δ' Δ'' E i K l v e1 v1 e2 v2 Φ :
  IntoVal e1 v1 → IntoVal e2 v2 →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I → v = v1 →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' = Some Δ'' →
  (Δ'' ⊢ WP fill K (Lit (LitBool true)) @ E {{ Φ }}) →
  Δ ⊢ WP fill K (CAS (Lit (LitLoc l)) e1 e2) @ E {{ Φ }}.
Proof.
  intros; subst. rewrite -wp_bind. eapply wand_apply; first exact: wp_cas_suc.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
End heap.

Tactic Notation "wp_apply" open_constr(lem) :=
  iPoseProofCore lem as false true (fun H =>
    lazymatch goal with
    | |- _ ⊢ wp ?E ?e ?Q =>
      reshape_expr e ltac:(fun K e' =>
        wp_bind_core K; iApplyHyp H; try iNext; simpl) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | _ => fail "wp_apply: not a 'wp'"
    end).

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_alloc _ _ _ H K); [apply _|..])
      |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
    [apply _
    |first [intros l | fail 1 "wp_alloc:" l "not fresh"];
      eexists; split;
        [env_cbv; reflexivity || fail "wp_alloc:" H "not fresh"
        |simpl; try wp_value_head]]
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  let H := iFresh in wp_alloc l as H.

Tactic Notation "wp_load" :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [apply _
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_load: cannot find" l "↦ ?"
    |simpl; try wp_value_head]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_store _ _ _ _ _ K); [apply _|..])
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [apply _
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_store: cannot find" l "↦ ?"
    |env_cbv; reflexivity
    |simpl; try first [wp_pure (Seq (Lit LitUnit) _)|wp_value_head]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_cas_fail" :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_cas_fail _ _ _ _ K); [apply _|apply _|..])
      |fail 1 "wp_cas_fail: cannot find 'CAS' in" e];
    [apply _
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_cas_fail: cannot find" l "↦ ?"
    |try congruence
    |simpl; try wp_value_head]
  | _ => fail "wp_cas_fail: not a 'wp'"
  end.

Tactic Notation "wp_cas_suc" :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_cas_suc _ _ _ _ _ K); [apply _|apply _|..])
      |fail 1 "wp_cas_suc: cannot find 'CAS' in" e];
    [apply _
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_cas_suc: cannot find" l "↦ ?"
    |try congruence
    |env_cbv; reflexivity
    |simpl; try wp_value_head]
  | _ => fail "wp_cas_suc: not a 'wp'"
  end.
