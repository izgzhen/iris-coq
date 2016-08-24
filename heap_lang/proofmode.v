From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export weakestpre.
From iris.heap_lang Require Export wp_tactics heap.
Import uPred.

Ltac wp_strip_later ::= iNext.

Section heap.
Context `{heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (iResUR Σ).

Global Instance into_and_mapsto l q v :
  IntoAnd false (l ↦{q} v) (l ↦{q/2} v) (l ↦{q/2} v).
Proof. by rewrite /IntoAnd heap_mapsto_op_eq Qp_div_2. Qed.

Lemma tac_wp_alloc Δ Δ' E j e v Φ :
  to_val e = Some v →
  (Δ ⊢ heap_ctx) → nclose heapN ⊆ E →
  IntoLaterEnvs Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (l ↦ v)) Δ' = Some Δ'' ∧
    (Δ'' ⊢ |={E}=> Φ (LitV (LitLoc l)))) →
  Δ ⊢ WP Alloc e @ E {{ Φ }}.
Proof.
  intros ???? HΔ. rewrite -wp_alloc // -always_and_sep_l.
  apply and_intro; first done.
  rewrite into_later_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  by rewrite right_id HΔ'.
Qed.

Lemma tac_wp_load Δ Δ' E i l q v Φ :
  (Δ ⊢ heap_ctx) → nclose heapN ⊆ E →
  IntoLaterEnvs Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  (Δ' ⊢ |={E}=> Φ v) →
  Δ ⊢ WP Load (Lit (LitLoc l)) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_load // -always_and_sep_l. apply and_intro; first done.
  rewrite into_later_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_store Δ Δ' Δ'' E i l v e v' Φ :
  to_val e = Some v' →
  (Δ ⊢ heap_ctx) → nclose heapN ⊆ E →
  IntoLaterEnvs Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' = Some Δ'' →
  (Δ'' ⊢ |={E}=> Φ (LitV LitUnit)) →
  Δ ⊢ WP Store (Lit (LitLoc l)) e @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_store // -always_and_sep_l. apply and_intro; first done.
  rewrite into_later_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas_fail Δ Δ' E i l q v e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  (Δ ⊢ heap_ctx) → nclose heapN ⊆ E →
  IntoLaterEnvs Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I → v ≠ v1 →
  (Δ' ⊢ |={E}=> Φ (LitV (LitBool false))) →
  Δ ⊢ WP CAS (Lit (LitLoc l)) e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_cas_fail // -always_and_sep_l. apply and_intro; first done.
  rewrite into_later_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas_suc Δ Δ' Δ'' E i l v e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  (Δ ⊢ heap_ctx) → nclose heapN ⊆ E →
  IntoLaterEnvs Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I → v = v1 →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' = Some Δ'' →
  (Δ'' ⊢ |={E}=> Φ (LitV (LitBool true))) →
  Δ ⊢ WP CAS (Lit (LitLoc l)) e1 e2 @ E {{ Φ }}.
Proof.
  intros; subst.
  rewrite -wp_cas_suc // -always_and_sep_l. apply and_intro; first done.
  rewrite into_later_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
End heap.

Tactic Notation "wp_apply" open_constr(lem) :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    wp_bind_core K; iApply lem; try iNext)
  | _ => fail "wp_apply: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with Alloc _ => wp_bind_core K end)
      |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
    eapply tac_wp_alloc with _ H _;
      [let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_alloc:" e' "not a value"
      |iAssumption || fail "wp_alloc: cannot find heap_ctx"
      |solve_ndisj || fail "wp_alloc: cannot open heap invariant"
      |apply _
      |first [intros l | fail 1 "wp_alloc:" l "not fresh"];
        eexists; split;
          [env_cbv; reflexivity || fail "wp_alloc:" H "not fresh"
          |wp_finish]]
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  let H := iFresh in wp_alloc l as H.

Tactic Notation "wp_load" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with Load _ => wp_bind_core K end)
      |fail 1 "wp_load: cannot find 'Load' in" e];
    eapply tac_wp_load;
      [iAssumption || fail "wp_load: cannot find heap_ctx"
      |solve_ndisj || fail "wp_load: cannot open heap invariant"
      |apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
       iAssumptionCore || fail "wp_load: cannot find" l "↦ ?"
      |wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with Store _ _ => wp_bind_core K end)
      |fail 1 "wp_store: cannot find 'Store' in" e];
    eapply tac_wp_store;
      [let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_store:" e' "not a value"
      |iAssumption || fail "wp_store: cannot find heap_ctx"
      |solve_ndisj || fail "wp_store: cannot open heap invariant"
      |apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
       iAssumptionCore || fail "wp_store: cannot find" l "↦ ?"
      |env_cbv; reflexivity
      |wp_finish]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_cas_fail" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with CAS _ _ _ => wp_bind_core K end)
      |fail 1 "wp_cas_fail: cannot find 'CAS' in" e];
    eapply tac_wp_cas_fail;
      [let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_cas_fail:" e' "not a value"
      |let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_cas_fail:" e' "not a value"
      |iAssumption || fail "wp_cas_fail: cannot find heap_ctx"
      |solve_ndisj || fail "wp_cas_fail: cannot open heap invariant"
      |apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
       iAssumptionCore || fail "wp_cas_fail: cannot find" l "↦ ?"
      |try congruence
      |wp_finish]
  | _ => fail "wp_cas_fail: not a 'wp'"
  end.

Tactic Notation "wp_cas_suc" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with CAS _ _ _ => wp_bind_core K end)
      |fail 1 "wp_cas_suc: cannot find 'CAS' in" e];
    eapply tac_wp_cas_suc;
      [let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_cas_suc:" e' "not a value"
      |let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_cas_suc:" e' "not a value"
      |iAssumption || fail "wp_cas_suc: cannot find heap_ctx"
      |solve_ndisj || fail "wp_cas_suc: cannot open heap invariant"
      |apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
       iAssumptionCore || fail "wp_cas_suc: cannot find" l "↦ ?"
      |try congruence
      |env_cbv; reflexivity
      |wp_finish]
  | _ => fail "wp_cas_suc: not a 'wp'"
  end.
