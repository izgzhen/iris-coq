From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export weakestpre.
From iris.heap_lang Require Export wp_tactics heap.
Import uPred.

Ltac strip_later ::= iNext.

Section heap.
Context {Σ : gFunctors} `{heapG Σ}.
Implicit Types N : namespace.
Implicit Types P Q : iPropG heap_lang Σ.
Implicit Types Φ : val → iPropG heap_lang Σ.
Implicit Types Δ : envs (iResR heap_lang (globalF Σ)).

Global Instance sep_destruct_mapsto l q v :
  SepDestruct false (l ↦{q} v) (l ↦{q/2} v) (l ↦{q/2} v).
Proof. by rewrite /SepDestruct heap_mapsto_op_split. Qed.

Lemma tac_wp_alloc Δ Δ' N E j e v Φ :
  to_val e = Some v → 
  Δ ⊢ heap_ctx N → nclose N ⊆ E →
  StripLaterEnvs Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (l ↦ v)) Δ' = Some Δ'' ∧
    Δ'' ⊢ Φ (LitV (LitLoc l))) →
  Δ ⊢ WP Alloc e @ E {{ Φ }}.
Proof.
  intros ???? HΔ. rewrite -wp_alloc // -always_and_sep_l.
  apply and_intro; first done.
  rewrite strip_later_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  by rewrite right_id HΔ'.
Qed.

Lemma tac_wp_load Δ Δ' N E i l q v Φ :
  Δ ⊢ heap_ctx N → nclose N ⊆ E →
  StripLaterEnvs Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  Δ' ⊢ Φ v →
  Δ ⊢ WP Load (Lit (LitLoc l)) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_load // -always_and_sep_l. apply and_intro; first done.
  rewrite strip_later_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_store Δ Δ' Δ'' N E i l v e v' Φ :
  to_val e = Some v' →
  Δ ⊢ heap_ctx N → nclose N ⊆ E →
  StripLaterEnvs Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' = Some Δ'' →
  Δ'' ⊢ Φ (LitV LitUnit) → Δ ⊢ WP Store (Lit (LitLoc l)) e @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_store // -always_and_sep_l. apply and_intro; first done.
  rewrite strip_later_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas_fail Δ Δ' N E i l q v e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  Δ ⊢ heap_ctx N → nclose N ⊆ E →
  StripLaterEnvs Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I → v ≠ v1 →
  Δ' ⊢ Φ (LitV (LitBool false)) →
  Δ ⊢ WP CAS (Lit (LitLoc l)) e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_cas_fail // -always_and_sep_l. apply and_intro; first done.
  rewrite strip_later_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas_suc Δ Δ' Δ'' N E i l e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  Δ ⊢ heap_ctx N → nclose N ⊆ E →
  StripLaterEnvs Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v1)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' = Some Δ'' →
  Δ'' ⊢ Φ (LitV (LitBool true)) → Δ ⊢ WP CAS (Lit (LitLoc l)) e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_cas_suc // -always_and_sep_l. apply and_intro; first done.
  rewrite strip_later_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
End heap.

Tactic Notation "wp_apply" open_constr(lem) :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    wp_bind K; iApply lem; try iNext)
  end.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | Alloc ?e =>
       wp_bind K; eapply tac_wp_alloc with _ _ H _;
         [wp_done || fail 2 "wp_alloc:" e "not a value"
         |iAssumption || fail 2 "wp_alloc: cannot find heap_ctx"
         |done || eauto with ndisj
         |apply _
         |intros l; eexists; split;
           [env_cbv; reflexivity || fail 2 "wp_alloc:" H "not fresh"
           |wp_finish]]
    end)
  end.
Tactic Notation "wp_alloc" ident(l) := let H := iFresh in wp_alloc l as H.

Tactic Notation "wp_load" :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | Load (Lit (LitLoc ?l)) =>
       wp_bind K; eapply tac_wp_load;
         [iAssumption || fail 2 "wp_load: cannot find heap_ctx"
         |done || eauto with ndisj
         |apply _
         |iAssumptionCore || fail 2 "wp_cas_fail: cannot find" l "↦ ?"
         |wp_finish]
    end)
  end.

Tactic Notation "wp_store" :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | Store ?l ?e =>
       wp_bind K; eapply tac_wp_store;
         [wp_done || fail 2 "wp_store:" e "not a value"
         |iAssumption || fail 2 "wp_store: cannot find heap_ctx"
         |done || eauto with ndisj
         |apply _
         |iAssumptionCore || fail 2 "wp_store: cannot find" l "↦ ?"
         |env_cbv; reflexivity
         |wp_finish]
    end)
  end.

Tactic Notation "wp_cas_fail" :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | CAS (Lit (LitLoc ?l)) ?e1 ?e2 =>
       wp_bind K; eapply tac_wp_cas_fail;
         [wp_done || fail 2 "wp_cas_fail:" e1 "not a value"
         |wp_done || fail 2 "wp_cas_fail:" e2 "not a value"
         |iAssumption || fail 2 "wp_cas_fail: cannot find heap_ctx"
         |done || eauto with ndisj
         |apply _
         |iAssumptionCore || fail 2 "wp_cas_fail: cannot find" l "↦ ?"
         |try discriminate
         |wp_finish]
    end)
  end.

Tactic Notation "wp_cas_suc" :=
  match goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | CAS (Lit (LitLoc ?l)) ?e1 ?e2 =>
       wp_bind K; eapply tac_wp_cas_suc;
         [wp_done || fail 2 "wp_cas_suc:" e1 "not a value"
         |wp_done || fail 2 "wp_cas_suc:" e1 "not a value"
         |iAssumption || fail 2 "wp_cas_suc: cannot find heap_ctx"
         |done || eauto with ndisj
         |apply _
         |iAssumptionCore || fail 2 "wp_cas_suc: cannot find" l "↦ ?"
         |env_cbv; reflexivity
         |wp_finish]
    end)
  end.
