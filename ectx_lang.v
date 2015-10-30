Require Import Arith Ssreflect.ssreflect Ssreflect.ssrfun.
Require Import world_prop world_prop_recdom core_lang lang iris_core iris_plog iris_ht_rules iris_vs_rules iris_derived_rules.
Require Import ModuRes.RA ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.RAConstr ModuRes.CMRA.

Set Bullet Behavior "Strict Subproofs".

(** This file defines an interface for languages with evaluation contexts, and shows that they have a Bind rule. *)
Module Type ECTX_LANG.

  (******************************************************************)
  (** ** Syntax, machine state, and atomic reductions **)
  (******************************************************************)

  (** Expressions and values **)
  Parameter expr : Type.

  Parameter is_value : expr -> Prop.
  Definition value : Type := {e: expr | is_value e}.
  Parameter is_value_dec : forall e, is_value e + ~is_value e.

  (** Evaluation contexts **)
  Parameter ectx : Type.
  Parameter empty_ctx : ectx.
  Parameter comp_ctx : ectx -> ectx -> ectx.
  Parameter fill : ectx -> expr -> expr.

  Axiom fill_empty : forall e, fill empty_ctx e = e.
  Axiom fill_comp  : forall K1 K2 e, fill K1 (fill K2 e) = fill (comp_ctx K1 K2) e.
  Axiom fill_inj_r  : forall K e1 e2, fill K e1 = fill K e2 -> e1 = e2.
  Axiom fill_value : forall K e, is_value (fill K e) -> is_value e.

  (** Shared machine state (e.g., the heap) **)
  Parameter state : Type.

  (** Primitive (single thread) machine configurations **)
  Definition prim_cfg : Type := (expr * state)%type.

  (** The primitive atomic stepping relation **)
  Parameter prim_step : prim_cfg -> prim_cfg -> option expr -> Prop.
  
  (** Some derived notions. **)
  Definition reducible e: Prop :=
    exists sigma cfg' ef, prim_step (e, sigma) cfg' ef.

  Definition stuck (e : expr) : Prop :=
    forall K e',
      e = fill K e' ->
      ~reducible e'.

  (** Atomic expressions **)
  Parameter atomic : expr -> Prop.

  (** Things ought to make sense. *)
  Axiom values_stuck :
    forall e, is_value e -> stuck e.

  (* When something does a step, and another decomposition of the same
     expression has a non-value e in the hole, then K is a left
     sub-context of K' - in other words, e also contains the reducible
     expression *)
  Axiom step_by_value :
    forall K K' e e',
      fill K e = fill K' e' ->
      reducible e' ->
      ~ is_value e ->
      exists K'', K' = comp_ctx K K''.

  Axiom atomic_not_value :
    forall e, atomic e -> ~is_value e.

  Axiom atomic_step: forall e σ e' σ' ef,
                       atomic e ->
                       prim_step (e, σ) (e', σ') ef ->
                       is_value e'.

  (* Atomics must not contain evaluation positions. *)
  Axiom atomic_fill: forall e K,
			atomic (fill K e) ->
			~ is_value e ->
			K = empty_ctx.
End ECTX_LANG.

Module EctxCoreLang (E: ECTX_LANG) <: CORE_LANG.

  Definition expr := E.expr.
  Definition is_value := E.is_value.
  Definition value := E.value.
  Definition is_value_dec := E.is_value_dec.

  Definition state := E.state.
  Definition prim_cfg := E.prim_cfg.

  (** Base reduction **)
  Definition prim_step (c1 c2: prim_cfg) (ef: option expr) :=
    match c1, c2 with
    | (e1, σ1), (e2, σ2) => exists K e1' e2', e1 = E.fill K e1' /\ e2 = E.fill K e2' /\
                                              E.prim_step (e1', σ1) (e2', σ2) ef
    end.

  Definition reducible e: Prop :=
    exists sigma cfg' ef, prim_step (e, sigma) cfg' ef.

  
  Definition is_ctx (ctx : expr -> expr) : Prop :=
    (forall e, is_value (ctx e) -> is_value e) /\
    (forall e1 σ1 e2 σ2 ef, prim_step (e1, σ1) (e2, σ2) ef -> prim_step (ctx e1, σ1) (ctx e2, σ2) ef) /\
    (forall e1 σ1 e2 σ2 ef, ~is_value e1 -> prim_step (ctx e1, σ1) (e2, σ2) ef ->
                            exists e2', e2 = ctx e2' /\ prim_step (e1, σ1) (e2', σ2) ef).

  Lemma reducible_eq e: reducible e <-> exists K e', e = E.fill K e' /\ E.reducible e'.
  Proof.
    split.
    - intros (σ & c2 & ef & Hstep). destruct c2 as [e2 σ2].
      destruct Hstep as (K & e' & e2' & Heq1 & Heq2 & Hstep).
      exists K e'. split; first assumption. exists σ (e2', σ2) ef.
      assumption.
    - intros (K & e' & Heq & Hred). destruct Hred as (σ & c2 & ef & Hred). destruct c2 as [e2 σ2].
      exists σ (E.fill K e2, σ2) ef. exists K e' e2. split; last split; assumption || reflexivity.
  Qed.

  Lemma values_stuck :
    forall e, is_value e -> ~reducible e.
  Proof.
    intros. intros HRed. apply reducible_eq in HRed. destruct HRed as (K & e' & Heq & HRed).
    eapply E.values_stuck; eassumption.
  Qed.

  (** Atomic **)
  Definition atomic := E.atomic.

  Lemma atomic_not_value :
    forall e, atomic e -> ~is_value e.
  Proof.
    exact E.atomic_not_value.
  Qed.

  Lemma atomic_step: forall e σ e' σ' ef,
      atomic e ->
      prim_step (e, σ) (e', σ') ef ->
      is_value e'.
  Proof.
    intros ? ? ? ? ? Hatomic (K & e1' & e2' & Heq1 & Heq2 & Hstep).
    move:(E.atomic_fill e1' K). subst. case/(_ _ _)/Wrap.
    - assumption.
    - intros Hval. eapply E.values_stuck; [eassumption|erewrite E.fill_empty;reflexivity|].
      do 3 eexists. eassumption.
    - intros Heq. subst.
      eapply E.atomic_step; first eassumption.
      erewrite !E.fill_empty. eassumption.
  Qed.

End EctxCoreLang.

Module Type ECTX_RES (RL : VIRA_T) (E : ECTX_LANG) <: CMRA_EXT_T.
 Module C := EctxCoreLang E.
 Include IRIS_RES RL C.
End ECTX_RES.

Module EctxRes (RL : VIRA_T) (E : ECTX_LANG) <: ECTX_RES RL E.
  Include ECTX_RES RL E.
End EctxRes.

Module ECTX_IRIS (RL : VIRA_T) (E : ECTX_LANG) (R: ECTX_RES RL E) (WP: WORLD_PROP R).

  Module Lang := EctxCoreLang E.
  Module Res := IrisRes RL Lang.
  Module World := WorldProp Res.
  Module Import Core := IrisCore RL Lang Res World.
  Module Import Plog := IrisPlog RL Lang Res World Core.
  Module Import HTRules := IrisHTRules RL Lang Res World Core Plog.
  Module Import VSRules := IrisVSRules RL Lang Res World Core Plog.
  Module Import DerivedRules := IrisDerivedRules RL Lang Res World Core Plog VSRules HTRules.

  Local Open Scope ra_scope.
  Local Open Scope de_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.

  (** We can hae bind with evaluation contexts **)
  Lemma fill_is_ctx K: is_ctx (E.fill K).
  Proof.
    split; last split.
    - intros ? Hval. eapply E.fill_value. eassumption.
    - intros ? ? ? ? ? (K' & e1' & e2' & Heq1 & Heq2 & Hstep).
      exists (E.comp_ctx K K') e1' e2'. rewrite -!E.fill_comp Heq1 Heq2.
      split; last split; reflexivity || assumption.
    - intros ? ? ? ? ? Hnval (K' & e1' & e2' & Heq1 & Heq2 & Hstep).
      destruct (E.step_by_value _ _ _ _ Heq1) as [K'' HeqK].
      + do 3 eexists. eassumption.
      + assumption.
      + subst e2 K'. rewrite -E.fill_comp in Heq1. apply E.fill_inj_r in Heq1. subst e1.
        exists (E.fill K'' e2'). split; first by rewrite -E.fill_comp.
        do 3 eexists. split; last split; eassumption || reflexivity.
  Qed.
        
  Lemma wpBind φ K e safe m :
    wp safe m e (HTRules.plug_bind (E.fill K) safe m φ) ⊑ wp safe m (E.fill K e) φ.
  Proof.
    apply wpBind. apply fill_is_ctx.
  Qed.

  Lemma htBind K P Q R e safe m :
    ht safe m P e Q ∧ all (plug_bind (E.fill K) safe m Q R) ⊑ ht safe m P (E.fill K e) R.
  Proof.
    apply htBind. apply fill_is_ctx.
  Qed.
  
End ECTX_IRIS.
