Require Import Arith Ssreflect.ssreflect.
Require Import world_prop world_prop_recdom core_lang lang iris_core iris_plog iris_meta iris_vs_rules iris_ht_rules.
Require Import ModuRes.RA ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.RAConstr.

Set Bullet Behavior "Strict Subproofs".

(* This is a really stupid instantiation of the Iris paremeters.
   We use it solely to show that there are no assumptions hidden
   in the development. *)

Module StupidLang : CORE_LANG.
  Inductive exprI :=
  | unitI: exprI.
  Implicit Types (e: exprI).
  Definition expr := exprI.

    
  Definition is_value e := True.
  Definition value : Type := {e: expr | is_value e}.
  Definition is_value_dec e : is_value e + ~is_value e.
    left. exact I.
  Defined.

  (** Shared machine state (e.g., the heap) **)
  Definition state : Type := Datatypes.unit.
  Implicit Types (σ: state).

  (** Primitive (single thread) machine configurations **)
  Definition prim_cfg : Type := (expr * state)%type.

  (** The primitive atomic stepping relation **)
  Definition prim_step (cfg1 cfg2: prim_cfg) (ef: option expr) := False.

  Definition reducible e: Prop :=
    exists sigma cfg' ef, prim_step (e, sigma) cfg' ef.

  Definition stuck (e : expr) : Prop :=
      ~reducible e.

  (** Atomic expressions **)
  Definition atomic e := False.

  (** Properties *)
  Lemma values_stuck :
    forall e, is_value e -> stuck e.
  Proof.
    firstorder.
  Qed.


  Lemma atomic_not_value :
    forall e, atomic e -> ~is_value e.
  Proof.
    firstorder.
  Qed.

  Lemma atomic_step: forall e σ e' σ' ef,
                       atomic e ->
                       prim_step (e, σ) (e', σ') ef ->
                       is_value e'.
  Proof.
    firstorder.
  Qed.

End StupidLang.

Module TrivialRA : VIRA_T.
  Definition res := ex unit.
  Instance res_type : Setoid res := _.
  Instance res_op   : RA_op res := _.
  Instance res_unit : RA_unit res := _.
  Instance res_valid: RA_valid res := _.
  Instance res_ra   : RA res := _.
  Instance res_vira : VIRA res := _.
End TrivialRA.

(* Now we can instantiate all the things *)
Module Res := IrisRes TrivialRA StupidLang.
Module World := WorldProp Res.
Module Import Core := IrisCore TrivialRA StupidLang Res World.
Module Import Plog := IrisPlog TrivialRA StupidLang Res World Core.
Module Import VSRules := IrisVSRules TrivialRA StupidLang Res World Core Plog.
Module Import HTRules := IrisHTRules TrivialRA StupidLang Res World Core Plog.
Module Import Meta := IrisMeta TrivialRA StupidLang Res World Core Plog HTRules.

(* Make sure the precondition of Bind can actually be met. *)
Lemma id_is_fill: IsFill (fun e => e).
Proof.
  split; last split.
  - by firstorder.
  - by firstorder.
  - intros. eexists. reflexivity.
Qed.

(* And now we check for axioms *)
Print Assumptions adequacy_obs.
Print Assumptions adequacy_safe.

Print Assumptions lift_atomic_step.
Print Assumptions lift_pure_det_step.

(* We just check some rules here - listing all of them
   (including the base logic) would take too long. *)
Print Assumptions pvsOpen.
Print Assumptions pvsClose.
Print Assumptions pvsTrans.
Print Assumptions pvsGhostUpd.

Print Assumptions wpPreVS.
Print Assumptions wpACons.
Print Assumptions wpFrameRes.
Print Assumptions wpBind.

