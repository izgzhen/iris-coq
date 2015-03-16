Require Import Arith ssreflect.
Require Import world_prop world_prop_recdom core_lang lang masks iris_core iris_plog iris_meta iris_vs_rules iris_ht_rules.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Bullet Behavior "Strict Subproofs".

(* This is a really stupid instantiation of the Iris paremeters.
   We use it solely to show that there are no assumptions hidden
   in the development. *)

Module StupidLang : CORE_LANG.
  Inductive exprI :=
  | unitI: exprI
  | forkI: exprI -> exprI.
  Implicit Types (e: exprI).
  Definition expr := exprI.
  Definition fork := forkI.

    
  Definition is_value e := match e with
                             | unitI => True
                             | forkI _ => False
                           end.
  Definition value : Type := {e: expr | is_value e}.
  Definition is_value_dec e : is_value e + ~is_value e.
    destruct e.
    - left. exact I.
    - right. tauto.
  Defined.

  Definition fork_ret := unitI.
  Lemma fork_ret_is_value : is_value fork_ret.
  Proof.
    exact I.
  Qed.
  Definition fork_ret_val : value := exist _ fork_ret fork_ret_is_value.
  Lemma fork_not_value e : ~is_value (fork e).
  Proof.
    tauto.
  Qed.
  Lemma fork_inj e1 e2: fork e1 = fork e2 -> e1 = e2.
  Proof.
    intros Heq. injection Heq. tauto.
  Qed.

  (** Evaluation contexts: You can just have the hole. There are no contexts below forks. **)
  Definition ectx : Type := Datatypes.unit.
  Implicit Types (K: ectx).
  Definition empty_ctx := tt.
  Definition comp_ctx K1 K2 := tt.
  Definition fill K e := e.

  Notation "'ε'"    := empty_ctx : lang_scope.
  Notation "K1 ∘ K2"  := (comp_ctx K1 K2) (at level 40, left associativity) : lang_scope.
  Notation "K '[[' e ']]' " := (fill K e) (at level 40, left associativity) : lang_scope.

  Local Open Scope lang_scope.
  
  Lemma fill_empty e : ε [[ e ]] = e.
  Proof.
    reflexivity.
  Qed.
  Lemma fill_comp K1 K2 e :
    K1 [[ K2 [[ e ]] ]] = K1 ∘ K2 [[ e ]].
  Proof.
    reflexivity.
  Qed.
  Lemma fill_inj1 K1 K2 e :
    K1 [[ e ]] = K2 [[ e ]] -> K1 = K2.
  Proof.
    intros _. destruct K1, K2. reflexivity.
  Qed.
  Lemma fill_inj2 K e1 e2 :
    K [[ e1 ]] = K [[ e2 ]] -> e1 = e2.
  Proof.
    tauto.
  Qed.
  Lemma fill_noinv K1 K2:
    K1 ∘ K2 = ε -> K1 = ε /\ K2 = ε.
  Proof.
    destruct K1, K2. intros _. split; reflexivity.
  Qed.
  Lemma fill_value K e:
    is_value (K [[ e ]]) -> K = ε.
  Proof.
    destruct K. now auto.
  Qed.
  Lemma fill_fork K e e':
    fork e' = K [[ e ]] -> K = ε.
  Proof.
    destruct K. now auto.
  Qed.
    

  (** Shared machine state (e.g., the heap) **)
  Definition state : Type := Datatypes.unit.
  Implicit Types (σ: state).

  (** Primitive (single thread) machine configurations **)
  Definition prim_cfg : Type := (expr * state)%type.

  (** The primitive atomic stepping relation **)
  Definition prim_step (cfg1 cfg2: prim_cfg) := False.


  Definition reducible e: Prop :=
    exists sigma cfg', prim_step (e, sigma) cfg'.

  Definition stuck (e : expr) : Prop :=
    forall K e',
      e = K [[ e' ]] ->
      ~reducible e'.

  Lemma fork_stuck K e:
    stuck (K [[ fork e ]]).
  Proof.
    now firstorder.
  Qed.
  Lemma values_stuck e:
    is_value e -> stuck e.
  Proof.
    now firstorder.
  Qed.

  (* When something does a step, and another decomposition of the same
     expression has a non-value e in the hole, then K is a left
     sub-context of K' - in other words, e also contains the reducible
     expression *)
  Lemma step_by_value :
    forall K K' e e',
      K [[ e ]] = K' [[ e' ]] ->
      reducible e' ->
      ~ is_value e ->
      exists K'', K' = K ∘ K''.
  Proof.
    now firstorder.
  Qed.
  (* Similar to above, buth with a fork instead of a reducible
     expression *)
  Lemma fork_by_value :
    forall K K' e e',
      K [[ e ]] = K' [[ fork e' ]] ->
      ~ is_value e ->
      exists K'', K' = K ∘ K''.
  Proof.
    intros. clear. destruct K, K'. exists ε. reflexivity.
  Qed.

  (** Atomic expressions **)
  Definition atomic e := False.

  Lemma atomic_reducible :
    forall e, atomic e -> reducible e.
  Proof.
    now firstorder.
  Qed.

  Lemma atomic_step: forall e σ e' σ',
                       atomic e ->
                       prim_step (e, σ) (e', σ') ->
                       is_value e'.
  Proof.
    now firstorder.
  Qed.

End StupidLang.

Module TrivialRA : RA_T.
  Definition res := ex unit.
  Instance res_type : Setoid res := _.
  Instance res_op   : RA_op res := _.
  Instance res_unit : RA_unit res := _.
  Instance res_valid: RA_valid res := _.
  Instance res_ra   : RA res := _.
End TrivialRA.

(* Now we can instantiate all the things *)
Module Res := IrisRes TrivialRA StupidLang.
Module World := WorldProp Res.
Module Import Core := IrisCore TrivialRA StupidLang Res World.
Module Import Plog := IrisPlog TrivialRA StupidLang Res World Core.
Module Import Meta := IrisMeta TrivialRA StupidLang Res World Core Plog.
Module Import HTRules := IrisHTRules TrivialRA StupidLang Res World Core Plog.
Module Import VSRules := IrisVSRules TrivialRA StupidLang Res World Core Plog.

(* And now we check for axioms *)
Print Assumptions adequacy_obs.
Print Assumptions adequacy_safe.
Print Assumptions robust_safety.

Print Assumptions lift_atomic_det_step.
Print Assumptions lift_pure_det_step.

Print Assumptions vsOpen.
Print Assumptions vsClose.
Print Assumptions vsNewInv.
Print Assumptions pvsFrame.
Print Assumptions pvsTrans.
Print Assumptions pvsGhostUpd.
Print Assumptions htBind.
Print Assumptions htCons.
Print Assumptions htACons.
