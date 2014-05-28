Require Import List.
Require Import RecDom.PCM.
Require Import core_lang.

(******************************************************************)
(** * Derived language with physical and logical resources **)
(******************************************************************)

Module Lang (RP: PCM_T) (RL: PCM_T) (C : CORE_LANG RP).

  Export C.
  Export RP RL.

  Local Open Scope lang_scope.

  (** Thread pools **)
  Definition tpool : Type := list expr.

  (** Machine configurations **)
  Definition cfg : Type := (tpool * state)%type.

  (* Threadpool stepping relation *)
  Inductive step (ρ ρ' : cfg) : Prop :=
  | step_atomic : forall e e' σ σ' K t1 t2,
      prim_step (e, σ) (e', σ') ->
      ρ  = (t1 ++ K [[ e  ]] :: t2, σ) ->
      ρ' = (t1 ++ K [[ e' ]] :: t2, σ') ->
      step ρ ρ'
  | step_fork : forall e σ K t1 t2,
      (* thread ID is 0 for the head of the list, new thread gets first free ID *)
      ρ  = (t1 ++ K [[ fork e   ]] :: t2, σ) ->
      ρ' = (t1 ++ K [[ fork_ret ]] :: t2 ++ e :: nil, σ) ->
      step ρ ρ'.

  (* Some derived facts about contexts *)
  Lemma comp_ctx_assoc K0 K1 K2 :
    (K0 ∘ K1) ∘ K2 = K0 ∘ (K1 ∘ K2).
  Proof.
    apply (fill_inj1 _ _ fork_ret).
    now rewrite <- !fill_comp.
  Qed.

  Lemma comp_ctx_emp_l K :
    ε ∘ K = K.
  Proof.
    apply (fill_inj1 _ _ fork_ret).
    now rewrite <- fill_comp, fill_empty.
  Qed.

  Lemma comp_ctx_emp_r K :
    K ∘ ε = K.
  Proof.
    apply (fill_inj1 _ _ fork_ret).
    now rewrite <- fill_comp,  fill_empty.
  Qed.

  Lemma comp_ctx_inj1 K1 K2 K :
    K1 ∘ K = K2 ∘ K ->
    K1 = K2.
  Proof.
    intros HEq.
    apply fill_inj1 with (K [[ fork_ret ]]).
    now rewrite !fill_comp, HEq.
  Qed.

  Lemma comp_ctx_inj2  K K1 K2 :
    K ∘ K1 = K ∘ K2 ->
    K1 = K2.
  Proof.
    intros HEq.
    apply fill_inj1 with fork_ret, fill_inj2 with K.
    now rewrite !fill_comp, HEq.
  Qed.

  Lemma comp_ctx_neut_emp_r K K' :
    K = K ∘ K' ->
    K' = ε.
  Proof.
    intros HEq.
    rewrite <- comp_ctx_emp_r in HEq at 1.
    apply comp_ctx_inj2 in HEq; congruence.
  Qed.

  Lemma comp_ctx_neut_emp_l K K' :
    K = K' ∘ K ->
    K' = ε.
  Proof.
    intros HEq.
    rewrite <- comp_ctx_emp_l in HEq at 1.
    apply comp_ctx_inj1 in HEq; congruence.
  Qed.

  (* atomic expressions *)
  Lemma fork_not_atomic K e :
    ~atomic (K [[ fork e ]]).
  Proof.
    intros HAt.
    apply atomic_not_stuck in HAt.
    apply HAt, fork_stuck.
  Qed.

  Lemma atomic_not_value e :
    atomic e -> ~is_value e.
  Proof.
    intros HAt HVal.
    apply atomic_not_stuck in HAt; apply values_stuck in HVal.
    tauto.
  Qed.

  (* Derived facts about expression erasure *)
  (* I don't think we need these for now — F. *)
  (*
  Lemma erase_exp_zero r e :
    erase_exp r e ->
    erase_exp RP.res_zero e.
  Proof.
    move=>r e H.
    rewrite -(RP.res_timesZ r) RP.res_timesC.
      by eapply C.erase_exp_mono.
  Qed.

  Lemma erase_exp_mono: forall r r' e,
                          erase_exp (resP r) e ->
                          erase_exp (resP (r ** r')) e.
  Proof.
    move=>r r' e H.
    case EQ_m:(RL.res_times (resL r) (resL r'))=>[m|].
    - erewrite resP_comm.
    - by apply C.erase_exp_mono.
    - by rewrite EQ_m.
    - move:(resL_zero _ _ EQ_m)=>->/=.
                               eapply erase_exp_zero; eassumption.
  Qed.

  Lemma erase_exp_idemp: forall r e,
                           erase_exp (resP r) e ->
                           exists r',
                             r = r ** r' /\
                             r' = r' ** r' /\
                             erase_exp (resP r') e.
  Proof.
    move=>[[rP rL]|] /= e H_erase; last first.
    - exists None.
             split; first done.
             split; first done.
             done.
             move:(C.erase_exp_idemp _ _ H_erase)=>{H_erase}[r'] [H_EQ1 [H_EQ2 H_erase]].
             exists (resFP r').
             split; last split.
             - case:r' H_EQ1 {H_EQ2 H_erase}=>[r'|]/=H_EQ1.
             - by rewrite -H_EQ1 RL.res_timesC RL.res_timesI /=.
                  - by rewrite RP.res_timesC RP.res_timesZ in H_EQ1.
             - by rewrite -resFP_comm -H_EQ2.
             - by rewrite resP_FP.
  Qed.

  Lemma erase_exp_split: forall r K e, 
                           erase_exp (resP r) (fill K e) ->
                           exists r_K r_e,
                             r = r_K ** r_e /\
                             erase_exp (resP r_K) (fill K fork_ret) /\
                             erase_exp (resP r_e) e.
  Proof.
    move=>r K e H_erase.
    move:(C.erase_exp_split _ _ _ H_erase)=>{H_erase}[r_K [r_e [H_EQ [H_erase1 H_erase2]]]].
    exists (resFP r_K ** resFL (resL r)). exists (resFP r_e).
    split; last split.
    - rewrite -{1}(res_eta r).
      rewrite res_timesA [_  ** resFP _]res_timesC -res_timesA.
      f_equal.
        by rewrite -resFP_comm H_EQ.
    - eapply erase_exp_mono.
        by rewrite resP_FP.
    - by rewrite resP_FP.
  Qed.

  Lemma erase_exp_combine: forall r_K r_e e K,
                             erase_exp (resP r_K) (fill K fork_ret) ->
                             erase_exp (resP r_e) e ->
                             erase_exp (resP (r_K ** r_e)) (fill K e).
  Proof.
    move=>r_k r_e e K H_K H_e.
    case EQ_m:(RL.res_times (resL r_k) (resL r_e))=>[m|]; last first.
    - apply resL_zero in EQ_m.
      rewrite EQ_m.
      eapply erase_exp_zero, erase_exp_combine; eassumption.
      rewrite resP_comm; last first.
    - by rewrite EQ_m.
      eapply erase_exp_combine; eassumption.
  Qed.*)

End Lang.
