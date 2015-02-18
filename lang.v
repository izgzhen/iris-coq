Require Import List.
Require Import core_lang.

(******************************************************************)
(** * Derived language with threadpool steps **)
(******************************************************************)

Module Lang (C : CORE_LANG).

  Export C.

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

  (* Lemmas about expressions *)
  Lemma reducible_not_value e:
    reducible e -> ~is_value e.
  Proof.
    intros H_red H_val.
    eapply values_stuck; try eassumption.
    now erewrite fill_empty.
  Qed.

  Lemma step_same_ctx: forall K K' e e',
                         fill K e = fill K' e' ->
                         reducible e  ->
                         reducible e' ->
                         K = K'.
  Proof.
    intros K K' e e' H_fill H_red H_red'.
    edestruct (step_by_value K K' e e') as [K'' H_K''].
    - assumption.
    - assumption.
    - now apply reducible_not_value.
    - edestruct (step_by_value K' K e' e) as [K''' H_K'''].
      + now symmetry.
      + assumption.
      + now apply reducible_not_value.
      + subst K.
        rewrite comp_ctx_assoc in H_K''.
        assert (H_emp := comp_ctx_neut_emp_r _ _ H_K'').
        apply fill_noinv in H_emp.
        destruct H_emp as[H_K'''_emp H_K''_emp].
        subst K'' K'''.
        now rewrite comp_ctx_emp_r.
  Qed.

  Lemma atomic_not_stuck e:
    atomic e -> ~stuck e.
  Proof.
    intros H_atomic H_stuck.
    eapply H_stuck.
    - now erewrite fill_empty.
    - now eapply atomic_reducible.
  Qed.

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

  Lemma atomic_fill e K
        (HAt : atomic (K [[ e ]]))
        (HNV : ~ is_value e) :
    K = empty_ctx.
  Proof.
    destruct (step_by_value K ε e (K [[ e ]])) as [K' EQK].
    - now rewrite fill_empty.
    - now apply atomic_reducible.
    - assumption.
    - symmetry in EQK; now apply fill_noinv in EQK.
  Qed.

  (* Reflexive, transitive closure of the step relation *)
  Inductive steps : cfg -> cfg -> Prop :=
  | steps_refl ρ : steps ρ ρ
  | stepn_trans ρ1 ρ2 ρ3 : step ρ1 ρ2 -> steps ρ2 ρ3 -> steps ρ1 ρ3.
                     
  
  Inductive stepn : nat -> cfg -> cfg -> Prop :=
  | stepn_O ρ : stepn O ρ ρ
  | stepn_S ρ1 ρ2 ρ3 n
            (HS  : step ρ1 ρ2)
            (HSN : stepn n ρ2 ρ3) :
      stepn (S n) ρ1 ρ3.

  Lemma steps_stepn ρ1 ρ2:
    steps ρ1 ρ2 -> exists n, stepn n ρ1 ρ2.
  Proof.
    induction 1.
    - eexists. eauto using stepn.
    - destruct IHsteps as [n IH]. eexists. eauto using stepn.
  Qed.

  Lemma stepn_steps n ρ1 ρ2:
    stepn n ρ1 ρ2 -> steps ρ1 ρ2.
  Proof.
    induction 1; now eauto using steps.
  Qed.

End Lang.
