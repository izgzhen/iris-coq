Require Import List.
Require Import RecDom.PCM.
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

End Lang.
