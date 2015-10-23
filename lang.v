Require Import Ssreflect.ssreflect.
Require Import List.
Require Import core_lang.
Require Import ModuRes.Relations ModuRes.CSetoid.

(******************************************************************)
(** * Derived language with threadpool steps **)
(******************************************************************)

Set Bullet Behavior "Strict Subproofs".

Module Lang (C : CORE_LANG).

  Export C.

  Delimit Scope lang_scope with lang.
  Local Open Scope lang_scope.

  (* Notation "'ε'"    := empty_ctx : lang_scope. *)
  (* Notation "K1 ∘ K2"  := (comp_ctx K1 K2) (at level 40, left associativity) : lang_scope. *)

  (* Arguments fork_not_value {_} _. *)
  (* Arguments comp_ctx_positive {_ _} _. *)
  (* Arguments fork_inj {_ _} _. *)
  (* Arguments fill_inj_r _ {_ _} _. *)
  (* Arguments fill_value {_ _} _. *)
  (* Arguments fill_fork {_ _ _} _. *)
  (* Arguments values_stuck {_} _ {_ _} _ _. *)
  (* Arguments atomic_reducible {_} _. *)
  Arguments atomic_step {_ _ _ _} _ _ _.

  Local Open Scope lang_scope.

  (** Thread pools **)
  Definition tpool : Type := list expr.

  (** Machine configurations **)
  Definition cfg : Type := (tpool * state)%type.

  (* Threadpool stepping relation *)
  Inductive step (ρ ρ' : cfg) : Prop :=
  | step_atomic : forall e e' σ σ' t1 t2,
                    ρ  = (t1 ++ e  :: t2, σ) ->
                    ρ' = (t1 ++ e' :: t2, σ') ->
                    prim_step (e, σ) (e', σ') None ->
                    step ρ ρ'
  | step_atomic_fork : forall e e' σ σ' t1 t2 ef,
                         ρ  = (t1 ++ e :: t2, σ) ->
                         ρ' = (t1 ++ e' :: t2 ++ ef :: nil, σ') ->
                         prim_step (e, σ) (e', σ') (Some ef) ->
      step ρ ρ'
  .
  
  (* | step_fork : forall e σ K t1 t2, *)
  (*     (* thread ID is 0 for the head of the list, new thread gets first free ID *) *)
  (*     ρ  = (t1 ++ fill K (fork e) :: t2, σ) -> *)
  (*     ρ' = (t1 ++ fill K fork_ret :: t2 ++ e :: nil, σ) -> *)
  (*     step ρ ρ'. *)

  (* Lemma comp_ctx_neut_emp_r {K K'} : *)
  (*   K = K ∘ K' -> *)
  (*   K' = ε. *)
  (* Proof. *)
  (*   intros HEq. *)
  (*   rewrite <- comp_ctx_emp_r in HEq at 1. *)
  (*   apply comp_ctx_inj_r in HEq; now symmetry. *)
  (* Qed. *)

  (* Lemmas about expressions *)
  Lemma reducible_not_value {e} :
    reducible e -> ~is_value e.
  Proof.
    intros H_red H_val.
    eapply values_stuck; try eassumption.
  Qed.

  (* Lemma reducible_not_fork {e K e'} : *)
  (*   reducible e -> e <> fill K (fork e'). *)
  (* Proof. *)
  (*   move=> HRed HDec. *)
  (*   move: (fork_stuck K e'); rewrite -HDec -(fill_empty e) => HStuck {HDec}. *)
  (*   exact: (HStuck _ _ eq_refl). *)
  (* Qed. *)

  (* Lemma step_same_ctx {K K' e e'} : *)
  (*                        fill K e = fill K' e' -> *)
  (*                        reducible e  -> *)
  (*                        reducible e' -> *)
  (*                        K = K'. *)
  (* Proof. *)
  (*   intros H_fill H_red H_red'. *)
  (*   edestruct (step_by_value K K' e e') as [K'' H_K'']. *)
  (*   - assumption. *)
  (*   - assumption. *)
  (*   - now apply reducible_not_value. *)
  (*   - edestruct (step_by_value K' K e' e) as [K''' H_K''']. *)
  (*     + now symmetry. *)
  (*     + assumption. *)
  (*     + now apply reducible_not_value. *)
  (*     + subst K. *)
  (*       rewrite <- comp_ctx_assoc in H_K''. *)
  (*       assert (H_emp := comp_ctx_neut_emp_r H_K''). *)
  (*       apply comp_ctx_positive in H_emp. *)
  (*       destruct H_emp as[H_K'''_emp H_K''_emp]. *)
  (*       subst K'' K'''. *)
  (*       now rewrite comp_ctx_emp_r. *)
  (* Qed. *)

  Lemma atomic_not_stuck {e} :
    atomic e -> ~stuck e.
  Proof.
    intros H_atomic H_stuck.
    eapply H_stuck.
    now eapply atomic_reducible.
  Qed.

  (* Lemma fork_not_atomic K e : *)
  (*   ~atomic (fill K (fork e)). *)
  (* Proof. *)
  (*   intros HAt. *)
  (*   apply atomic_not_stuck in HAt. *)
  (*   apply HAt, fork_stuck. *)
  (* Qed. *)

  Lemma atomic_not_value e :
    atomic e -> ~is_value e.
  Proof.
    intros HAt HVal.
    apply atomic_not_stuck in HAt; apply values_stuck in HVal.
    tauto.
  Qed.

  (* Lemma atomic_fill {e K} *)
  (*       (HAt : atomic (fill K e)) *)
  (*       (HNV : ~ is_value e) : *)
  (*   K = empty_ctx. *)
  (* Proof. *)
  (*   destruct (step_by_value K ε e (fill K e)) as [K' EQK]. *)
  (*   - now rewrite fill_empty. *)
  (*   - now apply atomic_reducible. *)
  (*   - assumption. *)
  (*   - symmetry in EQK; now apply comp_ctx_positive in EQK. *)
  (* Qed. *)

  (* Reflexive, transitive closure of the step relation *)
  Global Instance cfg_type : Setoid cfg := discreteType.
  Definition steps := refl_trans_closure step.
  Definition stepn := n_closure step.

End Lang.
