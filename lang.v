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

  Arguments atomic_step {_ _ _ _} _ _ _.

  (** Thread pools **)
  Definition tpool : Type := list expr.

  (** Machine configurations **)
  Definition cfg : Type := (tpool * state)%type.

  (* Threadpool stepping relation *)
  Definition option_to_list {A: Type} (o: option A): list A :=
    match o with
    | None => []
    | Some a => [a]
    end.

  Inductive step (ρ ρ' : cfg) : Prop :=
  | step_atomic : forall e e' ef σ σ' t1 t2,
                    ρ  = (t1 ++ e  :: t2, σ) ->
                    ρ' = (t1 ++ e' :: t2 ++ option_to_list ef, σ') ->
                    prim_step (e, σ) (e', σ') ef ->
                    step ρ ρ'
  .

  (* Reflexive, transitive closure of the step relation *)
  Global Instance cfg_type : Setoid cfg := discreteType.
  Definition steps := refl_trans_closure step.
  Definition stepn := n_closure step.

End Lang.
