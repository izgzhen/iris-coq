Require Import prelude.prelude.

Class Language (E V St : Type) := {
  to_expr : V → E;
  of_expr : E → option V;
  atomic : E → Prop;
  prim_step : E → St → E → St → option E → Prop;
  of_to_expr v : of_expr (to_expr v) = Some v;
  to_of_expr e v : of_expr e = Some v → to_expr v = e;
  values_stuck e σ e' σ' ef : prim_step e σ e' σ' ef → of_expr e = None;
  atomic_not_value e : atomic e → of_expr e = None;
  atomic_step e1 σ1 e2 σ2 ef :
    atomic e1 →
    prim_step e1 σ1 e2 σ2 ef →
    is_Some (of_expr e2)
}.

Section language.
  Context `{Language E V St}.

  Definition cfg : Type := (list E * St)%type.
  Inductive step (ρ1 ρ2 : cfg) : Prop :=
    | step_atomic e1 σ1 e2 σ2 ef t1 t2 :
       ρ1 = (t1 ++ e1 :: t2, σ1) →
       ρ1 = (t1 ++ e2 :: t2 ++ option_list ef, σ2) →
       prim_step e1 σ1 e2 σ2 ef →
       step ρ1 ρ2.

  Definition steps := rtc step.
  Definition stepn := nsteps step.

  Definition is_ctx (ctx : E → E) : Prop :=
    (∀ e, is_Some (of_expr (ctx e)) → is_Some (of_expr e)) ∧
    (∀ e1 σ1 e2 σ2 ef,
      prim_step e1 σ1 e2 σ2 ef -> prim_step (ctx e1) σ1 (ctx e2) σ2 ef) ∧
    (∀ e1' σ1 e2 σ2 ef,
      of_expr e1' = None → prim_step (ctx e1') σ1 e2 σ2 ef →
      ∃ e2', e2 = ctx e2' ∧ prim_step e1' σ1 e2' σ2 ef).
End language.

