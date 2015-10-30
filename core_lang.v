Module Type CORE_LANG.

  (******************************************************************)
  (** ** Syntax, machine state, and atomic reductions **)
  (******************************************************************)

  (** Expressions and values **)
  Parameter expr : Type.

  Parameter is_value : expr -> Prop.
  Definition value : Type := {e: expr | is_value e}.
  Parameter is_value_dec : forall e, is_value e + ~is_value e.

  (** Shared machine state (e.g., the heap) **)
  Parameter state : Type.

  (** Primitive (single thread) machine configurations **)
  Definition prim_cfg : Type := (expr * state)%type.
  
  (** The primitive atomic optionally-forking stepping relation **)
  Parameter prim_step : prim_cfg -> prim_cfg -> option expr -> Prop.

  (** Some derived notions **)
  Definition reducible e: Prop :=
    exists sigma cfg' ef, prim_step (e, sigma) cfg' ef.

  Definition is_ctx (ctx : expr -> expr) : Prop :=
    (forall e, is_value (ctx e) -> is_value e) /\
    (forall e1 σ1 e2 σ2 ef, prim_step (e1, σ1) (e2, σ2) ef -> prim_step (ctx e1, σ1) (ctx e2, σ2) ef) /\
    (forall e1 σ1 e2 σ2 ef, ~is_value e1 -> prim_step (ctx e1, σ1) (e2, σ2) ef ->
                            exists e2', e2 = ctx e2' /\ prim_step (e1, σ1) (e2', σ2) ef).


  (** Atomic expressions **)
  Parameter atomic : expr -> Prop.

  (** Things ought to make sense. **)
  Axiom values_stuck :
    forall e, is_value e -> ~reducible e.

  Axiom atomic_not_value :
    forall e, atomic e -> ~is_value e.

  Axiom atomic_step: forall e σ e' σ' ef,
                       atomic e ->
                       prim_step (e, σ) (e', σ') ef ->
                       is_value e'.

End CORE_LANG.
