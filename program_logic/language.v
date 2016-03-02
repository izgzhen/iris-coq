From algebra Require Export cofe.

Structure language := Language {
  expr : Type;
  val : Type;
  state : Type;
  of_val : val → expr;
  to_val : expr → option val;
  atomic : expr → Prop;
  prim_step : expr → state → expr → state → option expr → Prop;
  to_of_val v : to_val (of_val v) = Some v;
  of_to_val e v : to_val e = Some v → of_val v = e;
  val_stuck e σ e' σ' ef : prim_step e σ e' σ' ef → to_val e = None;
  atomic_not_val e : atomic e → to_val e = None;
  atomic_step e1 σ1 e2 σ2 ef :
    atomic e1 →
    prim_step e1 σ1 e2 σ2 ef →
    is_Some (to_val e2)
}.
Arguments of_val {_} _.
Arguments to_val {_} _.
Arguments atomic {_} _.
Arguments prim_step {_} _ _ _ _ _.
Arguments to_of_val {_} _.
Arguments of_to_val {_} _ _ _.
Arguments val_stuck {_} _ _ _ _ _ _.
Arguments atomic_not_val {_} _ _.
Arguments atomic_step {_} _ _ _ _ _ _ _.

Canonical Structure stateC Σ := leibnizC (state Σ).

Definition cfg (Λ : language) := (list (expr Λ) * state Λ)%type.

Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.

  Definition reducible (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ' ef, prim_step e σ e' σ' ef.
  Inductive step (ρ1 ρ2 : cfg Λ) : Prop :=
    | step_atomic e1 σ1 e2 σ2 ef t1 t2 :
       ρ1 = (t1 ++ e1 :: t2, σ1) →
       ρ2 = (t1 ++ e2 :: t2 ++ option_list ef, σ2) →
       prim_step e1 σ1 e2 σ2 ef →
       step ρ1 ρ2.

  Lemma reducible_not_val e σ : reducible e σ → to_val e = None.
  Proof. intros (?&?&?&?); eauto using val_stuck. Qed.
  Lemma atomic_of_val v : ¬atomic (of_val v).
  Proof. by intros Hat%atomic_not_val; rewrite to_of_val in Hat. Qed.
  Global Instance: Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.
End language.

Class LanguageCtx (Λ : language) (K : expr Λ → expr Λ) := {
  fill_not_val e :
    to_val e = None → to_val (K e) = None;
  fill_step e1 σ1 e2 σ2 ef :
    prim_step e1 σ1 e2 σ2 ef →
    prim_step (K e1) σ1 (K e2) σ2 ef;
  fill_step_inv e1' σ1 e2 σ2 ef :
    to_val e1' = None → prim_step (K e1') σ1 e2 σ2 ef →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 e2' σ2 ef
}.
