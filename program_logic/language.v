From iris.algebra Require Export cofe.

Structure language := Language {
  expr : Type;
  val : Type;
  state : Type;
  of_val : val → expr;
  to_val : expr → option val;
  prim_step : expr → state → expr → state → option expr → Prop;
  to_of_val v : to_val (of_val v) = Some v;
  of_to_val e v : to_val e = Some v → of_val v = e;
  val_stuck e σ e' σ' ef : prim_step e σ e' σ' ef → to_val e = None
}.
Arguments of_val {_} _.
Arguments to_val {_} _.
Arguments prim_step {_} _ _ _ _ _.
Arguments to_of_val {_} _.
Arguments of_to_val {_} _ _ _.
Arguments val_stuck {_} _ _ _ _ _ _.

Canonical Structure stateC Λ := leibnizC (state Λ).
Canonical Structure valC Λ := leibnizC (val Λ).
Canonical Structure exprC Λ := leibnizC (expr Λ).

Definition cfg (Λ : language) := (list (expr Λ) * state Λ)%type.

Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.

  Definition reducible (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ' ef, prim_step e σ e' σ' ef.
  Definition atomic (e : expr Λ) : Prop :=
    ∀ σ e' σ' ef, prim_step e σ e' σ' ef → is_Some (to_val e').
  Inductive step (ρ1 ρ2 : cfg Λ) : Prop :=
    | step_atomic e1 σ1 e2 σ2 ef t1 t2 :
       ρ1 = (t1 ++ e1 :: t2, σ1) →
       ρ2 = (t1 ++ e2 :: t2 ++ option_list ef, σ2) →
       prim_step e1 σ1 e2 σ2 ef →
       step ρ1 ρ2.

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.
  Lemma reducible_not_val e σ : reducible e σ → to_val e = None.
  Proof. intros (?&?&?&?); eauto using val_stuck. Qed.
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
