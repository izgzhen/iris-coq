From iris.algebra Require Export ofe.
Set Default Proof Using "Type".

Structure language := Language {
  expr : Type;
  val : Type;
  state : Type;
  of_val : val → expr;
  to_val : expr → option val;
  prim_step : expr → state → expr → state → list expr → Prop;
  to_of_val v : to_val (of_val v) = Some v;
  of_to_val e v : to_val e = Some v → of_val v = e;
  val_stuck e σ e' σ' efs : prim_step e σ e' σ' efs → to_val e = None
}.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.
Bind Scope expr_scope with expr.
Bind Scope val_scope with val.
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

Class LanguageCtx (Λ : language) (K : expr Λ → expr Λ) := {
  fill_not_val e :
    to_val e = None → to_val (K e) = None;
  fill_step e1 σ1 e2 σ2 efs :
    prim_step e1 σ1 e2 σ2 efs →
    prim_step (K e1) σ1 (K e2) σ2 efs;
  fill_step_inv e1' σ1 e2 σ2 efs :
    to_val e1' = None → prim_step (K e1') σ1 e2 σ2 efs →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 e2' σ2 efs
}.

Instance language_ctx_id Λ : LanguageCtx Λ id.
Proof. constructor; naive_solver. Qed.

Variant pbit := progress | noprogress.

Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.

  Definition reducible (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ' efs, prim_step e σ e' σ' efs.
  Definition irreducible (e : expr Λ) (σ : state Λ) :=
    ∀ e' σ' efs, ¬prim_step e σ e' σ' efs.
  Definition progressive (e : expr Λ) (σ : state Λ) :=
    is_Some (to_val e) ∨ reducible e σ.

  (* This (weak) form of atomicity is enough to open invariants when WP ensures
     safety, i.e., programs never can get stuck.  We have an example in
     lambdaRust of an expression that is atomic in this sense, but not in the
     stronger sense defined below, and we have to be able to open invariants
     around that expression.  See `CasStuckS` in
     [lambdaRust](https://gitlab.mpi-sws.org/FP/LambdaRust-coq/blob/master/theories/lang/lang.v). *)
  Class Atomic (e : expr Λ) : Prop :=
    atomic σ e' σ' efs : prim_step e σ e' σ' efs → irreducible e' σ'.

  (* To open invariants with a WP that does not ensure safety, we need a
     stronger form of atomicity.  With the above definition, in case `e` reduces
     to a stuck non-value, there is no proof that the invariants have been
     established again. *)
  Class StronglyAtomic (e : expr Λ) : Prop :=
    strongly_atomic σ e' σ' efs : prim_step e σ e' σ' efs → is_Some (to_val e').

  Inductive step (ρ1 ρ2 : cfg Λ) : Prop :=
    | step_atomic e1 σ1 e2 σ2 efs t1 t2 :
       ρ1 = (t1 ++ e1 :: t2, σ1) →
       ρ2 = (t1 ++ e2 :: t2 ++ efs, σ2) →
       prim_step e1 σ1 e2 σ2 efs →
       step ρ1 ρ2.

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.

  Lemma not_reducible e σ : ¬reducible e σ ↔ irreducible e σ.
  Proof. unfold reducible, irreducible. naive_solver. Qed.
  Lemma reducible_not_val e σ : reducible e σ → to_val e = None.
  Proof. intros (?&?&?&?); eauto using val_stuck. Qed.
  Lemma val_irreducible e σ : is_Some (to_val e) → irreducible e σ.
  Proof. intros [??] ??? ?%val_stuck. by destruct (to_val e). Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Lemma strongly_atomic_atomic e : StronglyAtomic e → Atomic e.
  Proof. unfold StronglyAtomic, Atomic. eauto using val_irreducible. Qed.

  Lemma reducible_fill `{LanguageCtx Λ K} e σ :
    to_val e = None → reducible (K e) σ → reducible e σ.
  Proof.
    intros ? (e'&σ'&efs&Hstep); unfold reducible.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto.
  Qed.
  Lemma irreducible_fill `{LanguageCtx Λ K} e σ :
    to_val e = None → irreducible e σ → irreducible (K e) σ.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.

  Lemma step_Permutation (t1 t1' t2 : list (expr Λ)) σ1 σ2 :
    t1 ≡ₚ t1' → step (t1,σ1) (t2,σ2) → ∃ t2', t2 ≡ₚ t2' ∧ step (t1',σ1) (t2',σ2).
  Proof.
    intros Ht [e1 σ1' e2 σ2' efs tl tr ?? Hstep]; simplify_eq/=.
    move: Ht; rewrite -Permutation_middle (symmetry_iff (≡ₚ)).
    intros (tl'&tr'&->&Ht)%Permutation_cons_inv.
    exists (tl' ++ e2 :: tr' ++ efs); split; [|by econstructor].
    by rewrite -!Permutation_middle !assoc_L Ht.
  Qed.

  Class PureExec (P : Prop) (e1 e2 : expr Λ) := {
    pure_exec_safe σ :
      P → reducible e1 σ;
    pure_exec_puredet σ1 e2' σ2 efs :
      P → prim_step e1 σ1 e2' σ2 efs → σ1 = σ2 ∧ e2 = e2' ∧ efs = [];
  }.

  Lemma hoist_pred_pure_exec (P : Prop) (e1 e2 : expr Λ) :
    (P → PureExec True e1 e2) →
    PureExec P e1 e2.
  Proof. intros HPE. split; intros; eapply HPE; eauto. Qed.

  (* This is a family of frequent assumptions for PureExec *)
  Class IntoVal (e : expr Λ) (v : val Λ) :=
    into_val : to_val e = Some v.

  Class AsVal (e : expr Λ) := as_val : is_Some (to_val e).
  (* There is no instance [IntoVal → AsVal] as often one can solve [AsVal] more
  efficiently since no witness has to be computed. *)
  Global Instance as_vals_of_val vs : TCForall AsVal (of_val <$> vs).
  Proof.
    apply TCForall_Forall, Forall_fmap, Forall_true=> v.
    rewrite /AsVal /= to_of_val; eauto.
  Qed.
End language.
