From Coq.QArith Require Import Qcanon.
From algebra Require Export cmra.
From algebra Require Import upred.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments div _ _ !_ !_ /.

Inductive frac (A : Type) :=
  | Frac : Qp → A → frac A
  | FracUnit : frac A.
Arguments Frac {_} _ _.
Arguments FracUnit {_}.
Instance maybe_Frac {A} : Maybe2 (@Frac A) := λ x,
  match x with Frac q a => Some (q,a) | _ => None end.
Instance: Params (@Frac) 2.

Section cofe.
Context {A : cofeT}.
Implicit Types a b : A.
Implicit Types x y : frac A.

(* Cofe *)
Inductive frac_equiv : Equiv (frac A) :=
  | Frac_equiv q1 q2 a b : q1 = q2 → a ≡ b → Frac q1 a ≡ Frac q2 b
  | FracUnit_equiv : FracUnit ≡ FracUnit.
Existing Instance frac_equiv.
Inductive frac_dist : Dist (frac A) :=
  | Frac_dist q1 q2 a b n : q1 = q2 → a ≡{n}≡ b → Frac q1 a ≡{n}≡ Frac q2 b
  | FracUnit_dist n : FracUnit ≡{n}≡ FracUnit.
Existing Instance frac_dist.

Global Instance Frac_ne q n : Proper (dist n ==> dist n) (@Frac A q).
Proof. by constructor. Qed.
Global Instance Frac_proper q : Proper ((≡) ==> (≡)) (@Frac A q).
Proof. by constructor. Qed.
Global Instance Frac_inj : Inj2 (=) (≡) (≡) (@Frac A).
Proof. by inversion_clear 1. Qed.
Global Instance Frac_dist_inj n : Inj2 (=) (dist n) (dist n) (@Frac A).
Proof. by inversion_clear 1. Qed.

Program Definition frac_chain (c : chain (frac A)) (q : Qp) (a : A)
    (H : maybe2 Frac (c 0) = Some (q,a)) : chain A :=
  {| chain_car n := match c n return _ with Frac _ b => b | _ => a end |}.
Next Obligation.
  intros c q a ? n i ?; simpl.
  destruct (c 0) eqn:?; simplify_eq/=.
  by feed inversion (chain_cauchy c n i).
Qed.
Instance frac_compl : Compl (frac A) := λ c,
  match Some_dec (maybe2 Frac (c 0)) with
  | inleft (exist (q,a) H) => Frac q (compl (frac_chain c q a H))
  | inright _ => c 0
  end.
Definition frac_cofe_mixin : CofeMixin (frac A).
Proof.
  split.
  - intros mx my; split.
    + by destruct 1; subst; constructor; try apply equiv_dist.
    + intros Hxy; feed inversion (Hxy 0); subst; constructor; try done.
      apply equiv_dist=> n; by feed inversion (Hxy n).
  - intros n; split.
    + by intros [q a|]; constructor.
    + by destruct 1; constructor.
    + destruct 1; inversion_clear 1; constructor; etrans; eauto.
  - by inversion_clear 1; constructor; done || apply dist_S.
  - intros n c; unfold compl, frac_compl.
    destruct (Some_dec (maybe2 Frac (c 0))) as [[[q a] Hx]|].
    { assert (c 0 = Frac q a) by (by destruct (c 0); simplify_eq/=).
      assert (∃ b, c n = Frac q b) as [y Hy].
      { feed inversion (chain_cauchy c 0 n);
          eauto with lia congruence f_equal. }
      rewrite Hy; constructor; auto.
      by rewrite (conv_compl n (frac_chain c q a Hx)) /= Hy. }
    feed inversion (chain_cauchy c 0 n); first lia;
       constructor; destruct (c 0); simplify_eq/=.
Qed.
Canonical Structure fracC : cofeT := CofeT frac_cofe_mixin.
Global Instance frac_discrete : Discrete A → Discrete fracC.
Proof. by inversion_clear 2; constructor; done || apply (timeless _). Qed.
Global Instance frac_leibniz : LeibnizEquiv A → LeibnizEquiv (frac A).
Proof. by destruct 2; f_equal; done || apply leibniz_equiv. Qed.

Global Instance Frac_timeless q (a : A) : Timeless a → Timeless (Frac q a).
Proof. by inversion_clear 2; constructor; done || apply (timeless _). Qed.
Global Instance FracUnit_timeless : Timeless (@FracUnit A).
Proof. by inversion_clear 1; constructor. Qed.
End cofe.

Arguments fracC : clear implicits.

(* Functor on COFEs *)
Definition frac_map {A B} (f : A → B) (x : frac A) : frac B :=
  match x with
  | Frac q a => Frac q (f a) | FracUnit => FracUnit
  end.
Instance: Params (@frac_map) 2.

Lemma frac_map_id {A} (x : frac A) : frac_map id x = x.
Proof. by destruct x. Qed.
Lemma frac_map_compose {A B C} (f : A → B) (g : B → C) (x : frac A) :
  frac_map (g ∘ f) x = frac_map g (frac_map f x).
Proof. by destruct x. Qed.
Lemma frac_map_ext {A B : cofeT} (f g : A → B) x :
  (∀ x, f x ≡ g x) → frac_map f x ≡ frac_map g x.
Proof. by destruct x; constructor. Qed.
Instance frac_map_cmra_ne {A B : cofeT} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@frac_map A B).
Proof. intros f f' Hf; destruct 1; constructor; by try apply Hf. Qed.
Definition fracC_map {A B} (f : A -n> B) : fracC A -n> fracC B :=
  CofeMor (frac_map f).
Instance fracC_map_ne A B n : Proper (dist n ==> dist n) (@fracC_map A B).
Proof. intros f f' Hf []; constructor; by try apply Hf. Qed.

Section cmra.
Context {A : cmraT}.
Implicit Types a b : A.
Implicit Types x y : frac A.

(* CMRA *)
Instance frac_valid : Valid (frac A) := λ x,
  match x with Frac q a => (q ≤ 1)%Qc ∧ ✓ a | FracUnit => True end.
Instance frac_validN : ValidN (frac A) := λ n x,
  match x with Frac q a => (q ≤ 1)%Qc ∧ ✓{n} a | FracUnit => True end.
Global Instance frac_empty : Empty (frac A) := FracUnit.
Instance frac_core : Core (frac A) := λ _, ∅.
Instance frac_op : Op (frac A) := λ x y,
  match x, y with
  | Frac q1 a, Frac q2 b => Frac (q1 + q2) (a ⋅ b)
  | Frac q a, FracUnit | FracUnit, Frac q a => Frac q a
  | FracUnit, FracUnit => FracUnit
  end.
Instance frac_div : Div (frac A) := λ x y,
  match x, y with
  | _, FracUnit => x
  | Frac q1 a, Frac q2 b =>
     match q1 - q2 with Some q => Frac q (a ÷ b) | None => FracUnit end%Qp
  | FracUnit, _ => FracUnit
  end.

Lemma Frac_op q1 q2 a b : Frac q1 a ⋅ Frac q2 b = Frac (q1 + q2) (a ⋅ b).
Proof. done. Qed.

Definition frac_cmra_mixin : CMRAMixin (frac A).
Proof.
  split.
  - intros n []; destruct 1; constructor; by cofe_subst. 
  - constructor.
  - do 2 destruct 1; split; by cofe_subst.
  - do 2 destruct 1; simplify_eq/=; try case_match; constructor; by cofe_subst.
  - intros [q a|]; rewrite /= ?cmra_valid_validN; naive_solver eauto using O.
  - intros n [q a|]; destruct 1; split; auto using cmra_validN_S.
  - intros [q1 a1|] [q2 a2|] [q3 a3|]; constructor; by rewrite ?assoc.
  - intros [q1 a1|] [q2 a2|]; constructor; by rewrite 1?comm ?[(q1+_)%Qp]comm.
  - intros []; by constructor.
  - done.
  - by exists FracUnit.
  - intros n [q1 a1|] [q2 a2|]; destruct 1; split; eauto using cmra_validN_op_l.
    trans (q1 + q2)%Qp; simpl; last done.
    rewrite -{1}(Qcplus_0_r q1) -Qcplus_le_mono_l; auto using Qclt_le_weak.
  - intros [q1 a1|] [q2 a2|] [[q3 a3|] Hx];
      inversion_clear Hx; simplify_eq/=; auto.
    + rewrite Qp_op_minus. by constructor; [|apply cmra_op_div; exists a3].
    + rewrite Qp_minus_diag. by constructor.
  - intros n [q a|] y1 y2 Hx Hx'; last first.
    { by exists (∅, ∅); destruct y1, y2; inversion_clear Hx'. }
    destruct Hx, y1 as [q1 b1|], y2 as [q2 b2|].
    + apply (inj2 Frac) in Hx'; destruct Hx' as [-> ?].
      destruct (cmra_extend n a b1 b2) as ([z1 z2]&?&?&?); auto.
      exists (Frac q1 z1,Frac q2 z2); by repeat constructor.
    + exists (Frac q a, ∅); inversion_clear Hx'; by repeat constructor.
    + exists (∅, Frac q a); inversion_clear Hx'; by repeat constructor.
    + exfalso; inversion_clear Hx'.
Qed.
Canonical Structure fracR : cmraT := CMRAT frac_cofe_mixin frac_cmra_mixin.
Global Instance frac_cmra_unit : CMRAUnit fracR.
Proof. split. done. by intros []. apply _. Qed.
Global Instance frac_cmra_discrete : CMRADiscrete A → CMRADiscrete fracR.
Proof.
  split; first apply _.
  intros [q a|]; destruct 1; split; auto using cmra_discrete_valid.
Qed.

Lemma frac_validN_inv_l n y a : ✓{n} (Frac 1 a ⋅ y) → y = ∅.
Proof.
  destruct y as [q b|]; [|done]=> -[Hq ?]; destruct (Qcle_not_lt _ _ Hq).
  by rewrite -{1}(Qcplus_0_r 1) -Qcplus_lt_mono_l.
Qed.
Lemma frac_valid_inv_l y a : ✓ (Frac 1 a ⋅ y) → y = ∅.
Proof. intros. by apply frac_validN_inv_l with 0 a, cmra_valid_validN. Qed.

(** Internalized properties *)
Lemma frac_equivI {M} (x y : frac A) :
  (x ≡ y)%I ≡ (match x, y with
               | Frac q1 a, Frac q2 b => q1 = q2 ∧ a ≡ b
               | FracUnit, FracUnit => True
               | _, _ => False
               end : uPred M)%I.
Proof.
  uPred.unseal; do 2 split; first by destruct 1.
  by destruct x, y; destruct 1; try constructor.
Qed.
Lemma frac_validI {M} (x : frac A) :
  (✓ x)%I ≡ (if x is Frac q a then ■ (q ≤ 1)%Qc ∧ ✓ a else True : uPred M)%I.
Proof. uPred.unseal. by destruct x. Qed.

(** ** Local updates *)
Global Instance frac_local_update_full p a :
  LocalUpdate (λ x, if x is Frac q _ then q = 1%Qp else False) (λ _, Frac p a).
Proof.
  split; first by intros ???.
  by intros n [q b|] y; [|done]=> -> /frac_validN_inv_l ->.
Qed.
Global Instance frac_local_update `{!LocalUpdate Lv L} :
  LocalUpdate (λ x, if x is Frac _ a then Lv a else False) (frac_map L).
Proof.
  split; first apply _. intros n [p a|] [q b|]; simpl; try done.
  intros ? [??]; constructor; [done|by apply (local_updateN L)].
Qed.

(** Updates *)
Lemma frac_update_full (a1 a2 : A) : ✓ a2 → Frac 1 a1 ~~> Frac 1 a2.
Proof.
  move=> ? n y /frac_validN_inv_l ->. split. done. by apply cmra_valid_validN.
Qed.
Lemma frac_update (a1 a2 : A) p : a1 ~~> a2 → Frac p a1 ~~> Frac p a2.
Proof.
  intros Ha n [q b|] [??]; split; auto.
  apply cmra_validN_op_l with (core a1), Ha. by rewrite cmra_core_r.
Qed.
End cmra.

Arguments fracR : clear implicits.

(* Functor *)
Instance frac_map_cmra_monotone {A B : cmraT} (f : A → B) :
  CMRAMonotone f → CMRAMonotone (frac_map f).
Proof.
  split; try apply _.
  - intros n [p a|]; destruct 1; split; auto using validN_preserving.
  - intros [q1 a1|] [q2 a2|] [[q3 a3|] Hx];
      inversion Hx; setoid_subst; try apply: cmra_unit_least; auto.
    destruct (included_preserving f a1 (a1 ⋅ a3)) as [b ?].
    { by apply cmra_included_l. }
    by exists (Frac q3 b); constructor.
Qed.

Program Definition fracRF (F : rFunctor) : rFunctor := {|
  rFunctor_car A B := fracR (rFunctor_car F A B);
  rFunctor_map A1 A2 B1 B2 fg := fracC_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply fracC_map_ne, rFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(frac_map_id x).
  apply frac_map_ext=>y; apply rFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -frac_map_compose.
  apply frac_map_ext=>y; apply rFunctor_compose.
Qed.

Instance fracRF_contractive F :
  rFunctorContractive F → rFunctorContractive (fracRF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply fracC_map_ne, rFunctor_contractive.
Qed.
