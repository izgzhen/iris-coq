From Coq.QArith Require Import Qcanon.
From iris.algebra Require Export cmra.
From iris.algebra Require Import upred.
Local Arguments op _ _ !_ !_ /.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.

Inductive frac A := Frac { frac_perm : Qp ; frac_car : A  }.
Add Printing Constructor frac.
Arguments Frac {_} _ _.
Arguments frac_perm {_} _.
Arguments frac_car {_} _.
Instance: Params (@Frac) 2.

Section cofe.
Context {A : cofeT}.
Implicit Types a b : A.
Implicit Types x y : frac A.

(* Cofe *)
Instance frac_equiv : Equiv (frac A) := λ x y,
  frac_perm x = frac_perm y ∧ frac_car x ≡ frac_car y.
Instance frac_dist : Dist (frac A) := λ n x y,
  frac_perm x = frac_perm y ∧ frac_car x ≡{n}≡ frac_car y.

Global Instance Frac_ne q n : Proper (dist n ==> dist n) (@Frac A q).
Proof. by constructor. Qed.
Global Instance Frac_proper q : Proper ((≡) ==> (≡)) (@Frac A q).
Proof. by constructor. Qed.
Global Instance Frac_inj : Inj2 (=) (≡) (≡) (@Frac A).
Proof. by destruct 1. Qed.
Global Instance Frac_dist_inj n : Inj2 (=) (dist n) (dist n) (@Frac A).
Proof. by destruct 1. Qed.

Global Instance frac_perm_ne n : Proper (dist n ==> (=)) (@frac_perm A).
Proof. by destruct 1. Qed.
Global Instance frac_car_ne n : Proper (dist n ==> dist n) (@frac_car A).
Proof. by destruct 1. Qed.
Global Instance frac_perm_proper : Proper ((≡) ==> (=)) (@frac_perm A).
Proof. by destruct 1. Qed.
Global Instance frac_car_proper : Proper ((≡) ==> (≡)) (@frac_car A).
Proof. by destruct 1. Qed.

Program Definition frac_chain (c : chain (frac A)) : chain A :=
  {| chain_car n := match c n return _ with Frac _ b => b end |}.
Next Obligation.
  intros c n i ?; simpl. destruct (c 0) eqn:?; simplify_eq/=.
  by feed inversion (chain_cauchy c n i).
Qed.
Instance frac_compl : Compl (frac A) := λ c,
  Frac (frac_perm (c 0)) (compl (frac_chain c)).
Definition frac_cofe_mixin : CofeMixin (frac A).
Proof.
  split.
  - intros mx my; split.
    + by destruct 1; subst; constructor; try apply equiv_dist.
    + intros Hxy; feed inversion (Hxy 0); subst; constructor; try done.
      apply equiv_dist=> n; by feed inversion (Hxy n).
  - intros n; split.
    + by intros [q a]; constructor.
    + by destruct 1; constructor.
    + destruct 1; inversion_clear 1; constructor; etrans; eauto.
  - by inversion_clear 1; constructor; done || apply dist_S.
  - intros n c; constructor; simpl.
    + destruct (chain_cauchy c 0 n); auto with lia.
    + apply (conv_compl n (frac_chain c)).
Qed.
Canonical Structure fracC : cofeT := CofeT (frac A) frac_cofe_mixin.
Global Instance frac_discrete : Discrete A → Discrete fracC.
Proof. by inversion_clear 2; constructor; done || apply (timeless _). Qed.
Global Instance frac_leibniz : LeibnizEquiv A → LeibnizEquiv (frac A).
Proof. intros ? [??] [??] [??]; f_equal; done || by apply leibniz_equiv. Qed.

Global Instance Frac_timeless q (a : A) : Timeless a → Timeless (Frac q a).
Proof. by inversion_clear 2; constructor; done || apply (timeless _). Qed.
End cofe.

Arguments fracC : clear implicits.

(* Functor on COFEs *)
Definition frac_map {A B} (f : A → B) (x : frac A) : frac B :=
  match x with Frac q a => Frac q (f a) end.
Instance: Params (@frac_map) 2.

Lemma frac_map_id {A} (x : frac A) : frac_map id x = x.
Proof. by destruct x. Qed.
Lemma frac_map_compose {A B C} (f : A → B) (g : B → C) (x : frac A) :
  frac_map (g ∘ f) x = frac_map g (frac_map f x).
Proof. by destruct x. Qed.
Lemma frac_map_ext {A B : cofeT} (f g : A → B) x :
  (∀ x, f x ≡ g x) → frac_map f x ≡ frac_map g x.
Proof. destruct x; constructor; simpl; auto. Qed.
Instance frac_map_cmra_ne {A B : cofeT} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@frac_map A B).
Proof. intros f f' Hf [??] [??] [??]; constructor; by try apply Hf. Qed.
Definition fracC_map {A B} (f : A -n> B) : fracC A -n> fracC B :=
  CofeMor (frac_map f).
Instance fracC_map_ne A B n : Proper (dist n ==> dist n) (@fracC_map A B).
Proof. intros f f' Hf []; constructor; by try apply Hf. Qed.

Section cmra.
Context {A : cmraT}.
Implicit Types a b : A.
Implicit Types x y : frac A.

Instance frac_valid : Valid (frac A) := λ x,
  (frac_perm x ≤ 1)%Qc ∧ ✓ frac_car x.
Global Arguments frac_valid !_/.
Instance frac_validN : ValidN (frac A) := λ n x,
  (frac_perm x ≤ 1)%Qc ∧ ✓{n} frac_car x.
Global Arguments frac_validN _ !_/.
Instance frac_pcore : PCore (frac A) := λ _, None.
Instance frac_op : Op (frac A) := λ x y,
  Frac (frac_perm x + frac_perm y) (frac_car x ⋅ frac_car y).
Global Arguments frac_op !_ !_ /.

Lemma Frac_op q1 q2 a b : Frac q1 a ⋅ Frac q2 b = Frac (q1 + q2) (a ⋅ b).
Proof. done. Qed.

Definition frac_cmra_mixin : CMRAMixin (frac A).
Proof.
  split; try discriminate.
  - intros n [??] [??] [??] [??]; constructor; by cofe_subst. 
  - intros ? [??] [??] [??] [??]; split; by cofe_subst.
  - intros [??]; rewrite /= ?cmra_valid_validN; naive_solver eauto using O.
  - intros n [q a]; destruct 1; split; auto using cmra_validN_S.
  - intros [q1 a1] [q2 a2] [q3 a3]; constructor; by rewrite /= ?assoc.
  - intros [q1 a1] [q2 a2]; constructor; by rewrite /= 1?comm ?[(q1+_)%Qp]comm.
  - intros n [q1 a1] [q2 a2]; destruct 1; split; eauto using cmra_validN_op_l.
    trans (q1 + q2)%Qp; simpl; last done.
    rewrite -{1}(Qcplus_0_r q1) -Qcplus_le_mono_l; auto using Qclt_le_weak.
  - intros n [q a] y1 y2 Hx Hx'.
    destruct Hx, y1 as [q1 b1], y2 as [q2 b2].
    apply (inj2 Frac) in Hx'; destruct Hx' as [-> ?].
    destruct (cmra_extend n a b1 b2) as ([z1 z2]&?&?&?); auto.
    exists (Frac q1 z1,Frac q2 z2); by repeat constructor.
Qed.
Canonical Structure fracR := CMRAT (frac A) frac_cofe_mixin frac_cmra_mixin.

Global Instance frac_cmra_discrete : CMRADiscrete A → CMRADiscrete fracR.
Proof.
  split; first apply _.
  intros [q a]; destruct 1; split; auto using cmra_discrete_valid.
Qed.

(** Internalized properties *)
Lemma frac_equivI {M} (x y : frac A) :
  x ≡ y ⊣⊢ (frac_perm x = frac_perm y ∧ frac_car x ≡ frac_car y : uPred M).
Proof. by uPred.unseal. Qed.
Lemma frac_validI {M} (x : frac A) :
  ✓ x ⊣⊢ (■ (frac_perm x ≤ 1)%Qc ∧ ✓ frac_car x : uPred M).
Proof. by uPred.unseal. Qed.

(** Exclusive *)
Global Instance frac_full_exclusive a : Exclusive (Frac 1 a).
Proof.
  move => [[??]?][/Qcle_not_lt[]]; simpl in *.
  by rewrite -{1}(Qcplus_0_r 1) -Qcplus_lt_mono_l.
Qed.

(** ** Local updates *)
Global Instance frac_local_update `{!LocalUpdate Lv L} :
  LocalUpdate (λ x, Lv (frac_car x)) (frac_map L).
Proof.
  split; first apply _. intros n [p a] [q b]; simpl.
  intros ? [??]; constructor; [done|by apply (local_updateN L)].
Qed.

(** Updates *)
Lemma frac_update (a1 a2 : A) p : a1 ~~> a2 → Frac p a1 ~~> Frac p a2.
Proof.
  intros Ha n mz [??]; split; first by destruct mz.
  pose proof (Ha n (frac_car <$> mz)); destruct mz; naive_solver.
Qed.
End cmra.

Arguments fracR : clear implicits.

(* Functor *)
Instance frac_map_cmra_monotone {A B : cmraT} (f : A → B) :
  CMRAMonotone f → CMRAMonotone (frac_map f).
Proof.
  split; try apply _.
  - intros n [p a]; destruct 1; split; simpl in *; auto using validN_preserving.
  - intros [q1 a1] [q2 a2] [[q3 a3] [??]]; setoid_subst.
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
