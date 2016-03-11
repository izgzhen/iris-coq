From iris.algebra Require Export cmra.
From iris.algebra Require Import upred.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.

(* TODO: Really, we should have sums, and then this should be just "excl unit + A". *)
Inductive one_shot {A : Type} :=
  | OneShotPending : one_shot
  | Shot : A → one_shot
  | OneShotUnit : one_shot
  | OneShotBot : one_shot.
Arguments one_shot _ : clear implicits.
Instance maybe_Shot {A} : Maybe (@Shot A) := λ x,
  match x with Shot a => Some a | _ => None end.
Instance: Params (@Shot) 1.

Section cofe.
Context {A : cofeT}.
Implicit Types a b : A.
Implicit Types x y : one_shot A.

(* Cofe *)
Inductive one_shot_equiv : Equiv (one_shot A) :=
  | OneShotPending_equiv : OneShotPending ≡ OneShotPending
  | OneShot_equiv a b : a ≡ b → Shot a ≡ Shot b
  | OneShotUnit_equiv : OneShotUnit ≡ OneShotUnit
  | OneShotBot_equiv : OneShotBot ≡ OneShotBot.
Existing Instance one_shot_equiv.
Inductive one_shot_dist : Dist (one_shot A) :=
  | OneShotPending_dist n : OneShotPending ≡{n}≡ OneShotPending
  | OneShot_dist n a b : a ≡{n}≡ b → Shot a ≡{n}≡ Shot b
  | OneShotUnit_dist n : OneShotUnit ≡{n}≡ OneShotUnit
  | OneShotBot_dist n : OneShotBot ≡{n}≡ OneShotBot.
Existing Instance one_shot_dist.

Global Instance One_Shot_ne n : Proper (dist n ==> dist n) (@Shot A).
Proof. by constructor. Qed.
Global Instance One_Shot_proper : Proper ((≡) ==> (≡)) (@Shot A).
Proof. by constructor. Qed.
Global Instance One_Shot_inj : Inj (≡) (≡) (@Shot A).
Proof. by inversion_clear 1. Qed.
Global Instance One_Shot_dist_inj n : Inj (dist n) (dist n) (@Shot A).
Proof. by inversion_clear 1. Qed.

Program Definition one_shot_chain (c : chain (one_shot A)) (a : A)
    (H : maybe Shot (c 0) = Some a) : chain A :=
  {| chain_car n := match c n return _ with Shot b => b | _ => a end |}.
Next Obligation.
  intros c a ? n i ?; simpl.
  destruct (c 0) eqn:?; simplify_eq/=.
  by feed inversion (chain_cauchy c n i).
Qed.
Instance one_shot_compl : Compl (one_shot A) := λ c,
  match Some_dec (maybe Shot (c 0)) with
  | inleft (exist a H) => Shot (compl (one_shot_chain c a H))
  | inright _ => c 0
  end.
Definition one_shot_cofe_mixin : CofeMixin (one_shot A).
Proof.
  split.
  - intros mx my; split.
    + by destruct 1; subst; constructor; try apply equiv_dist.
    + intros Hxy; feed inversion (Hxy 0); subst; constructor; try done.
      apply equiv_dist=> n; by feed inversion (Hxy n).
  - intros n; split.
    + by intros [|a| |]; constructor.
    + by destruct 1; constructor.
    + destruct 1; inversion_clear 1; constructor; etrans; eauto.
  - by inversion_clear 1; constructor; done || apply dist_S.
  - intros n c; unfold compl, one_shot_compl.
    destruct (Some_dec (maybe Shot (c 0))) as [[a Hx]|].
    { assert (c 0 = Shot a) by (by destruct (c 0); simplify_eq/=).
      assert (∃ b, c n = Shot b) as [y Hy].
      { feed inversion (chain_cauchy c 0 n);
          eauto with lia congruence f_equal. }
      rewrite Hy; constructor; auto.
      by rewrite (conv_compl n (one_shot_chain c a Hx)) /= Hy. }
    feed inversion (chain_cauchy c 0 n); first lia;
       constructor; destruct (c 0); simplify_eq/=.
Qed.
Canonical Structure one_shotC : cofeT := CofeT one_shot_cofe_mixin.
Global Instance one_shot_discrete : Discrete A → Discrete one_shotC.
Proof. by inversion_clear 2; constructor; done || apply (timeless _). Qed.
Global Instance one_shot_leibniz : LeibnizEquiv A → LeibnizEquiv (one_shot A).
Proof. by destruct 2; f_equal; done || apply leibniz_equiv. Qed.

Global Instance Shot_timeless (a : A) : Timeless a → Timeless (Shot a).
Proof. by inversion_clear 2; constructor; done || apply (timeless _). Qed.
Global Instance OneShotUnit_timeless : Timeless (@OneShotUnit A).
Proof. by inversion_clear 1; constructor. Qed.
End cofe.

Arguments one_shotC : clear implicits.

