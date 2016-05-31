From iris.algebra Require Export cmra.
From iris.algebra Require Import upred.
Local Arguments pcore _ _ !_ /.
Local Arguments cmra_pcore _ !_ /.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments cmra_validN _ _ !_ /.
Local Arguments cmra_valid _  !_ /.

(* TODO: Really, we should have sums, and then this should be just "excl unit + A". *)
Inductive one_shot (A : Type) :=
  | OneShotPending : one_shot A
  | Shot : A → one_shot A
  | OneShotBot : one_shot A.
Arguments OneShotPending {_}.
Arguments Shot {_} _.
Arguments OneShotBot {_}.

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
  | OneShotBot_equiv : OneShotBot ≡ OneShotBot.
Existing Instance one_shot_equiv.
Inductive one_shot_dist : Dist (one_shot A) :=
  | OneShotPending_dist n : OneShotPending ≡{n}≡ OneShotPending
  | OneShot_dist n a b : a ≡{n}≡ b → Shot a ≡{n}≡ Shot b
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

Program Definition one_shot_chain (c : chain (one_shot A)) (a : A) : chain A :=
  {| chain_car n := match c n return _ with Shot b => b | _ => a end |}.
Next Obligation. intros c a n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
Instance one_shot_compl : Compl (one_shot A) := λ c,
  match c 0 with Shot a => Shot (compl (one_shot_chain c a)) | x => x end.
Definition one_shot_cofe_mixin : CofeMixin (one_shot A).
Proof.
  split.
  - intros mx my; split.
    + by destruct 1; subst; constructor; try apply equiv_dist.
    + intros Hxy; feed inversion (Hxy 0); subst; constructor; try done.
      apply equiv_dist=> n; by feed inversion (Hxy n).
  - intros n; split.
    + by intros [|a|]; constructor.
    + by destruct 1; constructor.
    + destruct 1; inversion_clear 1; constructor; etrans; eauto.
  - by inversion_clear 1; constructor; done || apply dist_S.
  - intros n c; rewrite /compl /one_shot_compl.
    feed inversion (chain_cauchy c 0 n); first auto with lia; constructor.
    rewrite (conv_compl n (one_shot_chain c _)) /=. destruct (c n); naive_solver.
Qed.
Canonical Structure one_shotC : cofeT := CofeT (one_shot A) one_shot_cofe_mixin.
Global Instance one_shot_discrete : Discrete A → Discrete one_shotC.
Proof. by inversion_clear 2; constructor; done || apply (timeless _). Qed.
Global Instance one_shot_leibniz : LeibnizEquiv A → LeibnizEquiv (one_shot A).
Proof. by destruct 2; f_equal; done || apply leibniz_equiv. Qed.

Global Instance Shot_timeless (a : A) : Timeless a → Timeless (Shot a).
Proof. by inversion_clear 2; constructor; done || apply (timeless _). Qed.
End cofe.

Arguments one_shotC : clear implicits.

(* Functor on COFEs *)
Definition one_shot_map {A B} (f : A → B) (x : one_shot A) : one_shot B :=
  match x with
  | OneShotPending => OneShotPending
  | Shot a => Shot (f a)
  | OneShotBot => OneShotBot
  end.
Instance: Params (@one_shot_map) 2.

Lemma one_shot_map_id {A} (x : one_shot A) : one_shot_map id x = x.
Proof. by destruct x. Qed.
Lemma one_shot_map_compose {A B C} (f : A → B) (g : B → C) (x : one_shot A) :
  one_shot_map (g ∘ f) x = one_shot_map g (one_shot_map f x).
Proof. by destruct x. Qed.
Lemma one_shot_map_ext {A B : cofeT} (f g : A → B) x :
  (∀ x, f x ≡ g x) → one_shot_map f x ≡ one_shot_map g x.
Proof. by destruct x; constructor. Qed.
Instance one_shot_map_cmra_ne {A B : cofeT} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@one_shot_map A B).
Proof. intros f f' Hf; destruct 1; constructor; by try apply Hf. Qed.
Definition one_shotC_map {A B} (f : A -n> B) : one_shotC A -n> one_shotC B :=
  CofeMor (one_shot_map f).
Instance one_shotC_map_ne A B n : Proper (dist n ==> dist n) (@one_shotC_map A B).
Proof. intros f f' Hf []; constructor; by try apply Hf. Qed.

Section cmra.
Context {A : cmraT}.
Implicit Types a b : A.
Implicit Types x y : one_shot A.

(* CMRA *)
Instance one_shot_valid : Valid (one_shot A) := λ x,
  match x with
  | OneShotPending => True
  | Shot a => ✓ a
  | OneShotBot => False
  end.
Instance one_shot_validN : ValidN (one_shot A) := λ n x,
  match x with
  | OneShotPending => True
  | Shot a => ✓{n} a
  | OneShotBot => False
  end.
Instance one_shot_pcore : PCore (one_shot A) := λ x,
  match x with
  | OneShotPending => None
  | Shot a => Shot <$> pcore a
  | OneShotBot => Some OneShotBot
  end.
Instance one_shot_op : Op (one_shot A) := λ x y,
  match x, y with
  | Shot a, Shot b => Shot (a ⋅ b)
  | _, _ => OneShotBot
  end.

Lemma Shot_op a b : Shot a ⋅ Shot b = Shot (a ⋅ b).
Proof. done. Qed.

Lemma one_shot_included x y :
  x ≼ y ↔ y = OneShotBot ∨ ∃ a b, x = Shot a ∧ y = Shot b ∧ a ≼ b.
Proof.
  split.
  - intros [z Hy]; destruct x as [|a|], z as [|b|]; inversion_clear Hy; auto.
    right; eexists _, _; split_and!; eauto.
    setoid_subst; eauto using cmra_included_l.
  - intros [->|(a&b&->&->&c&?)].
    + destruct x; exists OneShotBot; constructor.
    + exists (Shot c); by constructor.
Qed.

Lemma one_shot_cmra_mixin : CMRAMixin (one_shot A).
Proof.
  split.
  - intros n []; destruct 1; constructor; by cofe_subst. 
  - intros ???? [n|n a b Hab|n] [=]; subst; eauto.
    destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
    destruct (cmra_pcore_ne n a b ca) as (cb&->&?); auto.
    exists (Shot cb); by repeat constructor.
  - intros ? [|a|] [|b|] H; inversion_clear H; cofe_subst; done.
  - intros [|a|]; rewrite /= ?cmra_valid_validN; naive_solver eauto using O.
  - intros n [|a|]; simpl; auto using cmra_validN_S.
  - intros [|a1|] [|a2|] [|a3|]; constructor; by rewrite ?assoc.
  - intros [|a1|] [|a2|]; constructor; by rewrite 1?comm.
  - intros [|a|] ? [=]; subst; auto.
    destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
    constructor; eauto using cmra_pcore_l.
  - intros [|a|] ? [=]; subst; auto.
    destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
    feed inversion (cmra_pcore_idemp a ca); repeat constructor; auto.
  - intros x y ? [->|(a&b&->&->&?)]%one_shot_included [=].
    { exists OneShotBot. rewrite one_shot_included; eauto. }
    destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
    destruct (cmra_pcore_preserving a b ca) as (cb&->&?); auto.
    exists (Shot cb). rewrite one_shot_included; eauto 10.
  - intros n [|a1|] [|a2|]; simpl; eauto using cmra_validN_op_l; done.
  - intros n [|a|] y1 y2 Hx Hx'.
    + destruct y1, y2; exfalso; by inversion_clear Hx'.
    + destruct y1 as [|b1|], y2 as [|b2|]; try (exfalso; by inversion_clear Hx').
       apply (inj Shot) in Hx'.
       destruct (cmra_extend n a b1 b2) as ([z1 z2]&?&?&?); auto.
       exists (Shot z1, Shot z2). by repeat constructor.
    + by exists (OneShotBot, OneShotBot); destruct y1, y2; inversion_clear Hx'.
Qed.
Canonical Structure one_shotR :=
  CMRAT (one_shot A) one_shot_cofe_mixin one_shot_cmra_mixin.

Global Instance one_shot_cmra_discrete : CMRADiscrete A → CMRADiscrete one_shotR.
Proof.
  split; first apply _.
  intros [|a|]; simpl; auto using cmra_discrete_valid.
Qed.

Global Instance Shot_persistent a : Persistent a → Persistent (Shot a).
Proof. rewrite /Persistent /=. inversion_clear 1; by repeat constructor. Qed.

(** Internalized properties *)
Lemma one_shot_equivI {M} (x y : one_shot A) :
  x ≡ y ⊣⊢ (match x, y with
            | OneShotPending, OneShotPending => True
            | Shot a, Shot b => a ≡ b
            | OneShotBot, OneShotBot => True
            | _, _ => False
            end : uPred M).
Proof.
  uPred.unseal; do 2 split; first by destruct 1.
  by destruct x, y; try destruct 1; try constructor.
Qed.
Lemma one_shot_validI {M} (x : one_shot A) :
  ✓ x ⊣⊢ (match x with
          | Shot a => ✓ a 
          | OneShotBot => False
          | _ => True
          end : uPred M).
Proof. uPred.unseal. by destruct x. Qed.

(** Updates *)
Lemma one_shot_update_shoot (a : A) : ✓ a → OneShotPending ~~> Shot a.
Proof. move=> ? n [y|] //= ?. by apply cmra_valid_validN. Qed.
Lemma one_shot_update (a1 a2 : A) : a1 ~~> a2 → Shot a1 ~~> Shot a2.
Proof.
  intros Ha n [[|b|]|] ?; simpl in *; auto.
  - by apply (Ha n (Some b)).
  - by apply (Ha n None).
Qed.
Lemma one_shot_updateP (P : A → Prop) (Q : one_shot A → Prop) a :
  a ~~>: P → (∀ b, P b → Q (Shot b)) → Shot a ~~>: Q.
Proof.
  intros Hx HP n mf Hm. destruct mf as [[|b|]|]; try by destruct Hm.
  - destruct (Hx n (Some b)) as (c&?&?); naive_solver.
  - destruct (Hx n None) as (c&?&?); naive_solver eauto using cmra_validN_op_l.
Qed.
Lemma one_shot_updateP' (P : A → Prop) a :
  a ~~>: P → Shot a ~~>: λ m', ∃ b, m' = Shot b ∧ P b.
Proof. eauto using one_shot_updateP. Qed.
End cmra.

Arguments one_shotR : clear implicits.

(* Functor *)
Instance one_shot_map_cmra_monotone {A B : cmraT} (f : A → B) :
  CMRAMonotone f → CMRAMonotone (one_shot_map f).
Proof.
  split; try apply _.
  - intros n [|a|]; simpl; auto using validN_preserving.
  - intros x y; rewrite !one_shot_included.
    intros [->|(a&b&->&->&?)]; simpl; eauto 10 using included_preserving.
Qed.

Program Definition one_shotRF (F : rFunctor) : rFunctor := {|
  rFunctor_car A B := one_shotR (rFunctor_car F A B);
  rFunctor_map A1 A2 B1 B2 fg := one_shotC_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply one_shotC_map_ne, rFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(one_shot_map_id x).
  apply one_shot_map_ext=>y; apply rFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -one_shot_map_compose.
  apply one_shot_map_ext=>y; apply rFunctor_compose.
Qed.

Instance one_shotRF_contractive F :
  rFunctorContractive F → rFunctorContractive (one_shotRF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply one_shotC_map_ne, rFunctor_contractive.
Qed.
