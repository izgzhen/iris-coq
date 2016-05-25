From iris.algebra Require Export cmra.
From iris.algebra Require Import upred.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments cmra_validN _ _ !_ /.
Local Arguments cmra_valid _  !_ /.

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
    + by intros [|a| |]; constructor.
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
Global Instance OneShotUnit_timeless : Timeless (@OneShotUnit A).
Proof. by inversion_clear 1; constructor. Qed.
End cofe.

Arguments one_shotC : clear implicits.

(* Functor on COFEs *)
Definition one_shot_map {A B} (f : A → B) (x : one_shot A) : one_shot B :=
  match x with
  | OneShotPending => OneShotPending
  | Shot a => Shot (f a)
  | OneShotUnit => OneShotUnit
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
  | OneShotUnit => True
  | OneShotBot => False
  end.
Instance one_shot_validN : ValidN (one_shot A) := λ n x,
  match x with
  | OneShotPending => True
  | Shot a => ✓{n} a
  | OneShotUnit => True
  | OneShotBot => False
  end.
Global Instance one_shot_empty : Empty (one_shot A) := OneShotUnit.
Instance one_shot_core : Core (one_shot A) := λ x,
  match x with
  | Shot a => Shot (core a)
  | OneShotBot => OneShotBot
  | _ => ∅
  end.
Instance one_shot_op : Op (one_shot A) := λ x y,
  match x, y with
  | Shot a, Shot b => Shot (a ⋅ b)
  | Shot a, OneShotUnit | OneShotUnit, Shot a => Shot a
  | OneShotUnit, OneShotPending | OneShotPending, OneShotUnit => OneShotPending
  | OneShotUnit, OneShotUnit => OneShotUnit
  | _, _ => OneShotBot
  end.

Lemma Shot_op a b : Shot a ⋅ Shot b = Shot (a ⋅ b).
Proof. done. Qed.
Lemma Shot_core a : core (Shot a) = Shot (core a).
Proof. done. Qed.

Lemma Shot_incl a b : Shot a ≼ Shot b ↔ a ≼ b.
Proof.
  split; intros [c H].
  - destruct c; inversion_clear H; first by eexists.
    by rewrite (_ : b ≡ a).
  - exists (Shot c). constructor. done.
Qed. 

Definition one_shot_cmra_mixin : CMRAMixin (one_shot A).
Proof.
  split.
  - intros n []; destruct 1; constructor; by cofe_subst. 
  - intros ? [|a| |] [|b| |] H; inversion_clear H; constructor; by f_equiv.
  - intros ? [|a| |] [|b| |] H; inversion_clear H; cofe_subst; done.
  - intros [|a| |]; rewrite /= ?cmra_valid_validN; naive_solver eauto using O.
  - intros n [|a| |]; simpl; auto using cmra_validN_S.
  - intros [|a1| |] [|a2| |] [|a3| |]; constructor; by rewrite ?assoc.
  - intros [|a1| |] [|a2| |]; constructor; by rewrite 1?comm.
  - intros [|a| |]; constructor; []. exact: cmra_core_l.
  - intros [|a| |]; constructor; []. exact: cmra_core_idemp.
  - intros [|a1| |] [|a2| |]; simpl;
      try solve [ by exists OneShotUnit; constructor
                | by exists OneShotBot; constructor
                | by intros [[|a3| |] H]; inversion_clear H ].
    + intros H%Shot_incl. apply Shot_incl, cmra_core_preserving. done.
    + intros _. exists (Shot (core a2)). by constructor.
  - intros n [|a1| |] [|a2| |]; simpl; eauto using cmra_validN_op_l; done.
  - intros n [|a| |] y1 y2 Hx Hx'; last 2 first.
    + by exists (∅, ∅); destruct y1, y2; inversion_clear Hx'.
    + by exists (OneShotBot, OneShotBot); destruct y1, y2; inversion_clear Hx'.
    + destruct y1, y2; try (exfalso; by inversion_clear Hx').
      * by exists (OneShotPending, OneShotUnit).
      * by exists (OneShotUnit, OneShotPending).
    +  destruct y1 as [|b1 | |], y2 as [|b2| |]; try (exfalso; by inversion_clear Hx').
       * apply (inj Shot) in Hx'.
         destruct (cmra_extend n a b1 b2) as ([z1 z2]&?&?&?); auto.
         exists (Shot z1, Shot z2). by repeat constructor.
       * exists (Shot a, ∅). inversion_clear Hx'. by repeat constructor.
       * exists (∅, Shot a). inversion_clear Hx'. by repeat constructor.
Qed.
Canonical Structure one_shotR : cmraT :=
  CMRAT (one_shot A) one_shot_cofe_mixin one_shot_cmra_mixin.
Global Instance one_shot_cmra_unit : CMRAUnit one_shotR.
Proof. split. done. by intros []. apply _. Qed.
Global Instance one_shot_cmra_discrete : CMRADiscrete A → CMRADiscrete one_shotR.
Proof.
  split; first apply _.
  intros [|a| |]; simpl; auto using cmra_discrete_valid.
Qed.

Global Instance Shot_persistent a : Persistent a → Persistent (Shot a).
Proof. by constructor. Qed.

Lemma one_shot_validN_inv_l n y : ✓{n} (OneShotPending ⋅ y) → y = ∅.
Proof. by destruct y; inversion_clear 1. Qed.
Lemma one_shot_valid_inv_l y : ✓ (OneShotPending ⋅ y) → y = ∅.
Proof. intros. by apply one_shot_validN_inv_l with 0, cmra_valid_validN. Qed.
Lemma one_shot_bot_largest y : y ≼ OneShotBot.
Proof. destruct y; exists OneShotBot; constructor. Qed.

(** Internalized properties *)
Lemma one_shot_equivI {M} (x y : one_shot A) :
  (x ≡ y) ⊣⊢ (match x, y with
               | OneShotPending, OneShotPending => True
               | Shot a, Shot b => a ≡ b
               | OneShotUnit, OneShotUnit => True
               | OneShotBot, OneShotBot => True
               | _, _ => False
               end : uPred M).
Proof.
  uPred.unseal; do 2 split; first by destruct 1.
  by destruct x, y; try destruct 1; try constructor.
Qed.
Lemma one_shot_validI {M} (x : one_shot A) :
  (✓ x) ⊣⊢ (match x with
            | Shot a => ✓ a 
            | OneShotBot => False
            | _ => True
            end : uPred M).
Proof. uPred.unseal. by destruct x. Qed.

(** Updates *)
Lemma one_shot_update_shoot (a : A) : ✓ a → OneShotPending ~~> Shot a.
Proof.
  move=> ? n y /one_shot_validN_inv_l ->. by apply cmra_valid_validN.
Qed.
Lemma one_shot_update (a1 a2 : A) : a1 ~~> a2 → Shot a1 ~~> Shot a2.
Proof.
  intros Ha n [|b| |] ?; simpl; auto.
  apply cmra_validN_op_l with (core a1), Ha. by rewrite cmra_core_r.
Qed.
Lemma one_shot_updateP (P : A → Prop) (Q : one_shot A → Prop) a :
  a ~~>: P → (∀ b, P b → Q (Shot b)) → Shot a ~~>: Q.
Proof.
  intros Hx HP n mf Hm. destruct mf as [|b| |]; try by destruct Hm.
  - destruct (Hx n b) as (c&?&?); try done.
    exists (Shot c). auto.
  - destruct (Hx n (core a)) as (c&?&?); try done.
    { by rewrite cmra_core_r. }
    exists (Shot c). split; simpl; eauto using cmra_validN_op_l.
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
  - intros n [|a| |]; simpl; auto using validN_preserving.
  - intros [|a1| |] [|a2| |] [[|a3| |] Hx];
      inversion Hx; setoid_subst; try apply cmra_unit_least;
        try apply one_shot_bot_largest; auto; [].
    destruct (included_preserving f a1 (a1 ⋅ a3)) as [b ?].
    { by apply cmra_included_l. }
    by exists (Shot b); constructor.
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
