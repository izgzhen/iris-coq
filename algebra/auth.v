From iris.algebra Require Export excl updates.
From iris.algebra Require Import upred.
Local Arguments valid _ _ !_ /.
Local Arguments validN _ _ _ !_ /.

Record auth (A : Type) := Auth { authoritative : option (excl A); auth_own : A }.
Add Printing Constructor auth.
Arguments Auth {_} _ _.
Arguments authoritative {_} _.
Arguments auth_own {_} _.
Notation "◯ a" := (Auth None a) (at level 20).
Notation "● a" := (Auth (Excl' a) ∅) (at level 20).

(* COFE *)
Section cofe.
Context {A : cofeT}.
Implicit Types a : option (excl A).
Implicit Types b : A.
Implicit Types x y : auth A.

Instance auth_equiv : Equiv (auth A) := λ x y,
  authoritative x ≡ authoritative y ∧ auth_own x ≡ auth_own y.
Instance auth_dist : Dist (auth A) := λ n x y,
  authoritative x ≡{n}≡ authoritative y ∧ auth_own x ≡{n}≡ auth_own y.

Global Instance Auth_ne : Proper (dist n ==> dist n ==> dist n) (@Auth A).
Proof. by split. Qed.
Global Instance Auth_proper : Proper ((≡) ==> (≡) ==> (≡)) (@Auth A).
Proof. by split. Qed.
Global Instance authoritative_ne: Proper (dist n ==> dist n) (@authoritative A).
Proof. by destruct 1. Qed.
Global Instance authoritative_proper : Proper ((≡) ==> (≡)) (@authoritative A).
Proof. by destruct 1. Qed.
Global Instance own_ne : Proper (dist n ==> dist n) (@auth_own A).
Proof. by destruct 1. Qed.
Global Instance own_proper : Proper ((≡) ==> (≡)) (@auth_own A).
Proof. by destruct 1. Qed.

Instance auth_compl : Compl (auth A) := λ c,
  Auth (compl (chain_map authoritative c)) (compl (chain_map auth_own c)).
Definition auth_cofe_mixin : CofeMixin (auth A).
Proof.
  split.
  - intros x y; unfold dist, auth_dist, equiv, auth_equiv.
    rewrite !equiv_dist; naive_solver.
  - intros n; split.
    + by intros ?; split.
    + by intros ?? [??]; split; symmetry.
    + intros ??? [??] [??]; split; etrans; eauto.
  - by intros ? [??] [??] [??]; split; apply dist_S.
  - intros n c; split. apply (conv_compl n (chain_map authoritative c)).
    apply (conv_compl n (chain_map auth_own c)).
Qed.
Canonical Structure authC := CofeT (auth A) auth_cofe_mixin.

Global Instance Auth_timeless a b :
  Timeless a → Timeless b → Timeless (Auth a b).
Proof. by intros ?? [??] [??]; split; apply: timeless. Qed.
Global Instance auth_discrete : Discrete A → Discrete authC.
Proof. intros ? [??]; apply _. Qed.
Global Instance auth_leibniz : LeibnizEquiv A → LeibnizEquiv (auth A).
Proof. by intros ? [??] [??] [??]; f_equal/=; apply leibniz_equiv. Qed.
End cofe.

Arguments authC : clear implicits.

(* CMRA *)
Section cmra.
Context {A : ucmraT}.
Implicit Types a b : A.
Implicit Types x y : auth A.

Instance auth_valid : Valid (auth A) := λ x,
  match authoritative x with
  | Excl' a => (∀ n, auth_own x ≼{n} a) ∧ ✓ a
  | None => ✓ auth_own x
  | ExclBot' => False
  end.
Global Arguments auth_valid !_ /.
Instance auth_validN : ValidN (auth A) := λ n x,
  match authoritative x with
  | Excl' a => auth_own x ≼{n} a ∧ ✓{n} a
  | None => ✓{n} auth_own x
  | ExclBot' => False
  end.
Global Arguments auth_validN _ !_ /.
Instance auth_pcore : PCore (auth A) := λ x,
  Some (Auth (core (authoritative x)) (core (auth_own x))).
Instance auth_op : Op (auth A) := λ x y,
  Auth (authoritative x ⋅ authoritative y) (auth_own x ⋅ auth_own y).

Lemma auth_included (x y : auth A) :
  x ≼ y ↔ authoritative x ≼ authoritative y ∧ auth_own x ≼ auth_own y.
Proof.
  split; [intros [[z1 z2] Hz]; split; [exists z1|exists z2]; apply Hz|].
  intros [[z1 Hz1] [z2 Hz2]]; exists (Auth z1 z2); split; auto.
Qed.
Lemma authoritative_validN n (x : auth A) : ✓{n} x → ✓{n} authoritative x.
Proof. by destruct x as [[[]|]]. Qed.
Lemma auth_own_validN n (x : auth A) : ✓{n} x → ✓{n} auth_own x.
Proof. destruct x as [[[]|]]; naive_solver eauto using cmra_validN_includedN. Qed.

Lemma auth_valid_discrete `{CMRADiscrete A} x :
  ✓ x ↔ match authoritative x with
        | Excl' a => auth_own x ≼ a ∧ ✓ a
        | None => ✓ auth_own x
        | ExclBot' => False
        end.
Proof.
  destruct x as [[[?|]|] ?]; simpl; try done.
  setoid_rewrite <-cmra_discrete_included_iff; naive_solver eauto using 0.
Qed.

Lemma auth_cmra_mixin : CMRAMixin (auth A).
Proof.
  apply cmra_total_mixin.
  - eauto.
  - by intros n x y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
  - by intros n y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
  - intros n [x a] [y b] [Hx Ha]; simpl in *.
    destruct Hx as [?? Hx|]; first destruct Hx; intros ?; cofe_subst; auto.
  - intros [[[?|]|] ?]; rewrite /= ?cmra_included_includedN ?cmra_valid_validN;
      naive_solver eauto using O.
  - intros n [[[]|] ?] ?; naive_solver eauto using cmra_includedN_S, cmra_validN_S.
  - by split; simpl; rewrite assoc.
  - by split; simpl; rewrite comm.
  - by split; simpl; rewrite ?cmra_core_l.
  - by split; simpl; rewrite ?cmra_core_idemp.
  - intros ??; rewrite! auth_included; intros [??].
    by split; simpl; apply cmra_core_preserving.
  - assert (∀ n (a b1 b2 : A), b1 ⋅ b2 ≼{n} a → b1 ≼{n} a).
    { intros n a b1 b2 <-; apply cmra_includedN_l. }
   intros n [[[a1|]|] b1] [[[a2|]|] b2];
     naive_solver eauto using cmra_validN_op_l, cmra_validN_includedN.
  - intros n x y1 y2 ? [??]; simpl in *.
    destruct (cmra_extend n (authoritative x) (authoritative y1)
      (authoritative y2)) as (ea&?&?&?); auto using authoritative_validN.
    destruct (cmra_extend n (auth_own x) (auth_own y1) (auth_own y2))
      as (b&?&?&?); auto using auth_own_validN.
    by exists (Auth (ea.1) (b.1), Auth (ea.2) (b.2)).
Qed.
Canonical Structure authR := CMRAT (auth A) auth_cofe_mixin auth_cmra_mixin.

Global Instance auth_cmra_discrete : CMRADiscrete A → CMRADiscrete authR.
Proof.
  split; first apply _.
  intros [[[?|]|] ?]; rewrite /= /cmra_valid /cmra_validN /=; auto.
  - setoid_rewrite <-cmra_discrete_included_iff.
    rewrite -cmra_discrete_valid_iff. tauto.
  - by rewrite -cmra_discrete_valid_iff.
Qed.

Instance auth_empty : Empty (auth A) := Auth ∅ ∅.
Lemma auth_ucmra_mixin : UCMRAMixin (auth A).
Proof.
  split; simpl.
  - apply (@ucmra_unit_valid A).
  - by intros x; constructor; rewrite /= left_id.
  - apply _.
  - do 2 constructor; simpl; apply (persistent_core _).
Qed.
Canonical Structure authUR :=
  UCMRAT (auth A) auth_cofe_mixin auth_cmra_mixin auth_ucmra_mixin.

Global Instance auth_frag_persistent a : Persistent a → Persistent (◯ a).
Proof. do 2 constructor; simpl; auto. by apply persistent_core. Qed.

(** Internalized properties *)
Lemma auth_equivI {M} (x y : auth A) :
  x ≡ y ⊣⊢ (authoritative x ≡ authoritative y ∧ auth_own x ≡ auth_own y : uPred M).
Proof. by uPred.unseal. Qed.
Lemma auth_validI {M} (x : auth A) :
  ✓ x ⊣⊢ (match authoritative x with
          | Excl' a => (∃ b, a ≡ auth_own x ⋅ b) ∧ ✓ a
          | None => ✓ auth_own x
          | ExclBot' => False
          end : uPred M).
Proof. uPred.unseal. by destruct x as [[[]|]]. Qed.

Lemma auth_frag_op a b : ◯ (a ⋅ b) ≡ ◯ a ⋅ ◯ b.
Proof. done. Qed.
Lemma auth_both_op a b : Auth (Excl' a) b ≡ ● a ⋅ ◯ b.
Proof. by rewrite /op /auth_op /= left_id. Qed.

Lemma auth_update a af b :
  a ~l~> b @ Some af →
  ● (a ⋅ af) ⋅ ◯ a ~~> ● (b ⋅ af) ⋅ ◯ b.
Proof.
  intros [Hab Hab']; apply cmra_total_update.
  move=> n [[[?|]|] bf1] // =>-[[bf2 Ha] ?]; do 2 red; simpl in *.
  move: Ha; rewrite !left_id=> Hm; split; auto.
  exists bf2. rewrite -assoc.
  apply (Hab' _ (Some _)); auto. by rewrite /= assoc.
Qed.
End cmra.

Arguments authR : clear implicits.
Arguments authUR : clear implicits.

(* Functor *)
Definition auth_map {A B} (f : A → B) (x : auth A) : auth B :=
  Auth (excl_map f <$> authoritative x) (f (auth_own x)).
Lemma auth_map_id {A} (x : auth A) : auth_map id x = x.
Proof. by destruct x as [[[]|]]. Qed.
Lemma auth_map_compose {A B C} (f : A → B) (g : B → C) (x : auth A) :
  auth_map (g ∘ f) x = auth_map g (auth_map f x).
Proof. by destruct x as [[[]|]]. Qed.
Lemma auth_map_ext {A B : cofeT} (f g : A → B) x :
  (∀ x, f x ≡ g x) → auth_map f x ≡ auth_map g x.
Proof.
  constructor; simpl; auto.
  apply option_fmap_setoid_ext=> a; by apply excl_map_ext.
Qed.
Instance auth_map_ne {A B : cofeT} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@auth_map A B).
Proof.
  intros f g Hf [??] [??] [??]; split; simpl in *; [|by apply Hf].
  apply option_fmap_ne; [|done]=> x y ?; by apply excl_map_ne.
Qed.
Instance auth_map_cmra_monotone {A B : ucmraT} (f : A → B) :
  CMRAMonotone f → CMRAMonotone (auth_map f).
Proof.
  split; try apply _.
  - intros n [[[a|]|] b]; rewrite /= /cmra_validN /=; try
      naive_solver eauto using includedN_preserving, validN_preserving.
  - by intros [x a] [y b]; rewrite !auth_included /=;
      intros [??]; split; simpl; apply: included_preserving.
Qed.
Definition authC_map {A B} (f : A -n> B) : authC A -n> authC B :=
  CofeMor (auth_map f).
Lemma authC_map_ne A B n : Proper (dist n ==> dist n) (@authC_map A B).
Proof. intros f f' Hf [[[a|]|] b]; repeat constructor; apply Hf. Qed.

Program Definition authURF (F : urFunctor) : urFunctor := {|
  urFunctor_car A B := authUR (urFunctor_car F A B);
  urFunctor_map A1 A2 B1 B2 fg := authC_map (urFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply authC_map_ne, urFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(auth_map_id x).
  apply auth_map_ext=>y; apply urFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -auth_map_compose.
  apply auth_map_ext=>y; apply urFunctor_compose.
Qed.

Instance authURF_contractive F :
  urFunctorContractive F → urFunctorContractive (authURF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply authC_map_ne, urFunctor_contractive.
Qed.
