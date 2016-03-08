From algebra Require Export excl.
From algebra Require Import upred.
Local Arguments valid _ _ !_ /.
Local Arguments validN _ _ _ !_ /.

Record auth (A : Type) : Type := Auth { authoritative : excl A ; own : A }.
Add Printing Constructor auth.
Arguments Auth {_} _ _.
Arguments authoritative {_} _.
Arguments own {_} _.
Notation "◯ a" := (Auth ExclUnit a) (at level 20).
Notation "● a" := (Auth (Excl a) ∅) (at level 20).

(* COFE *)
Section cofe.
Context {A : cofeT}.
Implicit Types a : excl A.
Implicit Types b : A.
Implicit Types x y : auth A.

Instance auth_equiv : Equiv (auth A) := λ x y,
  authoritative x ≡ authoritative y ∧ own x ≡ own y.
Instance auth_dist : Dist (auth A) := λ n x y,
  authoritative x ≡{n}≡ authoritative y ∧ own x ≡{n}≡ own y.

Global Instance Auth_ne : Proper (dist n ==> dist n ==> dist n) (@Auth A).
Proof. by split. Qed.
Global Instance Auth_proper : Proper ((≡) ==> (≡) ==> (≡)) (@Auth A).
Proof. by split. Qed.
Global Instance authoritative_ne: Proper (dist n ==> dist n) (@authoritative A).
Proof. by destruct 1. Qed.
Global Instance authoritative_proper : Proper ((≡) ==> (≡)) (@authoritative A).
Proof. by destruct 1. Qed.
Global Instance own_ne : Proper (dist n ==> dist n) (@own A).
Proof. by destruct 1. Qed.
Global Instance own_proper : Proper ((≡) ==> (≡)) (@own A).
Proof. by destruct 1. Qed.

Instance auth_compl : Compl (auth A) := λ c,
  Auth (compl (chain_map authoritative c)) (compl (chain_map own c)).
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
    apply (conv_compl n (chain_map own c)).
Qed.
Canonical Structure authC := CofeT auth_cofe_mixin.

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
Context {A : cmraT}.
Implicit Types a b : A.
Implicit Types x y : auth A.

Global Instance auth_empty `{Empty A} : Empty (auth A) := Auth ∅ ∅.
Instance auth_valid : Valid (auth A) := λ x,
  match authoritative x with
  | Excl a => own x ≼ a ∧ ✓ a
  | ExclUnit => ✓ own x
  | ExclBot => False
  end.
Global Arguments auth_valid !_ /.
Instance auth_validN : ValidN (auth A) := λ n x,
  match authoritative x with
  | Excl a => own x ≼{n} a ∧ ✓{n} a
  | ExclUnit => ✓{n} own x
  | ExclBot => False
  end.
Global Arguments auth_validN _ !_ /.
Instance auth_core : Core (auth A) := λ x,
  Auth (core (authoritative x)) (core (own x)).
Instance auth_op : Op (auth A) := λ x y,
  Auth (authoritative x ⋅ authoritative y) (own x ⋅ own y).
Instance auth_div : Div (auth A) := λ x y,
  Auth (authoritative x ÷ authoritative y) (own x ÷ own y).

Lemma auth_included (x y : auth A) :
  x ≼ y ↔ authoritative x ≼ authoritative y ∧ own x ≼ own y.
Proof.
  split; [intros [[z1 z2] Hz]; split; [exists z1|exists z2]; apply Hz|].
  intros [[z1 Hz1] [z2 Hz2]]; exists (Auth z1 z2); split; auto.
Qed.
Lemma authoritative_validN n (x : auth A) : ✓{n} x → ✓{n} authoritative x.
Proof. by destruct x as [[]]. Qed.
Lemma own_validN n (x : auth A) : ✓{n} x → ✓{n} own x.
Proof. destruct x as [[]]; naive_solver eauto using cmra_validN_includedN. Qed.

Definition auth_cmra_mixin : CMRAMixin (auth A).
Proof.
  split.
  - by intros n x y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
  - by intros n y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
  - intros n [x a] [y b] [Hx Ha]; simpl in *;
      destruct Hx; intros ?; cofe_subst; auto.
  - by intros n x1 x2 [Hx Hx'] y1 y2 [Hy Hy'];
      split; simpl; rewrite ?Hy ?Hy' ?Hx ?Hx'.
  - intros [[] ?]; rewrite /= ?cmra_included_includedN ?cmra_valid_validN;
      naive_solver eauto using O.
  - intros n [[] ?] ?; naive_solver eauto using cmra_includedN_S, cmra_validN_S.
  - by split; simpl; rewrite assoc.
  - by split; simpl; rewrite comm.
  - by split; simpl; rewrite ?cmra_core_l.
  - by split; simpl; rewrite ?cmra_core_idemp.
  - intros ??; rewrite! auth_included; intros [??].
    by split; simpl; apply cmra_core_preserving.
  - assert (∀ n (a b1 b2 : A), b1 ⋅ b2 ≼{n} a → b1 ≼{n} a).
    { intros n a b1 b2 <-; apply cmra_includedN_l. }
   intros n [[a1| |] b1] [[a2| |] b2];
     naive_solver eauto using cmra_validN_op_l, cmra_validN_includedN.
  - by intros ??; rewrite auth_included;
      intros [??]; split; simpl; apply cmra_op_div.
  - intros n x y1 y2 ? [??]; simpl in *.
    destruct (cmra_extend n (authoritative x) (authoritative y1)
      (authoritative y2)) as (ea&?&?&?); auto using authoritative_validN.
    destruct (cmra_extend n (own x) (own y1) (own y2))
      as (b&?&?&?); auto using own_validN.
    by exists (Auth (ea.1) (b.1), Auth (ea.2) (b.2)).
Qed.
Canonical Structure authR : cmraT := CMRAT auth_cofe_mixin auth_cmra_mixin.
Global Instance auth_cmra_discrete : CMRADiscrete A → CMRADiscrete authR.
Proof.
  split; first apply _.
  intros [[] ?]; by rewrite /= /cmra_valid /cmra_validN /=
    -?cmra_discrete_included_iff -?cmra_discrete_valid_iff.
Qed.

(** Internalized properties *)
Lemma auth_equivI {M} (x y : auth A) :
  (x ≡ y)%I ≡ (authoritative x ≡ authoritative y ∧ own x ≡ own y : uPred M)%I.
Proof. by uPred.unseal. Qed.
Lemma auth_validI {M} (x : auth A) :
  (✓ x)%I ≡ (match authoritative x with
             | Excl a => (∃ b, a ≡ own x ⋅ b) ∧ ✓ a
             | ExclUnit => ✓ own x
             | ExclBot => False
             end : uPred M)%I.
Proof. uPred.unseal. by destruct x as [[]]. Qed.

(** The notations ◯ and ● only work for CMRAs with an empty element. So, in
what follows, we assume we have an empty element. *)
Context `{Empty A, !CMRAUnit A}.

Global Instance auth_cmra_unit : CMRAUnit authR.
Proof.
  split; simpl.
  - by apply (@cmra_unit_valid A _).
  - by intros x; constructor; rewrite /= left_id.
  - apply _.
Qed.
Lemma auth_frag_op a b : ◯ (a ⋅ b) ≡ ◯ a ⋅ ◯ b.
Proof. done. Qed.
Lemma auth_both_op a b : Auth (Excl a) b ≡ ● a ⋅ ◯ b.
Proof. by rewrite /op /auth_op /= left_id. Qed.

Lemma auth_update a a' b b' :
  (∀ n af, ✓{n} a → a ≡{n}≡ a' ⋅ af → b ≡{n}≡ b' ⋅ af ∧ ✓{n} b) →
  ● a ⋅ ◯ a' ~~> ● b ⋅ ◯ b'.
Proof.
  move=> Hab n [[?| |] bf1] // =>-[[bf2 Ha] ?]; do 2 red; simpl in *.
  destruct (Hab n (bf1 ⋅ bf2)) as [Ha' ?]; auto.
  { by rewrite Ha left_id assoc. }
  split; [by rewrite Ha' left_id assoc; apply cmra_includedN_l|done].
Qed.

Lemma auth_local_update L `{!LocalUpdate Lv L} a a' :
  Lv a → ✓ L a' →
  ● a' ⋅ ◯ a ~~> ● L a' ⋅ ◯ L a.
Proof.
  intros. apply auth_update=>n af ? EQ; split; last by apply cmra_valid_validN.
  by rewrite EQ (local_updateN L) // -EQ.
Qed.

Lemma auth_update_op_l a a' b :
  ✓ (b ⋅ a) → ● a ⋅ ◯ a' ~~> ● (b ⋅ a) ⋅ ◯ (b ⋅ a').
Proof. by intros; apply (auth_local_update _). Qed.
Lemma auth_update_op_r a a' b :
  ✓ (a ⋅ b) → ● a ⋅ ◯ a' ~~> ● (a ⋅ b) ⋅ ◯ (a' ⋅ b).
Proof. rewrite -!(comm _ b); apply auth_update_op_l. Qed.

(* This does not seem to follow from auth_local_update.
   The trouble is that given ✓ (L a ⋅ a'), Lv a
   we need ✓ (a ⋅ a'). I think this should hold for every local update,
   but adding an extra axiom to local updates just for this is silly. *)
Lemma auth_local_update_l L `{!LocalUpdate Lv L} a a' :
  Lv a → ✓ (L a ⋅ a') →
  ● (a ⋅ a') ⋅ ◯ a ~~> ● (L a ⋅ a') ⋅ ◯ L a.
Proof.
  intros. apply auth_update=>n af ? EQ; split; last by apply cmra_valid_validN.
  by rewrite -(local_updateN L) // EQ -(local_updateN L) // -EQ.
Qed.
End cmra.

Arguments authR : clear implicits.

(* Functor *)
Definition auth_map {A B} (f : A → B) (x : auth A) : auth B :=
  Auth (excl_map f (authoritative x)) (f (own x)).
Lemma auth_map_id {A} (x : auth A) : auth_map id x = x.
Proof. by destruct x; rewrite /auth_map excl_map_id. Qed.
Lemma auth_map_compose {A B C} (f : A → B) (g : B → C) (x : auth A) :
  auth_map (g ∘ f) x = auth_map g (auth_map f x).
Proof. by destruct x; rewrite /auth_map excl_map_compose. Qed.
Lemma auth_map_ext {A B : cofeT} (f g : A → B) x :
  (∀ x, f x ≡ g x) → auth_map f x ≡ auth_map g x.
Proof. constructor; simpl; auto using excl_map_ext. Qed.
Instance auth_map_cmra_ne {A B : cofeT} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@auth_map A B).
Proof.
  intros f g Hf [??] [??] [??]; split; [by apply excl_map_cmra_ne|by apply Hf].
Qed.
Instance auth_map_cmra_monotone {A B : cmraT} (f : A → B) :
  CMRAMonotone f → CMRAMonotone (auth_map f).
Proof.
  split; try apply _.
  - intros n [[a| |] b]; rewrite /= /cmra_validN /=; try
      naive_solver eauto using includedN_preserving, validN_preserving.
  - by intros [x a] [y b]; rewrite !auth_included /=;
      intros [??]; split; simpl; apply: included_preserving.
Qed.
Definition authC_map {A B} (f : A -n> B) : authC A -n> authC B :=
  CofeMor (auth_map f).
Lemma authC_map_ne A B n : Proper (dist n ==> dist n) (@authC_map A B).
Proof. intros f f' Hf [[a| |] b]; repeat constructor; apply Hf. Qed.

Program Definition authRF (F : rFunctor) : rFunctor := {|
  rFunctor_car A B := authR (rFunctor_car F A B);
  rFunctor_map A1 A2 B1 B2 fg := authC_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply authC_map_ne, rFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(auth_map_id x).
  apply auth_map_ext=>y; apply rFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -auth_map_compose.
  apply auth_map_ext=>y; apply rFunctor_compose.
Qed.

Instance authRF_contractive F :
  rFunctorContractive F → rFunctorContractive (authRF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply authC_map_ne, rFunctor_contractive.
Qed.
