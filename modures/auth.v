Require Export modures.excl.
Local Arguments valid _ _ !_ /.
Local Arguments validN _ _ _ !_ /.

Record auth (A : Type) : Type := Auth { authoritative : excl A ; own : A }.
Arguments Auth {_} _ _.
Arguments authoritative {_} _.
Arguments own {_} _.
Notation "◯ x" := (Auth ExclUnit x) (at level 20).
Notation "● x" := (Auth (Excl x) ∅) (at level 20).

(* COFE *)
Section cofe.
Context {A : cofeT}.

Instance auth_equiv : Equiv (auth A) := λ x y,
  authoritative x ≡ authoritative y ∧ own x ≡ own y.
Instance auth_dist : Dist (auth A) := λ n x y,
  authoritative x ={n}= authoritative y ∧ own x ={n}= own y.

Global Instance Auth_ne : Proper (dist n ==> dist n ==> dist n) (@Auth A).
Proof. by split. Qed.
Global Instance authoritative_ne: Proper (dist n ==> dist n) (@authoritative A).
Proof. by destruct 1. Qed.
Global Instance own_ne : Proper (dist n ==> dist n) (@own A).
Proof. by destruct 1. Qed.

Instance auth_compl : Compl (auth A) := λ c,
  Auth (compl (chain_map authoritative c)) (compl (chain_map own c)).
Definition auth_cofe_mixin : CofeMixin (auth A).
Proof.
  split.
  * intros x y; unfold dist, auth_dist, equiv, auth_equiv.
    rewrite !equiv_dist; naive_solver.
  * intros n; split.
    + by intros ?; split.
    + by intros ?? [??]; split; symmetry.
    + intros ??? [??] [??]; split; etransitivity; eauto.
  * by intros n [x1 y1] [x2 y2] [??]; split; apply dist_S.
  * by split.
  * intros c n; split. apply (conv_compl (chain_map authoritative c) n).
    apply (conv_compl (chain_map own c) n).
Qed.
Canonical Structure authC := CofeT auth_cofe_mixin.
Instance Auth_timeless (x : excl A) (y : A) :
  Timeless x → Timeless y → Timeless (Auth x y).
Proof. by intros ?? [??] [??]; split; simpl in *; apply (timeless _). Qed.
End cofe.

Arguments authC : clear implicits.

(* CMRA *)
Section cmra.
Context {A : cmraT}.

Global Instance auth_empty `{Empty A} : Empty (auth A) := Auth ∅ ∅.
Instance auth_valid : Valid (auth A) := λ x,
  match authoritative x with
  | Excl a => own x ≼ a ∧ ✓ a
  | ExclUnit => ✓ (own x)
  | ExclBot => False
  end.
Global Arguments auth_valid !_ /.
Instance auth_validN : ValidN (auth A) := λ n x,
  match authoritative x with
  | Excl a => own x ≼{n} a ∧ ✓{n} a
  | ExclUnit => ✓{n} (own x)
  | ExclBot => n = 0
  end.
Global Arguments auth_validN _ !_ /.
Instance auth_unit : Unit (auth A) := λ x,
  Auth (unit (authoritative x)) (unit (own x)).
Instance auth_op : Op (auth A) := λ x y,
  Auth (authoritative x ⋅ authoritative y) (own x ⋅ own y).
Instance auth_minus : Minus (auth A) := λ x y,
  Auth (authoritative x ⩪ authoritative y) (own x ⩪ own y).
Lemma auth_included (x y : auth A) :
  x ≼ y ↔ authoritative x ≼ authoritative y ∧ own x ≼ own y.
Proof.
  split; [intros [[z1 z2] Hz]; split; [exists z1|exists z2]; apply Hz|].
  intros [[z1 Hz1] [z2 Hz2]]; exists (Auth z1 z2); split; auto.
Qed.
Lemma auth_includedN n (x y : auth A) :
  x ≼{n} y ↔ authoritative x ≼{n} authoritative y ∧ own x ≼{n} own y.
Proof.
  split; [intros [[z1 z2] Hz]; split; [exists z1|exists z2]; apply Hz|].
  intros [[z1 Hz1] [z2 Hz2]]; exists (Auth z1 z2); split; auto.
Qed.
Lemma authoritative_validN n (x : auth A) : ✓{n} x → ✓{n} (authoritative x).
Proof. by destruct x as [[]]. Qed.
Lemma own_validN n (x : auth A) : ✓{n} x → ✓{n} (own x).
Proof. destruct x as [[]]; naive_solver eauto using cmra_valid_includedN. Qed.

Definition auth_cmra_mixin : CMRAMixin (auth A).
Proof.
  split.
  * by intros n x y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
  * by intros n y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
  * intros n [x a] [y b] [Hx Ha]; simpl in *;
      destruct Hx as [[][]| | |]; intros ?; cofe_subst; auto.
  * by intros n x1 x2 [Hx Hx'] y1 y2 [Hy Hy'];
      split; simpl; rewrite ?Hy ?Hy' ?Hx ?Hx'.
  * by intros [[] ?]; simpl.
  * intros n [[] ?] ?; naive_solver eauto using cmra_included_S, cmra_valid_S.
  * destruct x as [[a| |] b]; simpl; rewrite ?cmra_included_includedN
      ?cmra_valid_validN; [naive_solver|naive_solver|].
    split; [done|intros Hn; discriminate (Hn 1)].
  * by split; simpl; rewrite (associative _).
  * by split; simpl; rewrite (commutative _).
  * by split; simpl; rewrite ?(ra_unit_l _).
  * by split; simpl; rewrite ?(ra_unit_idempotent _).
  * intros n ??; rewrite! auth_includedN; intros [??].
    by split; simpl; apply cmra_unit_preserving.
  * assert (∀ n (a b1 b2 : A), b1 ⋅ b2 ≼{n} a → b1 ≼{n} a).
    { intros n a b1 b2 <-; apply cmra_included_l. }
   intros n [[a1| |] b1] [[a2| |] b2];
     naive_solver eauto using cmra_valid_op_l, cmra_valid_includedN.
  * by intros n ??; rewrite auth_includedN;
      intros [??]; split; simpl; apply cmra_op_minus.
Qed.
Definition auth_cmra_extend_mixin : CMRAExtendMixin (auth A).
Proof.
  intros n x y1 y2 ? [??]; simpl in *.
  destruct (cmra_extend_op n (authoritative x) (authoritative y1)
    (authoritative y2)) as (z1&?&?&?); auto using authoritative_validN.
  destruct (cmra_extend_op n (own x) (own y1) (own y2))
    as (z2&?&?&?); auto using own_validN.
  by exists (Auth (z1.1) (z2.1), Auth (z1.2) (z2.2)).
Qed.
Canonical Structure authRA : cmraT :=
  CMRAT auth_cofe_mixin auth_cmra_mixin auth_cmra_extend_mixin.
Instance auth_ra_empty `{Empty A} : RAIdentity A → RAIdentity (auth A).
Proof.
  split; simpl; [apply ra_empty_valid|].
  by intros x; constructor; simpl; rewrite (left_id _ _).
Qed.
Lemma auth_frag_op (a b : A) : ◯ (a ⋅ b) ≡ ◯ a ⋅ ◯ b.
Proof. done. Qed.
Lemma auth_includedN' n (x y : authC A) :
  x ≼{n} y ↔ authoritative x ≼{n} authoritative y ∧ own x ≼{n} own y.
Proof.
  split; [intros [[z1 z2] Hz]; split; [exists z1|exists z2]; apply Hz|].
  intros [[z1 Hz1] [z2 Hz2]]; exists (Auth z1 z2); split; auto.
Qed.
End cmra.

Arguments authRA : clear implicits.

(* Functor *)
Instance auth_fmap : FMap auth := λ A B f x,
  Auth (f <$> authoritative x) (f (own x)).
Instance auth_fmap_cmra_ne {A B : cmraT} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@fmap auth _ A B).
Proof.
  intros f g Hf [??] [??] [??]; split; [by apply excl_fmap_cmra_ne|by apply Hf].
Qed.
Instance auth_fmap_cmra_monotone {A B : cmraT} (f : A → B) :
  (∀ n, Proper (dist n ==> dist n) f) → CMRAMonotone f →
  CMRAMonotone (fmap f : auth A → auth B).
Proof.
  split.
  * by intros n [x a] [y b]; rewrite !auth_includedN /=;
      intros [??]; split; simpl; apply: includedN_preserving.
  * intros n [[a| |] b]; rewrite /= /cmra_validN;
      naive_solver eauto using @includedN_preserving, @validN_preserving.
Qed.
Definition authRA_map {A B : cmraT} (f : A -n> B) : authRA A -n> authRA B :=
  CofeMor (fmap f : authRA A → authRA B).
Lemma authRA_map_ne A B n : Proper (dist n ==> dist n) (@authRA_map A B).
Proof. intros f f' Hf [[a| |] b]; repeat constructor; apply Hf. Qed.
