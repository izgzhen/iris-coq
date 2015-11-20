Require Export iris.excl.
Local Arguments disjoint _ _ !_ !_ /.

Record auth (A : Type) : Type := Auth { authoritative : excl A ; own : A }.
Arguments Auth {_} _ _.
Arguments authoritative {_} _.
Arguments own {_} _.
Notation "∘ x" := (Auth ExclUnit x) (at level 20).
Notation "∙ x" := (Auth (Excl x) ∅) (at level 20).

Instance auth_empty `{Empty A} : Empty (auth A) := Auth ∅ ∅.
Instance auth_valid `{Equiv A, Valid A, Op A} : Valid (auth A) := λ x,
  valid (authoritative x) ∧ excl_above (own x) (authoritative x).
Instance auth_equiv `{Equiv A} : Equiv (auth A) := λ x y,
  authoritative x ≡ authoritative y ∧ own x ≡ own y.
Instance auth_unit `{Unit A} : Unit (auth A) := λ x,
  Auth (unit (authoritative x)) (unit (own x)).
Instance auth_op `{Op A} : Op (auth A) := λ x y,
  Auth (authoritative x ⋅ authoritative y) (own x ⋅ own y).
Instance auth_minus `{Minus A} : Minus (auth A) := λ x y,
  Auth (authoritative x ⩪ authoritative y) (own x ⩪ own y).
Lemma auth_included `{Equiv A, Op A} (x y : auth A) :
  x ≼ y ↔ authoritative x ≼ authoritative y ∧ own x ≼ own y.
Proof.
  split; [intros [[z1 z2] Hz]; split; [exists z1|exists z2]; apply Hz|].
  intros [[z1 Hz1] [z2 Hz2]]; exists (Auth z1 z2); split; auto.
Qed.

Instance auth_ra `{RA A} : RA (auth A).
Proof.
  split.
  * split.
    + by intros ?; split.
    + by intros ?? [??]; split.
    + intros ??? [??] [??]; split; etransitivity; eauto.
  * by intros x y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy, ?Hy'.
  * by intros y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy, ?Hy'.
  * by intros y1 y2 [Hy Hy'] [??]; split; simpl; rewrite <-?Hy, <-?Hy'.
  * by intros x1 x2 [Hx Hx'] y1 y2 [Hy Hy'];
      split; simpl; rewrite ?Hy, ?Hy', ?Hx, ?Hx'.
  * by split; simpl; rewrite (associative _).
  * by split; simpl; rewrite (commutative _).
  * by split; simpl; rewrite ?(ra_unit_l _).
  * by split; simpl; rewrite ?(ra_unit_idempotent _).
  * intros ??; rewrite! auth_included; intros [??].
    by split; simpl; apply ra_unit_preserving.
  * intros ?? [??]; split; [by apply ra_valid_op_l with (authoritative y)|].
    by apply excl_above_weaken with (own x ⋅ own y)
      (authoritative x ⋅ authoritative y); try apply ra_included_l.
  * by intros ??; rewrite auth_included;
      intros [??]; split; simpl; apply ra_op_minus.
Qed.
Instance auth_ra_empty `{RA A, Empty A, !RAEmpty A} : RAEmpty (auth A).
Proof. split. done. by intros x; constructor; simpl; rewrite (left_id _ _). Qed.
Lemma auth_frag_op `{RA A} a b : ∘(a ⋅ b) ≡ ∘a ⋅ ∘b.
Proof. done. Qed.