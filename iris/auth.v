Require Export iris.excl.
Local Arguments disjoint _ _ !_ !_ /.
Local Arguments included _ _ !_ !_ /.

Record auth (A : Type) : Type := Auth { authorative : excl A ; own : A }.
Arguments Auth {_} _ _.
Arguments authorative {_} _.
Arguments own {_} _.
Notation "∘ x" := (Auth ExclUnit x) (at level 20).
Notation "∙ x" := (Auth (Excl x) ∅) (at level 20).

Instance auth_empty `{Empty A} : Empty (auth A) := Auth ∅ ∅.
Instance auth_valid `{Valid A, Included A} : Valid (auth A) := λ x,
  valid (authorative x) ∧ excl_above (own x) (authorative x).
Instance auth_equiv `{Equiv A} : Equiv (auth A) := λ x y,
  authorative x ≡ authorative y ∧ own x ≡ own y.
Instance auth_unit `{Unit A} : Unit (auth A) := λ x,
  Auth (unit (authorative x)) (unit (own x)).
Instance auth_op `{Op A} : Op (auth A) := λ x y,
  Auth (authorative x ⋅ authorative y) (own x ⋅ own y).
Instance auth_minus `{Minus A} : Minus (auth A) := λ x y,
  Auth (authorative x ⩪ authorative y) (own x ⩪ own y).
Instance auth_included `{Equiv A, Included A} : Included (auth A) := λ x y,
  authorative x ≼ authorative y ∧ own x ≼ own y.

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
  * by intros x y1 y2 [Hy Hy'] [??]; split; simpl; rewrite <-?Hy, <-?Hy'.
  * by split; simpl; rewrite (associative _).
  * by split; simpl; rewrite (commutative _).
  * by split; simpl; rewrite ?(ra_unit_l _).
  * by split; simpl; rewrite ?(ra_unit_idempotent _).
  * split; simpl; auto using ra_unit_weaken.
  * intros ?? [??]; split; [by apply ra_valid_op_l with (authorative y)|].
    by apply excl_above_weaken with (own x ⋅ own y)
      (authorative x ⋅ authorative y); try apply ra_included_l.
  * split; simpl; apply ra_included_l.
  * by intros ?? [??]; split; simpl; apply ra_op_minus.
Qed.
Instance auth_ra_empty `{RA A, Empty A, !RAEmpty A} : RAEmpty (auth A).
Proof. split. done. by intros x; constructor; simpl; rewrite (left_id _ _). Qed.
Lemma auth_frag_op `{RA A} a b : ∘(a ⋅ b) ≡ ∘a ⋅ ∘b.
Proof. done. Qed.
