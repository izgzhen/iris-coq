Require Export iris.cmra.
Local Arguments disjoint _ _ !_ !_ /.
Local Arguments included _ _ !_ !_ /.

Inductive excl (A : Type) :=
  | Excl : A → excl A
  | ExclUnit : Empty (excl A)
  | ExclBot : excl A.
Arguments Excl {_} _.
Arguments ExclUnit {_}.
Arguments ExclBot {_}.
Existing Instance ExclUnit.

Inductive excl_equiv `{Equiv A} : Equiv (excl A) :=
  | Excl_equiv (x y : A) : x ≡ y → Excl x ≡ Excl y
  | ExclUnit_equiv : ∅ ≡ ∅
  | ExclBot_equiv : ExclBot ≡ ExclBot.
Existing Instance excl_equiv.
Instance excl_valid {A} : Valid (excl A) := λ x,
  match x with Excl _ | ExclUnit => True | ExclBot => False end.
Instance excl_empty {A} : Empty (excl A) := ExclUnit.
Instance excl_unit {A} : Unit (excl A) := λ _, ∅.
Instance excl_op {A} : Op (excl A) := λ x y,
  match x, y with
  | Excl x, ExclUnit | ExclUnit, Excl x => Excl x
  | ExclUnit, ExclUnit => ExclUnit
  | _, _=> ExclBot
  end.
Instance excl_minus {A} : Minus (excl A) := λ x y,
  match x, y with
  | _, ExclUnit => x
  | Excl _, Excl _ => ExclUnit
  | _, _ => ExclBot
  end.
Instance excl_included `{Equiv A} : Included (excl A) := λ x y,
  match x, y with
  | Excl x, Excl y => x ≡ y
  | ExclUnit, _ => True
  | _, ExclBot => True
  | _, _ => False
  end.
Definition excl_above `{Included A} (x : A) (y : excl A) : Prop :=
  match y with Excl y' => x ≼ y' | ExclUnit => True | ExclBot => False end.
Instance excl_ra `{Equiv A, !Equivalence (@equiv A _)} : RA (excl A).
Proof.
  split.
  * split.
    + by intros []; constructor.
    + by destruct 1; constructor.
    + destruct 1; inversion 1; constructor; etransitivity; eauto.
  * by intros []; destruct 1; constructor.
  * constructor.
  * by destruct 1.
  * by do 2 destruct 1; constructor.
  * by intros []; destruct 1; simpl; try (intros Hx; rewrite Hx).
  * by intros [?| |] [?| |] [?| |]; constructor.
  * by intros [?| |] [?| |]; constructor.
  * by intros [?| |]; constructor.
  * constructor.
  * by intros [?| |] [?| |].
  * by intros [?| |] [?| |].
  * by intros [?| |] [?| |]; simpl; try constructor.
  * by intros [?| |] [?| |] ?; try constructor.
Qed.
Instance excl_empty_ra `{Equiv A, !Equivalence (@equiv A _)} : RAEmpty (excl A).
Proof. split. done. by intros []. Qed.
Lemma excl_update {A} (x : A) y : valid y → Excl x ⇝ y.
Proof. by destruct y; intros ? [?| |]. Qed.

Section excl_above.
  Context `{RA A}.
  Global Instance excl_above_proper : Proper ((≡) ==> (≡) ==> iff) excl_above.
  Proof. by intros ?? Hx; destruct 1 as [?? Hy| |]; simpl; rewrite ?Hx,?Hy. Qed.
  Lemma excl_above_weaken (a b : A) x y :
    excl_above b y → a ≼ b → x ≼ y → excl_above a x.
  Proof.
    destruct x as [a'| |], y as [b'| |]; simpl; intros ??; try done.
    by intros Hab; rewrite Hab; transitivity b.
  Qed.
End excl_above.
