From iris.algebra Require Export cofe.

Class Core (A : Type) := core : A → A.
Instance: Params (@core) 2.

Class Op (A : Type) := op : A → A → A.
Instance: Params (@op) 2.
Infix "⋅" := op (at level 50, left associativity) : C_scope.
Notation "(⋅)" := op (only parsing) : C_scope.

Definition included `{Equiv A, Op A} (x y : A) := ∃ z, y ≡ x ⋅ z.
Infix "≼" := included (at level 70) : C_scope.
Notation "(≼)" := included (only parsing) : C_scope.
Hint Extern 0 (_ ≼ _) => reflexivity.
Instance: Params (@included) 3.

Class ValidN (A : Type) := validN : nat → A → Prop.
Instance: Params (@validN) 3.
Notation "✓{ n } x" := (validN n x)
  (at level 20, n at next level, format "✓{ n }  x").

Class Valid (A : Type) := valid : A → Prop.
Instance: Params (@valid) 2.
Notation "✓ x" := (valid x) (at level 20) : C_scope.

Definition includedN `{Dist A, Op A} (n : nat) (x y : A) := ∃ z, y ≡{n}≡ x ⋅ z.
Notation "x ≼{ n } y" := (includedN n x y)
  (at level 70, n at next level, format "x  ≼{ n }  y") : C_scope.
Instance: Params (@includedN) 4.
Hint Extern 0 (_ ≼{_} _) => reflexivity.

Record CMRAMixin A `{Dist A, Equiv A, Core A, Op A, Valid A, ValidN A} := {
  (* setoids *)
  mixin_cmra_op_ne n (x : A) : Proper (dist n ==> dist n) (op x);
  mixin_cmra_core_ne n : Proper (dist n ==> dist n) core;
  mixin_cmra_validN_ne n : Proper (dist n ==> impl) (validN n);
  (* valid *)
  mixin_cmra_valid_validN x : ✓ x ↔ ∀ n, ✓{n} x;
  mixin_cmra_validN_S n x : ✓{S n} x → ✓{n} x;
  (* monoid *)
  mixin_cmra_assoc : Assoc (≡) (⋅);
  mixin_cmra_comm : Comm (≡) (⋅);
  mixin_cmra_core_l x : core x ⋅ x ≡ x;
  mixin_cmra_core_idemp x : core (core x) ≡ core x;
  mixin_cmra_core_preserving x y : x ≼ y → core x ≼ core y;
  mixin_cmra_validN_op_l n x y : ✓{n} (x ⋅ y) → ✓{n} x;
  mixin_cmra_extend n x y1 y2 :
    ✓{n} x → x ≡{n}≡ y1 ⋅ y2 →
    { z | x ≡ z.1 ⋅ z.2 ∧ z.1 ≡{n}≡ y1 ∧ z.2 ≡{n}≡ y2 }
}.

(** Bundeled version *)
Structure cmraT := CMRAT {
  cmra_car :> Type;
  cmra_equiv : Equiv cmra_car;
  cmra_dist : Dist cmra_car;
  cmra_compl : Compl cmra_car;
  cmra_core : Core cmra_car;
  cmra_op : Op cmra_car;
  cmra_valid : Valid cmra_car;
  cmra_validN : ValidN cmra_car;
  cmra_cofe_mixin : CofeMixin cmra_car;
  cmra_mixin : CMRAMixin cmra_car
}.
Arguments CMRAT _ {_ _ _ _ _ _ _} _ _.
Arguments cmra_car : simpl never.
Arguments cmra_equiv : simpl never.
Arguments cmra_dist : simpl never.
Arguments cmra_compl : simpl never.
Arguments cmra_core : simpl never.
Arguments cmra_op : simpl never.
Arguments cmra_valid : simpl never.
Arguments cmra_validN : simpl never.
Arguments cmra_cofe_mixin : simpl never.
Arguments cmra_mixin : simpl never.
Add Printing Constructor cmraT.
Existing Instances cmra_core cmra_op cmra_valid cmra_validN.
Coercion cmra_cofeC (A : cmraT) : cofeT := CofeT A (cmra_cofe_mixin A).
Canonical Structure cmra_cofeC.

(** Lifting properties from the mixin *)
Section cmra_mixin.
  Context {A : cmraT}.
  Implicit Types x y : A.
  Global Instance cmra_op_ne n (x : A) : Proper (dist n ==> dist n) (op x).
  Proof. apply (mixin_cmra_op_ne _ (cmra_mixin A)). Qed.
  Global Instance cmra_core_ne n : Proper (dist n ==> dist n) (@core A _).
  Proof. apply (mixin_cmra_core_ne _ (cmra_mixin A)). Qed.
  Global Instance cmra_validN_ne n : Proper (dist n ==> impl) (@validN A _ n).
  Proof. apply (mixin_cmra_validN_ne _ (cmra_mixin A)). Qed.
  Lemma cmra_valid_validN x : ✓ x ↔ ∀ n, ✓{n} x.
  Proof. apply (mixin_cmra_valid_validN _ (cmra_mixin A)). Qed.
  Lemma cmra_validN_S n x : ✓{S n} x → ✓{n} x.
  Proof. apply (mixin_cmra_validN_S _ (cmra_mixin A)). Qed.
  Global Instance cmra_assoc : Assoc (≡) (@op A _).
  Proof. apply (mixin_cmra_assoc _ (cmra_mixin A)). Qed.
  Global Instance cmra_comm : Comm (≡) (@op A _).
  Proof. apply (mixin_cmra_comm _ (cmra_mixin A)). Qed.
  Lemma cmra_core_l x : core x ⋅ x ≡ x.
  Proof. apply (mixin_cmra_core_l _ (cmra_mixin A)). Qed.
  Lemma cmra_core_idemp x : core (core x) ≡ core x.
  Proof. apply (mixin_cmra_core_idemp _ (cmra_mixin A)). Qed.
  Lemma cmra_core_preserving x y : x ≼ y → core x ≼ core y.
  Proof. apply (mixin_cmra_core_preserving _ (cmra_mixin A)). Qed.
  Lemma cmra_validN_op_l n x y : ✓{n} (x ⋅ y) → ✓{n} x.
  Proof. apply (mixin_cmra_validN_op_l _ (cmra_mixin A)). Qed.
  Lemma cmra_extend n x y1 y2 :
    ✓{n} x → x ≡{n}≡ y1 ⋅ y2 →
    { z | x ≡ z.1 ⋅ z.2 ∧ z.1 ≡{n}≡ y1 ∧ z.2 ≡{n}≡ y2 }.
  Proof. apply (mixin_cmra_extend _ (cmra_mixin A)). Qed.
End cmra_mixin.

(** * CMRAs with a unit element *)
(** We use the notation ∅ because for most instances (maps, sets, etc) the
`empty' element is the unit. *)
Class CMRAUnit (A : cmraT) `{Empty A} := {
  cmra_unit_valid : ✓ ∅;
  cmra_unit_left_id :> LeftId (≡) ∅ (⋅);
  cmra_unit_timeless :> Timeless ∅
}.
Instance cmra_unit_inhabited `{CMRAUnit A} : Inhabited A := populate ∅.

(** * Persistent elements *)
Class Persistent {A : cmraT} (x : A) := persistent : core x ≡ x.
Arguments persistent {_} _ {_}.

(** * Discrete CMRAs *)
Class CMRADiscrete (A : cmraT) := {
  cmra_discrete :> Discrete A;
  cmra_discrete_valid (x : A) : ✓{0} x → ✓ x
}.

(** * Morphisms *)
Class CMRAMonotone {A B : cmraT} (f : A → B) := {
  cmra_monotone_ne n :> Proper (dist n ==> dist n) f;
  validN_preserving n x : ✓{n} x → ✓{n} f x;
  included_preserving x y : x ≼ y → f x ≼ f y
}.
Arguments validN_preserving {_ _} _ {_} _ _ _.
Arguments included_preserving {_ _} _ {_} _ _ _.

(** * Local updates *)
(** The idea is that lemams taking this class will usually have L explicit,
    and leave Lv implicit - it will be inferred by the typeclass machinery. *)
Class LocalUpdate {A : cmraT} (Lv : A → Prop) (L : A → A) := {
  local_update_ne n :> Proper (dist n ==> dist n) L;
  local_updateN n x y : Lv x → ✓{n} (x ⋅ y) → L (x ⋅ y) ≡{n}≡ L x ⋅ y
}.
Arguments local_updateN {_ _} _ {_} _ _ _ _ _.

(** * Frame preserving updates *)
Definition cmra_updateP {A : cmraT} (x : A) (P : A → Prop) := ∀ n z,
  ✓{n} (x ⋅ z) → ∃ y, P y ∧ ✓{n} (y ⋅ z).
Instance: Params (@cmra_updateP) 1.
Infix "~~>:" := cmra_updateP (at level 70).
Definition cmra_update {A : cmraT} (x y : A) := ∀ n z,
  ✓{n} (x ⋅ z) → ✓{n} (y ⋅ z).
Infix "~~>" := cmra_update (at level 70).
Instance: Params (@cmra_update) 1.

(** * Properties **)
Section cmra.
Context {A : cmraT}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(** ** Setoids *)
Global Instance cmra_core_proper : Proper ((≡) ==> (≡)) (@core A _).
Proof. apply (ne_proper _). Qed.
Global Instance cmra_op_ne' n : Proper (dist n ==> dist n ==> dist n) (@op A _).
Proof.
  intros x1 x2 Hx y1 y2 Hy.
  by rewrite Hy (comm _ x1) Hx (comm _ y2).
Qed.
Global Instance ra_op_proper' : Proper ((≡) ==> (≡) ==> (≡)) (@op A _).
Proof. apply (ne_proper_2 _). Qed.
Global Instance cmra_validN_ne' : Proper (dist n ==> iff) (@validN A _ n) | 1.
Proof. by split; apply cmra_validN_ne. Qed.
Global Instance cmra_validN_proper : Proper ((≡) ==> iff) (@validN A _ n) | 1.
Proof. by intros n x1 x2 Hx; apply cmra_validN_ne', equiv_dist. Qed.

Global Instance cmra_valid_proper : Proper ((≡) ==> iff) (@valid A _).
Proof.
  intros x y Hxy; rewrite !cmra_valid_validN.
  by split=> ? n; [rewrite -Hxy|rewrite Hxy].
Qed.
Global Instance cmra_includedN_ne n :
  Proper (dist n ==> dist n ==> iff) (@includedN A _ _ n) | 1.
Proof.
  intros x x' Hx y y' Hy.
  by split; intros [z ?]; exists z; [rewrite -Hx -Hy|rewrite Hx Hy].
Qed.
Global Instance cmra_includedN_proper n :
  Proper ((≡) ==> (≡) ==> iff) (@includedN A _ _ n) | 1.
Proof.
  intros x x' Hx y y' Hy; revert Hx Hy; rewrite !equiv_dist=> Hx Hy.
  by rewrite (Hx n) (Hy n).
Qed.
Global Instance cmra_included_proper :
  Proper ((≡) ==> (≡) ==> iff) (@included A _ _) | 1.
Proof.
  intros x x' Hx y y' Hy.
  by split; intros [z ?]; exists z; [rewrite -Hx -Hy|rewrite Hx Hy].
Qed.
Global Instance cmra_update_proper :
  Proper ((≡) ==> (≡) ==> iff) (@cmra_update A).
Proof.
  intros x1 x2 Hx y1 y2 Hy; split=>? n z; [rewrite -Hx -Hy|rewrite Hx Hy]; auto.
Qed.
Global Instance cmra_updateP_proper :
  Proper ((≡) ==> pointwise_relation _ iff ==> iff) (@cmra_updateP A).
Proof.
  intros x1 x2 Hx P1 P2 HP; split=>Hup n z;
    [rewrite -Hx; setoid_rewrite <-HP|rewrite Hx; setoid_rewrite HP]; auto.
Qed.

(** ** Validity *)
Lemma cmra_validN_le n n' x : ✓{n} x → n' ≤ n → ✓{n'} x.
Proof. induction 2; eauto using cmra_validN_S. Qed.
Lemma cmra_valid_op_l x y : ✓ (x ⋅ y) → ✓ x.
Proof. rewrite !cmra_valid_validN; eauto using cmra_validN_op_l. Qed.
Lemma cmra_validN_op_r n x y : ✓{n} (x ⋅ y) → ✓{n} y.
Proof. rewrite (comm _ x); apply cmra_validN_op_l. Qed.
Lemma cmra_valid_op_r x y : ✓ (x ⋅ y) → ✓ y.
Proof. rewrite !cmra_valid_validN; eauto using cmra_validN_op_r. Qed.

(** ** Core *)
Lemma cmra_core_r x : x ⋅ core x ≡ x.
Proof. by rewrite (comm _ x) cmra_core_l. Qed.
Lemma cmra_core_core x : core x ⋅ core x ≡ core x.
Proof. by rewrite -{2}(cmra_core_idemp x) cmra_core_r. Qed.
Lemma cmra_core_validN n x : ✓{n} x → ✓{n} core x.
Proof. rewrite -{1}(cmra_core_l x); apply cmra_validN_op_l. Qed.
Lemma cmra_core_valid x : ✓ x → ✓ core x.
Proof. rewrite -{1}(cmra_core_l x); apply cmra_valid_op_l. Qed.
Global Instance cmra_core_persistent x : Persistent (core x).
Proof. apply cmra_core_idemp. Qed.

(** ** Order *)
Lemma cmra_included_includedN n x y : x ≼ y → x ≼{n} y.
Proof. intros [z ->]. by exists z. Qed.
Global Instance cmra_includedN_preorder n : PreOrder (@includedN A _ _ n).
Proof.
  split.
  - by intros x; exists (core x); rewrite cmra_core_r.
  - intros x y z [z1 Hy] [z2 Hz]; exists (z1 ⋅ z2).
    by rewrite assoc -Hy -Hz.
Qed.
Global Instance cmra_included_preorder: PreOrder (@included A _ _).
Proof.
  split.
  - by intros x; exists (core x); rewrite cmra_core_r.
  - intros x y z [z1 Hy] [z2 Hz]; exists (z1 ⋅ z2).
    by rewrite assoc -Hy -Hz.
Qed.
Lemma cmra_validN_includedN n x y : ✓{n} y → x ≼{n} y → ✓{n} x.
Proof. intros Hyv [z ?]; cofe_subst y; eauto using cmra_validN_op_l. Qed.
Lemma cmra_validN_included n x y : ✓{n} y → x ≼ y → ✓{n} x.
Proof. intros Hyv [z ?]; setoid_subst; eauto using cmra_validN_op_l. Qed.

Lemma cmra_includedN_S n x y : x ≼{S n} y → x ≼{n} y.
Proof. by intros [z Hz]; exists z; apply dist_S. Qed.
Lemma cmra_includedN_le n n' x y : x ≼{n} y → n' ≤ n → x ≼{n'} y.
Proof. induction 2; auto using cmra_includedN_S. Qed.

Lemma cmra_includedN_l n x y : x ≼{n} x ⋅ y.
Proof. by exists y. Qed.
Lemma cmra_included_l x y : x ≼ x ⋅ y.
Proof. by exists y. Qed.
Lemma cmra_includedN_r n x y : y ≼{n} x ⋅ y.
Proof. rewrite (comm op); apply cmra_includedN_l. Qed.
Lemma cmra_included_r x y : y ≼ x ⋅ y.
Proof. rewrite (comm op); apply cmra_included_l. Qed.

Lemma cmra_core_preservingN n x y : x ≼{n} y → core x ≼{n} core y.
Proof.
  intros [z ->].
  apply cmra_included_includedN, cmra_core_preserving, cmra_included_l.
Qed.
Lemma cmra_included_core x : core x ≼ x.
Proof. by exists x; rewrite cmra_core_l. Qed.
Lemma cmra_preservingN_l n x y z : x ≼{n} y → z ⋅ x ≼{n} z ⋅ y.
Proof. by intros [z1 Hz1]; exists z1; rewrite Hz1 (assoc op). Qed.
Lemma cmra_preserving_l x y z : x ≼ y → z ⋅ x ≼ z ⋅ y.
Proof. by intros [z1 Hz1]; exists z1; rewrite Hz1 (assoc op). Qed.
Lemma cmra_preservingN_r n x y z : x ≼{n} y → x ⋅ z ≼{n} y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply cmra_preservingN_l. Qed.
Lemma cmra_preserving_r x y z : x ≼ y → x ⋅ z ≼ y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply cmra_preserving_l. Qed.

Lemma cmra_included_dist_l n x1 x2 x1' :
  x1 ≼ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ x2' ∧ x2' ≡{n}≡ x2.
Proof.
  intros [z Hx2] Hx1; exists (x1' ⋅ z); split; auto using cmra_included_l.
  by rewrite Hx1 Hx2.
Qed.

(** ** Timeless *)
Lemma cmra_timeless_included_l x y : Timeless x → ✓{0} y → x ≼{0} y → x ≼ y.
Proof.
  intros ?? [x' ?].
  destruct (cmra_extend 0 y x x') as ([z z']&Hy&Hz&Hz'); auto; simpl in *.
  by exists z'; rewrite Hy (timeless x z).
Qed.
Lemma cmra_timeless_included_r n x y : Timeless y → x ≼{0} y → x ≼{n} y.
Proof. intros ? [x' ?]. exists x'. by apply equiv_dist, (timeless y). Qed.
Lemma cmra_op_timeless x1 x2 :
  ✓ (x1 ⋅ x2) → Timeless x1 → Timeless x2 → Timeless (x1 ⋅ x2).
Proof.
  intros ??? z Hz.
  destruct (cmra_extend 0 z x1 x2) as ([y1 y2]&Hz'&?&?); auto; simpl in *.
  { rewrite -?Hz. by apply cmra_valid_validN. }
  by rewrite Hz' (timeless x1 y1) // (timeless x2 y2).
Qed.

(** ** Discrete *)
Lemma cmra_discrete_valid_iff `{CMRADiscrete A} n x : ✓ x ↔ ✓{n} x.
Proof.
  split; first by rewrite cmra_valid_validN.
  eauto using cmra_discrete_valid, cmra_validN_le with lia.
Qed.
Lemma cmra_discrete_included_iff `{Discrete A} n x y : x ≼ y ↔ x ≼{n} y.
Proof.
  split; first by apply cmra_included_includedN.
  intros [z ->%(timeless_iff _ _)]; eauto using cmra_included_l.
Qed.
Lemma cmra_discrete_updateP `{CMRADiscrete A} (x : A) (P : A → Prop) :
  (∀ z, ✓ (x ⋅ z) → ∃ y, P y ∧ ✓ (y ⋅ z)) → x ~~>: P.
Proof. intros ? n. by setoid_rewrite <-cmra_discrete_valid_iff. Qed.
Lemma cmra_discrete_update `{CMRADiscrete A} (x y : A) :
  (∀ z, ✓ (x ⋅ z) → ✓ (y ⋅ z)) → x ~~> y.
Proof. intros ? n. by setoid_rewrite <-cmra_discrete_valid_iff. Qed.

(** ** RAs with a unit element *)
Section unit.
  Context `{Empty A, !CMRAUnit A}.
  Lemma cmra_unit_validN n : ✓{n} ∅.
  Proof. apply cmra_valid_validN, cmra_unit_valid. Qed.
  Lemma cmra_unit_leastN n x : ∅ ≼{n} x.
  Proof. by exists x; rewrite left_id. Qed.
  Lemma cmra_unit_least x : ∅ ≼ x.
  Proof. by exists x; rewrite left_id. Qed.
  Global Instance cmra_unit_right_id : RightId (≡) ∅ (⋅).
  Proof. by intros x; rewrite (comm op) left_id. Qed.
  Global Instance cmra_unit_persistent : Persistent ∅.
  Proof. by rewrite /Persistent -{2}(cmra_core_l ∅) right_id. Qed.
  Lemma cmra_core_unit : core (∅:A) ≡ ∅.
  Proof. by rewrite -{2}(cmra_core_l ∅) right_id. Qed.
End unit.

(** ** Local updates *)
Global Instance local_update_proper Lv (L : A → A) :
  LocalUpdate Lv L → Proper ((≡) ==> (≡)) L.
Proof. intros; apply (ne_proper _). Qed.

Lemma local_update L `{!LocalUpdate Lv L} x y :
  Lv x → ✓ (x ⋅ y) → L (x ⋅ y) ≡ L x ⋅ y.
Proof.
  by rewrite cmra_valid_validN equiv_dist=>?? n; apply (local_updateN L).
Qed.

Global Instance local_update_op x : LocalUpdate (λ _, True) (op x).
Proof. split. apply _. by intros n y1 y2 _ _; rewrite assoc. Qed.

Global Instance local_update_id : LocalUpdate (λ _, True) (@id A).
Proof. split; auto with typeclass_instances. Qed.

(** ** Updates *)
Global Instance cmra_update_preorder : PreOrder (@cmra_update A).
Proof. split. by intros x y. intros x y y' ?? z ?; naive_solver. Qed.
Lemma cmra_update_updateP x y : x ~~> y ↔ x ~~>: (y =).
Proof.
  split.
  - by intros Hx z ?; exists y; split; [done|apply (Hx z)].
  - by intros Hx n z ?; destruct (Hx n z) as (?&<-&?).
Qed.
Lemma cmra_updateP_id (P : A → Prop) x : P x → x ~~>: P.
Proof. by intros ? n z ?; exists x. Qed.
Lemma cmra_updateP_compose (P Q : A → Prop) x :
  x ~~>: P → (∀ y, P y → y ~~>: Q) → x ~~>: Q.
Proof.
  intros Hx Hy n z ?. destruct (Hx n z) as (y&?&?); auto. by apply (Hy y).
Qed.
Lemma cmra_updateP_compose_l (Q : A → Prop) x y : x ~~> y → y ~~>: Q → x ~~>: Q.
Proof.
  rewrite cmra_update_updateP.
  intros; apply cmra_updateP_compose with (y =); intros; subst; auto.
Qed.
Lemma cmra_updateP_weaken (P Q : A → Prop) x : x ~~>: P → (∀ y, P y → Q y) → x ~~>: Q.
Proof. eauto using cmra_updateP_compose, cmra_updateP_id. Qed.

Lemma cmra_updateP_op (P1 P2 Q : A → Prop) x1 x2 :
  x1 ~~>: P1 → x2 ~~>: P2 → (∀ y1 y2, P1 y1 → P2 y2 → Q (y1 ⋅ y2)) → x1 ⋅ x2 ~~>: Q.
Proof.
  intros Hx1 Hx2 Hy n z ?.
  destruct (Hx1 n (x2 ⋅ z)) as (y1&?&?); first by rewrite assoc.
  destruct (Hx2 n (y1 ⋅ z)) as (y2&?&?);
    first by rewrite assoc (comm _ x2) -assoc.
  exists (y1 ⋅ y2); split; last rewrite (comm _ y1) -assoc; auto.
Qed.
Lemma cmra_updateP_op' (P1 P2 : A → Prop) x1 x2 :
  x1 ~~>: P1 → x2 ~~>: P2 → x1 ⋅ x2 ~~>: λ y, ∃ y1 y2, y = y1 ⋅ y2 ∧ P1 y1 ∧ P2 y2.
Proof. eauto 10 using cmra_updateP_op. Qed.
Lemma cmra_update_op x1 x2 y1 y2 : x1 ~~> y1 → x2 ~~> y2 → x1 ⋅ x2 ~~> y1 ⋅ y2.
Proof.
  rewrite !cmra_update_updateP; eauto using cmra_updateP_op with congruence.
Qed.
Lemma cmra_update_id x : x ~~> x.
Proof. intro. auto. Qed.

Section unit_updates.
  Context `{Empty A, !CMRAUnit A}.
  Lemma cmra_update_unit x : x ~~> ∅.
  Proof. intros n z; rewrite left_id; apply cmra_validN_op_r. Qed.
  Lemma cmra_update_unit_alt y : ∅ ~~> y ↔ ∀ x, x ~~> y.
  Proof. split; [intros; trans ∅|]; auto using cmra_update_unit. Qed.
End unit_updates.
End cmra.

(** * Properties about monotone functions *)
Instance cmra_monotone_id {A : cmraT} : CMRAMonotone (@id A).
Proof. repeat split; by try apply _. Qed.
Instance cmra_monotone_compose {A B C : cmraT} (f : A → B) (g : B → C) :
  CMRAMonotone f → CMRAMonotone g → CMRAMonotone (g ∘ f).
Proof.
  split.
  - apply _. 
  - move=> n x Hx /=. by apply validN_preserving, validN_preserving.
  - move=> x y Hxy /=. by apply included_preserving, included_preserving.
Qed.

Section cmra_monotone.
  Context {A B : cmraT} (f : A → B) `{!CMRAMonotone f}.
  Global Instance cmra_monotone_proper : Proper ((≡) ==> (≡)) f := ne_proper _.
  Lemma includedN_preserving n x y : x ≼{n} y → f x ≼{n} f y.
  Proof.
    intros [z ->].
    apply cmra_included_includedN, (included_preserving f), cmra_included_l.
  Qed.
  Lemma valid_preserving x : ✓ x → ✓ f x.
  Proof. rewrite !cmra_valid_validN; eauto using validN_preserving. Qed.
End cmra_monotone.

(** Functors *)
Structure rFunctor := RFunctor {
  rFunctor_car : cofeT → cofeT → cmraT;
  rFunctor_map {A1 A2 B1 B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → rFunctor_car A1 B1 -n> rFunctor_car A2 B2;
  rFunctor_ne A1 A2 B1 B2 n :
    Proper (dist n ==> dist n) (@rFunctor_map A1 A2 B1 B2);
  rFunctor_id {A B} (x : rFunctor_car A B) : rFunctor_map (cid,cid) x ≡ x;
  rFunctor_compose {A1 A2 A3 B1 B2 B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    rFunctor_map (f◎g, g'◎f') x ≡ rFunctor_map (g,g') (rFunctor_map (f,f') x);
  rFunctor_mono {A1 A2 B1 B2} (fg : (A2 -n> A1) * (B1 -n> B2)) :
    CMRAMonotone (rFunctor_map fg) 
}.
Existing Instances rFunctor_ne rFunctor_mono.
Instance: Params (@rFunctor_map) 5.

Class rFunctorContractive (F : rFunctor) :=
  rFunctor_contractive A1 A2 B1 B2 :> Contractive (@rFunctor_map F A1 A2 B1 B2).

Definition rFunctor_diag (F: rFunctor) (A: cofeT) : cmraT := rFunctor_car F A A.
Coercion rFunctor_diag : rFunctor >-> Funclass.

Program Definition constRF (B : cmraT) : rFunctor :=
  {| rFunctor_car A1 A2 := B; rFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.

Instance constRF_contractive B : rFunctorContractive (constRF B).
Proof. rewrite /rFunctorContractive; apply _. Qed.

(** * Transporting a CMRA equality *)
Definition cmra_transport {A B : cmraT} (H : A = B) (x : A) : B :=
  eq_rect A id x _ H.

Section cmra_transport.
  Context {A B : cmraT} (H : A = B).
  Notation T := (cmra_transport H).
  Global Instance cmra_transport_ne n : Proper (dist n ==> dist n) T.
  Proof. by intros ???; destruct H. Qed.
  Global Instance cmra_transport_proper : Proper ((≡) ==> (≡)) T.
  Proof. by intros ???; destruct H. Qed.
  Lemma cmra_transport_op x y : T (x ⋅ y) = T x ⋅ T y.
  Proof. by destruct H. Qed.
  Lemma cmra_transport_core x : T (core x) = core (T x).
  Proof. by destruct H. Qed.
  Lemma cmra_transport_validN n x : ✓{n} T x ↔ ✓{n} x.
  Proof. by destruct H. Qed.
  Lemma cmra_transport_valid x : ✓ T x ↔ ✓ x.
  Proof. by destruct H. Qed.
  Global Instance cmra_transport_timeless x : Timeless x → Timeless (T x).
  Proof. by destruct H. Qed.
  Global Instance cmra_transport_persistent x : Persistent x → Persistent (T x).
  Proof. by destruct H. Qed.
  Lemma cmra_transport_updateP (P : A → Prop) (Q : B → Prop) x :
    x ~~>: P → (∀ y, P y → Q (T y)) → T x ~~>: Q.
  Proof. destruct H; eauto using cmra_updateP_weaken. Qed.
  Lemma cmra_transport_updateP' (P : A → Prop) x :
    x ~~>: P → T x ~~>: λ y, ∃ y', y = cmra_transport H y' ∧ P y'.
  Proof. eauto using cmra_transport_updateP. Qed.
End cmra_transport.

(** * Instances *)
(** ** Discrete CMRA *)
Record RAMixin A `{Equiv A, Core A, Op A, Valid A} := {
  (* setoids *)
  ra_op_ne (x : A) : Proper ((≡) ==> (≡)) (op x);
  ra_core_ne : Proper ((≡) ==> (≡)) core;
  ra_validN_ne : Proper ((≡) ==> impl) valid;
  (* monoid *)
  ra_assoc : Assoc (≡) (⋅);
  ra_comm : Comm (≡) (⋅);
  ra_core_l x : core x ⋅ x ≡ x;
  ra_core_idemp x : core (core x) ≡ core x;
  ra_core_preserving x y : x ≼ y → core x ≼ core y;
  ra_valid_op_l x y : ✓ (x ⋅ y) → ✓ x
}.

Section discrete.
  Context `{Equiv A, Core A, Op A, Valid A, @Equivalence A (≡)}.
  Context (ra_mix : RAMixin A).
  Existing Instances discrete_dist discrete_compl.

  Instance discrete_validN : ValidN A := λ n x, ✓ x.
  Definition discrete_cmra_mixin : CMRAMixin A.
  Proof.
    destruct ra_mix; split; try done.
    - intros x; split; first done. by move=> /(_ 0).
    - intros n x y1 y2 ??; by exists (y1,y2).
  Qed.
End discrete.

Notation discreteR A ra_mix :=
  (CMRAT A discrete_cofe_mixin (discrete_cmra_mixin ra_mix)).
Notation discreteLeibnizR A ra_mix :=
  (CMRAT A (@discrete_cofe_mixin _ equivL _) (discrete_cmra_mixin ra_mix)).

Global Instance discrete_cmra_discrete `{Equiv A, Core A, Op A, Valid A,
  @Equivalence A (≡)} (ra_mix : RAMixin A) : CMRADiscrete (discreteR A ra_mix).
Proof. split. apply _. done. Qed.

(** ** CMRA for the unit type *)
Section unit.
  Instance unit_valid : Valid () := λ x, True.
  Instance unit_validN : ValidN () := λ n x, True.
  Instance unit_core : Core () := λ x, x.
  Instance unit_op : Op () := λ x y, ().
  Global Instance unit_empty : Empty () := ().
  Definition unit_cmra_mixin : CMRAMixin ().
  Proof. by split; last exists ((),()). Qed.
  Canonical Structure unitR : cmraT := CMRAT () unit_cofe_mixin unit_cmra_mixin.
  Global Instance unit_cmra_unit : CMRAUnit unitR.
  Global Instance unit_cmra_discrete : CMRADiscrete unitR.
  Proof. done. Qed.
  Global Instance unit_persistent (x : ()) : Persistent x.
  Proof. done. Qed.
End unit.

(** ** Product *)
Section prod.
  Context {A B : cmraT}.
  Instance prod_op : Op (A * B) := λ x y, (x.1 ⋅ y.1, x.2 ⋅ y.2).
  Global Instance prod_empty `{Empty A, Empty B} : Empty (A * B) := (∅, ∅).
  Instance prod_core : Core (A * B) := λ x, (core (x.1), core (x.2)).
  Instance prod_valid : Valid (A * B) := λ x, ✓ x.1 ∧ ✓ x.2.
  Instance prod_validN : ValidN (A * B) := λ n x, ✓{n} x.1 ∧ ✓{n} x.2.
  Lemma prod_included (x y : A * B) : x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2.
  Proof.
    split; [intros [z Hz]; split; [exists (z.1)|exists (z.2)]; apply Hz|].
    intros [[z1 Hz1] [z2 Hz2]]; exists (z1,z2); split; auto.
  Qed.
  Lemma prod_includedN (x y : A * B) n : x ≼{n} y ↔ x.1 ≼{n} y.1 ∧ x.2 ≼{n} y.2.
  Proof.
    split; [intros [z Hz]; split; [exists (z.1)|exists (z.2)]; apply Hz|].
    intros [[z1 Hz1] [z2 Hz2]]; exists (z1,z2); split; auto.
  Qed.
  Definition prod_cmra_mixin : CMRAMixin (A * B).
  Proof.
    split; try apply _.
    - by intros n x y1 y2 [Hy1 Hy2]; split; rewrite /= ?Hy1 ?Hy2.
    - by intros n y1 y2 [Hy1 Hy2]; split; rewrite /= ?Hy1 ?Hy2.
    - by intros n y1 y2 [Hy1 Hy2] [??]; split; rewrite /= -?Hy1 -?Hy2.
    - intros x; split.
      + intros [??] n; split; by apply cmra_valid_validN.
      + intros Hxy; split; apply cmra_valid_validN=> n; apply Hxy.
    - by intros n x [??]; split; apply cmra_validN_S.
    - by split; rewrite /= assoc.
    - by split; rewrite /= comm.
    - by split; rewrite /= cmra_core_l.
    - by split; rewrite /= cmra_core_idemp.
    - intros x y; rewrite !prod_included.
      by intros [??]; split; apply cmra_core_preserving.
    - intros n x y [??]; split; simpl in *; eauto using cmra_validN_op_l.
    - intros n x y1 y2 [??] [??]; simpl in *.
      destruct (cmra_extend n (x.1) (y1.1) (y2.1)) as (z1&?&?&?); auto.
      destruct (cmra_extend n (x.2) (y1.2) (y2.2)) as (z2&?&?&?); auto.
      by exists ((z1.1,z2.1),(z1.2,z2.2)).
  Qed.
  Canonical Structure prodR : cmraT :=
    CMRAT (A * B) prod_cofe_mixin prod_cmra_mixin.
  Global Instance prod_cmra_unit `{Empty A, Empty B} :
    CMRAUnit A → CMRAUnit B → CMRAUnit prodR.
  Proof.
    split.
    - split; apply cmra_unit_valid.
    - by split; rewrite /=left_id.
    - by intros ? [??]; split; apply (timeless _).
  Qed.
  Global Instance prod_cmra_discrete :
    CMRADiscrete A → CMRADiscrete B → CMRADiscrete prodR.
  Proof. split. apply _. by intros ? []; split; apply cmra_discrete_valid. Qed.

  Global Instance pair_persistent x y :
    Persistent x → Persistent y → Persistent (x,y).
  Proof. by split. Qed.

  Lemma pair_split `{CMRAUnit A, CMRAUnit B} (x : A) (y : B) :
    (x, y) ≡ (x, ∅) ⋅ (∅, y).
  Proof. constructor; by rewrite /= ?left_id ?right_id. Qed.

  Lemma prod_update x y : x.1 ~~> y.1 → x.2 ~~> y.2 → x ~~> y.
  Proof. intros ?? n z [??]; split; simpl in *; auto. Qed.
  Lemma prod_updateP P1 P2 (Q : A * B → Prop)  x :
    x.1 ~~>: P1 → x.2 ~~>: P2 → (∀ a b, P1 a → P2 b → Q (a,b)) → x ~~>: Q.
  Proof.
    intros Hx1 Hx2 HP n z [??]; simpl in *.
    destruct (Hx1 n (z.1)) as (a&?&?), (Hx2 n (z.2)) as (b&?&?); auto.
    exists (a,b); repeat split; auto.
  Qed.
  Lemma prod_updateP' P1 P2 x :
    x.1 ~~>: P1 → x.2 ~~>: P2 → x ~~>: λ y, P1 (y.1) ∧ P2 (y.2).
  Proof. eauto using prod_updateP. Qed.

  Global Instance prod_local_update
      (LA : A → A) `{!LocalUpdate LvA LA} (LB : B → B) `{!LocalUpdate LvB LB} :
    LocalUpdate (λ x, LvA (x.1) ∧ LvB (x.2)) (prod_map LA LB).
  Proof.
    constructor.
    - intros n x y [??]; constructor; simpl; by apply local_update_ne.
    - intros n ?? [??] [??];
        constructor; simpl in *; eapply local_updateN; eauto.
  Qed.
End prod.

Arguments prodR : clear implicits.

Instance prod_map_cmra_monotone {A A' B B' : cmraT} (f : A → A') (g : B → B') :
  CMRAMonotone f → CMRAMonotone g → CMRAMonotone (prod_map f g).
Proof.
  split; first apply _.
  - by intros n x [??]; split; simpl; apply validN_preserving.
  - intros x y; rewrite !prod_included=> -[??] /=.
    by split; apply included_preserving.
Qed.
Program Definition prodRF (F1 F2 : rFunctor) : rFunctor := {|
  rFunctor_car A B := prodR (rFunctor_car F1 A B) (rFunctor_car F2 A B);
  rFunctor_map A1 A2 B1 B2 fg :=
    prodC_map (rFunctor_map F1 fg) (rFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 A1 A2 B1 B2 n ???; by apply prodC_map_ne; apply rFunctor_ne.
Qed.
Next Obligation. by intros F1 F2 A B [??]; rewrite /= !rFunctor_id. Qed.
Next Obligation.
  intros F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl.
  by rewrite !rFunctor_compose.
Qed.

Instance prodRF_contractive F1 F2 :
  rFunctorContractive F1 → rFunctorContractive F2 →
  rFunctorContractive (prodRF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply prodC_map_ne; apply rFunctor_contractive.
Qed.

(** ** CMRA for the option type *)
Section option.
  Context {A : cmraT}.

  Instance option_valid : Valid (option A) := λ mx,
    match mx with Some x => ✓ x | None => True end.
  Instance option_validN : ValidN (option A) := λ n mx,
    match mx with Some x => ✓{n} x | None => True end.
  Global Instance option_empty : Empty (option A) := None.
  Instance option_core : Core (option A) := fmap core.
  Instance option_op : Op (option A) := union_with (λ x y, Some (x ⋅ y)).

  Definition Some_valid a : ✓ Some a ↔ ✓ a := reflexivity _.
  Definition Some_op a b : Some (a ⋅ b) = Some a ⋅ Some b := eq_refl.

  Lemma option_included (mx my : option A) :
    mx ≼ my ↔ mx = None ∨ ∃ x y, mx = Some x ∧ my = Some y ∧ x ≼ y.
  Proof.
    split.
    - intros [mz Hmz].
      destruct mx as [x|]; [right|by left].
      destruct my as [y|]; [exists x, y|destruct mz; inversion_clear Hmz].
      destruct mz as [z|]; inversion_clear Hmz; split_and?; auto;
        setoid_subst; eauto using cmra_included_l.
    - intros [->|(x&y&->&->&z&Hz)]; try (by exists my; destruct my; constructor).
      by exists (Some z); constructor.
  Qed.

  Definition option_cmra_mixin  : CMRAMixin (option A).
  Proof.
    split.
    - by intros n [x|]; destruct 1; constructor; cofe_subst.
    - by destruct 1; constructor; cofe_subst.
    - by destruct 1; rewrite /validN /option_validN //=; cofe_subst.
    - intros [x|]; [apply cmra_valid_validN|done].
    - intros n [x|]; unfold validN, option_validN; eauto using cmra_validN_S.
    - intros [x|] [y|] [z|]; constructor; rewrite ?assoc; auto.
    - intros [x|] [y|]; constructor; rewrite 1?comm; auto.
    - by intros [x|]; constructor; rewrite cmra_core_l.
    - by intros [x|]; constructor; rewrite cmra_core_idemp.
    - intros mx my; rewrite !option_included ;intros [->|(x&y&->&->&?)]; auto.
      right; exists (core x), (core y); eauto using cmra_core_preserving.
    - intros n [x|] [y|]; rewrite /validN /option_validN /=;
        eauto using cmra_validN_op_l.
    - intros n mx my1 my2.
      destruct mx as [x|], my1 as [y1|], my2 as [y2|]; intros Hx Hx';
        try (by exfalso; inversion Hx'; auto).
      + destruct (cmra_extend n x y1 y2) as ([z1 z2]&?&?&?); auto.
        { by inversion_clear Hx'. }
        by exists (Some z1, Some z2); repeat constructor.
      + by exists (Some x,None); inversion Hx'; repeat constructor.
      + by exists (None,Some x); inversion Hx'; repeat constructor.
      + exists (None,None); repeat constructor.
  Qed.
  Canonical Structure optionR :=
    CMRAT (option A) option_cofe_mixin option_cmra_mixin.
  Global Instance option_cmra_unit : CMRAUnit optionR.
  Proof. split. done. by intros []. by inversion_clear 1. Qed.
  Global Instance option_cmra_discrete : CMRADiscrete A → CMRADiscrete optionR.
  Proof. split; [apply _|]. by intros [x|]; [apply (cmra_discrete_valid x)|]. Qed.

  (** Misc *)
  Global Instance Some_cmra_monotone : CMRAMonotone Some.
  Proof. split; [apply _|done|intros x y [z ->]; by exists (Some z)]. Qed.
  Lemma op_is_Some mx my : is_Some (mx ⋅ my) ↔ is_Some mx ∨ is_Some my.
  Proof.
    destruct mx, my; rewrite /op /option_op /= -!not_eq_None_Some; naive_solver.
  Qed.
  Lemma option_op_positive_dist_l n mx my : mx ⋅ my ≡{n}≡ None → mx ≡{n}≡ None.
  Proof. by destruct mx, my; inversion_clear 1. Qed.
  Lemma option_op_positive_dist_r n mx my : mx ⋅ my ≡{n}≡ None → my ≡{n}≡ None.
  Proof. by destruct mx, my; inversion_clear 1. Qed.

  Global Instance Some_persistent (x : A) : Persistent x → Persistent (Some x).
  Proof. by constructor. Qed.
  Global Instance option_persistent (mx : option A) :
    (∀ x : A, Persistent x) → Persistent mx.
  Proof. intros. destruct mx. apply _. apply cmra_unit_persistent. Qed.

  (** Updates *)
  Lemma option_updateP (P : A → Prop) (Q : option A → Prop) x :
    x ~~>: P → (∀ y, P y → Q (Some y)) → Some x ~~>: Q.
  Proof.
    intros Hx Hy n [y|] ?.
    { destruct (Hx n y) as (y'&?&?); auto. exists (Some y'); auto. }
    destruct (Hx n (core x)) as (y'&?&?); rewrite ?cmra_core_r; auto.
    by exists (Some y'); split; [auto|apply cmra_validN_op_l with (core x)].
  Qed.
  Lemma option_updateP' (P : A → Prop) x :
    x ~~>: P → Some x ~~>: λ my, default False my P.
  Proof. eauto using option_updateP. Qed.
  Lemma option_update x y : x ~~> y → Some x ~~> Some y.
  Proof.
    rewrite !cmra_update_updateP; eauto using option_updateP with congruence.
  Qed.
  Lemma option_update_None `{Empty A, !CMRAUnit A} : ∅ ~~> Some ∅.
  Proof.
    intros n [x|] ?; rewrite /op /cmra_op /validN /cmra_validN /= ?left_id;
      auto using cmra_unit_validN.
  Qed.
End option.

Arguments optionR : clear implicits.

Instance option_fmap_cmra_monotone {A B : cmraT} (f: A → B) `{!CMRAMonotone f} :
  CMRAMonotone (fmap f : option A → option B).
Proof.
  split; first apply _.
  - intros n [x|] ?; rewrite /cmra_validN //=. by apply (validN_preserving f).
  - intros mx my; rewrite !option_included.
    intros [->|(x&y&->&->&?)]; simpl; eauto 10 using @included_preserving.
Qed.
Program Definition optionRF (F : rFunctor) : rFunctor := {|
  rFunctor_car A B := optionR (rFunctor_car F A B);
  rFunctor_map A1 A2 B1 B2 fg := optionC_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_setoid_ext=>y; apply rFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_setoid_ext=>y; apply rFunctor_compose.
Qed.

Instance optionRF_contractive F :
  rFunctorContractive F → rFunctorContractive (optionRF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_contractive.
Qed.
