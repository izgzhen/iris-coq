From iris.algebra Require Export cofe.

Class PCore (A : Type) := pcore : A → option A.
Instance: Params (@pcore) 2.

Class Op (A : Type) := op : A → A → A.
Instance: Params (@op) 2.
Infix "⋅" := op (at level 50, left associativity) : C_scope.
Notation "(⋅)" := op (only parsing) : C_scope.

(* The inclusion quantifies over [A], not [option A].  This means we do not get
   reflexivity.  However, if we used [option A], the following would no longer
   hold:
     x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2
*)
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

Record CMRAMixin A `{Dist A, Equiv A, PCore A, Op A, Valid A, ValidN A} := {
  (* setoids *)
  mixin_cmra_op_ne n (x : A) : Proper (dist n ==> dist n) (op x);
  mixin_cmra_pcore_ne n x y cx :
    x ≡{n}≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡{n}≡ cy;
  mixin_cmra_validN_ne n : Proper (dist n ==> impl) (validN n);
  (* valid *)
  mixin_cmra_valid_validN x : ✓ x ↔ ∀ n, ✓{n} x;
  mixin_cmra_validN_S n x : ✓{S n} x → ✓{n} x;
  (* monoid *)
  mixin_cmra_assoc : Assoc (≡) (⋅);
  mixin_cmra_comm : Comm (≡) (⋅);
  mixin_cmra_pcore_l x cx : pcore x = Some cx → cx ⋅ x ≡ x;
  mixin_cmra_pcore_idemp x cx : pcore x = Some cx → pcore cx ≡ Some cx;
  mixin_cmra_pcore_mono x y cx :
    x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy;
  mixin_cmra_validN_op_l n x y : ✓{n} (x ⋅ y) → ✓{n} x;
  mixin_cmra_extend n x y1 y2 :
    ✓{n} x → x ≡{n}≡ y1 ⋅ y2 →
    ∃ z1 z2, x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2
}.

(** Bundeled version *)
Structure cmraT := CMRAT' {
  cmra_car :> Type;
  cmra_equiv : Equiv cmra_car;
  cmra_dist : Dist cmra_car;
  cmra_compl : Compl cmra_car;
  cmra_pcore : PCore cmra_car;
  cmra_op : Op cmra_car;
  cmra_valid : Valid cmra_car;
  cmra_validN : ValidN cmra_car;
  cmra_cofe_mixin : CofeMixin cmra_car;
  cmra_mixin : CMRAMixin cmra_car;
  _ : Type
}.
Arguments CMRAT' _ {_ _ _ _ _ _ _} _ _ _.
Notation CMRAT A m m' := (CMRAT' A m m' A).
Arguments cmra_car : simpl never.
Arguments cmra_equiv : simpl never.
Arguments cmra_dist : simpl never.
Arguments cmra_compl : simpl never.
Arguments cmra_pcore : simpl never.
Arguments cmra_op : simpl never.
Arguments cmra_valid : simpl never.
Arguments cmra_validN : simpl never.
Arguments cmra_cofe_mixin : simpl never.
Arguments cmra_mixin : simpl never.
Add Printing Constructor cmraT.
Hint Extern 0 (PCore _) => eapply (@cmra_pcore _) : typeclass_instances.
Hint Extern 0 (Op _) => eapply (@cmra_op _) : typeclass_instances.
Hint Extern 0 (Valid _) => eapply (@cmra_valid _) : typeclass_instances.
Hint Extern 0 (ValidN _) => eapply (@cmra_validN _) : typeclass_instances.
Coercion cmra_cofeC (A : cmraT) : cofeT := CofeT A (cmra_cofe_mixin A).
Canonical Structure cmra_cofeC.

(** Lifting properties from the mixin *)
Section cmra_mixin.
  Context {A : cmraT}.
  Implicit Types x y : A.
  Global Instance cmra_op_ne n (x : A) : Proper (dist n ==> dist n) (op x).
  Proof. apply (mixin_cmra_op_ne _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_ne n x y cx :
    x ≡{n}≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡{n}≡ cy.
  Proof. apply (mixin_cmra_pcore_ne _ (cmra_mixin A)). Qed.
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
  Lemma cmra_pcore_l x cx : pcore x = Some cx → cx ⋅ x ≡ x.
  Proof. apply (mixin_cmra_pcore_l _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_idemp x cx : pcore x = Some cx → pcore cx ≡ Some cx.
  Proof. apply (mixin_cmra_pcore_idemp _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_mono x y cx :
    x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy.
  Proof. apply (mixin_cmra_pcore_mono _ (cmra_mixin A)). Qed.
  Lemma cmra_validN_op_l n x y : ✓{n} (x ⋅ y) → ✓{n} x.
  Proof. apply (mixin_cmra_validN_op_l _ (cmra_mixin A)). Qed.
  Lemma cmra_extend n x y1 y2 :
    ✓{n} x → x ≡{n}≡ y1 ⋅ y2 →
    ∃ z1 z2, x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2.
  Proof. apply (mixin_cmra_extend _ (cmra_mixin A)). Qed.
End cmra_mixin.

Definition opM {A : cmraT} (x : A) (my : option A) :=
  match my with Some y => x ⋅ y | None => x end.
Infix "⋅?" := opM (at level 50, left associativity) : C_scope.

(** * Persistent elements *)
Class Persistent {A : cmraT} (x : A) := persistent : pcore x ≡ Some x.
Arguments persistent {_} _ {_}.

(** * Exclusive elements (i.e., elements that cannot have a frame). *)
Class Exclusive {A : cmraT} (x : A) := exclusive0_l y : ✓{0} (x ⋅ y) → False.
Arguments exclusive0_l {_} _ {_} _ _.

(** * CMRAs whose core is total *)
(** The function [core] may return a dummy when used on CMRAs without total
core. *)
Class CMRATotal (A : cmraT) := cmra_total (x : A) : is_Some (pcore x).

Class Core (A : Type) := core : A → A.
Instance: Params (@core) 2.

Instance core' `{PCore A} : Core A := λ x, from_option id x (pcore x).
Arguments core' _ _ _ /.

(** * CMRAs with a unit element *)
(** We use the notation ∅ because for most instances (maps, sets, etc) the
`empty' element is the unit. *)
Record UCMRAMixin A `{Dist A, Equiv A, PCore A, Op A, Valid A, Empty A} := {
  mixin_ucmra_unit_valid : ✓ ∅;
  mixin_ucmra_unit_left_id : LeftId (≡) ∅ (⋅);
  mixin_ucmra_pcore_unit : pcore ∅ ≡ Some ∅
}.

Structure ucmraT := UCMRAT' {
  ucmra_car :> Type;
  ucmra_equiv : Equiv ucmra_car;
  ucmra_dist : Dist ucmra_car;
  ucmra_compl : Compl ucmra_car;
  ucmra_pcore : PCore ucmra_car;
  ucmra_op : Op ucmra_car;
  ucmra_valid : Valid ucmra_car;
  ucmra_validN : ValidN ucmra_car;
  ucmra_empty : Empty ucmra_car;
  ucmra_cofe_mixin : CofeMixin ucmra_car;
  ucmra_cmra_mixin : CMRAMixin ucmra_car;
  ucmra_mixin : UCMRAMixin ucmra_car;
  _ : Type;
}.
Arguments UCMRAT' _ {_ _ _ _ _ _ _ _} _ _ _ _.
Notation UCMRAT A m m' m'' := (UCMRAT' A m m' m'' A).
Arguments ucmra_car : simpl never.
Arguments ucmra_equiv : simpl never.
Arguments ucmra_dist : simpl never.
Arguments ucmra_compl : simpl never.
Arguments ucmra_pcore : simpl never.
Arguments ucmra_op : simpl never.
Arguments ucmra_valid : simpl never.
Arguments ucmra_validN : simpl never.
Arguments ucmra_cofe_mixin : simpl never.
Arguments ucmra_cmra_mixin : simpl never.
Arguments ucmra_mixin : simpl never.
Add Printing Constructor ucmraT.
Hint Extern 0 (Empty _) => eapply (@ucmra_empty _) : typeclass_instances.
Coercion ucmra_cofeC (A : ucmraT) : cofeT := CofeT A (ucmra_cofe_mixin A).
Canonical Structure ucmra_cofeC.
Coercion ucmra_cmraR (A : ucmraT) : cmraT :=
  CMRAT A (ucmra_cofe_mixin A) (ucmra_cmra_mixin A).
Canonical Structure ucmra_cmraR.

(** Lifting properties from the mixin *)
Section ucmra_mixin.
  Context {A : ucmraT}.
  Implicit Types x y : A.
  Lemma ucmra_unit_valid : ✓ (∅ : A).
  Proof. apply (mixin_ucmra_unit_valid _ (ucmra_mixin A)). Qed.
  Global Instance ucmra_unit_left_id : LeftId (≡) ∅ (@op A _).
  Proof. apply (mixin_ucmra_unit_left_id _ (ucmra_mixin A)). Qed.
  Lemma ucmra_pcore_unit : pcore (∅:A) ≡ Some ∅.
  Proof. apply (mixin_ucmra_pcore_unit _ (ucmra_mixin A)). Qed.
End ucmra_mixin.

(** * Discrete CMRAs *)
Class CMRADiscrete (A : cmraT) := {
  cmra_discrete :> Discrete A;
  cmra_discrete_valid (x : A) : ✓{0} x → ✓ x
}.

(** * Morphisms *)
Class CMRAMonotone {A B : cmraT} (f : A → B) := {
  cmra_monotone_ne n :> Proper (dist n ==> dist n) f;
  validN_preserving n x : ✓{n} x → ✓{n} f x;
  cmra_monotone x y : x ≼ y → f x ≼ f y
}.
Arguments validN_preserving {_ _} _ {_} _ _ _.
Arguments cmra_monotone {_ _} _ {_} _ _ _.

(** * Properties **)
Section cmra.
Context {A : cmraT}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(** ** Setoids *)
Global Instance cmra_pcore_ne' n : Proper (dist n ==> dist n) (@pcore A _).
Proof.
  intros x y Hxy. destruct (pcore x) as [cx|] eqn:?.
  { destruct (cmra_pcore_ne n x y cx) as (cy&->&->); auto. }
  destruct (pcore y) as [cy|] eqn:?; auto.
  destruct (cmra_pcore_ne n y x cy) as (cx&?&->); simplify_eq/=; auto.
Qed.
Lemma cmra_pcore_proper x y cx :
  x ≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡ cy.
Proof.
  intros. destruct (cmra_pcore_ne 0 x y cx) as (cy&?&?); auto.
  exists cy; split; [done|apply equiv_dist=> n].
  destruct (cmra_pcore_ne n x y cx) as (cy'&?&?); naive_solver.
Qed.
Global Instance cmra_pcore_proper' : Proper ((≡) ==> (≡)) (@pcore A _).
Proof. apply (ne_proper _). Qed.
Global Instance cmra_op_ne' n : Proper (dist n ==> dist n ==> dist n) (@op A _).
Proof. intros x1 x2 Hx y1 y2 Hy. by rewrite Hy (comm _ x1) Hx (comm _ y2). Qed.
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
Global Instance cmra_opM_ne n : Proper (dist n ==> dist n ==> dist n) (@opM A).
Proof. destruct 2; by cofe_subst. Qed.
Global Instance cmra_opM_proper : Proper ((≡) ==> (≡) ==> (≡)) (@opM A).
Proof. destruct 2; by setoid_subst. Qed.

(** ** Op *)
Lemma cmra_opM_assoc x y mz : (x ⋅ y) ⋅? mz ≡ x ⋅ (y ⋅? mz).
Proof. destruct mz; by rewrite /= -?assoc. Qed.

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
Lemma cmra_pcore_l' x cx : pcore x ≡ Some cx → cx ⋅ x ≡ x.
Proof. intros (cx'&?&->)%equiv_Some_inv_r'. by apply cmra_pcore_l. Qed.
Lemma cmra_pcore_r x cx : pcore x = Some cx → x ⋅ cx ≡ x.
Proof. intros. rewrite comm. by apply cmra_pcore_l. Qed. 
Lemma cmra_pcore_r' x cx : pcore x ≡ Some cx → x ⋅ cx ≡ x.
Proof. intros (cx'&?&->)%equiv_Some_inv_r'. by apply cmra_pcore_r. Qed. 
Lemma cmra_pcore_idemp' x cx : pcore x ≡ Some cx → pcore cx ≡ Some cx.
Proof. intros (cx'&?&->)%equiv_Some_inv_r'. eauto using cmra_pcore_idemp. Qed. 
Lemma cmra_pcore_dup x cx : pcore x = Some cx → cx ≡ cx ⋅ cx.
Proof. intros; symmetry; eauto using cmra_pcore_r', cmra_pcore_idemp. Qed.
Lemma cmra_pcore_dup' x cx : pcore x ≡ Some cx → cx ≡ cx ⋅ cx.
Proof. intros; symmetry; eauto using cmra_pcore_r', cmra_pcore_idemp'. Qed.
Lemma cmra_pcore_validN n x cx : ✓{n} x → pcore x = Some cx → ✓{n} cx.
Proof.
  intros Hvx Hx%cmra_pcore_l. move: Hvx; rewrite -Hx. apply cmra_validN_op_l.
Qed.
Lemma cmra_pcore_valid x cx : ✓ x → pcore x = Some cx → ✓ cx.
Proof.
  intros Hv Hx%cmra_pcore_l. move: Hv; rewrite -Hx. apply cmra_valid_op_l.
Qed.

(** ** Persistent elements *)
Lemma persistent_dup x `{!Persistent x} : x ≡ x ⋅ x.
Proof. by apply cmra_pcore_dup' with x. Qed.

(** ** Exclusive elements *)
Lemma exclusiveN_l n x `{!Exclusive x} y : ✓{n} (x ⋅ y) → False.
Proof. intros. eapply (exclusive0_l x y), cmra_validN_le; eauto with lia. Qed.
Lemma exclusiveN_r n x `{!Exclusive x} y : ✓{n} (y ⋅ x) → False.
Proof. rewrite comm. by apply exclusiveN_l. Qed.
Lemma exclusive_l x `{!Exclusive x} y : ✓ (x ⋅ y) → False.
Proof. by move /cmra_valid_validN /(_ 0) /exclusive0_l. Qed.
Lemma exclusive_r x `{!Exclusive x} y : ✓ (y ⋅ x) → False.
Proof. rewrite comm. by apply exclusive_l. Qed.
Lemma exclusiveN_opM n x `{!Exclusive x} my : ✓{n} (x ⋅? my) → my = None.
Proof. destruct my as [y|]. move=> /(exclusiveN_l _ x) []. done. Qed.

(** ** Order *)
Lemma cmra_included_includedN n x y : x ≼ y → x ≼{n} y.
Proof. intros [z ->]. by exists z. Qed.
Global Instance cmra_includedN_trans n : Transitive (@includedN A _ _ n).
Proof.
  intros x y z [z1 Hy] [z2 Hz]; exists (z1 ⋅ z2). by rewrite assoc -Hy -Hz.
Qed.
Global Instance cmra_included_trans: Transitive (@included A _ _).
Proof.
  intros x y z [z1 Hy] [z2 Hz]; exists (z1 ⋅ z2). by rewrite assoc -Hy -Hz.
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

Lemma cmra_pcore_mono' x y cx :
  x ≼ y → pcore x ≡ Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy.
Proof.
  intros ? (cx'&?&Hcx)%equiv_Some_inv_r'.
  destruct (cmra_pcore_mono x y cx') as (cy&->&?); auto.
  exists cy; by rewrite Hcx.
Qed.
Lemma cmra_pcore_monoN' n x y cx :
  x ≼{n} y → pcore x ≡{n}≡ Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼{n} cy.
Proof.
  intros [z Hy] (cx'&?&Hcx)%dist_Some_inv_r'.
  destruct (cmra_pcore_mono x (x ⋅ z) cx')
    as (cy&Hxy&?); auto using cmra_included_l.
  assert (pcore y ≡{n}≡ Some cy) as (cy'&?&Hcy')%dist_Some_inv_r'.
  { by rewrite Hy Hxy. }
  exists cy'; split; first done.
  rewrite Hcx -Hcy'; auto using cmra_included_includedN.
Qed.
Lemma cmra_included_pcore x cx : pcore x = Some cx → cx ≼ x.
Proof. exists x. by rewrite cmra_pcore_l. Qed.
Lemma cmra_monoN_l n x y z : x ≼{n} y → z ⋅ x ≼{n} z ⋅ y.
Proof. by intros [z1 Hz1]; exists z1; rewrite Hz1 (assoc op). Qed.
Lemma cmra_mono_l x y z : x ≼ y → z ⋅ x ≼ z ⋅ y.
Proof. by intros [z1 Hz1]; exists z1; rewrite Hz1 (assoc op). Qed.
Lemma cmra_monoN_r n x y z : x ≼{n} y → x ⋅ z ≼{n} y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply cmra_monoN_l. Qed.
Lemma cmra_mono_r x y z : x ≼ y → x ⋅ z ≼ y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply cmra_mono_l. Qed.

Lemma cmra_included_dist_l n x1 x2 x1' :
  x1 ≼ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ x2' ∧ x2' ≡{n}≡ x2.
Proof.
  intros [z Hx2] Hx1; exists (x1' ⋅ z); split; auto using cmra_included_l.
  by rewrite Hx1 Hx2.
Qed.

(** ** Total core *)
Section total_core.
  Context `{CMRATotal A}.

  Lemma cmra_core_l x : core x ⋅ x ≡ x.
  Proof.
    destruct (cmra_total x) as [cx Hcx]. by rewrite /core /= Hcx cmra_pcore_l.
  Qed.
  Lemma cmra_core_idemp x : core (core x) ≡ core x.
  Proof.
    destruct (cmra_total x) as [cx Hcx]. by rewrite /core /= Hcx cmra_pcore_idemp.
  Qed.
  Lemma cmra_core_mono x y : x ≼ y → core x ≼ core y.
  Proof.
    intros; destruct (cmra_total x) as [cx Hcx].
    destruct (cmra_pcore_mono x y cx) as (cy&Hcy&?); auto.
    by rewrite /core /= Hcx Hcy.
  Qed.

  Global Instance cmra_core_ne n : Proper (dist n ==> dist n) (@core A _).
  Proof.
    intros x y Hxy. destruct (cmra_total x) as [cx Hcx].
    by rewrite /core /= -Hxy Hcx.
  Qed.
  Global Instance cmra_core_proper : Proper ((≡) ==> (≡)) (@core A _).
  Proof. apply (ne_proper _). Qed.

  Lemma cmra_core_r x : x ⋅ core x ≡ x.
  Proof. by rewrite (comm _ x) cmra_core_l. Qed.
  Lemma cmra_core_dup x : core x ≡ core x ⋅ core x.
  Proof. by rewrite -{3}(cmra_core_idemp x) cmra_core_r. Qed.
  Lemma cmra_core_validN n x : ✓{n} x → ✓{n} core x.
  Proof. rewrite -{1}(cmra_core_l x); apply cmra_validN_op_l. Qed.
  Lemma cmra_core_valid x : ✓ x → ✓ core x.
  Proof. rewrite -{1}(cmra_core_l x); apply cmra_valid_op_l. Qed.

  Lemma persistent_total x : Persistent x ↔ core x ≡ x.
  Proof.
    split; [intros; by rewrite /core /= (persistent x)|].
    rewrite /Persistent /core /=.
    destruct (cmra_total x) as [? ->]. by constructor.
  Qed.
  Lemma persistent_core x `{!Persistent x} : core x ≡ x.
  Proof. by apply persistent_total. Qed.

  Global Instance cmra_core_persistent x : Persistent (core x).
  Proof.
    destruct (cmra_total x) as [cx Hcx].
    rewrite /Persistent /core /= Hcx /=. eauto using cmra_pcore_idemp.
  Qed.

  Lemma cmra_included_core x : core x ≼ x.
  Proof. by exists x; rewrite cmra_core_l. Qed.
  Global Instance cmra_includedN_preorder n : PreOrder (@includedN A _ _ n).
  Proof.
    split; [|apply _]. by intros x; exists (core x); rewrite cmra_core_r.
  Qed.
  Global Instance cmra_included_preorder : PreOrder (@included A _ _).
  Proof.
    split; [|apply _]. by intros x; exists (core x); rewrite cmra_core_r.
  Qed.
  Lemma cmra_core_monoN n x y : x ≼{n} y → core x ≼{n} core y.
  Proof.
    intros [z ->].
    apply cmra_included_includedN, cmra_core_mono, cmra_included_l.
  Qed.
End total_core.

(** ** Timeless *)
Lemma cmra_timeless_included_l x y : Timeless x → ✓{0} y → x ≼{0} y → x ≼ y.
Proof.
  intros ?? [x' ?].
  destruct (cmra_extend 0 y x x') as (z&z'&Hy&Hz&Hz'); auto; simpl in *.
  by exists z'; rewrite Hy (timeless x z).
Qed.
Lemma cmra_timeless_included_r x y : Timeless y → x ≼{0} y → x ≼ y.
Proof. intros ? [x' ?]. exists x'. by apply (timeless y). Qed.
Lemma cmra_op_timeless x1 x2 :
  ✓ (x1 ⋅ x2) → Timeless x1 → Timeless x2 → Timeless (x1 ⋅ x2).
Proof.
  intros ??? z Hz.
  destruct (cmra_extend 0 z x1 x2) as (y1&y2&Hz'&?&?); auto; simpl in *.
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
End cmra.

(** * Properties about CMRAs with a unit element **)
Section ucmra.
  Context {A : ucmraT}.
  Implicit Types x y z : A.

  Lemma ucmra_unit_validN n : ✓{n} (∅:A).
  Proof. apply cmra_valid_validN, ucmra_unit_valid. Qed.
  Lemma ucmra_unit_leastN n x : ∅ ≼{n} x.
  Proof. by exists x; rewrite left_id. Qed.
  Lemma ucmra_unit_least x : ∅ ≼ x.
  Proof. by exists x; rewrite left_id. Qed.
  Global Instance ucmra_unit_right_id : RightId (≡) ∅ (@op A _).
  Proof. by intros x; rewrite (comm op) left_id. Qed.
  Global Instance ucmra_unit_persistent : Persistent (∅:A).
  Proof. apply ucmra_pcore_unit. Qed.

  Global Instance cmra_unit_total : CMRATotal A.
  Proof.
    intros x. destruct (cmra_pcore_mono' ∅ x ∅) as (cx&->&?);
      eauto using ucmra_unit_least, (persistent ∅).
  Qed.
End ucmra.
Hint Immediate cmra_unit_total.

(** * Constructing a CMRA with total core *)
Section cmra_total.
  Context A `{Dist A, Equiv A, PCore A, Op A, Valid A, ValidN A}.
  Context (total : ∀ x, is_Some (pcore x)).
  Context (op_ne : ∀ n (x : A), Proper (dist n ==> dist n) (op x)).
  Context (core_ne : ∀ n, Proper (dist n ==> dist n) (@core A _)).
  Context (validN_ne : ∀ n, Proper (dist n ==> impl) (@validN A _ n)).
  Context (valid_validN : ∀ (x : A), ✓ x ↔ ∀ n, ✓{n} x).
  Context (validN_S : ∀ n (x : A), ✓{S n} x → ✓{n} x).
  Context (op_assoc : Assoc (≡) (@op A _)).
  Context (op_comm : Comm (≡) (@op A _)).
  Context (core_l : ∀ x : A, core x ⋅ x ≡ x).
  Context (core_idemp : ∀ x : A, core (core x) ≡ core x).
  Context (core_mono : ∀ x y : A, x ≼ y → core x ≼ core y).
  Context (validN_op_l : ∀ n (x y : A), ✓{n} (x ⋅ y) → ✓{n} x).
  Context (extend : ∀ n (x y1 y2 : A),
    ✓{n} x → x ≡{n}≡ y1 ⋅ y2 →
    ∃ z1 z2, x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2).
  Lemma cmra_total_mixin : CMRAMixin A.
  Proof.
    split; auto.
    - intros n x y ? Hcx%core_ne Hx; move: Hcx. rewrite /core /= Hx /=.
      case (total y)=> [cy ->]; eauto.
    - intros x cx Hcx. move: (core_l x). by rewrite /core /= Hcx.
    - intros x cx Hcx. move: (core_idemp x). rewrite /core /= Hcx /=.
      case (total cx)=>[ccx ->]; by constructor.
    - intros x y cx Hxy%core_mono Hx. move: Hxy.
      rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto.
  Qed.
End cmra_total.

(** * Properties about monotone functions *)
Instance cmra_monotone_id {A : cmraT} : CMRAMonotone (@id A).
Proof. repeat split; by try apply _. Qed.
Instance cmra_monotone_compose {A B C : cmraT} (f : A → B) (g : B → C) :
  CMRAMonotone f → CMRAMonotone g → CMRAMonotone (g ∘ f).
Proof.
  split.
  - apply _. 
  - move=> n x Hx /=. by apply validN_preserving, validN_preserving.
  - move=> x y Hxy /=. by apply cmra_monotone, cmra_monotone.
Qed.

Section cmra_monotone.
  Context {A B : cmraT} (f : A → B) `{!CMRAMonotone f}.
  Global Instance cmra_monotone_proper : Proper ((≡) ==> (≡)) f := ne_proper _.
  Lemma cmra_monotoneN n x y : x ≼{n} y → f x ≼{n} f y.
  Proof.
    intros [z ->].
    apply cmra_included_includedN, (cmra_monotone f), cmra_included_l.
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

Structure urFunctor := URFunctor {
  urFunctor_car : cofeT → cofeT → ucmraT;
  urFunctor_map {A1 A2 B1 B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → urFunctor_car A1 B1 -n> urFunctor_car A2 B2;
  urFunctor_ne A1 A2 B1 B2 n :
    Proper (dist n ==> dist n) (@urFunctor_map A1 A2 B1 B2);
  urFunctor_id {A B} (x : urFunctor_car A B) : urFunctor_map (cid,cid) x ≡ x;
  urFunctor_compose {A1 A2 A3 B1 B2 B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    urFunctor_map (f◎g, g'◎f') x ≡ urFunctor_map (g,g') (urFunctor_map (f,f') x);
  urFunctor_mono {A1 A2 B1 B2} (fg : (A2 -n> A1) * (B1 -n> B2)) :
    CMRAMonotone (urFunctor_map fg) 
}.
Existing Instances urFunctor_ne urFunctor_mono.
Instance: Params (@urFunctor_map) 5.

Class urFunctorContractive (F : urFunctor) :=
  urFunctor_contractive A1 A2 B1 B2 :> Contractive (@urFunctor_map F A1 A2 B1 B2).

Definition urFunctor_diag (F: urFunctor) (A: cofeT) : ucmraT := urFunctor_car F A A.
Coercion urFunctor_diag : urFunctor >-> Funclass.

Program Definition constURF (B : ucmraT) : urFunctor :=
  {| urFunctor_car A1 A2 := B; urFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.

Instance constURF_contractive B : urFunctorContractive (constURF B).
Proof. rewrite /urFunctorContractive; apply _. Qed.

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
End cmra_transport.

(** * Instances *)
(** ** Discrete CMRA *)
Record RAMixin A `{Equiv A, PCore A, Op A, Valid A} := {
  (* setoids *)
  ra_op_proper (x : A) : Proper ((≡) ==> (≡)) (op x);
  ra_core_proper x y cx :
    x ≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡ cy;
  ra_validN_proper : Proper ((≡) ==> impl) valid;
  (* monoid *)
  ra_assoc : Assoc (≡) (⋅);
  ra_comm : Comm (≡) (⋅);
  ra_pcore_l x cx : pcore x = Some cx → cx ⋅ x ≡ x;
  ra_pcore_idemp x cx : pcore x = Some cx → pcore cx ≡ Some cx;
  ra_pcore_mono x y cx :
    x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy;
  ra_valid_op_l x y : ✓ (x ⋅ y) → ✓ x
}.

Section discrete.
  Context `{Equiv A, PCore A, Op A, Valid A, @Equivalence A (≡)}.
  Context (ra_mix : RAMixin A).
  Existing Instances discrete_dist discrete_compl.

  Instance discrete_validN : ValidN A := λ n x, ✓ x.
  Definition discrete_cmra_mixin : CMRAMixin A.
  Proof.
    destruct ra_mix; split; try done.
    - intros x; split; first done. by move=> /(_ 0).
    - intros n x y1 y2 ??; by exists y1, y2.
  Qed.
End discrete.

Notation discreteR A ra_mix :=
  (CMRAT A discrete_cofe_mixin (discrete_cmra_mixin ra_mix)).
Notation discreteUR A ra_mix ucmra_mix :=
  (UCMRAT A discrete_cofe_mixin (discrete_cmra_mixin ra_mix) ucmra_mix).

Global Instance discrete_cmra_discrete `{Equiv A, PCore A, Op A, Valid A,
  @Equivalence A (≡)} (ra_mix : RAMixin A) : CMRADiscrete (discreteR A ra_mix).
Proof. split. apply _. done. Qed.

Section ra_total.
  Context A `{Equiv A, PCore A, Op A, Valid A}.
  Context (total : ∀ x, is_Some (pcore x)).
  Context (op_proper : ∀ (x : A), Proper ((≡) ==> (≡)) (op x)).
  Context (core_proper: Proper ((≡) ==> (≡)) (@core A _)).
  Context (valid_proper : Proper ((≡) ==> impl) (@valid A _)).
  Context (op_assoc : Assoc (≡) (@op A _)).
  Context (op_comm : Comm (≡) (@op A _)).
  Context (core_l : ∀ x : A, core x ⋅ x ≡ x).
  Context (core_idemp : ∀ x : A, core (core x) ≡ core x).
  Context (core_mono : ∀ x y : A, x ≼ y → core x ≼ core y).
  Context (valid_op_l : ∀ x y : A, ✓ (x ⋅ y) → ✓ x).
  Lemma ra_total_mixin : RAMixin A.
  Proof.
    split; auto.
    - intros x y ? Hcx%core_proper Hx; move: Hcx. rewrite /core /= Hx /=.
      case (total y)=> [cy ->]; eauto.
    - intros x cx Hcx. move: (core_l x). by rewrite /core /= Hcx.
    - intros x cx Hcx. move: (core_idemp x). rewrite /core /= Hcx /=.
      case (total cx)=>[ccx ->]; by constructor.
    - intros x y cx Hxy%core_mono Hx. move: Hxy.
      rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto.
  Qed.
End ra_total.

(** ** CMRA for the unit type *)
Section unit.
  Instance unit_valid : Valid () := λ x, True.
  Instance unit_validN : ValidN () := λ n x, True.
  Instance unit_pcore : PCore () := λ x, Some x.
  Instance unit_op : Op () := λ x y, ().
  Lemma unit_cmra_mixin : CMRAMixin ().
  Proof. apply discrete_cmra_mixin, ra_total_mixin; by eauto. Qed.
  Canonical Structure unitR : cmraT := CMRAT () unit_cofe_mixin unit_cmra_mixin.

  Instance unit_empty : Empty () := ().
  Lemma unit_ucmra_mixin : UCMRAMixin ().
  Proof. done. Qed.
  Canonical Structure unitUR : ucmraT :=
    UCMRAT () unit_cofe_mixin unit_cmra_mixin unit_ucmra_mixin.

  Global Instance unit_cmra_discrete : CMRADiscrete unitR.
  Proof. done. Qed.
  Global Instance unit_persistent (x : ()) : Persistent x.
  Proof. by constructor. Qed.
End unit.

(** ** Natural numbers *)
Section nat.
  Instance nat_valid : Valid nat := λ x, True.
  Instance nat_validN : ValidN nat := λ n x, True.
  Instance nat_pcore : PCore nat := λ x, Some 0.
  Instance nat_op : Op nat := plus.
  Definition nat_op_plus x y : x ⋅ y = x + y := eq_refl.
  Lemma nat_included (x y : nat) : x ≼ y ↔ x ≤ y.
  Proof.
    split.
    - intros [z ->]; unfold op, nat_op; lia.
    - exists (y - x). by apply le_plus_minus.
  Qed.
  Lemma nat_ra_mixin : RAMixin nat.
  Proof.
    apply ra_total_mixin; try by eauto.
    - solve_proper.
    - intros x y z. apply Nat.add_assoc.
    - intros x y. apply Nat.add_comm.
    - by exists 0.
  Qed.
  Canonical Structure natR : cmraT := discreteR nat nat_ra_mixin.

  Instance nat_empty : Empty nat := 0.
  Lemma nat_ucmra_mixin : UCMRAMixin nat.
  Proof. split; apply _ || done. Qed.
  Canonical Structure natUR : ucmraT :=
    discreteUR nat nat_ra_mixin nat_ucmra_mixin.

  Global Instance nat_cmra_discrete : CMRADiscrete natR.
  Proof. constructor; apply _ || done. Qed.
End nat.

Definition mnat := nat.

Section mnat.
  Instance mnat_valid : Valid mnat := λ x, True.
  Instance mnat_validN : ValidN mnat := λ n x, True.
  Instance mnat_pcore : PCore mnat := Some.
  Instance mnat_op : Op mnat := Nat.max.
  Definition mnat_op_max x y : x ⋅ y = x `max` y := eq_refl.
  Lemma mnat_included (x y : mnat) : x ≼ y ↔ x ≤ y.
  Proof.
    split.
    - intros [z ->]; unfold op, mnat_op; lia.
    - exists y. by symmetry; apply Nat.max_r.
  Qed.
  Lemma mnat_ra_mixin : RAMixin mnat.
  Proof.
    apply ra_total_mixin; try by eauto.
    - solve_proper.
    - solve_proper.
    - intros x y z. apply Nat.max_assoc.
    - intros x y. apply Nat.max_comm.
    - intros x. apply Max.max_idempotent.
  Qed.
  Canonical Structure mnatR : cmraT := discreteR mnat mnat_ra_mixin.

  Instance mnat_empty : Empty mnat := 0.
  Lemma mnat_ucmra_mixin : UCMRAMixin mnat.
  Proof. split; apply _ || done. Qed.
  Canonical Structure mnatUR : ucmraT :=
    discreteUR mnat mnat_ra_mixin mnat_ucmra_mixin.

  Global Instance mnat_cmra_discrete : CMRADiscrete mnatR.
  Proof. constructor; apply _ || done. Qed.
  Global Instance mnat_persistent (x : mnat) : Persistent x.
  Proof. by constructor. Qed.
End mnat.

(** ** Product *)
Section prod.
  Context {A B : cmraT}.
  Local Arguments pcore _ _ !_ /.
  Local Arguments cmra_pcore _ !_/.

  Instance prod_op : Op (A * B) := λ x y, (x.1 ⋅ y.1, x.2 ⋅ y.2).
  Instance prod_pcore : PCore (A * B) := λ x,
    c1 ← pcore (x.1); c2 ← pcore (x.2); Some (c1, c2).
  Arguments prod_pcore !_ /.
  Instance prod_valid : Valid (A * B) := λ x, ✓ x.1 ∧ ✓ x.2.
  Instance prod_validN : ValidN (A * B) := λ n x, ✓{n} x.1 ∧ ✓{n} x.2.

  Lemma prod_pcore_Some (x cx : A * B) :
    pcore x = Some cx ↔ pcore (x.1) = Some (cx.1) ∧ pcore (x.2) = Some (cx.2).
  Proof. destruct x, cx; by intuition simplify_option_eq. Qed.
  Lemma prod_pcore_Some' (x cx : A * B) :
    pcore x ≡ Some cx ↔ pcore (x.1) ≡ Some (cx.1) ∧ pcore (x.2) ≡ Some (cx.2).
  Proof.
    split; [by intros (cx'&[-> ->]%prod_pcore_Some&->)%equiv_Some_inv_r'|].
    rewrite {3}/pcore /prod_pcore. (* TODO: use setoid rewrite *)
    intros [Hx1 Hx2]; inversion_clear Hx1; simpl; inversion_clear Hx2.
    by constructor.
  Qed.

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
    - intros n x y cx; setoid_rewrite prod_pcore_Some=> -[??] [??].
      destruct (cmra_pcore_ne n (x.1) (y.1) (cx.1)) as (z1&->&?); auto.
      destruct (cmra_pcore_ne n (x.2) (y.2) (cx.2)) as (z2&->&?); auto.
      exists (z1,z2); repeat constructor; auto.
    - by intros n y1 y2 [Hy1 Hy2] [??]; split; rewrite /= -?Hy1 -?Hy2.
    - intros x; split.
      + intros [??] n; split; by apply cmra_valid_validN.
      + intros Hxy; split; apply cmra_valid_validN=> n; apply Hxy.
    - by intros n x [??]; split; apply cmra_validN_S.
    - by split; rewrite /= assoc.
    - by split; rewrite /= comm.
    - intros x y [??]%prod_pcore_Some;
        constructor; simpl; eauto using cmra_pcore_l.
    - intros x y; rewrite prod_pcore_Some prod_pcore_Some'.
      naive_solver eauto using cmra_pcore_idemp.
    - intros x y cx; rewrite prod_included prod_pcore_Some=> -[??] [??].
      destruct (cmra_pcore_mono (x.1) (y.1) (cx.1)) as (z1&?&?); auto.
      destruct (cmra_pcore_mono (x.2) (y.2) (cx.2)) as (z2&?&?); auto.
      exists (z1,z2). by rewrite prod_included prod_pcore_Some.
    - intros n x y [??]; split; simpl in *; eauto using cmra_validN_op_l.
    - intros n x y1 y2 [??] [??]; simpl in *.
      destruct (cmra_extend n (x.1) (y1.1) (y2.1)) as (z11&z12&?&?&?); auto.
      destruct (cmra_extend n (x.2) (y1.2) (y2.2)) as (z21&z22&?&?&?); auto.
      by exists (z11,z21), (z12,z22).
  Qed.
  Canonical Structure prodR :=
    CMRAT (A * B) prod_cofe_mixin prod_cmra_mixin.

  Lemma pair_op (a a' : A) (b b' : B) : (a, b) ⋅ (a', b') = (a ⋅ a', b ⋅ b').
  Proof. done. Qed.

  Global Instance prod_cmra_total : CMRATotal A → CMRATotal B → CMRATotal prodR.
  Proof.
    intros H1 H2 [a b]. destruct (H1 a) as [ca ?], (H2 b) as [cb ?].
    exists (ca,cb); by simplify_option_eq.
  Qed.

  Global Instance prod_cmra_discrete :
    CMRADiscrete A → CMRADiscrete B → CMRADiscrete prodR.
  Proof. split. apply _. by intros ? []; split; apply cmra_discrete_valid. Qed.

  Global Instance pair_persistent x y :
    Persistent x → Persistent y → Persistent (x,y).
  Proof. by rewrite /Persistent prod_pcore_Some'. Qed.

  Global Instance pair_exclusive_l x y : Exclusive x → Exclusive (x,y).
  Proof. by intros ?[][?%exclusive0_l]. Qed.
  Global Instance pair_exclusive_r x y : Exclusive y → Exclusive (x,y).
  Proof. by intros ?[][??%exclusive0_l]. Qed.
End prod.

Arguments prodR : clear implicits.

Section prod_unit.
  Context {A B : ucmraT}.

  Instance prod_empty `{Empty A, Empty B} : Empty (A * B) := (∅, ∅).
  Lemma prod_ucmra_mixin : UCMRAMixin (A * B).
  Proof.
    split.
    - split; apply ucmra_unit_valid.
    - by split; rewrite /=left_id.
    - rewrite prod_pcore_Some'; split; apply (persistent _).
  Qed.
  Canonical Structure prodUR :=
    UCMRAT (A * B) prod_cofe_mixin prod_cmra_mixin prod_ucmra_mixin.

  Lemma pair_split (x : A) (y : B) : (x, y) ≡ (x, ∅) ⋅ (∅, y).
  Proof. by rewrite pair_op left_id right_id. Qed.
End prod_unit.

Arguments prodUR : clear implicits.

Instance prod_map_cmra_monotone {A A' B B' : cmraT} (f : A → A') (g : B → B') :
  CMRAMonotone f → CMRAMonotone g → CMRAMonotone (prod_map f g).
Proof.
  split; first apply _.
  - by intros n x [??]; split; simpl; apply validN_preserving.
  - intros x y; rewrite !prod_included=> -[??] /=.
    by split; apply cmra_monotone.
Qed.

Program Definition prodRF (F1 F2 : rFunctor) : rFunctor := {|
  rFunctor_car A B := prodR (rFunctor_car F1 A B) (rFunctor_car F2 A B);
  rFunctor_map A1 A2 B1 B2 fg :=
    prodC_map (rFunctor_map F1 fg) (rFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 A1 A2 B1 B2 n ???. by apply prodC_map_ne; apply rFunctor_ne.
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

Program Definition prodURF (F1 F2 : urFunctor) : urFunctor := {|
  urFunctor_car A B := prodUR (urFunctor_car F1 A B) (urFunctor_car F2 A B);
  urFunctor_map A1 A2 B1 B2 fg :=
    prodC_map (urFunctor_map F1 fg) (urFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 A1 A2 B1 B2 n ???. by apply prodC_map_ne; apply urFunctor_ne.
Qed.
Next Obligation. by intros F1 F2 A B [??]; rewrite /= !urFunctor_id. Qed.
Next Obligation.
  intros F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl.
  by rewrite !urFunctor_compose.
Qed.

Instance prodURF_contractive F1 F2 :
  urFunctorContractive F1 → urFunctorContractive F2 →
  urFunctorContractive (prodURF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply prodC_map_ne; apply urFunctor_contractive.
Qed.

(** ** CMRA for the option type *)
Section option.
  Context {A : cmraT}.
  Local Arguments core _ _ !_ /.
  Local Arguments pcore _ _ !_ /.

  Instance option_valid : Valid (option A) := λ mx,
    match mx with Some x => ✓ x | None => True end.
  Instance option_validN : ValidN (option A) := λ n mx,
    match mx with Some x => ✓{n} x | None => True end.
  Instance option_pcore : PCore (option A) := λ mx, Some (mx ≫= pcore).
  Arguments option_pcore !_ /.
  Instance option_op : Op (option A) := union_with (λ x y, Some (x ⋅ y)).

  Definition Some_valid a : ✓ Some a ↔ ✓ a := reflexivity _.
  Definition Some_op a b : Some (a ⋅ b) = Some a ⋅ Some b := eq_refl.
  Lemma Some_core `{CMRATotal A} a : Some (core a) = core (Some a).
  Proof. rewrite /core /=. by destruct (cmra_total a) as [? ->]. Qed.
  Lemma Some_op_opM x my : Some x ⋅ my = Some (x ⋅? my).
  Proof. by destruct my. Qed.

  Lemma option_included (mx my : option A) :
    mx ≼ my ↔ mx = None ∨ ∃ x y, mx = Some x ∧ my = Some y ∧ (x ≼ y ∨ x ≡ y).
  Proof.
    split.
    - intros [mz Hmz].
      destruct mx as [x|]; [right|by left].
      destruct my as [y|]; [exists x, y|destruct mz; inversion_clear Hmz].
      destruct mz as [z|]; inversion_clear Hmz; split_and?; auto;
        setoid_subst; eauto using cmra_included_l.
    - intros [->|(x&y&->&->&[[z Hz]|Hz])].
      + exists my. by destruct my.
      + exists (Some z); by constructor.
      + exists None; by constructor.
  Qed.

  Lemma option_cmra_mixin : CMRAMixin (option A).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - by intros n [x|]; destruct 1; constructor; cofe_subst.
    - destruct 1; by cofe_subst.
    - by destruct 1; rewrite /validN /option_validN //=; cofe_subst.
    - intros [x|]; [apply cmra_valid_validN|done].
    - intros n [x|]; unfold validN, option_validN; eauto using cmra_validN_S.
    - intros [x|] [y|] [z|]; constructor; rewrite ?assoc; auto.
    - intros [x|] [y|]; constructor; rewrite 1?comm; auto.
    - intros [x|]; simpl; auto.
      destruct (pcore x) as [cx|] eqn:?; constructor; eauto using cmra_pcore_l.
    - intros [x|]; simpl; auto.
      destruct (pcore x) as [cx|] eqn:?; simpl; eauto using cmra_pcore_idemp.
    - intros mx my; setoid_rewrite option_included.
      intros [->|(x&y&->&->&[?|?])]; simpl; eauto.
      + destruct (pcore x) as [cx|] eqn:?; eauto.
        destruct (cmra_pcore_mono x y cx) as (?&?&?); eauto 10.
      + destruct (pcore x) as [cx|] eqn:?; eauto.
        destruct (cmra_pcore_proper x y cx) as (?&?&?); eauto 10.
    - intros n [x|] [y|]; rewrite /validN /option_validN /=;
        eauto using cmra_validN_op_l.
    - intros n mx my1 my2.
      destruct mx as [x|], my1 as [y1|], my2 as [y2|]; intros Hx Hx';
        inversion_clear Hx'; auto.
      + destruct (cmra_extend n x y1 y2) as (z1&z2&?&?&?); auto.
        by exists (Some z1), (Some z2); repeat constructor.
      + by exists (Some x), None; repeat constructor.
      + by exists None, (Some x); repeat constructor.
      + exists None, None; repeat constructor.
  Qed.
  Canonical Structure optionR :=
    CMRAT (option A) option_cofe_mixin option_cmra_mixin.

  Global Instance option_cmra_discrete : CMRADiscrete A → CMRADiscrete optionR.
  Proof. split; [apply _|]. by intros [x|]; [apply (cmra_discrete_valid x)|]. Qed.

  Instance option_empty : Empty (option A) := None.
  Lemma option_ucmra_mixin : UCMRAMixin optionR.
  Proof. split. done. by intros []. done. Qed.
  Canonical Structure optionUR :=
    UCMRAT (option A) option_cofe_mixin option_cmra_mixin option_ucmra_mixin.

  (** Misc *)
  Global Instance Some_cmra_monotone : CMRAMonotone Some.
  Proof. split; [apply _|done|intros x y [z ->]; by exists (Some z)]. Qed.

  Lemma op_None mx my : mx ⋅ my = None ↔ mx = None ∧ my = None.
  Proof. destruct mx, my; naive_solver. Qed.
  Lemma op_is_Some mx my : is_Some (mx ⋅ my) ↔ is_Some mx ∨ is_Some my.
  Proof. rewrite -!not_eq_None_Some op_None. destruct mx, my; naive_solver. Qed.

  Global Instance Some_persistent (x : A) : Persistent x → Persistent (Some x).
  Proof. by constructor. Qed.
  Global Instance option_persistent (mx : option A) :
    (∀ x : A, Persistent x) → Persistent mx.
  Proof. intros. destruct mx; apply _. Qed.

  Lemma exclusiveN_Some_l n x `{!Exclusive x} my :
    ✓{n} (Some x ⋅ my) → my = None.
  Proof. destruct my. move=> /(exclusiveN_l _ x) []. done. Qed.
  Lemma exclusiveN_Some_r n x `{!Exclusive x} my :
    ✓{n} (my ⋅ Some x) → my = None.
  Proof. rewrite comm. by apply exclusiveN_Some_l. Qed.
End option.

Arguments optionR : clear implicits.
Arguments optionUR : clear implicits.

Instance option_fmap_cmra_monotone {A B : cmraT} (f: A → B) `{!CMRAMonotone f} :
  CMRAMonotone (fmap f : option A → option B).
Proof.
  split; first apply _.
  - intros n [x|] ?; rewrite /cmra_validN //=. by apply (validN_preserving f).
  - intros mx my; rewrite !option_included.
    intros [->|(x&y&->&->&[?|Hxy])]; simpl; eauto 10 using @cmra_monotone.
    right; exists (f x), (f y). by rewrite {4}Hxy; eauto.
Qed.
Program Definition optionURF (F : rFunctor) : urFunctor := {|
  urFunctor_car A B := optionUR (rFunctor_car F A B);
  urFunctor_map A1 A2 B1 B2 fg := optionC_map (rFunctor_map F fg)
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

Instance optionURF_contractive F :
  rFunctorContractive F → urFunctorContractive (optionURF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_contractive.
Qed.
