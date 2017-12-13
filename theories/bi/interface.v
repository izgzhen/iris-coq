From iris.algebra Require Export ofe.
Set Primitive Projections.

Reserved Notation "P ⊢ Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "'emp'".
Reserved Notation "'⌜' φ '⌝'" (at level 1, φ at level 200, format "⌜ φ ⌝").
Reserved Notation "P ∗ Q" (at level 80, right associativity).
Reserved Notation "P -∗ Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "▷ P" (at level 20, right associativity).

Section bi_mixin.
  Context {PROP : Type} `{Dist PROP, Equiv PROP} (prop_ofe_mixin : OfeMixin PROP).
  Context (bi_entails : PROP → PROP → Prop).
  Context (bi_emp : PROP).
  Context (bi_pure : Prop → PROP).
  Context (bi_and : PROP → PROP → PROP).
  Context (bi_or : PROP → PROP → PROP).
  Context (bi_impl : PROP → PROP → PROP).
  Context (bi_forall : ∀ A, (A → PROP) → PROP).
  Context (bi_exist : ∀ A, (A → PROP) → PROP).
  Context (bi_internal_eq : ∀ A : ofeT, A → A → PROP).
  Context (bi_sep : PROP → PROP → PROP).
  Context (bi_wand : PROP → PROP → PROP).
  Context (bi_plainly : PROP → PROP).
  Context (bi_persistently : PROP → PROP).
  Context (sbi_later : PROP → PROP).

  Local Infix "⊢" := bi_entails.
  Local Notation "'emp'" := bi_emp.
  Local Notation "'True'" := (bi_pure True).
  Local Notation "'False'" := (bi_pure False).
  Local Notation "'⌜' φ '⌝'" := (bi_pure φ%type%stdpp).
  Local Infix "∧" := bi_and.
  Local Infix "∨" := bi_or.
  Local Infix "→" := bi_impl.
  Local Notation "∀ x .. y , P" :=
    (bi_forall _ (λ x, .. (bi_forall _ (λ y, P)) ..)).
  Local Notation "∃ x .. y , P" :=
    (bi_exist _ (λ x, .. (bi_exist _ (λ y, P)) ..)).
  Local Notation "x ≡ y" := (bi_internal_eq _ x y).
  Local Infix "∗" := bi_sep.
  Local Infix "-∗" := bi_wand.
  Local Notation "▷ P" := (sbi_later P).

  Record BiMixin := {
    bi_mixin_entails_po : PreOrder bi_entails;
    bi_mixin_equiv_spec P Q : equiv P Q ↔ (P ⊢ Q) ∧ (Q ⊢ P);

    (* Non-expansiveness *)
    bi_mixin_pure_ne n : Proper (iff ==> dist n) bi_pure;
    bi_mixin_and_ne : NonExpansive2 bi_and;
    bi_mixin_or_ne : NonExpansive2 bi_or;
    bi_mixin_impl_ne : NonExpansive2 bi_impl;
    bi_mixin_forall_ne A n :
      Proper (pointwise_relation _ (dist n) ==> dist n) (bi_forall A);
    bi_mixin_exist_ne A n :
      Proper (pointwise_relation _ (dist n) ==> dist n) (bi_exist A);
    bi_mixin_sep_ne : NonExpansive2 bi_sep;
    bi_mixin_wand_ne : NonExpansive2 bi_wand;
    bi_mixin_plainly_ne : NonExpansive bi_plainly;
    bi_mixin_persistently_ne : NonExpansive bi_persistently;
    bi_mixin_internal_eq_ne (A : ofeT) : NonExpansive2 (bi_internal_eq A);

    (* Higher-order logic *)
    bi_mixin_pure_intro P (φ : Prop) : φ → P ⊢ ⌜ φ ⌝;
    bi_mixin_pure_elim' (φ : Prop) P : (φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P;
    bi_mixin_pure_forall_2 {A} (φ : A → Prop) : (∀ a, ⌜ φ a ⌝) ⊢ ⌜ ∀ a, φ a ⌝;

    bi_mixin_and_elim_l P Q : P ∧ Q ⊢ P;
    bi_mixin_and_elim_r P Q : P ∧ Q ⊢ Q;
    bi_mixin_and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R;

    bi_mixin_or_intro_l P Q : P ⊢ P ∨ Q;
    bi_mixin_or_intro_r P Q : Q ⊢ P ∨ Q;
    bi_mixin_or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R;

    bi_mixin_impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R;
    bi_mixin_impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R;

    bi_mixin_forall_intro {A} P (Ψ : A → PROP) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a;
    bi_mixin_forall_elim {A} {Ψ : A → PROP} a : (∀ a, Ψ a) ⊢ Ψ a;

    bi_mixin_exist_intro {A} {Ψ : A → PROP} a : Ψ a ⊢ ∃ a, Ψ a;
    bi_mixin_exist_elim {A} (Φ : A → PROP) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q;

    (* Equality *)
    bi_mixin_internal_eq_refl {A : ofeT} P (a : A) : P ⊢ a ≡ a;
    bi_mixin_internal_eq_rewrite {A : ofeT} a b (Ψ : A → PROP) :
      NonExpansive Ψ → a ≡ b ⊢ Ψ a → Ψ b;
    bi_mixin_fun_ext {A} {B : A → ofeT} (f g : ofe_fun B) : (∀ x, f x ≡ g x) ⊢ f ≡ g;
    bi_mixin_sig_eq {A : ofeT} (P : A → Prop) (x y : sig P) : `x ≡ `y ⊢ x ≡ y;
    bi_mixin_discrete_eq_1 {A : ofeT} (a b : A) : Discrete a → a ≡ b ⊢ ⌜a ≡ b⌝;

    (* BI connectives *)
    bi_mixin_sep_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q';
    bi_mixin_emp_sep_1 P : P ⊢ emp ∗ P;
    bi_mixin_emp_sep_2 P : emp ∗ P ⊢ P;
    bi_mixin_sep_comm' P Q : P ∗ Q ⊢ Q ∗ P;
    bi_mixin_sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R);
    bi_mixin_wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R;
    bi_mixin_wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R;

    (* Plainly *)
    bi_mixin_plainly_mono P Q : (P ⊢ Q) → bi_plainly P ⊢ bi_plainly Q;
    bi_mixin_plainly_elim_persistently P : bi_plainly P ⊢ bi_persistently P;
    bi_mixin_plainly_idemp_2 P : bi_plainly P ⊢ bi_plainly (bi_plainly P);

    bi_mixin_plainly_forall_2 {A} (Ψ : A → PROP) :
      (∀ a, bi_plainly (Ψ a)) ⊢ bi_plainly (∀ a, Ψ a);

    bi_mixin_prop_ext P Q : bi_plainly ((P → Q) ∧ (Q → P)) ⊢
      bi_internal_eq (OfeT PROP prop_ofe_mixin) P Q;

    (* The following two laws are very similar, and indeed they hold
       not just for □ and ■, but for any modality defined as
       `M P n x := ∀ y, R x y → P n y`. *)
    bi_mixin_persistently_impl_plainly P Q :
      (bi_plainly P → bi_persistently Q) ⊢ bi_persistently (bi_plainly P → Q);
    bi_mixin_plainly_impl_plainly P Q :
      (bi_plainly P → bi_plainly Q) ⊢ bi_plainly (bi_plainly P → Q);

    bi_mixin_plainly_emp_intro P : P ⊢ bi_plainly emp;
    bi_mixin_plainly_absorbing P Q : bi_plainly P ∗ Q ⊢ bi_plainly P;

    (* Persistently *)
    bi_mixin_persistently_mono P Q :
      (P ⊢ Q) → bi_persistently P ⊢ bi_persistently Q;
    bi_mixin_persistently_idemp_2 P :
      bi_persistently P ⊢ bi_persistently (bi_persistently P);
    bi_mixin_plainly_persistently_1 P :
      bi_plainly (bi_persistently P) ⊢ bi_plainly P;

    bi_mixin_persistently_forall_2 {A} (Ψ : A → PROP) :
      (∀ a, bi_persistently (Ψ a)) ⊢ bi_persistently (∀ a, Ψ a);
    bi_mixin_persistently_exist_1 {A} (Ψ : A → PROP) :
      bi_persistently (∃ a, Ψ a) ⊢ ∃ a, bi_persistently (Ψ a);

    bi_mixin_persistently_absorbing P Q :
      bi_persistently P ∗ Q ⊢ bi_persistently P;
    bi_mixin_persistently_and_sep_elim P Q :
      bi_persistently P ∧ Q ⊢ (emp ∧ P) ∗ Q;
  }.

  Record SbiMixin := {
    sbi_mixin_later_contractive : Contractive sbi_later;

    sbi_mixin_later_eq_1 {A : ofeT} (x y : A) : Next x ≡ Next y ⊢ ▷ (x ≡ y);
    sbi_mixin_later_eq_2 {A : ofeT} (x y : A) : ▷ (x ≡ y) ⊢ Next x ≡ Next y;

    sbi_mixin_later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q;
    sbi_mixin_löb P : (▷ P → P) ⊢ P;

    sbi_mixin_later_forall_2 {A} (Φ : A → PROP) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a;
    sbi_mixin_later_exist_false {A} (Φ : A → PROP) :
      (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a);
    sbi_mixin_later_sep_1 P Q : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q;
    sbi_mixin_later_sep_2 P Q : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q);
    sbi_mixin_later_plainly_1 P : ▷ bi_plainly P ⊢ bi_plainly (▷ P);
    sbi_mixin_later_plainly_2 P : bi_plainly (▷ P) ⊢ ▷ bi_plainly P;
    sbi_mixin_later_persistently_1 P :
      ▷ bi_persistently P ⊢ bi_persistently (▷ P);
    sbi_mixin_later_persistently_2 P :
      bi_persistently (▷ P) ⊢ ▷ bi_persistently P;

    sbi_mixin_later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P);
  }.
End bi_mixin.

Structure bi := Bi {
  bi_car :> Type;
  bi_dist : Dist bi_car;
  bi_equiv : Equiv bi_car;
  bi_entails : bi_car → bi_car → Prop;
  bi_emp : bi_car;
  bi_pure : Prop → bi_car;
  bi_and : bi_car → bi_car → bi_car;
  bi_or : bi_car → bi_car → bi_car;
  bi_impl : bi_car → bi_car → bi_car;
  bi_forall : ∀ A, (A → bi_car) → bi_car;
  bi_exist : ∀ A, (A → bi_car) → bi_car;
  bi_internal_eq : ∀ A : ofeT, A → A → bi_car;
  bi_sep : bi_car → bi_car → bi_car;
  bi_wand : bi_car → bi_car → bi_car;
  bi_plainly : bi_car → bi_car;
  bi_persistently : bi_car → bi_car;
  bi_ofe_mixin : OfeMixin bi_car;
  bi_bi_mixin : BiMixin bi_ofe_mixin bi_entails bi_emp bi_pure bi_and bi_or
                        bi_impl bi_forall bi_exist bi_internal_eq
                        bi_sep bi_wand bi_plainly bi_persistently;
}.

Coercion bi_ofeC (PROP : bi) : ofeT := OfeT PROP (bi_ofe_mixin PROP).
Canonical Structure bi_ofeC.

Instance: Params (@bi_entails) 1.
Instance: Params (@bi_emp) 1.
Instance: Params (@bi_pure) 1.
Instance: Params (@bi_and) 1.
Instance: Params (@bi_or) 1.
Instance: Params (@bi_impl) 1.
Instance: Params (@bi_forall) 2.
Instance: Params (@bi_exist) 2.
Instance: Params (@bi_internal_eq) 2.
Instance: Params (@bi_sep) 1.
Instance: Params (@bi_wand) 1.
Instance: Params (@bi_plainly) 1.
Instance: Params (@bi_persistently) 1.

Delimit Scope bi_scope with I.
Arguments bi_car : simpl never.
Arguments bi_dist : simpl never.
Arguments bi_equiv : simpl never.
Arguments bi_entails {PROP} _%I _%I : simpl never, rename.
Arguments bi_emp {PROP} : simpl never, rename.
Arguments bi_pure {PROP} _%stdpp : simpl never, rename.
Arguments bi_and {PROP} _%I _%I : simpl never, rename.
Arguments bi_or {PROP} _%I _%I : simpl never, rename.
Arguments bi_impl {PROP} _%I _%I : simpl never, rename.
Arguments bi_forall {PROP _} _%I : simpl never, rename.
Arguments bi_exist {PROP _} _%I : simpl never, rename.
Arguments bi_internal_eq {PROP _} _ _ : simpl never, rename.
Arguments bi_sep {PROP} _%I _%I : simpl never, rename.
Arguments bi_wand {PROP} _%I _%I : simpl never, rename.
Arguments bi_plainly {PROP} _%I : simpl never, rename.
Arguments bi_persistently {PROP} _%I : simpl never, rename.

Structure sbi := Sbi {
  sbi_car :> Type;
  sbi_dist : Dist sbi_car;
  sbi_equiv : Equiv sbi_car;
  sbi_entails : sbi_car → sbi_car → Prop;
  sbi_emp : sbi_car;
  sbi_pure : Prop → sbi_car;
  sbi_and : sbi_car → sbi_car → sbi_car;
  sbi_or : sbi_car → sbi_car → sbi_car;
  sbi_impl : sbi_car → sbi_car → sbi_car;
  sbi_forall : ∀ A, (A → sbi_car) → sbi_car;
  sbi_exist : ∀ A, (A → sbi_car) → sbi_car;
  sbi_internal_eq : ∀ A : ofeT, A → A → sbi_car;
  sbi_sep : sbi_car → sbi_car → sbi_car;
  sbi_wand : sbi_car → sbi_car → sbi_car;
  sbi_plainly : sbi_car → sbi_car;
  sbi_persistently : sbi_car → sbi_car;
  sbi_later : sbi_car → sbi_car;
  sbi_ofe_mixin : OfeMixin sbi_car;
  sbi_bi_mixin : BiMixin sbi_ofe_mixin sbi_entails sbi_emp sbi_pure sbi_and
                         sbi_or sbi_impl sbi_forall sbi_exist sbi_internal_eq
                         sbi_sep sbi_wand sbi_plainly sbi_persistently;
  sbi_sbi_mixin : SbiMixin sbi_entails sbi_pure sbi_or sbi_impl
                           sbi_forall sbi_exist sbi_internal_eq
                           sbi_sep sbi_plainly sbi_persistently sbi_later;
}.

Arguments sbi_car : simpl never.
Arguments sbi_entails {PROP} _%I _%I : simpl never, rename.
Arguments bi_emp {PROP} : simpl never, rename.
Arguments bi_pure {PROP} _%stdpp : simpl never, rename.
Arguments bi_and {PROP} _%I _%I : simpl never, rename.
Arguments bi_or {PROP} _%I _%I : simpl never, rename.
Arguments bi_impl {PROP} _%I _%I : simpl never, rename.
Arguments bi_forall {PROP _} _%I : simpl never, rename.
Arguments bi_exist {PROP _} _%I : simpl never, rename.
Arguments bi_internal_eq {PROP _} _ _ : simpl never, rename.
Arguments bi_sep {PROP} _%I _%I : simpl never, rename.
Arguments bi_wand {PROP} _%I _%I : simpl never, rename.
Arguments bi_plainly {PROP} _%I : simpl never, rename.
Arguments bi_persistently {PROP} _%I : simpl never, rename.

Coercion sbi_ofeC (PROP : sbi) : ofeT := OfeT PROP (sbi_ofe_mixin PROP).
Canonical Structure sbi_ofeC.
Coercion sbi_bi (PROP : sbi) : bi :=
  {| bi_ofe_mixin := sbi_ofe_mixin PROP; bi_bi_mixin := sbi_bi_mixin PROP |}.
Canonical Structure sbi_bi.

Arguments sbi_car : simpl never.
Arguments sbi_dist : simpl never.
Arguments sbi_equiv : simpl never.
Arguments sbi_entails {PROP} _%I _%I : simpl never, rename.
Arguments sbi_emp {PROP} : simpl never, rename.
Arguments sbi_pure {PROP} _%stdpp : simpl never, rename.
Arguments sbi_and {PROP} _%I _%I : simpl never, rename.
Arguments sbi_or {PROP} _%I _%I : simpl never, rename.
Arguments sbi_impl {PROP} _%I _%I : simpl never, rename.
Arguments sbi_forall {PROP _} _%I : simpl never, rename.
Arguments sbi_exist {PROP _} _%I : simpl never, rename.
Arguments sbi_internal_eq {PROP _} _ _ : simpl never, rename.
Arguments sbi_sep {PROP} _%I _%I : simpl never, rename.
Arguments sbi_wand {PROP} _%I _%I : simpl never, rename.
Arguments sbi_plainly {PROP} _%I : simpl never, rename.
Arguments sbi_persistently {PROP} _%I : simpl never, rename.
Arguments sbi_later {PROP} _%I : simpl never, rename.

Hint Extern 0 (bi_entails _ _) => reflexivity.
Instance bi_rewrite_relation (PROP : bi) : RewriteRelation (@bi_entails PROP).
Instance bi_inhabited {PROP : bi} : Inhabited PROP := populate (bi_pure True).

Notation "P ⊢ Q" := (bi_entails P%I Q%I) : stdpp_scope.
Notation "(⊢)" := bi_entails (only parsing) : stdpp_scope.

Notation "P ⊣⊢ Q" := (equiv (A:=bi_car _) P%I Q%I)
  (at level 95, no associativity) : stdpp_scope.
Notation "(⊣⊢)" := (equiv (A:=bi_car _)) (only parsing) : stdpp_scope.

Notation "P -∗ Q" := (P ⊢ Q) : stdpp_scope.

Notation "'emp'" := (bi_emp) : bi_scope.
Notation "'⌜' φ '⌝'" := (bi_pure φ%type%stdpp) : bi_scope.
Notation "'True'" := (bi_pure True) : bi_scope.
Notation "'False'" := (bi_pure False) : bi_scope.
Infix "∧" := bi_and : bi_scope.
Notation "(∧)" := bi_and (only parsing) : bi_scope.
Infix "∨" := bi_or : bi_scope.
Notation "(∨)" := bi_or (only parsing) : bi_scope.
Infix "→" := bi_impl : bi_scope.
Infix "∗" := bi_sep : bi_scope.
Notation "(∗)" := bi_sep (only parsing) : bi_scope.
Notation "P -∗ Q" := (bi_wand P Q) : bi_scope.
Notation "∀ x .. y , P" :=
  (bi_forall (λ x, .. (bi_forall (λ y, P)) ..)%I) : bi_scope.
Notation "∃ x .. y , P" :=
  (bi_exist (λ x, .. (bi_exist (λ y, P)) ..)%I) : bi_scope.

Infix "≡" := bi_internal_eq : bi_scope.
Notation "▷ P" := (sbi_later P) : bi_scope.

Coercion bi_valid {PROP : bi} (P : PROP) : Prop := emp ⊢ P.
Coercion sbi_valid {PROP : sbi} : PROP → Prop := bi_valid.

Arguments bi_valid {_} _%I : simpl never.
Typeclasses Opaque bi_valid.

Module bi.
Section bi_laws.
Context {PROP : bi}.
Implicit Types φ : Prop.
Implicit Types P Q R : PROP.
Implicit Types A : Type.

(* About the entailment *)
Global Instance entails_po : PreOrder (@bi_entails PROP).
Proof. eapply bi_mixin_entails_po, bi_bi_mixin. Qed.
Lemma equiv_spec P Q : P ≡ Q ↔ (P ⊢ Q) ∧ (Q ⊢ P).
Proof. eapply bi_mixin_equiv_spec, bi_bi_mixin. Qed.

(* Non-expansiveness *)
Global Instance pure_ne n : Proper (iff ==> dist n) (@bi_pure PROP).
Proof. eapply bi_mixin_pure_ne, bi_bi_mixin. Qed.
Global Instance and_ne : NonExpansive2 (@bi_and PROP).
Proof. eapply bi_mixin_and_ne, bi_bi_mixin. Qed.
Global Instance or_ne : NonExpansive2 (@bi_or PROP).
Proof. eapply bi_mixin_or_ne, bi_bi_mixin. Qed.
Global Instance impl_ne : NonExpansive2 (@bi_impl PROP).
Proof. eapply bi_mixin_impl_ne, bi_bi_mixin. Qed.
Global Instance forall_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_forall PROP A).
Proof. eapply bi_mixin_forall_ne, bi_bi_mixin. Qed.
Global Instance exist_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_exist PROP A).
Proof. eapply bi_mixin_exist_ne, bi_bi_mixin. Qed.
Global Instance sep_ne : NonExpansive2 (@bi_sep PROP).
Proof. eapply bi_mixin_sep_ne, bi_bi_mixin. Qed.
Global Instance wand_ne : NonExpansive2 (@bi_wand PROP).
Proof. eapply bi_mixin_wand_ne, bi_bi_mixin. Qed.
Global Instance plainly_ne : NonExpansive (@bi_plainly PROP).
Proof. eapply bi_mixin_plainly_ne, bi_bi_mixin. Qed.
Global Instance persistently_ne : NonExpansive (@bi_persistently PROP).
Proof. eapply bi_mixin_persistently_ne, bi_bi_mixin. Qed.

(* Higher-order logic *)
Lemma pure_intro P (φ : Prop) : φ → P ⊢ ⌜ φ ⌝.
Proof. eapply bi_mixin_pure_intro, bi_bi_mixin. Qed.
Lemma pure_elim' (φ : Prop) P : (φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P.
Proof. eapply bi_mixin_pure_elim', bi_bi_mixin. Qed.
Lemma pure_forall_2 {A} (φ : A → Prop) : (∀ a, ⌜ φ a ⌝ : PROP) ⊢ ⌜ ∀ a, φ a ⌝.
Proof. eapply bi_mixin_pure_forall_2, bi_bi_mixin. Qed.

Lemma and_elim_l P Q : P ∧ Q ⊢ P.
Proof. eapply bi_mixin_and_elim_l, bi_bi_mixin. Qed.
Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
Proof. eapply bi_mixin_and_elim_r, bi_bi_mixin. Qed.
Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
Proof. eapply bi_mixin_and_intro, bi_bi_mixin. Qed.

Lemma or_intro_l P Q : P ⊢ P ∨ Q.
Proof. eapply bi_mixin_or_intro_l, bi_bi_mixin. Qed.
Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
Proof. eapply bi_mixin_or_intro_r, bi_bi_mixin. Qed.
Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
Proof. eapply bi_mixin_or_elim, bi_bi_mixin. Qed.

Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
Proof. eapply bi_mixin_impl_intro_r, bi_bi_mixin. Qed.
Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
Proof. eapply bi_mixin_impl_elim_l', bi_bi_mixin. Qed.

Lemma forall_intro {A} P (Ψ : A → PROP) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
Proof. eapply bi_mixin_forall_intro, bi_bi_mixin. Qed.
Lemma forall_elim {A} {Ψ : A → PROP} a : (∀ a, Ψ a) ⊢ Ψ a.
Proof. eapply (bi_mixin_forall_elim  _ bi_entails), bi_bi_mixin. Qed.

Lemma exist_intro {A} {Ψ : A → PROP} a : Ψ a ⊢ ∃ a, Ψ a.
Proof. eapply bi_mixin_exist_intro, bi_bi_mixin. Qed.
Lemma exist_elim {A} (Φ : A → PROP) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
Proof. eapply bi_mixin_exist_elim, bi_bi_mixin. Qed.

(* Equality *)
Global Instance internal_eq_ne (A : ofeT) : NonExpansive2 (@bi_internal_eq PROP A).
Proof. eapply bi_mixin_internal_eq_ne, bi_bi_mixin. Qed.

Lemma internal_eq_refl {A : ofeT} P (a : A) : P ⊢ a ≡ a.
Proof. eapply bi_mixin_internal_eq_refl, bi_bi_mixin. Qed.
Lemma internal_eq_rewrite {A : ofeT} a b (Ψ : A → PROP) :
  NonExpansive Ψ → a ≡ b ⊢ Ψ a → Ψ b.
Proof. eapply bi_mixin_internal_eq_rewrite, bi_bi_mixin. Qed.

Lemma fun_ext {A} {B : A → ofeT} (f g : ofe_fun B) : (∀ x, f x ≡ g x) ⊢ (f ≡ g : PROP).
Proof. eapply bi_mixin_fun_ext, bi_bi_mixin. Qed.
Lemma sig_eq {A : ofeT} (P : A → Prop) (x y : sig P) : `x ≡ `y ⊢ (x ≡ y : PROP).
Proof. eapply bi_mixin_sig_eq, bi_bi_mixin. Qed.
Lemma discrete_eq_1 {A : ofeT} (a b : A) :
  Discrete a → a ≡ b ⊢ (⌜a ≡ b⌝ : PROP).
Proof. eapply bi_mixin_discrete_eq_1, bi_bi_mixin. Qed.

(* BI connectives *)
Lemma sep_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
Proof. eapply bi_mixin_sep_mono, bi_bi_mixin. Qed.
Lemma emp_sep_1 P : P ⊢ emp ∗ P.
Proof. eapply bi_mixin_emp_sep_1, bi_bi_mixin. Qed.
Lemma emp_sep_2 P : emp ∗ P ⊢ P.
Proof. eapply bi_mixin_emp_sep_2, bi_bi_mixin. Qed.
Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
Proof. eapply (bi_mixin_sep_comm' _ bi_entails), bi_bi_mixin. Qed.
Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
Proof. eapply bi_mixin_sep_assoc', bi_bi_mixin. Qed.
Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
Proof. eapply bi_mixin_wand_intro_r, bi_bi_mixin. Qed.
Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
Proof. eapply bi_mixin_wand_elim_l', bi_bi_mixin. Qed.

(* Plainly *)
Lemma plainly_mono P Q : (P ⊢ Q) → bi_plainly P ⊢ bi_plainly Q.
Proof. eapply bi_mixin_plainly_mono, bi_bi_mixin. Qed.
Lemma plainly_elim_persistently P : bi_plainly P ⊢ bi_persistently P.
Proof. eapply bi_mixin_plainly_elim_persistently, bi_bi_mixin. Qed.
Lemma plainly_idemp_2 P : bi_plainly P ⊢ bi_plainly (bi_plainly P).
Proof. eapply bi_mixin_plainly_idemp_2, bi_bi_mixin. Qed.
Lemma plainly_forall_2 {A} (Ψ : A → PROP) :
  (∀ a, bi_plainly (Ψ a)) ⊢ bi_plainly (∀ a, Ψ a).
Proof. eapply bi_mixin_plainly_forall_2, bi_bi_mixin. Qed.
Lemma prop_ext P Q : bi_plainly ((P → Q) ∧ (Q → P)) ⊢ P ≡ Q.
Proof. eapply (bi_mixin_prop_ext _ bi_entails), bi_bi_mixin. Qed.
Lemma persistently_impl_plainly P Q :
  (bi_plainly P → bi_persistently Q) ⊢ bi_persistently (bi_plainly P → Q).
Proof. eapply bi_mixin_persistently_impl_plainly, bi_bi_mixin. Qed.
Lemma plainly_impl_plainly P Q :
  (bi_plainly P → bi_plainly Q) ⊢ bi_plainly (bi_plainly P → Q).
Proof. eapply bi_mixin_plainly_impl_plainly, bi_bi_mixin. Qed.
Lemma plainly_absorbing P Q : bi_plainly P ∗ Q ⊢ bi_plainly P.
Proof. eapply (bi_mixin_plainly_absorbing _ bi_entails), bi_bi_mixin. Qed.
Lemma plainly_emp_intro P : P ⊢ bi_plainly emp.
Proof. eapply bi_mixin_plainly_emp_intro, bi_bi_mixin. Qed.

(* Persistently *)
Lemma persistently_mono P Q : (P ⊢ Q) → bi_persistently P ⊢ bi_persistently Q.
Proof. eapply bi_mixin_persistently_mono, bi_bi_mixin. Qed.
Lemma persistently_idemp_2 P :
  bi_persistently P ⊢ bi_persistently (bi_persistently P).
Proof. eapply bi_mixin_persistently_idemp_2, bi_bi_mixin. Qed.
Lemma plainly_persistently_1 P :
  bi_plainly (bi_persistently P) ⊢ bi_plainly P.
Proof. eapply (bi_mixin_plainly_persistently_1 _ bi_entails), bi_bi_mixin. Qed.

Lemma persistently_forall_2 {A} (Ψ : A → PROP) :
  (∀ a, bi_persistently (Ψ a)) ⊢ bi_persistently (∀ a, Ψ a).
Proof. eapply bi_mixin_persistently_forall_2, bi_bi_mixin. Qed.
Lemma persistently_exist_1 {A} (Ψ : A → PROP) :
  bi_persistently (∃ a, Ψ a) ⊢ ∃ a, bi_persistently (Ψ a).
Proof. eapply bi_mixin_persistently_exist_1, bi_bi_mixin. Qed.

Lemma persistently_absorbing P Q : bi_persistently P ∗ Q ⊢ bi_persistently P.
Proof. eapply (bi_mixin_persistently_absorbing _ bi_entails), bi_bi_mixin. Qed.
Lemma persistently_and_sep_elim P Q : bi_persistently P ∧ Q ⊢ (emp ∧ P) ∗ Q.
Proof. eapply bi_mixin_persistently_and_sep_elim, bi_bi_mixin. Qed.
End bi_laws.

Section sbi_laws.
Context {PROP : sbi}.
Implicit Types φ : Prop.
Implicit Types P Q R : PROP.

Global Instance later_contractive : Contractive (@sbi_later PROP).
Proof. eapply sbi_mixin_later_contractive, sbi_sbi_mixin. Qed.

Lemma later_eq_1 {A : ofeT} (x y : A) : Next x ≡ Next y ⊢ ▷ (x ≡ y : PROP).
Proof. eapply sbi_mixin_later_eq_1, sbi_sbi_mixin. Qed.
Lemma later_eq_2 {A : ofeT} (x y : A) : ▷ (x ≡ y) ⊢ (Next x ≡ Next y : PROP).
Proof. eapply sbi_mixin_later_eq_2, sbi_sbi_mixin. Qed.

Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
Proof. eapply sbi_mixin_later_mono, sbi_sbi_mixin. Qed.
Lemma löb P : (▷ P → P) ⊢ P.
Proof. eapply sbi_mixin_löb, sbi_sbi_mixin. Qed.

Lemma later_forall_2 {A} (Φ : A → PROP) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
Proof. eapply sbi_mixin_later_forall_2, sbi_sbi_mixin. Qed.
Lemma later_exist_false {A} (Φ : A → PROP) :
  (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
Proof. eapply sbi_mixin_later_exist_false, sbi_sbi_mixin. Qed.
Lemma later_sep_1 P Q : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q.
Proof. eapply sbi_mixin_later_sep_1, sbi_sbi_mixin. Qed.
Lemma later_sep_2 P Q : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q).
Proof. eapply sbi_mixin_later_sep_2, sbi_sbi_mixin. Qed.
Lemma later_plainly_1 P : ▷ bi_plainly P ⊢ bi_plainly (▷ P).
Proof. eapply (sbi_mixin_later_plainly_1 bi_entails), sbi_sbi_mixin. Qed.
Lemma later_plainly_2 P : bi_plainly (▷ P) ⊢ ▷ bi_plainly P.
Proof. eapply (sbi_mixin_later_plainly_2 bi_entails), sbi_sbi_mixin. Qed.
Lemma later_persistently_1 P : ▷ bi_persistently P ⊢ bi_persistently (▷ P).
Proof. eapply (sbi_mixin_later_persistently_1 bi_entails), sbi_sbi_mixin. Qed.
Lemma later_persistently_2 P : bi_persistently (▷ P) ⊢ ▷ bi_persistently P.
Proof. eapply (sbi_mixin_later_persistently_2 bi_entails), sbi_sbi_mixin. Qed.

Lemma later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
Proof. eapply sbi_mixin_later_false_em, sbi_sbi_mixin. Qed.
End sbi_laws.

End bi.

(* Typically, embeddings are used to *define* the destination BI.
   Hence we cannot ask it to verify the properties of embeddings. *)
Class BiEmbed (A B : Type) := bi_embed : A → B.
Arguments bi_embed {_ _ _} _%I : simpl never.
Notation "⎡ P ⎤" := (bi_embed P) : bi_scope.
Instance: Params (@bi_embed) 3.
Typeclasses Opaque bi_embed.

Class BiEmbedding (PROP1 PROP2 : bi) `{BiEmbed PROP1 PROP2} := {
  bi_embed_ne :> NonExpansive bi_embed;
  bi_embed_mono :> Proper ((⊢) ==> (⊢)) bi_embed;
  bi_embed_entails_inj :> Inj (⊢) (⊢) bi_embed;
  bi_embed_emp : ⎡emp⎤ ⊣⊢ emp;
  bi_embed_impl_2 P Q : (⎡P⎤ → ⎡Q⎤) ⊢ ⎡P → Q⎤;
  bi_embed_forall_2 A (Φ : A → PROP1) : (∀ x, ⎡Φ x⎤) ⊢ ⎡∀ x, Φ x⎤;
  bi_embed_exist_1 A (Φ : A → PROP1) : ⎡∃ x, Φ x⎤ ⊢ ∃ x, ⎡Φ x⎤;
  bi_embed_internal_eq_1 (A : ofeT) (x y : A) : ⎡x ≡ y⎤ ⊢ x ≡ y;
  bi_embed_sep P Q : ⎡P ∗ Q⎤ ⊣⊢ ⎡P⎤ ∗ ⎡Q⎤;
  bi_embed_wand_2 P Q : (⎡P⎤ -∗ ⎡Q⎤) ⊢ ⎡P -∗ Q⎤;
  bi_embed_plainly P : ⎡bi_plainly P⎤ ⊣⊢ bi_plainly ⎡P⎤;
  bi_embed_persistently P : ⎡bi_persistently P⎤ ⊣⊢ bi_persistently ⎡P⎤
}.

Class SbiEmbedding (PROP1 PROP2 : sbi) `{BiEmbed PROP1 PROP2} := {
  sbi_embed_bi_embed :> BiEmbedding PROP1 PROP2;
  sbi_embed_later P : ⎡▷ P⎤ ⊣⊢ ▷ ⎡P⎤
}.
