From iris.algebra Require Export cmra updates.
From iris.bi Require Export derived_connectives.
From stdpp Require Import finite.
Set Default Proof Using "Type".
Local Hint Extern 1 (_ ≼ _) => etrans; [eassumption|].
Local Hint Extern 1 (_ ≼ _) => etrans; [|eassumption].
Local Hint Extern 10 (_ ≤ _) => omega.

(** The basic definition of the uPred type, its metric and functor laws.
    You probably do not want to import this file. Instead, import
    base_logic.base_logic; that will also give you all the primitive
    and many derived laws for the logic. *)

Record uPred (M : ucmraT) : Type := IProp {
  uPred_holds :> nat → M → Prop;

  (* [uPred_mono] is used to prove non-expansiveness (guaranteed by
     [uPred_ne]). Therefore, it is important that we do not restrict
     it to only valid elements. *)
  uPred_mono n x1 x2 : uPred_holds n x1 → x1 ≼{n} x2 → uPred_holds n x2;

  (* We have to restrict this to hold only for valid elements,
     otherwise this condition is no longer limit preserving, and uPred
     does no longer form a COFE (i.e., [uPred_compl] breaks). This is
     because the distance and equivalence on this cofe ignores the
     truth value on invalid elements. This, in turn, is required by
     the fact that entailment has to ignore invalid elements, which is
     itself essential for proving [ownM_valid].

     We could, actually, remove this restriction and make this
     condition apply even to invalid elements: we have proved that
     uPred is isomorphic to a sub-COFE of the COFE of predicates that
     are monotonous both with respect to the step index and with
     respect to x. However, that would essentially require changing
     (by making it more complicated) the model of many connectives of
     the logic, which we don't want.
     This sub-COFE is the sub-COFE of monotonous sProp predicates P
     such that the following sProp assertion is valid:
          ∀ x, (V(x) → P(x)) → P(x)
     Where V is the validity predicate.

     Another way of saying that this is equivalent to this definition of
     uPred is to notice that our definition of uPred is equivalent to
     quotienting the COFE of monotonous sProp predicates with the
     following (sProp) equivalence relation:
       P1 ≡ P2  :=  ∀ x, V(x) → (P1(x) ↔ P2(x))
     whose equivalence classes appear to all have one only canonical
     representative such that ∀ x, (V(x) → P(x)) → P(x).
 *)
  uPred_closed n1 n2 x : uPred_holds n1 x → n2 ≤ n1 → ✓{n2} x → uPred_holds n2 x
}.
Arguments uPred_holds {_} _ _ _ : simpl never.
Add Printing Constructor uPred.
Instance: Params (@uPred_holds) 3.

Bind Scope bi_scope with uPred.
Arguments uPred_holds {_} _%I _ _.

Section cofe.
  Context {M : ucmraT}.

  Inductive uPred_equiv' (P Q : uPred M) : Prop :=
    { uPred_in_equiv : ∀ n x, ✓{n} x → P n x ↔ Q n x }.
  Instance uPred_equiv : Equiv (uPred M) := uPred_equiv'.
  Inductive uPred_dist' (n : nat) (P Q : uPred M) : Prop :=
    { uPred_in_dist : ∀ n' x, n' ≤ n → ✓{n'} x → P n' x ↔ Q n' x }.
  Instance uPred_dist : Dist (uPred M) := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin (uPred M).
  Proof.
    split.
    - intros P Q; split.
      + by intros HPQ n; split=> i x ??; apply HPQ.
      + intros HPQ; split=> n x ?; apply HPQ with n; auto.
    - intros n; split.
      + by intros P; split=> x i.
      + by intros P Q HPQ; split=> x i ??; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i x ??.
        by trans (Q i x);[apply HP|apply HQ].
    - intros n P Q HPQ; split=> i x ??; apply HPQ; auto.
  Qed.
  Canonical Structure uPredC : ofeT := OfeT (uPred M) uPred_ofe_mixin.

  Program Definition uPred_compl : Compl uPredC := λ c,
    {| uPred_holds n x := c n n x |}.
  Next Obligation. naive_solver eauto using uPred_mono. Qed.
  Next Obligation.
    intros c n1 n2 x ???; simpl in *.
    apply (chain_cauchy c n2 n1); eauto using uPred_closed.
  Qed.
  Global Program Instance uPred_cofe : Cofe uPredC := {| compl := uPred_compl |}.
  Next Obligation.
    intros n c; split=>i x ??; symmetry; apply (chain_cauchy c i n); auto.
  Qed.
End cofe.
Arguments uPredC : clear implicits.

Instance uPred_ne {M} (P : uPred M) n : Proper (dist n ==> iff) (P n).
Proof.
  intros x1 x2 Hx; split=> ?; eapply uPred_mono; eauto; by rewrite Hx.
Qed.
Instance uPred_proper {M} (P : uPred M) n : Proper ((≡) ==> iff) (P n).
Proof. by intros x1 x2 Hx; apply uPred_ne, equiv_dist. Qed.

Lemma uPred_holds_ne {M} (P Q : uPred M) n1 n2 x :
  P ≡{n2}≡ Q → n2 ≤ n1 → ✓{n2} x → Q n1 x → P n2 x.
Proof.
  intros [Hne] ???. eapply Hne; try done.
  eapply uPred_closed; eauto using cmra_validN_le.
Qed.

(** functor *)
Program Definition uPred_map {M1 M2 : ucmraT} (f : M2 -n> M1)
  `{!CmraMorphism f} (P : uPred M1) :
  uPred M2 := {| uPred_holds n x := P n (f x) |}.
Next Obligation. naive_solver eauto using uPred_mono, cmra_morphism_monotoneN. Qed.
Next Obligation. naive_solver eauto using uPred_closed, cmra_morphism_validN. Qed.

Instance uPred_map_ne {M1 M2 : ucmraT} (f : M2 -n> M1)
  `{!CmraMorphism f} n : Proper (dist n ==> dist n) (uPred_map f).
Proof.
  intros x1 x2 Hx; split=> n' y ??.
  split; apply Hx; auto using cmra_morphism_validN.
Qed.
Lemma uPred_map_id {M : ucmraT} (P : uPred M): uPred_map cid P ≡ P.
Proof. by split=> n x ?. Qed.
Lemma uPred_map_compose {M1 M2 M3 : ucmraT} (f : M1 -n> M2) (g : M2 -n> M3)
    `{!CmraMorphism f, !CmraMorphism g} (P : uPred M3):
  uPred_map (g ◎ f) P ≡ uPred_map f (uPred_map g P).
Proof. by split=> n x Hx. Qed.
Lemma uPred_map_ext {M1 M2 : ucmraT} (f g : M1 -n> M2)
      `{!CmraMorphism f} `{!CmraMorphism g}:
  (∀ x, f x ≡ g x) → ∀ x, uPred_map f x ≡ uPred_map g x.
Proof. intros Hf P; split=> n x Hx /=; by rewrite /uPred_holds /= Hf. Qed.
Definition uPredC_map {M1 M2 : ucmraT} (f : M2 -n> M1) `{!CmraMorphism f} :
  uPredC M1 -n> uPredC M2 := CofeMor (uPred_map f : uPredC M1 → uPredC M2).
Lemma uPredC_map_ne {M1 M2 : ucmraT} (f g : M2 -n> M1)
    `{!CmraMorphism f, !CmraMorphism g} n :
  f ≡{n}≡ g → uPredC_map f ≡{n}≡ uPredC_map g.
Proof.
  by intros Hfg P; split=> n' y ??;
    rewrite /uPred_holds /= (dist_le _ _ _ _(Hfg y)); last lia.
Qed.

Program Definition uPredCF (F : urFunctor) : cFunctor := {|
  cFunctor_car A B := uPredC (urFunctor_car F B A);
  cFunctor_map A1 A2 B1 B2 fg := uPredC_map (urFunctor_map F (fg.2, fg.1))
|}.
Next Obligation.
  intros F A1 A2 B1 B2 n P Q HPQ.
  apply uPredC_map_ne, urFunctor_ne; split; by apply HPQ.
Qed.
Next Obligation.
  intros F A B P; simpl. rewrite -{2}(uPred_map_id P).
  apply uPred_map_ext=>y. by rewrite urFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' P; simpl. rewrite -uPred_map_compose.
  apply uPred_map_ext=>y; apply urFunctor_compose.
Qed.

Instance uPredCF_contractive F :
  urFunctorContractive F → cFunctorContractive (uPredCF F).
Proof.
  intros ? A1 A2 B1 B2 n P Q HPQ. apply uPredC_map_ne, urFunctor_contractive.
  destruct n; split; by apply HPQ.
Qed.

(** logical entailement *)
Inductive uPred_entails {M} (P Q : uPred M) : Prop :=
  { uPred_in_entails : ∀ n x, ✓{n} x → P n x → Q n x }.
Hint Resolve uPred_mono uPred_closed : uPred_def.

(** logical connectives *)
Program Definition uPred_pure_def {M} (φ : Prop) : uPred M :=
  {| uPred_holds n x := φ |}.
Solve Obligations with done.
Definition uPred_pure_aux : seal (@uPred_pure_def). by eexists. Qed.
Definition uPred_pure {M} := unseal uPred_pure_aux M.
Definition uPred_pure_eq :
  @uPred_pure = @uPred_pure_def := seal_eq uPred_pure_aux.

Definition uPred_emp {M} : uPred M := uPred_pure True.

Program Definition uPred_and_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_and_aux : seal (@uPred_and_def). by eexists. Qed.
Definition uPred_and {M} := unseal uPred_and_aux M.
Definition uPred_and_eq: @uPred_and = @uPred_and_def := seal_eq uPred_and_aux.

Program Definition uPred_or_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_or_aux : seal (@uPred_or_def). by eexists. Qed.
Definition uPred_or {M} := unseal uPred_or_aux M.
Definition uPred_or_eq: @uPred_or = @uPred_or_def := seal_eq uPred_or_aux.

Program Definition uPred_impl_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       x ≼ x' → n' ≤ n → ✓{n'} x' → P n' x' → Q n' x' |}.
Next Obligation.
  intros M P Q n1 x1 x1' HPQ [x2 Hx1'] n2 x3 [x4 Hx3] ?; simpl in *.
  rewrite Hx3 (dist_le _ _ _ _ Hx1'); auto. intros ??.
  eapply HPQ; auto. exists (x2 ⋅ x4); by rewrite assoc.
Qed.
Next Obligation. intros M P Q [|n1] [|n2] x; auto with lia. Qed.
Definition uPred_impl_aux : seal (@uPred_impl_def). by eexists. Qed.
Definition uPred_impl {M} := unseal uPred_impl_aux M.
Definition uPred_impl_eq :
  @uPred_impl = @uPred_impl_def := seal_eq uPred_impl_aux.

Program Definition uPred_forall_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∀ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_forall_aux : seal (@uPred_forall_def). by eexists. Qed.
Definition uPred_forall {M A} := unseal uPred_forall_aux M A.
Definition uPred_forall_eq :
  @uPred_forall = @uPred_forall_def := seal_eq uPred_forall_aux.

Program Definition uPred_exist_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∃ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_exist_aux : seal (@uPred_exist_def). by eexists. Qed.
Definition uPred_exist {M A} := unseal uPred_exist_aux M A.
Definition uPred_exist_eq: @uPred_exist = @uPred_exist_def := seal_eq uPred_exist_aux.

Program Definition uPred_internal_eq_def {M} {A : ofeT} (a1 a2 : A) : uPred M :=
  {| uPred_holds n x := a1 ≡{n}≡ a2 |}.
Solve Obligations with naive_solver eauto 2 using (dist_le (A:=A)).
Definition uPred_internal_eq_aux : seal (@uPred_internal_eq_def). by eexists. Qed.
Definition uPred_internal_eq {M A} := unseal uPred_internal_eq_aux M A.
Definition uPred_internal_eq_eq:
  @uPred_internal_eq = @uPred_internal_eq_def := seal_eq uPred_internal_eq_aux.

Program Definition uPred_sep_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∃ x1 x2, x ≡{n}≡ x1 ⋅ x2 ∧ P n x1 ∧ Q n x2 |}.
Next Obligation.
  intros M P Q n x y (x1&x2&Hx&?&?) [z Hy].
  exists x1, (x2 ⋅ z); split_and?; eauto using uPred_mono, cmra_includedN_l.
  by rewrite Hy Hx assoc.
Qed.
Next Obligation.
  intros M P Q n1 n2 x (x1&x2&Hx&?&?) ?; rewrite {1}(dist_le _ _ _ _ Hx) // =>?.
  exists x1, x2; ofe_subst; split_and!;
    eauto using dist_le, uPred_closed, cmra_validN_op_l, cmra_validN_op_r.
Qed.
Definition uPred_sep_aux : seal (@uPred_sep_def). by eexists. Qed.
Definition uPred_sep {M} := unseal uPred_sep_aux M.
Definition uPred_sep_eq: @uPred_sep = @uPred_sep_def := seal_eq uPred_sep_aux.

Program Definition uPred_wand_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       n' ≤ n → ✓{n'} (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Next Obligation.
  intros M P Q n x1 x1' HPQ ? n3 x3 ???; simpl in *.
  apply uPred_mono with (x1 ⋅ x3);
    eauto using cmra_validN_includedN, cmra_monoN_r, cmra_includedN_le.
Qed.
Next Obligation. naive_solver. Qed.
Definition uPred_wand_aux : seal (@uPred_wand_def). by eexists. Qed.
Definition uPred_wand {M} := unseal uPred_wand_aux M.
Definition uPred_wand_eq :
  @uPred_wand = @uPred_wand_def := seal_eq uPred_wand_aux.

(* Equivalently, this could be `∀ y, P n y`.  That's closer to the intuition
   of "embedding the step-indexed logic in Iris", but the two are equivalent
   because Iris is afine.  The following is easier to work with. *)
Program Definition uPred_plainly_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n ε |}.
Solve Obligations with naive_solver eauto using uPred_closed, ucmra_unit_validN.
Definition uPred_plainly_aux : seal (@uPred_plainly_def). by eexists. Qed.
Definition uPred_plainly {M} := unseal uPred_plainly_aux M.
Definition uPred_plainly_eq :
  @uPred_plainly = @uPred_plainly_def := seal_eq uPred_plainly_aux.

Program Definition uPred_persistently_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n (core x) |}.
Next Obligation.
  intros M; naive_solver eauto using uPred_mono, @cmra_core_monoN.
Qed.
Next Obligation. naive_solver eauto using uPred_closed, @cmra_core_validN. Qed.
Definition uPred_persistently_aux : seal (@uPred_persistently_def). by eexists. Qed.
Definition uPred_persistently {M} := unseal uPred_persistently_aux M.
Definition uPred_persistently_eq :
  @uPred_persistently = @uPred_persistently_def := seal_eq uPred_persistently_aux.

Program Definition uPred_later_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := match n return _ with 0 => True | S n' => P n' x end |}.
Next Obligation.
  intros M P [|n] x1 x2; eauto using uPred_mono, cmra_includedN_S.
Qed.
Next Obligation.
  intros M P [|n1] [|n2] x; eauto using uPred_closed, cmra_validN_S with lia.
Qed.
Definition uPred_later_aux : seal (@uPred_later_def). by eexists. Qed.
Definition uPred_later {M} := unseal uPred_later_aux M.
Definition uPred_later_eq :
  @uPred_later = @uPred_later_def := seal_eq uPred_later_aux.

Program Definition uPred_ownM_def {M : ucmraT} (a : M) : uPred M :=
  {| uPred_holds n x := a ≼{n} x |}.
Next Obligation.
  intros M a n x1 x [a' Hx1] [x2 ->].
  exists (a' ⋅ x2). by rewrite (assoc op) Hx1.
Qed.
Next Obligation. naive_solver eauto using cmra_includedN_le. Qed.
Definition uPred_ownM_aux : seal (@uPred_ownM_def). by eexists. Qed.
Definition uPred_ownM {M} := unseal uPred_ownM_aux M.
Definition uPred_ownM_eq :
  @uPred_ownM = @uPred_ownM_def := seal_eq uPred_ownM_aux.

Program Definition uPred_cmra_valid_def {M} {A : cmraT} (a : A) : uPred M :=
  {| uPred_holds n x := ✓{n} a |}.
Solve Obligations with naive_solver eauto 2 using cmra_validN_le.
Definition uPred_cmra_valid_aux : seal (@uPred_cmra_valid_def). by eexists. Qed.
Definition uPred_cmra_valid {M A} := unseal uPred_cmra_valid_aux M A.
Definition uPred_cmra_valid_eq :
  @uPred_cmra_valid = @uPred_cmra_valid_def := seal_eq uPred_cmra_valid_aux.

Class BUpd (A : Type) : Type := bupd : A → A.

Program Definition uPred_bupd_def {M} (Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ k yf,
      k ≤ n → ✓{k} (x ⋅ yf) → ∃ x', ✓{k} (x' ⋅ yf) ∧ Q k x' |}.
Next Obligation.
  intros M Q n x1 x2 HQ [x3 Hx] k yf Hk.
  rewrite (dist_le _ _ _ _ Hx); last lia. intros Hxy.
  destruct (HQ k (x3 ⋅ yf)) as (x'&?&?); [auto|by rewrite assoc|].
  exists (x' ⋅ x3); split; first by rewrite -assoc.
  apply uPred_mono with x'; eauto using cmra_includedN_l.
Qed.
Next Obligation. naive_solver. Qed.
Definition uPred_bupd_aux {M} : seal (@uPred_bupd_def M). by eexists. Qed.
Instance uPred_bupd {M} : BUpd (uPred M) := unseal uPred_bupd_aux.
Definition uPred_bupd_eq {M} :
  @bupd _ uPred_bupd = @uPred_bupd_def M := seal_eq uPred_bupd_aux.

Module uPred_unseal.
Definition unseal_eqs :=
  (uPred_pure_eq, uPred_and_eq, uPred_or_eq, uPred_impl_eq, uPred_forall_eq,
  uPred_exist_eq, uPred_internal_eq_eq, uPred_sep_eq, uPred_wand_eq,
  uPred_plainly_eq, uPred_persistently_eq, uPred_later_eq, uPred_ownM_eq,
  uPred_cmra_valid_eq, @uPred_bupd_eq).
Ltac unseal := (* Coq unfold is used to circumvent bug #5699 in rewrite /foo *)
  unfold bi_emp; simpl;
  unfold uPred_emp, bi_pure, bi_and, bi_or, bi_impl, bi_forall, bi_exist,
  bi_internal_eq, bi_sep, bi_wand, bi_plainly, bi_persistently, sbi_later; simpl;
  unfold sbi_emp, sbi_pure, sbi_and, sbi_or, sbi_impl, sbi_forall, sbi_exist,
  sbi_internal_eq, sbi_sep, sbi_wand, sbi_plainly, sbi_persistently; simpl;
  rewrite !unseal_eqs /=.
End uPred_unseal.
Import uPred_unseal.

Local Arguments uPred_holds {_} !_ _ _ /.

Lemma uPred_bi_mixin (M : ucmraT) : BIMixin (ofe_mixin_of (uPred M))
  uPred_entails uPred_emp uPred_pure uPred_and uPred_or uPred_impl
                (@uPred_forall M) (@uPred_exist M) (@uPred_internal_eq M)
                uPred_sep uPred_wand uPred_plainly uPred_persistently.
Proof.
  split.
  - (* PreOrder uPred_entails *)
    split.
    + by intros P; split=> x i.
    + by intros P Q Q' HP HQ; split=> x i ??; apply HQ, HP.
  - (* (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P) *)
    intros P Q. split.
    + intros HPQ; split; split=> x i; apply HPQ.
    + intros [HPQ HQP]; split=> x n; by split; [apply HPQ|apply HQP].
  - (* Proper (iff ==> dist n) (@uPred_pure M) *)
    intros φ1 φ2 Hφ. by unseal; split=> -[|n] ?; try apply Hφ.
  - (* NonExpansive2 uPred_and *)
    intros n P P' HP Q Q' HQ; unseal; split=> x n' ??.
    split; (intros [??]; split; [by apply HP|by apply HQ]).
  - (* NonExpansive2 uPred_or *)
    intros n P P' HP Q Q' HQ; split=> x n' ??.
    unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
  - (* NonExpansive2 uPred_impl *)
    intros n P P' HP Q Q' HQ; split=> x n' ??.
    unseal; split; intros HPQ x' n'' ????; apply HQ, HPQ, HP; auto.
  - (* Proper (pointwise_relation A (dist n) ==> dist n) uPred_forall *)
    by intros A n Ψ1 Ψ2 HΨ; unseal; split=> n' x; split; intros HP a; apply HΨ.
  - (* Proper (pointwise_relation A (dist n) ==> dist n) uPred_exist *)
    intros A n Ψ1 Ψ2 HΨ.
    unseal; split=> n' x ??; split; intros [a ?]; exists a; by apply HΨ.
  - (* NonExpansive2 uPred_sep *)
    intros n P P' HP Q Q' HQ; split=> n' x ??.
    unseal; split; intros (x1&x2&?&?&?); ofe_subst x;
      exists x1, x2; split_and!; try (apply HP || apply HQ);
      eauto using cmra_validN_op_l, cmra_validN_op_r.
  - (* NonExpansive2 uPred_wand *)
    intros n P P' HP Q Q' HQ; split=> n' x ??.
    unseal; split; intros HPQ x' n'' ???;
      apply HQ, HPQ, HP; eauto using cmra_validN_op_r.
  - (* NonExpansive uPred_plainly *)
    intros n P1 P2 HP.
    unseal; split=> n' x; split; apply HP; eauto using @ucmra_unit_validN.
  - (* NonExpansive uPred_persistently *)
    intros n P1 P2 HP.
    unseal; split=> n' x; split; apply HP; eauto using @cmra_core_validN.
  - (* NonExpansive2 (@uPred_internal_eq M A) *)
    intros A n x x' Hx y y' Hy; split=> n' z; unseal; split; intros; simpl in *.
    + by rewrite -(dist_le _ _ _ _ Hx) -?(dist_le _ _ _ _ Hy); auto.
    + by rewrite (dist_le _ _ _ _ Hx) ?(dist_le _ _ _ _ Hy); auto.
  - (* φ → P ⊢ ⌜φ⌝ *)
    intros P φ ?. unseal; by split.
  - (* (φ → True ⊢ P) → ⌜φ⌝ ⊢ P *)
    intros φ P. unseal=> HP; split=> n x ??. by apply HP.
  - (* (∀ x : A, ⌜φ x⌝) ⊢ ⌜∀ x : A, φ x⌝ *)
    by unseal.
  - (* P ∧ Q ⊢ P *)
    intros P Q. unseal; by split=> n x ? [??].
  - (* P ∧ Q ⊢ Q *)
    intros P Q. unseal; by split=> n x ? [??].
  - (* (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R *)
    intros P Q R HQ HR; unseal; split=> n x ??; by split; [apply HQ|apply HR].
  - (* P ⊢ P ∨ Q *)
    intros P Q. unseal; split=> n x ??; left; auto.
  - (* Q ⊢ P ∨ Q *)
    intros P Q. unseal; split=> n x ??; right; auto.
  - (* (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R *)
    intros P Q R HP HQ. unseal; split=> n x ? [?|?]. by apply HP. by apply HQ.
  - (* (P ∧ Q ⊢ R) → P ⊢ Q → R. *)
    intros P Q R. unseal => HQ; split=> n x ?? n' x' ????. apply HQ;
      naive_solver eauto using uPred_mono, uPred_closed, cmra_included_includedN.
  - (* (P ⊢ Q → R) → P ∧ Q ⊢ R *)
    intros P Q R. unseal=> HP; split=> n x ? [??]. apply HP with n x; auto.
  - (* (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a *)
    intros A P Ψ. unseal; intros HPΨ; split=> n x ?? a; by apply HPΨ.
  - (* (∀ a, Ψ a) ⊢ Ψ a *)
    intros A Ψ a. unseal; split=> n x ? HP; apply HP.
  - (* Ψ a ⊢ ∃ a, Ψ a *)
    intros A Ψ a. unseal; split=> n x ??; by exists a.
  - (* (∀ a, Ψ a ⊢ Q) → (∃ a, Ψ a) ⊢ Q *)
    intros A Ψ Q. unseal; intros HΨ; split=> n x ? [a ?]; by apply HΨ with a.
  - (* P ⊢ a ≡ a *)
    intros A P a. unseal; by split=> n x ?? /=.
  - (* a ≡ b ⊢ Ψ a → Ψ b *)
    intros A a b Ψ Hnonexp.
    unseal; split=> n x ? Hab n' x' ??? HΨ. eapply Hnonexp with n a; auto.
  - (* (∀ x, f x ≡ g x) ⊢ f ≡ g *)
    by unseal.
  - (* `x ≡ `y ⊢ x ≡ y *)
    by unseal.
  - (* Discrete a → a ≡ b ⊣⊢ ⌜a ≡ b⌝ *)
    intros A a b ?. unseal; split=> n x ?; by apply (discrete_iff n).
  - (* (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q' *)
    intros P P' Q Q' HQ HQ'; unseal.
    split; intros n' x ? (x1&x2&?&?&?); exists x1,x2; ofe_subst x;
      eauto 7 using cmra_validN_op_l, cmra_validN_op_r, uPred_in_entails.
  - (* P ⊢ emp ∗ P *)
    intros P. rewrite /uPred_emp. unseal; split=> n x ?? /=.
    exists (core x), x. by rewrite cmra_core_l.
  - (* emp ∗ P ⊢ P *)
    intros P. unseal; split; intros n x ? (x1&x2&?&_&?); ofe_subst;
      eauto using uPred_mono, cmra_includedN_r.
  - (* P ∗ Q ⊢ Q ∗ P *)
    intros P Q. unseal; split; intros n x ? (x1&x2&?&?&?).
    exists x2, x1; by rewrite (comm op).
  - (* (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) *)
    intros P Q R. unseal; split; intros n x ? (x1&x2&Hx&(y1&y2&Hy&?&?)&?).
    exists y1, (y2 ⋅ x2); split_and?; auto.
    + by rewrite (assoc op) -Hy -Hx.
    + by exists y2, x2.
  - (* (P ∗ Q ⊢ R) → P ⊢ Q -∗ R *)
    intros P Q R. unseal=> HPQR; split=> n x ?? n' x' ???; apply HPQR; auto.
    exists x, x'; split_and?; auto.
    eapply uPred_closed with n; eauto using cmra_validN_op_l.
  - (* (P ⊢ Q -∗ R) → P ∗ Q ⊢ R *)
    intros P Q R. unseal=> HPQR. split; intros n x ? (?&?&?&?&?). ofe_subst.
    eapply HPQR; eauto using cmra_validN_op_l.
  - (* (P ⊢ Q) → bi_plainly P ⊢ bi_plainly Q *)
    intros P QR HP. unseal; split=> n x ? /=. by apply HP, ucmra_unit_validN.
  - (* bi_plainly P ⊢ bi_persistently P *)
    unseal; split; simpl; eauto using uPred_mono, @ucmra_unit_leastN.
  - (* bi_plainly P ⊢ bi_plainly (bi_plainly P) *)
    unseal; split=> n x ?? //.
  - (* (∀ a, bi_plainly (Ψ a)) ⊢ bi_plainly (∀ a, Ψ a) *)
    by unseal.
  - (* bi_plainly ((P → Q) ∧ (Q → P)) ⊢ P ≡ Q *)
    unseal; split=> n x ? /= HPQ; split=> n' x' ? HP;
    split; eapply HPQ; eauto using @ucmra_unit_least.
  - (* (bi_plainly P → bi_persistently Q) ⊢ bi_persistently (bi_plainly P → Q) *)
    unseal; split=> /= n x ? HPQ n' x' ????.
    eapply uPred_mono with (core x), cmra_included_includedN; auto.
    apply (HPQ n' x); eauto using cmra_validN_le.
  - (* (bi_plainly P → bi_plainly Q) ⊢ bi_plainly (bi_plainly P → Q) *)
    unseal; split=> /= n x ? HPQ n' x' ????.
    eapply uPred_mono with ε, cmra_included_includedN; auto.
    apply (HPQ n' x); eauto using cmra_validN_le.
  - (* P ⊢ bi_plainly emp (ADMISSIBLE) *)
    by unseal.
  - (* bi_plainly P ∗ Q ⊢ bi_plainly P *)
    intros P Q. move: (uPred_persistently P)=> P'.
    unseal; split; intros n x ? (x1&x2&?&?&_); ofe_subst;
      eauto using uPred_mono, cmra_includedN_l.
  - (* (P ⊢ Q) → bi_persistently P ⊢ bi_persistently Q *)
    intros P QR HP. unseal; split=> n x ? /=. by apply HP, cmra_core_validN.
  - (* bi_persistently P ⊢ bi_persistently (bi_persistently P) *)
    intros P. unseal; split=> n x ?? /=. by rewrite cmra_core_idemp.
  - (* bi_plainly (bi_persistently P) ⊢ bi_plainly P (ADMISSIBLE) *)
    intros P. unseal; split=> n  x ?? /=. by rewrite -(core_id_core ε).
  - (* (∀ a, bi_persistently (Ψ a)) ⊢ bi_persistently (∀ a, Ψ a) *)
    by unseal.
  - (* bi_persistently (∃ a, Ψ a) ⊢ ∃ a, bi_persistently (Ψ a) *)
    by unseal.
  - (* bi_persistently P ∗ Q ⊢ bi_persistently P (ADMISSIBLE) *)
    intros P Q. move: (uPred_persistently P)=> P'.
    unseal; split; intros n x ? (x1&x2&?&?&_); ofe_subst;
      eauto using uPred_mono, cmra_includedN_l.
  - (* bi_persistently P ∧ Q ⊢ (emp ∧ P) ∗ Q *)
    intros P Q. unseal; split=> n x ? [??]; simpl in *.
    exists (core x), x; rewrite ?cmra_core_l; auto.
Qed.

Lemma uPred_sbi_mixin (M : ucmraT) : SBIMixin
  uPred_entails uPred_pure uPred_or uPred_impl
  (@uPred_forall M) (@uPred_exist M) (@uPred_internal_eq M)
  uPred_sep uPred_plainly uPred_persistently uPred_later.
Proof.
  split.
  - (* Contractive sbi_later *)
    unseal; intros [|n] P Q HPQ; split=> -[|n'] x ?? //=; try omega.
    apply HPQ; eauto using cmra_validN_S.
  - (* Next x ≡ Next y ⊢ ▷ (x ≡ y) *)
    by unseal.
  - (* ▷ (x ≡ y) ⊢ Next x ≡ Next y *)
    by unseal.
  - (* (P ⊢ Q) → ▷ P ⊢ ▷ Q *)
    intros P Q.
    unseal=> HP; split=>-[|n] x ??; [done|apply HP; eauto using cmra_validN_S].
  - (* (▷ P → P) ⊢ P *)
    intros P. unseal; split=> n x ? HP; induction n as [|n IH]; [by apply HP|].
    apply HP, IH, uPred_closed with (S n); eauto using cmra_validN_S.
  - (* (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a *)
    intros A Φ. unseal; by split=> -[|n] x.
  - (* (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a) *)
    intros A Φ. unseal; split=> -[|[|n]] x /=; eauto.
  - (* ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q *)
    intros P Q. unseal; split=> -[|n] x ? /=.
    { by exists x, (core x); rewrite cmra_core_r. }
    intros (x1&x2&Hx&?&?); destruct (cmra_extend n x x1 x2)
      as (y1&y2&Hx'&Hy1&Hy2); eauto using cmra_validN_S; simpl in *.
    exists y1, y2; split; [by rewrite Hx'|by rewrite Hy1 Hy2].
  - (* ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q) *)
    intros P Q. unseal; split=> -[|n] x ? /=; [done|intros (x1&x2&Hx&?&?)].
    exists x1, x2; eauto using dist_S.
  - (* ▷ bi_plainly P ⊢ bi_plainly (▷ P) *)
    by unseal.
  - (* bi_plainly (▷ P) ⊢ ▷ bi_plainly P *)
    by unseal.
  - (* ▷ bi_persistently P ⊢ bi_persistently (▷ P) *)
    by unseal.
  - (* bi_persistently (▷ P) ⊢ ▷ bi_persistently P *)
    by unseal.
  - (* ▷ P ⊢ ▷ False ∨ (▷ False → P) *)
    intros P. unseal; split=> -[|n] x ? /= HP; [by left|right].
    intros [|n'] x' ????; [|done].
    eauto using uPred_closed, uPred_mono, cmra_included_includedN.
Qed.

Canonical Structure uPredI (M : ucmraT) : bi :=
  {| bi_ofe_mixin := ofe_mixin_of (uPred M); bi_bi_mixin := uPred_bi_mixin M |}.
Canonical Structure uPredSI (M : ucmraT) : sbi :=
  {| sbi_ofe_mixin := ofe_mixin_of (uPred M);
     sbi_bi_mixin := uPred_bi_mixin M; sbi_sbi_mixin := uPred_sbi_mixin M |}.

Coercion uPred_valid {M} : uPred M → Prop := bi_valid.

(* Latest notation *)
Notation "✓ x" := (uPred_cmra_valid x) (at level 20) : bi_scope.
Notation "|==> Q" := (bupd Q)
  (at level 99, Q at level 200, format "|==>  Q") : bi_scope.
Notation "P ==∗ Q" := (P ⊢ |==> Q)
  (at level 99, Q at level 200, only parsing) : stdpp_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q)%I
  (at level 99, Q at level 200, format "P  ==∗  Q") : bi_scope.

Module uPred.
Include uPred_unseal.
Section uPred.
Context {M : ucmraT}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.
Arguments uPred_holds {_} !_ _ _ /.
Hint Immediate uPred_in_entails.

Global Instance ownM_ne : NonExpansive (@uPred_ownM M).
Proof.
  intros n a b Ha.
  unseal; split=> n' x ? /=. by rewrite (dist_le _ _ _ _ Ha); last lia.
Qed.
Global Instance ownM_proper: Proper ((≡) ==> (⊣⊢)) (@uPred_ownM M) := ne_proper _.

Global Instance cmra_valid_ne {A : cmraT} :
  NonExpansive (@uPred_cmra_valid M A).
Proof.
  intros n a b Ha; unseal; split=> n' x ? /=.
  by rewrite (dist_le _ _ _ _ Ha); last lia.
Qed.
Global Instance cmra_valid_proper {A : cmraT} :
  Proper ((≡) ==> (⊣⊢)) (@uPred_cmra_valid M A) := ne_proper _.

Global Instance bupd_ne : NonExpansive (@bupd _ (@uPred_bupd M)).
Proof.
  intros n P Q HPQ.
  unseal; split=> n' x; split; intros HP k yf ??;
    destruct (HP k yf) as (x'&?&?); auto;
    exists x'; split; auto; apply HPQ; eauto using cmra_validN_op_l.
Qed.
Global Instance bupd_proper :
  Proper ((≡) ==> (≡)) (@bupd _ (@uPred_bupd M)) := ne_proper _.

(** BI instances *)

Global Instance uPred_affine : BiAffine (uPredI M) | 0.
Proof. intros P. rewrite /Affine. by apply bi.pure_intro. Qed.

Global Instance uPred_plainly_exist_1 : BiPlainlyExist (uPredI M).
Proof. unfold BiPlainlyExist. by unseal. Qed.

(** Limits *)
Lemma entails_lim (cP cQ : chain (uPredC M)) :
  (∀ n, cP n ⊢ cQ n) → compl cP ⊢ compl cQ.
Proof.
  intros Hlim; split=> n m ? HP.
  eapply uPred_holds_ne, Hlim, HP; eauto using conv_compl.
Qed.

(* Own *)
Lemma ownM_op (a1 a2 : M) :
  uPred_ownM (a1 ⋅ a2) ⊣⊢ uPred_ownM a1 ∗ uPred_ownM a2.
Proof.
  rewrite /bi_sep /=; unseal. split=> n x ?; split.
  - intros [z ?]; exists a1, (a2 ⋅ z); split; [by rewrite (assoc op)|].
    split. by exists (core a1); rewrite cmra_core_r. by exists z.
  - intros (y1&y2&Hx&[z1 Hy1]&[z2 Hy2]); exists (z1 ⋅ z2).
    by rewrite (assoc op _ z1) -(comm op z1) (assoc op z1)
      -(assoc op _ a2) (comm op z1) -Hy1 -Hy2.
Qed.
Lemma persistently_ownM_core (a : M) :
  uPred_ownM a ⊢ bi_persistently (uPred_ownM (core a)).
Proof.
  rewrite /bi_persistently /=. unseal.
  split=> n x Hx /=. by apply cmra_core_monoN.
Qed.
Lemma ownM_unit : bi_valid (uPred_ownM (ε:M)).
Proof. unseal; split=> n x ??; by  exists x; rewrite left_id. Qed.
Lemma later_ownM (a : M) : ▷ uPred_ownM a ⊢ ∃ b, uPred_ownM b ∧ ▷ (a ≡ b).
Proof.
  rewrite /bi_and /sbi_later /bi_exist /bi_internal_eq /=; unseal.
  split=> -[|n] x /= ? Hax; first by eauto using ucmra_unit_leastN.
  destruct Hax as [y ?].
  destruct (cmra_extend n x a y) as (a'&y'&Hx&?&?); auto using cmra_validN_S.
  exists a'. rewrite Hx. eauto using cmra_includedN_l.
Qed.

(* Valid *)
Lemma discrete_valid {A : cmraT} `{!CmraDiscrete A} (a : A) :
  ✓ a ⊣⊢ (⌜✓ a⌝ : uPred M).
Proof. unseal. split=> n x _. by rewrite /= -cmra_discrete_valid_iff. Qed.
Lemma ownM_valid (a : M) : uPred_ownM a ⊢ ✓ a.
Proof.
  unseal; split=> n x Hv [a' ?]; ofe_subst; eauto using cmra_validN_op_l.
Qed.
Lemma cmra_valid_intro {A : cmraT} (a : A) :
  ✓ a → bi_valid (PROP:=uPredI M) (✓ a).
Proof. unseal=> ?; split=> n x ? _ /=; by apply cmra_valid_validN. Qed.
Lemma cmra_valid_elim {A : cmraT} (a : A) : ¬ ✓{0} a → ✓ a ⊢ (False : uPred M).
Proof.
  intros Ha. unseal. split=> n x ??; apply Ha, cmra_validN_le with n; auto.
Qed.
Lemma plainly_cmra_valid_1 {A : cmraT} (a : A) : ✓ a ⊢ bi_plainly (✓ a : uPred M).
Proof. by unseal. Qed.
Lemma cmra_valid_weaken {A : cmraT} (a b : A) : ✓ (a ⋅ b) ⊢ (✓ a : uPred M).
Proof. unseal; split=> n x _; apply cmra_validN_op_l. Qed.

Lemma prod_validI {A B : cmraT} (x : A * B) : ✓ x ⊣⊢ (✓ x.1 ∧ ✓ x.2 : uPred M).
Proof. by unseal. Qed.
Lemma option_validI {A : cmraT} (mx : option A) :
  ✓ mx ⊣⊢ match mx with Some x => ✓ x | None => True : uPred M end.
Proof. unseal. by destruct mx. Qed.

Lemma ofe_fun_validI `{Finite A} {B : A → ucmraT} (g : ofe_fun B) :
  (✓ g : uPred M) ⊣⊢ ∀ i, ✓ g i.
Proof. by uPred.unseal. Qed.

(* Basic update modality *)
Lemma bupd_intro P : P ==∗ P.
Proof.
  unseal. split=> n x ? HP k yf ?; exists x; split; first done.
  apply uPred_closed with n; eauto using cmra_validN_op_l.
Qed.
Lemma bupd_mono P Q : (P ⊢ Q) → (|==> P) ==∗ Q.
Proof.
  unseal. intros HPQ; split=> n x ? HP k yf ??.
  destruct (HP k yf) as (x'&?&?); eauto.
  exists x'; split; eauto using uPred_in_entails, cmra_validN_op_l.
Qed.
Lemma bupd_trans P : (|==> |==> P) ==∗ P.
Proof. unseal; split; naive_solver. Qed.
Lemma bupd_frame_r P R : (|==> P) ∗ R ==∗ P ∗ R.
Proof.
  unseal. split; intros n x ? (x1&x2&Hx&HP&?) k yf ??.
  destruct (HP k (x2 ⋅ yf)) as (x'&?&?); eauto.
  { by rewrite assoc -(dist_le _ _ _ _ Hx); last lia. }
  exists (x' ⋅ x2); split; first by rewrite -assoc.
  exists x', x2; split_and?; auto.
  apply uPred_closed with n; eauto 3 using cmra_validN_op_l, cmra_validN_op_r.
Qed.
Lemma bupd_ownM_updateP x (Φ : M → Prop) :
  x ~~>: Φ → uPred_ownM x ==∗ ∃ y, ⌜Φ y⌝ ∧ uPred_ownM y.
Proof.
  intros Hup. unseal. split=> n x2 ? [x3 Hx] k yf ??.
  destruct (Hup k (Some (x3 ⋅ yf))) as (y&?&?); simpl in *.
  { rewrite /= assoc -(dist_le _ _ _ _ Hx); auto. }
  exists (y ⋅ x3); split; first by rewrite -assoc.
  exists y; eauto using cmra_includedN_l.
Qed.
Lemma bupd_plainly P : (|==> bi_plainly P) ⊢ P.
Proof.
  unseal; split => n x Hnx /= Hng.
  destruct (Hng n ε) as [? [_ Hng']]; try rewrite right_id; auto.
  eapply uPred_mono; eauto using ucmra_unit_leastN.
Qed.
End uPred.
End uPred.
