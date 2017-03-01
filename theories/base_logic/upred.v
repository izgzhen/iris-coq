From iris.algebra Require Export cmra.
Set Default Proof Using "Type".

(** The basic definition of the uPred type, its metric and functor laws.
    You probably do not want to import this file. Instead, import
    base_logic.base_logic; that will also give you all the primitive
    and many derived laws for the logic. *)

Record uPred (M : ucmraT) : Type := IProp {
  uPred_holds :> nat → M → Prop;
  uPred_mono n x1 x2 : uPred_holds n x1 → x1 ≼{n} x2 → uPred_holds n x2;
  uPred_closed n1 n2 x : uPred_holds n1 x → n2 ≤ n1 → ✓{n2} x → uPred_holds n2 x
}.
Arguments uPred_holds {_} _ _ _ : simpl never.
Add Printing Constructor uPred.
Instance: Params (@uPred_holds) 3.

Delimit Scope uPred_scope with I.
Bind Scope uPred_scope with uPred.
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
  `{!CMRAMonotone f} (P : uPred M1) :
  uPred M2 := {| uPred_holds n x := P n (f x) |}.
Next Obligation. naive_solver eauto using uPred_mono, cmra_monotoneN. Qed.
Next Obligation. naive_solver eauto using uPred_closed, cmra_monotone_validN. Qed.

Instance uPred_map_ne {M1 M2 : ucmraT} (f : M2 -n> M1)
  `{!CMRAMonotone f} n : Proper (dist n ==> dist n) (uPred_map f).
Proof.
  intros x1 x2 Hx; split=> n' y ??.
  split; apply Hx; auto using cmra_monotone_validN.
Qed.
Lemma uPred_map_id {M : ucmraT} (P : uPred M): uPred_map cid P ≡ P.
Proof. by split=> n x ?. Qed.
Lemma uPred_map_compose {M1 M2 M3 : ucmraT} (f : M1 -n> M2) (g : M2 -n> M3)
    `{!CMRAMonotone f, !CMRAMonotone g} (P : uPred M3):
  uPred_map (g ◎ f) P ≡ uPred_map f (uPred_map g P).
Proof. by split=> n x Hx. Qed.
Lemma uPred_map_ext {M1 M2 : ucmraT} (f g : M1 -n> M2)
      `{!CMRAMonotone f} `{!CMRAMonotone g}:
  (∀ x, f x ≡ g x) → ∀ x, uPred_map f x ≡ uPred_map g x.
Proof. intros Hf P; split=> n x Hx /=; by rewrite /uPred_holds /= Hf. Qed.
Definition uPredC_map {M1 M2 : ucmraT} (f : M2 -n> M1) `{!CMRAMonotone f} :
  uPredC M1 -n> uPredC M2 := CofeMor (uPred_map f : uPredC M1 → uPredC M2).
Lemma uPredC_map_ne {M1 M2 : ucmraT} (f g : M2 -n> M1)
    `{!CMRAMonotone f, !CMRAMonotone g} n :
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
Hint Extern 0 (uPred_entails _ _) => reflexivity.
Instance uPred_entails_rewrite_relation M : RewriteRelation (@uPred_entails M).

Hint Resolve uPred_mono uPred_closed : uPred_def.

(** Notations *)
Notation "P ⊢ Q" := (uPred_entails P%I Q%I)
  (at level 99, Q at level 200, right associativity) : C_scope.
Notation "(⊢)" := uPred_entails (only parsing) : C_scope.
Notation "P ⊣⊢ Q" := (equiv (A:=uPred _) P%I Q%I)
  (at level 95, no associativity) : C_scope.
Notation "(⊣⊢)" := (equiv (A:=uPred _)) (only parsing) : C_scope.

Module uPred.
Section entails.
Context {M : ucmraT}.
Implicit Types P Q : uPred M.

Global Instance: PreOrder (@uPred_entails M).
Proof.
  split.
  - by intros P; split=> x i.
  - by intros P Q Q' HP HQ; split=> x i ??; apply HQ, HP.
Qed.
Global Instance: AntiSymm (⊣⊢) (@uPred_entails M).
Proof. intros P Q HPQ HQP; split=> x n; by split; [apply HPQ|apply HQP]. Qed.

Lemma equiv_spec P Q : (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
Proof.
  split; [|by intros [??]; apply (anti_symm (⊢))].
  intros HPQ; split; split=> x i; apply HPQ.
Qed.
Lemma equiv_entails P Q : (P ⊣⊢ Q) → (P ⊢ Q).
Proof. apply equiv_spec. Qed.
Lemma equiv_entails_sym P Q : (Q ⊣⊢ P) → (P ⊢ Q).
Proof. apply equiv_spec. Qed.
Global Instance entails_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> iff) ((⊢) : relation (uPred M)).
Proof.
  move => P1 P2 /equiv_spec [HP1 HP2] Q1 Q2 /equiv_spec [HQ1 HQ2]; split; intros.
  - by trans P1; [|trans Q1].
  - by trans P2; [|trans Q2].
Qed.
Lemma entails_equiv_l (P Q R : uPred M) : (P ⊣⊢ Q) → (Q ⊢ R) → (P ⊢ R).
Proof. by intros ->. Qed.
Lemma entails_equiv_r (P Q R : uPred M) : (P ⊢ Q) → (Q ⊣⊢ R) → (P ⊢ R).
Proof. by intros ? <-. Qed.

Lemma entails_lim (P Q : chain (uPredC M)) :
  (∀ n, P n ⊢ Q n) → compl P ⊢ compl Q.
Proof.
  intros Hlim. split. intros n m Hval HP.
  eapply uPred_holds_ne, Hlim, HP; eauto using conv_compl.
Qed.

Lemma entails_lim' {T : ofeT} `{Cofe T} (P Q : T → uPredC M)
      `{!NonExpansive P} `{!NonExpansive Q} (c : chain T) :
  (∀ n, P (c n) ⊢ Q (c n)) → P (compl c) ⊢ Q (compl c).
Proof.
  set (cP := chain_map P c). set (cQ := chain_map Q c).
  rewrite -!compl_chain_map=>HPQ. exact: entails_lim.
Qed.

End entails.

Ltac entails_lim c :=
  pattern (compl c);
  match goal with
  | |- (λ o, ?P ⊢ ?Q) ?x => change (((λ o, P) x) ⊢ (λ o, Q) x)
  end;
  apply entails_lim'.

End uPred.
