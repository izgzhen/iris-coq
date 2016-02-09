Require Export algebra.cmra.
Local Hint Extern 1 (_ ≼ _) => etransitivity; [eassumption|].
Local Hint Extern 1 (_ ≼ _) => etransitivity; [|eassumption].
Local Hint Extern 10 (_ ≤ _) => omega.

Record uPred (M : cmraT) : Type := IProp {
  uPred_holds :> nat → M → Prop;
  uPred_ne x1 x2 n : uPred_holds n x1 → x1 ={n}= x2 → uPred_holds n x2;
  uPred_0 x : uPred_holds 0 x;
  uPred_weaken x1 x2 n1 n2 :
    uPred_holds n1 x1 → x1 ≼ x2 → n2 ≤ n1 → ✓{n2} x2 → uPred_holds n2 x2
}.
Arguments uPred_holds {_} _ _ _ : simpl never.
Global Opaque uPred_holds.
Local Transparent uPred_holds.
Hint Resolve uPred_0.
Add Printing Constructor uPred.
Instance: Params (@uPred_holds) 3.

Section cofe.
  Context {M : cmraT}.
  Instance uPred_equiv : Equiv (uPred M) := λ P Q, ∀ x n,
    ✓{n} x → P n x ↔ Q n x.
  Instance uPred_dist : Dist (uPred M) := λ n P Q, ∀ x n',
    n' ≤ n → ✓{n'} x → P n' x ↔ Q n' x.
  Program Instance uPred_compl : Compl (uPred M) := λ c,
    {| uPred_holds n x := c n n x |}.
  Next Obligation. by intros c x y n ??; simpl in *; apply uPred_ne with x. Qed.
  Next Obligation. by intros c x; simpl. Qed.
  Next Obligation.
    intros c x1 x2 n1 n2 ????; simpl in *.
    apply (chain_cauchy c n2 n1); eauto using uPred_weaken.
  Qed.
  Definition uPred_cofe_mixin : CofeMixin (uPred M).
  Proof.
    split.
    * intros P Q; split; [by intros HPQ n x i ??; apply HPQ|].
      intros HPQ x n ?; apply HPQ with n; auto.
    * intros n; split.
      + by intros P x i.
      + by intros P Q HPQ x i ??; symmetry; apply HPQ.
      + by intros P Q Q' HP HQ x i ??; transitivity (Q i x);[apply HP|apply HQ].
    * intros n P Q HPQ x i ??; apply HPQ; auto.
    * intros P Q x i; rewrite Nat.le_0_r=> ->; split; intros; apply uPred_0.
    * by intros c n x i ??; apply (chain_cauchy c i n).
  Qed.
  Canonical Structure uPredC : cofeT := CofeT uPred_cofe_mixin.
End cofe.
Arguments uPredC : clear implicits.

Instance uPred_ne' {M} (P : uPred M) n : Proper (dist n ==> iff) (P n).
Proof. intros x1 x2 Hx; split; eauto using uPred_ne. Qed.
Instance uPred_proper {M} (P : uPred M) n : Proper ((≡) ==> iff) (P n).
Proof. by intros x1 x2 Hx; apply uPred_ne', equiv_dist. Qed.

Lemma uPred_holds_ne {M} (P1 P2 : uPred M) n x :
  P1 ={n}= P2 → ✓{n} x → P1 n x → P2 n x.
Proof. intros HP ?; apply HP; auto. Qed.
Lemma uPred_weaken' {M} (P : uPred M) x1 x2 n1 n2 :
  x1 ≼ x2 → n2 ≤ n1 → ✓{n2} x2 → P n1 x1 → P n2 x2.
Proof. eauto using uPred_weaken. Qed.

(** functor *)
Program Definition uPred_map {M1 M2 : cmraT} (f : M2 -n> M1)
  `{!CMRAMonotone f} (P : uPred M1) :
  uPred M2 := {| uPred_holds n x := P n (f x) |}.
Next Obligation. by intros M1 M2 f ? P y1 y2 n ? Hy; rewrite /= -Hy. Qed.
Next Obligation. intros M1 M2 f _ P x; apply uPred_0. Qed.
Next Obligation.
  naive_solver eauto using uPred_weaken, included_preserving, validN_preserving.
Qed.
Instance uPred_map_ne {M1 M2 : cmraT} (f : M2 -n> M1)
  `{!CMRAMonotone f} :
  Proper (dist n ==> dist n) (uPred_map f).
Proof.
  by intros n x1 x2 Hx y n'; split; apply Hx; auto using validN_preserving.
Qed.
Lemma uPred_map_id {M : cmraT} (P : uPred M): uPred_map cid P ≡ P.
Proof. by intros x n ?. Qed.
Lemma uPred_map_compose {M1 M2 M3 : cmraT} (f : M1 -n> M2) (g : M2 -n> M3)
      `{!CMRAMonotone f} `{!CMRAMonotone g}
      (P : uPred M3):
  uPred_map (g ◎ f) P ≡ uPred_map f (uPred_map g P).
Proof. by intros x n Hx. Qed.
Lemma uPred_map_ext {M1 M2 : cmraT} (f g : M1 -n> M2)
      `{!CMRAMonotone f} `{!CMRAMonotone g}:
  (∀ x, f x ≡ g x) -> ∀ x, uPred_map f x ≡ uPred_map g x.
Proof. move=> H x P n Hx /=. by rewrite /uPred_holds /= H. Qed.
Definition uPredC_map {M1 M2 : cmraT} (f : M2 -n> M1) `{!CMRAMonotone f} :
  uPredC M1 -n> uPredC M2 := CofeMor (uPred_map f : uPredC M1 → uPredC M2).
Lemma upredC_map_ne {M1 M2 : cmraT} (f g : M2 -n> M1)
    `{!CMRAMonotone f, !CMRAMonotone g} n :
  f ={n}= g → uPredC_map f ={n}= uPredC_map g.
Proof.
  by intros Hfg P y n' ??;
    rewrite /uPred_holds /= (dist_le _ _ _ _(Hfg y)); last lia.
Qed.

(** logical entailement *)
Definition uPred_entails {M} (P Q : uPred M) := ∀ x n, ✓{n} x → P n x → Q n x.
Hint Extern 0 (uPred_entails ?P ?P) => reflexivity.
Instance uPred_entails_rewrite_relation M : RewriteRelation (@uPred_entails M).

(** logical connectives *)
Program Definition uPred_const {M} (φ : Prop) : uPred M :=
  {| uPred_holds n x := match n return _ with 0 => True | _ => φ end |}.
Solve Obligations with done.
Next Obligation. intros M P x1 x2 [|n1] [|n2]; auto with lia. Qed.
Instance uPred_inhabited M : Inhabited (uPred M) := populate (uPred_const True).

Program Definition uPred_and {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 using uPred_ne, uPred_weaken.
Program Definition uPred_or {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 using uPred_ne, uPred_weaken.
Program Definition uPred_impl {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ x' n',
       x ≼ x' → n' ≤ n → ✓{n'} x' → P n' x' → Q n' x' |}.
Next Obligation.
  intros M P Q x1' x1 n1 HPQ Hx1 x2 n2 ????.
  destruct (cmra_included_dist_l x1 x2 x1' n1) as (x2'&?&Hx2); auto.
  assert (x2' ={n2}= x2) as Hx2' by (by apply dist_le with n1).
  assert (✓{n2} x2') by (by rewrite Hx2'); rewrite -Hx2'.
  eauto using uPred_weaken, uPred_ne.
Qed.
Next Obligation. intros M P Q x1 x2 [|n]; auto with lia. Qed.
Next Obligation. naive_solver eauto 2 with lia. Qed.

Program Definition uPred_forall {M A} (P : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∀ a, P a n x |}.
Solve Obligations with naive_solver eauto 2 using uPred_ne, uPred_weaken.
Program Definition uPred_exist {M A} (P : A → uPred M) : uPred M :=
  {| uPred_holds n x :=
       match n return _ with 0 => True | _ => ∃ a, P a n x end |}.
Next Obligation. intros M A P x y [|n]; naive_solver eauto using uPred_ne. Qed.
Next Obligation. done. Qed.
Next Obligation.
  intros M A P x y [|n] [|n']; naive_solver eauto 2 using uPred_weaken with lia.
Qed.

Program Definition uPred_eq {M} {A : cofeT} (a1 a2 : A) : uPred M :=
  {| uPred_holds n x := a1 ={n}= a2 |}.
Solve Obligations with naive_solver eauto 2 using (dist_le (A:=A)).

Program Definition uPred_sep {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∃ x1 x2, x ={n}= x1 ⋅ x2 ∧ P n x1 ∧ Q n x2 |}.
Next Obligation.
  by intros M P Q x y n (x1&x2&?&?&?) Hxy; exists x1, x2; rewrite -Hxy.
Qed.
Next Obligation. by intros M P Q x; exists x, x. Qed.
Next Obligation.
  intros M P Q x y n1 n2 (x1&x2&Hx&?&?) Hxy ??.
  assert (∃ x2', y ={n2}= x1 ⋅ x2' ∧ x2 ≼ x2') as (x2'&Hy&?).
  { destruct Hxy as [z Hy]; exists (x2 ⋅ z); split; eauto using cmra_included_l.
    apply dist_le with n1; auto. by rewrite (associative op) -Hx Hy. }
  clear Hxy; cofe_subst y; exists x1, x2'; split_ands; [done| |].
  * apply uPred_weaken with x1 n1; eauto using cmra_validN_op_l.
  * apply uPred_weaken with x2 n1; eauto using cmra_validN_op_r.
Qed.

Program Definition uPred_wand {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ x' n',
       n' ≤ n → ✓{n'} (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Next Obligation.
  intros M P Q x1 x2 n1 HPQ Hx x3 n2 ???; simpl in *.
  rewrite -(dist_le _ _ _ _ Hx) //; apply HPQ; auto.
  by rewrite (dist_le _ _ _ n2 Hx).
Qed.
Next Obligation. intros M P Q x1 x2 [|n]; auto with lia. Qed.
Next Obligation.
  intros M P Q x1 x2 n1 n2 HPQ ??? x3 n3 ???; simpl in *.
  apply uPred_weaken with (x1 ⋅ x3) n3;
    eauto using cmra_validN_included, cmra_preserving_r.
Qed.

Program Definition uPred_later {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := match n return _ with 0 => True | S n' => P n' x end |}.
Next Obligation. intros M P ?? [|n]; eauto using uPred_ne,(dist_le (A:=M)). Qed.
Next Obligation. done. Qed.
Next Obligation.
  intros M P x1 x2 [|n1] [|n2]; eauto using uPred_weaken, cmra_validN_S.
Qed.
Program Definition uPred_always {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n (unit x) |}.
Next Obligation. by intros M P x1 x2 n ? Hx; rewrite /= -Hx. Qed.
Next Obligation. by intros; simpl. Qed.
Next Obligation.
  intros M P x1 x2 n1 n2 ????; eapply uPred_weaken with (unit x1) n1;
    eauto using cmra_unit_preserving, cmra_unit_validN.
Qed.

Program Definition uPred_own {M : cmraT} (a : M) : uPred M :=
  {| uPred_holds n x := a ≼{n} x |}.
Next Obligation. by intros M a x1 x2 n [a' ?] Hx; exists a'; rewrite -Hx. Qed.
Next Obligation. by intros M a x; exists x. Qed.
Next Obligation.
  intros M a x1 x n1 n2 [a' Hx1] [x2 Hx] ??.
  exists (a' ⋅ x2). by rewrite (associative op) -(dist_le _ _ _ _ Hx1) // Hx.
Qed.
Program Definition uPred_valid {M A : cmraT} (a : A) : uPred M :=
  {| uPred_holds n x := ✓{n} a |}.
Solve Obligations with naive_solver eauto 2 using cmra_validN_le, cmra_validN_0.

Delimit Scope uPred_scope with I.
Bind Scope uPred_scope with uPred.
Arguments uPred_holds {_} _%I _ _.
Arguments uPred_entails _ _%I _%I.
Notation "P ⊑ Q" := (uPred_entails P%I Q%I) (at level 70) : C_scope.
Notation "(⊑)" := uPred_entails (only parsing) : C_scope.
Notation "■ φ" := (uPred_const φ%type) (at level 20) : uPred_scope.
Notation "'False'" := (uPred_const False) : uPred_scope.
Notation "'True'" := (uPred_const True) : uPred_scope.
Infix "∧" := uPred_and : uPred_scope.
Notation "(∧)" := uPred_and (only parsing) : uPred_scope.
Infix "∨" := uPred_or : uPred_scope.
Notation "(∨)" := uPred_or (only parsing) : uPred_scope.
Infix "→" := uPred_impl : uPred_scope.
Infix "★" := uPred_sep (at level 80, right associativity) : uPred_scope.
Notation "(★)" := uPred_sep (only parsing) : uPred_scope.
Notation "P -★ Q" := (uPred_wand P Q)
  (at level 90, Q at level 200, right associativity) : uPred_scope.
Notation "∀ x .. y , P" :=
  (uPred_forall (λ x, .. (uPred_forall (λ y, P)) ..)%I) : uPred_scope.
Notation "∃ x .. y , P" :=
  (uPred_exist (λ x, .. (uPred_exist (λ y, P)) ..)%I) : uPred_scope.
Notation "▷ P" := (uPred_later P) (at level 20) : uPred_scope.
Notation "□ P" := (uPred_always P) (at level 20) : uPred_scope.
Infix "≡" := uPred_eq : uPred_scope.
Notation "✓" := uPred_valid (at level 1) : uPred_scope.

Definition uPred_iff {M} (P Q : uPred M) : uPred M := ((P → Q) ∧ (Q → P))%I.
Infix "↔" := uPred_iff : uPred_scope.

Fixpoint uPred_big_and {M} (Ps : list (uPred M)) :=
  match Ps with [] => True | P :: Ps => P ∧ uPred_big_and Ps end%I.
Instance: Params (@uPred_big_and) 1.
Notation "'Π∧' Ps" := (uPred_big_and Ps) (at level 20) : uPred_scope.
Fixpoint uPred_big_sep {M} (Ps : list (uPred M)) :=
  match Ps with [] => True | P :: Ps => P ★ uPred_big_sep Ps end%I.
Instance: Params (@uPred_big_sep) 1.
Notation "'Π★' Ps" := (uPred_big_sep Ps) (at level 20) : uPred_scope.

Class TimelessP {M} (P : uPred M) := timelessP : ▷ P ⊑ (P ∨ ▷ False).
Arguments timelessP {_} _ {_} _ _ _ _.
Class AlwaysStable {M} (P : uPred M) := always_stable : P ⊑ □ P.
Arguments always_stable {_} _ {_} _ _ _ _.

Module uPred. Section uPred_logic.
Context {M : cmraT}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types Ps Qs : list (uPred M).
Implicit Types A : Type.
Notation "P ⊑ Q" := (@uPred_entails M P%I Q%I). (* Force implicit argument M *)
Arguments uPred_holds {_} !_ _ _ /.

Global Instance: PreOrder (@uPred_entails M).
Proof. split. by intros P x i. by intros P Q Q' HP HQ x i ??; apply HQ, HP. Qed.
Global Instance: AntiSymmetric (≡) (@uPred_entails M).
Proof. intros P Q HPQ HQP; split; auto. Qed.
Lemma equiv_spec P Q : P ≡ Q ↔ P ⊑ Q ∧ Q ⊑ P.
Proof.
  split; [|by intros [??]; apply (anti_symmetric (⊑))].
  intros HPQ; split; intros x i; apply HPQ.
Qed.
Global Instance entails_proper :
  Proper ((≡) ==> (≡) ==> iff) ((⊑) : relation (uPred M)).
Proof.
  move => P1 P2 /equiv_spec [HP1 HP2] Q1 Q2 /equiv_spec [HQ1 HQ2]; split; intros.
  * by transitivity P1; [|transitivity Q1].
  * by transitivity P2; [|transitivity Q2].
Qed.

(** Non-expansiveness and setoid morphisms *)
Global Instance const_proper : Proper (iff ==> (≡)) (@uPred_const M).
Proof. by intros φ1 φ2 Hφ ? [|n] ?; try apply Hφ. Qed.
Global Instance and_ne n : Proper (dist n ==> dist n ==> dist n) (@uPred_and M).
Proof.
  intros P P' HP Q Q' HQ; split; intros [??]; split; by apply HP || by apply HQ.
Qed.
Global Instance and_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (@uPred_and M) := ne_proper_2 _.
Global Instance or_ne n : Proper (dist n ==> dist n ==> dist n) (@uPred_or M).
Proof.
  intros P P' HP Q Q' HQ; split; intros [?|?];
    first [by left; apply HP | by right; apply HQ].
Qed.
Global Instance or_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (@uPred_or M) := ne_proper_2 _.
Global Instance impl_ne n :
  Proper (dist n ==> dist n ==> dist n) (@uPred_impl M).
Proof.
  intros P P' HP Q Q' HQ; split; intros HPQ x' n'' ????; apply HQ,HPQ,HP; auto.
Qed.
Global Instance impl_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (@uPred_impl M) := ne_proper_2 _.
Global Instance sep_ne n : Proper (dist n ==> dist n ==> dist n) (@uPred_sep M).
Proof.
  intros P P' HP Q Q' HQ x n' ??; split; intros (x1&x2&?&?&?); cofe_subst x;
    exists x1, x2; split_ands; try (apply HP || apply HQ);
    eauto using cmra_validN_op_l, cmra_validN_op_r.
Qed.
Global Instance sep_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (@uPred_sep M) := ne_proper_2 _.
Global Instance wand_ne n :
  Proper (dist n ==> dist n ==> dist n) (@uPred_wand M).
Proof.
  intros P P' HP Q Q' HQ x n' ??; split; intros HPQ x' n'' ???;
    apply HQ, HPQ, HP; eauto using cmra_validN_op_r.
Qed.
Global Instance wand_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (@uPred_wand M) := ne_proper_2 _.
Global Instance eq_ne (A : cofeT) n :
  Proper (dist n ==> dist n ==> dist n) (@uPred_eq M A).
Proof.
  intros x x' Hx y y' Hy z n'; split; intros; simpl in *.
  * by rewrite -(dist_le _ _ _ _ Hx) -?(dist_le _ _ _ _ Hy); auto.
  * by rewrite (dist_le _ _ _ _ Hx) ?(dist_le _ _ _ _ Hy); auto.
Qed.
Global Instance eq_proper (A : cofeT) :
  Proper ((≡) ==> (≡) ==> (≡)) (@uPred_eq M A) := ne_proper_2 _.
Global Instance forall_ne A :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_forall M A).
Proof. by intros n P1 P2 HP12 x n'; split; intros HP a; apply HP12. Qed.
Global Instance forall_proper A :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@uPred_forall M A).
Proof. by intros P1 P2 HP12 x n'; split; intros HP a; apply HP12. Qed.
Global Instance exists_ne A :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_exist M A).
Proof.
  by intros n P1 P2 HP x [|n']; [|split; intros [a ?]; exists a; apply HP].
Qed.
Global Instance exist_proper A :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@uPred_exist M A).
Proof.
  by intros P1 P2 HP x [|n']; [|split; intros [a ?]; exists a; apply HP].
Qed.
Global Instance later_contractive : Contractive (@uPred_later M).
Proof.
  intros n P Q HPQ x [|n'] ??; simpl; [done|].
  apply HPQ; eauto using cmra_validN_S.
Qed.
Global Instance later_proper :
  Proper ((≡) ==> (≡)) (@uPred_later M) := ne_proper _.
Global Instance always_ne n: Proper (dist n ==> dist n) (@uPred_always M).
Proof. intros P1 P2 HP x n'; split; apply HP; eauto using cmra_unit_validN. Qed.
Global Instance always_proper :
  Proper ((≡) ==> (≡)) (@uPred_always M) := ne_proper _.
Global Instance own_ne n : Proper (dist n ==> dist n) (@uPred_own M).
Proof.
  by intros a1 a2 Ha x n'; split; intros [a' ?]; exists a'; simpl; first
    [rewrite -(dist_le _ _ _ _ Ha); last lia
    |rewrite (dist_le _ _ _ _ Ha); last lia].
Qed.
Global Instance own_proper : Proper ((≡) ==> (≡)) (@uPred_own M) := ne_proper _.
Global Instance iff_ne n : Proper (dist n ==> dist n ==> dist n) (@uPred_iff M).
Proof. unfold uPred_iff; solve_proper. Qed.
Global Instance iff_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (@uPred_iff M) := ne_proper_2 _.

(** Introduction and elimination rules *)
Lemma const_intro φ P : φ → P ⊑ ■ φ.
Proof. by intros ?? [|?]. Qed.
Lemma const_elim φ Q R : Q ⊑ ■ φ → (φ → Q ⊑ R) → Q ⊑ R.
Proof.
  intros HQP HQR x [|n] ??; first done.
  apply HQR; first eapply (HQP _ (S n)); eauto.
Qed.
Lemma True_intro P : P ⊑ True.
Proof. by apply const_intro. Qed.
Lemma False_elim P : False ⊑ P.
Proof. by intros x [|n] ?. Qed.
Lemma and_elim_l P Q : (P ∧ Q) ⊑ P.
Proof. by intros x n ? [??]. Qed.
Lemma and_elim_r P Q : (P ∧ Q) ⊑ Q.
Proof. by intros x n ? [??]. Qed.
Lemma and_intro P Q R : P ⊑ Q → P ⊑ R → P ⊑ (Q ∧ R).
Proof. intros HQ HR x n ??; split; auto. Qed.
Lemma or_intro_l P Q : P ⊑ (P ∨ Q).
Proof. intros x n ??; left; auto. Qed.
Lemma or_intro_r P Q : Q ⊑ (P ∨ Q).
Proof. intros x n ??; right; auto. Qed.
Lemma or_elim P Q R : P ⊑ R → Q ⊑ R → (P ∨ Q) ⊑ R.
Proof. intros HP HQ x n ? [?|?]. by apply HP. by apply HQ. Qed.
Lemma impl_intro_r P Q R : (P ∧ Q) ⊑ R → P ⊑ (Q → R).
Proof.
  intros HQ x n ?? x' n' ????; apply HQ; naive_solver eauto using uPred_weaken.
Qed.
Lemma impl_elim P Q R : P ⊑ (Q → R) → P ⊑ Q → P ⊑ R.
Proof. by intros HP HP' x n ??; apply HP with x n, HP'. Qed.
Lemma forall_intro {A} P (Q : A → uPred M): (∀ a, P ⊑ Q a) → P ⊑ (∀ a, Q a).
Proof. by intros HPQ x n ?? a; apply HPQ. Qed.
Lemma forall_elim {A} {P : A → uPred M} a : (∀ a, P a) ⊑ P a.
Proof. intros x n ? HP; apply HP. Qed.
Lemma exist_intro {A} {P : A → uPred M} a : P a ⊑ (∃ a, P a).
Proof. by intros x [|n] ??; [done|exists a]. Qed.
Lemma exist_elim {A} (P : A → uPred M) Q : (∀ a, P a ⊑ Q) → (∃ a, P a) ⊑ Q.
Proof. by intros HPQ x [|n] ?; [|intros [a ?]; apply HPQ with a]. Qed.
Lemma eq_refl {A : cofeT} (a : A) P : P ⊑ (a ≡ a).
Proof. by intros x n ??; simpl. Qed.
Lemma eq_rewrite {A : cofeT} P (Q : A → uPred M)
  `{HQ:∀ n, Proper (dist n ==> dist n) Q} a b : P ⊑ (a ≡ b) → P ⊑ Q a → P ⊑ Q b.
Proof.
  intros Hab Ha x n ??; apply HQ with n a; auto. by symmetry; apply Hab with x.
Qed.
Lemma eq_equiv `{Empty M, !CMRAIdentity M} {A : cofeT} (a b : A) :
  True ⊑ (a ≡ b) → a ≡ b.
Proof.
  intros Hab; apply equiv_dist; intros n; apply Hab with ∅.
  * apply cmra_valid_validN, cmra_empty_valid.
  * by destruct n.
Qed.
Lemma iff_equiv P Q : True ⊑ (P ↔ Q) → P ≡ Q.
Proof. by intros HPQ x [|n] ?; [|split; intros; apply HPQ with x (S n)]. Qed.

(* Derived logical stuff *)
Lemma and_elim_l' P Q R : P ⊑ R → (P ∧ Q) ⊑ R.
Proof. by rewrite and_elim_l. Qed.
Lemma and_elim_r' P Q R : Q ⊑ R → (P ∧ Q) ⊑ R.
Proof. by rewrite and_elim_r. Qed.
Lemma or_intro_l' P Q R : P ⊑ Q → P ⊑ (Q ∨ R).
Proof. intros ->; apply or_intro_l. Qed.
Lemma or_intro_r' P Q R : P ⊑ R → P ⊑ (Q ∨ R).
Proof. intros ->; apply or_intro_r. Qed.
Lemma exist_intro' {A} P (Q : A → uPred M) a : P ⊑ Q a → P ⊑ (∃ a, Q a).
Proof. intros ->; apply exist_intro. Qed.

Hint Resolve or_elim or_intro_l' or_intro_r'.
Hint Resolve and_intro and_elim_l' and_elim_r'.
Hint Immediate True_intro False_elim.

Lemma impl_intro_l P Q R : (Q ∧ P) ⊑ R → P ⊑ (Q → R).
Proof. intros HR; apply impl_intro_r; rewrite -HR; auto. Qed.
Lemma impl_elim_l P Q : ((P → Q) ∧ P) ⊑ Q.
Proof. apply impl_elim with P; auto. Qed.
Lemma impl_elim_r P Q : (P ∧ (P → Q)) ⊑ Q.
Proof. apply impl_elim with P; auto. Qed.
Lemma impl_elim_l' P Q R : P ⊑ (Q → R) → (P ∧ Q) ⊑ R.
Proof. intros; apply impl_elim with Q; auto. Qed.
Lemma impl_elim_r' P Q R : Q ⊑ (P → R) → (P ∧ Q) ⊑ R.
Proof. intros; apply impl_elim with P; auto. Qed.
Lemma impl_entails P Q : True ⊑ (P → Q) → P ⊑ Q.
Proof. intros HPQ; apply impl_elim with P; rewrite -?HPQ; auto. Qed.
Lemma entails_impl P Q : (P ⊑ Q) → True ⊑ (P → Q).
Proof. auto using impl_intro_l. Qed.

Lemma const_intro_l φ Q R : φ → (■φ ∧ Q) ⊑ R → Q ⊑ R.
Proof. intros ? <-; auto using const_intro. Qed.
Lemma const_intro_r φ Q R : φ → (Q ∧ ■φ) ⊑ R → Q ⊑ R.
Proof. intros ? <-; auto using const_intro. Qed.
Lemma const_elim_l φ Q R : (φ → Q ⊑ R) → (■ φ ∧ Q) ⊑ R.
Proof. intros; apply const_elim with φ; eauto. Qed.
Lemma const_elim_r φ Q R : (φ → Q ⊑ R) → (Q ∧ ■ φ) ⊑ R.
Proof. intros; apply const_elim with φ; eauto. Qed.
Lemma const_equiv (φ : Prop) : φ → (■ φ : uPred M)%I ≡ True%I.
Proof. intros; apply (anti_symmetric _); auto using const_intro. Qed.
Lemma equiv_eq {A : cofeT} P (a b : A) : a ≡ b → P ⊑ (a ≡ b).
Proof. intros ->; apply eq_refl. Qed.
Lemma eq_sym {A : cofeT} (a b : A) : (a ≡ b) ⊑ (b ≡ a).
Proof.
  refine (eq_rewrite _ (λ b, b ≡ a)%I a b _ _); auto using eq_refl.
  intros n; solve_proper.
Qed.

Lemma const_mono φ1 φ2 : (φ1 → φ2) → ■ φ1 ⊑ ■ φ2.
Proof. intros; apply const_elim with φ1; eauto using const_intro. Qed.
Lemma and_mono P P' Q Q' : P ⊑ Q → P' ⊑ Q' → (P ∧ P') ⊑ (Q ∧ Q').
Proof. auto. Qed.
Lemma or_mono P P' Q Q' : P ⊑ Q → P' ⊑ Q' → (P ∨ P') ⊑ (Q ∨ Q').
Proof. auto. Qed.
Lemma impl_mono P P' Q Q' : Q ⊑ P → P' ⊑ Q' → (P → P') ⊑ (Q → Q').
Proof.
  intros HP HQ'; apply impl_intro_l; rewrite -HQ'.
  apply impl_elim with P; eauto.
Qed.
Lemma forall_mono {A} (P Q : A → uPred M) :
  (∀ a, P a ⊑ Q a) → (∀ a, P a) ⊑ (∀ a, Q a).
Proof.
  intros HP. apply forall_intro=> a; rewrite -(HP a); apply forall_elim.
Qed.
Lemma exist_mono {A} (P Q : A → uPred M) :
  (∀ a, P a ⊑ Q a) → (∃ a, P a) ⊑ (∃ a, Q a).
Proof. intros HP. apply exist_elim=> a; rewrite (HP a); apply exist_intro. Qed.
Global Instance const_mono' : Proper (impl ==> (⊑)) (@uPred_const M).
Proof. intros φ1 φ2; apply const_mono. Qed.
Global Instance and_mono' : Proper ((⊑) ==> (⊑) ==> (⊑)) (@uPred_and M).
Proof. by intros P P' HP Q Q' HQ; apply and_mono. Qed.
Global Instance and_flip_mono' :
  Proper (flip (⊑) ==> flip (⊑) ==> flip (⊑)) (@uPred_and M).
Proof. by intros P P' HP Q Q' HQ; apply and_mono. Qed.
Global Instance or_mono' : Proper ((⊑) ==> (⊑) ==> (⊑)) (@uPred_or M).
Proof. by intros P P' HP Q Q' HQ; apply or_mono. Qed.
Global Instance or_flip_mono' :
  Proper (flip (⊑) ==> flip (⊑) ==> flip (⊑)) (@uPred_or M).
Proof. by intros P P' HP Q Q' HQ; apply or_mono. Qed.
Global Instance impl_mono' :
  Proper (flip (⊑) ==> (⊑) ==> (⊑)) (@uPred_impl M).
Proof. by intros P P' HP Q Q' HQ; apply impl_mono. Qed.
Global Instance forall_mono' A :
  Proper (pointwise_relation _ (⊑) ==> (⊑)) (@uPred_forall M A).
Proof. intros P1 P2; apply forall_mono. Qed.
Global Instance exist_mono' A :
  Proper (pointwise_relation _ (⊑) ==> (⊑)) (@uPred_exist M A).
Proof. intros P1 P2; apply exist_mono. Qed.

Global Instance and_idem : Idempotent (≡) (@uPred_and M).
Proof. intros P; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance or_idem : Idempotent (≡) (@uPred_or M).
Proof. intros P; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance and_comm : Commutative (≡) (@uPred_and M).
Proof. intros P Q; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance True_and : LeftId (≡) True%I (@uPred_and M).
Proof. intros P; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance and_True : RightId (≡) True%I (@uPred_and M).
Proof. intros P; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance False_and : LeftAbsorb (≡) False%I (@uPred_and M).
Proof. intros P; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance and_False : RightAbsorb (≡) False%I (@uPred_and M).
Proof. intros P; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance True_or : LeftAbsorb (≡) True%I (@uPred_or M).
Proof. intros P; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance or_True : RightAbsorb (≡) True%I (@uPred_or M).
Proof. intros P; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance False_or : LeftId (≡) False%I (@uPred_or M).
Proof. intros P; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance or_False : RightId (≡) False%I (@uPred_or M).
Proof. intros P; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance and_assoc : Associative (≡) (@uPred_and M).
Proof. intros P Q R; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance or_comm : Commutative (≡) (@uPred_or M).
Proof. intros P Q; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance or_assoc : Associative (≡) (@uPred_or M).
Proof. intros P Q R; apply (anti_symmetric (⊑)); auto. Qed.
Global Instance True_impl : LeftId (≡) True%I (@uPred_impl M).
Proof.
  intros P; apply (anti_symmetric (⊑)).
  * by rewrite -(left_id True%I uPred_and (_ → _)%I) impl_elim_r.
  * by apply impl_intro_l; rewrite left_id.
Qed.
Lemma or_and_l P Q R : (P ∨ Q ∧ R)%I ≡ ((P ∨ Q) ∧ (P ∨ R))%I.
Proof.
  apply (anti_symmetric (⊑)); first auto.
  do 2 (apply impl_elim_l', or_elim; apply impl_intro_l); auto.
Qed.
Lemma or_and_r P Q R : (P ∧ Q ∨ R)%I ≡ ((P ∨ R) ∧ (Q ∨ R))%I.
Proof. by rewrite -!(commutative _ R) or_and_l. Qed.
Lemma and_or_l P Q R : (P ∧ (Q ∨ R))%I ≡ (P ∧ Q ∨ P ∧ R)%I.
Proof.
  apply (anti_symmetric (⊑)); last auto.
  apply impl_elim_r', or_elim; apply impl_intro_l; auto.
Qed.
Lemma and_or_r P Q R : ((P ∨ Q) ∧ R)%I ≡ (P ∧ R ∨ Q ∧ R)%I.
Proof. by rewrite -!(commutative _ R) and_or_l. Qed.
Lemma and_exist_l {A} P (Q : A → uPred M) : (P ∧ ∃ a, Q a)%I ≡ (∃ a, P ∧ Q a)%I.
Proof.
  apply (anti_symmetric (⊑)).
  - apply impl_elim_r'. apply exist_elim=>a. apply impl_intro_l.
    by rewrite -(exist_intro a).
  - apply exist_elim=>a. apply and_intro; first by rewrite and_elim_l.
    by rewrite -(exist_intro a) and_elim_r.
Qed.
Lemma and_exist_r {A} P (Q : A → uPred M) : (P ∧ ∃ a, Q a)%I ≡ (∃ a, P ∧ Q a)%I.
Proof. by rewrite (commutative _ P) -and_exist_l (commutative _ P). Qed.

(* BI connectives *)
Lemma sep_mono P P' Q Q' : P ⊑ Q → P' ⊑ Q' → (P ★ P') ⊑ (Q ★ Q').
Proof.
  intros HQ HQ' x n' ? (x1&x2&?&?&?); exists x1, x2; cofe_subst x;
    eauto 7 using cmra_validN_op_l, cmra_validN_op_r.
Qed.
Global Instance True_sep : LeftId (≡) True%I (@uPred_sep M).
Proof.
  intros P x n Hvalid; split.
  * intros (x1&x2&?&_&?); cofe_subst; eauto using uPred_weaken, cmra_included_r.
  * by destruct n as [|n]; [|intros ?; exists (unit x), x; rewrite cmra_unit_l].
Qed. 
Global Instance sep_commutative : Commutative (≡) (@uPred_sep M).
Proof.
  by intros P Q x n ?; split;
    intros (x1&x2&?&?&?); exists x2, x1; rewrite (commutative op).
Qed.
Global Instance sep_associative : Associative (≡) (@uPred_sep M).
Proof.
  intros P Q R x n ?; split.
  * intros (x1&x2&Hx&?&y1&y2&Hy&?&?); exists (x1 ⋅ y1), y2; split_ands; auto.
    + by rewrite -(associative op) -Hy -Hx.
    + by exists x1, y1.
  * intros (x1&x2&Hx&(y1&y2&Hy&?&?)&?); exists y1, (y2 ⋅ x2); split_ands; auto.
    + by rewrite (associative op) -Hy -Hx.
    + by exists y2, x2.
Qed.
Lemma wand_intro_r P Q R : (P ★ Q) ⊑ R → P ⊑ (Q -★ R).
Proof.
  intros HPQR x n ?? x' n' ???; apply HPQR; auto.
  exists x, x'; split_ands; auto.
  eapply uPred_weaken with x n; eauto using cmra_validN_op_l.
Qed.
Lemma wand_elim_l P Q : ((P -★ Q) ★ P) ⊑ Q.
Proof. by intros x n ? (x1&x2&Hx&HPQ&?); cofe_subst; apply HPQ. Qed.

(* Derived BI Stuff *)
Hint Resolve sep_mono.
Global Instance sep_mono' : Proper ((⊑) ==> (⊑) ==> (⊑)) (@uPred_sep M).
Proof. by intros P P' HP Q Q' HQ; apply sep_mono. Qed.
Global Instance sep_flip_mono' :
  Proper (flip (⊑) ==> flip (⊑) ==> flip (⊑)) (@uPred_sep M).
Proof. by intros P P' HP Q Q' HQ; apply sep_mono. Qed.
Lemma wand_mono P P' Q Q' : Q ⊑ P → P' ⊑ Q' → (P -★ P') ⊑ (Q -★ Q').
Proof. intros HP HQ; apply wand_intro_r; rewrite HP -HQ; apply wand_elim_l. Qed.
Global Instance wand_mono' : Proper (flip (⊑) ==> (⊑) ==> (⊑)) (@uPred_wand M).
Proof. by intros P P' HP Q Q' HQ; apply wand_mono. Qed.

Global Instance sep_True : RightId (≡) True%I (@uPred_sep M).
Proof. by intros P; rewrite (commutative _) (left_id _ _). Qed.
Lemma sep_elim_l P Q : (P ★ Q) ⊑ P.
Proof. by rewrite (True_intro Q) (right_id _ _). Qed.
Lemma sep_elim_r P Q : (P ★ Q) ⊑ Q.
Proof. by rewrite (commutative (★))%I; apply sep_elim_l. Qed.
Lemma sep_elim_l' P Q R : P ⊑ R → (P ★ Q) ⊑ R.
Proof. intros ->; apply sep_elim_l. Qed.
Lemma sep_elim_r' P Q R : Q ⊑ R → (P ★ Q) ⊑ R.
Proof. intros ->; apply sep_elim_r. Qed.
Hint Resolve sep_elim_l' sep_elim_r'.
Lemma sep_intro_True_l P Q R : True ⊑ P → R ⊑ Q → R ⊑ (P ★ Q).
Proof. by intros; rewrite -(left_id True%I uPred_sep R); apply sep_mono. Qed.
Lemma sep_intro_True_r P Q R : R ⊑ P → True ⊑ Q → R ⊑ (P ★ Q).
Proof. by intros; rewrite -(right_id True%I uPred_sep R); apply sep_mono. Qed.
Lemma wand_intro_l P Q R : (Q ★ P) ⊑ R → P ⊑ (Q -★ R).
Proof. rewrite (commutative _); apply wand_intro_r. Qed.
Lemma wand_elim_r P Q : (P ★ (P -★ Q)) ⊑ Q.
Proof. rewrite (commutative _ P); apply wand_elim_l. Qed.
Lemma wand_elim_l' P Q R : P ⊑ (Q -★ R) → (P ★ Q) ⊑ R.
Proof. intros ->; apply wand_elim_l. Qed.
Lemma wand_elim_r' P Q R : Q ⊑ (P -★ R) → (P ★ Q) ⊑ R.
Proof. intros ->; apply wand_elim_r. Qed.
Lemma sep_and P Q : (P ★ Q) ⊑ (P ∧ Q).
Proof. auto. Qed.
Lemma impl_wand P Q : (P → Q) ⊑ (P -★ Q).
Proof. apply wand_intro_r, impl_elim with P; auto. Qed.

Global Instance sep_False : LeftAbsorb (≡) False%I (@uPred_sep M).
Proof. intros P; apply (anti_symmetric _); auto. Qed.
Global Instance False_sep : RightAbsorb (≡) False%I (@uPred_sep M).
Proof. intros P; apply (anti_symmetric _); auto. Qed.

Lemma sep_and_l P Q R : (P ★ (Q ∧ R)) ⊑ ((P ★ Q) ∧ (P ★ R)).
Proof. auto. Qed.
Lemma sep_and_r P Q R : ((P ∧ Q) ★ R) ⊑ ((P ★ R) ∧ (Q ★ R)).
Proof. auto. Qed.
Lemma sep_or_l P Q R : (P ★ (Q ∨ R))%I ≡ ((P ★ Q) ∨ (P ★ R))%I.
Proof.
  apply (anti_symmetric (⊑)); last by eauto 8.
  apply wand_elim_r', or_elim; apply wand_intro_l.
  - by apply or_intro_l.
  - by apply or_intro_r.
Qed.
Lemma sep_or_r P Q R : ((P ∨ Q) ★ R)%I ≡ ((P ★ R) ∨ (Q ★ R))%I.
Proof. by rewrite -!(commutative _ R) sep_or_l. Qed.
Lemma sep_exist_l {A} P (Q : A → uPred M) : (P ★ ∃ a, Q a)%I ≡ (∃ a, P ★ Q a)%I.
Proof.
  intros; apply (anti_symmetric (⊑)).
  - apply wand_elim_r', exist_elim=>a. apply wand_intro_l.
    by rewrite -(exist_intro a).
  - apply exist_elim=> a; apply sep_mono; auto using exist_intro.
Qed.
Lemma sep_exist_r {A} (P: A → uPred M) Q: ((∃ a, P a) ★ Q)%I ≡ (∃ a, P a ★ Q)%I.
Proof. setoid_rewrite (commutative _ _ Q); apply sep_exist_l. Qed.
Lemma sep_forall_l {A} P (Q : A → uPred M) : (P ★ ∀ a, Q a) ⊑ (∀ a, P ★ Q a).
Proof. by apply forall_intro=> a; rewrite forall_elim. Qed.
Lemma sep_forall_r {A} (P : A → uPred M) Q : ((∀ a, P a) ★ Q) ⊑ (∀ a, P a ★ Q).
Proof. by apply forall_intro=> a; rewrite forall_elim. Qed.

(* Later *)
Lemma later_mono P Q : P ⊑ Q → ▷ P ⊑ ▷ Q.
Proof. intros HP x [|n] ??; [done|apply HP; eauto using cmra_validN_S]. Qed.
Lemma later_intro P : P ⊑ ▷ P.
Proof.
  intros x [|n] ??; simpl in *; [done|].
  apply uPred_weaken with x (S n); eauto using cmra_validN_S.
Qed.
Lemma löb P : (▷ P → P) ⊑ P.
Proof.
  intros x n ? HP; induction n as [|n IH]; [by apply HP|].
  apply HP, IH, uPred_weaken with x (S n); eauto using cmra_validN_S.
Qed.
Lemma later_and P Q : (▷ (P ∧ Q))%I ≡ (▷ P ∧ ▷ Q)%I.
Proof. by intros x [|n]; split. Qed.
Lemma later_or P Q : (▷ (P ∨ Q))%I ≡ (▷ P ∨ ▷ Q)%I.
Proof. intros x [|n]; simpl; tauto. Qed.
Lemma later_forall {A} (P : A → uPred M) : (▷ ∀ a, P a)%I ≡ (∀ a, ▷ P a)%I.
Proof. by intros x [|n]. Qed.
Lemma later_exist {A} (P : A → uPred M) : (∃ a, ▷ P a) ⊑ (▷ ∃ a, P a).
Proof. by intros x [|[|n]]. Qed.
Lemma later_exist' `{Inhabited A} (P : A → uPred M) :
  (▷ ∃ a, P a)%I ≡ (∃ a, ▷ P a)%I.
Proof. intros x [|[|n]]; split; done || by exists inhabitant; simpl. Qed.
Lemma later_sep P Q : (▷ (P ★ Q))%I ≡ (▷ P ★ ▷ Q)%I.
Proof.
  intros x n ?; split.
  * destruct n as [|n]; simpl; [by exists x, x|intros (x1&x2&Hx&?&?)].
    destruct (cmra_extend_op n x x1 x2)
      as ([y1 y2]&Hx'&Hy1&Hy2); eauto using cmra_validN_S; simpl in *.
    exists y1, y2; split; [by rewrite Hx'|by rewrite Hy1 Hy2].
  * destruct n as [|n]; simpl; [done|intros (x1&x2&Hx&?&?)].
    exists x1, x2; eauto using dist_S.
Qed.

(* Later derived *)
Global Instance later_mono' : Proper ((⊑) ==> (⊑)) (@uPred_later M).
Proof. intros P Q; apply later_mono. Qed.
Lemma later_impl P Q : ▷ (P → Q) ⊑ (▷ P → ▷ Q).
Proof.
  apply impl_intro_l; rewrite -later_and.
  apply later_mono, impl_elim with P; auto.
Qed.
Lemma later_wand P Q : ▷ (P -★ Q) ⊑ (▷ P -★ ▷ Q).
Proof. apply wand_intro_r;rewrite -later_sep; apply later_mono,wand_elim_l. Qed.
Lemma löb_all_1 {A} (P Q : A → uPred M) :
  (∀ a, (▷(∀ b, P b → Q b) ∧ P a) ⊑ Q a) → ∀ a, P a ⊑ Q a.
Proof.
  intros Hlöb a. apply impl_entails. transitivity (∀ a, P a → Q a)%I; last first.
  { by rewrite (forall_elim a). } clear a.
  etransitivity; last by eapply löb.
  apply impl_intro_l, forall_intro=>a. rewrite right_id. by apply impl_intro_r.
Qed.

(* Always *)
Lemma always_const φ : (□ ■ φ : uPred M)%I ≡ (■ φ)%I.
Proof. done. Qed.
Lemma always_elim P : □ P ⊑ P.
Proof.
  intros x n ??; apply uPred_weaken with (unit x) n;
    eauto using cmra_included_unit.
Qed.
Lemma always_intro P Q : □ P ⊑ Q → □ P ⊑ □ Q.
Proof.
  intros HPQ x n ??; apply HPQ; simpl in *; auto using cmra_unit_validN.
  by rewrite cmra_unit_idempotent.
Qed.
Lemma always_and P Q : (□ (P ∧ Q))%I ≡ (□ P ∧ □ Q)%I.
Proof. done. Qed.
Lemma always_or P Q : (□ (P ∨ Q))%I ≡ (□ P ∨ □ Q)%I.
Proof. done. Qed.
Lemma always_forall {A} (P : A → uPred M) : (□ ∀ a, P a)%I ≡ (∀ a, □ P a)%I.
Proof. done. Qed.
Lemma always_exist {A} (P : A → uPred M) : (□ ∃ a, P a)%I ≡ (∃ a, □ P a)%I.
Proof. done. Qed.
Lemma always_and_sep_1 P Q : □ (P ∧ Q) ⊑ □ (P ★ Q).
Proof.
  intros x n ? [??]; exists (unit x), (unit x); rewrite cmra_unit_unit; auto.
Qed.
Lemma always_and_sep_l_1 P Q : (□ P ∧ Q) ⊑ (□ P ★ Q).
Proof.
  intros x n ? [??]; exists (unit x), x; simpl in *.
  by rewrite cmra_unit_l cmra_unit_idempotent.
Qed.
Lemma always_later P : (□ ▷ P)%I ≡ (▷ □ P)%I.
Proof. done. Qed.

(* Always derived *)
Lemma always_mono P Q : P ⊑ Q → □ P ⊑ □ Q.
Proof. intros. apply always_intro. by rewrite always_elim. Qed.
Hint Resolve always_mono.
Global Instance always_mono' : Proper ((⊑) ==> (⊑)) (@uPred_always M).
Proof. intros P Q; apply always_mono. Qed.
Lemma always_impl P Q : □ (P → Q) ⊑ (□ P → □ Q).
Proof.
  apply impl_intro_l; rewrite -always_and.
  apply always_mono, impl_elim with P; auto.
Qed.
Lemma always_eq {A:cofeT} (a b : A) : (□ (a ≡ b))%I ≡ (a ≡ b : uPred M)%I.
Proof.
  apply (anti_symmetric (⊑)); auto using always_elim.
  refine (eq_rewrite _ (λ b, □ (a ≡ b))%I a b _ _); auto.
  { intros n; solve_proper. }
  rewrite -(eq_refl _ True) always_const; auto.
Qed.
Lemma always_and_sep P Q : (□ (P ∧ Q))%I ≡ (□ (P ★ Q))%I.
Proof. apply (anti_symmetric (⊑)); auto using always_and_sep_1. Qed.
Lemma always_and_sep_l P Q : (□ P ∧ Q)%I ≡ (□ P ★ Q)%I.
Proof. apply (anti_symmetric (⊑)); auto using always_and_sep_l_1. Qed.
Lemma always_and_sep_r P Q : (P ∧ □ Q)%I ≡ (P ★ □ Q)%I.
Proof. by rewrite !(commutative _ P) always_and_sep_l. Qed.
Lemma always_sep P Q : (□ (P ★ Q))%I ≡ (□ P ★ □ Q)%I.
Proof. by rewrite -always_and_sep -always_and_sep_l always_and. Qed.
Lemma always_wand P Q : □ (P -★ Q) ⊑ (□ P -★ □ Q).
Proof. by apply wand_intro_r; rewrite -always_sep wand_elim_l. Qed.
Lemma always_sep_dup P : (□ P)%I ≡ (□ P ★ □ P)%I.
Proof. by rewrite -always_sep -always_and_sep (idempotent _). Qed.
Lemma always_wand_impl P Q : (□ (P -★ Q))%I ≡ (□ (P → Q))%I.
Proof.
  apply (anti_symmetric (⊑)); [|by rewrite -impl_wand].
  apply always_intro, impl_intro_r.
  by rewrite always_and_sep_l always_elim wand_elim_l.
Qed.
Lemma always_entails_l P Q : (P ⊑ □ Q) → P ⊑ (□ Q ★ P).
Proof. intros; rewrite -always_and_sep_l; auto. Qed.
Lemma always_entails_r P Q : (P ⊑ □ Q) → P ⊑ (P ★ □ Q).
Proof. intros; rewrite -always_and_sep_r; auto. Qed.

(* Own and valid *)
Lemma own_op (a1 a2 : M) :
  uPred_own (a1 ⋅ a2) ≡ (uPred_own a1 ★ uPred_own a2)%I.
Proof.
  intros x n ?; split.
  * intros [z ?]; exists a1, (a2 ⋅ z); split; [by rewrite (associative op)|].
    split. by exists (unit a1); rewrite cmra_unit_r. by exists z.
  * intros (y1&y2&Hx&[z1 Hy1]&[z2 Hy2]); exists (z1 ⋅ z2).
    by rewrite (associative op _ z1) -(commutative op z1) (associative op z1)
      -(associative op _ a2) (commutative op z1) -Hy1 -Hy2.
Qed.
Lemma always_own_unit (a : M) : (□ uPred_own (unit a))%I ≡ uPred_own (unit a).
Proof.
  intros x n; split; [by apply always_elim|intros [a' Hx]]; simpl.
  rewrite -(cmra_unit_idempotent a) Hx.
  apply cmra_unit_preservingN, cmra_includedN_l.
Qed.
Lemma always_own (a : M) : unit a ≡ a → (□ uPred_own a)%I ≡ uPred_own a.
Proof. by intros <-; rewrite always_own_unit. Qed.
Lemma own_something : True ⊑ ∃ a, uPred_own a.
Proof. intros x [|n] ??; [done|]. by exists x; simpl. Qed.
Lemma own_empty `{Empty M, !CMRAIdentity M} : True ⊑ uPred_own ∅.
Proof. intros x [|n] ??; [done|]. by  exists x; rewrite (left_id _ _). Qed.
Lemma own_valid (a : M) : uPred_own a ⊑ (✓ a).
Proof. move => x n Hv [a' ?]; cofe_subst; eauto using cmra_validN_op_l. Qed.
Lemma valid_intro {A : cmraT} (a : A) : ✓ a → True ⊑ (✓ a).
Proof. by intros ? x n ? _; simpl; apply cmra_valid_validN. Qed.
Lemma valid_elim {A : cmraT} (a : A) : ¬ ✓{1} a → (✓ a) ⊑ False.
Proof. intros Ha x [|n] ??; [|apply Ha, cmra_validN_le with (S n)]; auto. Qed.
Lemma valid_mono {A B : cmraT} (a : A) (b : B) :
  (∀ n, ✓{n} a → ✓{n} b) → (✓ a) ⊑ (✓ b).
Proof. by intros ? x n ?; simpl; auto. Qed.
Lemma always_valid {A : cmraT} (a : A) : (□ (✓ a))%I ≡ (✓ a : uPred M)%I.
Proof. done. Qed.
Lemma own_invalid (a : M) : ¬ ✓{1} a → uPred_own a ⊑ False.
Proof. by intros; rewrite own_valid valid_elim. Qed.

(* Big ops *)
Global Instance uPred_big_and_proper : Proper ((≡) ==> (≡)) (@uPred_big_and M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.
Global Instance uPred_big_sep_proper : Proper ((≡) ==> (≡)) (@uPred_big_sep M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.
Global Instance uPred_big_and_perm : Proper ((≡ₚ) ==> (≡)) (@uPred_big_and M).
Proof.
  induction 1 as [|P Ps Qs ? IH|P Q Ps|]; simpl; auto.
  * by rewrite IH.
  * by rewrite !associative (commutative _ P).
  * etransitivity; eauto.
Qed.
Global Instance uPred_big_sep_perm : Proper ((≡ₚ) ==> (≡)) (@uPred_big_sep M).
Proof.
  induction 1 as [|P Ps Qs ? IH|P Q Ps|]; simpl; auto.
  * by rewrite IH.
  * by rewrite !associative (commutative _ P).
  * etransitivity; eauto.
Qed.
Lemma uPred_big_and_app Ps Qs : (Π∧ (Ps ++ Qs))%I ≡ (Π∧ Ps ∧ Π∧ Qs)%I.
Proof. by induction Ps as [|?? IH]; rewrite /= ?left_id -?associative ?IH. Qed.
Lemma uPred_big_sep_app Ps Qs : (Π★ (Ps ++ Qs))%I ≡ (Π★ Ps ★ Π★ Qs)%I.
Proof. by induction Ps as [|?? IH]; rewrite /= ?left_id -?associative ?IH. Qed.
Lemma uPred_big_sep_and Ps : (Π★ Ps) ⊑ (Π∧ Ps).
Proof. by induction Ps as [|P Ps IH]; simpl; auto. Qed.
Lemma uPred_big_and_elem_of Ps P : P ∈ Ps → (Π∧ Ps) ⊑ P.
Proof. induction 1; simpl; auto. Qed.
Lemma uPred_big_sep_elem_of Ps P : P ∈ Ps → (Π★ Ps) ⊑ P.
Proof. induction 1; simpl; auto. Qed.

(* Timeless *)
Lemma timelessP_spec P : TimelessP P ↔ ∀ x n, ✓{n} x → P 1 x → P n x.
Proof.
  split.
  * intros HP x n ??; induction n as [|[|n]]; auto.
    by destruct (HP x (S (S n))); auto using cmra_validN_S.
  * move=> HP x [|[|n]] /=; auto; left.
    apply HP, uPred_weaken with x (S n); eauto using cmra_validN_le.
Qed.
Global Instance const_timeless φ : TimelessP (■ φ : uPred M)%I.
Proof. by apply timelessP_spec=> x [|n]. Qed.
Global Instance and_timeless P Q: TimelessP P → TimelessP Q → TimelessP (P ∧ Q).
Proof. by intros ??; rewrite /TimelessP later_and or_and_r; apply and_mono. Qed.
Global Instance or_timeless P Q : TimelessP P → TimelessP Q → TimelessP (P ∨ Q).
Proof.
  intros; rewrite /TimelessP later_or (timelessP P) (timelessP Q); eauto 10.
Qed.
Global Instance impl_timeless P Q : TimelessP Q → TimelessP (P → Q).
Proof.
  rewrite !timelessP_spec=> HP x [|n] ? HPQ x' [|n'] ????; auto.
  apply HP, HPQ, uPred_weaken with x' (S n'); eauto using cmra_validN_le.
Qed.
Global Instance sep_timeless P Q: TimelessP P → TimelessP Q → TimelessP (P ★ Q).
Proof.
  intros; rewrite /TimelessP later_sep (timelessP P) (timelessP Q).
  apply wand_elim_l', or_elim; apply wand_intro_r; auto.
  apply wand_elim_r', or_elim; apply wand_intro_r; auto.
  rewrite ?(commutative _ Q); auto.
Qed.
Global Instance wand_timeless P Q : TimelessP Q → TimelessP (P -★ Q).
Proof.
  rewrite !timelessP_spec=> HP x [|n] ? HPQ x' [|n'] ???; auto.
  apply HP, HPQ, uPred_weaken with x' (S n');
    eauto 3 using cmra_validN_le, cmra_validN_op_r.
Qed.
Global Instance forall_timeless {A} (P : A → uPred M) :
  (∀ x, TimelessP (P x)) → TimelessP (∀ x, P x).
Proof. by setoid_rewrite timelessP_spec=>HP x n ?? a; apply HP. Qed.
Global Instance exist_timeless {A} (P : A → uPred M) :
  (∀ x, TimelessP (P x)) → TimelessP (∃ x, P x).
Proof.
  by setoid_rewrite timelessP_spec=>HP x [|n] ?;
    [|intros [a ?]; exists a; apply HP].
Qed.
Global Instance always_timeless P : TimelessP P → TimelessP (□ P).
Proof.
  intros ?; rewrite /TimelessP.
  by rewrite -always_const -!always_later -always_or; apply always_mono.
Qed.
Global Instance eq_timeless {A : cofeT} (a b : A) :
  Timeless a → TimelessP (a ≡ b : uPred M)%I.
Proof. by intro; apply timelessP_spec=> x n ??; apply equiv_dist, timeless. Qed.
Global Instance own_timeless (a : M) : Timeless a → TimelessP (uPred_own a).
Proof.
  intros ?; apply timelessP_spec=> x [|n] ?? //; apply cmra_included_includedN,
    cmra_timeless_included_l; eauto using cmra_validN_le.
Qed.

(* Always stable *)
Notation AS := AlwaysStable.
Global Instance const_always_stable φ : AS (■ φ : uPred M)%I.
Proof. by rewrite /AlwaysStable always_const. Qed.
Global Instance always_always_stable P : AS (□ P).
Proof. by intros; apply always_intro. Qed.
Global Instance and_always_stable P Q: AS P → AS Q → AS (P ∧ Q).
Proof. by intros; rewrite /AlwaysStable always_and; apply and_mono. Qed.
Global Instance or_always_stable P Q : AS P → AS Q → AS (P ∨ Q).
Proof. by intros; rewrite /AlwaysStable always_or; apply or_mono. Qed.
Global Instance sep_always_stable P Q: AS P → AS Q → AS (P ★ Q).
Proof. by intros; rewrite /AlwaysStable always_sep; apply sep_mono. Qed.
Global Instance forall_always_stable {A} (P : A → uPred M) :
  (∀ x, AS (P x)) → AS (∀ x, P x).
Proof. by intros; rewrite /AlwaysStable always_forall; apply forall_mono. Qed.
Global Instance exist_always_stable {A} (P : A → uPred M) :
  (∀ x, AS (P x)) → AS (∃ x, P x).
Proof. by intros; rewrite /AlwaysStable always_exist; apply exist_mono. Qed.
Global Instance eq_always_stable {A : cofeT} (a b : A) : AS (a ≡ b : uPred M)%I.
Proof. by intros; rewrite /AlwaysStable always_eq. Qed.
Global Instance valid_always_stable {A : cmraT} (a : A) : AS (✓ a : uPred M)%I.
Proof. by intros; rewrite /AlwaysStable always_valid. Qed.
Global Instance later_always_stable P : AS P → AS (▷ P).
Proof. by intros; rewrite /AlwaysStable always_later; apply later_mono. Qed.
Global Instance own_unit_always_stable (a : M) : AS (uPred_own (unit a)).
Proof. by rewrite /AlwaysStable always_own_unit. Qed.
Global Instance default_always_stable {A} P (Q : A → uPred M) (mx : option A) :
  AS P → (∀ x, AS (Q x)) → AS (default P mx Q).
Proof. destruct mx; apply _. Qed.

Lemma always_always P `{!AlwaysStable P} : (□ P)%I ≡ P.
Proof. apply (anti_symmetric (⊑)); auto using always_elim. Qed.
Lemma always_intro' P Q `{!AlwaysStable P} : P ⊑ Q → P ⊑ □ Q.
Proof. rewrite -(always_always P); apply always_intro. Qed.
Lemma always_and_sep_l' P Q `{!AlwaysStable P} : (P ∧ Q)%I ≡ (P ★ Q)%I.
Proof. by rewrite -(always_always P) always_and_sep_l. Qed.
Lemma always_and_sep_r' P Q `{!AlwaysStable Q} : (P ∧ Q)%I ≡ (P ★ Q)%I.
Proof. by rewrite -(always_always Q) always_and_sep_r. Qed.
Lemma always_sep_dup' P `{!AlwaysStable P} : P ≡ (P ★ P)%I.
Proof. by rewrite -(always_always P) -always_sep_dup. Qed.
Lemma always_entails_l' P Q `{!AlwaysStable Q} : (P ⊑ Q) → P ⊑ (Q ★ P).
Proof. by rewrite -(always_always Q); apply always_entails_l. Qed.
Lemma always_entails_r' P Q `{!AlwaysStable Q} : (P ⊑ Q) → P ⊑ (P ★ Q).
Proof. by rewrite -(always_always Q); apply always_entails_r. Qed.

End uPred_logic. End uPred.
