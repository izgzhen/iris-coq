Require Import cmra cofe_instances.
Local Hint Extern 1 (_ ≼ _) => etransitivity; [eassumption|].
Local Hint Extern 1 (_ ≼ _) => etransitivity; [|eassumption].
Local Hint Extern 10 (_ ≤ _) => omega.

Structure iProp (A : cmraT) : Type := IProp {
  iprop_holds :> nat → A -> Prop;
  iprop_ne x1 x2 n : iprop_holds n x1 → x1 ={n}= x2 → iprop_holds n x2;
  iprop_weaken x1 x2 n1 n2 :
    x1 ≼ x2 → n2 ≤ n1 → validN n2 x2 → iprop_holds n1 x1 → iprop_holds n2 x2
}.
Add Printing Constructor iProp.
Instance: Params (@iprop_holds) 3.

Instance iprop_equiv (A : cmraT) : Equiv (iProp A) := λ P Q, ∀ x n,
  validN n x → P n x ↔ Q n x.
Instance iprop_dist (A : cmraT) : Dist (iProp A) := λ n P Q, ∀ x n',
  n' < n → validN n' x → P n' x ↔ Q n' x.
Program Instance iprop_compl (A : cmraT) : Compl (iProp A) := λ c,
  {| iprop_holds n x := c (S n) n x |}.
Next Obligation. by intros A c x y n ??; simpl in *; apply iprop_ne with x. Qed.
Next Obligation.
  intros A c x1 x2 n1 n2 ????; simpl in *.
  apply (chain_cauchy c (S n2) (S n1)); eauto using iprop_weaken, cmra_valid_le.
Qed.
Instance iprop_cofe (A : cmraT) : Cofe (iProp A).
Proof.
  split.
  * intros P Q; split; [by intros HPQ n x i ??; apply HPQ|].
    intros HPQ x n ?; apply HPQ with (S n); auto.
  * intros n; split.
    + by intros P x i.
    + by intros P Q HPQ x i ??; symmetry; apply HPQ.
    + by intros P Q Q' HP HQ x i ??; transitivity (Q i x); [apply HP|apply HQ].
  * intros n P Q HPQ x i ??; apply HPQ; auto.
  * intros P Q x i ??; lia.
  * intros c n x i ??; apply (chain_cauchy c (S i) n); auto.
Qed.
Instance iprop_holds_ne {A} (P : iProp A) n : Proper (dist n ==> iff) (P n).
Proof. intros x1 x2 Hx; split; eauto using iprop_ne. Qed.
Instance iprop_holds_proper {A} (P : iProp A) n : Proper ((≡) ==> iff) (P n).
Proof. by intros x1 x2 Hx; apply iprop_holds_ne, equiv_dist. Qed.
Definition iPropC (A : cmraT) : cofeT := CofeT (iProp A).

(** functor *)
Program Definition iProp_map {A B : cmraT} (f: B -n> A) `{!CMRAPreserving f}
  (P : iProp A) : iProp B := {| iprop_holds n x := P n (f x) |}.
Next Obligation. by intros A B f ? P y1 y2 n ? Hy; simpl; rewrite <-Hy. Qed.
Next Obligation.
  by intros A B f ? P y1 y2 n i ???; simpl; apply iprop_weaken; auto;
    apply validN_preserving || apply included_preserving.
Qed.

(** logical entailement *)
Instance iprop_entails {A} : SubsetEq (iProp A) := λ P Q, ∀ x n,
  validN n x → P n x → Q n x.

(** logical connectives *)
Program Definition iprop_const {A} (P : Prop) : iProp A :=
  {| iprop_holds n x := P |}.
Solve Obligations with done.

Program Definition iprop_and {A} (P Q : iProp A) : iProp A :=
  {| iprop_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 using iprop_ne, iprop_weaken.
Program Definition iprop_or {A} (P Q : iProp A) : iProp A :=
  {| iprop_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 using iprop_ne, iprop_weaken.
Program Definition iprop_impl {A} (P Q : iProp A) : iProp A :=
  {| iprop_holds n x := ∀ x' n',
       x ≼ x' → n' ≤ n → validN n' x' → P n' x' → Q n' x' |}.
Next Obligation.
  intros A P Q x1' x1 n1 HPQ Hx1 x2 n2 ????.
  destruct (cmra_included_dist_l x1 x2 x1' n1) as (x2'&?&Hx2); auto.
  assert (x2' ={n2}= x2) as Hx2' by (by apply dist_le with n1).
  assert (validN n2 x2') by (by rewrite Hx2'); rewrite <-Hx2'.
  by apply HPQ, iprop_weaken with x2' n2, iprop_ne with x2.
Qed.
Next Obligation. naive_solver eauto 2 with lia. Qed.

Program Definition iprop_forall {A B} (P : A → iProp B) : iProp B :=
  {| iprop_holds n x := ∀ a, P a n x |}.
Solve Obligations with naive_solver eauto 2 using iprop_ne, iprop_weaken.
Program Definition iprop_exist {A B} (P : A → iProp B) : iProp B :=
  {| iprop_holds n x := ∃ a, P a n x |}.
Solve Obligations with naive_solver eauto 2 using iprop_ne, iprop_weaken.

Program Definition iprop_eq {A} {B : cofeT} (b1 b2 : B) : iProp A :=
  {| iprop_holds n x := b1 ={n}= b2 |}.
Solve Obligations with naive_solver eauto 2 using (dist_le (A:=B)).

Program Definition iprop_sep {A} (P Q : iProp A) : iProp A :=
  {| iprop_holds n x := ∃ x1 x2, x ={n}= x1 ⋅ x2 ∧ P n x1 ∧ Q n x2 |}.
Next Obligation.
  by intros A P Q x y n (x1&x2&?&?&?) Hxy; exists x1, x2; rewrite <-Hxy.
Qed.
Next Obligation.
  intros A P Q x y n1 n2 Hxy ?? (x1&x2&Hx&?&?).
  assert (∃ x2', y ={n2}= x1 ⋅ x2' ∧ x2 ≼ x2') as (x2'&Hy&?).
  { rewrite ra_included_spec in Hxy; destruct Hxy as [z Hy].
    exists (x2 ⋅ z); split; eauto using ra_included_l.
    apply dist_le with n1; auto. by rewrite (associative op), <-Hx, Hy. }
  exists x1, x2'; split_ands; auto.
  * apply iprop_weaken with x1 n1; auto.
    by apply cmra_valid_op_l with x2'; rewrite <-Hy.
  * apply iprop_weaken with x2 n1; auto.
    by apply cmra_valid_op_r with x1; rewrite <-Hy.
Qed.

Program Definition iprop_wand {A} (P Q : iProp A) : iProp A :=
  {| iprop_holds n x := ∀ x' n',
       n' ≤ n → validN n' (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Next Obligation.
  intros A P Q x1 x2 n1 HPQ Hx x3 n2 ???; simpl in *.
  rewrite <-(dist_le _ _ _ _ Hx) by done; apply HPQ; auto.
  by rewrite (dist_le _ _ _ n2 Hx).
Qed.
Next Obligation.
  intros A P Q x1 x2 n1 n2 ??? HPQ x3 n3 ???; simpl in *.
  apply iprop_weaken with (x1 ⋅ x3) n3; auto using ra_preserving_r.
  apply HPQ; auto.
  apply cmra_valid_included with (x2 ⋅ x3); auto using ra_preserving_r.
Qed.

Program Definition iprop_later {A} (P : iProp A) : iProp A :=
  {| iprop_holds n x := match n return _ with 0 => True | S n' => P n' x end |}.
Next Obligation. intros A P ?? [|n]; eauto using iprop_ne,(dist_le (A:=A)). Qed.
Next Obligation.
  intros A P x1 x2 [|n1] [|n2] ????; auto with lia.
  apply iprop_weaken with x1 n1; eauto using cmra_valid_S.
Qed.
Program Definition iprop_always {A} (P : iProp A) : iProp A :=
  {| iprop_holds n x := P n (unit x) |}.
Next Obligation. by intros A P x1 x2 n ? Hx; simpl in *; rewrite <-Hx. Qed.
Next Obligation.
  intros A P x1 x2 n1 n2 ????; eapply iprop_weaken with (unit x1) n1;
    auto using ra_unit_preserving, cmra_unit_valid.
Qed.

Definition iprop_fixpoint {A} (P : iProp A → iProp A)
  `{!Contractive P} : iProp A := fixpoint P (iprop_const True).

Delimit Scope iprop_scope with I.
Bind Scope iprop_scope with iProp.
Arguments iprop_holds {_} _%I _ _.

Notation "'False'" := (iprop_const False) : iprop_scope.
Notation "'True'" := (iprop_const True) : iprop_scope.
Infix "∧" := iprop_and : iprop_scope.
Infix "∨" := iprop_or : iprop_scope.
Infix "→" := iprop_impl : iprop_scope.
Infix "★" := iprop_sep (at level 80, right associativity) : iprop_scope.
Infix "-★" := iprop_wand (at level 90) : iprop_scope.
Notation "∀ x .. y , P" :=
  (iprop_forall (λ x, .. (iprop_forall (λ y, P)) ..)) : iprop_scope.
Notation "∃ x .. y , P" :=
  (iprop_exist (λ x, .. (iprop_exist (λ y, P)) ..)) : iprop_scope.
Notation "▷ P" := (iprop_later P) (at level 20) : iprop_scope.
Notation "□ P" := (iprop_always P) (at level 20) : iprop_scope.

Section logic.
Context {A : cmraT}.
Implicit Types P Q : iProp A.

Global Instance iprop_preorder : PreOrder ((⊆) : relation (iProp A)).
Proof. split. by intros P x i. by intros P Q Q' HP HQ x i ??; apply HQ, HP. Qed.
Lemma iprop_equiv_spec P Q : P ≡ Q ↔ P ⊆ Q ∧ Q ⊆ P.
Proof.
  split.
  * intros HPQ; split; intros x i; apply HPQ.
  * by intros [HPQ HQP]; intros x i ?; split; [apply HPQ|apply HQP].
Qed.

(** Non-expansiveness *)
Global Instance iprop_const_proper : Proper (iff ==> (≡)) (@iprop_const A).
Proof. intros P Q HPQ ???; apply HPQ. Qed.
Global Instance iprop_and_ne n :
  Proper (dist n ==> dist n ==> dist n) (@iprop_and A).
Proof.
  intros P P' HP Q Q' HQ; split; intros [??]; split; by apply HP || by apply HQ.
Qed.
Global Instance iprop_and_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (@iprop_and A) := ne_proper_2 _.
Global Instance iprop_or_ne n :
  Proper (dist n ==> dist n ==> dist n) (@iprop_or A).
Proof.
  intros P P' HP Q Q' HQ; split; intros [?|?];
    first [by left; apply HP | by right; apply HQ].
Qed.
Global Instance iprop_or_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (@iprop_or A) := ne_proper_2 _.
Global Instance iprop_impl_ne n :
  Proper (dist n ==> dist n ==> dist n) (@iprop_impl A).
Proof.
  intros P P' HP Q Q' HQ; split; intros HPQ x' n'' ????; apply HQ,HPQ,HP; auto.
Qed.
Global Instance iprop_impl_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (@iprop_impl A) := ne_proper_2 _.
Global Instance iprop_sep_ne n :
  Proper (dist n ==> dist n ==> dist n) (@iprop_sep A).
Proof.
  intros P P' HP Q Q' HQ x n' ? Hx'; split; intros (x1&x2&Hx&?&?);
    exists x1, x2; rewrite  Hx in Hx'; split_ands; try apply HP; try apply HQ;
    eauto using cmra_valid_op_l, cmra_valid_op_r.
Qed.
Global Instance iprop_sep_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (@iprop_sep A) := ne_proper_2 _.
Global Instance iprop_wand_ne n :
  Proper (dist n ==> dist n ==> dist n) (@iprop_wand A).
Proof.
  intros P P' HP Q Q' HQ x n' ??; split; intros HPQ x' n'' ???;
    apply HQ, HPQ, HP; eauto using cmra_valid_op_r.
Qed.
Global Instance iprop_wand_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (@iprop_wand A) := ne_proper_2 _.
Global Instance iprop_eq_ne {B : cofeT} n :
  Proper (dist n ==> dist n ==> dist n) (@iprop_eq A B).
Proof.
  intros x x' Hx y y' Hy z n'; split; intros; simpl in *.
  * by rewrite <-(dist_le _ _ _ _ Hx), <-(dist_le _ _ _ _ Hy) by auto.
  * by rewrite (dist_le _ _ _ _ Hx), (dist_le _ _ _ _ Hy) by auto.
Qed.
Global Instance iprop_eq_proper {B : cofeT} :
  Proper ((≡) ==> (≡) ==> (≡)) (@iprop_eq A B) := ne_proper_2 _.
Global Instance iprop_forall_ne {B : cofeT} :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@iprop_forall B A).
Proof. by intros n P1 P2 HP12 x n'; split; intros HP a; apply HP12. Qed.
Global Instance iprop_forall_proper {B : cofeT} :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@iprop_forall B A).
Proof. by intros P1 P2 HP12 x n'; split; intros HP a; apply HP12. Qed.
Global Instance iprop_exists_ne {B : cofeT} :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@iprop_exist B A).
Proof.
  by intros n P1 P2 HP12 x n'; split; intros [a HP]; exists a; apply HP12.
Qed.
Global Instance iprop_exist_proper {B : cofeT} :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@iprop_exist B A).
Proof.
  by intros P1 P2 HP12 x n'; split; intros [a HP]; exists a; apply HP12.
Qed.

(** Introduction and elimination rules *)
Lemma iprop_True_intro P : P ⊆ True%I.
Proof. done. Qed.
Lemma iprop_False_elim P : False%I ⊆ P.
Proof. by intros x n ?. Qed.
Lemma iprop_and_elim_l P Q : (P ∧ Q)%I ⊆ P.
Proof. by intros x n ? [??]. Qed.
Lemma iprop_and_elim_r P Q : (P ∧ Q)%I ⊆ Q.
Proof. by intros x n ? [??]. Qed.
Lemma iprop_and_intro R P Q : R ⊆ P → R ⊆ Q → R ⊆ (P ∧ Q)%I.
Proof. intros HP HQ x n ??; split. by apply HP. by apply HQ. Qed.
Lemma iprop_or_intro_l P Q : P ⊆ (P ∨ Q)%I.
Proof. by left. Qed.
Lemma iprop_or_intro_r P Q : Q ⊆ (P ∨ Q)%I.
Proof. by right. Qed.
Lemma iprop_or_elim R P Q : P ⊆ R → Q ⊆ R → (P ∨ Q)%I ⊆ R.
Proof. intros HP HQ x n ? [?|?]. by apply HP. by apply HQ. Qed.
Lemma iprop_impl_intro P Q R : (R ∧ P)%I ⊆ Q → R ⊆ (P → Q)%I.
Proof.
  intros HQ x n ?? x' n' ????; apply HQ; naive_solver eauto using iprop_weaken.
Qed.
Lemma iprop_impl_elim P Q : ((P → Q) ∧ P)%I ⊆ Q.
Proof. by intros x n ? [HQ HP]; apply HQ. Qed.
Lemma iprop_forall_intro P `(Q: B → iProp A): (∀ b, P ⊆ Q b) → P ⊆ (∀ b, Q b)%I.
Proof. by intros HPQ x n ?? b; apply HPQ. Qed.
Lemma iprop_forall_elim `(P : B → iProp A) b : (∀ b, P b)%I ⊆ P b.
Proof. intros x n ? HP; apply HP. Qed.
Lemma iprop_exist_intro `(P : B → iProp A) b : P b ⊆ (∃ b, P b)%I.
Proof. by intros x n ??; exists b. Qed.
Lemma iprop_exist_elim `(P : B → iProp A) Q : (∀ b, P b ⊆ Q) → (∃ b, P b)%I ⊆ Q.
Proof. by intros HPQ x n ? [b ?]; apply HPQ with b. Qed.

(* BI connectives *)
Lemma iprop_sep_elim_l P Q : (P ★ Q)%I ⊆ P.
Proof.
  intros x n Hvalid (x1&x2&Hx&?&?); rewrite Hx in Hvalid |- *.
  by apply iprop_weaken with x1 n; auto using ra_included_l.
Qed.
Global Instance iprop_sep_left_id : LeftId (≡) True%I (@iprop_sep A).
Proof.
  intros P x n Hvalid; split.
  * intros (x1&x2&Hx&_&?); rewrite Hx in Hvalid |- *.
    apply iprop_weaken with x2 n; auto using ra_included_r.
  * by intros ?; exists (unit x), x; rewrite ra_unit_l.
Qed. 
Global Instance iprop_sep_commutative : Commutative (≡) (@iprop_sep A).
Proof.
  by intros P Q x n ?; split;
    intros (x1&x2&?&?&?); exists x2, x1; rewrite (commutative op).
Qed.
Global Instance iprop_sep_associative : Associative (≡) (@iprop_sep A).
Proof.
  intros P Q R x n ?; split.
  * intros (x1&x2&Hx&?&y1&y2&Hy&?&?); exists (x1 ⋅ y1), y2; split_ands; auto.
    + by rewrite <-(associative op), <-Hy, <-Hx.
    + by exists x1, y1.
  * intros (x1&x2&Hx&(y1&y2&Hy&?&?)&?); exists y1, (y2 ⋅ x2); split_ands; auto.
    + by rewrite (associative op), <-Hy, <-Hx.
    + by exists y2, x2.
Qed.
Lemma iprop_wand_intro P Q R : (R ★ P)%I ⊆ Q → R ⊆ (P -★ Q)%I.
Proof.
  intros HPQ x n ?? x' n' ???; apply HPQ; auto.
  exists x, x'; split_ands; auto.
  eapply iprop_weaken with x n; eauto using cmra_valid_op_l.
Qed.
Lemma iprop_wand_elim P Q : ((P -★ Q) ★ P)%I ⊆ Q.
Proof.
  by intros x n Hvalid (x1&x2&Hx&HPQ&?); rewrite Hx in Hvalid |- *; apply HPQ.
Qed.
Lemma iprop_sep_or P Q R : ((P ∨ Q) ★ R)%I ≡ ((P ★ R) ∨ (Q ★ R))%I.
Proof.
  split; [by intros (x1&x2&Hx&[?|?]&?); [left|right]; exists x1, x2|].
  intros [(x1&x2&Hx&?&?)|(x1&x2&Hx&?&?)]; exists x1, x2; split_ands;
    first [by left | by right | done].
Qed.
Lemma iprop_sep_and P Q R : ((P ∧ Q) ★ R)%I ⊆ ((P ★ R) ∧ (Q ★ R))%I.
Proof. by intros x n ? (x1&x2&Hx&[??]&?); split; exists x1, x2. Qed.
Lemma iprop_sep_exist {B} (P : B → iProp A) Q :
  ((∃ b, P b) ★ Q)%I ≡ (∃ b, P b ★ Q)%I.
Proof.
  split; [by intros (x1&x2&Hx&[b ?]&?); exists b, x1, x2|].
  intros [b (x1&x2&Hx&?&?)]; exists x1, x2; split_ands; by try exists b.
Qed.
Lemma iprop_sep_forall `(P : B → iProp A) Q :
  ((∀ b, P b) ★ Q)%I ⊆ (∀ b, P b ★ Q)%I.
Proof. by intros x n ? (x1&x2&Hx&?&?); intros b; exists x1, x2. Qed.

(* Later *)
Global Instance iprop_later_contractive : Contractive (@iprop_later A).
Proof.
  intros n P Q HPQ x [|n'] ??; simpl; [done|].
  apply HPQ; eauto using cmra_valid_S.
Qed.
Lemma iprop_later_weaken P : P ⊆ (▷ P)%I.
Proof.
  intros x [|n] ??; simpl in *; [done|].
  apply iprop_weaken with x (S n); auto using cmra_valid_S.
Qed.
Lemma iprop_lub P : (▷ P → P)%I ⊆ P.
Proof.
  intros x n ? HP; induction n as [|n IH]; [by apply HP|].
  apply HP, IH, iprop_weaken with x (S n); eauto using cmra_valid_S.
Qed.
Lemma iprop_later_impl P Q : (▷ (P → Q))%I ⊆ (▷ P → ▷ Q)%I.
Proof.
  intros x [|n] ? HPQ x' [|n'] ???; auto with lia.
  apply HPQ; auto using cmra_valid_S.
Qed.
Lemma iprop_later_and P Q : (▷ (P ∧ Q))%I ≡ (▷ P ∧ ▷ Q)%I.
Proof. by intros x [|n]; split. Qed.
Lemma iprop_later_or P Q : (▷ (P ∨ Q))%I ≡ (▷ P ∨ ▷ Q)%I.
Proof. intros x [|n]; simpl; tauto. Qed.
Lemma iprop_later_forall `(P : B → iProp A) : (▷ ∀ b, P b)%I ≡ (∀ b, ▷ P b)%I.
Proof. by intros x [|n]. Qed.
Lemma iprop_later_exist `(P : B → iProp A) : (∃ b, ▷ P b)%I ⊆ (▷ ∃ b, P b)%I.
Proof. by intros x [|n]. Qed.
Lemma iprop_later_exist' `{Inhabited B} (P : B → iProp A) :
  (▷ ∃ b, P b)%I ≡ (∃ b, ▷ P b)%I.
Proof.
  intros x [|n]; split; try done.
  by destruct (_ : Inhabited B) as [b]; exists b.
Qed.
Lemma iprop_later_sep P Q : (▷ (P ★ Q))%I ≡ (▷ P ★ ▷ Q)%I.
Proof.
  intros x n ?; split.
  * destruct n as [|n]; simpl; [by exists x, x|intros (x1&x2&Hx&?&?)].
    destruct (cmra_extend_op x x1 x2 n)
      as ([y1 y2]&Hx'&Hy1&Hy2); auto using cmra_valid_S; simpl in *.
    exists y1, y2; split; [by rewrite Hx'|by rewrite Hy1, Hy2].
  * destruct n as [|n]; simpl; [done|intros (x1&x2&Hx&?&?)].
    exists x1, x2; eauto using (dist_S (A:=A)).
Qed.

(* Always *)
Lemma iprop_always_necessity P : (□ P)%I ⊆ P.
Proof.
  intros x n ??; apply iprop_weaken with (unit x) n;auto using ra_included_unit.
Qed.
Lemma iprop_always_intro P Q : (□ P)%I ⊆ Q → (□ P)%I ⊆ (□ Q)%I.
Proof.
  intros HPQ x n ??; apply HPQ; simpl in *; auto using cmra_unit_valid.
  by rewrite ra_unit_idempotent.
Qed.
Lemma iprop_always_impl P Q : (□ (P → Q))%I ⊆ (□P → □Q)%I.
Proof.
  intros x n ? HPQ x' n' ???.
  apply HPQ; auto using ra_unit_preserving, cmra_unit_valid.
Qed.
Lemma iprop_always_and P Q : (□ (P ∧ Q))%I ≡ (□ P ∧ □ Q)%I.
Proof. done. Qed.
Lemma iprop_always_or P Q : (□ (P ∨ Q))%I ≡ (□ P ∨ □ Q)%I.
Proof. done. Qed.
Lemma iprop_always_forall `(P : B → iProp A) : (□ ∀ b, P b)%I ≡ (∀ b, □ P b)%I.
Proof. done. Qed.
Lemma iprop_always_exist `(P : B → iProp A) : (□ ∃ b, P b)%I ≡ (∃ b, □ P b)%I.
Proof. done. Qed.
Lemma iprop_always_and_always_box P Q : (□ P ∧ Q)%I ⊆ (□ P ★ Q)%I.
Proof.
  intros x n ? [??]; exists (unit x), x; simpl in *.
  by rewrite ra_unit_l, ra_unit_idempotent.
Qed.

(* Fix *)
Lemma iprop_fixpoint_unfold (P : iProp A → iProp A) `{!Contractive P} :
  iprop_fixpoint P ≡ P (iprop_fixpoint P).
Proof. apply fixpoint_unfold. Qed.
End logic.

