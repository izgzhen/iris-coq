From algebra Require Export cmra.
From algebra Require Import functor upred.
Local Hint Extern 10 (_ ≤ _) => omega.

Record agree (A : Type) : Type := Agree {
  agree_car :> nat → A;
  agree_is_valid : nat → Prop;
  agree_valid_S n : agree_is_valid (S n) → agree_is_valid n
}.
Arguments Agree {_} _ _ _.
Arguments agree_car {_} _ _.
Arguments agree_is_valid {_} _ _.

Section agree.
Context {A : cofeT}.

Instance agree_validN : ValidN (agree A) := λ n x,
  agree_is_valid x n ∧ ∀ n', n' ≤ n → x n' ≡{n'}≡ x n.
Lemma agree_valid_le n n' (x : agree A) :
  agree_is_valid x n → n' ≤ n → agree_is_valid x n'.
Proof. induction 2; eauto using agree_valid_S. Qed.
Instance agree_equiv : Equiv (agree A) := λ x y,
  (∀ n, agree_is_valid x n ↔ agree_is_valid y n) ∧
  (∀ n, agree_is_valid x n → x n ≡{n}≡ y n).
Instance agree_dist : Dist (agree A) := λ n x y,
  (∀ n', n' ≤ n → agree_is_valid x n' ↔ agree_is_valid y n') ∧
  (∀ n', n' ≤ n → agree_is_valid x n' → x n' ≡{n'}≡ y n').
Program Instance agree_compl : Compl (agree A) := λ c,
  {| agree_car n := c (S n) n; agree_is_valid n := agree_is_valid (c (S n)) n |}.
Next Obligation.
  intros c n ?. apply (chain_cauchy c n (S (S n))), agree_valid_S; auto.
Qed.
Definition agree_cofe_mixin : CofeMixin (agree A).
Proof.
  split.
  - intros x y; split.
    + by intros Hxy n; split; intros; apply Hxy.
    + by intros Hxy; split; intros; apply Hxy with n.
  - split.
    + by split.
    + by intros x y Hxy; split; intros; symmetry; apply Hxy; auto; apply Hxy.
    + intros x y z Hxy Hyz; split; intros n'; intros.
      * trans (agree_is_valid y n'). by apply Hxy. by apply Hyz.
      * trans (y n'). by apply Hxy. by apply Hyz, Hxy.
  - intros n x y Hxy; split; intros; apply Hxy; auto.
  - intros n c; apply and_wlog_r; intros;
      symmetry; apply (chain_cauchy c); naive_solver.
Qed.
Canonical Structure agreeC := CofeT agree_cofe_mixin.

Lemma agree_car_ne n (x y : agree A) : ✓{n} x → x ≡{n}≡ y → x n ≡{n}≡ y n.
Proof. by intros [??] Hxy; apply Hxy. Qed.
Lemma agree_cauchy n (x : agree A) i : ✓{n} x → i ≤ n → x i ≡{i}≡ x n.
Proof. by intros [? Hx]; apply Hx. Qed.

Program Instance agree_op : Op (agree A) := λ x y,
  {| agree_car := x;
     agree_is_valid n := agree_is_valid x n ∧ agree_is_valid y n ∧ x ≡{n}≡ y |}.
Next Obligation. naive_solver eauto using agree_valid_S, dist_S. Qed.
Instance agree_unit : Unit (agree A) := id.
Instance agree_minus : Minus (agree A) := λ x y, x.
Instance: Comm (≡) (@op (agree A) _).
Proof. intros x y; split; [naive_solver|by intros n (?&?&Hxy); apply Hxy]. Qed.
Lemma agree_idemp (x : agree A) : x ⋅ x ≡ x.
Proof. split; naive_solver. Qed.
Instance: ∀ n : nat, Proper (dist n ==> impl) (@validN (agree A) _ n).
Proof.
  intros n x y Hxy [? Hx]; split; [by apply Hxy|intros n' ?].
  rewrite -(proj2 Hxy n') 1?(Hx n'); eauto using agree_valid_le.
  by apply dist_le with n; try apply Hxy.
Qed.
Instance: ∀ x : agree A, Proper (dist n ==> dist n) (op x).
Proof.
  intros n x y1 y2 [Hy' Hy]; split; [|done].
  split; intros (?&?&Hxy); repeat (intro || split);
    try apply Hy'; eauto using agree_valid_le.
  - etrans; [apply Hxy|apply Hy]; eauto using agree_valid_le.
  - etrans; [apply Hxy|symmetry; apply Hy, Hy'];
      eauto using agree_valid_le.
Qed.
Instance: Proper (dist n ==> dist n ==> dist n) (@op (agree A) _).
Proof. by intros n x1 x2 Hx y1 y2 Hy; rewrite Hy !(comm _ _ y2) Hx. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) op := ne_proper_2 _.
Instance: Assoc (≡) (@op (agree A) _).
Proof.
  intros x y z; split; simpl; intuition;
    repeat match goal with H : agree_is_valid _ _ |- _ => clear H end;
    by cofe_subst; rewrite !agree_idemp.
Qed.
Lemma agree_includedN n (x y : agree A) : x ≼{n} y ↔ y ≡{n}≡ x ⋅ y.
Proof.
  split; [|by intros ?; exists y].
  by intros [z Hz]; rewrite Hz assoc agree_idemp.
Qed.
Definition agree_cmra_mixin : CMRAMixin (agree A).
Proof.
  split; try (apply _ || done).
  - by intros n x1 x2 Hx y1 y2 Hy.
  - intros n x [? Hx]; split; [by apply agree_valid_S|intros n' ?].
    rewrite (Hx n'); last auto.
    symmetry; apply dist_le with n; try apply Hx; auto.
  - intros x; apply agree_idemp.
  - by intros n x y [(?&?&?) ?].
  - by intros n x y; rewrite agree_includedN.
Qed.
Lemma agree_op_inv n (x1 x2 : agree A) : ✓{n} (x1 ⋅ x2) → x1 ≡{n}≡ x2.
Proof. intros Hxy; apply Hxy. Qed.
Lemma agree_valid_includedN n (x y : agree A) : ✓{n} y → x ≼{n} y → x ≡{n}≡ y.
Proof.
  move=> Hval [z Hy]; move: Hval; rewrite Hy.
  by move=> /agree_op_inv->; rewrite agree_idemp.
Qed.
Definition agree_cmra_extend_mixin : CMRAExtendMixin (agree A).
Proof.
  intros n x y1 y2 Hval Hx; exists (x,x); simpl; split.
  - by rewrite agree_idemp.
  - by move: Hval; rewrite Hx; move=> /agree_op_inv->; rewrite agree_idemp.
Qed.
Canonical Structure agreeRA : cmraT :=
  CMRAT agree_cofe_mixin agree_cmra_mixin agree_cmra_extend_mixin.

Program Definition to_agree (x : A) : agree A :=
  {| agree_car n := x; agree_is_valid n := True |}.
Solve Obligations with done.
Global Instance to_agree_ne n : Proper (dist n ==> dist n) to_agree.
Proof. intros x1 x2 Hx; split; naive_solver eauto using @dist_le. Qed.
Global Instance to_agree_proper : Proper ((≡) ==> (≡)) to_agree := ne_proper _.
Global Instance to_agree_inj n : Inj (dist n) (dist n) (to_agree).
Proof. by intros x y [_ Hxy]; apply Hxy. Qed.
Lemma to_agree_car n (x : agree A) : ✓{n} x → to_agree (x n) ≡{n}≡ x.
Proof. intros [??]; split; naive_solver eauto using agree_valid_le. Qed.

(** Internalized properties *)
Lemma agree_equivI {M} a b : (to_agree a ≡ to_agree b)%I ≡ (a ≡ b : uPred M)%I.
Proof. do 2 split. by intros [? Hv]; apply (Hv n). apply: to_agree_ne. Qed.
Lemma agree_validI {M} x y : ✓ (x ⋅ y) ⊑ (x ≡ y : uPred M).
Proof. split=> r n _ ?; by apply: agree_op_inv. Qed.
End agree.

Arguments agreeC : clear implicits.
Arguments agreeRA : clear implicits.

Program Definition agree_map {A B} (f : A → B) (x : agree A) : agree B :=
  {| agree_car n := f (x n); agree_is_valid := agree_is_valid x |}.
Solve Obligations with auto using agree_valid_S.
Lemma agree_map_id {A} (x : agree A) : agree_map id x = x.
Proof. by destruct x. Qed.
Lemma agree_map_compose {A B C} (f : A → B) (g : B → C) (x : agree A) :
  agree_map (g ∘ f) x = agree_map g (agree_map f x).
Proof. done. Qed.

Section agree_map.
  Context {A B : cofeT} (f : A → B) `{Hf: ∀ n, Proper (dist n ==> dist n) f}.
  Global Instance agree_map_ne n : Proper (dist n ==> dist n) (agree_map f).
  Proof. by intros x1 x2 Hx; split; simpl; intros; [apply Hx|apply Hf, Hx]. Qed.
  Global Instance agree_map_proper :
    Proper ((≡) ==> (≡)) (agree_map f) := ne_proper _.
  Lemma agree_map_ext (g : A → B) x :
    (∀ x, f x ≡ g x) → agree_map f x ≡ agree_map g x.
  Proof. by intros Hfg; split; simpl; intros; rewrite ?Hfg. Qed.
  Global Instance agree_map_monotone : CMRAMonotone (agree_map f).
  Proof.
    split; [|by intros n x [? Hx]; split; simpl; [|by intros n' ?; rewrite Hx]].
    intros n x y; rewrite !agree_includedN; intros Hy; rewrite Hy.
    split; last done; split; simpl; last tauto.
    by intros (?&?&Hxy); repeat split; intros;
       try apply Hxy; try apply Hf; eauto using @agree_valid_le.
  Qed.
End agree_map.

Definition agreeC_map {A B} (f : A -n> B) : agreeC A -n> agreeC B :=
  CofeMor (agree_map f : agreeC A → agreeC B).
Instance agreeC_map_ne A B n : Proper (dist n ==> dist n) (@agreeC_map A B).
Proof.
  intros f g Hfg x; split; simpl; intros; first done.
  by apply dist_le with n; try apply Hfg.
Qed.

Program Definition agreeF : iFunctor :=
  {| ifunctor_car := agreeRA; ifunctor_map := @agreeC_map |}.
Solve Obligations with done.
