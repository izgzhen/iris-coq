Require Export iris.cmra.
Local Hint Extern 10 (_ ≤ _) => omega.

Record agree A `{Dist A} := Agree {
  agree_car :> nat → A;
  agree_is_valid : nat → Prop;
  agree_valid_0 : agree_is_valid 0;
  agree_valid_S n : agree_is_valid (S n) → agree_is_valid n
}.
Arguments Agree {_ _} _ _ _ _.
Arguments agree_car {_ _} _ _.
Arguments agree_is_valid {_ _} _ _.

Section agree.
Context `{Cofe A}.

Global Instance agree_validN : ValidN (agree A) := λ n x,
  agree_is_valid x n ∧ ∀ n', n' ≤ n → x n' ={n'}= x n.
Lemma agree_valid_le (x : agree A) n n' :
  agree_is_valid x n → n' ≤ n → agree_is_valid x n'.
Proof. induction 2; eauto using agree_valid_S. Qed.
Global Instance agree_valid : Valid (agree A) := λ x, ∀ n, validN n x.
Global Instance agree_equiv : Equiv (agree A) := λ x y,
  (∀ n, agree_is_valid x n ↔ agree_is_valid y n) ∧
  (∀ n, agree_is_valid x n → x n ={n}= y n).
Global Instance agree_dist : Dist (agree A) := λ n x y,
  (∀ n', n' ≤ n → agree_is_valid x n' ↔ agree_is_valid y n') ∧
  (∀ n', n' ≤ n → agree_is_valid x n' → x n' ={n'}= y n').
Global Program Instance agree_compl : Compl (agree A) := λ c,
  {| agree_car n := c n n; agree_is_valid n := agree_is_valid (c n) n |}.
Next Obligation. intros; apply agree_valid_0. Qed.
Next Obligation.
  intros c n ?; apply (chain_cauchy c n (S n)), agree_valid_S; auto.
Qed.
Instance agree_cofe : Cofe (agree A).
Proof.
  split.
  * intros x y; split.
    + by intros Hxy n; split; intros; apply Hxy.
    + by intros Hxy; split; intros; apply Hxy with n.
  * split.
    + by split.
    + by intros x y Hxy; split; intros; symmetry; apply Hxy; auto; apply Hxy.
    + intros x y z Hxy Hyz; split; intros n'; intros.
      - transitivity (agree_is_valid y n'). by apply Hxy. by apply Hyz.
      - transitivity (y n'). by apply Hxy. by apply Hyz, Hxy.
  * intros n x y Hxy; split; intros; apply Hxy; auto.
  * intros x y; split; intros n'; rewrite Nat.le_0_r; intros ->; [|done].
    by split; intros; apply agree_valid_0.
  * by intros c n; split; intros; apply (chain_cauchy c).
Qed.

Global Program Instance agree_op : Op (agree A) := λ x y,
  {| agree_car := x;
     agree_is_valid n := agree_is_valid x n ∧ agree_is_valid y n ∧ x ={n}= y |}.
Next Obligation. by intros; simpl; split_ands; try apply agree_valid_0. Qed.
Next Obligation. naive_solver eauto using agree_valid_S, dist_S. Qed.
Global Instance agree_unit : Unit (agree A) := id.
Global Instance agree_minus : Minus (agree A) := λ x y, x.
Global Instance agree_included : Included (agree A) := λ x y, y ≡ x ⋅ y.
Instance: Commutative (≡) (@op (agree A) _).
Proof. intros x y; split; [naive_solver|by intros n (?&?&Hxy); apply Hxy]. Qed.
Definition agree_idempotent (x : agree A) : x ⋅ x ≡ x.
Proof. split; naive_solver. Qed.
Instance: ∀ x : agree A, Proper (dist n ==> dist n) (op x).
Proof.
  intros n x y1 y2 [Hy' Hy]; split; [|done].
  split; intros (?&?&Hxy); repeat (intro || split);
    try apply Hy'; eauto using agree_valid_le.
  * etransitivity; [apply Hxy|apply Hy]; eauto using agree_valid_le.
  * etransitivity; [apply Hxy|symmetry; apply Hy, Hy'];
      eauto using agree_valid_le.
Qed.
Instance: Proper (dist n ==> dist n ==> dist n) op.
Proof. by intros n x1 x2 Hx y1 y2 Hy; rewrite Hy,!(commutative _ _ y2), Hx. Qed.
Instance: Proper ((≡) ==> (≡) ==> (≡)) op := ne_proper_2 _.
Instance: Associative (≡) (@op (agree A) _).
Proof.
  intros x y z; split; simpl; intuition;
    repeat match goal with H : agree_is_valid _ _ |- _ => clear H end;
    by cofe_subst; rewrite !agree_idempotent.
Qed.
Global Instance agree_cmra : CMRA (agree A).
Proof.
  split; try (apply _ || done).
  * intros n x y Hxy [? Hx]; split; [by apply Hxy|intros n' ?].
    rewrite <-(proj2 Hxy n'), (Hx n') by eauto using agree_valid_le.
    by apply dist_le with n; try apply Hxy.
  * by intros n x1 x2 Hx y1 y2 Hy.
  * by intros x y1 y2 Hy ?; do 2 red; rewrite <-Hy.
  * intros x; split; [apply agree_valid_0|].
    by intros n'; rewrite Nat.le_0_r; intros ->.
  * intros n x [? Hx]; split; [by apply agree_valid_S|intros n' ?].
    rewrite (Hx n') by auto; symmetry; apply dist_le with n; try apply Hx; auto.
  * intros x; apply agree_idempotent.
  * intros x y; change (x ⋅ y ≡ x ⋅ (x ⋅ y)).
    by rewrite (associative _), agree_idempotent.
  * by intros x y n [(?&?&?) ?].
  * by intros x y; do 2 red; rewrite (associative _), agree_idempotent.
Qed.
Lemma agree_op_inv (x y1 y2 : agree A) n :
  validN n x → x ={n}= y1 ⋅ y2 → y1 ={n}= y2.
Proof. by intros [??] Hxy; apply Hxy. Qed.
Global Instance agree_extend : CMRAExtend (agree A).
Proof.
  intros x y1 y2 n ? Hx; exists (x,x); simpl; split.
  * by rewrite agree_idempotent.
  * by rewrite Hx, (agree_op_inv x y1 y2), agree_idempotent by done.
Qed.
Program Definition to_agree (x : A) : agree A :=
  {| agree_car n := x; agree_is_valid n := True |}.
Solve Obligations with done.
Global Instance to_agree_ne n : Proper (dist n ==> dist n) to_agree.
Proof. intros x1 x2 Hx; split; naive_solver eauto using @dist_le. Qed.
Lemma agree_car_ne (x y : agree A) n : validN n x → x ={n}= y → x n ={n}= y n.
Proof. by intros [??] Hxy; apply Hxy. Qed.
Lemma agree_cauchy (x : agree A) n i : n ≤ i → validN i x → x n ={n}= x i.
Proof. by intros ? [? Hx]; apply Hx. Qed.
Lemma agree_to_agree_inj (x y : agree A) a n :
  validN n x → x ={n}= to_agree a ⋅ y → x n ={n}= a.
Proof.
  by intros; transitivity ((to_agree a ⋅ y) n); [by apply agree_car_ne|].
Qed.
End agree.

Section agree_map.
  Context `{Cofe A,Cofe B} (f : A → B) `{Hf: ∀ n, Proper (dist n ==> dist n) f}.
  Program Definition agree_map (x : agree A) : agree B :=
    {| agree_car n := f (x n); agree_is_valid := agree_is_valid x |}.
  Solve Obligations with auto using agree_valid_0, agree_valid_S.
  Global Instance agree_map_ne n : Proper (dist n ==> dist n) agree_map.
  Proof. by intros x1 x2 Hx; split; simpl; intros; [apply Hx|apply Hf, Hx]. Qed.
  Global Instance agree_map_proper: Proper ((≡)==>(≡)) agree_map := ne_proper _.
  Global Instance agree_map_preserving : CMRAPreserving agree_map.
  Proof.
    split; [|by intros n x [? Hx]; split; simpl; [|by intros n' ?; rewrite Hx]].
    intros x y; unfold included, agree_included; intros Hy; rewrite Hy.
    split; [split|done].
    * by intros (?&?&Hxy); repeat (intro || split);
        try apply Hxy; try apply Hf; eauto using @agree_valid_le.
    * by intros (?&(?&?&Hxy)&_); repeat split;
        try apply Hxy; eauto using agree_valid_le.
  Qed.
End agree_map.
Lemma agree_map_id `{Cofe A} (x : agree A) : agree_map id x = x.
Proof. by destruct x. Qed.
Lemma agree_map_compose `{Cofe A, Cofe B, Cofe C} (f : A → B) (g : B → C)
  (x : agree A) : agree_map (g ∘ f) x = agree_map g (agree_map f x).
Proof. done. Qed.

Canonical Structure agreeRA (A : cofeT) : cmraT := CMRAT (agree A).
Definition agreeRA_map {A B} (f : A -n> B) : agreeRA A -n> agreeRA B :=
  CofeMor (agree_map f : agreeRA A → agreeRA B).
Instance agreeRA_map_ne A B n : Proper (dist n ==> dist n) (@agreeRA_map A B).
Proof.
  intros f g Hfg x; split; simpl; intros; [done|].
  by apply dist_le with n; try apply Hfg.
Qed.
