Require Export cmra.
Local Hint Extern 10 (_ ≤ _) => omega.

Record agree A `{Dist A} := Agree {
  agree_car :> nat → A;
  agree_is_valid : nat → Prop;
  agree_valid_0 : agree_is_valid 0;
  agree_valid_S n : agree_is_valid (S n) → agree_is_valid n;
  agree_cauchy n i: n ≤ i → agree_is_valid i → agree_car n ={n}= agree_car i
}.
Arguments Agree {_ _} _ _ _ _ _.
Arguments agree_car {_ _} _ _.
Arguments agree_is_valid {_ _} _ _.
Arguments agree_cauchy {_ _} _ _ _ _ _.

Section agree.
Context `{Cofe A}.

Global Instance agree_validN : ValidN (agree A) := λ n x, agree_is_valid x n.
Lemma agree_valid_le (x : agree A) n n' : validN n x → n' ≤ n → validN n' x.
Proof. unfold validN, agree_validN; induction 2; eauto using agree_valid_S. Qed.
Global Instance agree_valid : Valid (agree A) := λ x, ∀ n, validN n x.
Global Instance agree_equiv : Equiv (agree A) := λ x y,
  (∀ n, validN n x ↔ validN n y) ∧ (∀ n, validN n x → x n ={n}= y n).
Global Instance agree_dist : Dist (agree A) := λ n x y,
  (∀ n', n' ≤ n → validN n' x ↔ validN n' y) ∧
  (∀ n', n' ≤ n → validN n' x → x n' ={n'}= y n').
Global Program Instance agree_compl : Compl (agree A) := λ c,
  {| agree_car n := c n n; agree_is_valid n := validN n (c n) |}.
Next Obligation. intros; apply agree_valid_0. Qed.
Next Obligation.
  intros c n ?; apply (chain_cauchy c n (S n)), agree_valid_S; auto.
Qed.
Next Obligation.
  intros c n i ??; simpl in *; rewrite <-(agree_cauchy (c i) n i) by done.
  by apply (chain_cauchy c), (chain_cauchy c) with i, agree_valid_le with i.
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
      - transitivity (validN n' y). by apply Hxy. by apply Hyz.
      - transitivity (y n'). by apply Hxy. by apply Hyz, Hxy.
  * intros n x y Hxy; split; intros; apply Hxy; auto.
  * intros x y; split; intros n'; rewrite Nat.le_0_r; intros ->; [|done].
    by split; intros; apply agree_valid_0.
  * by intros c n; split; intros; apply (chain_cauchy c).
Qed.

Global Program Instance agree_op : Op (agree A) := λ x y,
  {| agree_car := x; agree_is_valid n := validN n x ∧ validN n y ∧ x ={n}= y |}.
Next Obligation. by intros; simpl; split_ands; try apply agree_valid_0. Qed.
Next Obligation. naive_solver eauto using agree_valid_le, dist_S. Qed.
Next Obligation. by intros x y n i ? (?&?&?); apply agree_cauchy. Qed.
Global Instance agree_unit : Unit (agree A) := id.
Global Instance agree_minus : Minus (agree A) := λ x y, x.
Global Instance agree_included : Included (agree A) := λ x y, y ≡ x ⋅ y.
Instance: Associative (≡) (@op (agree A) _).
Proof.
  intros x y z; split; [split|done].
  * intros (?&(?&?&Hyz)&Hxy); repeat (intros (?&?&?) || intro || split);
      eauto using agree_valid_le; try apply Hxy; auto.
    etransitivity; [by apply Hxy|by apply Hyz].
  * intros ((?&?&Hxy)&?&Hxz); repeat split;
      try apply Hxy; eauto using agree_valid_le;
      by etransitivity; [symmetry; apply Hxy|apply Hxz];
       repeat (intro || split); eauto using agree_valid_le; apply Hxy; auto.
Qed.
Instance: Commutative (≡) (@op (agree A) _).
Proof.
  intros x y; split; [split|intros n (?&?&Hxy); apply Hxy; auto];
    intros (?&?&Hxy); repeat split; eauto using agree_valid_le;
    intros n' ??; symmetry; apply Hxy; eauto using agree_valid_le.
Qed.
Definition agree_idempotent (x : agree A) : x ⋅ x ≡ x.
Proof. split; [split;[by intros (?&?&?)|done]|done]. Qed.
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
Global Instance agree_cmra : CMRA (agree A).
Proof.
  split; try (apply _ || done).
  * by intros n x y Hxy ?; apply Hxy.
  * by intros n x1 x2 Hx y1 y2 Hy.
  * by intros x y1 y2 Hy ?; do 2 red; rewrite <-Hy.
  * intros; apply agree_valid_0.
  * intros n x ?; apply agree_valid_le with (S n); auto.
  * intros x; apply agree_idempotent.
  * intros x y; change (x ⋅ y ≡ x ⋅ (x ⋅ y)).
    by rewrite (associative _), agree_idempotent.
  * by intros x y n (?&?&?).
  * by intros x y; do 2 red; rewrite (associative _), agree_idempotent.
Qed.
Program Definition to_agree (x : A) : agree A :=
  {| agree_car n := x; agree_is_valid n := True |}.
Solve Obligations with done.
Global Instance to_agree_ne n : Proper (dist n ==> dist n) to_agree.
Proof. intros x1 x2 Hx; split; naive_solver eauto using @dist_le. Qed.

Lemma agree_op_inv (x y1 y2 : agree A) n :
  validN n x → x ={n}= y1 ⋅ y2 → y1 ={n}= y2.
Proof. by intros ? Hxy; apply Hxy. Qed.
Global Instance agree_extend : CMRAExtend (agree A).
Proof.
  intros x y1 y2 n ? Hx; exists (x,x); simpl; split.
  * by rewrite agree_idempotent.
  * by rewrite Hx, (agree_op_inv x y1 y2), agree_idempotent by done.
Qed.
End agree.

Canonical Structure agreeC (A : cmraT) : cmraT := CMRAT (agree A).

Section agree_map.
  Context `{Cofe A, Cofe B} (f: A → B) `{Hf: ∀ n, Proper (dist n ==> dist n) f}.
  Program Definition agree_map (x : agree A) : agree B :=
   {| agree_car n := f (x n); agree_is_valid n := validN n x |}.
  Next Obligation. apply agree_valid_0. Qed.
  Next Obligation. by intros x n ?; apply agree_valid_S. Qed.
  Next Obligation. by intros x n i ??; simpl; rewrite (agree_cauchy x n i). Qed.
  Global Instance agree_map_ne n : Proper (dist n ==> dist n) agree_map.
  Proof. by intros x1 x2 Hx; split; simpl; intros; [apply Hx|apply Hf, Hx]. Qed.
  Global Instance agree_map_preserving : CMRAPreserving agree_map.
  Proof.
    split; [|by intros n ?].
    intros x y; unfold included, agree_included; intros Hy; rewrite Hy.
    split; [split|done].
    * by intros (?&?&Hxy); repeat (intro || split);
        try apply Hxy; try apply Hf; eauto using @agree_valid_le.
    * by intros (?&(?&?&Hxy)&_); repeat split;
        try apply Hxy; eauto using agree_valid_le.
  Qed.
End agree_map.
