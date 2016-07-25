From iris.algebra Require Export cmra.

(** * Local updates *)
Record local_update {A : cmraT} (mz : option A) (x y : A) := {
  local_update_valid n : ✓{n} (x ⋅? mz) → ✓{n} (y ⋅? mz);
  local_update_go n mz' :
    ✓{n} (x ⋅? mz) → x ⋅? mz ≡{n}≡ x ⋅? mz' → y ⋅? mz ≡{n}≡ y ⋅? mz'
}.
Notation "x ~l~> y @ mz" := (local_update mz x y) (at level 70).
Instance: Params (@local_update) 1.

Section updates.
Context {A : cmraT}.
Implicit Types x y : A.

Global Instance local_update_proper :
  Proper ((≡) ==> (≡) ==> (≡) ==> iff) (@local_update A).
Proof.
  cut (Proper ((≡) ==> (≡) ==> (≡) ==> impl) (@local_update A)).
  { intros Hproper; split; by apply Hproper. }
  intros mz mz' Hmz x x' Hx y y' Hy [Hv Hup]; constructor; setoid_subst; auto.
Qed.

Global Instance local_update_preorder mz : PreOrder (@local_update A mz).
Proof.
  split.
  - intros x; by split.
  - intros x1 x2 x3 [??] [??]; split; eauto.
Qed.

Lemma exclusive_local_update `{!Exclusive x} y mz : ✓ y → x ~l~> y @ mz.
Proof.
  split; intros n.
  - move=> /exclusiveN_opM ->. by apply cmra_valid_validN.
  - intros mz' ? Hmz.
    by rewrite (exclusiveN_opM n x mz) // (exclusiveN_opM n x mz') -?Hmz.
Qed.

Lemma op_local_update x1 x2 y mz :
  x1 ~l~> x2 @ Some (y ⋅? mz) → x1 ⋅ y ~l~> x2 ⋅ y @ mz.
Proof.
  intros [Hv1 H1]; split.
  - intros n. rewrite !cmra_opM_assoc. move=> /Hv1 /=; auto.
  - intros n mz'. rewrite !cmra_opM_assoc. move=> Hv /(H1 _ (Some _) Hv) /=; auto.
Qed.

Lemma alloc_local_update x y mz :
  (∀ n, ✓{n} (x ⋅? mz) → ✓{n} (x ⋅ y ⋅? mz)) → x ~l~> x ⋅ y @ mz.
Proof.
  split; first done.
  intros n mz' _. by rewrite !(comm _ x) !cmra_opM_assoc=> ->.
Qed.

Lemma local_update_total `{CMRADiscrete A} x y mz :
  x ~l~> y @ mz ↔
    (✓ (x ⋅? mz) → ✓ (y ⋅? mz)) ∧
    (∀ mz', ✓ (x ⋅? mz) → x ⋅? mz ≡ x ⋅? mz' → y ⋅? mz ≡ y ⋅? mz').
Proof.
  split.
  - destruct 1. split; intros until 0;
      rewrite !(cmra_discrete_valid_iff 0) ?(timeless_iff 0); auto.
  - intros [??]; split; intros until 0;
      rewrite -!cmra_discrete_valid_iff -?timeless_iff; auto.
Qed.
End updates.

(** * Product *)
Lemma prod_local_update {A B : cmraT} (x y : A * B) mz :
  x.1 ~l~> y.1 @ fst <$> mz → x.2 ~l~> y.2 @ snd <$> mz →
  x ~l~> y @ mz.
Proof.
  intros [Hv1 H1] [Hv2 H2]; split.
  - intros n [??]; destruct mz; split; auto.
  - intros n mz' [??] [??].
    specialize (H1 n (fst <$> mz')); specialize (H2 n (snd <$> mz')).
    destruct mz, mz'; split; naive_solver.
Qed.

(** * Option *)
Lemma option_local_update {A : cmraT} (x y : A) mmz :
  x ~l~> y @ mjoin mmz →
  Some x ~l~> Some y @ mmz.
Proof.
  intros [Hv H]; split; first destruct mmz as [[?|]|]; auto.
  intros n mmz'. specialize (H n (mjoin mmz')).
  destruct mmz as [[]|], mmz' as [[]|]; inversion_clear 2; constructor; auto.
Qed.

(** * Natural numbers  *)
Lemma nat_local_update (x y : nat) mz : x ~l~> y @ mz.
Proof.
  split; first done.
  compute -[plus]; destruct mz as [z|]; intros n [z'|]; lia.
Qed.

Lemma mnat_local_update (x y : mnat) mz : x ≤ y → x ~l~> y @ mz.
Proof.
  split; first done.
  compute -[max]; destruct mz as [z|]; intros n [z'|]; lia.
Qed.
