From iris.proofmode Require Export classes.
From iris.algebra Require Import gmap.
From stdpp Require Import gmultiset.
From iris.base_logic Require Import big_op tactics.
Set Default Proof Using "Type".
Import uPred.

Section classes.
Context {M : ucmraT}.
Implicit Types P Q R : uPred M.

(* FromAssumption *)
Global Instance from_assumption_exact p P : FromAssumption p P P | 0.
Proof. destruct p; by rewrite /FromAssumption /= ?always_elim. Qed.
Global Instance from_assumption_False p P : FromAssumption p False P | 1.
Proof. destruct p; rewrite /FromAssumption /= ?always_pure; apply False_elim. Qed.

Global Instance from_assumption_always_r P Q :
  FromAssumption true P Q → FromAssumption true P (□ Q).
Proof. rewrite /FromAssumption=><-. by rewrite always_always. Qed.

Global Instance from_assumption_always_l p P Q :
  FromAssumption p P Q → FromAssumption p (□ P) Q.
Proof. rewrite /FromAssumption=><-. by rewrite always_elim. Qed.
Global Instance from_assumption_later p P Q :
  FromAssumption p P Q → FromAssumption p P (▷ Q)%I.
Proof. rewrite /FromAssumption=>->. apply later_intro. Qed.
Global Instance from_assumption_laterN n p P Q :
  FromAssumption p P Q → FromAssumption p P (▷^n Q)%I.
Proof. rewrite /FromAssumption=>->. apply laterN_intro. Qed.
Global Instance from_assumption_bupd p P Q :
  FromAssumption p P Q → FromAssumption p P (|==> Q)%I.
Proof. rewrite /FromAssumption=>->. apply bupd_intro. Qed.
Global Instance from_assumption_forall {A} p (Φ : A → uPred M) Q x :
  FromAssumption p (Φ x) Q → FromAssumption p (∀ x, Φ x) Q.
Proof. rewrite /FromAssumption=> <-. by rewrite forall_elim. Qed.

(* IntoPure *)
Global Instance into_pure_pure φ : @IntoPure M ⌜φ⌝ φ.
Proof. done. Qed.
Global Instance into_pure_eq {A : ofeT} (a b : A) :
  Timeless a → @IntoPure M (a ≡ b) (a ≡ b).
Proof. intros. by rewrite /IntoPure timeless_eq. Qed.
Global Instance into_pure_cmra_valid `{CMRADiscrete A} (a : A) :
  @IntoPure M (✓ a) (✓ a).
Proof. by rewrite /IntoPure discrete_valid. Qed.

Global Instance into_pure_pure_and (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 ∧ P2) (φ1 ∧ φ2).
Proof. rewrite /IntoPure pure_and. by intros -> ->. Qed.
Global Instance into_pure_pure_sep (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 ∗ P2) (φ1 ∧ φ2).
Proof. rewrite /IntoPure sep_and pure_and. by intros -> ->. Qed.
Global Instance into_pure_pure_or (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 ∨ P2) (φ1 ∨ φ2).
Proof. rewrite /IntoPure pure_or. by intros -> ->. Qed.
Global Instance into_pure_pure_impl (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 → P2) (φ1 → φ2).
Proof. rewrite /FromPure /IntoPure pure_impl. by intros -> ->. Qed.
Global Instance into_pure_pure_wand (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → IntoPure P2 φ2 → IntoPure (P1 -∗ P2) (φ1 → φ2).
Proof.
  rewrite /FromPure /IntoPure pure_impl always_impl_wand. by intros -> ->.
Qed.

Global Instance into_pure_exist {X : Type} (Φ : X → uPred M) (φ : X → Prop) :
  (∀ x, @IntoPure M (Φ x) (φ x)) → @IntoPure M (∃ x, Φ x) (∃ x, φ x).
Proof.
  rewrite /IntoPure=>Hx. apply exist_elim=>x. rewrite Hx.
  apply pure_elim'=>Hφ. apply pure_intro. eauto.
Qed.

Global Instance into_pure_forall {X : Type} (Φ : X → uPred M) (φ : X → Prop) :
  (∀ x, @IntoPure M (Φ x) (φ x)) → @IntoPure M (∀ x, Φ x) (∀ x, φ x).
Proof.
  rewrite /IntoPure=>Hx. rewrite -pure_forall_2. by setoid_rewrite Hx.
Qed.

(* FromPure *)
Global Instance from_pure_pure φ : @FromPure M ⌜φ⌝ φ.
Proof. done. Qed.
Global Instance from_pure_internal_eq {A : ofeT} (a b : A) :
  @FromPure M (a ≡ b) (a ≡ b).
Proof.
  rewrite /FromPure. eapply pure_elim; [done|]=> ->. apply internal_eq_refl'.
Qed.
Global Instance from_pure_cmra_valid {A : cmraT} (a : A) :
  @FromPure M (✓ a) (✓ a).
Proof.
  rewrite /FromPure. eapply pure_elim; [done|]=> ?.
  rewrite -cmra_valid_intro //. auto with I.
Qed.
Global Instance from_pure_bupd P φ : FromPure P φ → FromPure (|==> P) φ.
Proof. rewrite /FromPure=> ->. apply bupd_intro. Qed.

Global Instance from_pure_pure_and (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 ∧ P2) (φ1 ∧ φ2).
Proof. rewrite /FromPure pure_and. by intros -> ->. Qed.
Global Instance from_pure_pure_sep (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 ∗ P2) (φ1 ∧ φ2).
Proof. rewrite /FromPure pure_and always_and_sep_l. by intros -> ->. Qed.
Global Instance from_pure_pure_or (φ1 φ2 : Prop) P1 P2 :
  FromPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 ∨ P2) (φ1 ∨ φ2).
Proof. rewrite /FromPure pure_or. by intros -> ->. Qed.
Global Instance from_pure_pure_impl (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 → P2) (φ1 → φ2).
Proof. rewrite /FromPure /IntoPure pure_impl. by intros -> ->. Qed.
Global Instance from_pure_pure_wand (φ1 φ2 : Prop) P1 P2 :
  IntoPure P1 φ1 → FromPure P2 φ2 → FromPure (P1 -∗ P2) (φ1 → φ2).
Proof.
  rewrite /FromPure /IntoPure pure_impl always_impl_wand. by intros -> ->.
Qed.

Global Instance from_pure_exist {X : Type} (Φ : X → uPred M) (φ : X → Prop) :
  (∀ x, @FromPure M (Φ x) (φ x)) → @FromPure M (∃ x, Φ x) (∃ x, φ x).
Proof.
  rewrite /FromPure=>Hx. apply pure_elim'=>-[x ?]. rewrite -(exist_intro x).
  rewrite -Hx. apply pure_intro. done.
Qed.
Global Instance from_pure_forall {X : Type} (Φ : X → uPred M) (φ : X → Prop) :
  (∀ x, @FromPure M (Φ x) (φ x)) → @FromPure M (∀ x, Φ x) (∀ x, φ x).
Proof.
  rewrite /FromPure=>Hx. apply forall_intro=>x. apply pure_elim'=>Hφ.
  rewrite -Hx. apply pure_intro. done.
Qed.

(* IntoPersistentP *)
Global Instance into_persistentP_always_trans P Q :
  IntoPersistentP P Q → IntoPersistentP (□ P) Q | 0.
Proof. rewrite /IntoPersistentP=> ->. by rewrite always_always. Qed.
Global Instance into_persistentP_always P : IntoPersistentP (□ P) P | 1.
Proof. done. Qed.
Global Instance into_persistentP_persistent P :
  PersistentP P → IntoPersistentP P P | 100.
Proof. done. Qed.

(* IntoLater *)
Global Instance into_laterN_later n P Q :
  IntoLaterN n P Q → IntoLaterN' (S n) (▷ P) Q.
Proof. by rewrite /IntoLaterN' /IntoLaterN =>->. Qed.
Global Instance into_laterN_laterN n P : IntoLaterN' n (▷^n P) P.
Proof. done. Qed.
Global Instance into_laterN_laterN_plus n m P Q :
  IntoLaterN m P Q → IntoLaterN' (n + m) (▷^n P) Q.
Proof. rewrite /IntoLaterN' /IntoLaterN=>->. by rewrite laterN_plus. Qed.

Global Instance into_laterN_and_l n P1 P2 Q1 Q2 :
  IntoLaterN' n P1 Q1 → IntoLaterN n P2 Q2 →
  IntoLaterN' n (P1 ∧ P2) (Q1 ∧ Q2) | 10.
Proof. rewrite /IntoLaterN' /IntoLaterN=> -> ->. by rewrite laterN_and. Qed.
Global Instance into_laterN_and_r n P P2 Q2 :
  IntoLaterN' n P2 Q2 → IntoLaterN' n (P ∧ P2) (P ∧ Q2) | 11.
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ->. by rewrite laterN_and -(laterN_intro _ P).
Qed.

Global Instance into_laterN_or_l n P1 P2 Q1 Q2 :
  IntoLaterN' n P1 Q1 → IntoLaterN n P2 Q2 →
  IntoLaterN' n (P1 ∨ P2) (Q1 ∨ Q2) | 10.
Proof. rewrite /IntoLaterN' /IntoLaterN=> -> ->. by rewrite laterN_or. Qed.
Global Instance into_laterN_or_r n P P2 Q2 :
  IntoLaterN' n P2 Q2 →
  IntoLaterN' n (P ∨ P2) (P ∨ Q2) | 11.
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ->. by rewrite laterN_or -(laterN_intro _ P).
Qed.

Global Instance into_laterN_sep_l n P1 P2 Q1 Q2 :
  IntoLaterN' n P1 Q1 → IntoLaterN n P2 Q2 →
  IntoLaterN' n (P1 ∗ P2) (Q1 ∗ Q2) | 10.
Proof. rewrite /IntoLaterN' /IntoLaterN=> -> ->. by rewrite laterN_sep. Qed.
Global Instance into_laterN_sep_r n P P2 Q2 :
  IntoLaterN' n P2 Q2 →
  IntoLaterN' n (P ∗ P2) (P ∗ Q2) | 11.
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ->. by rewrite laterN_sep -(laterN_intro _ P).
Qed.

Global Instance into_laterN_big_sepL n {A} (Φ Ψ : nat → A → uPred M) (l: list A) :
  (∀ x k, IntoLaterN' n (Φ k x) (Ψ k x)) →
  IntoLaterN' n ([∗ list] k ↦ x ∈ l, Φ k x) ([∗ list] k ↦ x ∈ l, Ψ k x).
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ?.
  rewrite big_sepL_laterN. by apply big_sepL_mono.
Qed.
Global Instance into_laterN_big_sepM n `{Countable K} {A}
    (Φ Ψ : K → A → uPred M) (m : gmap K A) :
  (∀ x k, IntoLaterN' n (Φ k x) (Ψ k x)) →
  IntoLaterN' n ([∗ map] k ↦ x ∈ m, Φ k x) ([∗ map] k ↦ x ∈ m, Ψ k x).
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ?.
  rewrite big_sepM_laterN; by apply big_sepM_mono.
Qed.
Global Instance into_laterN_big_sepS n `{Countable A}
    (Φ Ψ : A → uPred M) (X : gset A) :
  (∀ x, IntoLaterN' n (Φ x) (Ψ x)) →
  IntoLaterN' n ([∗ set] x ∈ X, Φ x) ([∗ set] x ∈ X, Ψ x).
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ?.
  rewrite big_sepS_laterN; by apply big_sepS_mono.
Qed.
Global Instance into_laterN_big_sepMS n `{Countable A}
    (Φ Ψ : A → uPred M) (X : gmultiset A) :
  (∀ x, IntoLaterN' n (Φ x) (Ψ x)) →
  IntoLaterN' n ([∗ mset] x ∈ X, Φ x) ([∗ mset] x ∈ X, Ψ x).
Proof.
  rewrite /IntoLaterN' /IntoLaterN=> ?.
  rewrite big_sepMS_laterN; by apply big_sepMS_mono.
Qed.

(* FromLater *)
Global Instance from_laterN_later P :FromLaterN 1 (▷ P) P | 0.
Proof. done. Qed.
Global Instance from_laterN_laterN n P : FromLaterN n (▷^n P) P | 0.
Proof. done. Qed.

(* The instances below are used when stripping a specific number of laters, or
to balance laters in different branches of ∧, ∨ and ∗. *)
Global Instance from_laterN_0 P : FromLaterN 0 P P | 100. (* fallthrough *)
Proof. done. Qed.
Global Instance from_laterN_later_S n P Q :
  FromLaterN n P Q → FromLaterN (S n) (▷ P) Q.
Proof. by rewrite /FromLaterN=><-. Qed.
Global Instance from_laterN_later_plus n m P Q :
  FromLaterN m P Q → FromLaterN (n + m) (▷^n P) Q.
Proof. rewrite /FromLaterN=><-. by rewrite laterN_plus. Qed.

Global Instance from_later_and n P1 P2 Q1 Q2 :
  FromLaterN n P1 Q1 → FromLaterN n P2 Q2 → FromLaterN n (P1 ∧ P2) (Q1 ∧ Q2).
Proof. intros ??; red. by rewrite laterN_and; apply and_mono. Qed.
Global Instance from_later_or n P1 P2 Q1 Q2 :
  FromLaterN n P1 Q1 → FromLaterN n P2 Q2 → FromLaterN n (P1 ∨ P2) (Q1 ∨ Q2).
Proof. intros ??; red. by rewrite laterN_or; apply or_mono. Qed.
Global Instance from_later_sep n P1 P2 Q1 Q2 :
  FromLaterN n P1 Q1 → FromLaterN n P2 Q2 → FromLaterN n (P1 ∗ P2) (Q1 ∗ Q2).
Proof. intros ??; red. by rewrite laterN_sep; apply sep_mono. Qed.

Global Instance from_later_always n P Q :
  FromLaterN n P Q → FromLaterN n (□ P) (□ Q).
Proof. by rewrite /FromLaterN -always_laterN=> ->. Qed.

Global Instance from_later_forall {A} n (Φ Ψ : A → uPred M) :
  (∀ x, FromLaterN n (Φ x) (Ψ x)) → FromLaterN n (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /FromLaterN laterN_forall=> ?. by apply forall_mono. Qed.
Global Instance from_later_exist {A} n (Φ Ψ : A → uPred M) :
  Inhabited A → (∀ x, FromLaterN n (Φ x) (Ψ x)) →
  FromLaterN n (∃ x, Φ x) (∃ x, Ψ x).
Proof. intros ?. rewrite /FromLaterN laterN_exist=> ?. by apply exist_mono. Qed.

(* IntoWand *)
Global Instance wand_weaken_exact P Q : WandWeaken P Q P Q.
Proof. done. Qed.
Global Instance wand_weaken_later P Q P' Q' :
  WandWeaken P Q P' Q' → WandWeaken' P Q (▷ P') (▷ Q').
Proof.
  rewrite /WandWeaken' /WandWeaken=> ->. by rewrite -later_wand -later_intro.
Qed.
Global Instance wand_weaken_laterN n P Q P' Q' :
  WandWeaken P Q P' Q' → WandWeaken' P Q (▷^n P') (▷^n Q').
Proof.
  rewrite /WandWeaken' /WandWeaken=> ->. by rewrite -laterN_wand -laterN_intro.
Qed.
Global Instance bupd_weaken_laterN P Q P' Q' :
  WandWeaken P Q P' Q' → WandWeaken' P Q (|==> P') (|==> Q').
Proof.
  rewrite /WandWeaken' /WandWeaken=> ->.
  apply wand_intro_l. by rewrite bupd_wand_r.
Qed.

Global Instance into_wand_wand P P' Q Q' :
  WandWeaken P Q P' Q' → IntoWand (P -∗ Q) P' Q'.
Proof. done. Qed.
Global Instance into_wand_impl P P' Q Q' :
  WandWeaken P Q P' Q' → IntoWand (P → Q) P' Q'.
Proof. rewrite /WandWeaken /IntoWand /= => <-. apply impl_wand. Qed.

Global Instance into_wand_iff_l P P' Q Q' :
  WandWeaken P Q P' Q' → IntoWand (P ↔ Q) P' Q'.
Proof. rewrite /WandWeaken /IntoWand=> <-. apply and_elim_l', impl_wand. Qed.
Global Instance into_wand_iff_r P P' Q Q' :
  WandWeaken Q P Q' P' → IntoWand (P ↔ Q) Q' P'.
Proof. rewrite /WandWeaken /IntoWand=> <-. apply and_elim_r', impl_wand. Qed.

Global Instance into_wand_forall {A} (Φ : A → uPred M) P Q x :
  IntoWand (Φ x) P Q → IntoWand (∀ x, Φ x) P Q.
Proof. rewrite /IntoWand=> <-. apply forall_elim. Qed.
Global Instance into_wand_always R P Q : IntoWand R P Q → IntoWand (□ R) P Q.
Proof. rewrite /IntoWand=> ->. apply always_elim. Qed.

Global Instance into_wand_later R P Q :
  IntoWand R P Q → IntoWand (▷ R) (▷ P) (▷ Q).
Proof. rewrite /IntoWand=> ->. by rewrite -later_wand. Qed.
Global Instance into_wand_laterN n R P Q :
  IntoWand R P Q → IntoWand (▷^n R) (▷^n P) (▷^n Q).
Proof. rewrite /IntoWand=> ->. by rewrite -laterN_wand. Qed.
Global Instance into_wand_bupd R P Q :
  IntoWand R P Q → IntoWand (|==> R) (|==> P) (|==> Q).
Proof.
  rewrite /IntoWand=> ->. apply wand_intro_l. by rewrite bupd_sep wand_elim_r.
Qed.

(* FromAnd *)
Global Instance from_and_and p P1 P2 : FromAnd p (P1 ∧ P2) P1 P2 | 100.
Proof. by apply mk_from_and_and. Qed.

Global Instance from_and_sep P1 P2 : FromAnd false (P1 ∗ P2) P1 P2 | 100.
Proof. done. Qed.
Global Instance from_and_sep_persistent_l P1 P2 :
  PersistentP P1 → FromAnd true (P1 ∗ P2) P1 P2 | 9.
Proof. intros. by rewrite /FromAnd always_and_sep_l. Qed.
Global Instance from_and_sep_persistent_r P1 P2 :
  PersistentP P2 → FromAnd true (P1 ∗ P2) P1 P2 | 10.
Proof. intros. by rewrite /FromAnd always_and_sep_r. Qed.

Global Instance from_and_pure p φ ψ : @FromAnd M p ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. apply mk_from_and_and. by rewrite pure_and. Qed.
Global Instance from_and_always p P Q1 Q2 :
  FromAnd false P Q1 Q2 → FromAnd p (□ P) (□ Q1) (□ Q2).
Proof.
  intros. apply mk_from_and_and.
  by rewrite always_and_sep_l' -always_sep -(from_and _ P).
Qed.
Global Instance from_and_later p P Q1 Q2 :
  FromAnd p P Q1 Q2 → FromAnd p (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromAnd=> <-. destruct p; by rewrite ?later_and ?later_sep. Qed.
Global Instance from_and_laterN p n P Q1 Q2 :
  FromAnd p P Q1 Q2 → FromAnd p (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /FromAnd=> <-. destruct p; by rewrite ?laterN_and ?laterN_sep. Qed.

Global Instance from_sep_ownM (a b1 b2 : M) :
  FromOp a b1 b2 →
  FromAnd false (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof. intros. by rewrite /FromAnd -ownM_op from_op. Qed.
Global Instance from_sep_ownM_persistent (a b1 b2 : M) :
  FromOp a b1 b2 → Or (Persistent b1) (Persistent b2) →
  FromAnd true (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof.
  intros ? Hper; apply mk_from_and_persistent; [destruct Hper; apply _|].
  by rewrite -ownM_op from_op.
Qed.

Global Instance from_sep_bupd P Q1 Q2 :
  FromAnd false P Q1 Q2 → FromAnd false (|==> P) (|==> Q1) (|==> Q2).
Proof. rewrite /FromAnd=><-. apply bupd_sep. Qed.

Global Instance from_and_big_sepL_cons {A} (Φ : nat → A → uPred M) x l :
  FromAnd false ([∗ list] k ↦ y ∈ x :: l, Φ k y) (Φ 0 x) ([∗ list] k ↦ y ∈ l, Φ (S k) y).
Proof. by rewrite /FromAnd big_sepL_cons. Qed.
Global Instance from_and_big_sepL_cons_persistent {A} (Φ : nat → A → uPred M) x l :
  PersistentP (Φ 0 x) →
  FromAnd true ([∗ list] k ↦ y ∈ x :: l, Φ k y) (Φ 0 x) ([∗ list] k ↦ y ∈ l, Φ (S k) y).
Proof. intros. by rewrite /FromAnd big_opL_cons always_and_sep_l. Qed.

Global Instance from_and_big_sepL_app {A} (Φ : nat → A → uPred M) l1 l2 :
  FromAnd false ([∗ list] k ↦ y ∈ l1 ++ l2, Φ k y)
    ([∗ list] k ↦ y ∈ l1, Φ k y) ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y).
Proof. by rewrite /FromAnd big_sepL_app. Qed.
Global Instance from_sep_big_sepL_app_persistent {A} (Φ : nat → A → uPred M) l1 l2 :
  (∀ k y, PersistentP (Φ k y)) →
  FromAnd true ([∗ list] k ↦ y ∈ l1 ++ l2, Φ k y)
    ([∗ list] k ↦ y ∈ l1, Φ k y) ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y).
Proof. intros. by rewrite /FromAnd big_opL_app always_and_sep_l. Qed.

(* FromOp *)
Global Instance from_op_op {A : cmraT} (a b : A) : FromOp (a ⋅ b) a b.
Proof. by rewrite /FromOp. Qed.

(* TODO: Worst case there could be a lot of backtracking on these instances,
try to refactor. *)
Global Instance from_op_pair {A B : cmraT} (a b1 b2 : A) (a' b1' b2' : B) :
  FromOp a b1 b2 → FromOp a' b1' b2' → FromOp (a,a') (b1,b1') (b2,b2').
Proof. by constructor. Qed.
Global Instance from_op_pair_persistent_l {A B : cmraT} (a : A) (a' b1' b2' : B) :
  Persistent a → FromOp a' b1' b2' → FromOp (a,a') (a,b1') (a,b2').
Proof. constructor=> //=. by rewrite -persistent_dup. Qed.
Global Instance from_op_pair_persistent_r {A B : cmraT} (a b1 b2 : A) (a' : B) :
  Persistent a' → FromOp a b1 b2 → FromOp (a,a') (b1,a') (b2,a').
Proof. constructor=> //=. by rewrite -persistent_dup. Qed.

Global Instance from_op_Some {A : cmraT} (a : A) b1 b2 :
  FromOp a b1 b2 → FromOp (Some a) (Some b1) (Some b2).
Proof. by constructor. Qed.

(* IntoOp *)
Global Instance into_op_op {A : cmraT} (a b : A) : IntoOp (a ⋅ b) a b.
Proof. by rewrite /IntoOp. Qed.

Global Instance into_op_pair {A B : cmraT} (a b1 b2 : A) (a' b1' b2' : B) :
  IntoOp a b1 b2 → IntoOp a' b1' b2' →
  IntoOp (a,a') (b1,b1') (b2,b2').
Proof. by constructor. Qed.
Global Instance into_op_pair_persistent_l {A B : cmraT} (a : A) (a' b1' b2' : B) :
  Persistent a → IntoOp a' b1' b2' → IntoOp (a,a') (a,b1') (a,b2').
Proof. constructor=> //=. by rewrite -persistent_dup. Qed.
Global Instance into_op_pair_persistent_r {A B : cmraT} (a b1 b2 : A) (a' : B) :
  Persistent a' → IntoOp a b1 b2 → IntoOp (a,a') (b1,a') (b2,a').
Proof. constructor=> //=. by rewrite -persistent_dup. Qed.

Global Instance into_op_Some {A : cmraT} (a : A) b1 b2 :
  IntoOp a b1 b2 → IntoOp (Some a) (Some b1) (Some b2).
Proof. by constructor. Qed.

(* IntoAnd *)
Global Instance into_and_sep p P Q : IntoAnd p (P ∗ Q) P Q.
Proof. by apply mk_into_and_sep. Qed.
Global Instance into_and_ownM p (a b1 b2 : M) :
  IntoOp a b1 b2 →
  IntoAnd p (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof. intros. apply mk_into_and_sep. by rewrite (into_op a) ownM_op. Qed.

Global Instance into_and_and P Q : IntoAnd true (P ∧ Q) P Q.
Proof. done. Qed.
Global Instance into_and_and_persistent_l P Q :
  PersistentP P → IntoAnd false (P ∧ Q) P Q.
Proof. intros; by rewrite /IntoAnd /= always_and_sep_l. Qed.
Global Instance into_and_and_persistent_r P Q :
  PersistentP Q → IntoAnd false (P ∧ Q) P Q.
Proof. intros; by rewrite /IntoAnd /= always_and_sep_r. Qed.

Global Instance into_and_pure p φ ψ : @IntoAnd M p ⌜φ ∧ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. apply mk_into_and_sep. by rewrite pure_and always_and_sep_r. Qed.
Global Instance into_and_always p P Q1 Q2 :
  IntoAnd true P Q1 Q2 → IntoAnd p (□ P) (□ Q1) (□ Q2).
Proof.
  rewrite /IntoAnd=>->. destruct p; by rewrite ?always_and always_and_sep_r.
Qed.
Global Instance into_and_later p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /IntoAnd=>->. destruct p; by rewrite ?later_and ?later_sep. Qed.
Global Instance into_and_laterN n p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /IntoAnd=>->. destruct p; by rewrite ?laterN_and ?laterN_sep. Qed.

(* We use [IsCons] and [IsApp] to make sure that [frame_big_sepL_cons] and
[frame_big_sepL_app] cannot be applied repeatedly often when having
[ [∗ list] k ↦ x ∈ ?e, Φ k x] with [?e] an evar. *)
Global Instance into_and_big_sepL_cons {A} p (Φ : nat → A → uPred M) l x l' :
  IsCons l x l' →
  IntoAnd p ([∗ list] k ↦ y ∈ l, Φ k y)
    (Φ 0 x) ([∗ list] k ↦ y ∈ l', Φ (S k) y).
Proof. rewrite /IsCons=>->. apply mk_into_and_sep. by rewrite big_sepL_cons. Qed.
Global Instance into_and_big_sepL_app {A} p (Φ : nat → A → uPred M) l l1 l2 :
  IsApp l l1 l2 →
  IntoAnd p ([∗ list] k ↦ y ∈ l, Φ k y)
    ([∗ list] k ↦ y ∈ l1, Φ k y) ([∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y).
Proof. rewrite /IsApp=>->. apply mk_into_and_sep. by rewrite big_sepL_app. Qed.

(* Frame *)
Global Instance frame_here p R : Frame p R R True.
Proof. by rewrite /Frame right_id always_if_elim. Qed.
Global Instance frame_here_pure p φ Q : FromPure Q φ → Frame p ⌜φ⌝ Q True.
Proof. rewrite /FromPure /Frame=> ->. by rewrite always_if_elim right_id. Qed.

Class MakeSep (P Q PQ : uPred M) := make_sep : P ∗ Q ⊣⊢ PQ.
Global Instance make_sep_true_l P : MakeSep True P P.
Proof. by rewrite /MakeSep left_id. Qed.
Global Instance make_sep_true_r P : MakeSep P True P.
Proof. by rewrite /MakeSep right_id. Qed.
Global Instance make_sep_default P Q : MakeSep P Q (P ∗ Q) | 100.
Proof. done. Qed.

Global Instance frame_sep_persistent_l R P1 P2 Q1 Q2 Q' :
  Frame true R P1 Q1 → MaybeFrame true R P2 Q2 → MakeSep Q1 Q2 Q' →
  Frame true R (P1 ∗ P2) Q' | 9.
Proof.
  rewrite /Frame /MaybeFrame /MakeSep /= => <- <- <-.
  rewrite {1}(always_sep_dup (□ R)). solve_sep_entails.
Qed.
Global Instance frame_sep_l R P1 P2 Q Q' :
  Frame false R P1 Q → MakeSep Q P2 Q' → Frame false R (P1 ∗ P2) Q' | 9.
Proof. rewrite /Frame /MakeSep => <- <-. by rewrite assoc. Qed.
Global Instance frame_sep_r p R P1 P2 Q Q' :
  Frame p R P2 Q → MakeSep P1 Q Q' → Frame p R (P1 ∗ P2) Q' | 10.
Proof. rewrite /Frame /MakeSep => <- <-. by rewrite assoc -(comm _ P1) assoc. Qed.

Global Instance frame_big_sepL_cons {A} p (Φ : nat → A → uPred M) R Q l x l' :
  IsCons l x l' →
  Frame p R (Φ 0 x ∗ [∗ list] k ↦ y ∈ l', Φ (S k) y) Q →
  Frame p R ([∗ list] k ↦ y ∈ l, Φ k y) Q.
Proof. rewrite /IsCons=>->. by rewrite /Frame big_sepL_cons. Qed.
Global Instance frame_big_sepL_app {A} p (Φ : nat → A → uPred M) R Q l l1 l2 :
  IsApp l l1 l2 →
  Frame p R (([∗ list] k ↦ y ∈ l1, Φ k y) ∗
           [∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y) Q →
  Frame p R ([∗ list] k ↦ y ∈ l, Φ k y) Q.
Proof. rewrite /IsApp=>->. by rewrite /Frame big_sepL_app. Qed.

Class MakeAnd (P Q PQ : uPred M) := make_and : P ∧ Q ⊣⊢ PQ.
Global Instance make_and_true_l P : MakeAnd True P P.
Proof. by rewrite /MakeAnd left_id. Qed.
Global Instance make_and_true_r P : MakeAnd P True P.
Proof. by rewrite /MakeAnd right_id. Qed.
Global Instance make_and_default P Q : MakeAnd P Q (P ∧ Q) | 100.
Proof. done. Qed.
Global Instance frame_and_l p R P1 P2 Q Q' :
  Frame p R P1 Q → MakeAnd Q P2 Q' → Frame p R (P1 ∧ P2) Q' | 9.
Proof. rewrite /Frame /MakeAnd => <- <-; eauto 10 with I. Qed.
Global Instance frame_and_r p R P1 P2 Q Q' :
  Frame p R P2 Q → MakeAnd P1 Q Q' → Frame p R (P1 ∧ P2) Q' | 10.
Proof. rewrite /Frame /MakeAnd => <- <-; eauto 10 with I. Qed.

Class MakeOr (P Q PQ : uPred M) := make_or : P ∨ Q ⊣⊢ PQ.
Global Instance make_or_true_l P : MakeOr True P True.
Proof. by rewrite /MakeOr left_absorb. Qed.
Global Instance make_or_true_r P : MakeOr P True True.
Proof. by rewrite /MakeOr right_absorb. Qed.
Global Instance make_or_default P Q : MakeOr P Q (P ∨ Q) | 100.
Proof. done. Qed.

Global Instance frame_or_persistent_l R P1 P2 Q1 Q2 Q :
  Frame true R P1 Q1 → MaybeFrame true R P2 Q2 → MakeOr Q1 Q2 Q →
  Frame true R (P1 ∨ P2) Q | 9.
Proof. rewrite /Frame /MakeOr => <- <- <-. by rewrite -sep_or_l. Qed.
Global Instance frame_or_persistent_r R P1 P2 Q1 Q2 Q :
  MaybeFrame true R P2 Q2 → MakeOr P1 Q2 Q →
  Frame true R (P1 ∨ P2) Q | 10.
Proof.
  rewrite /Frame /MaybeFrame /MakeOr => <- <-. by rewrite sep_or_l sep_elim_r.
Qed.
Global Instance frame_or R P1 P2 Q1 Q2 Q :
  Frame false R P1 Q1 → Frame false R P2 Q2 → MakeOr Q1 Q2 Q →
  Frame false R (P1 ∨ P2) Q.
Proof. rewrite /Frame /MakeOr => <- <- <-. by rewrite -sep_or_l. Qed.

Global Instance frame_wand p R P1 P2 Q2 :
  Frame p R P2 Q2 → Frame p R (P1 -∗ P2) (P1 -∗ Q2).
Proof.
  rewrite /Frame=> ?. apply wand_intro_l.
  by rewrite assoc (comm _ P1) -assoc wand_elim_r.
Qed.

Class MakeLater (P lP : uPred M) := make_later : ▷ P ⊣⊢ lP.
Global Instance make_later_true : MakeLater True True.
Proof. by rewrite /MakeLater later_True. Qed.
Global Instance make_later_default P : MakeLater P (▷ P) | 100.
Proof. done. Qed.

Global Instance frame_later p R R' P Q Q' :
  IntoLaterN 1 R' R → Frame p R P Q → MakeLater Q Q' → Frame p R' (▷ P) Q'.
Proof.
  rewrite /Frame /MakeLater /IntoLaterN=>-> <- <-.
  by rewrite always_if_later later_sep.
Qed.

Class MakeLaterN (n : nat) (P lP : uPred M) := make_laterN : ▷^n P ⊣⊢ lP.
Global Instance make_laterN_true n : MakeLaterN n True True.
Proof. by rewrite /MakeLaterN laterN_True. Qed.
Global Instance make_laterN_default P : MakeLaterN n P (▷^n P) | 100.
Proof. done. Qed.

Global Instance frame_laterN p n R R' P Q Q' :
  IntoLaterN n R' R → Frame p R P Q → MakeLaterN n Q Q' → Frame p R' (▷^n P) Q'.
Proof.
  rewrite /Frame /MakeLater /IntoLaterN=>-> <- <-.
  by rewrite always_if_laterN laterN_sep.
Qed.

Class MakeAlways (P Q : uPred M) := make_always : □ P ⊣⊢ Q.
Global Instance make_always_true : MakeAlways True True.
Proof. by rewrite /MakeAlways always_pure. Qed.
Global Instance make_always_default P : MakeAlways P (□ P) | 100.
Proof. done. Qed.

Global Instance frame_always R P Q Q' :
  Frame true R P Q → MakeAlways Q Q' → Frame true R (□ P) Q'.
Proof.
  rewrite /Frame /MakeAlways=> <- <-.
  by rewrite always_sep /= always_always.
Qed.

Class MakeExcept0 (P Q : uPred M) := make_except_0 : ◇ P ⊣⊢ Q.
Global Instance make_except_0_True : MakeExcept0 True True.
Proof. by rewrite /MakeExcept0 except_0_True. Qed.
Global Instance make_except_0_default P : MakeExcept0 P (◇ P) | 100.
Proof. done. Qed.

Global Instance frame_except_0 p R P Q Q' :
  Frame p R P Q → MakeExcept0 Q Q' → Frame p R (◇ P) Q'.
Proof.
  rewrite /Frame /MakeExcept0=><- <-.
  by rewrite except_0_sep -(except_0_intro (□?p R)).
Qed.

Global Instance frame_exist {A} p R (Φ Ψ : A → uPred M) :
  (∀ a, Frame p R (Φ a) (Ψ a)) → Frame p R (∃ x, Φ x) (∃ x, Ψ x).
Proof. rewrite /Frame=> ?. by rewrite sep_exist_l; apply exist_mono. Qed.
Global Instance frame_forall {A} p R (Φ Ψ : A → uPred M) :
  (∀ a, Frame p R (Φ a) (Ψ a)) → Frame p R (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /Frame=> ?. by rewrite sep_forall_l; apply forall_mono. Qed.

Global Instance frame_bupd p R P Q : Frame p R P Q → Frame p R (|==> P) (|==> Q).
Proof. rewrite /Frame=><-. by rewrite bupd_frame_l. Qed.

(* FromOr *)
Global Instance from_or_or P1 P2 : FromOr (P1 ∨ P2) P1 P2.
Proof. done. Qed.
Global Instance from_or_bupd P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|==> P) (|==> Q1) (|==> Q2).
Proof. rewrite /FromOr=><-. apply or_elim; apply bupd_mono; auto with I. Qed.
Global Instance from_or_pure φ ψ : @FromOr M ⌜φ ∨ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /FromOr pure_or. Qed.
Global Instance from_or_always P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (□ P) (□ Q1) (□ Q2).
Proof. rewrite /FromOr=> <-. by rewrite always_or. Qed.
Global Instance from_or_later P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromOr=><-. by rewrite later_or. Qed.
Global Instance from_or_laterN n P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /FromOr=><-. by rewrite laterN_or. Qed.

(* IntoOr *)
Global Instance into_or_or P Q : IntoOr (P ∨ Q) P Q.
Proof. done. Qed.
Global Instance into_or_pure φ ψ : @IntoOr M ⌜φ ∨ ψ⌝ ⌜φ⌝ ⌜ψ⌝.
Proof. by rewrite /IntoOr pure_or. Qed.
Global Instance into_or_always P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (□ P) (□ Q1) (□ Q2).
Proof. rewrite /IntoOr=>->. by rewrite always_or. Qed.
Global Instance into_or_later P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /IntoOr=>->. by rewrite later_or. Qed.
Global Instance into_or_laterN n P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /IntoOr=>->. by rewrite laterN_or. Qed.

(* FromExist *)
Global Instance from_exist_exist {A} (Φ : A → uPred M): FromExist (∃ a, Φ a) Φ.
Proof. done. Qed.
Global Instance from_exist_bupd {A} P (Φ : A → uPred M) :
  FromExist P Φ → FromExist (|==> P) (λ a, |==> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.
Global Instance from_exist_pure {A} (φ : A → Prop) :
  @FromExist M A ⌜∃ x, φ x⌝ (λ a, ⌜φ a⌝)%I.
Proof. by rewrite /FromExist pure_exist. Qed.
Global Instance from_exist_always {A} P (Φ : A → uPred M) :
  FromExist P Φ → FromExist (□ P) (λ a, □ (Φ a))%I.
Proof.
  rewrite /FromExist=> <-. apply exist_elim=>x. apply always_mono, exist_intro.
Qed.
Global Instance from_exist_later {A} P (Φ : A → uPred M) :
  FromExist P Φ → FromExist (▷ P) (λ a, ▷ (Φ a))%I.
Proof.
  rewrite /FromExist=> <-. apply exist_elim=>x. apply later_mono, exist_intro.
Qed.
Global Instance from_exist_laterN {A} n P (Φ : A → uPred M) :
  FromExist P Φ → FromExist (▷^n P) (λ a, ▷^n (Φ a))%I.
Proof.
  rewrite /FromExist=> <-. apply exist_elim=>x. apply laterN_mono, exist_intro.
Qed.

(* IntoExist *)
Global Instance into_exist_exist {A} (Φ : A → uPred M) : IntoExist (∃ a, Φ a) Φ.
Proof. done. Qed.
Global Instance into_exist_pure {A} (φ : A → Prop) :
  @IntoExist M A ⌜∃ x, φ x⌝ (λ a, ⌜φ a⌝)%I.
Proof. by rewrite /IntoExist pure_exist. Qed.
Global Instance into_exist_always {A} P (Φ : A → uPred M) :
  IntoExist P Φ → IntoExist (□ P) (λ a, □ (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP always_exist. Qed.
Global Instance into_exist_later {A} P (Φ : A → uPred M) :
  IntoExist P Φ → Inhabited A → IntoExist (▷ P) (λ a, ▷ (Φ a))%I.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP later_exist. Qed.
Global Instance into_exist_laterN {A} n P (Φ : A → uPred M) :
  IntoExist P Φ → Inhabited A → IntoExist (▷^n P) (λ a, ▷^n (Φ a))%I.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP laterN_exist. Qed.

(* IntoForall *)
Global Instance into_forall_forall {A} (Φ : A → uPred M) : IntoForall (∀ a, Φ a) Φ.
Proof. done. Qed.
Global Instance into_forall_always {A} P (Φ : A → uPred M) :
  IntoForall P Φ → IntoForall (□ P) (λ a, □ (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP always_forall. Qed.

(* FromModal *)
Global Instance from_modal_later P : FromModal (▷ P) P.
Proof. apply later_intro. Qed.
Global Instance from_modal_bupd P : FromModal (|==> P) P.
Proof. apply bupd_intro. Qed.
Global Instance from_modal_except_0 P : FromModal (◇ P) P.
Proof. apply except_0_intro. Qed.

(* ElimModal *)
Global Instance elim_modal_wand P P' Q Q' R :
  ElimModal P P' Q Q' → ElimModal P P' (R -∗ Q) (R -∗ Q').
Proof.
  rewrite /ElimModal=> H. apply wand_intro_r.
  by rewrite wand_curry -assoc (comm _ P') -wand_curry wand_elim_l.
Qed.
Global Instance forall_modal_wand {A} P P' (Φ Ψ : A → uPred M) :
  (∀ x, ElimModal P P' (Φ x) (Ψ x)) → ElimModal P P' (∀ x, Φ x) (∀ x, Ψ x).
Proof.
  rewrite /ElimModal=> H. apply forall_intro=> a. by rewrite (forall_elim a).
Qed.

Global Instance elim_modal_always P Q : ElimModal (□ P) P Q Q.
Proof. intros. by rewrite /ElimModal always_elim wand_elim_r. Qed.

Global Instance elim_modal_bupd P Q : ElimModal (|==> P) P (|==> Q) (|==> Q).
Proof. by rewrite /ElimModal bupd_frame_r wand_elim_r bupd_trans. Qed.

Global Instance elim_modal_except_0 P Q : IsExcept0 Q → ElimModal (◇ P) P Q Q.
Proof.
  intros. rewrite /ElimModal (except_0_intro (_ -∗ _)).
  by rewrite -except_0_sep wand_elim_r.
Qed.
Global Instance elim_modal_timeless_bupd P Q :
  TimelessP P → IsExcept0 Q → ElimModal (▷ P) P Q Q.
Proof.
  intros. rewrite /ElimModal (except_0_intro (_ -∗ _)) (timelessP P).
  by rewrite -except_0_sep wand_elim_r.
Qed.
Global Instance elim_modal_timeless_bupd' p P Q :
  TimelessP P → IsExcept0 Q → ElimModal (▷?p P) P Q Q.
Proof.
  destruct p; simpl; auto using elim_modal_timeless_bupd.
  intros _ _. by rewrite /ElimModal wand_elim_r.
Qed.

Global Instance is_except_0_except_0 P : IsExcept0 (◇ P).
Proof. by rewrite /IsExcept0 except_0_idemp. Qed.
Global Instance is_except_0_later P : IsExcept0 (▷ P).
Proof. by rewrite /IsExcept0 except_0_later. Qed.
Global Instance is_except_0_bupd P : IsExcept0 P → IsExcept0 (|==> P).
Proof.
  rewrite /IsExcept0=> HP.
  by rewrite -{2}HP -(except_0_idemp P) -except_0_bupd -(except_0_intro P).
Qed.
End classes.
