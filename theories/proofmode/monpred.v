From iris.bi Require Export monpred.
From iris.proofmode Require Import tactics.
Import MonPred.

Section bi.
Context {I : bi_index} {PROP : bi}.
Local Notation monPred := (monPred I PROP).
Implicit Types P Q R : monPred.
Implicit Types 𝓟 𝓠 𝓡 : PROP.
Implicit Types φ : Prop.
Implicit Types i j : I.

Class MakeMonPredCar i P 𝓟 :=
  make_monPred_car : P i ⊣⊢ 𝓟.
Arguments MakeMonPredCar _ _%I _%I.

Global Instance make_monPred_car_pure φ i : MakeMonPredCar i ⌜φ⌝ ⌜φ⌝.
Proof. rewrite /MakeMonPredCar. by unseal. Qed.
Global Instance make_monPred_car_internal_eq {A : ofeT} (x y : A) i :
  MakeMonPredCar i (x ≡ y) (x ≡ y).
Proof. rewrite /MakeMonPredCar. by unseal. Qed.
Global Instance make_monPred_car_emp i : MakeMonPredCar i emp emp.
Proof. rewrite /MakeMonPredCar. by unseal. Qed.
Global Instance make_monPred_car_sep i P 𝓟 Q 𝓠 :
  MakeMonPredCar i P 𝓟 → MakeMonPredCar i Q 𝓠 →
  MakeMonPredCar i (P ∗ Q) (𝓟 ∗ 𝓠).
Proof. rewrite /MakeMonPredCar=><-<-. by unseal. Qed.
Global Instance make_monPred_car_and i P 𝓟 Q 𝓠 :
  MakeMonPredCar i P 𝓟 → MakeMonPredCar i Q 𝓠 →
  MakeMonPredCar i (P ∧ Q) (𝓟 ∧ 𝓠).
Proof. rewrite /MakeMonPredCar=><-<-. by unseal. Qed.
Global Instance make_monPred_car_or i P 𝓟 Q 𝓠 :
  MakeMonPredCar i P 𝓟 → MakeMonPredCar i Q 𝓠 →
  MakeMonPredCar i (P ∨ Q) (𝓟 ∨ 𝓠).
Proof. rewrite /MakeMonPredCar=><-<-. by unseal. Qed.
Global Instance make_monPred_car_forall {A} i (Φ : A → monPred) (Ψ : A → PROP) :
  (∀ a, MakeMonPredCar i (Φ a) (Ψ a)) → MakeMonPredCar i (∀ a, Φ a) (∀ a, Ψ a).
Proof. rewrite /MakeMonPredCar=>H. setoid_rewrite <- H. by unseal. Qed.
Global Instance make_monPred_car_exists {A} i (Φ : A → monPred) (Ψ : A → PROP) :
  (∀ a, MakeMonPredCar i (Φ a) (Ψ a)) → MakeMonPredCar i (∃ a, Φ a) (∃ a, Ψ a).
Proof. rewrite /MakeMonPredCar=>H. setoid_rewrite <- H. by unseal. Qed.
Global Instance make_monPred_car_persistently i P 𝓟 :
  MakeMonPredCar i P 𝓟 → MakeMonPredCar i (bi_persistently P) (bi_persistently 𝓟).
Proof. rewrite /MakeMonPredCar=><-. by unseal. Qed.
Global Instance make_monPred_car_affinely i P 𝓟 :
  MakeMonPredCar i P 𝓟 → MakeMonPredCar i (bi_affinely P) (bi_affinely 𝓟).
Proof. rewrite /MakeMonPredCar=><-. by unseal. Qed.
Global Instance make_monPred_car_absorbingly i P 𝓟 :
  MakeMonPredCar i P 𝓟 → MakeMonPredCar i (bi_absorbingly P) (bi_absorbingly 𝓟).
Proof. rewrite /MakeMonPredCar=><-. by unseal. Qed.
Global Instance make_monPred_car_plainly i P Φ :
  (∀ j, MakeMonPredCar j P (Φ j)) →
  MakeMonPredCar i (bi_plainly P) (∀ j, bi_plainly (Φ j)).
Proof. rewrite /MakeMonPredCar=>H. unseal. by do 3 f_equiv. Qed.
Global Instance make_monPred_car_persistently_if i P 𝓟 p :
  MakeMonPredCar i P 𝓟 →
  MakeMonPredCar i (bi_persistently_if p P) (bi_persistently_if p 𝓟).
Proof. destruct p; simpl; apply _. Qed.
Global Instance make_monPred_car_affinely_if i P 𝓟 p :
  MakeMonPredCar i P 𝓟 →
  MakeMonPredCar i (bi_affinely_if p P) (bi_affinely_if p 𝓟).
Proof. destruct p; simpl; apply _. Qed.
Global Instance make_monPred_car_embed i : MakeMonPredCar i ⎡P⎤ P.
Proof. rewrite /MakeMonPredCar. by unseal. Qed.
Global Instance make_monPred_car_in i j : MakeMonPredCar j (monPred_in i) ⌜i ⊑ j⌝.
Proof. rewrite /MakeMonPredCar. by unseal. Qed.
Global Instance make_monPred_car_default i P : MakeMonPredCar i P (P i) | 100.
Proof. by rewrite /MakeMonPredCar. Qed.

Global Instance from_assumption_make_monPred_car_l p i P 𝓟 :
  MakeMonPredCar i P 𝓟 → FromAssumption p (P i) 𝓟.
Proof.
  rewrite /MakeMonPredCar /FromAssumption=><-.
  apply  bi.affinely_persistently_if_elim.
Qed.
Global Instance from_assumption_make_monPred_car_r p i P 𝓟 :
  MakeMonPredCar i P 𝓟 → FromAssumption p 𝓟 (P i).
Proof.
  rewrite /MakeMonPredCar /FromAssumption=><-.
  apply  bi.affinely_persistently_if_elim.
Qed.

Global Instance as_valid_monPred_car φ P (Φ : I → PROP) :
  AsValid φ P → (∀ i, MakeMonPredCar i P (Φ i)) → AsValid' φ (∀ i, Φ i) | 100.
Proof.
  rewrite /MakeMonPredCar /AsValid' /AsValid /bi_valid=> -> EQ.
  setoid_rewrite <-EQ. unseal; split.
  - move=>[/= /bi.forall_intro //].
  - move=>HP. split=>i. rewrite /= HP bi.forall_elim //.
Qed.
Global Instance as_valid_monPred_car_wand φ P Q (Φ Ψ : I → PROP) :
  AsValid φ (P -∗ Q) →
  (∀ i, MakeMonPredCar i P (Φ i)) → (∀ i, MakeMonPredCar i Q (Ψ i)) →
  AsValid' φ (∀ i, Φ i -∗ Ψ i).
Proof.
  rewrite /AsValid' /AsValid /MakeMonPredCar. intros -> EQ1 EQ2.
  setoid_rewrite <-EQ1. setoid_rewrite <-EQ2. split.
  - move=>/bi.wand_entails HP. setoid_rewrite HP. by iIntros (i) "$".
  - move=>HP. apply bi.entails_wand. split=>i. iIntros "H". by iApply HP.
Qed.
Global Instance as_valid_monPred_car_equiv φ P Q (Φ Ψ : I → PROP) :
  AsValid φ (P ∗-∗ Q) →
  (∀ i, MakeMonPredCar i P (Φ i)) → (∀ i, MakeMonPredCar i Q (Ψ i)) →
  AsValid' φ (∀ i, Φ i ∗-∗ Ψ i).
Proof.
  rewrite /AsValid' /AsValid /MakeMonPredCar. intros -> EQ1 EQ2.
  setoid_rewrite <-EQ1. setoid_rewrite <-EQ2. split.
  - move=>/bi.wand_iff_equiv HP. setoid_rewrite HP. iIntros. iSplit; iIntros "$".
  - move=>HP. apply bi.equiv_wand_iff. split=>i. by iSplit; iIntros; iApply HP.
Qed.

Global Instance into_pure_monPred_car P φ i :
  IntoPure P φ → IntoPure (P i) φ.
Proof. rewrite /IntoPure=>->. by unseal. Qed.
Global Instance from_pure_monPred_car P φ i :
  FromPure P φ → FromPure (P i) φ.
Proof. rewrite /FromPure=><-. by unseal. Qed.
Global Instance into_pure_monPred_in i j :
  @IntoPure PROP (monPred_in i j) (i ⊑ j).
Proof. rewrite /IntoPure. by unseal. Qed.
Global Instance from_pure_monPred_in i j :
  @FromPure PROP (monPred_in i j) (i ⊑ j).
Proof. rewrite /FromPure. by unseal. Qed.

Global Instance into_internal_eq_monPred_car {A : ofeT} (x y : A) P i :
  IntoInternalEq P x y → IntoInternalEq (P i) x y.
Proof. rewrite /IntoInternalEq=> ->. by unseal. Qed.

Global Instance into_persistent_monPred_car p P Q 𝓠 i :
  IntoPersistent p P Q → MakeMonPredCar i Q 𝓠 → IntoPersistent p (P i) 𝓠 | 0.
Proof.
  rewrite /IntoPersistent /MakeMonPredCar /bi_persistently_if.
  unseal=>-[/(_ i) ?] <-. by destruct p.
Qed.

Global Instance from_always_monPred_car a pe P Q 𝓠 i :
  FromAlways a pe false P Q → MakeMonPredCar i Q 𝓠 →
  FromAlways a pe false (P i) 𝓠 | 0.
Proof.
  rewrite /FromAlways /MakeMonPredCar /bi_persistently_if /bi_affinely_if=><-.
  by destruct a, pe=><-; try unseal.
Qed.

(* FIXME : P and Q do not go through MakeMonPredCar, which prevent
   lazilly unfolding of monPred connectives there.  The reason we
   cannot do that is that IntoWand is sometimes called with known
   values, which we do not wnat to replace with existentials.  *)
Global Instance into_wand_monPred_car p q R P Q i :
  IntoWand p q R P Q → IntoWand p q (R i) (P i) (Q i).
Proof.
  rewrite /IntoWand /MakeMonPredCar /bi_affinely_if /bi_persistently_if.
  destruct p, q=> /bi.wand_elim_l' [/(_ i) H]; apply bi.wand_intro_r;
  revert H; unseal; done.
Qed.
Global Instance into_wand_wand'_monPred p q P Q 𝓟 𝓠 i :
  IntoWand' p q ((P -∗ Q) i) 𝓟 𝓠 → IntoWand p q ((P -∗ Q) i) 𝓟 𝓠 | 100.
Proof. done. Qed.
Global Instance into_wand_impl'_monPred p q P Q 𝓟 𝓠 i :
  IntoWand' p q ((P → Q) i) 𝓟 𝓠 → IntoWand p q ((P → Q) i) 𝓟 𝓠 | 100.
Proof. done. Qed.

Global Instance from_forall_monPred_car_wand P Q (Φ Ψ : I → PROP) i :
  (∀ j, MakeMonPredCar j P (Φ j)) → (∀ j, MakeMonPredCar j Q (Ψ j)) →
  FromForall ((P -∗ Q) i)%I (λ j, ⌜i ⊑ j⌝ → Φ j -∗ Ψ j)%I.
Proof.
  rewrite /FromForall /MakeMonPredCar. unseal=> H1 H2.
  setoid_rewrite H1. setoid_rewrite H2. done.
Qed.
Global Instance into_forall_monPred_car_wand P Q (Φ Ψ : I → PROP) i :
  (∀ j, MakeMonPredCar j P (Φ j)) → (∀ j, MakeMonPredCar j Q (Ψ j)) →
  IntoForall ((P -∗ Q) i) (λ j, ⌜i ⊑ j⌝ → Φ j -∗ Ψ j)%I.
Proof.
  rewrite /IntoForall /MakeMonPredCar. unseal=> H1 H2.
  setoid_rewrite H1. setoid_rewrite H2. done.
Qed.
Global Instance from_forall_monPred_car_impl P Q (Φ Ψ : I → PROP) i :
  (∀ j, MakeMonPredCar j P (Φ j)) → (∀ j, MakeMonPredCar j Q (Ψ j)) →
  FromForall ((P → Q) i)%I (λ j, ⌜i ⊑ j⌝ → Φ j → Ψ j)%I.
Proof.
  rewrite /FromForall /MakeMonPredCar. unseal=> H1 H2.
  setoid_rewrite H1. setoid_rewrite H2. done.
Qed.
Global Instance into_forall_monPred_car_impl P Q (Φ Ψ : I → PROP) i :
  (∀ j, MakeMonPredCar j P (Φ j)) → (∀ j, MakeMonPredCar j Q (Ψ j)) →
  IntoForall ((P → Q) i) (λ j, ⌜i ⊑ j⌝ → Φ j → Ψ j)%I.
Proof.
  rewrite /IntoForall /MakeMonPredCar. unseal=> H1 H2.
  setoid_rewrite H1. setoid_rewrite H2. done.
Qed.

Global Instance from_and_monPred_car P Q1 𝓠1 Q2 𝓠2 i :
  FromAnd P Q1 Q2 → MakeMonPredCar i Q1 𝓠1 → MakeMonPredCar i Q2 𝓠2 →
  FromAnd (P i) 𝓠1 𝓠2.
Proof. rewrite /FromAnd /MakeMonPredCar /MakeMonPredCar=> <- <- <-. by unseal. Qed.
Global Instance into_and_monPred_car p P Q1 𝓠1 Q2 𝓠2 i :
  IntoAnd p P Q1 Q2 → MakeMonPredCar i Q1 𝓠1 → MakeMonPredCar i Q2 𝓠2 →
  IntoAnd p (P i) 𝓠1 𝓠2.
Proof.
  rewrite /IntoAnd /MakeMonPredCar /bi_affinely_if /bi_persistently_if.
  destruct p=>-[/(_ i) H] <- <-; revert H; unseal; done.
Qed.

Global Instance from_sep_monPred_car P Q1 𝓠1 Q2 𝓠2 i :
  FromSep P Q1 Q2 → MakeMonPredCar i Q1 𝓠1 → MakeMonPredCar i Q2 𝓠2 →
  FromSep (P i) 𝓠1 𝓠2.
Proof. rewrite /FromSep /MakeMonPredCar=> <- <- <-. by unseal. Qed.
Global Instance into_sep_monPred_car P Q1 𝓠1 Q2 𝓠2 i :
  IntoSep P Q1 Q2 → MakeMonPredCar i Q1 𝓠1 → MakeMonPredCar i Q2 𝓠2 →
  IntoSep (P i) 𝓠1 𝓠2.
Proof. rewrite /IntoSep /MakeMonPredCar=> -> <- <-. by unseal. Qed.

Global Instance from_or_monPred_car P Q1 𝓠1 Q2 𝓠2 i :
  FromOr P Q1 Q2 → MakeMonPredCar i Q1 𝓠1 → MakeMonPredCar i Q2 𝓠2 →
  FromOr (P i) 𝓠1 𝓠2.
Proof. rewrite /FromOr /MakeMonPredCar=> <- <- <-. by unseal. Qed.
Global Instance into_or_monPred_car P Q1 𝓠1 Q2 𝓠2 i :
  IntoOr P Q1 Q2 → MakeMonPredCar i Q1 𝓠1 → MakeMonPredCar i Q2 𝓠2 →
  IntoOr (P i) 𝓠1 𝓠2.
Proof. rewrite /IntoOr /MakeMonPredCar=> -> <- <-. by unseal. Qed.

Global Instance from_exist_monPred_car {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  FromExist P Φ → (∀ a, MakeMonPredCar i (Φ a) (Ψ a)) → FromExist (P i) Ψ.
Proof.
  rewrite /FromExist /MakeMonPredCar=><- H. setoid_rewrite <- H. by unseal.
Qed.
Global Instance into_exist_monPred_car {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  IntoExist P Φ → (∀ a, MakeMonPredCar i (Φ a) (Ψ a)) → IntoExist (P i) Ψ.
Proof.
  rewrite /IntoExist /MakeMonPredCar=>-> H. setoid_rewrite <- H. by unseal.
Qed.

Global Instance from_forall_monPred_car {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  FromForall P Φ → (∀ a, MakeMonPredCar i (Φ a) (Ψ a)) → FromForall (P i) Ψ.
Proof.
  rewrite /FromForall /MakeMonPredCar=><- H. setoid_rewrite <- H. by unseal.
Qed.
Global Instance into_forall_monPred_car {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  IntoForall P Φ → (∀ a, MakeMonPredCar i (Φ a) (Ψ a)) → IntoForall (P i) Ψ.
Proof.
  rewrite /IntoForall /MakeMonPredCar=>-> H. setoid_rewrite <- H. by unseal.
Qed.

Global Instance from_forall_monPred_car_all P (Φ : I → PROP) i :
  (∀ i, MakeMonPredCar i P (Φ i)) → FromForall (monPred_all P i) Φ.
Proof.
  rewrite /FromForall /MakeMonPredCar=>H. setoid_rewrite <- H. by unseal.
Qed.
Global Instance into_forall_monPred_car_all P (Φ : I → PROP) i :
  (∀ i, MakeMonPredCar i P (Φ i)) → IntoForall (monPred_all P i) Φ.
Proof.
  rewrite /IntoForall /MakeMonPredCar=>H. setoid_rewrite <- H. by unseal.
Qed.

(* FIXME : there are two good ways to frame under a call to
   monPred_car. This may cause some backtracking in the typeclass
   search, and hence performance issues. *)
Global Instance frame_monPred_car i p P Q 𝓠 R :
  Frame p R P Q → MakeMonPredCar i Q 𝓠 → Frame p (R i) (P i) 𝓠.
Proof.
  rewrite /Frame /MakeMonPredCar /bi_affinely_if /bi_persistently_if=> <- <-.
  by destruct p; unseal.
Qed.
Global Instance frame_monPred_car_embed i p P Q 𝓠 𝓡 :
  Frame p ⎡𝓡⎤ P Q → MakeMonPredCar i Q 𝓠 → Frame p 𝓡 (P i) 𝓠.
Proof.
  rewrite /Frame /MakeMonPredCar /bi_affinely_if /bi_persistently_if=> <- <-.
  by destruct p; unseal.
Qed.

Global Instance from_modal_monPred_car i P Q 𝓠 :
  FromModal P Q → MakeMonPredCar i Q 𝓠 → FromModal (P i) 𝓠.
Proof. by rewrite /FromModal /MakeMonPredCar=> <- <-. Qed.
End bi.

Hint Mode MakeMonPredCar + + - ! -.

Section sbi.
Context {I : bi_index} {PROP : sbi}.
Local Notation monPred := (monPred I PROP).
Implicit Types P Q R : monPred.
Implicit Types 𝓟 𝓠 𝓡 : PROP.
Implicit Types φ : Prop.
Implicit Types i j : I.

Global Instance is_except_0_monPred_car i P :
  IsExcept0 P → IsExcept0 (P i).
Proof. rewrite /IsExcept0=>- [/(_ i)]. by unseal. Qed.

Global Instance make_monPred_car_except_0 i P 𝓠 :
  MakeMonPredCar i P 𝓠 → MakeMonPredCar i (◇ P)%I (◇ 𝓠)%I.
Proof. rewrite /MakeMonPredCar=><-. by unseal. Qed.
Global Instance make_monPred_car_later i P 𝓠 :
  MakeMonPredCar i P 𝓠 → MakeMonPredCar i (▷ P)%I (▷ 𝓠)%I.
Proof. rewrite /MakeMonPredCar=><-. by unseal. Qed.
Global Instance make_monPred_car_laterN i n P 𝓠 :
  MakeMonPredCar i P 𝓠 → MakeMonPredCar i (▷^n P)%I (▷^n 𝓠)%I.
Proof. rewrite /MakeMonPredCar=> <-. elim n=>//= ? <-. by unseal. Qed.

Global Instance into_except_0_monPred_car_fwd i P Q 𝓠 :
  IntoExcept0 P Q → MakeMonPredCar i Q 𝓠 → IntoExcept0 (P i) 𝓠.
Proof. rewrite /IntoExcept0 /MakeMonPredCar=> -> <-. by unseal. Qed.
Global Instance into_except_0_monPred_car_bwd i P 𝓟 Q :
  IntoExcept0 P Q → MakeMonPredCar i P 𝓟 → IntoExcept0 𝓟 (Q i).
Proof. rewrite /IntoExcept0 /MakeMonPredCar=> H <-. rewrite H. by unseal. Qed.

Global Instance into_later_monPred_car i n P Q 𝓠 :
  IntoLaterN n P Q → MakeMonPredCar i Q 𝓠 → IntoLaterN n (P i) 𝓠.
Proof.
  rewrite /IntoLaterN /MakeMonPredCar=> -> <-. elim n=>//= ? <-. by unseal.
Qed.
Global Instance from_later_monPred_car i n P Q 𝓠 :
  FromLaterN n P Q → MakeMonPredCar i Q 𝓠 → FromLaterN n (P i) 𝓠.
Proof. rewrite /FromLaterN /MakeMonPredCar=> <- <-. elim n=>//= ? ->. by unseal. Qed.
End sbi.
