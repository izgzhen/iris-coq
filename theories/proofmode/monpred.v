From iris.bi Require Export monpred.
From iris.proofmode Require Import tactics.
Import MonPred.

Section bi.
Context {I : bi_index} {PROP : bi}.
Local Notation monPred := (monPred I PROP).
Implicit Types P Q R : monPred.
Implicit Types φ : Prop.
Implicit Types i j : I.

Global Instance as_valid_monPred_car φ P :
  AsValid φ P → AsValid φ (∀ i, P i).
Proof.
  rewrite /AsValid /bi_valid=> ->; unseal; split.
  - move=>[/= /bi.forall_intro //].
  - move=>H. split=>i. rewrite /= H bi.forall_elim //.
Qed.

Global Instance into_pure_monPred_car P φ i : IntoPure P φ → IntoPure (P i) φ.
Proof. rewrite /IntoPure=> ->. by unseal. Qed.
Global Instance from_pure_monPred_car P φ i : FromPure P φ → FromPure (P i) φ.
Proof. rewrite /FromPure=> <-. by unseal. Qed.
Global Instance into_internal_eq_monPred_car {A : ofeT} (x y : A) P i :
  IntoInternalEq P x y → IntoInternalEq (P i) x y.
Proof. rewrite /IntoInternalEq=> ->. by unseal. Qed.

Global Instance into_persistent_monPred_car p P Q i:
  IntoPersistent p P Q → IntoPersistent p (P i) (Q i) | 0.
Proof.
  rewrite /IntoPersistent /bi_persistently_if. unseal=>-[/(_ i)].
  by destruct p.
Qed.
Global Instance from_always_monPred_car a pe P Q i :
  FromAlways a pe false P Q → FromAlways a pe false (P i) (Q i) | 0.
Proof.
  rewrite /FromAlways /bi_persistently_if /bi_affinely_if=><-.
  by destruct a, pe; try unseal.
Qed.

Global Instance into_wand_monPred_car p q R P Q i :
  IntoWand p q R P Q → IntoWand p q (R i) (P i) (Q i).
Proof.
  rewrite /IntoWand /bi_affinely_if /bi_persistently_if=>/bi.wand_elim_l' <-.
  apply bi.wand_intro_r. by destruct p, q; unseal.
Qed.
Global Instance from_forall_monPred_car_wand P Q i :
  FromForall ((P -∗ Q) i)%I (λ j, ⌜i ⊑ j⌝ → P j -∗ Q j)%I.
Proof. rewrite /FromForall. by unseal. Qed.
Global Instance into_forall_monPred_car_wand P Q i :
  IntoForall ((P -∗ Q) i) (λ j, ⌜i ⊑ j⌝ → P j -∗ Q j)%I.
Proof. rewrite /IntoForall. by unseal. Qed.
Global Instance from_forall_monPred_car_impl P Q i :
  FromForall ((P → Q) i)%I (λ j, ⌜i ⊑ j⌝ → P j → Q j)%I.
Proof. rewrite /FromForall. by unseal. Qed.
Global Instance into_forall_monPred_car_impl P Q i :
  IntoForall ((P → Q) i) (λ j, ⌜i ⊑ j⌝ → P j → Q j)%I.
Proof. rewrite /IntoForall. by unseal. Qed.

Global Instance from_and_monPred_car P Q1 Q2 i:
  FromAnd P Q1 Q2 → FromAnd (P i) (Q1 i) (Q2 i).
Proof. rewrite /FromAnd=> <-. by unseal. Qed.
Global Instance into_and_monPred_car p P Q1 Q2 i:
  IntoAnd p P Q1 Q2 → IntoAnd p (P i) (Q1 i) (Q2 i).
Proof.
  rewrite /IntoAnd /bi_affinely_if /bi_persistently_if=>-[/(_ i)].
  by destruct p; unseal.
Qed.

Global Instance from_sep_monPred_car P Q1 Q2 i:
  FromSep P Q1 Q2 → FromSep (P i) (Q1 i) (Q2 i).
Proof. rewrite /FromSep=> <-. by unseal. Qed.
Global Instance into_sep_monPred_car P Q1 Q2 i:
  IntoSep P Q1 Q2 → IntoSep (P i) (Q1 i) (Q2 i).
Proof. rewrite /IntoSep=> ->. by unseal. Qed.

Global Instance from_or_monPred_car P Q1 Q2 i:
  FromOr P Q1 Q2 → FromOr (P i) (Q1 i) (Q2 i).
Proof. rewrite /FromOr=> <-. by unseal. Qed.
Global Instance into_or_monPred_car P Q1 Q2 i:
  IntoOr P Q1 Q2 → IntoOr (P i) (Q1 i) (Q2 i).
Proof. rewrite /IntoOr=> ->. by unseal. Qed.

Global Instance from_exist_monPred_car {A} P (Φ : A → monPred) i :
  FromExist P Φ → FromExist (P i) (λ a, Φ a i).
Proof. rewrite /FromExist=><-. by unseal. Qed.
Global Instance into_exist_monPred_car {A} P (Φ : A → monPred) i :
  IntoExist P Φ → IntoExist (P i) (λ a, Φ a i).
Proof. rewrite /IntoExist=>->. by unseal. Qed.

Global Instance from_forall_monPred_car {A} P (Φ : A → monPred) i :
  FromForall P Φ → FromForall (P i) (λ a, Φ a i).
Proof. rewrite /FromForall=><-. by unseal. Qed.
Global Instance into_forall_monPred_car {A} P (Φ : A → monPred) i :
  IntoForall P Φ → IntoForall (P i) (λ a, Φ a i).
Proof. rewrite /IntoForall=>->. by unseal. Qed.

Class MakeMonPredCar i P (Q : PROP) :=
  make_monPred_car : P i ⊣⊢ Q.
Arguments MakeMonPredCar _ _%I _%I.
Global Instance make_monPred_car_true i : MakeMonPredCar i True True.
Proof. rewrite /MakeMonPredCar. by unseal. Qed.
Global Instance make_monPred_car_emp i : MakeMonPredCar i emp emp.
Proof. rewrite /MakeMonPredCar. by unseal. Qed.
Global Instance make_monPred_car_default i P : MakeMonPredCar i P (P i).
Proof. by rewrite /MakeMonPredCar. Qed.

(* FIXME : there are two good ways to frame under a call to
   monPred_car. This may cause some backtracking in the typeclass
   search, and hence performance issues. *)
Global Instance frame_monPred_car i p P Q (Q' : PROP) R :
  Frame p R P Q → MakeMonPredCar i Q Q' → Frame p (R i) (P i) Q'.
Proof.
  rewrite /Frame /MakeMonPredCar /bi_affinely_if /bi_persistently_if=> <- <-.
  by destruct p; unseal.
Qed.
Global Instance frame_monPred_car_embed i p P Q (Q' R: PROP) :
  Frame p ⎡R⎤ P Q → MakeMonPredCar i Q Q' → Frame p R (P i) Q'.
Proof.
  rewrite /Frame /MakeMonPredCar /bi_affinely_if /bi_persistently_if=> <- <-.
  by destruct p; unseal.
Qed.

Global Instance from_modal_monPred_car i P Q :
  FromModal P Q → FromModal (P i) (Q i).
Proof. by rewrite /FromModal=>->. Qed.
End bi.

Section sbi.
Context {I : bi_index} {PROP : sbi}.
Local Notation monPred := (monPred I PROP).
Implicit Types P Q R : monPred.
Implicit Types φ : Prop.
Implicit Types i j : I.

Global Instance is_except_0_monPred_car i P :
  IsExcept0 P → IsExcept0 (P i).
Proof. rewrite /IsExcept0=>- [/(_ i)]. by unseal. Qed.
Global Instance into_except_0_monPred_car i P Q :
  IntoExcept0 P Q → IntoExcept0 (P i) (Q i).
Proof. rewrite /IntoExcept0=> ->. by unseal. Qed.
Global Instance into_later_monPred_car i n P Q :
  IntoLaterN n P Q → IntoLaterN n (P i) (Q i).
Proof.
  rewrite /IntoLaterN=> ->. induction n as [|? IH]=>//. rewrite /= -IH. by unseal.
Qed.
Global Instance from_later_monPred_car i n P Q :
  FromLaterN n P Q → FromLaterN n (P i) (Q i).
Proof.
  rewrite /FromLaterN=> <-. induction n as [|? IH]=>//. rewrite /= IH. by unseal.
Qed.
End sbi.
