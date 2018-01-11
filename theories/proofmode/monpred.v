From iris.bi Require Export monpred.
From iris.proofmode Require Import tactics.
Import MonPred.

Class MakeMonPredAt {I : biIndex} {PROP : bi} (i : I)
      (P : monPred I PROP) (𝓟 : PROP) :=
  make_monPred_at : P i ⊣⊢ 𝓟.
Arguments MakeMonPredAt {_ _} _ _%I _%I.
Hint Mode MakeMonPredAt + + - ! - : typeclass_instances.

Class IsBiIndexRel {I : biIndex} (i j : I) := is_bi_index_rel : i ⊑ j.
Hint Mode IsBiIndexRel + - - : typeclass_instances.
Instance is_bi_index_rel_refl {I : biIndex} (i : I) : IsBiIndexRel i i | 0.
Proof. by rewrite /IsBiIndexRel. Qed.
Hint Extern 1 (IsBiIndexRel _ _) => unfold IsBiIndexRel; assumption
            : typeclass_instances.

Section bi.
Context {I : biIndex} {PROP : bi}.
Local Notation monPred := (monPred I PROP).
Local Notation MakeMonPredAt := (@MakeMonPredAt I PROP).
Implicit Types P Q R : monPred.
Implicit Types 𝓟 𝓠 𝓡 : PROP.
Implicit Types φ : Prop.
Implicit Types i j : I.

Global Instance make_monPred_at_pure φ i : MakeMonPredAt i ⌜φ⌝ ⌜φ⌝.
Proof. rewrite /MakeMonPredAt. by unseal. Qed.
Global Instance make_monPred_at_internal_eq {A : ofeT} (x y : A) i :
  MakeMonPredAt i (x ≡ y) (x ≡ y).
Proof. rewrite /MakeMonPredAt. by unseal. Qed.
Global Instance make_monPred_at_emp i : MakeMonPredAt i emp emp.
Proof. rewrite /MakeMonPredAt. by unseal. Qed.
Global Instance make_monPred_at_sep i P 𝓟 Q 𝓠 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i Q 𝓠 →
  MakeMonPredAt i (P ∗ Q) (𝓟 ∗ 𝓠).
Proof. rewrite /MakeMonPredAt=><-<-. by unseal. Qed.
Global Instance make_monPred_at_and i P 𝓟 Q 𝓠 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i Q 𝓠 →
  MakeMonPredAt i (P ∧ Q) (𝓟 ∧ 𝓠).
Proof. rewrite /MakeMonPredAt=><-<-. by unseal. Qed.
Global Instance make_monPred_at_or i P 𝓟 Q 𝓠 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i Q 𝓠 →
  MakeMonPredAt i (P ∨ Q) (𝓟 ∨ 𝓠).
Proof. rewrite /MakeMonPredAt=><-<-. by unseal. Qed.
Global Instance make_monPred_at_forall {A} i (Φ : A → monPred) (Ψ : A → PROP) :
  (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → MakeMonPredAt i (∀ a, Φ a) (∀ a, Ψ a).
Proof. rewrite /MakeMonPredAt=>H. setoid_rewrite <- H. by unseal. Qed.
Global Instance make_monPred_at_exists {A} i (Φ : A → monPred) (Ψ : A → PROP) :
  (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → MakeMonPredAt i (∃ a, Φ a) (∃ a, Ψ a).
Proof. rewrite /MakeMonPredAt=>H. setoid_rewrite <- H. by unseal. Qed.
Global Instance make_monPred_at_persistently i P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (bi_persistently P) (bi_persistently 𝓟).
Proof. rewrite /MakeMonPredAt=><-. by unseal. Qed.
Global Instance make_monPred_at_affinely i P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (bi_affinely P) (bi_affinely 𝓟).
Proof. rewrite /MakeMonPredAt=><-. by unseal. Qed.
Global Instance make_monPred_at_absorbingly i P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (bi_absorbingly P) (bi_absorbingly 𝓟).
Proof. rewrite /MakeMonPredAt=><-. by unseal. Qed.
Global Instance make_monPred_at_persistently_if i P 𝓟 p :
  MakeMonPredAt i P 𝓟 →
  MakeMonPredAt i (bi_persistently_if p P) (bi_persistently_if p 𝓟).
Proof. destruct p; simpl; apply _. Qed.
Global Instance make_monPred_at_affinely_if i P 𝓟 p :
  MakeMonPredAt i P 𝓟 →
  MakeMonPredAt i (bi_affinely_if p P) (bi_affinely_if p 𝓟).
Proof. destruct p; simpl; apply _. Qed.
Global Instance make_monPred_at_embed i : MakeMonPredAt i ⎡P⎤ P.
Proof. rewrite /MakeMonPredAt. by unseal. Qed.
Global Instance make_monPred_at_in i j : MakeMonPredAt j (monPred_in i) ⌜i ⊑ j⌝.
Proof. rewrite /MakeMonPredAt. by unseal. Qed.
Global Instance make_monPred_at_default i P : MakeMonPredAt i P (P i) | 100.
Proof. by rewrite /MakeMonPredAt. Qed.

Global Instance from_assumption_make_monPred_at_l p i j P 𝓟 :
  MakeMonPredAt i P 𝓟 → IsBiIndexRel j i → FromAssumption p (P j) 𝓟.
Proof.
  rewrite /MakeMonPredAt /FromAssumption /IsBiIndexRel=><- ->.
  apply  bi.affinely_persistently_if_elim.
Qed.
Global Instance from_assumption_make_monPred_at_r p i j P 𝓟 :
  MakeMonPredAt i P 𝓟 → IsBiIndexRel i j → FromAssumption p 𝓟 (P j).
Proof.
  rewrite /MakeMonPredAt /FromAssumption /IsBiIndexRel=><- ->.
  apply  bi.affinely_persistently_if_elim.
Qed.

Global Instance as_valid_monPred_at φ P (Φ : I → PROP) :
  AsValid φ P → (∀ i, MakeMonPredAt i P (Φ i)) → AsValid' φ (∀ i, Φ i) | 100.
Proof.
  rewrite /MakeMonPredAt /AsValid' /AsValid /bi_valid=> -> EQ.
  setoid_rewrite <-EQ. unseal; split.
  - move=>[/= /bi.forall_intro //].
  - move=>HP. split=>i. rewrite /= HP bi.forall_elim //.
Qed.
Global Instance as_valid_monPred_at_wand φ P Q (Φ Ψ : I → PROP) :
  AsValid φ (P -∗ Q) →
  (∀ i, MakeMonPredAt i P (Φ i)) → (∀ i, MakeMonPredAt i Q (Ψ i)) →
  AsValid' φ (∀ i, Φ i -∗ Ψ i).
Proof.
  rewrite /AsValid' /AsValid /MakeMonPredAt. intros -> EQ1 EQ2.
  setoid_rewrite <-EQ1. setoid_rewrite <-EQ2. split.
  - move=>/bi.wand_entails HP. setoid_rewrite HP. by iIntros (i) "$".
  - move=>HP. apply bi.entails_wand. split=>i. iIntros "H". by iApply HP.
Qed.
Global Instance as_valid_monPred_at_equiv φ P Q (Φ Ψ : I → PROP) :
  AsValid φ (P ∗-∗ Q) →
  (∀ i, MakeMonPredAt i P (Φ i)) → (∀ i, MakeMonPredAt i Q (Ψ i)) →
  AsValid' φ (∀ i, Φ i ∗-∗ Ψ i).
Proof.
  rewrite /AsValid' /AsValid /MakeMonPredAt. intros -> EQ1 EQ2.
  setoid_rewrite <-EQ1. setoid_rewrite <-EQ2. split.
  - move=>/bi.wand_iff_equiv HP. setoid_rewrite HP. iIntros. iSplit; iIntros "$".
  - move=>HP. apply bi.equiv_wand_iff. split=>i. by iSplit; iIntros; iApply HP.
Qed.

Global Instance into_pure_monPred_at P φ i :
  IntoPure P φ → IntoPure (P i) φ.
Proof. rewrite /IntoPure=>->. by unseal. Qed.
Global Instance from_pure_monPred_at P φ i :
  FromPure P φ → FromPure (P i) φ.
Proof. rewrite /FromPure=><-. by unseal. Qed.
Global Instance into_pure_monPred_in i j :
  @IntoPure PROP (monPred_in i j) (i ⊑ j).
Proof. rewrite /IntoPure. by unseal. Qed.
Global Instance from_pure_monPred_in i j :
  @FromPure PROP (monPred_in i j) (i ⊑ j).
Proof. rewrite /FromPure. by unseal. Qed.

Global Instance into_internal_eq_monPred_at {A : ofeT} (x y : A) P i :
  IntoInternalEq P x y → IntoInternalEq (P i) x y.
Proof. rewrite /IntoInternalEq=> ->. by unseal. Qed.

Global Instance into_persistent_monPred_at p P Q 𝓠 i :
  IntoPersistent p P Q → MakeMonPredAt i Q 𝓠 → IntoPersistent p (P i) 𝓠 | 0.
Proof.
  rewrite /IntoPersistent /MakeMonPredAt /bi_persistently_if.
  unseal=>-[/(_ i) ?] <-. by destruct p.
Qed.

Global Instance from_always_monPred_at a pe P Q 𝓠 i :
  FromAlways a pe false P Q → MakeMonPredAt i Q 𝓠 →
  FromAlways a pe false (P i) 𝓠 | 0.
Proof.
  rewrite /FromAlways /MakeMonPredAt /bi_persistently_if /bi_affinely_if=><-.
  by destruct a, pe=><-; try unseal.
Qed.

Lemma into_wand_monPred_at_unknown_unknown p q R P 𝓟 Q 𝓠 i :
  IntoWand p q R P Q →  MakeMonPredAt i P 𝓟 → MakeMonPredAt i Q 𝓠 →
  IntoWand p q (R i) 𝓟 𝓠.
Proof.
  rewrite /IntoWand /MakeMonPredAt /bi_affinely_if /bi_persistently_if.
  destruct p, q=> /bi.wand_elim_l' [/(_ i) H] <- <-; apply bi.wand_intro_r;
  revert H; unseal; done.
Qed.
Lemma into_wand_monPred_at_unknown_known p q R P 𝓟 Q i j :
  IsBiIndexRel i j → IntoWand p q R P Q →
  MakeMonPredAt j P 𝓟 → IntoWand p q (R i) 𝓟 (Q j).
Proof.
  rewrite /IntoWand /IsBiIndexRel /MakeMonPredAt=>-> ? ?.
  eapply into_wand_monPred_at_unknown_unknown=>//. apply _.
Qed.
Lemma into_wand_monPred_at_known_unknown_le p q R P Q 𝓠 i j :
  IsBiIndexRel i j → IntoWand p q R P Q →
  MakeMonPredAt j Q 𝓠 → IntoWand p q (R i) (P j) 𝓠.
Proof.
  rewrite /IntoWand /IsBiIndexRel /MakeMonPredAt=>-> ? ?.
  eapply into_wand_monPred_at_unknown_unknown=>//. apply _.
Qed.
Lemma into_wand_monPred_at_known_unknown_ge p q R P Q 𝓠 i j :
  IsBiIndexRel i j → IntoWand p q R P Q →
  MakeMonPredAt j Q 𝓠 → IntoWand p q (R j) (P i) 𝓠.
Proof.
  rewrite /IntoWand /IsBiIndexRel /MakeMonPredAt=>-> ? ?.
  eapply into_wand_monPred_at_unknown_unknown=>//. apply _.
Qed.

Global Instance into_wand_wand'_monPred p q P Q 𝓟 𝓠 i :
  IntoWand' p q ((P -∗ Q) i) 𝓟 𝓠 → IntoWand p q ((P -∗ Q) i) 𝓟 𝓠 | 100.
Proof. done. Qed.
Global Instance into_wand_impl'_monPred p q P Q 𝓟 𝓠 i :
  IntoWand' p q ((P → Q) i) 𝓟 𝓠 → IntoWand p q ((P → Q) i) 𝓟 𝓠 | 100.
Proof. done. Qed.

Global Instance from_forall_monPred_at_wand P Q (Φ Ψ : I → PROP) i :
  (∀ j, MakeMonPredAt j P (Φ j)) → (∀ j, MakeMonPredAt j Q (Ψ j)) →
  FromForall ((P -∗ Q) i)%I (λ j, ⌜i ⊑ j⌝ → Φ j -∗ Ψ j)%I.
Proof.
  rewrite /FromForall /MakeMonPredAt. unseal=> H1 H2. do 2 f_equiv.
  by rewrite H1 H2.
Qed.
Global Instance from_forall_monPred_at_impl P Q (Φ Ψ : I → PROP) i :
  (∀ j, MakeMonPredAt j P (Φ j)) → (∀ j, MakeMonPredAt j Q (Ψ j)) →
  FromForall ((P → Q) i)%I (λ j, ⌜i ⊑ j⌝ → Φ j → Ψ j)%I.
Proof.
  rewrite /FromForall /MakeMonPredAt. unseal=> H1 H2. do 2 f_equiv.
  by rewrite H1 H2 bi.pure_impl_forall.
Qed.

Global Instance into_forall_monPred_at_index P i :
  IntoForall (P i) (λ j, ⌜i ⊑ j⌝ → P j)%I | 100.
Proof.
  rewrite /IntoForall. setoid_rewrite bi.pure_impl_forall.
  do 2 apply bi.forall_intro=>?. by f_equiv.
Qed.

Global Instance from_and_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  FromAnd P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  FromAnd (P i) 𝓠1 𝓠2.
Proof. rewrite /FromAnd /MakeMonPredAt /MakeMonPredAt=> <- <- <-. by unseal. Qed.
Global Instance into_and_monPred_at p P Q1 𝓠1 Q2 𝓠2 i :
  IntoAnd p P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  IntoAnd p (P i) 𝓠1 𝓠2.
Proof.
  rewrite /IntoAnd /MakeMonPredAt /bi_affinely_if /bi_persistently_if.
  destruct p=>-[/(_ i) H] <- <-; revert H; unseal; done.
Qed.

Global Instance from_sep_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  FromSep P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  FromSep (P i) 𝓠1 𝓠2.
Proof. rewrite /FromSep /MakeMonPredAt=> <- <- <-. by unseal. Qed.
Global Instance into_sep_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  IntoSep P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  IntoSep (P i) 𝓠1 𝓠2.
Proof. rewrite /IntoSep /MakeMonPredAt=> -> <- <-. by unseal. Qed.

Global Instance from_or_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  FromOr P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  FromOr (P i) 𝓠1 𝓠2.
Proof. rewrite /FromOr /MakeMonPredAt=> <- <- <-. by unseal. Qed.
Global Instance into_or_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  IntoOr P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  IntoOr (P i) 𝓠1 𝓠2.
Proof. rewrite /IntoOr /MakeMonPredAt=> -> <- <-. by unseal. Qed.

Global Instance from_exist_monPred_at {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  FromExist P Φ → (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → FromExist (P i) Ψ.
Proof.
  rewrite /FromExist /MakeMonPredAt=><- H. setoid_rewrite <- H. by unseal.
Qed.
Global Instance into_exist_monPred_at {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  IntoExist P Φ → (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → IntoExist (P i) Ψ.
Proof.
  rewrite /IntoExist /MakeMonPredAt=>-> H. setoid_rewrite <- H. by unseal.
Qed.

Global Instance foram_forall_monPred_at_plainly i P Φ :
  (∀ i, MakeMonPredAt i P (Φ i)) →
  FromForall (bi_plainly P i) (λ j, bi_plainly (Φ j)).
Proof. rewrite /FromForall /MakeMonPredAt=>H. unseal. do 3 f_equiv. rewrite H //. Qed.
Global Instance into_forall_monPred_at_plainly i P Φ :
  (∀ i, MakeMonPredAt i P (Φ i)) →
  IntoForall (bi_plainly P i) (λ j, bi_plainly (Φ j)).
Proof. rewrite /IntoForall /MakeMonPredAt=>H. unseal. do 3 f_equiv. rewrite H //. Qed.

Global Instance from_forall_monPred_at_all P (Φ : I → PROP) i :
  (∀ i, MakeMonPredAt i P (Φ i)) → FromForall (monPred_all P i) Φ.
Proof.
  rewrite /FromForall /MakeMonPredAt=>H. setoid_rewrite <- H. by unseal.
Qed.
Global Instance into_forall_monPred_at_all P (Φ : I → PROP) i :
  (∀ i, MakeMonPredAt i P (Φ i)) → IntoForall (monPred_all P i) Φ.
Proof.
  rewrite /IntoForall /MakeMonPredAt=>H. setoid_rewrite <- H. by unseal.
Qed.

Global Instance from_exist_monPred_at_ex P (Φ : I → PROP) i :
  (∀ i, MakeMonPredAt i P (Φ i)) → FromExist (monPred_ex P i) Φ.
Proof.
  rewrite /FromExist /MakeMonPredAt=>H. setoid_rewrite <- H. by unseal.
Qed.
Global Instance into_exist_monPred_at_ex P (Φ : I → PROP) i :
  (∀ i, MakeMonPredAt i P (Φ i)) → IntoExist (monPred_ex P i) Φ.
Proof.
  rewrite /IntoExist /MakeMonPredAt=>H. setoid_rewrite <- H. by unseal.
Qed.

Global Instance from_forall_monPred_at {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  FromForall P Φ → (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → FromForall (P i) Ψ.
Proof.
  rewrite /FromForall /MakeMonPredAt=><- H. setoid_rewrite <- H. by unseal.
Qed.
Global Instance into_forall_monPred_at {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  IntoForall P Φ → (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → IntoForall (P i) Ψ.
Proof.
  rewrite /IntoForall /MakeMonPredAt=>-> H. setoid_rewrite <- H. by unseal.
Qed.

(* FIXME : there are two good ways to frame under a call to
   monPred_at. This may cause some backtracking in the typeclass
   search, and hence performance issues. *)
Global Instance frame_monPred_at p P Q 𝓠 R i j :
  IsBiIndexRel i j → Frame p R P Q → MakeMonPredAt j Q 𝓠 →
  Frame p (R i) (P j) 𝓠.
Proof.
  rewrite /Frame /MakeMonPredAt /bi_affinely_if /bi_persistently_if
          /IsBiIndexRel=> Hij <- <-.
  by destruct p; rewrite Hij; unseal.
Qed.
Global Instance frame_monPred_at_embed i p P Q 𝓠 𝓡 :
  Frame p ⎡𝓡⎤ P Q → MakeMonPredAt i Q 𝓠 → Frame p 𝓡 (P i) 𝓠.
Proof.
  rewrite /Frame /MakeMonPredAt /bi_affinely_if /bi_persistently_if=> <- <-.
  by destruct p; unseal.
Qed.

Global Instance from_modal_monPred_at i P Q 𝓠 :
  FromModal P Q → MakeMonPredAt i Q 𝓠 → FromModal (P i) 𝓠.
Proof. by rewrite /FromModal /MakeMonPredAt=> <- <-. Qed.
End bi.

(* When P and/or Q are evars when doing typeclass search on [IntoWand
   (R i) P Q], we use [MakeMonPredAt] in order to normalize the
   result of unification. However, when they are not evars, we want to
   propagate the known information through typeclass search. Hence, we
   do not want to use [MakeMonPredAt].

   As a result, depending on P and Q being evars, we use a different
   version of [into_wand_monPred_at_xx_xx]. *)
Hint Extern 3 (IntoWand _ _ (monPred_at _ _) ?P ?Q) =>
     is_evar P; is_evar Q;
     eapply @into_wand_monPred_at_unknown_unknown
     : typeclass_instances.
Hint Extern 2 (IntoWand _ _ (monPred_at _ _) ?P (monPred_at ?Q _)) =>
     eapply @into_wand_monPred_at_unknown_known
     : typeclass_instances.
Hint Extern 2 (IntoWand _ _ (monPred_at _ _) (monPred_at ?P _) ?Q) =>
     eapply @into_wand_monPred_at_known_unknown_le
     : typeclass_instances.
Hint Extern 2 (IntoWand _ _ (monPred_at _ _) (monPred_at ?P _) ?Q) =>
     eapply @into_wand_monPred_at_known_unknown_ge
     : typeclass_instances.

Section sbi.
Context {I : biIndex} {PROP : sbi}.
Local Notation monPred := (monPred I PROP).
Implicit Types P Q R : monPred.
Implicit Types 𝓟 𝓠 𝓡 : PROP.
Implicit Types φ : Prop.
Implicit Types i j : I.

Global Instance is_except_0_monPred_at i P :
  IsExcept0 P → IsExcept0 (P i).
Proof. rewrite /IsExcept0=>- [/(_ i)]. by unseal. Qed.

Global Instance make_monPred_at_except_0 i P 𝓠 :
  MakeMonPredAt i P 𝓠 → MakeMonPredAt i (◇ P)%I (◇ 𝓠)%I.
Proof. rewrite /MakeMonPredAt=><-. by unseal. Qed.
Global Instance make_monPred_at_later i P 𝓠 :
  MakeMonPredAt i P 𝓠 → MakeMonPredAt i (▷ P)%I (▷ 𝓠)%I.
Proof. rewrite /MakeMonPredAt=><-. by unseal. Qed.
Global Instance make_monPred_at_laterN i n P 𝓠 :
  MakeMonPredAt i P 𝓠 → MakeMonPredAt i (▷^n P)%I (▷^n 𝓠)%I.
Proof. rewrite /MakeMonPredAt=> <-. elim n=>//= ? <-. by unseal. Qed.

Global Instance into_except_0_monPred_at_fwd i P Q 𝓠 :
  IntoExcept0 P Q → MakeMonPredAt i Q 𝓠 → IntoExcept0 (P i) 𝓠.
Proof. rewrite /IntoExcept0 /MakeMonPredAt=> -> <-. by unseal. Qed.
Global Instance into_except_0_monPred_at_bwd i P 𝓟 Q :
  IntoExcept0 P Q → MakeMonPredAt i P 𝓟 → IntoExcept0 𝓟 (Q i).
Proof. rewrite /IntoExcept0 /MakeMonPredAt=> H <-. rewrite H. by unseal. Qed.

Global Instance into_later_monPred_at i n P Q 𝓠 :
  IntoLaterN n P Q → MakeMonPredAt i Q 𝓠 → IntoLaterN n (P i) 𝓠.
Proof.
  rewrite /IntoLaterN /MakeMonPredAt=> -> <-. elim n=>//= ? <-. by unseal.
Qed.
Global Instance from_later_monPred_at i n P Q 𝓠 :
  FromLaterN n P Q → MakeMonPredAt i Q 𝓠 → FromLaterN n (P i) 𝓠.
Proof. rewrite /FromLaterN /MakeMonPredAt=> <- <-. elim n=>//= ? ->. by unseal. Qed.
End sbi.
