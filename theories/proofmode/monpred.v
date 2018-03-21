From iris.bi Require Export monpred.
From iris.bi Require Import plainly.
From iris.proofmode Require Import tactics class_instances.

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

Section modalities.
  Context {I : biIndex} {PROP : bi}.

  Lemma modality_objectively_mixin :
    modality_mixin (@monPred_objectively I PROP)
      (MIEnvFilter Objective) (MIEnvFilter Objective).
  Proof.
    split; simpl; split_and?; intros;
      try match goal with H : TCDiag _ _ _ |- _ => destruct H end;
      eauto using bi.equiv_entails_sym, objective_objectively,
        monPred_objectively_mono, monPred_objectively_and,
        monPred_objectively_sep_2 with typeclass_instances.
  Qed.
  Definition modality_objectively :=
    Modality _ modality_objectively_mixin.
End modalities.

Section bi.
Context {I : biIndex} {PROP : bi}.
Local Notation monPredI := (monPredI I PROP).
Local Notation monPred := (monPred I PROP).
Local Notation MakeMonPredAt := (@MakeMonPredAt I PROP).
Implicit Types P Q R : monPred.
Implicit Types 𝓟 𝓠 𝓡 : PROP.
Implicit Types φ : Prop.
Implicit Types i j : I.

Global Instance from_modal_objectively P :
  FromModal modality_objectively (<obj> P) (<obj> P) P | 1.
Proof. by rewrite /FromModal. Qed.
Global Instance from_modal_subjectively P :
  FromModal modality_id (<subj> P) (<subj> P) P | 1.
Proof. by rewrite /FromModal /= -monPred_subjectively_intro. Qed.

Global Instance from_modal_affinely_monPred_at `(sel : A) P Q 𝓠 i :
  FromModal modality_affinely sel P Q → MakeMonPredAt i Q 𝓠 →
  FromModal modality_affinely sel (P i) 𝓠 | 0.
Proof.
  rewrite /FromModal /MakeMonPredAt /==> <- <-. by rewrite monPred_at_affinely.
Qed.
Global Instance from_modal_persistently_monPred_at `(sel : A) P Q 𝓠 i :
  FromModal modality_persistently sel P Q → MakeMonPredAt i Q 𝓠 →
  FromModal modality_persistently sel (P i) 𝓠 | 0.
Proof.
  rewrite /FromModal /MakeMonPredAt /==> <- <-. by rewrite monPred_at_persistently.
Qed.
Global Instance from_modal_affinely_persistently_monPred_at `(sel : A) P Q 𝓠 i :
  FromModal modality_intuitionistically sel P Q → MakeMonPredAt i Q 𝓠 →
  FromModal modality_intuitionistically sel (P i) 𝓠 | 0.
Proof.
  rewrite /FromModal /MakeMonPredAt /==> <- <-.
  by rewrite monPred_at_affinely monPred_at_persistently.
Qed.
Global Instance from_modal_id_monPred_at `(sel : A) P Q 𝓠 i :
  FromModal modality_id sel P Q → MakeMonPredAt i Q 𝓠 →
  FromModal modality_id sel (P i) 𝓠.
Proof. by rewrite /FromModal /MakeMonPredAt=> <- <-. Qed.

Global Instance make_monPred_at_pure φ i : MakeMonPredAt i ⌜φ⌝ ⌜φ⌝.
Proof. by rewrite /MakeMonPredAt monPred_at_pure. Qed.
Global Instance make_monPred_at_emp i : MakeMonPredAt i emp emp.
Proof. by rewrite /MakeMonPredAt monPred_at_emp. Qed.
Global Instance make_monPred_at_sep i P 𝓟 Q 𝓠 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i Q 𝓠 →
  MakeMonPredAt i (P ∗ Q) (𝓟 ∗ 𝓠).
Proof. by rewrite /MakeMonPredAt monPred_at_sep=><-<-. Qed.
Global Instance make_monPred_at_and i P 𝓟 Q 𝓠 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i Q 𝓠 →
  MakeMonPredAt i (P ∧ Q) (𝓟 ∧ 𝓠).
Proof. by rewrite /MakeMonPredAt monPred_at_and=><-<-. Qed.
Global Instance make_monPred_at_or i P 𝓟 Q 𝓠 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i Q 𝓠 →
  MakeMonPredAt i (P ∨ Q) (𝓟 ∨ 𝓠).
Proof. by rewrite /MakeMonPredAt monPred_at_or=><-<-. Qed.
Global Instance make_monPred_at_forall {A} i (Φ : A → monPred) (Ψ : A → PROP) :
  (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → MakeMonPredAt i (∀ a, Φ a) (∀ a, Ψ a).
Proof. rewrite /MakeMonPredAt monPred_at_forall=>H. by setoid_rewrite <- H. Qed.
Global Instance make_monPred_at_exists {A} i (Φ : A → monPred) (Ψ : A → PROP) :
  (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → MakeMonPredAt i (∃ a, Φ a) (∃ a, Ψ a).
Proof. rewrite /MakeMonPredAt monPred_at_exist=>H. by setoid_rewrite <- H. Qed.
Global Instance make_monPred_at_persistently i P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (<pers> P) (<pers> 𝓟).
Proof. by rewrite /MakeMonPredAt monPred_at_persistently=><-. Qed.
Global Instance make_monPred_at_affinely i P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (<affine> P) (<affine> 𝓟).
Proof. by rewrite /MakeMonPredAt monPred_at_affinely=><-. Qed.
Global Instance make_monPred_at_absorbingly i P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (<absorb> P) (<absorb> 𝓟).
Proof. by rewrite /MakeMonPredAt monPred_at_absorbingly=><-. Qed.
Global Instance make_monPred_at_persistently_if i P 𝓟 p :
  MakeMonPredAt i P 𝓟 →
  MakeMonPredAt i (<pers>?p P) (<pers>?p 𝓟).
Proof. destruct p; simpl; apply _. Qed.
Global Instance make_monPred_at_affinely_if i P 𝓟 p :
  MakeMonPredAt i P 𝓟 →
  MakeMonPredAt i (<affine>?p P) (<affine>?p 𝓟).
Proof. destruct p; simpl; apply _. Qed.
Global Instance make_monPred_at_embed i 𝓟 : MakeMonPredAt i ⎡𝓟⎤ 𝓟.
Proof. by rewrite /MakeMonPredAt monPred_at_embed. Qed.
Global Instance make_monPred_at_in i j : MakeMonPredAt j (monPred_in i) ⌜i ⊑ j⌝.
Proof. by rewrite /MakeMonPredAt monPred_at_in. Qed.
Global Instance make_monPred_at_default i P : MakeMonPredAt i P (P i) | 100.
Proof. by rewrite /MakeMonPredAt. Qed.
Global Instance make_monPred_at_bupd `{BiBUpd PROP} i P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (|==> P)%I (|==> 𝓟)%I.
Proof. by rewrite /MakeMonPredAt monPred_at_bupd=> <-. Qed.

Global Instance from_assumption_make_monPred_at_l p i j P 𝓟 :
  MakeMonPredAt i P 𝓟 → IsBiIndexRel j i → KnownLFromAssumption p (P j) 𝓟.
Proof.
  rewrite /MakeMonPredAt /KnownLFromAssumption /FromAssumption /IsBiIndexRel=><- ->.
  apply  bi.intuitionistically_if_elim.
Qed.
Global Instance from_assumption_make_monPred_at_r p i j P 𝓟 :
  MakeMonPredAt i P 𝓟 → IsBiIndexRel i j → KnownRFromAssumption p 𝓟 (P j).
Proof.
  rewrite /MakeMonPredAt /KnownRFromAssumption /FromAssumption /IsBiIndexRel=><- ->.
  apply  bi.intuitionistically_if_elim.
Qed.

Global Instance from_assumption_make_monPred_objectively P Q :
  FromAssumption p P Q → KnownLFromAssumption p (<obj> P) Q.
Proof.
  intros ?.
  by rewrite /KnownLFromAssumption /FromAssumption monPred_objectively_elim.
Qed.
Global Instance from_assumption_make_monPred_subjectively P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (<subj> Q).
Proof.
  intros ?.
  by rewrite /KnownRFromAssumption /FromAssumption -monPred_subjectively_intro.
Qed.

Global Instance as_emp_valid_monPred_at φ P (Φ : I → PROP) :
  AsEmpValid0 φ P → (∀ i, MakeMonPredAt i P (Φ i)) → AsEmpValid φ (∀ i, Φ i) | 100.
Proof.
  rewrite /MakeMonPredAt /AsEmpValid0 /AsEmpValid /bi_emp_valid=> -> EQ.
  setoid_rewrite <-EQ. split.
  - move=>[H]. apply bi.forall_intro=>i. rewrite -H. by rewrite monPred_at_emp.
  - move=>HP. split=>i. rewrite monPred_at_emp HP bi.forall_elim //.
Qed.
Global Instance as_emp_valid_monPred_at_wand φ P Q (Φ Ψ : I → PROP) :
  AsEmpValid0 φ (P -∗ Q) →
  (∀ i, MakeMonPredAt i P (Φ i)) → (∀ i, MakeMonPredAt i Q (Ψ i)) →
  AsEmpValid φ (∀ i, Φ i -∗ Ψ i).
Proof.
  rewrite /AsEmpValid0 /AsEmpValid /MakeMonPredAt. intros -> EQ1 EQ2.
  setoid_rewrite <-EQ1. setoid_rewrite <-EQ2. split.
  - move=>/bi.wand_entails HP. setoid_rewrite HP. by iIntros (i) "$".
  - move=>HP. apply bi.entails_wand. split=>i. iIntros "H". by iApply HP.
Qed.
Global Instance as_emp_valid_monPred_at_equiv φ P Q (Φ Ψ : I → PROP) :
  AsEmpValid0 φ (P ∗-∗ Q) →
  (∀ i, MakeMonPredAt i P (Φ i)) → (∀ i, MakeMonPredAt i Q (Ψ i)) →
  AsEmpValid φ (∀ i, Φ i ∗-∗ Ψ i).
Proof.
  rewrite /AsEmpValid0 /AsEmpValid /MakeMonPredAt. intros -> EQ1 EQ2.
  setoid_rewrite <-EQ1. setoid_rewrite <-EQ2. split.
  - move=>/bi.wand_iff_equiv HP. setoid_rewrite HP. iIntros. iSplit; iIntros "$".
  - move=>HP. apply bi.equiv_wand_iff. split=>i. by iSplit; iIntros; iApply HP.
Qed.

Global Instance into_pure_monPred_at P φ i : IntoPure P φ → IntoPure (P i) φ.
Proof. rewrite /IntoPure=>->. by rewrite monPred_at_pure. Qed.
Global Instance from_pure_monPred_at a P φ i : FromPure a P φ → FromPure a (P i) φ.
Proof. rewrite /FromPure=><-. by rewrite monPred_at_affinely_if monPred_at_pure. Qed.
Global Instance into_pure_monPred_in i j : @IntoPure PROP (monPred_in i j) (i ⊑ j).
Proof. by rewrite /IntoPure monPred_at_in. Qed.
Global Instance from_pure_monPred_in i j af : @FromPure PROP af (monPred_in i j) (i ⊑ j).
Proof. by rewrite /FromPure monPred_at_in bi.affinely_if_elim. Qed.

Global Instance into_persistent_monPred_at p P Q 𝓠 i :
  IntoPersistent p P Q → MakeMonPredAt i Q 𝓠 → IntoPersistent p (P i) 𝓠 | 0.
Proof.
  rewrite /IntoPersistent /MakeMonPredAt  =>-[/(_ i) ?] <-.
  by rewrite -monPred_at_persistently -monPred_at_persistently_if.
Qed.

Lemma into_wand_monPred_at_unknown_unknown p q R P 𝓟 Q 𝓠 i :
  IntoWand p q R P Q →  MakeMonPredAt i P 𝓟 → MakeMonPredAt i Q 𝓠 →
  IntoWand p q (R i) 𝓟 𝓠.
Proof.
  rewrite /IntoWand /MakeMonPredAt /bi_affinely_if /bi_persistently_if.
  destruct p, q=> /bi.wand_elim_l' [/(_ i) H] <- <-; apply bi.wand_intro_r;
  revert H; by rewrite monPred_at_sep ?monPred_at_affinely ?monPred_at_persistently.
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
  rewrite /FromForall /MakeMonPredAt monPred_at_wand=> H1 H2. do 2 f_equiv.
  by rewrite H1 H2.
Qed.
Global Instance from_forall_monPred_at_impl P Q (Φ Ψ : I → PROP) i :
  (∀ j, MakeMonPredAt j P (Φ j)) → (∀ j, MakeMonPredAt j Q (Ψ j)) →
  FromForall ((P → Q) i)%I (λ j, ⌜i ⊑ j⌝ → Φ j → Ψ j)%I.
Proof.
  rewrite /FromForall /MakeMonPredAt monPred_at_impl=> H1 H2. do 2 f_equiv.
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
Proof.
  rewrite /FromAnd /MakeMonPredAt /MakeMonPredAt=> <- <- <-.
  by rewrite monPred_at_and.
Qed.
Global Instance into_and_monPred_at p P Q1 𝓠1 Q2 𝓠2 i :
  IntoAnd p P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  IntoAnd p (P i) 𝓠1 𝓠2.
Proof.
  rewrite /IntoAnd /MakeMonPredAt /bi_affinely_if /bi_persistently_if.
  destruct p=>-[/(_ i) H] <- <-; revert H;
  by rewrite ?monPred_at_affinely ?monPred_at_persistently monPred_at_and.
Qed.

Global Instance from_sep_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  FromSep P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  FromSep (P i) 𝓠1 𝓠2.
Proof. rewrite /FromSep /MakeMonPredAt=> <- <- <-. by rewrite monPred_at_sep. Qed.
Global Instance into_sep_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  IntoSep P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  IntoSep (P i) 𝓠1 𝓠2.
Proof. rewrite /IntoSep /MakeMonPredAt=> -> <- <-. by rewrite monPred_at_sep. Qed.
Global Instance from_or_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  FromOr P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  FromOr (P i) 𝓠1 𝓠2.
Proof. rewrite /FromOr /MakeMonPredAt=> <- <- <-. by rewrite monPred_at_or. Qed.
Global Instance into_or_monPred_at P Q1 𝓠1 Q2 𝓠2 i :
  IntoOr P Q1 Q2 → MakeMonPredAt i Q1 𝓠1 → MakeMonPredAt i Q2 𝓠2 →
  IntoOr (P i) 𝓠1 𝓠2.
Proof. rewrite /IntoOr /MakeMonPredAt=> -> <- <-. by rewrite monPred_at_or. Qed.

Global Instance from_exist_monPred_at {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  FromExist P Φ → (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → FromExist (P i) Ψ.
Proof.
  rewrite /FromExist /MakeMonPredAt=><- H. setoid_rewrite <- H.
  by rewrite monPred_at_exist.
Qed.
Global Instance into_exist_monPred_at {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  IntoExist P Φ → (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → IntoExist (P i) Ψ.
Proof.
  rewrite /IntoExist /MakeMonPredAt=>-> H. setoid_rewrite <- H.
  by rewrite monPred_at_exist.
Qed.

Global Instance from_forall_monPred_at_objectively P (Φ : I → PROP) i :
  (∀ i, MakeMonPredAt i P (Φ i)) → FromForall ((<obj> P) i)%I Φ.
Proof.
  rewrite /FromForall /MakeMonPredAt monPred_at_objectively=>H. by setoid_rewrite <- H.
Qed.
Global Instance into_forall_monPred_at_objectively P (Φ : I → PROP) i :
  (∀ i, MakeMonPredAt i P (Φ i)) → IntoForall ((<obj> P) i) Φ.
Proof.
  rewrite /IntoForall /MakeMonPredAt monPred_at_objectively=>H. by setoid_rewrite <- H.
Qed.

Global Instance from_exist_monPred_at_ex P (Φ : I → PROP) i :
  (∀ i, MakeMonPredAt i P (Φ i)) → FromExist ((<subj> P) i) Φ.
Proof.
  rewrite /FromExist /MakeMonPredAt monPred_at_subjectively=>H. by setoid_rewrite <- H.
Qed.
Global Instance into_exist_monPred_at_ex P (Φ : I → PROP) i :
  (∀ i, MakeMonPredAt i P (Φ i)) → IntoExist ((<subj> P) i) Φ.
Proof.
  rewrite /IntoExist /MakeMonPredAt monPred_at_subjectively=>H. by setoid_rewrite <- H.
Qed.

Global Instance from_forall_monPred_at {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  FromForall P Φ → (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → FromForall (P i) Ψ.
Proof.
  rewrite /FromForall /MakeMonPredAt=><- H. setoid_rewrite <- H.
  by rewrite monPred_at_forall.
Qed.
Global Instance into_forall_monPred_at {A} P (Φ : A → monPred) (Ψ : A → PROP) i :
  IntoForall P Φ → (∀ a, MakeMonPredAt i (Φ a) (Ψ a)) → IntoForall (P i) Ψ.
Proof.
  rewrite /IntoForall /MakeMonPredAt=>-> H. setoid_rewrite <- H.
  by rewrite monPred_at_forall.
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
  destruct p; by rewrite Hij monPred_at_sep ?monPred_at_affinely ?monPred_at_persistently.
Qed.
Global Instance frame_monPred_at_embed i p P Q 𝓠 𝓡 :
  Frame p ⎡𝓡⎤ P Q → MakeMonPredAt i Q 𝓠 → Frame p 𝓡 (P i) 𝓠.
Proof.
  rewrite /Frame /MakeMonPredAt /bi_affinely_if /bi_persistently_if=> <- <-.
  destruct p; by rewrite monPred_at_sep ?monPred_at_affinely
                         ?monPred_at_persistently monPred_at_embed.
Qed.

Global Instance into_embed_objective P :
  Objective P → IntoEmbed P (∀ i, P i).
Proof.
  rewrite /IntoEmbed=> ?.
  by rewrite {1}(objective_objectively P) monPred_objectively_unfold.
Qed.

Global Instance elim_modal_at_bupd_goal `{BiBUpd PROP} φ 𝓟 𝓟' Q Q' i :
  ElimModal φ 𝓟 𝓟' (|==> Q i) (|==> Q' i) →
  ElimModal φ 𝓟 𝓟' ((|==> Q) i) ((|==> Q') i).
Proof. by rewrite /ElimModal !monPred_at_bupd. Qed.
Global Instance elim_modal_at_bupd_hyp `{BiBUpd PROP} φ P 𝓟 𝓟' 𝓠 𝓠' i:
  MakeMonPredAt i P 𝓟 →
  ElimModal φ (|==> 𝓟) 𝓟' 𝓠 𝓠' →
  ElimModal φ ((|==> P) i) 𝓟' 𝓠 𝓠'.
Proof. by rewrite /MakeMonPredAt /ElimModal monPred_at_bupd=><-. Qed.

Global Instance add_modal_at_bupd_goal `{BiBUpd PROP} φ 𝓟 𝓟' Q i :
  AddModal 𝓟 𝓟' (|==> Q i)%I → AddModal 𝓟 𝓟' ((|==> Q) i).
Proof. by rewrite /AddModal !monPred_at_bupd. Qed.
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

Global Instance from_forall_monPred_at_plainly `{BiPlainly PROP} i P Φ :
  (∀ i, MakeMonPredAt i P (Φ i)) →
  FromForall ((■ P) i) (λ j, ■ (Φ j))%I.
Proof.
  rewrite /FromForall /MakeMonPredAt=>HPΦ. rewrite monPred_at_plainly.
  by setoid_rewrite HPΦ.
Qed.
Global Instance into_forall_monPred_at_plainly `{BiPlainly PROP} i P Φ :
  (∀ i, MakeMonPredAt i P (Φ i)) →
  IntoForall ((■ P) i) (λ j, ■ (Φ j))%I.
Proof.
  rewrite /IntoForall /MakeMonPredAt=>HPΦ. rewrite monPred_at_plainly.
  by setoid_rewrite HPΦ.
Qed.

Global Instance is_except_0_monPred_at i P :
  IsExcept0 P → IsExcept0 (P i).
Proof. rewrite /IsExcept0=>- [/(_ i)]. by rewrite monPred_at_except_0. Qed.

Global Instance make_monPred_at_internal_eq {A : ofeT} (x y : A) i :
  @MakeMonPredAt I PROP i (x ≡ y) (x ≡ y).
Proof. by rewrite /MakeMonPredAt monPred_at_internal_eq. Qed.
Global Instance make_monPred_at_except_0 i P 𝓠 :
  MakeMonPredAt i P 𝓠 → MakeMonPredAt i (◇ P)%I (◇ 𝓠)%I.
Proof. by rewrite /MakeMonPredAt monPred_at_except_0=><-. Qed.
Global Instance make_monPred_at_later i P 𝓠 :
  MakeMonPredAt i P 𝓠 → MakeMonPredAt i (▷ P)%I (▷ 𝓠)%I.
Proof. by rewrite /MakeMonPredAt monPred_at_later=><-. Qed.
Global Instance make_monPred_at_laterN i n P 𝓠 :
  MakeMonPredAt i P 𝓠 → MakeMonPredAt i (▷^n P)%I (▷^n 𝓠)%I.
Proof. rewrite /MakeMonPredAt=> <-. elim n=>//= ? <-. by rewrite monPred_at_later. Qed.
Global Instance make_monPred_at_fupd `{BiFUpd PROP} i E1 E2 P 𝓟 :
  MakeMonPredAt i P 𝓟 → MakeMonPredAt i (|={E1,E2}=> P)%I (|={E1,E2}=> 𝓟)%I.
Proof. by rewrite /MakeMonPredAt monPred_at_fupd=> <-. Qed.

Global Instance into_internal_eq_monPred_at {A : ofeT} (x y : A) P i :
  IntoInternalEq P x y → IntoInternalEq (P i) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite monPred_at_internal_eq. Qed.

Global Instance into_except_0_monPred_at_fwd i P Q 𝓠 :
  IntoExcept0 P Q → MakeMonPredAt i Q 𝓠 → IntoExcept0 (P i) 𝓠.
Proof. rewrite /IntoExcept0 /MakeMonPredAt=> -> <-. by rewrite monPred_at_except_0. Qed.
Global Instance into_except_0_monPred_at_bwd i P 𝓟 Q :
  IntoExcept0 P Q → MakeMonPredAt i P 𝓟 → IntoExcept0 𝓟 (Q i).
Proof. rewrite /IntoExcept0 /MakeMonPredAt=> H <-. by rewrite H monPred_at_except_0. Qed.

Global Instance maybe_into_later_monPred_at i n P Q 𝓠 :
  IntoLaterN false n P Q → MakeMonPredAt i Q 𝓠 →
  IntoLaterN false n (P i) 𝓠.
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN /MakeMonPredAt=> -> <-. elim n=>//= ? <-.
  by rewrite monPred_at_later.
Qed.
Global Instance from_later_monPred_at i `(sel : A) n P Q 𝓠 :
  FromModal (modality_laterN n) sel P Q → MakeMonPredAt i Q 𝓠 →
  FromModal (modality_laterN n) sel (P i) 𝓠.
Proof.
  rewrite /FromModal /MakeMonPredAt=> <- <-. elim n=>//= ? ->.
  by rewrite monPred_at_later.
Qed.

Global Instance elim_modal_at_fupd_goal `{BiFUpd PROP} φ E1 E2 E3 𝓟 𝓟' Q Q' i :
  ElimModal φ 𝓟 𝓟' (|={E1,E3}=> Q i) (|={E2,E3}=> Q' i) →
  ElimModal φ 𝓟 𝓟' ((|={E1,E3}=> Q) i) ((|={E2,E3}=> Q') i).
Proof. by rewrite /ElimModal !monPred_at_fupd. Qed.
Global Instance elim_modal_at_fupd_hyp `{BiFUpd PROP} φ E1 E2 P 𝓟 𝓟' 𝓠 𝓠' i :
  MakeMonPredAt i P 𝓟 →
  ElimModal φ (|={E1,E2}=> 𝓟) 𝓟' 𝓠 𝓠' →
  ElimModal φ ((|={E1,E2}=> P) i) 𝓟' 𝓠 𝓠'.
Proof. by rewrite /MakeMonPredAt /ElimModal monPred_at_fupd=><-. Qed.

Global Instance add_modal_at_fupd_goal `{BiFUpd PROP} E1 E2 𝓟 𝓟' Q i :
  AddModal 𝓟 𝓟' (|={E1,E2}=> Q i) → AddModal 𝓟 𝓟' ((|={E1,E2}=> Q) i).
Proof. by rewrite /AddModal !monPred_at_fupd. Qed.

Global Instance elim_inv_embed φ 𝓟inv 𝓟in 𝓟out 𝓟close Pin Pout Pclose Q Q' :
  (∀ i, ElimInv φ 𝓟inv 𝓟in 𝓟out 𝓟close (Q i) (Q' i)) →
  MakeEmbed 𝓟in Pin → MakeEmbed 𝓟out Pout → MakeEmbed 𝓟close Pclose →
  ElimInv φ ⎡𝓟inv⎤ Pin Pout Pclose Q Q'.
Proof.
  rewrite /MakeEmbed /ElimInv=>H <- <- <- ?. iStartProof PROP.
  iIntros (?) "(?&?&HQ')". iApply H; [done|]. iFrame. iIntros "?". by iApply "HQ'".
Qed.
End sbi.
