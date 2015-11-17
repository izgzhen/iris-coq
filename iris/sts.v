Require Export iris.ra.
Require Import prelude.sets prelude.bsets iris.dra.
Local Arguments valid _ _ !_ /.
Local Arguments op _ _ !_ !_ /.
Local Arguments unit _ _ !_ /.

Module sts.
Inductive t {A B} (R : relation A) (tok : A → bset B) :=
  | auth : A → bset B → t R tok
  | frag : set A → bset B → t R tok.
Arguments auth {_ _ _ _} _ _.
Arguments frag {_ _ _ _} _ _.

Section sts_core.
Context {A B : Type} `{∀ x y : B, Decision (x = y)}.
Context (R : relation A) (tok : A → bset B).

Inductive sts_equiv : Equiv (t R tok) :=
  | auth_equiv s T1 T2 : T1 ≡ T2 → auth s T1 ≡ auth s T2
  | frag_equiv S1 S2 T1 T2 : T1 ≡ T2 → S1 ≡ S2 → frag S1 T1 ≡ frag S2 T2.
Global Existing Instance sts_equiv.
Inductive step : relation (A * bset B) :=
  | Step s1 s2 T1 T2 :
     R s1 s2 → tok s1 ∩ T1 ≡ ∅ → tok s2 ∩ T2 ≡ ∅ → tok s1 ∪ T1 ≡ tok s2 ∪ T2 →
     step (s1,T1) (s2,T2).
Hint Resolve Step.
Inductive frame_step (T : bset B) (s1 s2 : A) : Prop :=
  | Frame_step T1 T2 :
     T1 ∩ (tok s1 ∪ T) ≡ ∅ → step (s1,T1) (s2,T2) → frame_step T s1 s2.
Hint Resolve Frame_step.
Record closed (T : bset B) (S : set A) : Prop := Closed {
  closed_disjoint s : s ∈ S → tok s ∩ T ≡ ∅;
  closed_step s1 s2 : s1 ∈ S → frame_step T s1 s2 → s2 ∈ S
}.
Lemma closed_steps S T s1 s2 :
  closed T S → s1 ∈ S → rtc (frame_step T) s1 s2 → s2 ∈ S.
Proof. induction 3; eauto using closed_step. Qed.
Global Instance sts_valid : Valid (t R tok) := λ x,
  match x with auth s T => tok s ∩ T ≡ ∅ | frag S' T => closed T S' end.
Definition up (T : bset B) (s : A) : set A := mkSet (rtc (frame_step T) s).
Definition up_set (T : bset B) (S : set A) : set A := S ≫= up T.
Global Instance sts_unit : Unit (t R tok) := λ x,
  match x with
  | frag S' _ => frag (up_set ∅ S') ∅ | auth s _ => frag (up ∅ s) ∅
  end.
Inductive sts_disjoint : Disjoint (t R tok) :=
  | frag_frag_disjoint S1 S2 T1 T2 : T1 ∩ T2 ≡ ∅ → frag S1 T1 ⊥ frag S2 T2
  | auth_frag_disjoint s S T1 T2 : s ∈ S → T1 ∩ T2 ≡ ∅ → auth s T1 ⊥ frag S T2
  | frag_auth_disjoint s S T1 T2 : s ∈ S → T1 ∩ T2 ≡ ∅ → frag S T1 ⊥ auth s T2.
Global Existing Instance sts_disjoint.
Global Instance sts_op : Op (t R tok) := λ x1 x2,
  match x1, x2 with
  | frag S1 T1, frag S2 T2 => frag (S1 ∩ S2) (T1 ∪ T2)
  | auth s T1, frag _ T2 => auth s (T1 ∪ T2)
  | frag _ T1, auth s T2 => auth s (T1 ∪ T2)
  | auth s T1, auth _ T2 => auth s (T1 ∪ T2) (* never happens *)
  end.
Inductive sts_included : Included (t R tok) :=
  | frag_frag_included S1 S2 T1 T2 S' :
     T1 ⊆ T2 → S2 ≡ S1 ∩ S' → closed (T2 ∖ T1) S' → frag S1 T1 ≼ frag S2 T2
  | frag_auth_included s S T1 T2 : s ∈ S → T1 ⊆ T2 → frag S T1 ≼ auth s T2
  | auth_auth_included s T1 T2 : T1 ⊆ T2 → auth s T1 ≼ auth s T2.
Global Existing Instance sts_included.
Global Instance sts_minus : Minus (t R tok) := λ x1 x2,
  match x1, x2 with
  | frag S1 T1, frag S2 T2 => frag (up_set (T1 ∖ T2) S1) (T1 ∖ T2)
  | auth s T1, frag _ T2 => auth s (T1 ∖ T2)
  | frag _ T2, auth s T1 => auth s (T1 ∖ T2) (* never happens *)
  | auth s T1, auth _ T2 => frag (up (T1 ∖ T2) s) (T1 ∖ T2)
  end.

Hint Extern 5 (equiv (A:=set _) _ _) => esolve_elem_of : sts.
Hint Extern 5 (equiv (A:=bset _) _ _) => esolve_elem_of : sts.
Hint Extern 5 (_ ∈ _) => esolve_elem_of : sts.
Hint Extern 5 (_ ⊆ _) => esolve_elem_of : sts.
Instance: Equivalence ((≡) : relation (t R tok)).
Proof.
  split.
  * by intros []; constructor.
  * by destruct 1; constructor.
  * destruct 1; inversion_clear 1; constructor; etransitivity; eauto.
Qed.
Instance framestep_proper : Proper ((≡) ==> (=) ==> (=) ==> impl) frame_step.
Proof. intros ?? HT ?? <- ?? <-; destruct 1; econstructor; eauto with sts. Qed.
Instance closed_proper' : Proper ((≡) ==> (≡) ==> impl) closed.
Proof.
  intros ?? HT ?? HS; destruct 1;
    constructor; intros until 0; rewrite <-?HS, <-?HT; eauto.
Qed.
Instance closed_proper : Proper ((≡) ==> (≡) ==> iff) closed.
Proof. by split; apply closed_proper'. Qed.
Lemma closed_op T1 T2 S1 S2 :
  closed T1 S1 → closed T2 S2 → T1 ∩ T2 ≡ ∅ → closed (T1 ∪ T2) (S1 ∩ S2).
Proof.
  intros [? Hstep1] [? Hstep2] ?; split; [esolve_elem_of|].
  intros s3 s4; rewrite !elem_of_intersection; intros [??] [T ??]; split.
  * apply Hstep1 with s3; eauto with sts.
  * apply Hstep2 with s3; eauto with sts.
Qed.
Lemma closed_all : closed ∅ set_all.
Proof. split; auto with sts. Qed.
Hint Resolve closed_all : sts.
Instance up_preserving : Proper (flip (⊆) ==> (=) ==> (⊆)) up.
Proof.
  intros T T' HT s ? <-; apply elem_of_subseteq.
  induction 1 as [|s1 s2 s3 [T1 T2]]; [constructor|].
  eapply rtc_l; [eapply Frame_step with T1 T2|]; eauto with sts.
Qed.
Instance up_proper : Proper ((≡) ==> (=) ==> (≡)) up.
Proof. by intros ?? [??] ???; split; apply up_preserving. Qed.
Instance up_set_proper : Proper ((≡) ==> (≡) ==> (≡)) up_set.
Proof. by intros T1 T2 HT S1 S2 HS; unfold up_set; rewrite HS, HT. Qed.
Lemma elem_of_up s T : s ∈ up T s.
Proof. constructor. Qed.
Lemma subseteq_up_set S T : S ⊆ up_set T S.
Proof. intros s ?; apply elem_of_bind; eauto using elem_of_up. Qed.
Lemma closed_up_set S T : (∀ s, s ∈ S → tok s ∩ T ≡ ∅) → closed T (up_set T S).
Proof.
  intros HS; unfold up_set; split.
  * intros s; rewrite !elem_of_bind; intros (s'&Hstep&Hs').
    specialize (HS s' Hs'); clear Hs' S.
    induction Hstep as [s|s1 s2 s3 [T1 T2 ? Hstep] ? IH]; auto.
    inversion_clear Hstep; apply IH; clear IH; auto with sts.
  * intros s1 s2; rewrite !elem_of_bind; intros (s&?&?) ?; exists s.
    split; [eapply rtc_r|]; eauto.
Qed.
Lemma closed_up_set_empty S : closed ∅ (up_set ∅ S).
Proof. eauto using closed_up_set with sts. Qed.
Lemma closed_up s T : tok s ∩ T ≡ ∅ → closed T (up T s).
Proof.
  intros; rewrite <-(collection_bind_singleton (up T) s).
  apply closed_up_set; auto with sts.
Qed.
Lemma closed_up_empty s : closed ∅ (up ∅ s).
Proof. eauto using closed_up with sts. Qed.
Lemma up_closed S T : closed T S → up_set T S ≡ S.
Proof.
  intros; split; auto using subseteq_up_set; intros s.
  unfold up_set; rewrite elem_of_bind; intros (s'&Hstep&?).
  induction Hstep; eauto using closed_step.
Qed.
Lemma up_set_subseteq T1 T2 S1 S2 :
  closed (T2 ∖ T1) S2 → up_set (T2 ∖ T1) (S1 ∩ S2) ⊆ S2.
Proof.
  intros ? s2; unfold up_set; rewrite elem_of_bind; intros (s1&?&?).
  apply closed_steps with (T2 ∖ T1) s1; auto with sts.
Qed.
Global Instance sts_dra : DRA (t R tok).
Proof.
  split.
  * apply _.
  * by do 2 destruct 1; constructor; setoid_subst.
  * by destruct 1; constructor; setoid_subst.
  * by intros ? [|]; destruct 1; inversion_clear 1; constructor; setoid_subst.
  * by do 2 destruct 1; constructor; setoid_subst.
  * by do 2 destruct 1; inversion_clear 1; econstructor; setoid_subst.
  * assert (∀ T T' S s,
      closed T S → s ∈ S → tok s ∩ T' ≡ ∅ → tok s ∩ (T ∪ T') ≡ ∅).
    { intros S T T' s [??]; esolve_elem_of. }
    destruct 3; simpl in *; auto using closed_op with sts.
  * intros []; simpl; eauto using closed_up, closed_up_set with sts.
  * destruct 3; simpl in *; setoid_subst; eauto using closed_up with sts.
    eapply closed_up_set; eauto 2 using closed_disjoint with sts.
  * intros [] [] []; constructor; rewrite ?(associative _); auto with sts.
  * destruct 4; inversion_clear 1; constructor; auto with sts.
  * destruct 4; inversion_clear 1; constructor; auto with sts.
  * destruct 1; constructor; auto with sts.
  * destruct 3; constructor; auto with sts.
  * intros []; constructor; auto using elem_of_up with sts.
  * intros [|S T]; constructor; auto with sts.
    assert (S ⊆ up_set ∅ S); auto using subseteq_up_set with sts.
  * intros [s T|S T]; constructor; auto with sts.
    + by rewrite (up_closed (up _ _)) by auto using closed_up with sts.
    + by rewrite (up_closed (up_set _ _)) by auto using closed_up_set with sts.
  * destruct 3 as [S1 S2| |]; simpl;
      match goal with |- _ ≼ frag ?S _ => apply frag_frag_included with S end;
      eauto using closed_up_empty, closed_up_set_empty;
      unfold up_set; esolve_elem_of.
  * destruct 3 as [S1 S2 T1 T2| |]; econstructor; eauto with sts.
    by setoid_replace ((T1 ∪ T2) ∖ T1) with T2 by esolve_elem_of.
  * destruct 3; constructor; eauto using elem_of_up with sts.
  * destruct 3 as [S1 S2 T1 T2 S'| |]; constructor;
      rewrite ?(commutative _ (_ ∖ _)), <-?union_difference; auto with sts.
    assert (S2 ⊆ up_set (T2 ∖ T1) S2) by eauto using subseteq_up_set.
    assert (up_set (T2 ∖ T1) (S1 ∩ S') ⊆ S') by eauto using up_set_subseteq.
    esolve_elem_of.
Qed.
Lemma step_closed s1 s2 T1 T2 S Tf :
  step (s1,T1) (s2,T2) → closed Tf S → s1 ∈ S → T1 ∩ Tf ≡ ∅ →
  s2 ∈ S ∧ T2 ∩ Tf ≡ ∅ ∧ tok s2 ∩ T2 ≡ ∅.
Proof.
  inversion_clear 1 as [???? HR Hs1 Hs2]; intros [? Hstep] ??; split_ands; auto.
  * eapply Hstep with s1, Frame_step with T1 T2; auto with sts.
  * clear Hstep Hs1 Hs2; esolve_elem_of.
Qed.
End sts_core.
End sts.

Section sts_ra.
Context {A B : Type} `{∀ x y : B, Decision (x = y)}.
Context (R : relation A) (tok : A → bset B).

Definition sts := validity (valid : sts.t R tok → Prop).
Global Instance sts_unit : Unit sts := validity_unit _.
Global Instance sts_op : Op sts := validity_op _.
Global Instance sts_included : Included sts := validity_included _.
Global Instance sts_minus : Minus sts := validity_minus _.
Global Instance sts_ra : RA sts := validity_ra _.
Definition sts_auth (s : A) (T : bset B) : sts := to_validity (sts.auth s T).
Definition sts_frag (S : set A) (T : bset B) : sts :=
  to_validity (sts.frag S T).
Lemma sts_update s1 s2 T1 T2 :
  sts.step R tok (s1,T1) (s2,T2) → sts_auth s1 T1 ⇝ sts_auth s2 T2.
Proof.
  intros ?; apply dra_update; inversion 3 as [|? S ? Tf|]; subst.
  destruct (sts.step_closed R tok s1 s2 T1 T2 S Tf) as (?&?&?); auto.
  repeat (done || constructor).
Qed.
End sts_ra.
