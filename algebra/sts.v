From prelude Require Export sets.
From algebra Require Export cmra.
From algebra Require Import dra.
Local Arguments valid _ _ !_ /.
Local Arguments op _ _ !_ !_ /.
Local Arguments unit _ _ !_ /.

Inductive sts {A B} (R : relation A) (tok : A → set B) :=
  | auth : A → set B → sts R tok
  | frag : set A → set B → sts R tok.
Arguments auth {_ _ _ _} _ _.
Arguments frag {_ _ _ _} _ _.

Module sts.
Section sts_core.
Context {A B : Type} (R : relation A) (tok : A → set B).
Infix "≼" := dra_included.

Inductive sts_equiv : Equiv (sts R tok) :=
  | auth_equiv s T1 T2 : T1 ≡ T2 → auth s T1 ≡ auth s T2
  | frag_equiv S1 S2 T1 T2 : T1 ≡ T2 → S1 ≡ S2 → frag S1 T1 ≡ frag S2 T2.
Global Existing Instance sts_equiv.
Inductive step : relation (A * set B) :=
  | Step s1 s2 T1 T2 :
     R s1 s2 → tok s1 ∩ T1 ≡ ∅ → tok s2 ∩ T2 ≡ ∅ → tok s1 ∪ T1 ≡ tok s2 ∪ T2 →
     step (s1,T1) (s2,T2).
Hint Resolve Step.
Inductive frame_step (T : set B) (s1 s2 : A) : Prop :=
  | Frame_step T1 T2 :
     T1 ∩ (tok s1 ∪ T) ≡ ∅ → step (s1,T1) (s2,T2) → frame_step T s1 s2.
Hint Resolve Frame_step.
Record closed (S : set A) (T : set B) : Prop := Closed {
  closed_ne : S ≢ ∅;
  closed_disjoint s : s ∈ S → tok s ∩ T ≡ ∅;
  closed_step s1 s2 : s1 ∈ S → frame_step T s1 s2 → s2 ∈ S
}.
Lemma closed_steps S T s1 s2 :
  closed S T → s1 ∈ S → rtc (frame_step T) s1 s2 → s2 ∈ S.
Proof. induction 3; eauto using closed_step. Qed.
Global Instance sts_valid : Valid (sts R tok) := λ x,
  match x with auth s T => tok s ∩ T ≡ ∅ | frag S' T => closed S' T end.
Definition up (s : A) (T : set B) : set A := mkSet (rtc (frame_step T) s).
Definition up_set (S : set A) (T : set B) : set A := S ≫= λ s, up s T.
Global Instance sts_unit : Unit (sts R tok) := λ x,
  match x with
  | frag S' _ => frag (up_set S' ∅ ) ∅ | auth s _ => frag (up s ∅) ∅
  end.
Inductive sts_disjoint : Disjoint (sts R tok) :=
  | frag_frag_disjoint S1 S2 T1 T2 :
     S1 ∩ S2 ≢ ∅ → T1 ∩ T2 ≡ ∅ → frag S1 T1 ⊥ frag S2 T2
  | auth_frag_disjoint s S T1 T2 : s ∈ S → T1 ∩ T2 ≡ ∅ → auth s T1 ⊥ frag S T2
  | frag_auth_disjoint s S T1 T2 : s ∈ S → T1 ∩ T2 ≡ ∅ → frag S T1 ⊥ auth s T2.
Global Existing Instance sts_disjoint.
Global Instance sts_op : Op (sts R tok) := λ x1 x2,
  match x1, x2 with
  | frag S1 T1, frag S2 T2 => frag (S1 ∩ S2) (T1 ∪ T2)
  | auth s T1, frag _ T2 => auth s (T1 ∪ T2)
  | frag _ T1, auth s T2 => auth s (T1 ∪ T2)
  | auth s T1, auth _ T2 => auth s (T1 ∪ T2) (* never happens *)
  end.
Global Instance sts_minus : Minus (sts R tok) := λ x1 x2,
  match x1, x2 with
  | frag S1 T1, frag S2 T2 => frag (up_set S1 (T1 ∖ T2)) (T1 ∖ T2)
  | auth s T1, frag _ T2 => auth s (T1 ∖ T2)
  | frag _ T2, auth s T1 => auth s (T1 ∖ T2) (* never happens *)
  | auth s T1, auth _ T2 => frag (up s (T1 ∖ T2)) (T1 ∖ T2)
  end.

Hint Extern 10 (equiv (A:=set _) _ _) => solve_elem_of : sts.
Hint Extern 10 (¬(equiv (A:=set _) _ _)) => solve_elem_of : sts.
Hint Extern 10 (_ ∈ _) => solve_elem_of : sts.
Hint Extern 10 (_ ⊆ _) => solve_elem_of : sts.
Instance: Equivalence ((≡) : relation (sts R tok)).
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
    constructor; intros until 0; rewrite -?HS -?HT; eauto.
Qed.
Instance closed_proper : Proper ((≡) ==> (≡) ==> iff) closed.
Proof. by split; apply closed_proper'. Qed.
Lemma closed_op T1 T2 S1 S2 :
  closed S1 T1 → closed S2 T2 →
  T1 ∩ T2 ≡ ∅ → S1 ∩ S2 ≢ ∅ → closed (S1 ∩ S2) (T1 ∪ T2).
Proof.
  intros [_ ? Hstep1] [_ ? Hstep2] ?; split; [done|solve_elem_of|].
  intros s3 s4; rewrite !elem_of_intersection; intros [??] [T3 T4 ?]; split.
  * apply Hstep1 with s3, Frame_step with T3 T4; auto with sts.
  * apply Hstep2 with s3, Frame_step with T3 T4; auto with sts.
Qed.
Instance up_preserving : Proper ((=) ==> flip (⊆) ==> (⊆)) up.
Proof.
  intros s ? <- T T' HT ; apply elem_of_subseteq.
  induction 1 as [|s1 s2 s3 [T1 T2]]; [constructor|].
  eapply rtc_l; [eapply Frame_step with T1 T2|]; eauto with sts.
Qed.
Instance up_proper : Proper ((=) ==> (≡) ==> (≡)) up.
Proof. by intros ??? ?? [??]; split; apply up_preserving. Qed.
Instance up_set_proper : Proper ((≡) ==> (≡) ==> (≡)) up_set.
Proof.
  intros S1 S2 HS T1 T2 HT. rewrite /up_set HS.
  f_equiv=>s1 s2 Hs. by rewrite Hs HT.
Qed.
Lemma elem_of_up s T : s ∈ up s T.
Proof. constructor. Qed.
Lemma subseteq_up_set S T : S ⊆ up_set S T.
Proof. intros s ?; apply elem_of_bind; eauto using elem_of_up. Qed.
Lemma closed_up_set S T :
  (∀ s, s ∈ S → tok s ∩ T ≡ ∅) → S ≢ ∅ → closed (up_set S T) T.
Proof.
  intros HS Hne; unfold up_set; split.
  * assert (∀ s, s ∈ up s T) by eauto using elem_of_up. solve_elem_of.
  * intros s; rewrite !elem_of_bind; intros (s'&Hstep&Hs').
    specialize (HS s' Hs'); clear Hs' Hne S.
    induction Hstep as [s|s1 s2 s3 [T1 T2 ? Hstep] ? IH]; auto.
    inversion_clear Hstep; apply IH; clear IH; auto with sts.
  * intros s1 s2; rewrite !elem_of_bind; intros (s&?&?) ?; exists s.
    split; [eapply rtc_r|]; eauto.
Qed.
Lemma closed_up_set_empty S : S ≢ ∅ → closed (up_set S ∅) ∅.
Proof. eauto using closed_up_set with sts. Qed.
Lemma closed_up s T : tok s ∩ T ≡ ∅ → closed (up s T) T.
Proof.
  intros; rewrite -(collection_bind_singleton (λ s, up s T) s).
  apply closed_up_set; solve_elem_of.
Qed.
Lemma closed_up_empty s : closed (up s ∅) ∅.
Proof. eauto using closed_up with sts. Qed.
Lemma up_closed S T : closed S T → up_set S T ≡ S.
Proof.
  intros; split; auto using subseteq_up_set; intros s.
  unfold up_set; rewrite elem_of_bind; intros (s'&Hstep&?).
  induction Hstep; eauto using closed_step.
Qed.
Global Instance sts_dra : DRA (sts R tok).
Proof.
  split.
  * apply _.
  * by do 2 destruct 1; constructor; setoid_subst.
  * by destruct 1; constructor; setoid_subst.
  * by intros ? [|]; destruct 1; inversion_clear 1; constructor; setoid_subst.
  * by do 2 destruct 1; constructor; setoid_subst.
  * assert (∀ T T' S s,
      closed S T → s ∈ S → tok s ∩ T' ≡ ∅ → tok s ∩ (T ∪ T') ≡ ∅).
    { intros S T T' s [??]; solve_elem_of. }
    destruct 3; simpl in *; auto using closed_op with sts.
  * intros []; simpl; eauto using closed_up, closed_up_set, closed_ne with sts.
  * intros ???? (z&Hy&?&Hxz); destruct Hxz; inversion Hy;clear Hy; setoid_subst;
      rewrite ?disjoint_union_difference; auto using closed_up with sts.
    eapply closed_up_set; eauto 2 using closed_disjoint with sts.
  * intros [] [] []; constructor; rewrite ?assoc; auto with sts.
  * destruct 4; inversion_clear 1; constructor; auto with sts.
  * destruct 4; inversion_clear 1; constructor; auto with sts.
  * destruct 1; constructor; auto with sts.
  * destruct 3; constructor; auto with sts.
  * intros [|S T]; constructor; auto using elem_of_up with sts.
    assert (S ⊆ up_set S ∅ ∧ S ≢ ∅) by eauto using subseteq_up_set, closed_ne.
    solve_elem_of.
  * intros [|S T]; constructor; auto with sts.
    assert (S ⊆ up_set S ∅); auto using subseteq_up_set with sts.
  * intros [s T|S T]; constructor; auto with sts.
    + rewrite (up_closed (up _ _)); auto using closed_up with sts.
    + rewrite (up_closed (up_set _ _));
        eauto using closed_up_set, closed_ne with sts.
  * intros x y ?? (z&Hy&?&Hxz); exists (unit (x ⋅ y)); split_ands.
    + destruct Hxz;inversion_clear Hy;constructor;unfold up_set; solve_elem_of.
    + destruct Hxz; inversion_clear Hy; simpl;
        auto using closed_up_set_empty, closed_up_empty with sts.
    + destruct Hxz; inversion_clear Hy; constructor;
        repeat match goal with
        | |- context [ up_set ?S ?T ] =>
           unless (S ⊆ up_set S T) by done; pose proof (subseteq_up_set S T)
        | |- context [ up ?s ?T ] =>
           unless (s ∈ up s T) by done; pose proof (elem_of_up s T)
        end; auto with sts.
  * intros x y ?? (z&Hy&_&Hxz); destruct Hxz; inversion_clear Hy; constructor;
      repeat match goal with
      | |- context [ up_set ?S ?T ] =>
         unless (S ⊆ up_set S T) by done; pose proof (subseteq_up_set S T)
      | |- context [ up ?s ?T ] =>
           unless (s ∈ up s T) by done; pose proof (elem_of_up s T)
      end; auto with sts.
  * intros x y ?? (z&Hy&?&Hxz); destruct Hxz as [S1 S2 T1 T2| |];
      inversion Hy; clear Hy; constructor; setoid_subst;
      rewrite ?disjoint_union_difference; auto.
    split; [|apply intersection_greatest; auto using subseteq_up_set with sts].
    apply intersection_greatest; [auto with sts|].
    intros s2; rewrite elem_of_intersection.
    unfold up_set; rewrite elem_of_bind; intros (?&s1&?&?&?).
    apply closed_steps with T2 s1; auto with sts.
Qed.
Lemma step_closed s1 s2 T1 T2 S Tf :
  step (s1,T1) (s2,T2) → closed S Tf → s1 ∈ S → T1 ∩ Tf ≡ ∅ →
  s2 ∈ S ∧ T2 ∩ Tf ≡ ∅ ∧ tok s2 ∩ T2 ≡ ∅.
Proof.
  inversion_clear 1 as [???? HR Hs1 Hs2]; intros [?? Hstep]??; split_ands; auto.
  * eapply Hstep with s1, Frame_step with T1 T2; auto with sts.
  * solve_elem_of -Hstep Hs1 Hs2.
Qed.
End sts_core.
End sts.

Section stsRA.
Context {A B : Type} (R : relation A) (tok : A → set B).

Canonical Structure stsRA := validityRA (sts R tok).
Definition sts_auth (s : A) (T : set B) : stsRA := to_validity (auth s T).
Definition sts_frag (S : set A) (T : set B) : stsRA := to_validity (frag S T).
Lemma sts_update s1 s2 T1 T2 :
  sts.step R tok (s1,T1) (s2,T2) → sts_auth s1 T1 ~~> sts_auth s2 T2.
Proof.
  intros ?; apply validity_update; inversion 3 as [|? S ? Tf|]; subst.
  destruct (sts.step_closed R tok s1 s2 T1 T2 S Tf) as (?&?&?); auto.
  repeat (done || constructor).
Qed.
End stsRA.
