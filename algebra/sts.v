From prelude Require Export sets.
From algebra Require Export cmra.
From algebra Require Import dra.
Local Arguments valid _ _ !_ /.
Local Arguments op _ _ !_ !_ /.
Local Arguments unit _ _ !_ /.

(** * Definition of STSs *)
Module sts.
Structure stsT := STS {
  state : Type;
  token : Type;
  prim_step : relation state;
  tok : state → set token;
}.
Arguments STS {_ _} _ _.
Arguments prim_step {_} _ _.
Arguments tok {_} _.
Notation states sts := (set (state sts)).
Notation tokens sts := (set (token sts)).

(** * Theory and definitions *)
Section sts.
Context {sts : stsT}.

(** ** Step relations *)
Inductive step : relation (state sts * tokens sts) :=
  | Step s1 s2 T1 T2 :
     (* TODO: This asks for ⊥ on sets: T1 ⊥ T2 := T1 ∩ T2 ⊆ ∅. *)
     prim_step s1 s2 → tok s1 ∩ T1 ≡ ∅ → tok s2 ∩ T2 ≡ ∅ →
     tok s1 ∪ T1 ≡ tok s2 ∪ T2 → step (s1,T1) (s2,T2).
Inductive frame_step (T : tokens sts) (s1 s2 : state sts) : Prop :=
  | Frame_step T1 T2 :
     T1 ∩ (tok s1 ∪ T) ≡ ∅ → step (s1,T1) (s2,T2) → frame_step T s1 s2.

(** ** Closure under frame steps *)
Record closed (S : states sts) (T : tokens sts) : Prop := Closed {
  closed_ne : S ≢ ∅;
  closed_disjoint s : s ∈ S → tok s ∩ T ⊆ ∅;
  closed_step s1 s2 : s1 ∈ S → frame_step T s1 s2 → s2 ∈ S
}.
Definition up (s : state sts) (T : tokens sts) : states sts :=
  mkSet (rtc (frame_step T) s).
Definition up_set (S : states sts) (T : tokens sts) : states sts :=
  S ≫= λ s, up s T.

(** Tactic setup *)
Hint Resolve Step.
Hint Extern 10 (equiv (A:=set _) _ _) => solve_elem_of : sts.
Hint Extern 10 (¬equiv (A:=set _) _ _) => solve_elem_of : sts.
Hint Extern 10 (_ ∈ _) => solve_elem_of : sts.
Hint Extern 10 (_ ⊆ _) => solve_elem_of : sts.

(** ** Setoids *)
Instance framestep_mono : Proper (flip (⊆) ==> (=) ==> (=) ==> impl) frame_step.
Proof.
  intros ?? HT ?? <- ?? <-; destruct 1; econstructor;
    eauto with sts; solve_elem_of.
Qed.
Global Instance framestep_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) frame_step.
Proof. by intros ?? [??] ??????; split; apply framestep_mono. Qed.
Instance closed_proper' : Proper ((≡) ==> (≡) ==> impl) closed.
Proof.
  intros ?? HT ?? HS; destruct 1;
    constructor; intros until 0; rewrite -?HS -?HT; eauto.
Qed.
Global Instance closed_proper : Proper ((≡) ==> (≡) ==> iff) closed.
Proof. by split; apply closed_proper'. Qed.
Global Instance up_preserving : Proper ((=) ==> flip (⊆) ==> (⊆)) up.
Proof.
  intros s ? <- T T' HT ; apply elem_of_subseteq.
  induction 1 as [|s1 s2 s3 [T1 T2]]; [constructor|].
  eapply rtc_l; [eapply Frame_step with T1 T2|]; eauto with sts.
Qed.
Global Instance up_proper : Proper ((=) ==> (≡) ==> (≡)) up.
Proof. by intros ??? ?? [??]; split; apply up_preserving. Qed.
Global Instance up_set_preserving : Proper ((⊆) ==> flip (⊆) ==> (⊆)) up_set.
Proof.
  intros S1 S2 HS T1 T2 HT. rewrite /up_set.
  f_equiv; last done. move =>s1 s2 Hs. simpl in HT. by apply up_preserving.
Qed.
Global Instance up_set_proper : Proper ((≡) ==> (≡) ==> (≡)) up_set.
Proof. by intros S1 S2 [??] T1 T2 [??]; split; apply up_set_preserving. Qed.

(** ** Properties of closure under frame steps *)
Lemma closed_disjoint' S T s : closed S T → s ∈ S → tok s ∩ T ≡ ∅.
Proof. intros [_ ? _]; solve_elem_of. Qed.
Lemma closed_steps S T s1 s2 :
  closed S T → s1 ∈ S → rtc (frame_step T) s1 s2 → s2 ∈ S.
Proof. induction 3; eauto using closed_step. Qed.
Lemma closed_op T1 T2 S1 S2 :
  closed S1 T1 → closed S2 T2 →
  T1 ∩ T2 ≡ ∅ → S1 ∩ S2 ≢ ∅ → closed (S1 ∩ S2) (T1 ∪ T2).
Proof.
  intros [_ ? Hstep1] [_ ? Hstep2] ?; split; [done|solve_elem_of|].
  intros s3 s4; rewrite !elem_of_intersection; intros [??] [T3 T4 ?]; split.
  - apply Hstep1 with s3, Frame_step with T3 T4; auto with sts.
  - apply Hstep2 with s3, Frame_step with T3 T4; auto with sts.
Qed.
Lemma step_closed s1 s2 T1 T2 S Tf :
  step (s1,T1) (s2,T2) → closed S Tf → s1 ∈ S → T1 ∩ Tf ≡ ∅ →
  s2 ∈ S ∧ T2 ∩ Tf ≡ ∅ ∧ tok s2 ∩ T2 ≡ ∅.
Proof.
  inversion_clear 1 as [???? HR Hs1 Hs2]; intros [?? Hstep]??; split_ands; auto.
  - eapply Hstep with s1, Frame_step with T1 T2; auto with sts.
  - solve_elem_of -Hstep Hs1 Hs2.
Qed.

(** ** Properties of the closure operators *)
Lemma elem_of_up s T : s ∈ up s T.
Proof. constructor. Qed.
Lemma subseteq_up_set S T : S ⊆ up_set S T.
Proof. intros s ?; apply elem_of_bind; eauto using elem_of_up. Qed.
Lemma up_up_set s T : up s T ≡ up_set {[ s ]} T.
Proof. by rewrite /up_set collection_bind_singleton. Qed.
Lemma closed_up_set S T :
  (∀ s, s ∈ S → tok s ∩ T ⊆ ∅) → S ≢ ∅ → closed (up_set S T) T.
Proof.
  intros HS Hne; unfold up_set; split.
  - assert (∀ s, s ∈ up s T) by eauto using elem_of_up. solve_elem_of.
  - intros s; rewrite !elem_of_bind; intros (s'&Hstep&Hs').
    specialize (HS s' Hs'); clear Hs' Hne S.
    induction Hstep as [s|s1 s2 s3 [T1 T2 ? Hstep] ? IH]; first done.
    inversion_clear Hstep; apply IH; clear IH; auto with sts.
  - intros s1 s2; rewrite !elem_of_bind; intros (s&?&?) ?; exists s.
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
End sts. End sts.

Notation stsT := sts.stsT.
Notation STS := sts.STS.

(** * STSs form a disjoint RA *)
(* This module should never be imported, uses the module [sts] below. *)
Module sts_dra.
Import sts.

(* The type of bounds we can give to the state of an STS. This is the type
   that we equip with an RA structure. *)
Inductive car (sts : stsT) :=
  | auth : state sts → set (token sts) → car sts
  | frag : set (state sts) → set (token sts ) → car sts.
Arguments auth {_} _ _.
Arguments frag {_} _ _.

Section sts_dra.
Context {sts : stsT}.
Infix "≼" := dra_included.
Implicit Types S : states sts.
Implicit Types T : tokens sts.

Inductive sts_equiv : Equiv (car sts) :=
  | auth_equiv s T1 T2 : T1 ≡ T2 → auth s T1 ≡ auth s T2
  | frag_equiv S1 S2 T1 T2 : T1 ≡ T2 → S1 ≡ S2 → frag S1 T1 ≡ frag S2 T2.
Existing Instance sts_equiv.
Instance sts_valid : Valid (car sts) := λ x,
  match x with auth s T => tok s ∩ T ≡ ∅ | frag S' T => closed S' T end.
Instance sts_unit : Unit (car sts) := λ x,
  match x with
  | frag S' _ => frag (up_set S' ∅ ) ∅
  | auth s _  => frag (up s ∅) ∅
  end.
Inductive sts_disjoint : Disjoint (car sts) :=
  | frag_frag_disjoint S1 S2 T1 T2 :
     S1 ∩ S2 ≢ ∅ → T1 ∩ T2 ≡ ∅ → frag S1 T1 ⊥ frag S2 T2
  | auth_frag_disjoint s S T1 T2 :
     s ∈ S → T1 ∩ T2 ≡ ∅ → auth s T1 ⊥ frag S T2
  | frag_auth_disjoint s S T1 T2 :
     s ∈ S → T1 ∩ T2 ≡ ∅ → frag S T1 ⊥ auth s T2.
Existing Instance sts_disjoint.
Instance sts_op : Op (car sts) := λ x1 x2,
  match x1, x2 with
  | frag S1 T1, frag S2 T2 => frag (S1 ∩ S2) (T1 ∪ T2)
  | auth s T1, frag _ T2 => auth s (T1 ∪ T2)
  | frag _ T1, auth s T2 => auth s (T1 ∪ T2)
  | auth s T1, auth _ T2 => auth s (T1 ∪ T2)(* never happens *)
  end.
Instance sts_minus : Minus (car sts) := λ x1 x2,
  match x1, x2 with
  | frag S1 T1, frag S2 T2 => frag (up_set S1 (T1 ∖ T2)) (T1 ∖ T2)
  | auth s T1, frag _ T2 => auth s (T1 ∖ T2)
  | frag _ T2, auth s T1 => auth s (T1 ∖ T2) (* never happens *)
  | auth s T1, auth _ T2 => frag (up s (T1 ∖ T2)) (T1 ∖ T2)
  end.

Hint Extern 10 (equiv (A:=set _) _ _) => solve_elem_of : sts.
Hint Extern 10 (¬equiv (A:=set _) _ _) => solve_elem_of : sts.
Hint Extern 10 (_ ∈ _) => solve_elem_of : sts.
Hint Extern 10 (_ ⊆ _) => solve_elem_of : sts.
Instance sts_equivalence: Equivalence ((≡) : relation (car sts)).
Proof.
  split.
  - by intros []; constructor.
  - by destruct 1; constructor.
  - destruct 1; inversion_clear 1; constructor; etransitivity; eauto.
Qed.
Global Instance sts_dra : DRA (car sts).
Proof.
  split.
  - apply _.
  - by do 2 destruct 1; constructor; setoid_subst.
  - by destruct 1; constructor; setoid_subst.
  - by destruct 1; simpl; intros ?; setoid_subst.
  - by intros ? [|]; destruct 1; inversion_clear 1; constructor; setoid_subst.
  - by do 2 destruct 1; constructor; setoid_subst.
  - assert (∀ T T' S s,
      closed S T → s ∈ S → tok s ∩ T' ≡ ∅ → tok s ∩ (T ∪ T') ≡ ∅).
    { intros S T T' s [??]; solve_elem_of. }
    destruct 3; simpl in *; auto using closed_op with sts.
  - intros []; simpl; eauto using closed_up, closed_up_set, closed_ne with sts.
  - intros ???? (z&Hy&?&Hxz); destruct Hxz; inversion Hy;clear Hy; setoid_subst;
      rewrite ?disjoint_union_difference; auto using closed_up with sts.
    eapply closed_up_set; eauto 2 using closed_disjoint with sts.
  - intros [] [] []; constructor; rewrite ?assoc; auto with sts.
  - destruct 4; inversion_clear 1; constructor; auto with sts.
  - destruct 4; inversion_clear 1; constructor; auto with sts.
  - destruct 1; constructor; auto with sts.
  - destruct 3; constructor; auto with sts.
  - intros [|S T]; constructor; auto using elem_of_up with sts.
    assert (S ⊆ up_set S ∅ ∧ S ≢ ∅) by eauto using subseteq_up_set, closed_ne.
    solve_elem_of.
  - intros [|S T]; constructor; auto with sts.
    assert (S ⊆ up_set S ∅); auto using subseteq_up_set with sts.
  - intros [s T|S T]; constructor; auto with sts.
    + rewrite (up_closed (up _ _)); auto using closed_up with sts.
    + rewrite (up_closed (up_set _ _));
        eauto using closed_up_set, closed_ne with sts.
  - intros x y ?? (z&Hy&?&Hxz); exists (unit (x ⋅ y)); split_ands.
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
  - intros x y ?? (z&Hy&_&Hxz); destruct Hxz; inversion_clear Hy; constructor;
      repeat match goal with
      | |- context [ up_set ?S ?T ] =>
         unless (S ⊆ up_set S T) by done; pose proof (subseteq_up_set S T)
      | |- context [ up ?s ?T ] =>
           unless (s ∈ up s T) by done; pose proof (elem_of_up s T)
      end; auto with sts.
  - intros x y ?? (z&Hy&?&Hxz); destruct Hxz as [S1 S2 T1 T2| |];
      inversion Hy; clear Hy; constructor; setoid_subst;
      rewrite ?disjoint_union_difference; auto.
    split; [|apply intersection_greatest; auto using subseteq_up_set with sts].
    apply intersection_greatest; [auto with sts|].
    intros s2; rewrite elem_of_intersection.
    unfold up_set; rewrite elem_of_bind; intros (?&s1&?&?&?).
    apply closed_steps with T2 s1; auto with sts.
Qed.
Canonical Structure RA : cmraT := validityRA (car sts).
End sts_dra. End sts_dra.

(** * The STS Resource Algebra *)
(** Finally, the general theory of STS that should be used by users *)
Notation stsRA := (@sts_dra.RA).

Section sts_definitions.
  Context {sts : stsT}.
  Definition sts_auth (s : sts.state sts) (T : sts.tokens sts) : stsRA sts :=
    to_validity (sts_dra.auth s T).
  Definition sts_frag (S : sts.states sts) (T : sts.tokens sts) : stsRA sts :=
    to_validity (sts_dra.frag S T).
  Definition sts_frag_up (s : sts.state sts) (T : sts.tokens sts) : stsRA sts :=
    sts_frag (sts.up s T) T.
End sts_definitions.
Instance: Params (@sts_auth) 2.
Instance: Params (@sts_frag) 1.
Instance: Params (@sts_frag_up) 2.

Section stsRA.
Import sts.
Context {sts : stsT}.
Implicit Types s : state sts.
Implicit Types S : states sts.
Implicit Types T : tokens sts.

(** Setoids *)
Global Instance sts_auth_proper s : Proper ((≡) ==> (≡)) (sts_auth s).
Proof. (* this proof is horrible *)
  intros T1 T2 HT. rewrite /sts_auth.
  by eapply to_validity_proper; try apply _; constructor.
Qed.
Global Instance sts_frag_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sts_frag sts).
Proof.
  intros S1 S2 ? T1 T2 HT; rewrite /sts_auth.
  by eapply to_validity_proper; try apply _; constructor.
Qed.
Global Instance sts_frag_up_proper s : Proper ((≡) ==> (≡)) (sts_frag_up s).
Proof. intros T1 T2 HT. by rewrite /sts_frag_up HT. Qed.

(** Validity *)
Lemma sts_auth_valid s T : ✓ sts_auth s T ↔ tok s ∩ T ≡ ∅.
Proof. split. by move=> /(_ 0). by intros ??. Qed.
Lemma sts_frag_valid S T : ✓ sts_frag S T ↔ closed S T.
Proof. split. by move=> /(_ 0). by intros ??. Qed.
Lemma sts_frag_up_valid s T : tok s ∩ T ≡ ∅ → ✓ sts_frag_up s T.
Proof. intros; by apply sts_frag_valid, closed_up. Qed.

Lemma sts_auth_frag_valid_inv s S T1 T2 :
  ✓ (sts_auth s T1 ⋅ sts_frag S T2) → s ∈ S.
Proof. by move=> /(_ 0) [? [? Hdisj]]; inversion Hdisj. Qed.

(** Op *)
Lemma sts_op_auth_frag s S T :
  s ∈ S → closed S T → sts_auth s ∅ ⋅ sts_frag S T ≡ sts_auth s T.
Proof.
  intros; split; [split|constructor; solve_elem_of]; simpl.
  - intros (?&?&?); by apply closed_disjoint' with S.
  - intros; split_ands. solve_elem_of+. done. constructor; solve_elem_of.
Qed.
Lemma sts_op_auth_frag_up s T :
  tok s ∩ T ≡ ∅ → sts_auth s ∅ ⋅ sts_frag_up s T ≡ sts_auth s T.
Proof. intros; apply sts_op_auth_frag; auto using elem_of_up, closed_up. Qed.

Lemma sts_op_frag S1 S2 T1 T2 :
  T1 ∩ T2 ⊆ ∅ → sts.closed S1 T1 → sts.closed S2 T2 →
  sts_frag (S1 ∩ S2) (T1 ∪ T2) ≡ sts_frag S1 T1 ⋅ sts_frag S2 T2.
Proof.
  intros HT HS1 HS2. rewrite /sts_frag.
  (* FIXME why does rewrite not work?? *)
  etransitivity; last eapply to_validity_op; try done; [].
  intros Hval. constructor; last solve_elem_of. eapply closed_ne, Hval.
Qed.

(** Frame preserving updates *)
Lemma sts_update_auth s1 s2 T1 T2 :
  step (s1,T1) (s2,T2) → sts_auth s1 T1 ~~> sts_auth s2 T2.
Proof.
  intros ?; apply validity_update; inversion 3 as [|? S ? Tf|]; subst.
  destruct (step_closed s1 s2 T1 T2 S Tf) as (?&?&?); auto.
  repeat (done || constructor).
Qed.

Lemma sts_update_frag S1 S2 T :
  closed S2 T → S1 ⊆ S2 → sts_frag S1 T ~~> sts_frag S2 T.
Proof.
  rewrite /sts_frag=> HS Hcl. apply validity_update.
  inversion 3 as [|? S ? Tf|]; simplify_equality'.
  - split; first done. constructor; [solve_elem_of|done].
  - split; first done. constructor; solve_elem_of.
Qed.

Lemma sts_update_frag_up s1 S2 T :
  closed S2 T → s1 ∈ S2 → sts_frag_up s1 T ~~> sts_frag S2 T.
Proof.
  intros; by apply sts_update_frag; [|intros ?; eauto using closed_steps].
Qed.

(** Inclusion *)
Lemma sts_frag_included S1 S2 T1 T2 :
  closed S2 T2 →
  sts_frag S1 T1 ≼ sts_frag S2 T2 ↔
  (closed S1 T1 ∧ ∃ Tf, T2 ≡ T1 ∪ Tf ∧ T1 ∩ Tf ≡ ∅ ∧ S2 ≡ S1 ∩ up_set S2 Tf).
Proof. (* This should use some general properties of DRAs. To be improved
when we have RAs back *)
  move=>Hcl2. split.
  - intros [[[Sf Tf|Sf Tf] vf Hvf] EQ].
    { exfalso. inversion_clear EQ as [Hv EQ']. apply EQ' in Hcl2. simpl in Hcl2.
      inversion Hcl2. }
    inversion_clear EQ as [Hv EQ'].
    move:(EQ' Hcl2)=>{EQ'} EQ. inversion_clear EQ as [|? ? ? ? HT HS].
    destruct Hv as [Hv _]. move:(Hv Hcl2)=>{Hv} [/= Hcl1  [Hclf Hdisj]].
    apply Hvf in Hclf. simpl in Hclf. clear Hvf.
    inversion_clear Hdisj. split; last (exists Tf; split_ands); [done..|].
    apply (anti_symm (⊆)).
    + move=>s HS2. apply elem_of_intersection. split; first by apply HS.
      by apply subseteq_up_set.
    + move=>s /elem_of_intersection [HS1 Hscl]. apply HS. split; first done.
      destruct Hscl as [s' [Hsup Hs']].
      eapply closed_steps; last (hnf in Hsup; eexact Hsup); first done.
      solve_elem_of +HS Hs'.
  - intros (Hcl1 & Tf & Htk & Hf & Hs).
    exists (sts_frag (up_set S2 Tf) Tf).
    split; first split; simpl;[|done|].
    + intros _. split_ands; first done.
      * apply closed_up_set; last by eapply closed_ne.
        move=>s Hs2. move:(closed_disjoint _ _ Hcl2 _ Hs2).
        solve_elem_of +Htk.
      * constructor; last done. rewrite -Hs. by eapply closed_ne.
    + intros _. constructor; [ solve_elem_of +Htk | done].
Qed.

Lemma sts_frag_included' S1 S2 T :
  closed S2 T → closed S1 T → S2 ≡ S1 ∩ up_set S2 ∅ →
  sts_frag S1 T ≼ sts_frag S2 T.
Proof.
  intros. apply sts_frag_included; split_ands; auto.
  exists ∅; split_ands; done || solve_elem_of+.
Qed.
End stsRA.
