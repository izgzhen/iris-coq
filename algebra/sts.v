From prelude Require Export sets.
From algebra Require Export cmra.
From algebra Require Import dra.
Local Arguments valid _ _ !_ /.
Local Arguments op _ _ !_ !_ /.
Local Arguments core _ _ !_ /.

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
Notation steps := (rtc step).
Inductive frame_step (T : tokens sts) (s1 s2 : state sts) : Prop :=
  | Frame_step T1 T2 :
     T1 ∩ (tok s1 ∪ T) ≡ ∅ → step (s1,T1) (s2,T2) → frame_step T s1 s2.

(** ** Closure under frame steps *)
Record closed (S : states sts) (T : tokens sts) : Prop := Closed {
  closed_disjoint s : s ∈ S → tok s ∩ T ≡ ∅;
  closed_step s1 s2 : s1 ∈ S → frame_step T s1 s2 → s2 ∈ S
}.
Definition up (s : state sts) (T : tokens sts) : states sts :=
  {[ s' | rtc (frame_step T) s s' ]}.
Definition up_set (S : states sts) (T : tokens sts) : states sts :=
  S ≫= λ s, up s T.

(** Tactic setup *)
Hint Resolve Step.
Hint Extern 50 (equiv (A:=set _) _ _) => set_solver : sts.
Hint Extern 50 (¬equiv (A:=set _) _ _) => set_solver : sts.
Hint Extern 50 (_ ∈ _) => set_solver : sts.
Hint Extern 50 (_ ⊆ _) => set_solver : sts.

(** ** Setoids *)
Instance framestep_mono : Proper (flip (⊆) ==> (=) ==> (=) ==> impl) frame_step.
Proof.
  intros ?? HT ?? <- ?? <-; destruct 1; econstructor;
    eauto with sts; set_solver.
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
  eapply elem_of_mkSet, rtc_l; [eapply Frame_step with T1 T2|]; eauto with sts.
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
Lemma closed_steps S T s1 s2 :
  closed S T → s1 ∈ S → rtc (frame_step T) s1 s2 → s2 ∈ S.
Proof. induction 3; eauto using closed_step. Qed.
Lemma closed_op T1 T2 S1 S2 :
  closed S1 T1 → closed S2 T2 → closed (S1 ∩ S2) (T1 ∪ T2).
Proof.
  intros [? Hstep1] [? Hstep2]; split; [set_solver|].
  intros s3 s4; rewrite !elem_of_intersection; intros [??] [T3 T4 ?]; split.
  - apply Hstep1 with s3, Frame_step with T3 T4; auto with sts.
  - apply Hstep2 with s3, Frame_step with T3 T4; auto with sts.
Qed.
Lemma step_closed s1 s2 T1 T2 S Tf :
  step (s1,T1) (s2,T2) → closed S Tf → s1 ∈ S → T1 ∩ Tf ≡ ∅ →
  s2 ∈ S ∧ T2 ∩ Tf ≡ ∅ ∧ tok s2 ∩ T2 ≡ ∅.
Proof.
  inversion_clear 1 as [???? HR Hs1 Hs2]; intros [? Hstep]??; split_and?; auto.
  - eapply Hstep with s1, Frame_step with T1 T2; auto with sts.
  - set_solver -Hstep Hs1 Hs2.
Qed.
Lemma steps_closed s1 s2 T1 T2 S Tf :
  steps (s1,T1) (s2,T2) → closed S Tf → s1 ∈ S → T1 ∩ Tf ≡ ∅ →
  tok s1 ∩ T1 ≡ ∅ → s2 ∈ S ∧ T2 ∩ Tf ≡ ∅ ∧ tok s2 ∩ T2 ≡ ∅.
Proof.
  remember (s1,T1) as sT1 eqn:HsT1; remember (s2,T2) as sT2 eqn:HsT2.
  intros Hsteps; revert s1 T1 HsT1 s2 T2 HsT2.
  induction Hsteps as [?|? [s2 T2] ? Hstep Hsteps IH];
     intros s1 T1 HsT1 s2' T2' ?????; simplify_eq; first done.
  destruct (step_closed s1 s2 T1 T2 S Tf) as (?&?&?); eauto.
Qed.

(** ** Properties of the closure operators *)
Lemma elem_of_up s T : s ∈ up s T.
Proof. constructor. Qed.
Lemma subseteq_up_set S T : S ⊆ up_set S T.
Proof. intros s ?; apply elem_of_bind; eauto using elem_of_up. Qed.
Lemma up_up_set s T : up s T ≡ up_set {[ s ]} T.
Proof. by rewrite /up_set collection_bind_singleton. Qed.
Lemma closed_up_set S T :
  (∀ s, s ∈ S → tok s ∩ T ≡ ∅) → closed (up_set S T) T.
Proof.
  intros HS; unfold up_set; split.
  - intros s; rewrite !elem_of_bind; intros (s'&Hstep&Hs').
    specialize (HS s' Hs'); clear Hs' S.
    induction Hstep as [s|s1 s2 s3 [T1 T2 ? Hstep] ? IH]; first done.
    inversion_clear Hstep; apply IH; clear IH; auto with sts.
  - intros s1 s2; rewrite /up; set_unfold; intros (s&?&?) ?; exists s.
    split; [eapply rtc_r|]; eauto.
Qed.
Lemma closed_up s T : tok s ∩ T ≡ ∅ → closed (up s T) T.
Proof.
  intros; rewrite -(collection_bind_singleton (λ s, up s T) s).
  apply closed_up_set; set_solver.
Qed.
Lemma closed_up_set_empty S : closed (up_set S ∅) ∅.
Proof. eauto using closed_up_set with sts. Qed.
Lemma closed_up_empty s : closed (up s ∅) ∅.
Proof. eauto using closed_up with sts. Qed.
Lemma up_set_empty S T : up_set S T ≡ ∅ → S ≡ ∅.
Proof. move:(subseteq_up_set S T). set_solver. Qed.
Lemma up_set_non_empty S T : S ≢ ∅ → up_set S T ≢ ∅.
Proof. by move=>? /up_set_empty. Qed.
Lemma up_non_empty s T : up s T ≢ ∅.
Proof. eapply non_empty_inhabited, elem_of_up. Qed.
Lemma up_closed S T : closed S T → up_set S T ≡ S.
Proof.
  intros; split; auto using subseteq_up_set; intros s.
  unfold up_set; rewrite elem_of_bind; intros (s'&Hstep&?).
  induction Hstep; eauto using closed_step.
Qed.
Lemma up_subseteq s T S : closed S T → s ∈ S → sts.up s T ⊆ S.
Proof. move=> ?? s' ?. eauto using closed_steps. Qed.
Lemma up_set_subseteq S1 T S2 : closed S2 T → S1 ⊆ S2 → sts.up_set S1 T ⊆ S2.
Proof. move=> ?? s [s' [? ?]]. eauto using closed_steps. Qed.
End sts.

Notation steps := (rtc step).
End sts.

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
Global Existing Instance sts_equiv.
Global Instance sts_valid : Valid (car sts) := λ x,
  match x with
  | auth s T => tok s ∩ T ≡ ∅
  | frag S' T => closed S' T ∧ S' ≢ ∅
  end.
Global Instance sts_core : Core (car sts) := λ x,
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
Global Existing Instance sts_disjoint.
Global Instance sts_op : Op (car sts) := λ x1 x2,
  match x1, x2 with
  | frag S1 T1, frag S2 T2 => frag (S1 ∩ S2) (T1 ∪ T2)
  | auth s T1, frag _ T2 => auth s (T1 ∪ T2)
  | frag _ T1, auth s T2 => auth s (T1 ∪ T2)
  | auth s T1, auth _ T2 => auth s (T1 ∪ T2)(* never happens *)
  end.
Global Instance sts_div : Div (car sts) := λ x1 x2,
  match x1, x2 with
  | frag S1 T1, frag S2 T2 => frag (up_set S1 (T1 ∖ T2)) (T1 ∖ T2)
  | auth s T1, frag _ T2 => auth s (T1 ∖ T2)
  | frag _ T2, auth s T1 => auth s (T1 ∖ T2) (* never happens *)
  | auth s T1, auth _ T2 => frag (up s (T1 ∖ T2)) (T1 ∖ T2)
  end.

Hint Extern 50 (equiv (A:=set _) _ _) => set_solver : sts.
Hint Extern 50 (¬equiv (A:=set _) _ _) => set_solver : sts.
Hint Extern 50 (_ ∈ _) => set_solver : sts.
Hint Extern 50 (_ ⊆ _) => set_solver : sts.
Global Instance sts_equivalence: Equivalence ((≡) : relation (car sts)).
Proof.
  split.
  - by intros []; constructor.
  - by destruct 1; constructor.
  - destruct 1; inversion_clear 1; constructor; etrans; eauto.
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
  - destruct 3; simpl in *; destruct_and?; eauto using closed_op;
      match goal with H : closed _ _ |- _ => destruct H end; set_solver.
  - intros []; simpl; intros; destruct_and?; split;
      eauto using closed_up, up_non_empty, closed_up_set, up_set_empty with sts.
  - intros ???? (z&Hy&?&Hxz); destruct Hxz; inversion Hy; clear Hy;
      setoid_subst; destruct_and?; split_and?;
      rewrite disjoint_union_difference //;
      eauto using up_set_non_empty, up_non_empty, closed_up, closed_disjoint; [].
    eapply closed_up_set=> s ?; eapply closed_disjoint; eauto with sts.
  - intros [] [] []; constructor; rewrite ?assoc; auto with sts.
  - destruct 4; inversion_clear 1; constructor; auto with sts.
  - destruct 4; inversion_clear 1; constructor; auto with sts.
  - destruct 1; constructor; auto with sts.
  - destruct 3; constructor; auto with sts.
  - intros [|S T]; constructor; auto using elem_of_up with sts.
  - intros [|S T]; constructor; auto with sts.
  - intros [s T|S T]; constructor; auto with sts.
    + rewrite (up_closed (up _ _)); auto using closed_up with sts.
    + rewrite (up_closed (up_set _ _)); eauto using closed_up_set with sts.
  - intros x y ?? (z&Hy&?&Hxz); exists (core (x ⋅ y)); split_and?.
    + destruct Hxz; inversion_clear Hy; constructor; unfold up_set; set_solver.
    + destruct Hxz; inversion_clear Hy; simpl; split_and?;
        auto using closed_up_set_empty, closed_up_empty, up_non_empty; [].
      apply up_set_non_empty. set_solver.
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
    intros s2; rewrite elem_of_intersection. destruct_and?.
    unfold up_set; rewrite elem_of_bind; intros (?&s1&?&?&?).
    apply closed_steps with T2 s1; auto with sts.
Qed.
Canonical Structure R : cmraT := validityR (car sts).
End sts_dra. End sts_dra.

(** * The STS Resource Algebra *)
(** Finally, the general theory of STS that should be used by users *)
Notation stsR := (@sts_dra.R).

Section sts_definitions.
  Context {sts : stsT}.
  Definition sts_auth (s : sts.state sts) (T : sts.tokens sts) : stsR sts :=
    to_validity (sts_dra.auth s T).
  Definition sts_frag (S : sts.states sts) (T : sts.tokens sts) : stsR sts :=
    to_validity (sts_dra.frag S T).
  Definition sts_frag_up (s : sts.state sts) (T : sts.tokens sts) : stsR sts :=
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

Global Instance sts_cmra_discrete : CMRADiscrete (stsR sts).
Proof. apply validity_cmra_discrete. Qed.

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
Proof. done. Qed.
Lemma sts_frag_valid S T : ✓ sts_frag S T ↔ closed S T ∧ S ≢ ∅.
Proof. done. Qed.
Lemma sts_frag_up_valid s T : tok s ∩ T ≡ ∅ → ✓ sts_frag_up s T.
Proof. intros. by apply sts_frag_valid; auto using closed_up, up_non_empty. Qed.

Lemma sts_auth_frag_valid_inv s S T1 T2 :
  ✓ (sts_auth s T1 ⋅ sts_frag S T2) → s ∈ S.
Proof. by intros (?&?&Hdisj); inversion Hdisj. Qed.

(** Op *)
Lemma sts_op_auth_frag s S T :
  s ∈ S → closed S T → sts_auth s ∅ ⋅ sts_frag S T ≡ sts_auth s T.
Proof.
  intros; split; [split|constructor; set_solver]; simpl.
  - intros (?&?&?); by apply closed_disjoint with S.
  - intros; split_and?; last constructor; set_solver.
Qed.
Lemma sts_op_auth_frag_up s T :
  sts_auth s ∅ ⋅ sts_frag_up s T ≡ sts_auth s T.
Proof.
  intros; split; [split|constructor; set_solver]; simpl.
  - intros (?&[??]&?). by apply closed_disjoint with (up s T), elem_of_up.
  - intros; split_and?.
    + set_solver+.
    + by apply closed_up.
    + apply up_non_empty.
    + constructor; last set_solver. apply elem_of_up.
Qed.

Lemma sts_op_frag S1 S2 T1 T2 :
  T1 ∩ T2 ≡ ∅ → sts.closed S1 T1 → sts.closed S2 T2 →
  sts_frag (S1 ∩ S2) (T1 ∪ T2) ≡ sts_frag S1 T1 ⋅ sts_frag S2 T2.
Proof.
  intros HT HS1 HS2. rewrite /sts_frag.
  (* FIXME why does rewrite not work?? *)
  etrans; last eapply to_validity_op; first done; [].
  move=>/=[??]. split_and!; [auto; set_solver..|].
  constructor; done.
Qed.

(** Frame preserving updates *)
Lemma sts_update_auth s1 s2 T1 T2 :
  steps (s1,T1) (s2,T2) → sts_auth s1 T1 ~~> sts_auth s2 T2.
Proof.
  intros ?; apply validity_update.
  inversion 3 as [|? S ? Tf|]; simplify_eq/=; destruct_and?.
  destruct (steps_closed s1 s2 T1 T2 S Tf) as (?&?&?); auto; [].
  repeat (done || constructor).
Qed.

Lemma sts_update_frag S1 S2 T1 T2 :
  closed S2 T2 → S1 ⊆ S2 → T2 ⊆ T1 → sts_frag S1 T1 ~~> sts_frag S2 T2.
Proof.
  rewrite /sts_frag=> ? HS HT. apply validity_update.
  inversion 3 as [|? S ? Tf|]; simplify_eq/=.
  - split_and!; first done; first set_solver. constructor; set_solver.
  - split_and!; first done; first set_solver. constructor; set_solver.
Qed.

Lemma sts_update_frag_up s1 S2 T1 T2 :
  closed S2 T2 → s1 ∈ S2 → T2 ⊆ T1 → sts_frag_up s1 T1 ~~> sts_frag S2 T2.
Proof.
  intros ? ? HT; apply sts_update_frag; [intros; eauto using closed_steps..].
  rewrite <-HT. eapply up_subseteq; done.
Qed.

Lemma up_set_intersection S1 Sf Tf :
  closed Sf Tf → 
  S1 ∩ Sf ≡ S1 ∩ up_set (S1 ∩ Sf) Tf.
Proof.
  intros Hclf. apply (anti_symm (⊆)).
  + move=>s [HS1 HSf]. split. by apply HS1. by apply subseteq_up_set.
  + move=>s [HS1 [s' [/elem_of_mkSet Hsup Hs']]]. split; first done.
    eapply closed_steps, Hsup; first done. set_solver +Hs'.
Qed.

(** Inclusion *)
(* This is surprisingly different from to_validity_included. I am not sure
   whether this is because to_validity_included is non-canonical, or this
   one here is non-canonical - but I suspect both. *)
Lemma sts_frag_included S1 S2 T1 T2 :
  closed S2 T2 → S2 ≢ ∅ →
  (sts_frag S1 T1 ≼ sts_frag S2 T2) ↔
  (closed S1 T1 ∧ S1 ≢ ∅ ∧ ∃ Tf, T2 ≡ T1 ∪ Tf ∧ T1 ∩ Tf ≡ ∅ ∧
                                 S2 ≡ S1 ∩ up_set S2 Tf).
Proof.
  destruct (to_validity_included (sts_dra.car sts) (sts_dra.frag S1 T1) (sts_dra.frag S2 T2)) as [Hfincl Htoincl].
  intros Hcl2 HS2ne. split.
  - intros Hincl. destruct Hfincl as ((Hcl1 & ?) & (z & EQ & Hval & Hdisj)).
    { split; last done. split; done. }
    clear Htoincl. split_and!; try done; [].
    destruct z as [sf Tf|Sf Tf].
    { exfalso. inversion_clear EQ. }
    exists Tf. inversion_clear EQ as [|? ? ? ? HT2 HS2].
    inversion_clear Hdisj as [? ? ? ? _ HTdisj | |]. split_and!; [done..|].
    rewrite HS2. apply up_set_intersection. apply Hval.
  - intros (Hcl & Hne & (Tf & HT & HTdisj & HS)). destruct Htoincl as ((Hcl' & ?) & (z & EQ)); last first.
    { exists z. exact EQ. } clear Hfincl.
    split; first (split; done). exists (sts_dra.frag (up_set S2 Tf) Tf). split_and!.
    + constructor; done.
    + simpl. split.
      * apply closed_up_set. move=>s Hs2. move:(closed_disjoint _ _ Hcl2 _ Hs2).
        set_solver +HT.
      * by apply up_set_non_empty.
    + constructor; last done. by rewrite -HS.
Qed.

Lemma sts_frag_included' S1 S2 T :
  closed S2 T → closed S1 T → S2 ≢ ∅ → S1 ≢ ∅ → S2 ≡ S1 ∩ up_set S2 ∅ →
  sts_frag S1 T ≼ sts_frag S2 T.
Proof.
  intros. apply sts_frag_included; split_and?; auto.
  exists ∅; split_and?; done || set_solver+.
Qed.

End stsRA.

(** STSs without tokens: Some stuff is simpler *)
Module sts_notok.
Structure stsT := STS {
  state : Type;
  prim_step : relation state;
}.
Arguments STS {_} _.
Arguments prim_step {_} _ _.
Notation states sts := (set (state sts)).

Canonical sts_notok (sts : stsT) : sts.stsT :=
  sts.STS (token:=Empty_set) (@prim_step sts) (λ _, ∅).

Section sts.
Context {sts : stsT}.
Implicit Types s : state sts.
Implicit Types S : states sts.

Notation prim_steps := (rtc prim_step).

Lemma sts_step s1 s2 :
  prim_step s1 s2 → sts.step (s1, ∅) (s2, ∅).
Proof.
  intros. split; set_solver.
Qed.

Lemma sts_steps s1 s2 :
  prim_steps s1 s2 → sts.steps (s1, ∅) (s2, ∅).
Proof.
  induction 1; eauto using sts_step, rtc_refl, rtc_l.
Qed.

Lemma frame_prim_step T s1 s2 :
  sts.frame_step T s1 s2 → prim_step s1 s2.
Proof.
  inversion 1 as [??? Hstep]. inversion_clear Hstep. done.
Qed.

Lemma prim_frame_step T s1 s2 :
  prim_step s1 s2 → sts.frame_step T s1 s2.
Proof.
  intros Hstep. apply sts.Frame_step with ∅ ∅; first set_solver.
  by apply sts_step.
Qed.

Lemma mk_closed S :
  (∀ s1 s2, s1 ∈ S → prim_step s1 s2 → s2 ∈ S) → sts.closed S ∅.
Proof.
  intros ?. constructor; first by set_solver.
  intros ????. eauto using frame_prim_step.
Qed.

End sts.
Notation steps := (rtc prim_step).
End sts_notok.

Coercion sts_notok.sts_notok : sts_notok.stsT >-> sts.stsT.
Notation sts_notokT := sts_notok.stsT.
Notation STS_NoTok := sts_notok.STS.

Section sts_notokRA.
Import sts_notok.
Context {sts : sts_notokT}.
Implicit Types s : state sts.
Implicit Types S : states sts.

Lemma sts_notok_update_auth s1 s2 :
  rtc prim_step s1 s2 → sts_auth s1 ∅ ~~> sts_auth s2 ∅.
Proof.
  intros. by apply sts_update_auth, sts_steps.
Qed.

End sts_notokRA.

