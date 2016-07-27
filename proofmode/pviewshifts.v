From iris.proofmode Require Import coq_tactics spec_patterns.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export pviewshifts.
Import uPred.

Section pvs.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P Q : iProp Λ Σ.

Global Instance from_pure_pvs E P φ : FromPure P φ → FromPure (|={E}=> P) φ.
Proof. intros ??. by rewrite -pvs_intro (from_pure P). Qed.
Global Instance from_assumption_pvs E p P Q :
  FromAssumption p P Q → FromAssumption p P (|={E}=> Q)%I.
Proof. rewrite /FromAssumption=>->. apply pvs_intro. Qed.
Global Instance from_sep_pvs E P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|={E}=> P) (|={E}=> Q1) (|={E}=> Q2).
Proof. rewrite /FromSep=><-. apply pvs_sep. Qed.
Global Instance or_split_pvs E1 E2 P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|={E1,E2}=> P) (|={E1,E2}=> Q1) (|={E1,E2}=> Q2).
Proof. rewrite /FromOr=><-. apply or_elim; apply pvs_mono; auto with I. Qed.
Global Instance exists_split_pvs {A} E1 E2 P (Φ : A → iProp Λ Σ) :
  FromExist P Φ → FromExist (|={E1,E2}=> P) (λ a, |={E1,E2}=> Φ a)%I.
Proof.
  rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.
Global Instance frame_pvs E1 E2 R P Q :
  Frame R P Q → Frame R (|={E1,E2}=> P) (|={E1,E2}=> Q).
Proof. rewrite /Frame=><-. by rewrite pvs_frame_l. Qed.
Global Instance into_wand_pvs E1 E2 R P Q :
  IntoWand R P Q → IntoWand R (|={E1,E2}=> P) (|={E1,E2}=> Q) | 100.
Proof. rewrite /IntoWand=>->. apply wand_intro_l. by rewrite pvs_wand_r. Qed.

Global Instance timeless_elim_pvs E1 E2 Q : TimelessElim (|={E1,E2}=> Q).
Proof.
  intros P ?. rewrite (pvs_timeless E1 P) pvs_frame_r.
  by rewrite wand_elim_r pvs_trans; last set_solver.
Qed.

Class IsFSA {A} (P : iProp Λ Σ) (E : coPset)
    (fsa : FSA Λ Σ A) (fsaV : Prop) (Φ : A → iProp Λ Σ) := {
  is_fsa : P ⊣⊢ fsa E Φ;
  is_fsa_is_fsa :> FrameShiftAssertion fsaV fsa;
}.
Global Arguments is_fsa {_} _ _ _ _ _ {_}.
Global Instance is_fsa_pvs E P :
  IsFSA (|={E}=> P)%I E pvs_fsa True (λ _, P).
Proof. split. done. apply _. Qed.
Global Instance is_fsa_fsa {A} (fsa : FSA Λ Σ A) E Φ :
  FrameShiftAssertion fsaV fsa → IsFSA (fsa E Φ) E fsa fsaV Φ.
Proof. done. Qed.

Global Instance to_assert_pvs {A} P Q E (fsa : FSA Λ Σ A) fsaV Φ :
  IsFSA Q E fsa fsaV Φ → IntoAssert P Q (|={E}=> P).
Proof.
  intros. by rewrite /IntoAssert pvs_frame_r wand_elim_r (is_fsa Q) fsa_pvs_fsa.
Qed.
Global Instance timeless_elim_fsa {A} Q E (fsa : FSA Λ Σ A) fsaV Φ :
  IsFSA Q E fsa fsaV Φ → TimelessElim Q.
Proof.
  intros ? P ?. rewrite (is_fsa Q) -{2}fsa_pvs_fsa.
  by rewrite (pvs_timeless _ P) pvs_frame_r wand_elim_r.
Qed.

Lemma tac_pvs_intro Δ E1 E2 Q : E1 = E2 → (Δ ⊢ Q) → Δ ⊢ |={E1,E2}=> Q.
Proof. intros -> ->. apply pvs_intro. Qed.

Lemma tac_pvs_elim Δ Δ' E1 E2 E3 i p P' E1' E2' P Q :
  envs_lookup i Δ = Some (p, P') → P' = (|={E1',E2'}=> P)%I →
  (E1' = E1 ∧ E2' = E2 ∧ E2 ⊆ E1 ∪ E3
  ∨ E2 = E2' ∪ E1 ∖ E1' ∧ E2' ⊥ E1 ∖ E1' ∧ E1' ⊆ E1 ∧ E2' ⊆ E1' ∪ E3) →
  envs_replace i p false (Esnoc Enil i P) Δ = Some Δ' →
  (Δ' ={E2,E3}=> Q) → Δ ={E1,E3}=> Q.
Proof.
  intros ? -> HE ? HQ. rewrite envs_replace_sound //; simpl.
  rewrite always_if_elim right_id pvs_frame_r wand_elim_r HQ.
  destruct HE as [(?&?&?)|(?&?&?&?)]; subst; first (by apply pvs_trans).
  etrans; [eapply pvs_mask_frame'|apply pvs_trans]; auto; set_solver.
Qed.

Lemma tac_pvs_elim_fsa {A} (fsa : FSA Λ Σ A) fsaV Δ Δ' E i p P' P Q Φ :
  envs_lookup i Δ = Some (p, P') → P' = (|={E}=> P)%I →
  IsFSA Q E fsa fsaV Φ →
  envs_replace i p false (Esnoc Enil i P) Δ = Some Δ' →
  (Δ' ⊢ fsa E Φ) → Δ ⊢ Q.
Proof.
  intros ? -> ??. rewrite (is_fsa Q) -fsa_pvs_fsa.
  eapply tac_pvs_elim; set_solver.
Qed.
End pvs.

Tactic Notation "iPvsIntro" := apply tac_pvs_intro; first try fast_done.

Tactic Notation "iPvsCore" constr(H) :=
  match goal with
  | |- _ ⊢ |={_,_}=> _ =>
    eapply tac_pvs_elim with _ _ H _ _ _ _ _;
      [env_cbv; reflexivity || fail "iPvs:" H "not found"
      |let P := match goal with |- ?P = _ => P end in
       reflexivity || fail "iPvs:" H ":" P "not a pvs with the right mask"
      |first
         [left; split_and!;
            [reflexivity|reflexivity|try (rewrite (idemp_L (∪)); reflexivity)]
         |right; split; first reflexivity]
      |env_cbv; reflexivity|]
  | |- _ =>
    eapply tac_pvs_elim_fsa with _ _ _ _ H _ _ _ _;
      [env_cbv; reflexivity || fail "iPvs:" H "not found"
      |let P := match goal with |- ?P = _ => P end in
       reflexivity || fail "iPvs:" H ":" P "not a pvs with the right mask"
      |let P := match goal with |- IsFSA ?P _ _ _ _ => P end in
       apply _ || fail "iPvs:" P "not a pvs"
      |env_cbv; reflexivity|simpl]
  end.

Tactic Notation "iPvs" open_constr(H) :=
  iDestructHelp H as (fun H => iPvsCore H; last iDestruct H as "?").
Tactic Notation "iPvs" open_constr(H) "as" constr(pat) :=
  iDestructHelp H as (fun H => iPvsCore H; last iDestruct H as pat).
Tactic Notation "iPvs" open_constr(H) "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  iDestructHelp H as (fun H => iPvsCore H; last iDestruct H as ( x1 ) pat).
Tactic Notation "iPvs" open_constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  iDestructHelp H as (fun H => iPvsCore H; last iDestruct H as ( x1 x2 ) pat).
Tactic Notation "iPvs" open_constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  iDestructHelp H as (fun H => iPvsCore H; last iDestruct H as ( x1 x2 x3 ) pat).
Tactic Notation "iPvs" open_constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  iDestructHelp H as (fun H =>
    iPvsCore H; last iDestruct H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "iPvs" open_constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  iDestructHelp H as (fun H =>
    iPvsCore H; last iDestruct H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "iPvs" open_constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  iDestructHelp H as (fun H =>
    iPvsCore H; last iDestruct H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "iPvs" open_constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  iDestructHelp H as (fun H =>
    iPvsCore H; last iDestruct H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "iPvs" open_constr(H) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  iDestructHelp H as (fun H =>
    iPvsCore H; last iDestruct H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).

Hint Extern 2 (of_envs _ ⊢ _) =>
  match goal with |- _ ⊢ (|={_}=> _)%I => iPvsIntro end.
