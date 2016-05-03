From iris.proofmode Require Import coq_tactics spec_patterns.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export pviewshifts.
Import uPred.

Section pvs.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P Q : iProp Λ Σ.

Global Instance to_assumption_pvs E p P Q :
  ToAssumption p P Q → ToAssumption p P (|={E}=> Q)%I.
Proof. rewrite /ToAssumption=>->. apply pvs_intro. Qed.
Global Instance sep_split_pvs E P Q1 Q2 :
  SepSplit P Q1 Q2 → SepSplit (|={E}=> P) (|={E}=> Q1) (|={E}=> Q2).
Proof. rewrite /SepSplit=><-. apply pvs_sep. Qed.
Global Instance or_split_pvs E1 E2 P Q1 Q2 :
  OrSplit P Q1 Q2 → OrSplit (|={E1,E2}=> P) (|={E1,E2}=> Q1) (|={E1,E2}=> Q2).
Proof. rewrite /OrSplit=><-. apply or_elim; apply pvs_mono; auto with I. Qed.
Global Instance exists_split_pvs {A} E1 E2 P (Φ : A → iProp Λ Σ) :
  ExistSplit P Φ → ExistSplit (|={E1,E2}=> P) (λ a, |={E1,E2}=> Φ a)%I.
Proof.
  rewrite /ExistSplit=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
Qed.
Global Instance frame_pvs E1 E2 R P mQ :
  Frame R P mQ →
  Frame R (|={E1,E2}=> P) (Some (|={E1,E2}=> from_option True mQ))%I.
Proof. rewrite /Frame=><-. by rewrite pvs_frame_l. Qed.
Global Instance to_wand_pvs E1 E2 R P Q :
  ToWand R P Q → ToWand R (|={E1,E2}=> P) (|={E1,E2}=> Q).
Proof. rewrite /ToWand=>->. apply wand_intro_l. by rewrite pvs_wand_r. Qed.

Class FSASplit {A} (P : iProp Λ Σ) (E : coPset)
    (fsa : FSA Λ Σ A) (fsaV : Prop) (Φ : A → iProp Λ Σ) := {
  fsa_split : fsa E Φ ⊢ P;
  fsa_split_fsa :> FrameShiftAssertion fsaV fsa;
}.
Global Arguments fsa_split {_} _ _ _ _ _ {_}.
Global Instance fsa_split_pvs E P :
  FSASplit (|={E}=> P)%I E pvs_fsa True (λ _, P).
Proof. split. done. apply _. Qed.

Lemma tac_pvs_intro Δ E Q : Δ ⊢ Q → Δ ⊢ |={E}=> Q.
Proof. intros ->. apply pvs_intro. Qed.

Lemma tac_pvs_elim Δ Δ' E1 E2 E3 i p P Q :
  envs_lookup i Δ = Some (p, |={E1,E2}=> P)%I →
  envs_replace i p false (Esnoc Enil i P) Δ = Some Δ' →
  E2 ⊆ E1 ∪ E3 →
  Δ' ⊢ (|={E2,E3}=> Q) → Δ ⊢ |={E1,E3}=> Q.
Proof.
  intros ??? HQ. rewrite envs_replace_sound //; simpl. destruct p.
  - by rewrite always_elim right_id pvs_frame_r wand_elim_r HQ pvs_trans.
  - by rewrite right_id pvs_frame_r wand_elim_r HQ pvs_trans.
Qed.

Lemma tac_pvs_elim_fsa {A} (fsa : FSA Λ Σ A) fsaV Δ Δ' E i p P Q Φ :
  envs_lookup i Δ = Some (p, |={E}=> P)%I → FSASplit Q E fsa fsaV Φ →
  envs_replace i p false (Esnoc Enil i P) Δ = Some Δ' →
  Δ' ⊢ fsa E Φ → Δ ⊢ Q.
Proof.
  intros ???. rewrite -(fsa_split Q) -fsa_pvs_fsa.
  eapply tac_pvs_elim; set_solver.
Qed.

Lemma tac_pvs_timeless Δ Δ' E1 E2 i p P Q :
  envs_lookup i Δ = Some (p, ▷ P)%I → TimelessP P →
  envs_simple_replace i p (Esnoc Enil i P) Δ = Some Δ' →
  Δ' ⊢ (|={E1,E2}=> Q) → Δ ⊢ (|={E1,E2}=> Q).
Proof.
  intros ??? HQ. rewrite envs_simple_replace_sound //; simpl.
  destruct p.
  - rewrite always_later (pvs_timeless E1 (□ P)%I) pvs_frame_r.
    by rewrite right_id wand_elim_r HQ pvs_trans; last set_solver.
  - rewrite (pvs_timeless E1 P) pvs_frame_r right_id wand_elim_r HQ.
    by rewrite pvs_trans; last set_solver.
Qed.

Lemma tac_pvs_timeless_fsa {A} (fsa : FSA Λ Σ A) fsaV Δ Δ' E i p P Q Φ :
  FSASplit Q E fsa fsaV Φ →
  envs_lookup i Δ = Some (p, ▷ P)%I → TimelessP P →
  envs_simple_replace i p (Esnoc Enil i P) Δ = Some Δ' →
  Δ' ⊢ fsa E Φ → Δ ⊢ Q.
Proof.
  intros ????. rewrite -(fsa_split Q) -fsa_pvs_fsa.
  eauto using tac_pvs_timeless.
Qed.

Lemma tac_pvs_assert {A} (fsa : FSA Λ Σ A) fsaV Δ Δ1 Δ2 Δ2' E lr js j P Q Φ :
  FSASplit Q E fsa fsaV Φ →
  envs_split lr js Δ = Some (Δ1,Δ2) →
  envs_app false (Esnoc Enil j P) Δ2 = Some Δ2' →
  Δ1 ⊢ (|={E}=> P) → Δ2' ⊢ fsa E Φ → Δ ⊢ Q.
Proof.
  intros ??? HP HQ. rewrite -(fsa_split Q) -fsa_pvs_fsa -HQ envs_split_sound //.
  rewrite HP envs_app_sound //; simpl.
  by rewrite right_id pvs_frame_r wand_elim_r.
Qed.
End pvs.

Tactic Notation "iPvsIntro" := apply tac_pvs_intro.

Tactic Notation "iPvsCore" constr(H) :=
  match goal with
  | |- _ ⊢ |={_,_}=> _ =>
    eapply tac_pvs_elim with _ _ H _ _;
      [env_cbv; reflexivity || fail "iPvs:" H "not found"
      |env_cbv; reflexivity
      |try (rewrite (idemp_L (∪)); reflexivity)|]
  | |- _ =>
    eapply tac_pvs_elim_fsa with _ _ _ _ H _ _ _;
      [env_cbv; reflexivity || fail "iPvs:" H "not found"
      |let P := match goal with |- FSASplit ?P _ _ _ _ => P end in
       apply _ || fail "iPvs:" P "not a pvs"
      |env_cbv; reflexivity|simpl]
  end.

Tactic Notation "iPvs" open_constr(H) :=
  iDestructHelp H as (fun H => iPvsCore H; last iDestruct H as "?").
Tactic Notation "iPvs" open_constr(H) "as" constr(pat) :=
  iDestructHelp H as (fun H => iPvsCore H; last iDestruct H as pat).
Tactic Notation "iPvs" open_constr(H) "as" "{" simple_intropattern(x1) "}"
    constr(pat) :=
  iDestructHelp H as (fun H => iPvsCore H; last iDestruct H as { x1 } pat).
Tactic Notation "iPvs" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) "}" constr(pat) :=
  iDestructHelp H as (fun H => iPvsCore H; last iDestruct H as { x1 x2 } pat).
Tactic Notation "iPvs" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) "}" constr(pat) :=
  iDestructHelp H as (fun H => iPvsCore H; last iDestruct H as { x1 x2 x3 } pat).
Tactic Notation "iPvs" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) "}"
    constr(pat) :=
  iDestructHelp H as (fun H =>
    iPvsCore H; last iDestruct H as { x1 x2 x3 x4 } pat).
Tactic Notation "iPvs" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) "}" constr(pat) :=
  iDestructHelp H as (fun H =>
    iPvsCore H; last iDestruct H as { x1 x2 x3 x4 x5 } pat).
Tactic Notation "iPvs" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) "}" constr(pat) :=
  iDestructHelp H as (fun H =>
    iPvsCore H; last iDestruct H as { x1 x2 x3 x4 x5 x6 } pat).
Tactic Notation "iPvs" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) "}"
    constr(pat) :=
  iDestructHelp H as (fun H =>
    iPvsCore H; last iDestruct H as { x1 x2 x3 x4 x5 x6 x7 } pat).
Tactic Notation "iPvs" open_constr(H) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) "}" constr(pat) :=
  iDestructHelp H as (fun H =>
    iPvsCore H; last iDestruct H as { x1 x2 x3 x4 x5 x6 x7 x8 } pat).

Tactic Notation "iTimeless" constr(H) :=
  match goal with
  | |- _ ⊢ |={_,_}=> _ =>
     eapply tac_pvs_timeless with _ H _ _;
       [env_cbv; reflexivity || fail "iTimeless:" H "not found"
       |let P := match goal with |- TimelessP ?P => P end in
        apply _ || fail "iTimeless: " P "not timeless"
       |env_cbv; reflexivity|simpl]
  | |- _ =>
     eapply tac_pvs_timeless_fsa with _ _ _ _ H _ _ _;
       [let P := match goal with |- FSASplit ?P _ _ _ _ => P end in
        apply _ || fail "iTimeless: " P "not a pvs"
       |env_cbv; reflexivity || fail "iTimeless:" H "not found"
       |let P := match goal with |- TimelessP ?P => P end in
        apply _ || fail "iTimeless: " P "not timeless"
       |env_cbv; reflexivity|simpl]
  end.

Tactic Notation "iTimeless" constr(H) "as" constr(Hs) :=
  iTimeless H; iDestruct H as Hs.

Tactic Notation "iPvsAssert" constr(Q) "as" constr(pat) "with" constr(Hs) :=
  let H := iFresh in
  let Hs := spec_pat.parse_one Hs in
  lazymatch Hs with
  | SAssert ?lr ?Hs =>
     eapply tac_pvs_assert with _ _ _ _ _ _ lr Hs H Q _;
       [let P := match goal with |- FSASplit ?P _ _ _ _ => P end in
        apply _ || fail "iPvsAssert: " P "not a pvs"
       |env_cbv; reflexivity || fail "iPvsAssert:" Hs "not found"
       |env_cbv; reflexivity|
       |simpl; iDestruct H as pat]
  | ?pat => fail "iPvsAssert: invalid pattern" pat
  end.
Tactic Notation "iPvsAssert" constr(Q) "as" constr(pat) :=
  iPvsAssert Q as pat with "[]".
