From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export pviewshifts.
From iris.program_logic Require Export invariants.
Import uPred.

Section invariants.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Λ Σ.

Lemma tac_inv_fsa {A} (fsa : FSA Λ Σ A) fsaV Δ Δ' E N i P Q Φ :
  IsFSA Q E fsa fsaV Φ →
  fsaV → nclose N ⊆ E → (of_envs Δ ⊢ inv N P) →
  envs_app false (Esnoc Enil i (▷ P)) Δ = Some Δ' →
  (Δ' ⊢ fsa (E ∖ nclose N) (λ a, ▷ P ★ Φ a)) → Δ ⊢ Q.
Proof.
  intros ????? HΔ'. rewrite (is_fsa Q) -(inv_fsa fsa _ _ P) //.
  rewrite // -always_and_sep_l. apply and_intro; first done.
  rewrite envs_app_sound //; simpl. by rewrite right_id HΔ'.
Qed.

Lemma tac_inv_fsa_timeless {A} (fsa : FSA Λ Σ A) fsaV Δ Δ' E N i P Q Φ :
  IsFSA Q E fsa fsaV Φ →
  fsaV → nclose N ⊆ E → (of_envs Δ ⊢ inv N P) → TimelessP P →
  envs_app false (Esnoc Enil i P) Δ = Some Δ' →
  (Δ' ⊢ fsa (E ∖ nclose N) (λ a, P ★ Φ a)) → Δ ⊢ Q.
Proof.
  intros ?????? HΔ'. rewrite (is_fsa Q) -(inv_fsa fsa _ _ P) //.
  rewrite // -always_and_sep_l. apply and_intro, wand_intro_l; first done.
  trans (|={E ∖ N}=> P ★ Δ)%I; first by rewrite pvs_timeless pvs_frame_r.
  apply (fsa_strip_pvs _).
  rewrite envs_app_sound //; simpl. rewrite right_id HΔ' wand_elim_r.
  apply: fsa_mono=> v. by rewrite -later_intro.
Qed.
End invariants.

Tactic Notation "iInvCore" constr(N) "as" constr(H) :=
  eapply tac_inv_fsa with _ _ _ _ N H _ _;
    [let P := match goal with |- IsFSA ?P _ _ _ _ => P end in
     apply _ || fail "iInv: cannot viewshift in goal" P
    |try fast_done (* atomic *)
    |done || eauto with ndisj (* [eauto with ndisj] is slow *)
    |iAssumption || fail "iInv: invariant" N "not found"
    |env_cbv; reflexivity
    |simpl (* get rid of FSAs *)].

Tactic Notation "iInv" constr(N) "as" constr(pat) :=
  let H := iFresh in iInvCore N as H; last iDestruct H as pat.
Tactic Notation "iInv" constr(N) "as" "{" simple_intropattern(x1) "}"
    constr(pat) :=
  let H := iFresh in iInvCore N as H; last iDestruct H as {x1} pat.
Tactic Notation "iInv" constr(N) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) "}" constr(pat) :=
  let H := iFresh in iInvCore N as H; last iDestruct H as {x1 x2} pat.
Tactic Notation "iInv" constr(N) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) "}" constr(pat) :=
  let H := iFresh in iInvCore N as H; last iDestruct H as {x1 x2 x3} pat.
Tactic Notation "iInv" constr(N) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) "}"
    constr(pat) :=
  let H := iFresh in iInvCore N as H; last iDestruct H as {x1 x2 x3 x4} pat.

Tactic Notation "iInvCore>" constr(N) "as" constr(H) :=
  eapply tac_inv_fsa_timeless with _ _ _ _ N H _ _;
    [let P := match goal with |- IsFSA ?P _ _ _ _ => P end in
     apply _ || fail "iInv: cannot viewshift in goal" P
    |try fast_done (* atomic *)
    |done || eauto with ndisj (* [eauto with ndisj] is slow *)
    |iAssumption || fail "iOpenInv: invariant" N "not found"
    |let P := match goal with |- TimelessP ?P => P end in
     apply _ || fail "iInv:" P "not timeless"
    |env_cbv; reflexivity
    |simpl (* get rid of FSAs *)].

Tactic Notation "iInv>" constr(N) "as" constr(pat) :=
  let H := iFresh in iInvCore> N as H; last iDestruct H as pat.
Tactic Notation "iInv>" constr(N) "as" "{" simple_intropattern(x1) "}"
    constr(pat) :=
  let H := iFresh in iInvCore> N as H; last iDestruct H as {x1} pat.
Tactic Notation "iInv>" constr(N) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) "}" constr(pat) :=
  let H := iFresh in iInvCore> N as H; last iDestruct H as {x1 x2} pat.
Tactic Notation "iInv>" constr(N) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) "}" constr(pat) :=
  let H := iFresh in iInvCore> N as H; last iDestruct H as {x1 x2 x3} pat.
Tactic Notation "iInv>" constr(N) "as" "{" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) "}"
    constr(pat) :=
  let H := iFresh in iInvCore> N as H; last iDestruct H as {x1 x2 x3 x4} pat.
