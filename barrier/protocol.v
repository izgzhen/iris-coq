From algebra Require Export sts.
From program_logic Require Import ghost_ownership.

(** The STS describing the main barrier protocol. Every state has an index-set
    associated with it. These indices are actually [gname], because we use them
    with saved propositions. *)
Inductive phase := Low | High.
Record state := State { state_phase : phase; state_I : gset gname }.
Add Printing Constructor state.
Inductive token := Change (i : gname) | Send.

Global Instance stateT_inhabited: Inhabited state := populate (State Low ∅).
Global Instance Change_inj : Inj (=) (=) Change.
Proof. by injection 1. Qed.

Inductive prim_step : relation state :=
  | ChangeI p I2 I1 : prim_step (State p I1) (State p I2)
  | ChangePhase I : prim_step (State Low I) (State High I).

Definition tok (s : state) : set token :=
  {[ t | ∃ i, t = Change i ∧ i ∉ state_I s ]} ∪
  (if state_phase s is High then {[ Send ]} else ∅).
Global Arguments tok !_ /.

Canonical Structure sts := sts.STS prim_step tok.

(* The set of states containing some particular i *)
Definition i_states (i : gname) : set state := {[ s | i ∈ state_I s ]}.

(* The set of low states *)
Definition low_states : set state := {[ s | state_phase s = Low ]}.

Lemma i_states_closed i : sts.closed (i_states i) {[ Change i ]}.
Proof.
  split; first (intros [[] I]; set_solver).
  (* If we do the destruct of the states early, and then inversion
     on the proof of a transition, it doesn't work - we do not obtain
     the equalities we need. So we destruct the states late, because this
     means we can use "destruct" instead of "inversion". *)
  intros s1 s2 Hs1 [T1 T2 Hdisj Hstep'].
  inversion_clear Hstep' as [? ? ? ? Htrans _ _ Htok].
  destruct Htrans as [[] ??|]; done || set_solver.
Qed.

Lemma low_states_closed : sts.closed low_states {[ Send ]}.
Proof.
  split; first (intros [??]; set_solver).
  intros s1 s2 Hs1 [T1 T2 Hdisj Hstep'].
  inversion_clear Hstep' as [? ? ? ? Htrans _ _ Htok].
  destruct Htrans as [[] ??|]; done || set_solver.
Qed.

(* Proof that we can take the steps we need. *)
Lemma signal_step I : sts.steps (State Low I, {[Send]}) (State High I, ∅).
Proof. apply rtc_once. constructor; first constructor; set_solver. Qed.

Lemma wait_step i I :
  i ∈ I →
  sts.steps (State High I, {[ Change i ]}) (State High (I ∖ {[ i ]}), ∅).
Proof.
  intros. apply rtc_once.
  constructor; first constructor; [set_solver..|].
  apply elem_of_equiv=>-[j|]; last set_solver.
  destruct (decide (i = j)); set_solver.
Qed.

Lemma split_step p i i1 i2 I :
  i ∈ I → i1 ∉ I → i2 ∉ I → i1 ≠ i2 →
  sts.steps
    (State p I, {[ Change i ]})
    (State p ({[i1]} ∪ ({[i2]} ∪ (I ∖ {[i]}))), {[ Change i1; Change i2 ]}).
Proof.
  intros. apply rtc_once. constructor; first constructor.
  - destruct p; set_solver.
  - destruct p; set_solver.
  - apply elem_of_equiv=> /= -[j|]; last set_solver.
    set_unfold; rewrite !(inj_iff Change).
    assert (Change j ∈ match p with Low => ∅ | High => {[Send]} end ↔ False)
      as -> by (destruct p; set_solver).
    destruct (decide (i1 = j)) as [->|]; first naive_solver.
    destruct (decide (i2 = j)) as [->|]; first naive_solver.
    destruct (decide (i = j)) as [->|]; naive_solver.
Qed.
