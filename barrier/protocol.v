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

Definition change_tok (I : gset gname) : set token :=
  {[ t | match t with Change i => i ∉ I | Send => False end ]}.
Definition send_tok (p : phase) : set token :=
  match p with Low => ∅ | High => {[ Send ]} end.
Definition tok (s : state) : set token :=
  change_tok (state_I s) ∪ send_tok (state_phase s).
Global Arguments tok !_ /.

Canonical Structure sts := sts.STS prim_step tok.

(* The set of states containing some particular i *)
Definition i_states (i : gname) : set state := {[ s | i ∈ state_I s ]}.

(* The set of low states *)
Definition low_states : set state := {[ s | state_phase s = Low ]}.

Lemma i_states_closed i : sts.closed (i_states i) {[ Change i ]}.
Proof.
  split.
  - move=>[p I]. rewrite /= !elem_of_mkSet /= =>HI.
    destruct p; set_solver by eauto.
  - (* If we do the destruct of the states early, and then inversion
       on the proof of a transition, it doesn't work - we do not obtain
       the equalities we need. So we destruct the states late, because this
       means we can use "destruct" instead of "inversion". *)
    move=>s1 s2. rewrite !elem_of_mkSet.
    intros Hs1 [T1 T2 Hdisj Hstep'].
    inversion_clear Hstep' as [? ? ? ? Htrans _ _ Htok].
    destruct Htrans; simpl in *; last done.
    move: Hs1 Hdisj Htok. rewrite elem_of_equiv_empty elem_of_equiv.
    move=> ? /(_ (Change i)) Hdisj /(_ (Change i)); move: Hdisj.
    rewrite elem_of_intersection elem_of_union !elem_of_mkSet.
    intros; apply dec_stable.
    destruct p; set_solver.
Qed.

Lemma low_states_closed : sts.closed low_states {[ Send ]}.
Proof.
  split.
  - move=>[p I]. rewrite /= /tok !elem_of_mkSet /= =>HI.
    destruct p; set_solver.
  - move=>s1 s2. rewrite !elem_of_mkSet.
    intros Hs1 [T1 T2 Hdisj Hstep'].
    inversion_clear Hstep' as [? ? ? ? Htrans _ _ Htok].
    destruct Htrans; simpl in *; first by destruct p.
    exfalso; set_solver.
Qed.

(* Proof that we can take the steps we need. *)
Lemma signal_step I : sts.steps (State Low I, {[Send]}) (State High I, ∅).
Proof. apply rtc_once. constructor; first constructor; set_solver. Qed.

Lemma wait_step i I :
  i ∈ I →
  sts.steps (State High I, {[ Change i ]}) (State High (I ∖ {[ i ]}), ∅).
Proof.
  intros. apply rtc_once.
  constructor; first constructor; simpl; [set_solver by eauto..|].
  (* TODO this proof is rather annoying. *)
  apply elem_of_equiv=>t. rewrite !elem_of_union.
  rewrite !elem_of_mkSet /change_tok /=.
  destruct t as [j|]; last set_solver.
  rewrite elem_of_difference elem_of_singleton.
  destruct (decide (i = j)); set_solver.
Qed.

Lemma split_step p i i1 i2 I :
  i ∈ I → i1 ∉ I → i2 ∉ I → i1 ≠ i2 →
  sts.steps
    (State p I, {[ Change i ]})
    (State p ({[i1]} ∪ ({[i2]} ∪ (I ∖ {[i]}))), {[ Change i1; Change i2 ]}).
Proof.
  intros. apply rtc_once.
  constructor; first constructor; simpl.
  - destruct p; set_solver.
  (* This gets annoying... and I think I can see a pattern with all these proofs. Automatable? *)
  - apply elem_of_equiv=>t. destruct t; last set_solver.
    rewrite !elem_of_mkSet !not_elem_of_union !not_elem_of_singleton
      not_elem_of_difference elem_of_singleton !(inj_iff Change).
    destruct p; naive_solver.
  - apply elem_of_equiv=>t. destruct t as [j|]; last set_solver.
    rewrite !elem_of_mkSet !not_elem_of_union !not_elem_of_singleton
      not_elem_of_difference elem_of_singleton !(inj_iff Change).
    destruct (decide (i1 = j)) as [->|]; first tauto.
    destruct (decide (i2 = j)) as [->|]; intuition.
Qed.
