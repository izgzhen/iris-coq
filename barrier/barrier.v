From program_logic Require Export sts.
From heap_lang Require Export derived heap wp_tactics notation.

Definition newchan := (λ: "", ref '0)%L.
Definition signal := (λ: "x", "x" <- '1)%L.
Definition wait := (rec: "wait" "x" := if: !"x" = '1 then '() else "wait" "x")%L.

(** The STS describing the main barrier protocol. *)
Module barrier_proto.
  Inductive phase := Low | High.
  Record stateT := State { state_phase : phase; state_I : gset gname }.
  Inductive token := Change (i : gname) | Send.

  Global Instance stateT_inhabited: Inhabited stateT.
  Proof. split. exact (State Low ∅). Qed.

  Definition change_tokens (I : gset gname) : set token :=
    mkSet (λ t, match t with Change i => i ∈ I | Send => False end).

  Inductive trans : relation stateT :=
  | ChangeI p I2 I1 : trans (State p I1) (State p I2)
  | ChangePhase I : trans (State Low I) (State High I).

  Definition tok (s : stateT) : set token :=
      change_tokens (state_I s)
    ∪ match state_phase s with Low => ∅ | High => {[ Send ]} end.

  Definition sts := sts.STS trans tok.

  Definition i_states (i : gname) : set stateT :=
    mkSet (λ s, i ∈ state_I s).

  Lemma i_states_closed i :
    sts.closed sts (i_states i) {[ Change i ]}.
  Proof.
    split.
    - apply non_empty_inhabited.
    
End barrier_proto.

