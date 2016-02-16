From program_logic Require Export sts.
From heap_lang Require Export derived heap wp_tactics notation.

Definition newchan := (λ: "", ref '0)%L.
Definition signal := (λ: "x", "x" <- '1)%L.
Definition wait := (rec: "wait" "x" :=if: !"x" = '1 then '() else "wait" "x")%L.

(** The STS describing the main barrier protocol. Every state has an index-set
    associated with it. These indices are actually [gname], because we use them
    with saved propositions. *)
Module barrier_proto.
  Inductive phase := Low | High.
  Record stateT := State { state_phase : phase; state_I : gset gname }.
  Inductive token := Change (i : gname) | Send.

  Global Instance stateT_inhabited: Inhabited stateT.
  Proof. split. exact (State Low ∅). Qed.

  Definition change_tokens (I : gset gname) : set token :=
    mkSet (λ t, match t with Change i => i ∉ I | Send => False end).

  Inductive trans : relation stateT :=
  | ChangeI p I2 I1 : trans (State p I1) (State p I2)
  | ChangePhase I : trans (State Low I) (State High I).

  Definition tok (s : stateT) : set token :=
      change_tokens (state_I s)
    ∪ match state_phase s with Low => ∅ | High => {[ Send ]} end.

  Definition sts := sts.STS trans tok.

  (* The set of states containing some particular i *)
  Definition i_states (i : gname) : set stateT :=
    mkSet (λ s, i ∈ state_I s).

  Lemma i_states_closed i :
    sts.closed sts (i_states i) {[ Change i ]}.
  Proof.
    split.
    - apply (non_empty_inhabited(State Low {[ i ]})). rewrite !mkSet_elem_of /=.
      apply lookup_singleton.
    - move=>[p I]. rewrite /= /tok !mkSet_elem_of /= =>HI.
      move=>s' /elem_of_intersection. rewrite !mkSet_elem_of /=.
      move=>[[Htok|Htok] ? ]; subst s'; first done.
      destruct p; done.
    - (* If we do the destruct of the states early, and then inversion
         on the proof of a transition, it doesn't work - we do not obtain
         the equalities we need. So we destruct the states late, because this
         means we can use "destruct" instead of "inversion". *)
      move=>s1 s2. rewrite !mkSet_elem_of /==> Hs1 Hstep.
      (* We probably want some helper lemmas for this... *)
      inversion_clear Hstep as [T1 T2 Hdisj Hstep'].
      inversion_clear Hstep' as [? ? ? ? Htrans _ _ Htok].
      destruct Htrans; last done; move:Hs1 Hdisj Htok.
      rewrite /= /tok /=.
      intros. apply dec_stable. 
      assert (Change i ∉ change_tokens I1) as HI1
        by (rewrite mkSet_not_elem_of; solve_elem_of +Hs1).
      assert (Change i ∉ change_tokens I2) as HI2.
      { destruct p.
        - solve_elem_of +Htok Hdisj HI1.
        - solve_elem_of +Htok Hdisj HI1 / discriminate. }
      done.
  Qed.

  (* The set of low states *)
  Definition low_states : set stateT :=
    mkSet (λ s, if state_phase s is Low then True else False).
  
  Lemma low_states_closed :
    sts.closed sts low_states {[ Send ]}.
  Proof.
    split.
    - apply (non_empty_inhabited(State Low ∅)). by rewrite !mkSet_elem_of /=.
    - move=>[p I]. rewrite /= /tok !mkSet_elem_of /= =>HI.
      destruct p; last done. solve_elem_of+ /discriminate.
    - move=>s1 s2. rewrite !mkSet_elem_of /==> Hs1 Hstep.
      inversion_clear Hstep as [T1 T2 Hdisj Hstep'].
      inversion_clear Hstep' as [? ? ? ? Htrans _ _ Htok].
      destruct Htrans; move:Hs1 Hdisj Htok =>/=;
                                first by destruct p.
      rewrite /= /tok /=. intros. solve_elem_of +Hdisj Htok.
  Qed.

End barrier_proto.

