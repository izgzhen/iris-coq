From algebra Require Export upred_big_op.
From program_logic Require Export sts saved_prop.
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

  Canonical Structure sts := sts.STS trans tok.

  (* The set of states containing some particular i *)
  Definition i_states (i : gname) : set stateT :=
    mkSet (λ s, i ∈ state_I s).

  Lemma i_states_closed i :
    sts.closed (i_states i) {[ Change i ]}.
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
    sts.closed low_states {[ Send ]}.
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
(* I am too lazy to type the full module name all the time. But then
   why did we even put this into a module? Because some of the names 
   are so general.
   What we'd really like here is to import *some* of the names from
   the module into our namespaces. But Coq doesn't seem to support that...?? *)
Import barrier_proto.

(** Now we come to the Iris part of the proof. *)
Section proof.
  Context {Σ : iFunctorG} (N : namespace).
  (* TODO: Bundle HeapI and HeapG and have notation so that we can just write
     "l ↦ '0". *)
  Context (HeapI : gid) `{!HeapInG Σ HeapI} (HeapG : gname).
  Context (StsI : gid) `{!STSInG heap_lang Σ StsI sts}.
  Context (SpI : gid) `{!SavedPropInG heap_lang Σ SpI}.

  Notation iProp := (iPropG heap_lang Σ).

  Definition waiting (P : iProp) (I : gset gname) : iProp :=
    (∃ Q : gmap gname iProp, ▷(P -★ Π★{map Q} (λ _ Q, Q)) ★
                             Π★{map Q} (λ i Q, saved_prop_own SpI i Q))%I.

  Definition ress (I : gset gname) : iProp :=
    (Π★{set I} (λ i, ∃ Q, saved_prop_own SpI i Q ★ ▷Q))%I.

  Definition barrier_inv (l : loc) (P : iProp) (s : stateT) : iProp :=
    match s with
    | State Low I' => (heap_mapsto HeapI HeapG l ('0) ★ waiting P I')%I
    | State High I' => (heap_mapsto HeapI HeapG l ('1) ★ ress I')%I
    end.

  Definition barrier_ctx (γ : gname) (l : loc) (P : iProp) : iProp :=
    (heap_ctx HeapI HeapG N ★ sts_ctx StsI sts γ N (barrier_inv l P))%I.

  Definition send (l : loc) (P : iProp) : iProp :=
    (∃ γ, barrier_ctx γ l P ★ sts_ownS StsI sts γ low_states {[ Send ]})%I.

  Definition recv (l : loc) (R : iProp) : iProp :=
    (∃ γ (P Q : iProp) i, barrier_ctx γ l P ★ sts_ownS StsI sts γ (i_states i) {[ Change i ]} ★
        saved_prop_own SpI i Q ★ ▷(Q -★ R))%I.
    
  Lemma newchan_spec (P : iProp) (Q : val → iProp) :
    (∀ l, recv l P ★ send l P -★ Q (LocV l)) ⊑ wp coPset_all (newchan '()) Q.
  Proof.
  Abort.

  Lemma signal_spec l P (Q : val → iProp) :
    (send l P ★ P ★ Q '()) ⊑ wp coPset_all (signal (LocV l)) Q.
  Proof.
  Abort.

  Lemma wait_spec l P (Q : val → iProp) :
    (recv l P ★ (P -★ Q '())) ⊑ wp coPset_all (wait (LocV l)) Q.
  Proof.
  Abort.

  Lemma split_spec l P1 P2 Q :
    (recv l (P1 ★ P2) ★ (recv l P1 ★ recv l P2 -★ Q '())) ⊑ wp coPset_all Skip Q.
  Proof.
  Abort.

  Lemma recv_strengthen l P1 P2 :
    (P1 -★ P2) ⊑ (recv l P1 -★ recv l P2).
  Proof.
  Abort.

End proof.
