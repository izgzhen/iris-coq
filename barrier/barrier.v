From algebra Require Export upred_big_op.
From program_logic Require Export sts saved_prop.
From heap_lang Require Export derived heap wp_tactics notation.
Import uPred.

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

  Lemma low_states_closed : sts.closed low_states {[ Send ]}.
  Proof.
    split.
    - apply (non_empty_inhabited(State Low ∅)). by rewrite !mkSet_elem_of /=.
    - move=>[p I]. rewrite /= /tok !mkSet_elem_of /= =>HI.
      destruct p; last done. solve_elem_of.
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
  Context `{heapG Σ} (heapN : namespace).
  Context `{stsG heap_lang Σ sts}.
  Context `{savedPropG heap_lang Σ}.

  Notation iProp := (iPropG heap_lang Σ).

  Definition waiting (P : iProp) (I : gset gname) : iProp :=
    (∃ R : gname → iProp, ▷(P -★ Π★{set I} (λ i, R i)) ★
                             Π★{set I} (λ i, saved_prop_own i (R i)))%I.

  Definition ress (I : gset gname) : iProp :=
    (Π★{set I} (λ i, ∃ R, saved_prop_own i R ★ ▷R))%I.

  Local Notation state_to_val s :=
    (match s with State Low _ => 0 | State High _ => 1 end).
  Definition barrier_inv (l : loc) (P : iProp) (s : stateT) : iProp :=
    (l ↦ '(state_to_val s) ★
     match s with State Low I' => waiting P I' | State High I' => ress I' end
    )%I.

  Definition barrier_ctx (γ : gname) (l : loc) (P : iProp) : iProp :=
    (heap_ctx heapN ★ sts_ctx γ N (barrier_inv l P))%I.

  Definition send (l : loc) (P : iProp) : iProp :=
    (∃ γ, barrier_ctx γ l P ★ sts_ownS γ low_states {[ Send ]})%I.

  Definition recv (l : loc) (R : iProp) : iProp :=
    (∃ γ (P Q : iProp) i, barrier_ctx γ l P ★ sts_ownS γ (i_states i) {[ Change i ]} ★
        saved_prop_own i Q ★ ▷(Q -★ R))%I.

  Lemma newchan_spec (P : iProp) (Q : val → iProp) :
    (heap_ctx heapN ★ ∀ l, recv l P ★ send l P -★ Q (LocV l))
    ⊑ wp ⊤ (newchan '()) Q.
  Proof.
    rewrite /newchan. wp_rec. (* TODO: wp_seq. *)
    rewrite -wp_pvs. wp> eapply wp_alloc; eauto with I ndisj.
    apply forall_intro=>l. rewrite (forall_elim l). apply wand_intro_l.
    rewrite !assoc. apply pvs_wand_r.
    (* The core of this proof: Allocating the STS and the saved prop. *)
    eapply sep_elim_True_r.
    { by eapply (saved_prop_alloc _ P). }
    rewrite pvs_frame_l. apply pvs_strip_pvs. rewrite sep_exist_l.
    apply exist_elim=>i.
    transitivity (pvs ⊤ ⊤ (heap_ctx heapN ★ ▷ (barrier_inv l P (State Low {[ i ]}))  ★ saved_prop_own i P)).
    - rewrite -pvs_intro. rewrite [(_ ★ heap_ctx _)%I]comm -!assoc. apply sep_mono_r.
      rewrite {1}[saved_prop_own _ _]always_sep_dup !assoc. apply sep_mono_l.
      rewrite /barrier_inv /waiting -later_intro. apply sep_mono_r.
      rewrite -(exist_intro (const P)) /=. rewrite -[saved_prop_own _ _](left_id True%I (★)%I).
      apply sep_mono.
      + rewrite -later_intro. apply wand_intro_l. rewrite right_id.
        by rewrite big_sepS_singleton.
      + by rewrite big_sepS_singleton.
    - rewrite (sts_alloc (barrier_inv l P) ⊤ N); last by eauto. rewrite !pvs_frame_r !pvs_frame_l. 
      rewrite pvs_trans'. apply pvs_strip_pvs. rewrite sep_exist_r sep_exist_l. apply exist_elim=>γ.
      (* TODO: The record notation is rather annoying here *)
      rewrite /recv /send. rewrite -(exist_intro γ) -(exist_intro P).
      rewrite -(exist_intro P) -(exist_intro i) -(exist_intro γ).
      (* This is even more annoying than usually, since rewrite sometimes unfolds stuff... *)
      rewrite [barrier_ctx _ _ _]lock !assoc [(_ ★ locked _)%I]comm !assoc -lock.
      rewrite -always_sep_dup.
      rewrite [barrier_ctx _ _ _]lock always_and_sep_l -!assoc assoc -lock.
      rewrite -pvs_frame_l. apply sep_mono_r.
      rewrite [(saved_prop_own _ _ ★ _)%I]comm !assoc. rewrite -pvs_frame_r. apply sep_mono_l.
      rewrite -assoc [(▷ _ ★ _)%I]comm assoc -pvs_frame_r.
      eapply sep_elim_True_r; last eapply sep_mono_l.
      { rewrite -later_intro. apply wand_intro_l. by rewrite right_id. }
      rewrite (sts_own_weaken ⊤ _ _ (i_states i ∩ low_states) _ ({[ Change i ]} ∪ {[ Send ]})).
      + apply pvs_mono. rewrite sts_ownS_op; first done.
        * solve_elem_of.
        * apply i_states_closed.
        * apply low_states_closed.
      + rewrite /= /tok /=. apply elem_of_equiv=>t. rewrite elem_of_difference elem_of_union.
        rewrite !mkSet_elem_of /change_tokens.
        (* TODO: destruct t; solve_elem_of does not work. What is the best way to do on? *)
        admit.
      + apply elem_of_intersection. rewrite !mkSet_elem_of /=. solve_elem_of.
      + (* TODO: Need lemma about closenedd os intersection / union. *) admit.
  Abort.

  Lemma signal_spec l P (Q : val → iProp) :
    heapN ⊥ N → (send l P ★ P ★ Q '()) ⊑ wp ⊤ (signal (LocV l)) Q.
  Proof.
    intros Hdisj. rewrite /signal /send /barrier_ctx. rewrite sep_exist_r.
    apply exist_elim=>γ. wp_rec. (* FIXME wp_let *)
    (* I think some evars here are better than repeating *everything* *)
    eapply (sts_fsaS _ (wp_fsa _)) with (N0:=N) (γ0:=γ); simpl;
      eauto with I ndisj.
    rewrite [(_ ★ sts_ownS _ _ _)%I]comm -!assoc /wp_fsa. apply sep_mono_r.
    apply forall_intro=>-[p I]. apply wand_intro_l. rewrite -!assoc.
    apply const_elim_sep_l=>Hs. destruct p; last done.
    rewrite {1}/barrier_inv =>/={Hs}. rewrite later_sep.
    eapply wp_store; eauto with I ndisj.
    rewrite -!assoc. apply sep_mono_r. etransitivity; last eapply later_mono.
    { (* Is this really the best way to strip the later? *)
      erewrite later_sep. apply sep_mono_r. apply later_intro. }
    apply wand_intro_l. rewrite -(exist_intro (State High I)).
    rewrite -(exist_intro ∅). rewrite const_equiv /=; last first.
    { constructor; first constructor; rewrite /= /tok /=; solve_elem_of. }
    rewrite left_id -later_intro {2}/barrier_inv -!assoc. apply sep_mono_r.
    rewrite !assoc [(_ ★ P)%I]comm !assoc -2!assoc.
    apply sep_mono; last first.
    { apply wand_intro_l. eauto with I. }
    (* Now we come to the core of the proof: Updating from waiting to ress. *)
    rewrite /waiting /ress sep_exist_l. apply exist_elim=>{Q} Q.
    rewrite later_wand {1}(later_intro P) !assoc wand_elim_r.
    (* TODO: Now we need stuff about Π★{set I} *)
  Abort.

  Lemma wait_spec l P (Q : val → iProp) :
    heapN ⊥ N → (recv l P ★ (P -★ Q '())) ⊑ wp ⊤ (wait (LocV l)) Q.
  Proof.
  Abort.

  Lemma split_spec l P1 P2 Q :
    (recv l (P1 ★ P2) ★ (recv l P1 ★ recv l P2 -★ Q '())) ⊑ wp ⊤ Skip Q.
  Proof.
  Abort.

  Lemma recv_strengthen l P1 P2 :
    (P1 -★ P2) ⊑ (recv l P1 -★ recv l P2).
  Proof.
  Abort.

End proof.
