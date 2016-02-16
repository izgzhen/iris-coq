From algebra Require Export sts.
From algebra Require Import dra.
From program_logic Require Export invariants ghost_ownership.
Import uPred.

Local Arguments valid _ _ !_ /.
Local Arguments op _ _ !_ !_ /.
Local Arguments unit _ _ !_ /.

Module sts.
(** This module is *not* meant to be imported. Instead, just use "sts.ctx" etc.
    like you would use "auth_ctx" etc. *)
Export algebra.sts.sts.

Class InG Λ Σ (i : gid) (sts : stsT) := {
  inG :> ghost_ownership.InG Λ Σ i (sts.RA sts);
  inh :> Inhabited (state sts);
}.

Section definitions.
  Context {Λ Σ} (i : gid) (sts : stsT) `{!InG Λ Σ i sts} (γ : gname).
  Definition inv  (φ : state sts → iPropG Λ Σ) : iPropG Λ Σ :=
    (∃ s, own i γ (auth sts s ∅) ★ φ s)%I.
  Definition in_states (S : set (state sts)) (T: set (token sts)) : iPropG Λ Σ:=
    own i γ (frag sts S T)%I.
  Definition in_state (s : state sts) (T: set (token sts)) : iPropG Λ Σ :=
    in_states (up sts s T) T.
  Definition ctx (N : namespace) (φ : state sts → iPropG Λ Σ) : iPropG Λ Σ :=
    invariants.inv N (inv φ).
End definitions.
Instance: Params (@inv) 6.
Instance: Params (@in_states) 6.
Instance: Params (@in_state) 6.
Instance: Params (@ctx) 7.

Section sts.
  Context {Λ Σ} (i : gid) (sts : stsT) `{!InG Λ Σ StsI sts}.
  Context (φ : state sts → iPropG Λ Σ).
  Implicit Types N : namespace.
  Implicit Types P Q R : iPropG Λ Σ.
  Implicit Types γ : gname.

  (* The same rule as implication does *not* hold, as could be shown using
     sts_frag_included. *)
  Lemma in_states_weaken E γ S1 S2 T :
    S1 ⊆ S2 → closed sts S2 T →
    in_states StsI sts γ S1 T ⊑ pvs E E (in_states StsI sts γ S2 T).
  Proof.
    rewrite /in_states=>Hs Hcl. apply own_update, sts_update_frag; done.
  Qed.

  Lemma in_state_states E γ s S T :
    s ∈ S → closed sts S T →
    in_state StsI sts γ s T ⊑ pvs E E (in_states StsI sts γ S T).
  Proof.
    move=>Hs Hcl. apply in_states_weaken; last done.
    move=>s' Hup. eapply closed_steps in Hcl;last (hnf in Hup; eexact Hup);done.
  Qed.

  Lemma alloc N s :
    φ s ⊑ pvs N N (∃ γ, ctx StsI sts γ N φ ∧
                        in_state StsI sts γ s (set_all ∖ sts.(tok) s)).
  Proof.
    eapply sep_elim_True_r.
    { eapply (own_alloc StsI (auth sts s (set_all ∖ sts.(tok) s)) N).
      apply discrete_valid=>/=. solve_elem_of. }
    rewrite pvs_frame_l. apply pvs_strip_pvs.
    rewrite sep_exist_l. apply exist_elim=>γ. rewrite -(exist_intro γ).
    transitivity (▷ inv StsI sts γ φ ★
                    in_state StsI sts γ s (set_all ∖ sts.(tok) s))%I.
    { rewrite /inv -later_intro -(exist_intro s).
      rewrite [(_ ★ φ _)%I]comm -assoc. apply sep_mono; first done.
      rewrite -own_op. apply equiv_spec, own_proper.
      split; first split; simpl.
      - intros; solve_elem_of+.
      - intros _. split_ands; first by solve_elem_of+.
        + apply closed_up. solve_elem_of+.
        + constructor; last solve_elem_of+. apply sts.elem_of_up. 
      - intros _. constructor. solve_elem_of+. }
    rewrite (inv_alloc N) /ctx pvs_frame_r. apply pvs_mono.
    by rewrite always_and_sep_l.
  Qed.

  Lemma opened E γ S T :
    (▷ inv StsI sts γ φ ★ in_states StsI sts γ S T)
      ⊑ pvs E E (∃ s, ■ (s ∈ S) ★ ▷ φ s ★ own StsI γ (auth sts s T)).
  Proof.
    rewrite /inv /in_states later_exist sep_exist_r. apply exist_elim=>s.
    rewrite later_sep pvs_timeless !pvs_frame_r. apply pvs_mono.
    rewrite -(exist_intro s).
    rewrite [(_ ★ ▷φ _)%I]comm -!assoc -own_op -[(▷φ _ ★ _)%I]comm.
    rewrite own_valid_l discrete_validI.
    rewrite -!assoc. apply const_elim_sep_l=>-[_ [Hcl Hdisj]].
    simpl in Hdisj, Hcl. inversion_clear Hdisj. rewrite const_equiv // left_id.
    rewrite comm. apply sep_mono; first done.
    apply equiv_spec, own_proper. split; first split; simpl.
    - intros Hdisj. split_ands; first by solve_elem_of+.
      + done.
      + constructor; [done | solve_elem_of-].
    - intros _. by eapply closed_disjoint.
    - intros _. constructor. solve_elem_of+.
  Qed.

  Lemma closing E γ s T s' T' :
    step sts (s, T) (s', T') →
    (▷ φ s' ★ own StsI γ (auth sts s T))
    ⊑ pvs E E (▷ inv StsI sts γ φ ★ in_state StsI sts γ s' T').
  Proof.
    intros Hstep. rewrite /inv /in_states -(exist_intro s').
    rewrite later_sep [(_ ★ ▷φ _)%I]comm -assoc.
    rewrite -pvs_frame_l. apply sep_mono; first done.
    rewrite -later_intro.
    rewrite own_valid_l discrete_validI. apply const_elim_sep_l=>Hval.
    simpl in Hval. transitivity (pvs E E (own StsI γ (auth sts s' T'))).
    { by apply own_update, sts.update_auth. }
    apply pvs_mono. rewrite -own_op. apply equiv_spec, own_proper.
    split; first split; simpl.
    - intros _.
      set Tf := set_all ∖ sts.(tok) s ∖ T.
      assert (closed sts (up sts s Tf) Tf).
      { apply closed_up. rewrite /Tf. solve_elem_of+. }
      eapply step_closed; [done..| |].
      + apply elem_of_up.
      + rewrite /Tf. solve_elem_of+.
    - intros ?. split_ands; first by solve_elem_of+.
      + apply closed_up. done.
      + constructor; last solve_elem_of+. apply elem_of_up.
    - intros _. constructor. solve_elem_of+.
  Qed.

  Context {V} (fsa : FSA Λ (globalF Σ) V) `{!FrameShiftAssertion fsaV fsa}.

  Lemma states_fsa E N P (Q : V → iPropG Λ Σ) γ S T :
    fsaV → nclose N ⊆ E →
    P ⊑ ctx StsI sts γ N φ →
    P ⊑ (in_states StsI sts γ S T ★ ∀ s,
          ■ (s ∈ S) ★ ▷ φ s -★
          fsa (E ∖ nclose N) (λ x, ∃ s' T',
            ■ (step sts (s, T) (s', T')) ★ ▷ φ s' ★
            (in_state StsI sts γ s' T' -★ Q x))) →
    P ⊑ fsa E Q.
  Proof.
    rewrite /ctx=>? HN Hinv Hinner.
    eapply (inv_fsa fsa); eauto. rewrite Hinner=>{Hinner Hinv P HN}.
    apply wand_intro_l. rewrite assoc.
    rewrite (opened (E ∖ N)) !pvs_frame_r !sep_exist_r.
    apply (fsa_strip_pvs fsa). apply exist_elim=>s.
    rewrite (forall_elim s). rewrite [(▷_ ★ _)%I]comm.
    (* Getting this wand eliminated is really annoying. *)
    rewrite [(■_ ★ _)%I]comm -!assoc [(▷φ _ ★ _ ★ _)%I]assoc [(▷φ _ ★ _)%I]comm.
    rewrite wand_elim_r fsa_frame_l.
    apply (fsa_mono_pvs fsa)=> x.
    rewrite sep_exist_l; apply exist_elim=> s'.
    rewrite sep_exist_l; apply exist_elim=>T'.
    rewrite comm -!assoc. apply const_elim_sep_l=>-Hstep.
    rewrite assoc [(_ ★ (_ -★ _))%I]comm -assoc.
    rewrite (closing (E ∖ N)) //; [].
    rewrite pvs_frame_l. apply pvs_mono.
    by rewrite assoc [(_ ★ ▷_)%I]comm -assoc wand_elim_l.
  Qed.

  Lemma state_fsa E N P (Q : V → iPropG Λ Σ) γ s0 T :
    fsaV → nclose N ⊆ E →
    P ⊑ ctx StsI sts γ N φ →
    P ⊑ (in_state StsI sts γ s0 T ★ ∀ s,
          ■ (s ∈ up sts s0 T) ★ ▷ φ s -★
          fsa (E ∖ nclose N) (λ x, ∃ s' T',
            ■ (step sts (s, T) (s', T')) ★ ▷ φ s' ★
            (in_state StsI sts γ s' T' -★ Q x))) →
    P ⊑ fsa E Q.
  Proof.
    rewrite {1}/state. apply states_fsa.
  Qed.

End sts.

End sts.
