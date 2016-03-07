From algebra Require Export sts upred_tactics.
From program_logic Require Export invariants ghost_ownership.
Import uPred.

(** The CMRA we need. *)
Class stsG Λ Σ (sts : stsT) := StsG {
  sts_inG :> inG Λ Σ (stsR sts);
  sts_inhabited :> Inhabited (sts.state sts);
}.
Coercion sts_inG : stsG >-> inG.
(** The Functor we need. *)
Definition stsGF (sts : stsT) : gFunctor := GFunctor (constRF (stsR sts)).
(* Show and register that they match. *)
Instance inGF_stsG sts `{inGF Λ Σ (stsGF sts)}
  `{Inhabited (sts.state sts)} : stsG Λ Σ sts.
Proof. split; try apply _. apply: inGF_inG. Qed.

Section definitions.
  Context `{i : stsG Λ Σ sts} (γ : gname).
  Definition sts_ownS (S : sts.states sts) (T : sts.tokens sts) : iPropG Λ Σ:=
    own γ (sts_frag S T).
  Definition sts_own (s : sts.state sts) (T : sts.tokens sts) : iPropG Λ Σ :=
    own γ (sts_frag_up s T).
  Definition sts_inv (φ : sts.state sts → iPropG Λ Σ) : iPropG Λ Σ :=
    (∃ s, own γ (sts_auth s ∅) ★ φ s)%I.
  Definition sts_ctx (N : namespace) (φ: sts.state sts → iPropG Λ Σ) : iPropG Λ Σ :=
    inv N (sts_inv φ).

  Global Instance sts_inv_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) sts_inv.
  Proof. solve_proper. Qed.
  Global Instance sts_inv_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) sts_inv.
  Proof. solve_proper. Qed.
  Global Instance sts_ownS_proper : Proper ((≡) ==> (≡) ==> (≡)) sts_ownS.
  Proof. solve_proper. Qed.
  Global Instance sts_own_proper s : Proper ((≡) ==> (≡)) (sts_own s).
  Proof. solve_proper. Qed.
  Global Instance sts_ctx_ne n N :
    Proper (pointwise_relation _ (dist n) ==> dist n) (sts_ctx N).
  Proof. solve_proper. Qed.
  Global Instance sts_ctx_proper N :
    Proper (pointwise_relation _ (≡) ==> (≡)) (sts_ctx N).
  Proof. solve_proper. Qed.
  Global Instance sts_ctx_always_stable N φ : AlwaysStable (sts_ctx N φ).
  Proof. apply _. Qed.
End definitions.
Typeclasses Opaque sts_own sts_ownS sts_ctx.
Instance: Params (@sts_inv) 5.
Instance: Params (@sts_ownS) 5.
Instance: Params (@sts_own) 6.
Instance: Params (@sts_ctx) 6.

Section sts.
  Context `{stsG Λ Σ sts} (φ : sts.state sts → iPropG Λ Σ).
  Implicit Types N : namespace.
  Implicit Types P Q R : iPropG Λ Σ.
  Implicit Types γ : gname.
  Implicit Types S : sts.states sts.
  Implicit Types T : sts.tokens sts.

  (* The same rule as implication does *not* hold, as could be shown using
     sts_frag_included. *)
  Lemma sts_ownS_weaken E γ S1 S2 T1 T2 :
    T2 ⊆ T1 → S1 ⊆ S2 → sts.closed S2 T2 →
    sts_ownS γ S1 T1 ⊑ (|={E}=> sts_ownS γ S2 T2).
  Proof. intros ? ? ?. by apply own_update, sts_update_frag. Qed.

  Lemma sts_own_weaken E γ s S T1 T2 :
    T2 ⊆ T1 → s ∈ S → sts.closed S T2 →
    sts_own γ s T1 ⊑ (|={E}=> sts_ownS γ S T2).
  Proof. intros ???. by apply own_update, sts_update_frag_up. Qed.

  Lemma sts_ownS_op γ S1 S2 T1 T2 :
    T1 ∩ T2 ⊆ ∅ → sts.closed S1 T1 → sts.closed S2 T2 →
    sts_ownS γ (S1 ∩ S2) (T1 ∪ T2) ≡ (sts_ownS γ S1 T1 ★ sts_ownS γ S2 T2)%I.
  Proof. intros. by rewrite /sts_ownS -own_op sts_op_frag. Qed.

  Lemma sts_alloc E N s :
    nclose N ⊆ E →
    ▷ φ s ⊑ (|={E}=> ∃ γ, sts_ctx γ N φ ∧ sts_own γ s (⊤ ∖ sts.tok s)).
  Proof.
    intros HN. eapply sep_elim_True_r.
    { apply (own_alloc (sts_auth s (⊤ ∖ sts.tok s)) E).
      apply sts_auth_valid; set_solver. }
    rewrite pvs_frame_l. apply pvs_strip_pvs.
    rewrite sep_exist_l. apply exist_elim=>γ. rewrite -(exist_intro γ).
    trans (▷ sts_inv γ φ ★ sts_own γ s (⊤ ∖ sts.tok s))%I.
    { rewrite /sts_inv -(exist_intro s) later_sep.
      ecancel [▷ φ _]%I.
      by rewrite -later_intro -own_op sts_op_auth_frag_up; last set_solver. }
    rewrite (inv_alloc N E) // /sts_ctx pvs_frame_r.
    by rewrite always_and_sep_l.
  Qed.

  Lemma sts_opened E γ S T :
    (▷ sts_inv γ φ ★ sts_ownS γ S T)
    ⊑ (|={E}=> ∃ s, ■ (s ∈ S) ★ ▷ φ s ★ own γ (sts_auth s T)).
  Proof.
    rewrite /sts_inv later_exist sep_exist_r. apply exist_elim=>s.
    rewrite later_sep pvs_timeless !pvs_frame_r. apply pvs_mono.
    rewrite -(exist_intro s). ecancel [▷ φ _]%I.
    rewrite -own_op own_valid_l discrete_valid.
    apply const_elim_sep_l=> Hvalid.
    assert (s ∈ S) by eauto using sts_auth_frag_valid_inv.
    rewrite const_equiv // left_id sts_op_auth_frag //.
    by assert (✓ sts_frag S T) as [??] by eauto using cmra_valid_op_r.
  Qed.

  Lemma sts_closing E γ s T s' T' :
    sts.steps (s, T) (s', T') →
    (▷ φ s' ★ own γ (sts_auth s T)) ⊑ (|={E}=> ▷ sts_inv γ φ ★ sts_own γ s' T').
  Proof.
    intros Hstep. rewrite /sts_inv -(exist_intro s') later_sep.
    (* TODO it would be really nice to use cancel here *)
    rewrite [(_ ★ ▷ φ _)%I]comm -assoc.
    rewrite -pvs_frame_l. apply sep_mono_r. rewrite -later_intro.
    rewrite own_valid_l discrete_valid. apply const_elim_sep_l=>Hval.
    trans (|={E}=> own γ (sts_auth s' T'))%I.
    { by apply own_update, sts_update_auth. }
    by rewrite -own_op sts_op_auth_frag_up.
  Qed.

  Context {V} (fsa : FSA Λ (globalF Σ) V) `{!FrameShiftAssertion fsaV fsa}.

  Lemma sts_fsaS E N P (Ψ : V → iPropG Λ Σ) γ S T :
    fsaV → nclose N ⊆ E →
    P ⊑ sts_ctx γ N φ →
    P ⊑ (sts_ownS γ S T ★ ∀ s,
          ■ (s ∈ S) ★ ▷ φ s -★
          fsa (E ∖ nclose N) (λ x, ∃ s' T',
            ■ sts.steps (s, T) (s', T') ★ ▷ φ s' ★
            (sts_own γ s' T' -★ Ψ x))) →
    P ⊑ fsa E Ψ.
  Proof.
    rewrite /sts_ctx=>? HN Hinv Hinner.
    eapply (inv_fsa fsa); eauto. rewrite Hinner=>{Hinner Hinv P HN}.
    apply wand_intro_l. rewrite assoc.
    rewrite (sts_opened (E ∖ N)) !pvs_frame_r !sep_exist_r.
    apply (fsa_strip_pvs fsa). apply exist_elim=>s.
    rewrite (forall_elim s). rewrite [(▷_ ★ _)%I]comm.
    eapply wand_apply_r; first (by eapply (wand_frame_l (own γ _))); last first.
    { rewrite assoc [(_ ★ own _ _)%I]comm -assoc. done. }
    rewrite fsa_frame_l.
    apply (fsa_mono_pvs fsa)=> x.
    rewrite sep_exist_l; apply exist_elim=> s'.
    rewrite sep_exist_l; apply exist_elim=>T'.
    rewrite comm -!assoc. apply const_elim_sep_l=>-Hstep.
    rewrite assoc [(_ ★ (_ -★ _))%I]comm -assoc.
    rewrite (sts_closing (E ∖ N)) //; [].
    rewrite pvs_frame_l. apply pvs_mono.
    by rewrite assoc [(_ ★ ▷_)%I]comm -assoc wand_elim_l.
  Qed.

  Lemma sts_fsa E N P (Ψ : V → iPropG Λ Σ) γ s0 T :
    fsaV → nclose N ⊆ E →
    P ⊑ sts_ctx γ N φ →
    P ⊑ (sts_own γ s0 T ★ ∀ s,
          ■ (s ∈ sts.up s0 T) ★ ▷ φ s -★
          fsa (E ∖ nclose N) (λ x, ∃ s' T',
            ■ (sts.steps (s, T) (s', T')) ★ ▷ φ s' ★
            (sts_own γ s' T' -★ Ψ x))) →
    P ⊑ fsa E Ψ.
  Proof. by apply sts_fsaS. Qed.
End sts.
