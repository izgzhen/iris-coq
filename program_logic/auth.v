Require Export algebra.auth algebra.functor.
Require Export program_logic.invariants program_logic.ghost_ownership.
Import uPred.

Section auth.
  Context {A : cmraT} `{Empty A, !CMRAIdentity A} `{!∀ a : A, Timeless a}.
  Context {Λ : language} {Σ : iFunctorG} (AuthI : gid) `{!InG Λ Σ AuthI (authRA A)}.
  Context (N : namespace) (φ : A → iPropG Λ Σ).

  Implicit Types P Q R : iPropG Λ Σ.
  Implicit Types a b : A.
  Implicit Types γ : gname.

  (* TODO: Need this to be proven somewhere. *)
  Hypothesis auth_valid :
    forall a b, (✓ Auth (Excl a) b : iPropG Λ Σ) ⊑ (∃ b', a ≡ b ⋅ b').

  Definition auth_inv (γ : gname) : iPropG Λ Σ :=
    (∃ a, own AuthI γ (● a) ★ φ a)%I.
  Definition auth_own (γ : gname) (a : A) : iPropG Λ Σ := own AuthI γ (◯ a).
  Definition auth_ctx (γ : gname) : iPropG Λ Σ := inv N (auth_inv γ).

  Lemma auth_alloc a :
    ✓a → φ a ⊑ pvs N N (∃ γ, auth_ctx γ ∧ auth_own γ a).
  Proof.
    intros Ha. rewrite -(right_id True%I (★)%I (φ _)).
    rewrite (own_alloc AuthI (Auth (Excl a) a) N) //; [].
    rewrite pvs_frame_l. apply pvs_strip_pvs.
    rewrite sep_exist_l. apply exist_elim=>γ. rewrite -(exist_intro γ).
    transitivity (▷auth_inv γ ★ auth_own γ a)%I.
    { rewrite /auth_inv -later_intro -(exist_intro a).
      rewrite [(_ ★ φ _)%I]comm -assoc. apply sep_mono; first done.
      rewrite /auth_own -own_op auth_both_op. done. }
    rewrite (inv_alloc N) /auth_ctx pvs_frame_r. apply pvs_mono.
    by rewrite always_and_sep_l'.
  Qed.

  Context {Hφ : ∀ n, Proper (dist n ==> dist n) φ}.

  Lemma auth_opened E a γ :
    (▷auth_inv γ ★ auth_own γ a) ⊑ pvs E E (∃ a', ▷φ (a ⋅ a') ★ own AuthI γ (● (a ⋅ a') ⋅ ◯ a)).
  Proof.
    rewrite /auth_inv. rewrite later_exist sep_exist_r. apply exist_elim=>b.
    rewrite later_sep [(▷own _ _ _)%I]pvs_timeless !pvs_frame_r. apply pvs_mono.
    rewrite /auth_own [(_ ★ ▷φ _)%I]comm -assoc -own_op.
    rewrite own_valid_r auth_valid !sep_exist_l /=. apply exist_elim=>a'.
    rewrite [∅ ⋅ _]left_id -(exist_intro a').
    apply (eq_rewrite b (a ⋅ a')
              (λ x, ▷φ x ★ own AuthI γ (● x ⋅ ◯ a))%I); first by solve_ne.
    { by rewrite !sep_elim_r. }
    apply sep_mono; first done.
    by rewrite sep_elim_l.
  Qed.

  Lemma auth_closing E `{!LocalUpdate Lv L} a a' γ :
    Lv a → ✓ (L a ⋅ a') →
    (▷φ (L a ⋅ a') ★ own AuthI γ (● (a ⋅ a') ⋅ ◯ a))
    ⊑ pvs E E (▷auth_inv γ ★ auth_own γ (L a)).
  Proof.
    intros HL Hv. rewrite /auth_inv /auth_own -(exist_intro (L a ⋅ a')).
    rewrite later_sep [(_ ★ ▷φ _)%I]comm -assoc.
    rewrite -pvs_frame_l. apply sep_mono; first done.
    rewrite -later_intro -own_op.
    by apply own_update, (auth_local_update_l L).
  Qed.

  (* Notice how the user has to prove that `b⋅a'` is valid at all
     step-indices. However, since A is timeless, that should not be
     a restriction.  *)
  Lemma auth_fsa {X : Type} {FSA} (FSAs : FrameShiftAssertion (A:=X) FSA)
        `{!LocalUpdate Lv L} E P (Q : X → iPropG Λ Σ) γ a :
    nclose N ⊆ E →
    (auth_ctx γ ★ auth_own γ a ★ (∀ a', ▷φ (a ⋅ a') -★
        FSA (E ∖ nclose N) (λ x, ■(Lv a ∧ ✓(L a⋅a')) ★ ▷φ (L a ⋅ a') ★ (auth_own γ (L a) -★ Q x))))
      ⊑ FSA E Q.
  Proof.
    rewrite /auth_ctx=>HN.
    rewrite -inv_fsa; last eassumption.
    apply sep_mono; first done. apply wand_intro_l.
    rewrite assoc auth_opened !pvs_frame_r !sep_exist_r.
    apply fsa_strip_pvs; first done. apply exist_elim=>a'.
    rewrite (forall_elim a'). rewrite [(▷_ ★ _)%I]comm.
    rewrite -[((_ ★ ▷_) ★ _)%I]assoc wand_elim_r fsa_frame_l.
    apply fsa_mono_pvs; first done. intros x. rewrite comm -!assoc.
    apply const_elim_sep_l=>-[HL Hv].
    rewrite assoc [(_ ★ (_ -★ _))%I]comm -assoc.
    rewrite auth_closing //; []. erewrite pvs_frame_l. apply pvs_mono.
    by rewrite assoc [(_ ★ ▷_)%I]comm -assoc wand_elim_l.
  Qed.
End auth.
