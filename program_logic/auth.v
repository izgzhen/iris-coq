From algebra Require Export auth.
From program_logic Require Export invariants ghost_ownership.
Import uPred.

Class AuthInG Λ Σ (i : gid) (A : cmraT) `{Empty A} := {
  auth_inG :> InG Λ Σ i (authRA A);
  auth_identity :> CMRAIdentity A;
  auth_timeless (a : A) :> Timeless a;
}.

(* TODO: Once we switched to RAs, it is no longer necessary to remember that a is
   constantly valid. *)
Section definitions.
  Context {Λ Σ A} (i : gid) `{AuthInG Λ Σ i A} (γ : gname).
  Definition auth_inv (φ : A → iPropG Λ Σ) : iPropG Λ Σ :=
    (∃ a, (■ ✓ a ∧ own i γ (● a)) ★ φ a)%I.
  Definition auth_own (a : A) : iPropG Λ Σ := own i γ (◯ a).
  Definition auth_ctx (N : namespace) (φ : A → iPropG Λ Σ) : iPropG Λ Σ :=
    inv N (auth_inv φ).
End definitions.
Instance: Params (@auth_inv) 7.
Instance: Params (@auth_own) 7.
Instance: Params (@auth_ctx) 8.

Section auth.
  Context `{AuthInG Λ Σ AuthI A}.
  Context (φ : A → iPropG Λ Σ) {φ_proper : Proper ((≡) ==> (≡)) φ}.
  Implicit Types N : namespace.
  Implicit Types P Q R : iPropG Λ Σ.
  Implicit Types a b : A.
  Implicit Types γ : gname.

  Global Instance auth_own_ne n γ :
    Proper (dist n ==> dist n) (auth_own AuthI γ).
  Proof. by rewrite /auth_own=> a b ->. Qed.
  Global Instance auth_own_proper γ : Proper ((≡) ==> (≡)) (auth_own AuthI γ).
  Proof. by rewrite /auth_own=> a b ->. Qed.
  Lemma auto_own_op γ a b :
    auth_own AuthI γ (a ⋅ b) ≡ (auth_own AuthI γ a ★ auth_own AuthI γ b)%I.
  Proof. by rewrite /auth_own -own_op auth_frag_op. Qed.
  Lemma auto_own_valid γ a : auth_own AuthI γ a ⊑ ✓ a.
  Proof. by rewrite /auth_own own_valid auth_validI. Qed.

  Lemma auth_alloc N a :
    ✓ a → φ a ⊑ pvs N N (∃ γ, auth_ctx AuthI γ N φ ∧ auth_own AuthI γ a).
  Proof.
    intros Ha. eapply sep_elim_True_r.
    { by eapply (own_alloc AuthI (Auth (Excl a) a) N). }
    rewrite pvs_frame_l. apply pvs_strip_pvs.
    rewrite sep_exist_l. apply exist_elim=>γ. rewrite -(exist_intro γ).
    transitivity (▷ auth_inv AuthI γ φ ★ auth_own AuthI γ a)%I.
    { rewrite /auth_inv -later_intro -(exist_intro a).
      rewrite const_equiv // left_id.
      rewrite [(_ ★ φ _)%I]comm -assoc. apply sep_mono; first done.
      rewrite /auth_own -own_op auth_both_op. done. }
    rewrite (inv_alloc N) /auth_ctx pvs_frame_r. apply pvs_mono.
    by rewrite always_and_sep_l.
  Qed.

  Lemma auth_empty E γ : True ⊑ pvs E E (auth_own AuthI γ ∅).
  Proof. by rewrite own_update_empty /auth_own. Qed.

  Lemma auth_opened E γ a :
    (▷ auth_inv AuthI γ φ ★ auth_own AuthI γ a)
    ⊑ pvs E E (∃ a', ■ ✓ (a ⋅ a') ★ ▷ φ (a ⋅ a') ★ own AuthI γ (● (a ⋅ a') ⋅ ◯ a)).
  Proof.
    rewrite /auth_inv. rewrite later_exist sep_exist_r. apply exist_elim=>b.
    rewrite later_sep [(▷(_ ∧ _))%I]pvs_timeless !pvs_frame_r. apply pvs_mono.
    rewrite always_and_sep_l -!assoc. apply const_elim_sep_l=>Hv.
    rewrite /auth_own [(▷φ _ ★ _)%I]comm assoc -own_op.
    rewrite own_valid_r auth_validI /= and_elim_l sep_exist_l sep_exist_r /=.
    apply exist_elim=>a'.
    rewrite left_id -(exist_intro a').
    apply (eq_rewrite b (a ⋅ a') (λ x, ■✓x ★ ▷φ x ★ own AuthI γ (● x ⋅ ◯ a))%I).
    { by move=>n ? ? /timeless_iff ->. }
    { by eauto with I. }
    rewrite const_equiv // left_id comm.
    apply sep_mono; first done.
    by rewrite sep_elim_l.
  Qed.

  Lemma auth_closing `{!LocalUpdate Lv L} E γ a a' :
    Lv a → ✓ (L a ⋅ a') →
    (▷ φ (L a ⋅ a') ★ own AuthI γ (● (a ⋅ a') ⋅ ◯ a))
    ⊑ pvs E E (▷ auth_inv AuthI γ φ ★ auth_own AuthI γ (L a)).
  Proof.
    intros HL Hv. rewrite /auth_inv /auth_own -(exist_intro (L a ⋅ a')).
    rewrite later_sep [(_ ★ ▷φ _)%I]comm -assoc.
    rewrite -pvs_frame_l. apply sep_mono; first done.
    rewrite const_equiv // left_id -later_intro -own_op.
    by apply own_update, (auth_local_update_l L).
  Qed.

  Context {V} (fsa : FSA Λ (globalF Σ) V) `{!FrameShiftAssertion fsaV fsa}.

  (* Notice how the user has to prove that `b⋅a'` is valid at all
     step-indices. However, since A is timeless, that should not be
     a restriction. *)
  Lemma auth_fsa E N P (Q : V → iPropG Λ Σ) γ a :
    fsaV →
    nclose N ⊆ E →
    P ⊑ auth_ctx AuthI γ N φ →
    P ⊑ (▷ auth_own AuthI γ a ★ ∀ a',
          ■ ✓ (a ⋅ a') ★ ▷ φ (a ⋅ a') -★
          fsa (E ∖ nclose N) (λ x, ∃ L Lv (Hup : LocalUpdate Lv L),
            ■ (Lv a ∧ ✓ (L a ⋅ a')) ★ ▷ φ (L a ⋅ a') ★
            (auth_own AuthI γ (L a) -★ Q x))) →
    P ⊑ fsa E Q.
  Proof.
    rewrite /auth_ctx=>? HN Hinv Hinner.
    eapply (inv_fsa fsa); eauto. rewrite Hinner=>{Hinner Hinv P HN}.
    apply wand_intro_l. rewrite assoc.
    rewrite (pvs_timeless (E ∖ N)) pvs_frame_l pvs_frame_r.
    apply (fsa_strip_pvs fsa).
    rewrite (auth_opened (E ∖ N)) !pvs_frame_r !sep_exist_r.
    apply (fsa_strip_pvs fsa). apply exist_elim=>a'.
    rewrite (forall_elim a'). rewrite [(▷_ ★ _)%I]comm.
    (* Getting this wand eliminated is really annoying. *)
    rewrite [(■_ ★ _)%I]comm -!assoc [(▷φ _ ★ _ ★ _)%I]assoc [(▷φ _ ★ _)%I]comm.
    rewrite wand_elim_r fsa_frame_l.
    apply (fsa_mono_pvs fsa)=> x.
    rewrite sep_exist_l; apply exist_elim=> L.
    rewrite sep_exist_l; apply exist_elim=> Lv.
    rewrite sep_exist_l; apply exist_elim=> ?.
    rewrite comm -!assoc. apply const_elim_sep_l=>-[HL Hv].
    rewrite assoc [(_ ★ (_ -★ _))%I]comm -assoc.
    rewrite (auth_closing (E ∖ N)) //; [].
    rewrite pvs_frame_l. apply pvs_mono.
    by rewrite assoc [(_ ★ ▷_)%I]comm -assoc wand_elim_l.
  Qed.
  Lemma auth_fsa' L `{!LocalUpdate Lv L} E N P (Q: V → iPropG Λ Σ) γ a :
    fsaV →
    nclose N ⊆ E →
    P ⊑ auth_ctx AuthI γ N φ →
    P ⊑ (▷ auth_own AuthI γ a ★ (∀ a',
          ■ ✓ (a ⋅ a') ★ ▷ φ (a ⋅ a') -★
          fsa (E ∖ nclose N) (λ x,
            ■ (Lv a ∧ ✓ (L a ⋅ a')) ★ ▷ φ (L a ⋅ a') ★
            (auth_own AuthI γ (L a) -★ Q x)))) →
    P ⊑ fsa E Q.
  Proof.
    intros ??? HP. eapply auth_fsa with N γ a; eauto.
    rewrite HP; apply sep_mono; first done; apply forall_mono=> a'.
    apply wand_mono; first done. apply (fsa_mono fsa)=> b.
    rewrite -(exist_intro L). by repeat erewrite <-exist_intro by apply _.
  Qed.
End auth.
