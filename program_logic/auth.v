From algebra Require Export auth upred_tactics.
From program_logic Require Export invariants ghost_ownership.
Import uPred.

(* The CMRA we need. *)
Class authG Λ Σ (A : cmraT) `{Empty A} := AuthG {
  auth_inG :> inG Λ Σ (authR A);
  auth_identity :> CMRAUnit A;
  auth_timeless :> CMRADiscrete A;
}.
(* The Functor we need. *)
Definition authGF (A : cmraT) : gFunctor := GFunctor (constRF (authR A)).
(* Show and register that they match. *)
Instance authGF_inGF (A : cmraT) `{inGF Λ Σ (authGF A)}
  `{CMRAUnit A, CMRADiscrete A} : authG Λ Σ A.
Proof. split; try apply _. apply: inGF_inG. Qed.

Section definitions.
  Context `{authG Λ Σ A} (γ : gname).
  Definition auth_own  (a : A) : iPropG Λ Σ :=
    own γ (◯ a).
  Definition auth_inv (φ : A → iPropG Λ Σ) : iPropG Λ Σ :=
    (∃ a, own γ (● a) ★ φ a)%I.
  Definition auth_ctx (N : namespace) (φ : A → iPropG Λ Σ) : iPropG Λ Σ :=
    inv N (auth_inv φ).

  Global Instance auth_own_ne n : Proper (dist n ==> dist n) auth_own.
  Proof. solve_proper. Qed.
  Global Instance auth_own_proper : Proper ((≡) ==> (≡)) auth_own.
  Proof. solve_proper. Qed.
  Global Instance auth_own_timeless a : TimelessP (auth_own a).
  Proof. apply _. Qed.
  Global Instance auth_ctx_always_stable N φ : AlwaysStable (auth_ctx N φ).
  Proof. apply _. Qed.
End definitions.

Typeclasses Opaque auth_own auth_ctx.
Instance: Params (@auth_inv) 6.
Instance: Params (@auth_own) 6.
Instance: Params (@auth_ctx) 7.

Section auth.
  Context `{AuthI : authG Λ Σ A}.
  Context (φ : A → iPropG Λ Σ) {φ_proper : Proper ((≡) ==> (≡)) φ}.
  Implicit Types N : namespace.
  Implicit Types P Q R : iPropG Λ Σ.
  Implicit Types a b : A.
  Implicit Types γ : gname.

  Lemma auth_own_op γ a b :
    auth_own γ (a ⋅ b) ≡ (auth_own γ a ★ auth_own γ b)%I.
  Proof. by rewrite /auth_own -own_op auth_frag_op. Qed.
  Lemma auth_own_valid γ a : auth_own γ a ⊑ ✓ a.
  Proof. by rewrite /auth_own own_valid auth_validI. Qed.

  Lemma auth_alloc N E a :
    ✓ a → nclose N ⊆ E →
    ▷ φ a ⊑ (|={E}=> ∃ γ, auth_ctx γ N φ ∧ auth_own γ a).
  Proof.
    intros Ha HN. eapply sep_elim_True_r.
    { by eapply (own_alloc (Auth (Excl a) a) E). }
    rewrite pvs_frame_l. apply pvs_strip_pvs.
    rewrite sep_exist_l. apply exist_elim=>γ. rewrite -(exist_intro γ).
    trans (▷ auth_inv γ φ ★ auth_own γ a)%I.
    { rewrite /auth_inv -(exist_intro a) later_sep.
      ecancel [▷ φ _]%I.
      by rewrite -later_intro -own_op auth_both_op. }
    rewrite (inv_alloc N E) // /auth_ctx pvs_frame_r. apply pvs_mono.
    by rewrite always_and_sep_l.
  Qed.

  Lemma auth_empty γ E : True ⊑ |={E}=> auth_own γ ∅.
  Proof. by rewrite -own_empty. Qed.

  Lemma auth_opened E γ a :
    (▷ auth_inv γ φ ★ auth_own γ a)
    ⊑ (|={E}=> ∃ a', ✓ (a ⋅ a') ★ ▷ φ (a ⋅ a') ★ own γ (● (a ⋅ a') ⋅ ◯ a)).
  Proof.
    rewrite /auth_inv. rewrite later_exist sep_exist_r. apply exist_elim=>b.
    rewrite later_sep [(▷ own _ _)%I]pvs_timeless !pvs_frame_r. apply pvs_mono.
    rewrite own_valid_l discrete_valid -!assoc. apply const_elim_sep_l=>Hv.
    rewrite [(▷φ _ ★ _)%I]comm assoc -own_op.
    rewrite own_valid_r auth_validI /= and_elim_l sep_exist_l sep_exist_r /=.
    apply exist_elim=>a'.
    rewrite left_id -(exist_intro a').
    apply (eq_rewrite b (a ⋅ a') (λ x, ✓ x ★ ▷ φ x ★ own γ (● x ⋅ ◯ a))%I).
    { by move=>n x y /timeless_iff ->. }
    { by eauto with I. }
    rewrite -valid_intro; last by apply Hv.
    rewrite left_id comm. auto with I.
  Qed.

  Lemma auth_closing `{!LocalUpdate Lv L} E γ a a' :
    Lv a → ✓ (L a ⋅ a') →
    (▷ φ (L a ⋅ a') ★ own γ (● (a ⋅ a') ⋅ ◯ a))
    ⊑ (|={E}=> ▷ auth_inv γ φ ★ auth_own γ (L a)).
  Proof.
    intros HL Hv. rewrite /auth_inv -(exist_intro (L a ⋅ a')).
    (* TODO it would be really nice to use cancel here *)
    rewrite later_sep [(_ ★ ▷φ _)%I]comm -assoc.
    rewrite -pvs_frame_l. apply sep_mono_r.
    rewrite -later_intro -own_op.
    by apply own_update, (auth_local_update_l L).
  Qed.

  Context {V} (fsa : FSA Λ (globalF Σ) V) `{!FrameShiftAssertion fsaV fsa}.

  Lemma auth_fsa E N P (Ψ : V → iPropG Λ Σ) γ a :
    fsaV →
    nclose N ⊆ E →
    P ⊑ auth_ctx γ N φ →
    P ⊑ (▷ auth_own γ a ★ ∀ a',
          ■ ✓ (a ⋅ a') ★ ▷ φ (a ⋅ a') -★
          fsa (E ∖ nclose N) (λ x, ∃ L Lv (Hup : LocalUpdate Lv L),
            ■ (Lv a ∧ ✓ (L a ⋅ a')) ★ ▷ φ (L a ⋅ a') ★
            (auth_own γ (L a) -★ Ψ x))) →
    P ⊑ fsa E Ψ.
  Proof.
    rewrite /auth_ctx=>? HN Hinv Hinner.
    eapply (inv_fsa fsa); eauto. rewrite Hinner=>{Hinner Hinv P HN}.
    apply wand_intro_l. rewrite assoc.
    rewrite (pvs_timeless (E ∖ N)) pvs_frame_l pvs_frame_r.
    apply (fsa_strip_pvs fsa).
    rewrite (auth_opened (E ∖ N)) !pvs_frame_r !sep_exist_r.
    apply (fsa_strip_pvs fsa). apply exist_elim=>a'.
    rewrite (forall_elim a'). rewrite [(▷_ ★ _)%I]comm.
    eapply wand_apply_r; first (by eapply (wand_frame_l (own γ _))); last first.
    { rewrite assoc [(_ ★ own _ _)%I]comm -assoc discrete_valid.  done. }
    rewrite fsa_frame_l.
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
  Lemma auth_fsa' L `{!LocalUpdate Lv L} E N P (Ψ : V → iPropG Λ Σ) γ a :
    fsaV →
    nclose N ⊆ E →
    P ⊑ auth_ctx γ N φ →
    P ⊑ (▷ auth_own γ a ★ (∀ a',
          ■ ✓ (a ⋅ a') ★ ▷ φ (a ⋅ a') -★
          fsa (E ∖ nclose N) (λ x,
            ■ (Lv a ∧ ✓ (L a ⋅ a')) ★ ▷ φ (L a ⋅ a') ★
            (auth_own γ (L a) -★ Ψ x)))) →
    P ⊑ fsa E Ψ.
  Proof.
    intros ??? HP. eapply auth_fsa with N γ a; eauto.
    rewrite HP; apply sep_mono_r, forall_mono=> a'.
    apply wand_mono; first done. apply (fsa_mono fsa)=> b.
    rewrite -(exist_intro L). by repeat erewrite <-exist_intro by apply _.
  Qed.
End auth.
