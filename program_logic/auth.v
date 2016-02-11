Require Export algebra.auth algebra.functor.
Require Export program_logic.invariants program_logic.ghost_ownership.
Import uPred ghost_ownership.

Section auth.
  Context {A : cmraT} `{Empty A, !CMRAIdentity A}.
  Context {Λ : language} {Σ : gid → iFunctor} (AuthI : gid) `{!InG Λ Σ AuthI (authRA A)}.
  (* TODO: Come up with notation for "iProp Λ (globalC Σ)". *)
  Context (N : namespace) (φ : A → iProp Λ (globalC Σ)).
  Implicit Types P Q R : iProp Λ (globalC Σ).
  Implicit Types a b : A.
  Implicit Types γ : gname.

  (* TODO: Need this to be proven somewhere. *)
  (* FIXME ✓ binds too strong, I need parenthesis here. *)
  Hypothesis auth_valid :
    forall a b, (✓(Auth (Excl a) b) : iProp Λ (globalC Σ)) ⊑ (∃ b', a ≡ b ⋅ b').

  (* FIXME how much would break if we had a global instance from ∅ to Inhabited? *)
  Local Instance auth_inhabited : Inhabited A.
  Proof. split. exact ∅. Qed.

  Definition auth_inv (γ : gname) : iProp Λ (globalC Σ) :=
    (∃ a, own AuthI γ (●a) ★ φ a)%I.
  Definition auth_own (γ : gname) (a : A) := own AuthI γ (◯a).
  Definition auth_ctx (γ : gname) := inv N (auth_inv γ).

  Lemma auth_alloc a :
    ✓a → φ a ⊑ pvs N N (∃ γ, auth_ctx γ ∧ auth_own γ a).
  Proof.
    intros Ha. rewrite -(right_id True%I (★)%I (φ _)).
    rewrite (own_alloc AuthI (Auth (Excl a) a) N) //; [].
    rewrite pvs_frame_l. apply pvs_strip_pvs.
    rewrite sep_exist_l. apply exist_elim=>γ. rewrite -(exist_intro γ).
    transitivity (▷auth_inv γ ★ auth_own γ a)%I.
    { rewrite /auth_inv -later_intro -(exist_intro a).
      rewrite (commutative _ _ (φ _)) -associative. apply sep_mono; first done.
      rewrite /auth_own -own_op auth_both_op. done. }
    rewrite (inv_alloc N) /auth_ctx pvs_frame_r. apply pvs_mono.
    by rewrite always_and_sep_l'.
  Qed.

  Context {Hφ : ∀ n, Proper (dist n ==> dist n) φ}.

  Lemma auth_opened a γ :
    (auth_inv γ ★ auth_own γ a) ⊑ (∃ a', φ (a ⋅ a') ★ own AuthI γ (● (a ⋅ a') ⋅ ◯ a)).
  Proof.
    rewrite /auth_inv. rewrite sep_exist_r. apply exist_elim=>b.
    rewrite /auth_own [(_ ★ φ _)%I]commutative -associative -own_op.
    rewrite own_valid_r auth_valid !sep_exist_l /=. apply exist_elim=>a'.
    rewrite [∅ ⋅ _]left_id -(exist_intro a').
    apply (eq_rewrite b (a ⋅ a')
              (λ x, φ x ★ own AuthI γ (● x ⋅ ◯ a))%I).
    { (* TODO this asks for automation. *)
      move=>n a1 a2 Ha. by rewrite !Ha. }
    { by rewrite !sep_elim_r. }
    apply sep_mono; first done.
    by rewrite sep_elim_l.
  Qed.

  Context (L : LocalUpdate A) `{!LocalUpdateSpec L}.
  Lemma auth_closing E a a' b γ :
    L a = Some b → ✓(b ⋅ a') →
    (▷φ (b ⋅ a') ★ own AuthI γ (● (a ⋅ a') ⋅ ◯ a))
      ⊑ pvs E E (▷auth_inv γ ★ auth_own γ b).
  Proof.
    intros HL Hv. rewrite /auth_inv /auth_own -(exist_intro (b ⋅ a')).
    rewrite later_sep [(_ ★ ▷φ _)%I]commutative -associative.
    rewrite -pvs_frame_l. apply sep_mono; first done.
    rewrite -later_intro -own_op. apply own_update.
    by apply (auth_local_update L).
  Qed.

  (* FIXME it should be enough to assume that A is all-timeless. *)
  (* Notice how the user has t prove that `L a` equals `Some b` at
     *all* step-indices, and similar that `b⋅a'` is valid at all
     step-indices. This is because the side-conditions for frame-preserving
     updates have to be shown on the meta-level. *)
  Lemma auth_pvs `{!∀ a : authRA A, Timeless a} E P (Q : A → iProp Λ (globalC Σ)) γ a :
    nclose N ⊆ E →
    (auth_ctx γ ★ auth_own γ a ★ (∀ a', ▷φ (a ⋅ a') -★
          pvs (E ∖ nclose N) (E ∖ nclose N)
            (∃ b, L a = Some b ★ ■(✓(b⋅a')) ★ ▷φ (b ⋅ a') ★ Q b)))
      ⊑ pvs E E (∃ b, auth_own γ b ★ Q b).
  Proof.
    rewrite /auth_ctx=>HN.
    rewrite -[pvs E E _]pvs_open_close; last eassumption.
    apply sep_mono; first done. apply wand_intro_l.
    rewrite [auth_own _ _]later_intro associative -later_sep.
    rewrite auth_opened later_exist sep_exist_r. apply exist_elim=>a'.
    rewrite (forall_elim a'). rewrite [(▷_ ★ _)%I]commutative later_sep.
    rewrite associative wand_elim_l pvs_frame_r. apply pvs_strip_pvs.
    rewrite sep_exist_r. apply exist_elim=>b.
    rewrite [(▷own _ _ _)%I]pvs_timeless pvs_frame_l. apply pvs_strip_pvs.
    rewrite -!associative. apply const_elim_sep_l=>HL.
    apply const_elim_sep_l=>Hv.
    rewrite associative [(_ ★ Q b)%I]commutative -associative auth_closing //; [].
    erewrite pvs_frame_l. apply pvs_mono. rewrite -(exist_intro b).
    rewrite associative [(_ ★ Q b)%I]commutative associative.
    apply sep_mono; last done. by rewrite commutative.
  Qed.
End auth.

