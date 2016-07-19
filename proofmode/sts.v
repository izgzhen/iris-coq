From iris.proofmode Require Import coq_tactics pviewshifts.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export sts.
Import uPred.

Section sts.
Context `{stsG Λ Σ sts} (φ : sts.state sts → iPropG Λ Σ).
Implicit Types P Q : iPropG Λ Σ.

Lemma tac_sts_fsa {A} (fsa : FSA Λ _ A) fsaV Δ E N i γ S T Q Φ :
  IsFSA Q E fsa fsaV Φ →
  fsaV →
  envs_lookup i Δ = Some (false, sts_ownS γ S T) →
  (of_envs Δ ⊢ sts_ctx γ N φ) → nclose N ⊆ E →
  (∀ s, s ∈ S → ∃ Δ',
    envs_simple_replace i false (Esnoc Enil i (▷ φ s)) Δ = Some Δ' ∧
    (Δ' ⊢ fsa (E ∖ nclose N) (λ a, ∃ s' T',
      ■ sts.steps (s, T) (s', T') ★ ▷ φ s' ★ (sts_own γ s' T' -★ Φ a)))) →
  Δ ⊢ Q.
Proof.
  intros ????? HΔ'. rewrite (is_fsa Q) -(sts_fsaS φ fsa) //.
  rewrite // -always_and_sep_l. apply and_intro; first done.
  rewrite envs_lookup_sound //; simpl; apply sep_mono_r.
  apply forall_intro=>s; apply wand_intro_l.
  rewrite -assoc; apply pure_elim_sep_l=> Hs.
  destruct (HΔ' s) as (Δ'&?&?); clear HΔ'; auto.
  rewrite envs_simple_replace_sound' //; simpl.
  by rewrite right_id wand_elim_r.
Qed.
End sts.

Tactic Notation "iSts" constr(H) "as"
    simple_intropattern(s) simple_intropattern(Hs) :=
  match type of H with
  | string => eapply tac_sts_fsa with _ _ _ _ _ _ H _ _ _ _
  | gname => eapply tac_sts_fsa with _ _ _ _ _ _ _ H _ _ _
  | _ => fail "iSts:" H "not a string or gname"
  end;
    [let P := match goal with |- IsFSA ?P _ _ _ _ => P end in
     apply _ || fail "iSts: cannot viewshift in goal" P
    |auto with fsaV
    |iAssumptionCore || fail "iSts:" H "not found"
    |iAssumption || fail "iSts: invariant not found"
    |solve_ndisj
    |intros s Hs; eexists; split; [env_cbv; reflexivity|simpl]].
Tactic Notation "iSts" constr(H) "as" simple_intropattern(s) := iSts H as s ?.
