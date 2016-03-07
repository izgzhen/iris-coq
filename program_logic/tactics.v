From algebra Require Export upred_tactics.
From program_logic Require Export pviewshifts.
Import uPred.

Module uPred_reflection_pvs.
  Import uPred_reflection.
  Section uPred_reflection_pvs.
  
  Context {Λ : language} {Σ : iFunctor}.
  Local Notation iProp := (iProp Λ Σ).

  Lemma cancel_entails_pvs Σ' E1 E2 e1 e2 e1' e2' ns :
    cancel ns e1 = Some e1' → cancel ns e2 = Some e2' →
    eval Σ' e1' ⊑ pvs E1 E2 (eval Σ' e2' : iProp) → eval Σ' e1 ⊑ pvs E1 E2 (eval Σ' e2).
  Proof.
    intros ??. rewrite !eval_flatten.
    rewrite (flatten_cancel e1 e1' ns) // (flatten_cancel e2 e2' ns) //; csimpl.
    rewrite !fmap_app !big_sep_app. rewrite -pvs_frame_l. apply sep_mono_r.
  Qed.

  End uPred_reflection_pvs.
  
  Ltac quote_pvs :=
    match goal with
    | |- ?P1 ⊑ pvs ?E1 ?E2 ?P2 =>
      lazymatch type of (_ : Quote [] _ P1 _) with Quote _ ?Σ2 _ ?e1 =>
      lazymatch type of (_ : Quote Σ2 _ P2 _) with Quote _ ?Σ3 _ ?e2 =>
        change (eval Σ3 e1 ⊑ pvs E1 E2 (eval Σ3 e2)) end end
    end.
End uPred_reflection_pvs.

Tactic Notation "cancel_pvs" constr(Ps) :=
  uPred_reflection_pvs.quote_pvs;
  let Σ := match goal with |- uPred_reflection.eval ?Σ _ ⊑ _ => Σ end in
  let ns' := lazymatch type of (_ : uPred_reflection.QuoteArgs Σ Ps _) with
             | uPred_reflection.QuoteArgs _ _ ?ns' => ns'
             end in
  eapply uPred_reflection_pvs.cancel_entails_pvs with (ns:=ns');
    [cbv; reflexivity|cbv; reflexivity|simpl]. 

Tactic Notation "ecancel_pvs" open_constr(Ps) :=
  close_uPreds Ps ltac:(fun Qs => cancel_pvs Qs).
