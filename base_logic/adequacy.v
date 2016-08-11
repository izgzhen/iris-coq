From iris.base_logic Require Export upred.

Lemma adequacy {M : ucmraT} φ n :
  (True ⊢ Nat.iter n (λ P : uPred M, |=r=> ▷ P) (■ φ)) → φ.
Proof.
  cut (∀ x, ✓{n} x → Nat.iter n (λ P : uPred M, |=r=> ▷ P)%I (■ φ)%I n x → φ).
  { intros help H. eapply (help ∅); eauto using ucmra_unit_validN.
    eapply H; try uPred.unseal; by eauto using ucmra_unit_validN. }
  uPred.unseal. induction n as [|n IH]=> x Hx Hvs; auto.
  destruct (Hvs (S n) ∅) as (x'&?&?); rewrite ?right_id; auto.
  eapply IH with x'; eauto using cmra_validN_S, cmra_validN_op_l.
Qed.

Theorem soundness {M : ucmraT} : ¬ ((True : uPred M) ⊢ False).
Proof. exact (adequacy False 0). Qed.