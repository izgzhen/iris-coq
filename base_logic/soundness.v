From iris.base_logic Require Export primitive derived.
Import uPred_entails uPred_primitive.

Section adequacy.
Context {M : ucmraT}.

(** Consistency and adequancy statements *)
Lemma soundness φ n : (Nat.iter n (λ P, |==> ▷ P) (@uPred_pure M φ))%I → φ.
Proof.
  cut (∀ x, ✓{n} x → Nat.iter n (λ P, |==> ▷ P)%I (@uPred_pure M φ) n x → φ).
  { intros help H. eapply (help ∅); eauto using ucmra_unit_validN.
    eapply H; try unseal; by eauto using ucmra_unit_validN. }
  unseal. induction n as [|n IH]=> x Hx Hupd; auto.
  destruct (Hupd (S n) ∅) as (x'&?&?); rewrite ?right_id; auto.
  eapply IH with x'; eauto using cmra_validN_S, cmra_validN_op_l.
Qed.

Corollary consistency_modal n :
  ¬ (Nat.iter n (λ P, |==> ▷ P) (False : uPred M))%I.
Proof. exact (soundness False n). Qed.

Corollary consistency : ¬ (False : uPred M)%I.
Proof. exact (consistency_modal 0). Qed.
End adequacy.
