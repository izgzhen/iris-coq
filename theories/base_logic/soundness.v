From iris.base_logic Require Export base_logic.
Set Default Proof Using "Type".
Import uPred.

Section adequacy.
Context {M : ucmraT}.

(** Consistency and adequancy statements *)
Lemma soundness φ n :
  bi_valid (PROP:=uPredI M) (Nat.iter n (λ P, |==> ▷ P) (⌜ φ ⌝))%I → φ.
Proof.
  cut (∀ x, ✓{n} x → Nat.iter n (λ P, |==> ▷ P)%I (@uPred_pure M φ) n x → φ).
  { intros help H. eapply (help ∅); eauto using ucmra_unit_validN.
    eapply H; first by eauto using ucmra_unit_validN.
    rewrite /bi_emp /= /uPred_emp. by unseal. }
  unseal. induction n as [|n IH]=> x Hx Hupd; auto.
  destruct (Hupd (S n) ε) as (x'&?&?); rewrite ?right_id; auto.
  eapply IH with x'; eauto using cmra_validN_S, cmra_validN_op_l.
Qed.

Corollary consistency_modal n :
  ¬bi_valid (PROP:=uPredI M) (Nat.iter n (λ P, |==> ▷ P) (False : uPred M))%I.
Proof. exact (soundness False n). Qed.

Corollary consistency : ¬bi_valid (PROP:=uPredI M) False.
Proof. exact (consistency_modal 0). Qed.
End adequacy.
