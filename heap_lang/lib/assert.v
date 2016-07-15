From iris.heap_lang Require Export derived.
From iris.heap_lang Require Import wp_tactics substitution notation.

Definition Assert (e : expr) : expr :=
  if: e then #() else #0 #0. (* #0 #0 is unsafe *)

Instance closed_assert X e : Closed X e → Closed X (Assert e) := _.
Instance do_subst_assert x es e er :
  Subst x es e er → Subst x es (Assert e) (Assert er).
Proof. intros; red. by rewrite /Assert /subst -/subst; f_equal/=. Qed.
Typeclasses Opaque Assert.

Lemma wp_assert {Σ} (Φ : val → iProp heap_lang Σ) :
  ▷ Φ #() ⊢ WP Assert #true {{ Φ }}.
Proof. by rewrite -wp_if_true -wp_value. Qed.

Lemma wp_assert' {Σ} (Φ : val → iProp heap_lang Σ) e :
  WP e {{ v, v = #true ∧ ▷ Φ #() }} ⊢ WP Assert e {{ Φ }}.
Proof.
  rewrite /Assert. wp_focus e; apply wp_mono=>v.
  apply uPred.pure_elim_l=>->. apply wp_assert.
Qed.
