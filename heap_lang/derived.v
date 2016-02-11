Require Export heap_lang.lifting.
Import uPred.

(** Define some derived forms, and derived lemmas about them. *)
Notation Lam x e := (Rec "" x e).
Notation Let x e1 e2 := (App (Lam x e2) e1).
Notation Seq e1 e2 := (Let "" e1 e2).
Notation LamV x e := (RecV "" x e).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)).
Notation SeqCtx e2 := (LetCtx "" e2).

Section derived.
Context {Σ : iFunctor}.
Implicit Types P : iProp heap_lang Σ.
Implicit Types Q : val → iProp heap_lang Σ.

(** Proof rules for the sugar *)
Lemma wp_lam E x ef e v Q :
  to_val e = Some v → ▷ wp E (gsubst ef x e) Q ⊑ wp E (App (Lam x ef) e) Q.
Proof.
  intros <-%of_to_val; rewrite -wp_rec ?to_of_val //.
  by rewrite (gsubst_correct _ _ (RecV _ _ _)) subst_empty.
Qed.

Lemma wp_let E x e1 e2 v Q :
  to_val e1 = Some v → ▷ wp E (gsubst e2 x e1) Q ⊑ wp E (Let x e1 e2) Q.
Proof. apply wp_lam. Qed.

Lemma wp_seq E e1 e2 Q : wp E e1 (λ _, ▷ wp E e2 Q) ⊑ wp E (Seq e1 e2) Q.
Proof.
  rewrite -(wp_bind [LetCtx "" e2]). apply wp_mono=>v.
  by rewrite -wp_let //= ?gsubst_correct ?subst_empty ?to_of_val.
Qed.

Lemma wp_le E (n1 n2 : nat) P Q :
  (n1 ≤ n2 → P ⊑ ▷ Q (LitV $ LitBool true)) →
  (n2 < n1 → P ⊑ ▷ Q (LitV $ LitBool false)) →
  P ⊑ wp E (BinOp LeOp (Lit $ LitNat n1) (Lit $ LitNat n2)) Q.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 ≤ n2)); by eauto with omega.
Qed.

Lemma wp_lt E (n1 n2 : nat) P Q :
  (n1 < n2 → P ⊑ ▷ Q (LitV $ LitBool true)) →
  (n2 ≤ n1 → P ⊑ ▷ Q (LitV $ LitBool false)) →
  P ⊑ wp E (BinOp LtOp (Lit $ LitNat n1) (Lit $ LitNat n2)) Q.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 < n2)); by eauto with omega.
Qed.

Lemma wp_eq E (n1 n2 : nat) P Q :
  (n1 = n2 → P ⊑ ▷ Q (LitV $ LitBool true)) →
  (n1 ≠ n2 → P ⊑ ▷ Q (LitV $ LitBool false)) →
  P ⊑ wp E (BinOp EqOp (Lit $ LitNat n1) (Lit $ LitNat n2)) Q.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 = n2)); by eauto with omega.
Qed.

End derived.
