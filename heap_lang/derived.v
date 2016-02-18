From heap_lang Require Export lifting.
Import uPred.

(** Define some derived forms, and derived lemmas about them. *)
Notation Lam x e := (Rec "" x e).
Notation Let x e1 e2 := (App (Lam x e2) e1).
Notation Seq e1 e2 := (Let "" e1 e2).
Notation LamV x e := (RecV "" x e).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)).
Notation SeqCtx e2 := (LetCtx "" e2).
Notation Skip := (Seq (Lit LitUnit) (Lit LitUnit)).

Section derived.
Context {Σ : iFunctor}.
Implicit Types P Q : iProp heap_lang Σ.
Implicit Types Φ : val → iProp heap_lang Σ.

(** Proof rules for the sugar *)
Lemma wp_lam' E x ef e v Φ :
  to_val e = Some v → ▷ wp E (subst ef x v) Φ ⊑ wp E (App (Lam x ef) e) Φ.
Proof. intros. by rewrite -wp_rec' ?subst_empty. Qed.

Lemma wp_let' E x e1 e2 v Φ :
  to_val e1 = Some v → ▷ wp E (subst e2 x v) Φ ⊑ wp E (Let x e1 e2) Φ.
Proof. apply wp_lam'. Qed.

Lemma wp_seq E e1 e2 Φ : wp E e1 (λ _, ▷ wp E e2 Φ) ⊑ wp E (Seq e1 e2) Φ.
Proof.
  rewrite -(wp_bind [LetCtx "" e2]). apply wp_mono=>v.
  by rewrite -wp_let' //= ?to_of_val ?subst_empty.
Qed.

Lemma wp_skip E Φ : ▷ (Φ (LitV LitUnit)) ⊑ wp E Skip Φ.
Proof. rewrite -wp_seq -wp_value // -wp_value //. Qed.

Lemma wp_le E (n1 n2 : Z) P Φ :
  (n1 ≤ n2 → P ⊑ ▷ Φ (LitV $ LitBool true)) →
  (n2 < n1 → P ⊑ ▷ Φ (LitV $ LitBool false)) →
  P ⊑ wp E (BinOp LeOp (Lit $ LitInt n1) (Lit $ LitInt n2)) Φ.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 ≤ n2)); by eauto with omega.
Qed.

Lemma wp_lt E (n1 n2 : Z) P Φ :
  (n1 < n2 → P ⊑ ▷ Φ (LitV $ LitBool true)) →
  (n2 ≤ n1 → P ⊑ ▷ Φ (LitV $ LitBool false)) →
  P ⊑ wp E (BinOp LtOp (Lit $ LitInt n1) (Lit $ LitInt n2)) Φ.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 < n2)); by eauto with omega.
Qed.

Lemma wp_eq E (n1 n2 : Z) P Φ :
  (n1 = n2 → P ⊑ ▷ Φ (LitV $ LitBool true)) →
  (n1 ≠ n2 → P ⊑ ▷ Φ (LitV $ LitBool false)) →
  P ⊑ wp E (BinOp EqOp (Lit $ LitInt n1) (Lit $ LitInt n2)) Φ.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 = n2)); by eauto with omega.
Qed.
End derived.
