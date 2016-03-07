From heap_lang Require Export lifting.
Import uPred.

(** Define some derived forms, and derived lemmas about them. *)
Notation Lam x e := (Rec BAnon x e).
Notation Let x e1 e2 := (App (Lam x e2) e1).
Notation Seq e1 e2 := (Let BAnon e1 e2).
Notation LamV x e := (RecV BAnon x e).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)).
Notation SeqCtx e2 := (LetCtx BAnon e2).
Notation Skip := (Seq (Lit LitUnit) (Lit LitUnit)).
Notation Match e0 x1 e1 x2 e2 := (Case e0 (Lam x1 e1) (Lam x2 e2)).

Section derived.
Context {Σ : iFunctor}.
Implicit Types P Q : iProp heap_lang Σ.
Implicit Types Φ : val → iProp heap_lang Σ.

(** Proof rules for the sugar *)
Lemma wp_lam E x ef e v Φ :
  to_val e = Some v →
  ▷ #> subst' x e ef @ E {{ Φ }} ⊑ #> App (Lam x ef) e @ E {{ Φ }}.
Proof. intros. by rewrite -wp_rec. Qed.

Lemma wp_let E x e1 e2 v Φ :
  to_val e1 = Some v →
  ▷ #> subst' x e1 e2 @ E {{ Φ }} ⊑ #> Let x e1 e2 @ E {{ Φ }}.
Proof. apply wp_lam. Qed.

Lemma wp_seq E e1 e2 v Φ :
  to_val e1 = Some v →
  ▷ #> e2 @ E {{ Φ }} ⊑ #> Seq e1 e2 @ E {{ Φ }}.
Proof. intros ?. by rewrite -wp_let. Qed.

Lemma wp_skip E Φ : ▷ Φ (LitV LitUnit) ⊑ #> Skip @ E {{ Φ }}.
Proof. rewrite -wp_seq // -wp_value //. Qed.

Lemma wp_match_inl E e0 v0 x1 e1 x2 e2 Φ :
  to_val e0 = Some v0 →
  ▷ #> subst' x1 e0 e1 @ E {{ Φ }} ⊑ #> Match (InjL e0) x1 e1 x2 e2 @ E {{ Φ }}.
Proof. intros. by rewrite -wp_case_inl // -[X in _ ⊑ X]later_intro -wp_let. Qed.

Lemma wp_match_inr E e0 v0 x1 e1 x2 e2 Φ :
  to_val e0 = Some v0 →
  ▷ #> subst' x2 e0 e2 @ E {{ Φ }} ⊑ #> Match (InjR e0) x1 e1 x2 e2 @ E {{ Φ }}.
Proof. intros. by rewrite -wp_case_inr // -[X in _ ⊑ X]later_intro -wp_let. Qed.

Lemma wp_le E (n1 n2 : Z) P Φ :
  (n1 ≤ n2 → P ⊑ ▷ Φ (LitV (LitBool true))) →
  (n2 < n1 → P ⊑ ▷ Φ (LitV (LitBool false))) →
  P ⊑ #> BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 ≤ n2)); by eauto with omega.
Qed.

Lemma wp_lt E (n1 n2 : Z) P Φ :
  (n1 < n2 → P ⊑ ▷ Φ (LitV (LitBool true))) →
  (n2 ≤ n1 → P ⊑ ▷ Φ (LitV (LitBool false))) →
  P ⊑ #> BinOp LtOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 < n2)); by eauto with omega.
Qed.

Lemma wp_eq E (n1 n2 : Z) P Φ :
  (n1 = n2 → P ⊑ ▷ Φ (LitV (LitBool true))) →
  (n1 ≠ n2 → P ⊑ ▷ Φ (LitV (LitBool false))) →
  P ⊑ #> BinOp EqOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 = n2)); by eauto with omega.
Qed.
End derived.
