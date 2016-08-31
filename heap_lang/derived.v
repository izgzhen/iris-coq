From iris.heap_lang Require Export lifting.
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
Context `{irisG heap_lang Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.

(** Proof rules for the sugar *)
Lemma wp_lam E x ef e Φ :
  is_Some (to_val e) → Closed (x :b: []) ef →
  ▷ WP subst' x e ef @ E {{ Φ }} ⊢ WP App (Lam x ef) e @ E {{ Φ }}.
Proof. intros. by rewrite -(wp_rec _ BAnon) //. Qed.

Lemma wp_let E x e1 e2 Φ :
  is_Some (to_val e1) → Closed (x :b: []) e2 →
  ▷ WP subst' x e1 e2 @ E {{ Φ }} ⊢ WP Let x e1 e2 @ E {{ Φ }}.
Proof. apply wp_lam. Qed.

Lemma wp_seq E e1 e2 Φ :
  is_Some (to_val e1) → Closed [] e2 →
  ▷ WP e2 @ E {{ Φ }} ⊢ WP Seq e1 e2 @ E {{ Φ }}.
Proof. intros ??. by rewrite -wp_let. Qed.

Lemma wp_skip E Φ : ▷ Φ (LitV LitUnit) ⊢ WP Skip @ E {{ Φ }}.
Proof. rewrite -wp_seq; last eauto. by rewrite -wp_value. Qed.

Lemma wp_match_inl E e0 x1 e1 x2 e2 Φ :
  is_Some (to_val e0) → Closed (x1 :b: []) e1 →
  ▷ WP subst' x1 e0 e1 @ E {{ Φ }} ⊢ WP Match (InjL e0) x1 e1 x2 e2 @ E {{ Φ }}.
Proof. intros. by rewrite -wp_case_inl // -[X in _ ⊢ X]later_intro -wp_let. Qed.

Lemma wp_match_inr E e0 x1 e1 x2 e2 Φ :
  is_Some (to_val e0) → Closed (x2 :b: []) e2 →
  ▷ WP subst' x2 e0 e2 @ E {{ Φ }} ⊢ WP Match (InjR e0) x1 e1 x2 e2 @ E {{ Φ }}.
Proof. intros. by rewrite -wp_case_inr // -[X in _ ⊢ X]later_intro -wp_let. Qed.

Lemma wp_le E (n1 n2 : Z) P Φ :
  (n1 ≤ n2 → P ⊢ ▷ |={E}=> Φ (LitV (LitBool true))) →
  (n2 < n1 → P ⊢ ▷ |={E}=> Φ (LitV (LitBool false))) →
  P ⊢ WP BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 ≤ n2)); by eauto with omega.
Qed.

Lemma wp_lt E (n1 n2 : Z) P Φ :
  (n1 < n2 → P ⊢ ▷ |={E}=> Φ (LitV (LitBool true))) →
  (n2 ≤ n1 → P ⊢ ▷ |={E}=> Φ (LitV (LitBool false))) →
  P ⊢ WP BinOp LtOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 < n2)); by eauto with omega.
Qed.

Lemma wp_eq E e1 e2 v1 v2 P Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  (v1 = v2 → P ⊢ ▷ |={E}=> Φ (LitV (LitBool true))) →
  (v1 ≠ v2 → P ⊢ ▷ |={E}=> Φ (LitV (LitBool false))) →
  P ⊢ WP BinOp EqOp e1 e2 @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (v1 = v2)); by eauto.
Qed.
End derived.
