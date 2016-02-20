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
  to_val e = Some v →
  ▷ || subst ef x v @ E {{ Φ }} ⊑ || App (Lam x ef) e @ E {{ Φ }}.
Proof. intros. by rewrite -wp_rec' ?subst_empty. Qed.

Lemma wp_let' E x e1 e2 v Φ :
  to_val e1 = Some v →
  ▷ || subst e2 x v @ E {{ Φ }} ⊑ || Let x e1 e2 @ E {{ Φ }}.
Proof. apply wp_lam'. Qed.

Lemma wp_seq E e1 e2 v Φ :
  to_val e1 = Some v →
  ▷ || e2 @ E {{ Φ }} ⊑ || Seq e1 e2 @ E {{ Φ }}.
Proof. intros ?. rewrite -wp_let' // subst_empty //. Qed.

Lemma wp_skip E Φ : ▷ Φ (LitV LitUnit) ⊑ || Skip @ E {{ Φ }}.
Proof. rewrite -wp_seq // -wp_value //. Qed.

Lemma wp_le E (n1 n2 : Z) P Φ :
  (n1 ≤ n2 → P ⊑ ▷ Φ (LitV (LitBool true))) →
  (n2 < n1 → P ⊑ ▷ Φ (LitV (LitBool false))) →
  P ⊑ || BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 ≤ n2)); by eauto with omega.
Qed.

Lemma wp_lt E (n1 n2 : Z) P Φ :
  (n1 < n2 → P ⊑ ▷ Φ (LitV (LitBool true))) →
  (n2 ≤ n1 → P ⊑ ▷ Φ (LitV (LitBool false))) →
  P ⊑ || BinOp LtOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 < n2)); by eauto with omega.
Qed.

Lemma wp_eq E (n1 n2 : Z) P Φ :
  (n1 = n2 → P ⊑ ▷ Φ (LitV (LitBool true))) →
  (n1 ≠ n2 → P ⊑ ▷ Φ (LitV (LitBool false))) →
  P ⊑ || BinOp EqOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 = n2)); by eauto with omega.
Qed.
End derived.
