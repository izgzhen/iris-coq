Require Export heap_lang.heap_lang heap_lang.lifting.
Import uPred heap_lang.

(** Define some syntactic sugar. LitTrue and LitFalse are defined in heap_lang.v. *)
Notation Lam x e := (Rec "" x e).
Notation Let x e1 e2 := (App (Lam x e2) e1).
Notation Seq e1 e2 := (Let "" e1 e2).
Notation LamV x e := (RecV "" x e).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)).
Notation SeqCtx e2 := (LetCtx "" e2).

Module notations.
  Delimit Scope lang_scope with L.
  Bind Scope lang_scope with expr.
  Arguments wp {_ _} _ _%L _.

  Coercion LitNat : nat >-> base_lit.
  Coercion LitBool : bool >-> base_lit.
  (** No coercion from base_lit to expr. This makes is slightly easier to tell
     apart language and Coq expressions. *)
  Coercion Var : string >-> expr.
  Coercion App : expr >-> Funclass.

  (** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
  first. *)
  (* What about Arguments for hoare triples?. *)
  Notation "' l" := (Lit l) (at level 8, format "' l") : lang_scope.
  Notation "! e" := (Load e%L) (at level 10, format "! e") : lang_scope.
  Notation "'ref' e" := (Alloc e%L) (at level 30) : lang_scope.
  Notation "e1 + e2" := (BinOp PlusOp e1%L e2%L)
    (at level 50, left associativity) : lang_scope.
  Notation "e1 - e2" := (BinOp MinusOp e1%L e2%L)
    (at level 50, left associativity) : lang_scope.
  Notation "e1 ≤ e2" := (BinOp LeOp e1%L e2%L) (at level 70) : lang_scope.
  Notation "e1 < e2" := (BinOp LtOp e1%L e2%L) (at level 70) : lang_scope.
  Notation "e1 = e2" := (BinOp EqOp e1%L e2%L) (at level 70) : lang_scope.
  (* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
  Notation "e1 <- e2" := (Store e1%L e2%L) (at level 80) : lang_scope.
  Notation "'rec:' f x := e" := (Rec f x e%L)
    (at level 102, f at level 1, x at level 1, e at level 200) : lang_scope.
  Notation "'if' e1 'then' e2 'else' e3" := (If e1%L e2%L e3%L)
    (at level 200, e1, e2, e3 at level 200) : lang_scope.

  (** Derived notions, in order of declaration. The notations for let and seq
  are stated explicitly instead of relying on the Notations Let and Seq as
  defined above. This is needed because App is now a coercion, and these
  notations are otherwise not pretty printed back accordingly. *)
  Notation "λ: x , e" := (Lam x e%L)
    (at level 102, x at level 1, e at level 200) : lang_scope.
  Notation "'let:' x := e1 'in' e2" := (Lam x e2%L e1%L)
    (at level 102, x at level 1, e1, e2 at level 200) : lang_scope.
  Notation "e1 ; e2" := (Lam "" e2%L e1%L)
    (at level 100, e2 at level 200) : lang_scope.
End notations.

Section suger.
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
  (n1 ≤ n2 → P ⊑ ▷ Q (LitV true)) →
  (n1 > n2 → P ⊑ ▷ Q (LitV false)) →
  P ⊑ wp E (BinOp LeOp (Lit n1) (Lit n2)) Q.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 ≤ n2)); by eauto with omega.
Qed.

Lemma wp_lt E (n1 n2 : nat) P Q :
  (n1 < n2 → P ⊑ ▷ Q (LitV true)) →
  (n1 ≥ n2 → P ⊑ ▷ Q (LitV false)) →
  P ⊑ wp E (BinOp LtOp (Lit n1) (Lit n2)) Q.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 < n2)); by eauto with omega.
Qed.

Lemma wp_eq E (n1 n2 : nat) P Q :
  (n1 = n2 → P ⊑ ▷ Q (LitV true)) →
  (n1 ≠ n2 → P ⊑ ▷ Q (LitV false)) →
  P ⊑ wp E (BinOp EqOp (Lit n1) (Lit n2)) Q.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 = n2)); by eauto with omega.
Qed.

End suger.
