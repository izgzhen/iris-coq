From heap_lang Require Export derived.

(** We define an alternative notion of substitution [gsubst e x ev] that
preserves the expression [e] syntactically in case the variable [x] does not
occur freely in [e]. By syntactically, we mean that [e] is preserved without
unfolding any Coq definitions. For example:

<<
  Definition id : val := λ: "x", "x".
  Eval simpl in subst (id "y") "y" '10.   (* (Lam "x" "x") '10 *)
  Eval simpl in gsubst (id "y") "y" '10.  (* id '10 *)
>>

For [gsubst e x ev] to work, [e] should not contain any opaque parts.
Fundamentally, the way this works is that [gsubst] tests whether a subterm
needs substitution, before it traverses into the term. This way, unaffected
sub-terms are returned directly, rather than their tree structure being
deconstructed and composed again.

The function [gsubst e x ev] differs in yet another way from [subst e x v].
The function [gsubst] substitutes an expression [ev] whereas [subst]
substitutes a value [v]. This way we avoid unnecessary conversion back and
forth between values and expressions, which could also cause Coq definitions
to be unfolded. For example, consider the rule [wp_rec'] from below:

<<
  Definition foo : val := rec: "f" "x" := ... .

  Lemma wp_rec E e1 f x erec e2 v Φ :
    e1 = Rec f x erec →
    to_val e2 = Some v →
    ▷ || gsubst (gsubst erec f e1) x e2 @ E {{ Φ }} ⊑ || App e1 e2 @ E {{ Φ }}.
>>

We ensure that [e1] is substituted instead of [RecV f x erec]. So, for example
when taking [e1 := foo] we ensure that [foo] is substituted without being
unfolded. *)

(** * Implementation *)
(** The core of [gsubst e x ev] is the partial function [gsubst_go e x ev] that
returns [None] in case [x] does not occur freely in [e] and [Some e'] in case
[x] occurs in [e]. The function [gsubst e x ev] is then simply defined as
[from_option e (gsubst_go e x ev)]. *)
Definition gsubst_lift {A B C} (f : A → B → C)
    (x : A) (y : B) (mx : option A) (my : option B) : option C :=
  match mx, my with
  | Some x, Some y => Some (f x y)
  | Some x, None => Some (f x y)
  | None, Some y => Some (f x y)
  | None, None => None
  end.
Fixpoint gsubst_go (e : expr) (x : string) (ev : expr) : option expr :=
  match e with
  | Var y => if decide (x = y ∧ x ≠ "") then Some ev else None
  | Rec f y e =>
     if decide (x ≠ f ∧ x ≠ y) then Rec f y <$> gsubst_go e x ev else None
  | App e1 e2 => gsubst_lift App e1 e2 (gsubst_go e1 x ev) (gsubst_go e2 x ev)
  | Lit l => None
  | UnOp op e => UnOp op <$> gsubst_go e x ev
  | BinOp op e1 e2 =>
     gsubst_lift (BinOp op) e1 e2 (gsubst_go e1 x ev) (gsubst_go e2 x ev)
  | If e0 e1 e2 =>
     gsubst_lift id (If e0 e1) e2
       (gsubst_lift If e0 e1 (gsubst_go e0 x ev) (gsubst_go e1 x ev))
       (gsubst_go e2 x ev)
  | Pair e1 e2 => gsubst_lift Pair e1 e2 (gsubst_go e1 x ev) (gsubst_go e2 x ev)
  | Fst e => Fst <$> gsubst_go e x ev
  | Snd e => Snd <$> gsubst_go e x ev
  | InjL e => InjL <$> gsubst_go e x ev
  | InjR e => InjR <$> gsubst_go e x ev
  | Case e0 x1 e1 x2 e2 =>
     gsubst_lift id (Case e0 x1 e1 x2) e2
       (gsubst_lift (λ e0' e1', Case e0' x1 e1' x2) e0 e1
         (gsubst_go e0 x ev)
         (if decide (x ≠ x1) then gsubst_go e1 x ev else None))
       (if decide (x ≠ x2) then gsubst_go e2 x ev else None)
  | Fork e => Fork <$> gsubst_go e x ev
  | Loc l => None
  | Alloc e => Alloc <$> gsubst_go e x ev
  | Load e => Load <$> gsubst_go e x ev
  | Store e1 e2 => gsubst_lift Store e1 e2 (gsubst_go e1 x ev) (gsubst_go e2 x ev)
  | Cas e0 e1 e2 =>
     gsubst_lift id (Cas e0 e1) e2
       (gsubst_lift Cas e0 e1 (gsubst_go e0 x ev) (gsubst_go e1 x ev))
       (gsubst_go e2 x ev)
  end.
Definition gsubst (e : expr) (x : string) (ev : expr) : expr :=
  from_option e (gsubst_go e x ev).

(** * Simpl  *)
(** Ensure that [simpl] unfolds [gsubst e x ev] when applied to a concrete term
[e] and use [simpl nomatch] to ensure that it does not reduce in case [e]
contains any opaque parts that block reduction. *)
Arguments gsubst !_ _ _/ : simpl nomatch.

(** We define heap_lang functions as values (see [id] above). In order to
ensure too eager conversion to expressions, we block [simpl]. *)
Arguments of_val : simpl never.

(** * Correctness *)
(** We prove that [gsubst] behaves like [subst] when substituting values. *)
Lemma gsubst_None e x v : gsubst_go e x (of_val v) = None → e = subst e x v.
Proof.
  induction e; simpl; unfold gsubst_lift; intros;
    repeat (simplify_option_eq || case_match); f_equal; auto.
Qed.
Lemma gsubst_correct e x v : gsubst e x (of_val v) = subst e x v.
Proof.
  unfold gsubst; destruct (gsubst_go e x (of_val v)) as [e'|] eqn:He; simpl;
    last by apply gsubst_None.
  revert e' He; induction e; simpl; unfold gsubst_lift; intros;
    repeat (simplify_option_eq || case_match);
    f_equal; auto using gsubst_None.
Qed.

(** * Weakest precondition rules *)
Section wp.
Context {Σ : iFunctor}.
Implicit Types P Q : iProp heap_lang Σ.
Implicit Types Φ : val → iProp heap_lang Σ.
Hint Resolve to_of_val.

Lemma wp_rec E e1 f x erec e2 v Φ :
  e1 = Rec f x erec →
  to_val e2 = Some v →
  ▷ || gsubst (gsubst erec f e1) x e2 @ E {{ Φ }} ⊑ || App e1 e2 @ E {{ Φ }}.
Proof.
  intros -> <-%of_to_val.
  rewrite (gsubst_correct _ _ (RecV _ _ _)) gsubst_correct.
  by apply wp_rec'.
Qed.

Lemma wp_lam E x ef e v Φ :
  to_val e = Some v →
  ▷ || gsubst ef x e @ E {{ Φ }} ⊑ || App (Lam x ef) e @ E {{ Φ }}.
Proof. intros <-%of_to_val; rewrite gsubst_correct. by apply wp_lam'. Qed.

Lemma wp_let E x e1 e2 v Φ :
  to_val e1 = Some v →
  ▷ || gsubst e2 x e1 @ E {{ Φ }} ⊑ || Let x e1 e2 @ E {{ Φ }}.
Proof. apply wp_lam. Qed.

Lemma wp_case_inl E e0 v0 x1 e1 x2 e2 Φ :
  to_val e0 = Some v0 →
  ▷ || gsubst e1 x1 e0 @ E {{ Φ }} ⊑ || Case (InjL e0) x1 e1 x2 e2 @ E {{ Φ }}.
Proof. intros <-%of_to_val; rewrite gsubst_correct. by apply wp_case_inl'. Qed.

Lemma wp_case_inr E e0 v0 x1 e1 x2 e2 Φ :
  to_val e0 = Some v0 →
  ▷ || gsubst e2 x2 e0 @ E {{ Φ }} ⊑ || Case (InjR e0) x1 e1 x2 e2 @ E {{ Φ }}.
Proof. intros <-%of_to_val; rewrite gsubst_correct. by apply wp_case_inr'. Qed.
End wp.
