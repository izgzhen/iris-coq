Require Export heap_lang.heap_lang heap_lang.lifting.
Import uPred heap_lang.

(** Define some syntactic sugar. LitTrue and LitFalse are defined in heap_lang.v. *)
Definition Lam (e : {bind expr}) := Rec e.[ren(+1)].
Definition Let (e1 : expr) (e2: {bind expr}) := App (Lam e2) e1.
Definition Seq (e1 e2 : expr) := Let e1 e2.[ren(+1)].
Definition If (e0 e1 e2 : expr) := Case e0 e1.[ren(+1)] e2.[ren(+1)].
Definition Lt e1 e2 := Le (Plus e1 $ LitNat 1) e2.
Definition Eq e1 e2 :=
  Let e1 (Let e2.[ren(+1)]
         (If (Le (Var 0) (Var 1)) (Le (Var 1) (Var 0)) LitFalse)).

Definition LamV (e : {bind expr}) := RecV e.[ren(+1)].

Definition LetCtx (e2 : {bind expr}) := AppRCtx (LamV e2).
Definition SeqCtx (e2 : expr) := LetCtx (e2.[ren(+1)]).

Module notations.
  Delimit Scope lang_scope with L.
  Bind Scope lang_scope with expr.
  Arguments wp {_ _} _ _%L _.

  Coercion LitNat : nat >-> expr.
  Coercion LitNatV : nat >-> val.
  Coercion Loc : loc >-> expr.
  Coercion LocV : loc >-> val.
  Coercion App : expr >-> Funclass.

  (** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
  first. *)
  (* What about Arguments for hoare triples?. *)
  (* The colons indicate binders. "let" is not consistent here though,
     thing are only bound in the "in". *)
  Notation "# n" := (ids (term:=expr) n) (at level 1, format "# n") : lang_scope.
  Notation "! e" := (Load e%L) (at level 10, format "! e") : lang_scope.
  Notation "'ref' e" := (Alloc e%L) (at level 30) : lang_scope.
  Notation "e1 + e2" := (Plus e1%L e2%L)
    (at level 50, left associativity) : lang_scope.
  Notation "e1 ≤ e2" := (Le e1%L e2%L) (at level 70) : lang_scope.
  Notation "e1 < e2" := (Lt e1%L e2%L) (at level 70) : lang_scope.
  (* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
  Notation "e1 <- e2" := (Store e1%L e2%L) (at level 80) : lang_scope.
  Notation "e1 ; e2" := (Seq e1%L e2%L)
    (at level 100, e2 at level 200) : lang_scope.
  Notation "'let:' e1 'in' e2" := (Let e1%L e2%L)
    (at level 102, e2 at level 200) : lang_scope.
  Notation "'λ:' e" := (Lam e%L) (at level 102, e at level 200) : lang_scope.
  Notation "'rec::' e" := (Rec e%L) (at level 102, e at level 200) : lang_scope.
  Notation "'if' e1 'then' e2 'else' e3" := (If e1%L e2%L e3%L)
    (at level 200, e1, e2, e3 at level 200) : lang_scope.
End notations.

Section suger.
Context {Σ : iFunctor}.
Implicit Types P : iProp heap_lang Σ.
Implicit Types Q : val → iProp heap_lang Σ.

(** Proof rules for the sugar *)
Lemma wp_lam E ef e v Q :
  to_val e = Some v → ▷ wp E ef.[e/] Q ⊑ wp E (App (Lam ef) e) Q.
Proof.
  intros Hv. rewrite -wp_rec; last eassumption.
  (* RJ: This pulls in functional extensionality. If that bothers us, we have
     to talk to the Autosubst guys. *)
  by asimpl.
Qed.
Lemma wp_let E e1 e2 Q :
  wp E e1 (λ v, ▷wp E (e2.[of_val v/]) Q) ⊑ wp E (Let e1 e2) Q.
Proof.
  rewrite -(wp_bind [LetCtx e2]). apply wp_mono=>v.
  by rewrite -wp_lam //= to_of_val.
Qed.
Lemma wp_if_true E e1 e2 Q : ▷ wp E e1 Q ⊑ wp E (If LitTrue e1 e2) Q.
Proof. rewrite -wp_case_inl //. by asimpl. Qed.
Lemma wp_if_false E e1 e2 Q : ▷ wp E e2 Q ⊑ wp E (If LitFalse e1 e2) Q.
Proof. rewrite -wp_case_inr //. by asimpl. Qed.
Lemma wp_lt E n1 n2 P Q :
  (n1 < n2 → P ⊑ ▷ Q LitTrueV) →
  (n1 ≥ n2 → P ⊑ ▷ Q LitFalseV) →
  P ⊑ wp E (Lt (LitNat n1) (LitNat n2)) Q.
Proof.
  intros; rewrite -(wp_bind [LeLCtx _]) -wp_plus -later_intro /=.
  auto using wp_le with lia.
Qed.
Lemma wp_eq E n1 n2 P Q :
  (n1 = n2 → P ⊑ ▷ Q LitTrueV) →
  (n1 ≠ n2 → P ⊑ ▷ Q LitFalseV) →
  P ⊑ wp E (Eq (LitNat n1) (LitNat n2)) Q.
Proof.
  intros HPeq HPne.
  rewrite -wp_let -wp_value' // -later_intro; asimpl.
  rewrite -wp_rec //; asimpl.
  rewrite -(wp_bind [CaseCtx _ _]) -later_intro; asimpl.
  apply wp_le; intros; asimpl.
  * rewrite -wp_case_inl // -!later_intro. apply wp_le; auto with lia.
  * rewrite -wp_case_inr // -later_intro -wp_value' //; auto with lia.
Qed.
End suger.
