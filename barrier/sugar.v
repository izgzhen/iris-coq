Require Export barrier.heap_lang barrier.lifting.
Import uPred.

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

Definition LetCtx (K1 : ectx) (e2 : {bind expr}) := AppRCtx (LamV e2) K1.
Definition SeqCtx (K1 : ectx) (e2 : expr) := LetCtx K1 (e2.[ren(+1)]).

(** Proof rules for the sugar *)
Lemma wp_lam E ef e v Q :
  e2v e = Some v →
  ▷wp (Σ:=Σ) E ef.[e/] Q ⊑ wp (Σ:=Σ) E (App (Lam ef) e) Q.
Proof.
  intros Hv. rewrite -wp_rec; last eassumption.
  (* RJ: This pulls in functional extensionality. If that bothers us, we have
     to talk to the Autosubst guys. *)
  by asimpl.
Qed.

Lemma wp_let e1 e2 E Q :
  wp (Σ:=Σ) E e1 (λ v, ▷wp (Σ:=Σ) E (e2.[v2e v/]) Q) ⊑ wp (Σ:=Σ) E (Let e1 e2) Q.
Proof.
  rewrite -(wp_bind (LetCtx EmptyCtx e2)). apply wp_mono=>v.
  rewrite -wp_lam //. by rewrite v2v.
Qed.

Lemma wp_if_true e1 e2 E Q :
  ▷wp (Σ:=Σ) E e1 Q ⊑ wp (Σ:=Σ) E (If LitTrue e1 e2) Q.
Proof.
  rewrite -wp_case_inl //. by asimpl.
Qed.

Lemma wp_if_false e1 e2 E Q :
  ▷wp (Σ:=Σ) E e2 Q ⊑ wp (Σ:=Σ) E (If LitFalse e1 e2) Q.
Proof.
  rewrite -wp_case_inr //. by asimpl.
Qed.

Lemma wp_lt n1 n2 E P Q :
  (n1 < n2 → P ⊑ ▷Q LitTrueV) →
  (n1 ≥ n2 → P ⊑ ▷Q LitFalseV) →
  P ⊑ wp (Σ:=Σ) E (Lt (LitNat n1) (LitNat n2)) Q.
Proof.
  intros HPlt HPge.
  rewrite -(wp_bind (LeLCtx EmptyCtx _)) -wp_plus -later_intro. simpl.
  apply wp_le; intros; [apply HPlt|apply HPge]; omega.
Qed.

Lemma wp_eq n1 n2 E P Q :
  (n1 = n2 → P ⊑ ▷Q LitTrueV) →
  (n1 ≠ n2 → P ⊑ ▷Q LitFalseV) →
  P ⊑ wp (Σ:=Σ) E (Eq (LitNat n1) (LitNat n2)) Q.
Proof.
  intros HPeq HPne.
  rewrite -wp_let -wp_value' // -later_intro. asimpl.
  rewrite -wp_rec //. asimpl.
  rewrite -(wp_bind (CaseCtx EmptyCtx _ _)) -later_intro.
  apply wp_le; intros Hn12.
  - asimpl. rewrite -wp_case_inl // -!later_intro. apply wp_le; intros Hn12'.
    + apply HPeq; omega.
    + apply HPne; omega.
  - asimpl. rewrite -wp_case_inr // -later_intro -wp_value' //.
    apply HPne; omega.
Qed.
