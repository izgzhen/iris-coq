From iris.base_logic Require Export upred.

Record sProp := SProp {
  sProp_holds :> nat → Prop;
  sProp_holds_mono : Proper (flip (≤) ==> impl) sProp_holds
}.

Existing Instance sProp_holds_mono.
Instance sprop_holds_mono_flip (P : sProp) : Proper ((≤) ==> flip impl) P.
Proof. solve_proper. Qed.

Arguments sProp_holds _ _ : simpl never.
Add Printing Constructor sProp.

Section sProp_cofe.
  Inductive sProp_equiv' (P Q : sProp) : Prop :=
    { sProp_in_equiv : ∀ n, P n ↔ Q n }.
  Instance sProp_equiv : Equiv sProp := sProp_equiv'.
  Inductive sProp_dist' (n : nat) (P Q : sProp) : Prop :=
    { sProp_in_dist : ∀ n', n' ≤ n → P n' ↔ Q n' }.
  Instance sProp_dist : Dist sProp := sProp_dist'.
  Definition sProp_ofe_mixin : OfeMixin sProp.
  Proof.
    split.
    - intros P Q; split.
      + intros HPQ n; split=>??; apply HPQ.
      + intros HPQ; split=>?; eapply HPQ; auto.
    - intros n; split.
      + by intros P; split.
      + by intros P Q HPQ; split=> ??; symmetry; apply HPQ.
      + by intros P Q Q' HP HQ; split=> n' ?; trans (Q n'); [apply HP|apply HQ].
    - intros n P Q HPQ; split=> ??. apply HPQ. auto.
  Qed.
  Canonical Structure sPropC : ofeT := OfeT (sProp) sProp_ofe_mixin.

  Program Definition sProp_compl : Compl sPropC := λ c,
    {| sProp_holds n := c n n |}.
  Next Obligation.
    move => c n1 n2 Hn12 /(sProp_holds_mono _ _ _ Hn12) H.
    by apply (chain_cauchy c _ _ Hn12).
  Qed.
  Global Program Instance sProp_cofe : Cofe sPropC := {| compl := sProp_compl |}.
  Next Obligation. intros n. split=>n' Hn'. symmetry. by apply (chain_cauchy c). Qed.
End sProp_cofe.
Arguments sPropC : clear implicits.

Instance sProp_proper : Proper ((≡) ==> (=) ==> iff) sProp_holds.
Proof. by move=> ??[?]??->. Qed.

Global Instance limit_preserving_sprop `{Cofe A} (P : A → sPropC) :
  NonExpansive P → LimitPreserving (λ x, ∀ n, P x n).
Proof.
  intros ? c Hc n. specialize (Hc n n).
  assert (Hcompl : P (compl c) ≡{n}≡ P (c n)) by by rewrite (conv_compl n c).
  by apply Hcompl.
Qed.

Section uPred1.

Context {M : ucmraT}.

(* TODO : use logical connectives in sProp *)
Program Definition uPred1_valid (P : M -n> sPropC) : sPropC :=
  SProp (λ n, ∀ n', n' ≤ n →
         (∀ x1 x2, x1 ≼{n'} x2 → P x1 n' → P x2 n') ∧
         (∀ x, (∀ n'', n'' ≤ n' → ✓{n''} x → P x n'') → P x n')) _.
Next Obligation. move=>??? /= H. by setoid_rewrite H. Qed.
Instance uPred1_valid_ne : NonExpansive uPred1_valid.
Proof.
  split=>??. repeat ((apply forall_proper=>?) || f_equiv).
  - split=> HH ?; apply H, HH, H=>//; lia.
  - split=> HH ?; (apply H, HH; [lia|])=> ???; (apply H; [lia|auto]).
Qed.

Definition uPred1 :=
  sigC (λ (P : M -n> sPropC), ∀ n, uPred1_valid P n).
Global Instance uPred1_cofe : Cofe uPred1.
Proof. eapply @sig_cofe, limit_preserving_sprop, _. Qed.

Program Definition uPred_of_uPred1 (P : uPred1) : uPred M :=
  {| uPred_holds n x := `P x n |}.
Next Obligation.
  intros P ?????. by eapply (proj1 (proj2_sig P _ _ (le_refl _))).
Qed.
Next Obligation. move => /= ????? Hle. by rewrite ->Hle. Qed.

Global Instance uPred_of_uPred1_ne : NonExpansive uPred_of_uPred1.
Proof.
  move=>??? EQ. split=>? x ??. specialize (EQ x). by split=>H; apply EQ.
Qed.
Global Instance uPred_of_uPred1_proper : Proper ((≡) ==> (≡)) uPred_of_uPred1.
Proof. apply (ne_proper _). Qed.

Program Definition uPred1_of_uPred (P : uPred M) : uPred1 :=
  λne x, SProp (λ n, ∀ n', n' ≤ n → ✓{n'}x → P n' x) _.
Next Obligation. move => ???? /= Hle ?. by setoid_rewrite -> Hle. Qed. 
Next Obligation.
  move => ???? H. split=>??. do 2 apply forall_proper=>?.
  split=>HH ?;
    (eapply uPred_ne; [eapply dist_le; [by symmetry|lia]|]);
    (eapply HH, cmra_validN_ne; [eapply dist_le|]=>//; lia).
Qed.
Next Obligation.
  split.
  - move=>??? HP ???. eapply uPred_mono, cmra_includedN_le=>//.
    eapply HP, cmra_validN_includedN=>//. eapply cmra_includedN_le=>//.
  - move=>? HP ???. by eapply HP.
Qed.

Global Instance uPred1_of_uPred_ne : NonExpansive uPred1_of_uPred.
Proof.
  move=>??? EQ. split=>??. do 3 apply forall_proper=>?. apply EQ=>//. lia.
Qed.
Global Instance uPred1_of_uPred_proper : Proper ((≡) ==> (≡)) uPred1_of_uPred.
Proof. apply (ne_proper _). Qed.

Lemma uPred1_of_uPred_of_uPred1 P : uPred1_of_uPred (uPred_of_uPred1 P) ≡ P.
Proof.
  split=>?; split=>HP.
  - apply (proj2 (proj2_sig P _ _ (le_refl _)))=>???. by apply HP.
  - move=>? Hle ?. unfold uPred_holds=>/=. by rewrite ->Hle.
Qed.

Lemma uPred_of_uPred1_of_uPred P : uPred_of_uPred1 (uPred1_of_uPred P) ≡ P.
Proof.
  split=>?; split=>HP.
  - by apply HP.
  - move=>???. by eapply uPred_closed.
Qed.

End uPred1.
Arguments  uPred1 _ : clear implicits.

Section uPred2.
Context {M : ucmraT}.

Record uPred2 : Type := IProp {
  uPred2_holds :> M → sProp;
  uPred2_mono n x1 x2 : uPred2_holds x1 n → x1 ≼{n} x2 → uPred2_holds x2 n
}.

Section cofe.
  Inductive uPred2_equiv' (P Q : uPred2) : Prop :=
    { uPred_in_equiv : ∀ n x, ✓{n} x → P x n ↔ Q x n }.
  Instance uPred2_equiv : Equiv uPred2 := uPred2_equiv'.
  Inductive uPred2_dist' (n : nat) (P Q : uPred2) : Prop :=
    { uPred_in_dist : ∀ n' x, n' ≤ n → ✓{n'} x → P x n' ↔ Q x n' }.
  Instance uPred_dist : Dist uPred2 := uPred2_dist'.
  Definition uPred2_ofe_mixin : OfeMixin uPred2.
  Proof.
    split.
    - intros P Q; split.
      + by intros HPQ n; split=> i x ??; apply HPQ.
      + intros HPQ; split=> n x ?; apply HPQ with n; auto.
    - intros n; split.
      + by intros P; split=> x i.
      + by intros P Q HPQ; split=> x i ??; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i x ??.
        by trans (Q x i);[apply HP|apply HQ].
    - intros n P Q HPQ; split=> i x ??; apply HPQ; auto.
  Qed.
  Canonical Structure uPred2C : ofeT := OfeT uPred2 uPred2_ofe_mixin.

  Program Definition uPred2_compl : Compl uPred2C := λ c,
    {| uPred2_holds x := SProp (λ n, ∀ n', n' ≤ n → ✓{n'}x → c n x n') _ |}.
  Next Obligation.
    move => c ? n1 n2 /= Hn12 H ???. apply (chain_cauchy c _ _ Hn12)=>//.
    apply H. lia. done.
  Qed.
  Next Obligation.
    move => ???? HH ????. eapply uPred2_mono, cmra_includedN_le=>//.
    apply HH=>//. eapply cmra_validN_includedN=>//.
    by eapply cmra_includedN_le.
  Qed.
  Global Program Instance uPred2_cofe :
    Cofe uPred2C := {| compl := uPred2_compl |}.
  Next Obligation.
    intro n. split. move => ?? Hle. split=>HP.
    - apply (chain_cauchy c _ _ Hle)=>//. by apply HP.
    - move=> ???. eapply sProp_holds_mono=>//.
      eapply (chain_cauchy c _ n), HP=>//.
  Qed.
End cofe.

Program Definition uPred2_of_uPred1 (P : uPred1 M) : uPred2 :=
  {| uPred2_holds x := `P x |}.
Next Obligation.
  move=>/= P ?????. by eapply (proj1 (proj2_sig P _ _ (le_refl _))).
Qed.
Global Instance uPred2_of_uPred1_ne : NonExpansive uPred2_of_uPred1.
Proof. move=>??? EQ. split=>????. by apply EQ. Qed.
Global Instance uPred2_of_uPred1_proper : Proper ((≡) ==> (≡)) uPred2_of_uPred1.
Proof. apply (ne_proper _). Qed.

Program Definition uPred1_of_uPred2 (P : uPred2) : uPred1 M :=
  λne x, SProp (λ n, ∀ n', n' ≤ n → ✓{n'}x → P x n') _.
Next Obligation. move=>???? HLE ??. rewrite <-HLE. auto. Qed.
Next Obligation.
  split=>??. do 2 apply forall_proper=>?.
  split=>HH ?; (eapply uPred2_mono, cmra_includedN_le;
   [eapply HH, cmra_validN_ne; [eapply dist_le; [done|lia]|done]|
                                by rewrite H|lia]).
Qed.
Next Obligation.
  split.
  - move=>??? HH ???. eapply uPred2_mono; [|by eapply cmra_includedN_le].
    by eapply HH, cmra_validN_includedN, cmra_includedN_le.
  - move=>? HH ???. by eapply HH.
Qed.
Global Instance uPred1_of_uPred2_ne : NonExpansive uPred1_of_uPred2.
Proof.
  move=> ??? EQ. split=>??. do 3 eapply forall_proper=>?.
  apply EQ. lia. done.
Qed.

Lemma uPred1_of_uPred2_of_uPred1 P : uPred1_of_uPred2 (uPred2_of_uPred1 P) ≡ P.
Proof.
  split=>?. split=>HP.
  - apply (proj2 (proj2_sig P _ _ (le_refl _))). intros. by apply HP.
  - intros ???. by eapply sProp_holds_mono, HP.
Qed.

Lemma uPred2_of_uPred1_of_uPred2 P : uPred2_of_uPred1 (uPred1_of_uPred2 P) ≡ P.
Proof.
  split=>?. split=>HP.
  - by apply HP.
  - intros ???. by eapply sProp_holds_mono, HP.
Qed.

End uPred2.
Arguments uPred2 _ : clear implicits.
Arguments uPred2C _ : clear implicits.
