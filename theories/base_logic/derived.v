From iris.base_logic Require Export primitive.
Set Default Proof Using "Type".
Import upred.uPred primitive.uPred.

Definition uPred_iff {M} (P Q : uPred M) : uPred M := ((P → Q) ∧ (Q → P))%I.
Instance: Params (@uPred_iff) 1.
Infix "↔" := uPred_iff : uPred_scope.

Definition uPred_laterN {M} (n : nat) (P : uPred M) : uPred M :=
  Nat.iter n uPred_later P.
Instance: Params (@uPred_laterN) 2.
Notation "▷^ n P" := (uPred_laterN n P)
  (at level 20, n at level 9, P at level 20,
   format "▷^ n  P") : uPred_scope.
Notation "▷? p P" := (uPred_laterN (Nat.b2n p) P)
  (at level 20, p at level 9, P at level 20,
   format "▷? p  P") : uPred_scope.

Definition uPred_always_if {M} (p : bool) (P : uPred M) : uPred M :=
  (if p then □ P else P)%I.
Instance: Params (@uPred_always_if) 2.
Arguments uPred_always_if _ !_ _/.
Notation "□? p P" := (uPred_always_if p P)
  (at level 20, p at level 9, P at level 20, format "□? p  P").

Definition uPred_except_0 {M} (P : uPred M) : uPred M := ▷ False ∨ P.
Notation "◇ P" := (uPred_except_0 P)
  (at level 20, right associativity) : uPred_scope.
Instance: Params (@uPred_except_0) 1.
Typeclasses Opaque uPred_except_0.

Class TimelessP {M} (P : uPred M) := timelessP : ▷ P ⊢ ◇ P.
Arguments timelessP {_} _ {_}.
Hint Mode TimelessP + ! : typeclass_instances.
Instance: Params (@TimelessP) 1.

Class PersistentP {M} (P : uPred M) := persistentP : P ⊢ □ P.
Arguments persistentP {_} _ {_}.
Hint Mode PersistentP + ! : typeclass_instances.
Instance: Params (@PersistentP) 1.

Module uPred.
Section derived.
Context {M : ucmraT}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.
Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I). (* Force implicit argument M *)
Notation "P ⊣⊢ Q" := (equiv (A:=uPred M) P%I Q%I). (* Force implicit argument M *)

(* Derived logical stuff *)
Lemma False_elim P : False ⊢ P.
Proof. by apply (pure_elim' False). Qed.
Lemma True_intro P : P ⊢ True.
Proof. by apply pure_intro. Qed.

Lemma and_elim_l' P Q R : (P ⊢ R) → P ∧ Q ⊢ R.
Proof. by rewrite and_elim_l. Qed.
Lemma and_elim_r' P Q R : (Q ⊢ R) → P ∧ Q ⊢ R.
Proof. by rewrite and_elim_r. Qed.
Lemma or_intro_l' P Q R : (P ⊢ Q) → P ⊢ Q ∨ R.
Proof. intros ->; apply or_intro_l. Qed.
Lemma or_intro_r' P Q R : (P ⊢ R) → P ⊢ Q ∨ R.
Proof. intros ->; apply or_intro_r. Qed.
Lemma exist_intro' {A} P (Ψ : A → uPred M) a : (P ⊢ Ψ a) → P ⊢ ∃ a, Ψ a.
Proof. intros ->; apply exist_intro. Qed.
Lemma forall_elim' {A} P (Ψ : A → uPred M) : (P ⊢ ∀ a, Ψ a) → ∀ a, P ⊢ Ψ a.
Proof. move=> HP a. by rewrite HP forall_elim. Qed.

Hint Resolve pure_intro.
Hint Resolve or_elim or_intro_l' or_intro_r'.
Hint Resolve and_intro and_elim_l' and_elim_r'.
Hint Immediate True_intro False_elim.

Lemma impl_intro_l P Q R : (Q ∧ P ⊢ R) → P ⊢ Q → R.
Proof. intros HR; apply impl_intro_r; rewrite -HR; auto. Qed.
Lemma impl_elim_l P Q : (P → Q) ∧ P ⊢ Q.
Proof. apply impl_elim with P; auto. Qed.
Lemma impl_elim_r P Q : P ∧ (P → Q) ⊢ Q.
Proof. apply impl_elim with P; auto. Qed.
Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
Proof. intros; apply impl_elim with Q; auto. Qed.
Lemma impl_elim_r' P Q R : (Q ⊢ P → R) → P ∧ Q ⊢ R.
Proof. intros; apply impl_elim with P; auto. Qed.
Lemma impl_entails P Q : (P → Q)%I → P ⊢ Q.
Proof. intros HPQ; apply impl_elim with P; rewrite -?HPQ; auto. Qed.
Lemma entails_impl P Q : (P ⊢ Q) → (P → Q)%I.
Proof. intro. apply impl_intro_l. auto. Qed.

Lemma and_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∧ P' ⊢ Q ∧ Q'.
Proof. auto. Qed.
Lemma and_mono_l P P' Q : (P ⊢ Q) → P ∧ P' ⊢ Q ∧ P'.
Proof. by intros; apply and_mono. Qed.
Lemma and_mono_r P P' Q' : (P' ⊢ Q') → P ∧ P' ⊢ P ∧ Q'.
Proof. by apply and_mono. Qed.

Lemma or_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∨ P' ⊢ Q ∨ Q'.
Proof. auto. Qed.
Lemma or_mono_l P P' Q : (P ⊢ Q) → P ∨ P' ⊢ Q ∨ P'.
Proof. by intros; apply or_mono. Qed.
Lemma or_mono_r P P' Q' : (P' ⊢ Q') → P ∨ P' ⊢ P ∨ Q'.
Proof. by apply or_mono. Qed.

Lemma impl_mono P P' Q Q' : (Q ⊢ P) → (P' ⊢ Q') → (P → P') ⊢ Q → Q'.
Proof.
  intros HP HQ'; apply impl_intro_l; rewrite -HQ'.
  apply impl_elim with P; eauto.
Qed.
Lemma forall_mono {A} (Φ Ψ : A → uPred M) :
  (∀ a, Φ a ⊢ Ψ a) → (∀ a, Φ a) ⊢ ∀ a, Ψ a.
Proof.
  intros HP. apply forall_intro=> a; rewrite -(HP a); apply forall_elim.
Qed.
Lemma exist_mono {A} (Φ Ψ : A → uPred M) :
  (∀ a, Φ a ⊢ Ψ a) → (∃ a, Φ a) ⊢ ∃ a, Ψ a.
Proof. intros HΦ. apply exist_elim=> a; rewrite (HΦ a); apply exist_intro. Qed.

Global Instance and_mono' : Proper ((⊢) ==> (⊢) ==> (⊢)) (@uPred_and M).
Proof. by intros P P' HP Q Q' HQ; apply and_mono. Qed.
Global Instance and_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (@uPred_and M).
Proof. by intros P P' HP Q Q' HQ; apply and_mono. Qed.
Global Instance or_mono' : Proper ((⊢) ==> (⊢) ==> (⊢)) (@uPred_or M).
Proof. by intros P P' HP Q Q' HQ; apply or_mono. Qed.
Global Instance or_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (@uPred_or M).
Proof. by intros P P' HP Q Q' HQ; apply or_mono. Qed.
Global Instance impl_mono' :
  Proper (flip (⊢) ==> (⊢) ==> (⊢)) (@uPred_impl M).
Proof. by intros P P' HP Q Q' HQ; apply impl_mono. Qed.
Global Instance impl_flip_mono' :
  Proper ((⊢) ==> flip (⊢) ==> flip (⊢)) (@uPred_impl M).
Proof. by intros P P' HP Q Q' HQ; apply impl_mono. Qed.
Global Instance forall_mono' A :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (@uPred_forall M A).
Proof. intros P1 P2; apply forall_mono. Qed.
Global Instance forall_flip_mono' A :
  Proper (pointwise_relation _ (flip (⊢)) ==> flip (⊢)) (@uPred_forall M A).
Proof. intros P1 P2; apply forall_mono. Qed.
Global Instance exist_mono' A :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (@uPred_exist M A).
Proof. intros P1 P2; apply exist_mono. Qed.
Global Instance exist_flip_mono' A :
  Proper (pointwise_relation _ (flip (⊢)) ==> flip (⊢)) (@uPred_exist M A).
Proof. intros P1 P2; apply exist_mono. Qed.

Global Instance and_idem : IdemP (⊣⊢) (@uPred_and M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_idem : IdemP (⊣⊢) (@uPred_or M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_comm : Comm (⊣⊢) (@uPred_and M).
Proof. intros P Q; apply (anti_symm (⊢)); auto. Qed.
Global Instance True_and : LeftId (⊣⊢) True%I (@uPred_and M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_True : RightId (⊣⊢) True%I (@uPred_and M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance False_and : LeftAbsorb (⊣⊢) False%I (@uPred_and M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_False : RightAbsorb (⊣⊢) False%I (@uPred_and M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance True_or : LeftAbsorb (⊣⊢) True%I (@uPred_or M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_True : RightAbsorb (⊣⊢) True%I (@uPred_or M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance False_or : LeftId (⊣⊢) False%I (@uPred_or M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_False : RightId (⊣⊢) False%I (@uPred_or M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_assoc : Assoc (⊣⊢) (@uPred_and M).
Proof. intros P Q R; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_comm : Comm (⊣⊢) (@uPred_or M).
Proof. intros P Q; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_assoc : Assoc (⊣⊢) (@uPred_or M).
Proof. intros P Q R; apply (anti_symm (⊢)); auto. Qed.
Global Instance True_impl : LeftId (⊣⊢) True%I (@uPred_impl M).
Proof.
  intros P; apply (anti_symm (⊢)).
  - by rewrite -(left_id True%I uPred_and (_ → _)%I) impl_elim_r.
  - by apply impl_intro_l; rewrite left_id.
Qed.
Lemma False_impl P : (False → P) ⊣⊢ True.
Proof.
  apply (anti_symm (⊢)); [by auto|].
  apply impl_intro_l. rewrite left_absorb. auto.
Qed.

Lemma exists_impl_forall {A} P (Ψ : A → uPred M) :
  ((∃ x : A, Ψ x) → P) ⊣⊢ ∀ x : A, Ψ x → P.
Proof.
  apply equiv_spec; split.
  - apply forall_intro=>x. by rewrite -exist_intro.
  - apply impl_intro_r, impl_elim_r', exist_elim=>x.
    apply impl_intro_r. by rewrite (forall_elim x) impl_elim_r.
Qed.

Lemma or_and_l P Q R : P ∨ Q ∧ R ⊣⊢ (P ∨ Q) ∧ (P ∨ R).
Proof.
  apply (anti_symm (⊢)); first auto.
  do 2 (apply impl_elim_l', or_elim; apply impl_intro_l); auto.
Qed.
Lemma or_and_r P Q R : P ∧ Q ∨ R ⊣⊢ (P ∨ R) ∧ (Q ∨ R).
Proof. by rewrite -!(comm _ R) or_and_l. Qed.
Lemma and_or_l P Q R : P ∧ (Q ∨ R) ⊣⊢ P ∧ Q ∨ P ∧ R.
Proof.
  apply (anti_symm (⊢)); last auto.
  apply impl_elim_r', or_elim; apply impl_intro_l; auto.
Qed.
Lemma and_or_r P Q R : (P ∨ Q) ∧ R ⊣⊢ P ∧ R ∨ Q ∧ R.
Proof. by rewrite -!(comm _ R) and_or_l. Qed.
Lemma and_exist_l {A} P (Ψ : A → uPred M) : P ∧ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∧ Ψ a.
Proof.
  apply (anti_symm (⊢)).
  - apply impl_elim_r'. apply exist_elim=>a. apply impl_intro_l.
    by rewrite -(exist_intro a).
  - apply exist_elim=>a. apply and_intro; first by rewrite and_elim_l.
    by rewrite -(exist_intro a) and_elim_r.
Qed.
Lemma and_exist_r {A} P (Φ: A → uPred M) : (∃ a, Φ a) ∧ P ⊣⊢ ∃ a, Φ a ∧ P.
Proof.
  rewrite -(comm _ P) and_exist_l. apply exist_proper=>a. by rewrite comm.
Qed.
Lemma or_exist {A} (Φ Ψ : A → uPred M) :
  (∃ a, Φ a ∨ Ψ a) ⊣⊢ (∃ a, Φ a) ∨ (∃ a, Ψ a).
Proof.
  apply (anti_symm (⊢)).
  - apply exist_elim=> a. by rewrite -!(exist_intro a).
  - apply or_elim; apply exist_elim=> a; rewrite -(exist_intro a); auto.
Qed.

Lemma pure_elim φ Q R : (Q ⊢ ⌜φ⌝) → (φ → Q ⊢ R) → Q ⊢ R.
Proof.
  intros HQ HQR. rewrite -(idemp uPred_and Q) {1}HQ.
  apply impl_elim_l', pure_elim'=> ?. by apply entails_impl, HQR.
Qed.
Lemma pure_mono φ1 φ2 : (φ1 → φ2) → ⌜φ1⌝ ⊢ ⌜φ2⌝.
Proof. intros; apply pure_elim with φ1; eauto. Qed.
Global Instance pure_mono' : Proper (impl ==> (⊢)) (@uPred_pure M).
Proof. intros φ1 φ2; apply pure_mono. Qed.
Global Instance pure_flip_mono : Proper (flip impl ==> flip (⊢)) (@uPred_pure M).
Proof. intros φ1 φ2; apply pure_mono. Qed.
Lemma pure_iff φ1 φ2 : (φ1 ↔ φ2) → ⌜φ1⌝ ⊣⊢ ⌜φ2⌝.
Proof. intros [??]; apply (anti_symm _); auto using pure_mono. Qed.
Lemma pure_intro_l φ Q R : φ → (⌜φ⌝ ∧ Q ⊢ R) → Q ⊢ R.
Proof. intros ? <-; auto using pure_intro. Qed.
Lemma pure_intro_r φ Q R : φ → (Q ∧ ⌜φ⌝ ⊢ R) → Q ⊢ R.
Proof. intros ? <-; auto. Qed.
Lemma pure_intro_impl φ Q R : φ → (Q ⊢ ⌜φ⌝ → R) → Q ⊢ R.
Proof. intros ? ->. eauto using pure_intro_l, impl_elim_r. Qed.
Lemma pure_elim_l φ Q R : (φ → Q ⊢ R) → ⌜φ⌝ ∧ Q ⊢ R.
Proof. intros; apply pure_elim with φ; eauto. Qed.
Lemma pure_elim_r φ Q R : (φ → Q ⊢ R) → Q ∧ ⌜φ⌝ ⊢ R.
Proof. intros; apply pure_elim with φ; eauto. Qed.

Lemma pure_True (φ : Prop) : φ → ⌜φ⌝ ⊣⊢ True.
Proof. intros; apply (anti_symm _); auto. Qed.
Lemma pure_False (φ : Prop) : ¬φ → ⌜φ⌝ ⊣⊢ False.
Proof. intros; apply (anti_symm _); eauto using pure_elim. Qed.

Lemma pure_and φ1 φ2 : ⌜φ1 ∧ φ2⌝ ⊣⊢ ⌜φ1⌝ ∧ ⌜φ2⌝.
Proof.
  apply (anti_symm _).
  - eapply pure_elim=> // -[??]; auto.
  - eapply (pure_elim φ1); [auto|]=> ?. eapply (pure_elim φ2); auto.
Qed.
Lemma pure_or φ1 φ2 : ⌜φ1 ∨ φ2⌝ ⊣⊢ ⌜φ1⌝ ∨ ⌜φ2⌝.
Proof.
  apply (anti_symm _).
  - eapply pure_elim=> // -[?|?]; auto.
  - apply or_elim; eapply pure_elim; eauto.
Qed.
Lemma pure_impl φ1 φ2 : ⌜φ1 → φ2⌝ ⊣⊢ (⌜φ1⌝ → ⌜φ2⌝).
Proof.
  apply (anti_symm _).
  - apply impl_intro_l. rewrite -pure_and. apply pure_mono. naive_solver.
  - rewrite -pure_forall_2. apply forall_intro=> ?.
    by rewrite -(left_id True uPred_and (_→_))%I (pure_True φ1) // impl_elim_r.
Qed.
Lemma pure_forall {A} (φ : A → Prop) : ⌜∀ x, φ x⌝ ⊣⊢ ∀ x, ⌜φ x⌝.
Proof.
  apply (anti_symm _); auto using pure_forall_2.
  apply forall_intro=> x. eauto using pure_mono.
Qed.
Lemma pure_exist {A} (φ : A → Prop) : ⌜∃ x, φ x⌝ ⊣⊢ ∃ x, ⌜φ x⌝.
Proof.
  apply (anti_symm _).
  - eapply pure_elim=> // -[x ?]. rewrite -(exist_intro x); auto.
  - apply exist_elim=> x. eauto using pure_mono.
Qed.

Lemma internal_eq_refl' {A : ofeT} (a : A) P : P ⊢ a ≡ a.
Proof. rewrite (True_intro P). apply internal_eq_refl. Qed.
Hint Resolve internal_eq_refl'.
Lemma equiv_internal_eq {A : ofeT} P (a b : A) : a ≡ b → P ⊢ a ≡ b.
Proof. by intros ->. Qed.
Lemma internal_eq_sym {A : ofeT} (a b : A) : a ≡ b ⊢ b ≡ a.
Proof. apply (internal_eq_rewrite a b (λ b, b ≡ a)%I); auto. solve_proper. Qed.
Lemma internal_eq_rewrite_contractive {A : ofeT} a b (Ψ : A → uPred M) P
  {HΨ : Contractive Ψ} : (P ⊢ ▷ (a ≡ b)) → (P ⊢ Ψ a) → P ⊢ Ψ b.
Proof.
  move: HΨ=> /contractiveI HΨ Heq ?.
  apply (internal_eq_rewrite (Ψ a) (Ψ b) id _)=>//=. by rewrite -HΨ.
Qed.

Lemma pure_impl_forall φ P : (⌜φ⌝ → P) ⊣⊢ (∀ _ : φ, P).
Proof.
  apply (anti_symm _).
  - apply forall_intro=> ?. by rewrite pure_True // left_id.
  - apply impl_intro_l, pure_elim_l=> Hφ. by rewrite (forall_elim Hφ).
Qed.
Lemma pure_alt φ : ⌜φ⌝ ⊣⊢ ∃ _ : φ, True.
Proof.
  apply (anti_symm _).
  - eapply pure_elim; eauto=> H. rewrite -(exist_intro H); auto.
  - by apply exist_elim, pure_intro.
Qed.
Lemma and_alt P Q : P ∧ Q ⊣⊢ ∀ b : bool, if b then P else Q.
Proof.
  apply (anti_symm _); first apply forall_intro=> -[]; auto.
  apply and_intro. by rewrite (forall_elim true). by rewrite (forall_elim false).
Qed.
Lemma or_alt P Q : P ∨ Q ⊣⊢ ∃ b : bool, if b then P else Q.
Proof.
  apply (anti_symm _); last apply exist_elim=> -[]; auto.
  apply or_elim. by rewrite -(exist_intro true). by rewrite -(exist_intro false).
Qed.

Global Instance iff_ne : NonExpansive2 (@uPred_iff M).
Proof. unfold uPred_iff; solve_proper. Qed.
Global Instance iff_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@uPred_iff M) := ne_proper_2 _.

Lemma iff_refl Q P : Q ⊢ P ↔ P.
Proof. rewrite /uPred_iff; apply and_intro; apply impl_intro_l; auto. Qed.
Lemma iff_equiv P Q : (P ↔ Q)%I → (P ⊣⊢ Q).
Proof.
  intros HPQ; apply (anti_symm (⊢));
    apply impl_entails; rewrite /uPred_valid HPQ /uPred_iff; auto.
Qed.
Lemma equiv_iff P Q : (P ⊣⊢ Q) → (P ↔ Q)%I.
Proof. intros ->; apply iff_refl. Qed.
Lemma internal_eq_iff P Q : P ≡ Q ⊢ P ↔ Q.
Proof.
  apply (internal_eq_rewrite P Q (λ Q, P ↔ Q))%I;
    first solve_proper; auto using iff_refl.
Qed.

(* Derived BI Stuff *)
Hint Resolve sep_mono.
Lemma sep_mono_l P P' Q : (P ⊢ Q) → P ∗ P' ⊢ Q ∗ P'.
Proof. by intros; apply sep_mono. Qed.
Lemma sep_mono_r P P' Q' : (P' ⊢ Q') → P ∗ P' ⊢ P ∗ Q'.
Proof. by apply sep_mono. Qed.
Global Instance sep_mono' : Proper ((⊢) ==> (⊢) ==> (⊢)) (@uPred_sep M).
Proof. by intros P P' HP Q Q' HQ; apply sep_mono. Qed.
Global Instance sep_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (@uPred_sep M).
Proof. by intros P P' HP Q Q' HQ; apply sep_mono. Qed.
Lemma wand_mono P P' Q Q' : (Q ⊢ P) → (P' ⊢ Q') → (P -∗ P') ⊢ Q -∗ Q'.
Proof.
  intros HP HQ; apply wand_intro_r. rewrite HP -HQ. by apply wand_elim_l'.
Qed.
Global Instance wand_mono' : Proper (flip (⊢) ==> (⊢) ==> (⊢)) (@uPred_wand M).
Proof. by intros P P' HP Q Q' HQ; apply wand_mono. Qed.
Global Instance wand_flip_mono' :
  Proper ((⊢) ==> flip (⊢) ==> flip (⊢)) (@uPred_wand M).
Proof. by intros P P' HP Q Q' HQ; apply wand_mono. Qed.

Global Instance sep_comm : Comm (⊣⊢) (@uPred_sep M).
Proof. intros P Q; apply (anti_symm _); auto using sep_comm'. Qed.
Global Instance sep_assoc : Assoc (⊣⊢) (@uPred_sep M).
Proof.
  intros P Q R; apply (anti_symm _); auto using sep_assoc'.
  by rewrite !(comm _ P) !(comm _ _ R) sep_assoc'.
Qed.
Global Instance True_sep : LeftId (⊣⊢) True%I (@uPred_sep M).
Proof. intros P; apply (anti_symm _); auto using True_sep_1, True_sep_2. Qed.
Global Instance sep_True : RightId (⊣⊢) True%I (@uPred_sep M).
Proof. by intros P; rewrite comm left_id. Qed.
Lemma sep_elim_l P Q : P ∗ Q ⊢ P.
Proof. by rewrite (True_intro Q) right_id. Qed.
Lemma sep_elim_r P Q : P ∗ Q ⊢ Q.
Proof. by rewrite (comm (∗))%I; apply sep_elim_l. Qed.
Lemma sep_elim_l' P Q R : (P ⊢ R) → P ∗ Q ⊢ R.
Proof. intros ->; apply sep_elim_l. Qed.
Lemma sep_elim_r' P Q R : (Q ⊢ R) → P ∗ Q ⊢ R.
Proof. intros ->; apply sep_elim_r. Qed.
Hint Resolve sep_elim_l' sep_elim_r'.
Lemma sep_intro_True_l P Q R : P%I → (R ⊢ Q) → R ⊢ P ∗ Q.
Proof. by intros; rewrite -(left_id True%I uPred_sep R); apply sep_mono. Qed.
Lemma sep_intro_True_r P Q R : (R ⊢ P) → Q%I → R ⊢ P ∗ Q.
Proof. by intros; rewrite -(right_id True%I uPred_sep R); apply sep_mono. Qed.
Lemma sep_elim_True_l P Q R : P → (P ∗ R ⊢ Q) → R ⊢ Q.
Proof. by intros HP; rewrite -HP left_id. Qed.
Lemma sep_elim_True_r P Q R : P → (R ∗ P ⊢ Q) → R ⊢ Q.
Proof. by intros HP; rewrite -HP right_id. Qed.
Lemma wand_intro_l P Q R : (Q ∗ P ⊢ R) → P ⊢ Q -∗ R.
Proof. rewrite comm; apply wand_intro_r. Qed.
Lemma wand_elim_l P Q : (P -∗ Q) ∗ P ⊢ Q.
Proof. by apply wand_elim_l'. Qed.
Lemma wand_elim_r P Q : P ∗ (P -∗ Q) ⊢ Q.
Proof. rewrite (comm _ P); apply wand_elim_l. Qed.
Lemma wand_elim_r' P Q R : (Q ⊢ P -∗ R) → P ∗ Q ⊢ R.
Proof. intros ->; apply wand_elim_r. Qed.
Lemma wand_apply P Q R S : (P ⊢ Q -∗ R) → (S ⊢ P ∗ Q) → S ⊢ R.
Proof. intros HR%wand_elim_l' HQ. by rewrite HQ. Qed.
Lemma wand_frame_l P Q R : (Q -∗ R) ⊢ P ∗ Q -∗ P ∗ R.
Proof. apply wand_intro_l. rewrite -assoc. apply sep_mono_r, wand_elim_r. Qed.
Lemma wand_frame_r P Q R : (Q -∗ R) ⊢ Q ∗ P -∗ R ∗ P.
Proof.
  apply wand_intro_l. rewrite ![(_ ∗ P)%I]comm -assoc.
  apply sep_mono_r, wand_elim_r.
Qed.
Lemma wand_diag P : (P -∗ P) ⊣⊢ True.
Proof. apply (anti_symm _); auto. apply wand_intro_l; by rewrite right_id. Qed.
Lemma wand_True P : (True -∗ P) ⊣⊢ P.
Proof.
  apply (anti_symm _); last by auto using wand_intro_l.
  eapply sep_elim_True_l; last by apply wand_elim_r. done.
Qed.
Lemma wand_entails P Q : (P -∗ Q)%I → P ⊢ Q.
Proof.
  intros HPQ. eapply sep_elim_True_r; first exact: HPQ. by rewrite wand_elim_r.
Qed.
Lemma entails_wand P Q : (P ⊢ Q) → (P -∗ Q)%I.
Proof. intro. apply wand_intro_l. auto. Qed.
Lemma wand_curry P Q R : (P -∗ Q -∗ R) ⊣⊢ (P ∗ Q -∗ R).
Proof.
  apply (anti_symm _).
  - apply wand_intro_l. by rewrite (comm _ P) -assoc !wand_elim_r.
  - do 2 apply wand_intro_l. by rewrite assoc (comm _ Q) wand_elim_r.
Qed.

Lemma sep_and P Q : (P ∗ Q) ⊢ (P ∧ Q).
Proof. auto. Qed.
Lemma impl_wand P Q : (P → Q) ⊢ P -∗ Q.
Proof. apply wand_intro_r, impl_elim with P; auto. Qed.
Lemma pure_elim_sep_l φ Q R : (φ → Q ⊢ R) → ⌜φ⌝ ∗ Q ⊢ R.
Proof. intros; apply pure_elim with φ; eauto. Qed.
Lemma pure_elim_sep_r φ Q R : (φ → Q ⊢ R) → Q ∗ ⌜φ⌝ ⊢ R.
Proof. intros; apply pure_elim with φ; eauto. Qed.

Global Instance sep_False : LeftAbsorb (⊣⊢) False%I (@uPred_sep M).
Proof. intros P; apply (anti_symm _); auto. Qed.
Global Instance False_sep : RightAbsorb (⊣⊢) False%I (@uPred_sep M).
Proof. intros P; apply (anti_symm _); auto. Qed.

Lemma entails_equiv_and P Q : (P ⊣⊢ Q ∧ P) ↔ (P ⊢ Q).
Proof. split. by intros ->; auto. intros; apply (anti_symm _); auto. Qed.
Lemma sep_and_l P Q R : P ∗ (Q ∧ R) ⊢ (P ∗ Q) ∧ (P ∗ R).
Proof. auto. Qed.
Lemma sep_and_r P Q R : (P ∧ Q) ∗ R ⊢ (P ∗ R) ∧ (Q ∗ R).
Proof. auto. Qed.
Lemma sep_or_l P Q R : P ∗ (Q ∨ R) ⊣⊢ (P ∗ Q) ∨ (P ∗ R).
Proof.
  apply (anti_symm (⊢)); last by eauto 8.
  apply wand_elim_r', or_elim; apply wand_intro_l; auto.
Qed.
Lemma sep_or_r P Q R : (P ∨ Q) ∗ R ⊣⊢ (P ∗ R) ∨ (Q ∗ R).
Proof. by rewrite -!(comm _ R) sep_or_l. Qed.
Lemma sep_exist_l {A} P (Ψ : A → uPred M) : P ∗ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∗ Ψ a.
Proof.
  intros; apply (anti_symm (⊢)).
  - apply wand_elim_r', exist_elim=>a. apply wand_intro_l.
    by rewrite -(exist_intro a).
  - apply exist_elim=> a; apply sep_mono; auto using exist_intro.
Qed.
Lemma sep_exist_r {A} (Φ: A → uPred M) Q: (∃ a, Φ a) ∗ Q ⊣⊢ ∃ a, Φ a ∗ Q.
Proof. setoid_rewrite (comm _ _ Q); apply sep_exist_l. Qed.
Lemma sep_forall_l {A} P (Ψ : A → uPred M) : P ∗ (∀ a, Ψ a) ⊢ ∀ a, P ∗ Ψ a.
Proof. by apply forall_intro=> a; rewrite forall_elim. Qed.
Lemma sep_forall_r {A} (Φ : A → uPred M) Q : (∀ a, Φ a) ∗ Q ⊢ ∀ a, Φ a ∗ Q.
Proof. by apply forall_intro=> a; rewrite forall_elim. Qed.

(* Always derived *)
Hint Resolve always_mono always_elim.
Global Instance always_mono' : Proper ((⊢) ==> (⊢)) (@uPred_always M).
Proof. intros P Q; apply always_mono. Qed.
Global Instance always_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@uPred_always M).
Proof. intros P Q; apply always_mono. Qed.

Lemma always_intro' P Q : (□ P ⊢ Q) → □ P ⊢ □ Q.
Proof. intros <-. apply always_idemp_2. Qed.
Lemma always_idemp P : □ □ P ⊣⊢ □ P.
Proof. apply (anti_symm _); auto using always_idemp_2. Qed.

Lemma always_pure φ : □ ⌜φ⌝ ⊣⊢ ⌜φ⌝.
Proof.
  apply (anti_symm _); auto.
  apply pure_elim'=> Hφ.
  trans (∀ x : False, □ True : uPred M)%I; [by apply forall_intro|].
  rewrite always_forall_2. auto using always_mono, pure_intro.
Qed.
Lemma always_forall {A} (Ψ : A → uPred M) : (□ ∀ a, Ψ a) ⊣⊢ (∀ a, □ Ψ a).
Proof.
  apply (anti_symm _); auto using always_forall_2.
  apply forall_intro=> x. by rewrite (forall_elim x).
Qed.
Lemma always_exist {A} (Ψ : A → uPred M) : (□ ∃ a, Ψ a) ⊣⊢ (∃ a, □ Ψ a).
Proof.
  apply (anti_symm _); auto using always_exist_1.
  apply exist_elim=> x. by rewrite (exist_intro x).
Qed.
Lemma always_and P Q : □ (P ∧ Q) ⊣⊢ □ P ∧ □ Q.
Proof. rewrite !and_alt always_forall. by apply forall_proper=> -[]. Qed.
Lemma always_or P Q : □ (P ∨ Q) ⊣⊢ □ P ∨ □ Q.
Proof. rewrite !or_alt always_exist. by apply exist_proper=> -[]. Qed.
Lemma always_impl P Q : □ (P → Q) ⊢ □ P → □ Q.
Proof.
  apply impl_intro_l; rewrite -always_and.
  apply always_mono, impl_elim with P; auto.
Qed.
Lemma always_internal_eq {A:ofeT} (a b : A) : □ (a ≡ b) ⊣⊢ a ≡ b.
Proof.
  apply (anti_symm (⊢)); auto using always_elim.
  apply (internal_eq_rewrite a b (λ b, □ (a ≡ b))%I); auto.
  { intros n; solve_proper. }
  rewrite -(internal_eq_refl a) always_pure; auto.
Qed.

Lemma always_and_sep_l' P Q : □ P ∧ Q ⊣⊢ □ P ∗ Q.
Proof. apply (anti_symm (⊢)); auto using always_and_sep_l_1. Qed.
Lemma always_and_sep_r' P Q : P ∧ □ Q ⊣⊢ P ∗ □ Q.
Proof. by rewrite !(comm _ P) always_and_sep_l'. Qed.
Lemma always_sep_dup' P : □ P ⊣⊢ □ P ∗ □ P.
Proof. by rewrite -always_and_sep_l' idemp. Qed.

Lemma always_and_sep P Q : □ (P ∧ Q) ⊣⊢ □ (P ∗ Q).
Proof.
  apply (anti_symm (⊢)); auto.
  rewrite -{1}always_idemp always_and always_and_sep_l'; auto.
Qed.
Lemma always_sep P Q : □ (P ∗ Q) ⊣⊢ □ P ∗ □ Q.
Proof. by rewrite -always_and_sep -always_and_sep_l' always_and. Qed.

Lemma always_wand P Q : □ (P -∗ Q) ⊢ □ P -∗ □ Q.
Proof. by apply wand_intro_r; rewrite -always_sep wand_elim_l. Qed.
Lemma always_wand_impl P Q : □ (P -∗ Q) ⊣⊢ □ (P → Q).
Proof.
  apply (anti_symm (⊢)); [|by rewrite -impl_wand].
  apply always_intro', impl_intro_r.
  by rewrite always_and_sep_l' always_elim wand_elim_l.
Qed.
Lemma always_entails_l' P Q : (P ⊢ □ Q) → P ⊢ □ Q ∗ P.
Proof. intros; rewrite -always_and_sep_l'; auto. Qed.
Lemma always_entails_r' P Q : (P ⊢ □ Q) → P ⊢ P ∗ □ Q.
Proof. intros; rewrite -always_and_sep_r'; auto. Qed.

Lemma always_laterN n P : □ ▷^n P ⊣⊢ ▷^n □ P.
Proof. induction n as [|n IH]; simpl; auto. by rewrite always_later IH. Qed.

Lemma wand_alt P Q : (P -∗ Q) ⊣⊢ ∃ R, R ∗ □ (P ∗ R → Q).
Proof.
  apply (anti_symm (⊢)).
  - rewrite -(right_id True%I uPred_sep (P -∗ Q)%I) -(exist_intro (P -∗ Q)%I).
    apply sep_mono_r. rewrite -always_pure. apply always_mono, impl_intro_l.
    by rewrite wand_elim_r right_id.
  - apply exist_elim=> R. apply wand_intro_l. rewrite assoc -always_and_sep_r'.
    by rewrite always_elim impl_elim_r.
Qed.
Lemma impl_alt P Q : (P → Q) ⊣⊢ ∃ R, R ∧ □ (P ∧ R -∗ Q).
Proof.
  apply (anti_symm (⊢)).
  - rewrite -(right_id True%I uPred_and (P → Q)%I) -(exist_intro (P → Q)%I).
    apply and_mono_r. rewrite -always_pure. apply always_mono, wand_intro_l.
    by rewrite impl_elim_r right_id.
  - apply exist_elim=> R. apply impl_intro_l. rewrite assoc always_and_sep_r'.
    by rewrite always_elim wand_elim_r.
Qed.

(* Later derived *)
Lemma later_proper P Q : (P ⊣⊢ Q) → ▷ P ⊣⊢ ▷ Q.
Proof. by intros ->. Qed.
Hint Resolve later_mono later_proper.
Global Instance later_mono' : Proper ((⊢) ==> (⊢)) (@uPred_later M).
Proof. intros P Q; apply later_mono. Qed.
Global Instance later_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@uPred_later M).
Proof. intros P Q; apply later_mono. Qed.

Lemma later_intro P : P ⊢ ▷ P.
Proof.
  rewrite -(and_elim_l (▷ P) P) -(löb (▷ P ∧ P)).
  apply impl_intro_l. by rewrite {1}(and_elim_r (▷ P)).
Qed.

Lemma later_True : ▷ True ⊣⊢ True.
Proof. apply (anti_symm (⊢)); auto using later_intro. Qed.
Lemma later_forall {A} (Φ : A → uPred M) : (▷ ∀ a, Φ a) ⊣⊢ (∀ a, ▷ Φ a).
Proof.
  apply (anti_symm _); auto using later_forall_2.
  apply forall_intro=> x. by rewrite (forall_elim x).
Qed.
Lemma later_exist `{Inhabited A} (Φ : A → uPred M) :
  ▷ (∃ a, Φ a) ⊣⊢ (∃ a, ▷ Φ a).
Proof.
  apply: anti_symm; [|apply exist_elim; eauto using exist_intro].
  rewrite later_exist_false. apply or_elim; last done.
  rewrite -(exist_intro inhabitant); auto.
Qed.
Lemma later_and P Q : ▷ (P ∧ Q) ⊣⊢ ▷ P ∧ ▷ Q.
Proof. rewrite !and_alt later_forall. by apply forall_proper=> -[]. Qed.
Lemma later_or P Q : ▷ (P ∨ Q) ⊣⊢ ▷ P ∨ ▷ Q.
Proof. rewrite !or_alt later_exist. by apply exist_proper=> -[]. Qed.
Lemma later_impl P Q : ▷ (P → Q) ⊢ ▷ P → ▷ Q.
Proof. apply impl_intro_l; rewrite -later_and; eauto using impl_elim. Qed.
Lemma later_wand P Q : ▷ (P -∗ Q) ⊢ ▷ P -∗ ▷ Q.
Proof. apply wand_intro_r; rewrite -later_sep; eauto using wand_elim_l. Qed.
Lemma later_iff P Q : ▷ (P ↔ Q) ⊢ ▷ P ↔ ▷ Q.
Proof. by rewrite /uPred_iff later_and !later_impl. Qed.


(* Iterated later modality *)
Global Instance laterN_ne m : NonExpansive (@uPred_laterN M m).
Proof. induction m; simpl. by intros ???. solve_proper. Qed.
Global Instance laterN_proper m :
  Proper ((⊣⊢) ==> (⊣⊢)) (@uPred_laterN M m) := ne_proper _.

Lemma laterN_0 P : ▷^0 P ⊣⊢ P.
Proof. done. Qed.
Lemma later_laterN n P : ▷^(S n) P ⊣⊢ ▷ ▷^n P.
Proof. done. Qed.
Lemma laterN_later n P : ▷^(S n) P ⊣⊢ ▷^n ▷ P.
Proof. induction n; simpl; auto. Qed.
Lemma laterN_plus n1 n2 P : ▷^(n1 + n2) P ⊣⊢ ▷^n1 ▷^n2 P.
Proof. induction n1; simpl; auto. Qed.
Lemma laterN_le n1 n2 P : n1 ≤ n2 → ▷^n1 P ⊢ ▷^n2 P.
Proof. induction 1; simpl; by rewrite -?later_intro. Qed.

Lemma laterN_mono n P Q : (P ⊢ Q) → ▷^n P ⊢ ▷^n Q.
Proof. induction n; simpl; auto. Qed.
Global Instance laterN_mono' n : Proper ((⊢) ==> (⊢)) (@uPred_laterN M n).
Proof. intros P Q; apply laterN_mono. Qed.
Global Instance laterN_flip_mono' n :
  Proper (flip (⊢) ==> flip (⊢)) (@uPred_laterN M n).
Proof. intros P Q; apply laterN_mono. Qed.

Lemma laterN_intro n P : P ⊢ ▷^n P.
Proof. induction n as [|n IH]; simpl; by rewrite -?later_intro. Qed.

Lemma laterN_True n : ▷^n True ⊣⊢ True.
Proof. apply (anti_symm (⊢)); auto using laterN_intro. Qed.
Lemma laterN_forall {A} n (Φ : A → uPred M) : (▷^n ∀ a, Φ a) ⊣⊢ (∀ a, ▷^n Φ a).
Proof. induction n as [|n IH]; simpl; rewrite -?later_forall; auto. Qed.
Lemma laterN_exist `{Inhabited A} n (Φ : A → uPred M) :
  (▷^n ∃ a, Φ a) ⊣⊢ ∃ a, ▷^n Φ a.
Proof. induction n as [|n IH]; simpl; rewrite -?later_exist; auto. Qed.
Lemma laterN_and n P Q : ▷^n (P ∧ Q) ⊣⊢ ▷^n P ∧ ▷^n Q.
Proof. induction n as [|n IH]; simpl; rewrite -?later_and; auto. Qed.
Lemma laterN_or n P Q : ▷^n (P ∨ Q) ⊣⊢ ▷^n P ∨ ▷^n Q.
Proof. induction n as [|n IH]; simpl; rewrite -?later_or; auto. Qed.
Lemma laterN_impl n P Q : ▷^n (P → Q) ⊢ ▷^n P → ▷^n Q.
Proof.
  apply impl_intro_l; rewrite -laterN_and; eauto using impl_elim, laterN_mono.
Qed.
Lemma laterN_sep n P Q : ▷^n (P ∗ Q) ⊣⊢ ▷^n P ∗ ▷^n Q.
Proof. induction n as [|n IH]; simpl; rewrite -?later_sep; auto. Qed.
Lemma laterN_wand n P Q : ▷^n (P -∗ Q) ⊢ ▷^n P -∗ ▷^n Q.
Proof.
  apply wand_intro_r; rewrite -laterN_sep; eauto using wand_elim_l,laterN_mono.
Qed.
Lemma laterN_iff n P Q : ▷^n (P ↔ Q) ⊢ ▷^n P ↔ ▷^n Q.
Proof. by rewrite /uPred_iff laterN_and !laterN_impl. Qed.

(* Conditional always *)
Global Instance always_if_ne p : NonExpansive (@uPred_always_if M p).
Proof. solve_proper. Qed.
Global Instance always_if_proper p : Proper ((⊣⊢) ==> (⊣⊢)) (@uPred_always_if M p).
Proof. solve_proper. Qed.
Global Instance always_if_mono p : Proper ((⊢) ==> (⊢)) (@uPred_always_if M p).
Proof. solve_proper. Qed.

Lemma always_if_elim p P : □?p P ⊢ P.
Proof. destruct p; simpl; auto using always_elim. Qed.
Lemma always_elim_if p P : □ P ⊢ □?p P.
Proof. destruct p; simpl; auto using always_elim. Qed.

Lemma always_if_pure p φ : □?p ⌜φ⌝ ⊣⊢ ⌜φ⌝.
Proof. destruct p; simpl; auto using always_pure. Qed.
Lemma always_if_and p P Q : □?p (P ∧ Q) ⊣⊢ □?p P ∧ □?p Q.
Proof. destruct p; simpl; auto using always_and. Qed.
Lemma always_if_or p P Q : □?p (P ∨ Q) ⊣⊢ □?p P ∨ □?p Q.
Proof. destruct p; simpl; auto using always_or. Qed.
Lemma always_if_exist {A} p (Ψ : A → uPred M) : (□?p ∃ a, Ψ a) ⊣⊢ ∃ a, □?p Ψ a.
Proof. destruct p; simpl; auto using always_exist. Qed.
Lemma always_if_sep p P Q : □?p (P ∗ Q) ⊣⊢ □?p P ∗ □?p Q.
Proof. destruct p; simpl; auto using always_sep. Qed.
Lemma always_if_later p P : □?p ▷ P ⊣⊢ ▷ □?p P.
Proof. destruct p; simpl; auto using always_later. Qed.
Lemma always_if_laterN p n P : □?p ▷^n P ⊣⊢ ▷^n □?p P.
Proof. destruct p; simpl; auto using always_laterN. Qed.

(* True now *)
Global Instance except_0_ne : NonExpansive (@uPred_except_0 M).
Proof. solve_proper. Qed.
Global Instance except_0_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@uPred_except_0 M).
Proof. solve_proper. Qed.
Global Instance except_0_mono' : Proper ((⊢) ==> (⊢)) (@uPred_except_0 M).
Proof. solve_proper. Qed.
Global Instance except_0_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@uPred_except_0 M).
Proof. solve_proper. Qed.

Lemma except_0_intro P : P ⊢ ◇ P.
Proof. rewrite /uPred_except_0; auto. Qed.
Lemma except_0_mono P Q : (P ⊢ Q) → ◇ P ⊢ ◇ Q.
Proof. by intros ->. Qed.
Lemma except_0_idemp P : ◇ ◇ P ⊢ ◇ P.
Proof. rewrite /uPred_except_0; auto. Qed.

Lemma except_0_True : ◇ True ⊣⊢ True.
Proof. rewrite /uPred_except_0. apply (anti_symm _); auto. Qed.
Lemma except_0_or P Q : ◇ (P ∨ Q) ⊣⊢ ◇ P ∨ ◇ Q.
Proof. rewrite /uPred_except_0. apply (anti_symm _); auto. Qed.
Lemma except_0_and P Q : ◇ (P ∧ Q) ⊣⊢ ◇ P ∧ ◇ Q.
Proof. by rewrite /uPred_except_0 or_and_l. Qed.
Lemma except_0_sep P Q : ◇ (P ∗ Q) ⊣⊢ ◇ P ∗ ◇ Q.
Proof.
  rewrite /uPred_except_0. apply (anti_symm _).
  - apply or_elim; last by auto.
    by rewrite -!or_intro_l -always_pure -always_later -always_sep_dup'.
  - rewrite sep_or_r sep_elim_l sep_or_l; auto.
Qed.
Lemma except_0_forall {A} (Φ : A → uPred M) : ◇ (∀ a, Φ a) ⊢ ∀ a, ◇ Φ a.
Proof. apply forall_intro=> a. by rewrite (forall_elim a). Qed.
Lemma except_0_exist_2 {A} (Φ : A → uPred M) : (∃ a, ◇ Φ a) ⊢ ◇ ∃ a, Φ a.
Proof. apply exist_elim=> a. by rewrite (exist_intro a). Qed.
Lemma except_0_exist `{Inhabited A} (Φ : A → uPred M) :
  ◇ (∃ a, Φ a) ⊣⊢ (∃ a, ◇ Φ a).
Proof.
  apply (anti_symm _); [|by apply except_0_exist_2]. apply or_elim.
  - rewrite -(exist_intro inhabitant). by apply or_intro_l.
  - apply exist_mono=> a. apply except_0_intro.
Qed.
Lemma except_0_later P : ◇ ▷ P ⊢ ▷ P.
Proof. by rewrite /uPred_except_0 -later_or False_or. Qed.
Lemma except_0_always P : ◇ □ P ⊣⊢ □ ◇ P.
Proof. by rewrite /uPred_except_0 always_or always_later always_pure. Qed.
Lemma except_0_always_if p P : ◇ □?p P ⊣⊢ □?p ◇ P.
Proof. destruct p; simpl; auto using except_0_always. Qed.
Lemma except_0_frame_l P Q : P ∗ ◇ Q ⊢ ◇ (P ∗ Q).
Proof. by rewrite {1}(except_0_intro P) except_0_sep. Qed.
Lemma except_0_frame_r P Q : ◇ P ∗ Q ⊢ ◇ (P ∗ Q).
Proof. by rewrite {1}(except_0_intro Q) except_0_sep. Qed.

(* Own and valid derived *)
Lemma always_ownM (a : M) : Persistent a → □ uPred_ownM a ⊣⊢ uPred_ownM a.
Proof.
  intros; apply (anti_symm _); first by apply:always_elim.
  by rewrite {1}always_ownM_core persistent_core.
Qed.
Lemma ownM_invalid (a : M) : ¬ ✓{0} a → uPred_ownM a ⊢ False.
Proof. by intros; rewrite ownM_valid cmra_valid_elim. Qed.
Global Instance ownM_mono : Proper (flip (≼) ==> (⊢)) (@uPred_ownM M).
Proof. intros a b [b' ->]. rewrite ownM_op. eauto. Qed.
Lemma ownM_empty' : uPred_ownM ∅ ⊣⊢ True.
Proof. apply (anti_symm _); first by auto. apply ownM_empty. Qed.
Lemma always_cmra_valid {A : cmraT} (a : A) : □ ✓ a ⊣⊢ ✓ a.
Proof.
  intros; apply (anti_symm _); first by apply:always_elim.
  apply:always_cmra_valid_1.
Qed.

(** * Derived rules *)
Global Instance bupd_mono' : Proper ((⊢) ==> (⊢)) (@uPred_bupd M).
Proof. intros P Q; apply bupd_mono. Qed.
Global Instance bupd_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) (@uPred_bupd M).
Proof. intros P Q; apply bupd_mono. Qed.
Lemma bupd_frame_l R Q : (R ∗ |==> Q) ==∗ R ∗ Q.
Proof. rewrite !(comm _ R); apply bupd_frame_r. Qed.
Lemma bupd_wand_l P Q : (P -∗ Q) ∗ (|==> P) ==∗ Q.
Proof. by rewrite bupd_frame_l wand_elim_l. Qed.
Lemma bupd_wand_r P Q : (|==> P) ∗ (P -∗ Q) ==∗ Q.
Proof. by rewrite bupd_frame_r wand_elim_r. Qed.
Lemma bupd_sep P Q : (|==> P) ∗ (|==> Q) ==∗ P ∗ Q.
Proof. by rewrite bupd_frame_r bupd_frame_l bupd_trans. Qed.
Lemma bupd_ownM_update x y : x ~~> y → uPred_ownM x ⊢ |==> uPred_ownM y.
Proof.
  intros; rewrite (bupd_ownM_updateP _ (y =)); last by apply cmra_update_updateP.
  by apply bupd_mono, exist_elim=> y'; apply pure_elim_l=> ->.
Qed.
Lemma except_0_bupd P : ◇ (|==> P) ⊢ (|==> ◇ P).
Proof.
  rewrite /uPred_except_0. apply or_elim; auto using bupd_mono.
  by rewrite -bupd_intro -or_intro_l.
Qed.

(* Timeless instances *)
Global Instance TimelessP_proper : Proper ((≡) ==> iff) (@TimelessP M).
Proof. solve_proper. Qed.
Global Instance pure_timeless φ : TimelessP (⌜φ⌝ : uPred M)%I.
Proof.
  rewrite /TimelessP pure_alt later_exist_false. by setoid_rewrite later_True.
Qed.
Global Instance valid_timeless {A : cmraT} `{CMRADiscrete A} (a : A) :
  TimelessP (✓ a : uPred M)%I.
Proof. rewrite /TimelessP !discrete_valid. apply (timelessP _). Qed.
Global Instance and_timeless P Q: TimelessP P → TimelessP Q → TimelessP (P ∧ Q).
Proof. intros; rewrite /TimelessP except_0_and later_and; auto. Qed.
Global Instance or_timeless P Q : TimelessP P → TimelessP Q → TimelessP (P ∨ Q).
Proof. intros; rewrite /TimelessP except_0_or later_or; auto. Qed.
Global Instance impl_timeless P Q : TimelessP Q → TimelessP (P → Q).
Proof.
  rewrite /TimelessP=> HQ. rewrite later_false_excluded_middle.
  apply or_mono, impl_intro_l; first done.
  rewrite -{2}(löb Q); apply impl_intro_l.
  rewrite HQ /uPred_except_0 !and_or_r. apply or_elim; last auto.
  by rewrite assoc (comm _ _ P) -assoc !impl_elim_r.
Qed.
Global Instance sep_timeless P Q: TimelessP P → TimelessP Q → TimelessP (P ∗ Q).
Proof. intros; rewrite /TimelessP except_0_sep later_sep; auto. Qed.
Global Instance wand_timeless P Q : TimelessP Q → TimelessP (P -∗ Q).
Proof.
  rewrite /TimelessP=> HQ. rewrite later_false_excluded_middle.
  apply or_mono, wand_intro_l; first done.
  rewrite -{2}(löb Q); apply impl_intro_l.
  rewrite HQ /uPred_except_0 !and_or_r. apply or_elim; last auto.
  rewrite -(always_pure) -always_later always_and_sep_l'.
  by rewrite assoc (comm _ _ P) -assoc -always_and_sep_l' impl_elim_r wand_elim_r.
Qed.
Global Instance forall_timeless {A} (Ψ : A → uPred M) :
  (∀ x, TimelessP (Ψ x)) → TimelessP (∀ x, Ψ x).
Proof.
  rewrite /TimelessP=> HQ. rewrite later_false_excluded_middle.
  apply or_mono; first done. apply forall_intro=> x.
  rewrite -(löb (Ψ x)); apply impl_intro_l.
  rewrite HQ /uPred_except_0 !and_or_r. apply or_elim; last auto.
  by rewrite impl_elim_r (forall_elim x).
Qed.
Global Instance exist_timeless {A} (Ψ : A → uPred M) :
  (∀ x, TimelessP (Ψ x)) → TimelessP (∃ x, Ψ x).
Proof.
  rewrite /TimelessP=> ?. rewrite later_exist_false. apply or_elim.
  - rewrite /uPred_except_0; auto.
  - apply exist_elim=> x. rewrite -(exist_intro x); auto.
Qed.
Global Instance always_timeless P : TimelessP P → TimelessP (□ P).
Proof. intros; rewrite /TimelessP except_0_always -always_later; auto. Qed.
Global Instance always_if_timeless p P : TimelessP P → TimelessP (□?p P).
Proof. destruct p; apply _. Qed.
Global Instance eq_timeless {A : ofeT} (a b : A) :
  Timeless a → TimelessP (a ≡ b : uPred M)%I.
Proof. intros. rewrite /TimelessP !timeless_eq. apply (timelessP _). Qed.
Global Instance ownM_timeless (a : M) : Timeless a → TimelessP (uPred_ownM a).
Proof.
  intros ?. rewrite /TimelessP later_ownM. apply exist_elim=> b.
  rewrite (timelessP (a≡b)) (except_0_intro (uPred_ownM b)) -except_0_and.
  apply except_0_mono. rewrite internal_eq_sym.
  apply (internal_eq_rewrite b a (uPred_ownM)); first apply _; auto.
Qed.
Global Instance from_option_timeless {A} P (Ψ : A → uPred M) (mx : option A) :
  (∀ x, TimelessP (Ψ x)) → TimelessP P → TimelessP (from_option Ψ P mx).
Proof. destruct mx; apply _. Qed.

(* Derived lemmas for persistence *)
Global Instance PersistentP_proper : Proper ((≡) ==> iff) (@PersistentP M).
Proof. solve_proper. Qed.
Global Instance limit_preserving_PersistentP {A:ofeT} `{Cofe A} (Φ : A → uPred M) :
  NonExpansive Φ → LimitPreserving (λ x, PersistentP (Φ x)).
Proof. intros. apply limit_preserving_entails; solve_proper. Qed.

Lemma always_always P `{!PersistentP P} : □ P ⊣⊢ P.
Proof. apply (anti_symm (⊢)); auto using always_elim. Qed.
Lemma always_if_always p P `{!PersistentP P} : □?p P ⊣⊢ P.
Proof. destruct p; simpl; auto using always_always. Qed.
Lemma always_intro P Q `{!PersistentP P} : (P ⊢ Q) → P ⊢ □ Q.
Proof. rewrite -(always_always P); apply always_intro'. Qed.
Lemma always_and_sep_l P Q `{!PersistentP P} : P ∧ Q ⊣⊢ P ∗ Q.
Proof. by rewrite -(always_always P) always_and_sep_l'. Qed.
Lemma always_and_sep_r P Q `{!PersistentP Q} : P ∧ Q ⊣⊢ P ∗ Q.
Proof. by rewrite -(always_always Q) always_and_sep_r'. Qed.
Lemma always_sep_dup P `{!PersistentP P} : P ⊣⊢ P ∗ P.
Proof. by rewrite -(always_always P) -always_sep_dup'. Qed.
Lemma always_entails_l P Q `{!PersistentP Q} : (P ⊢ Q) → P ⊢ Q ∗ P.
Proof. by rewrite -(always_always Q); apply always_entails_l'. Qed.
Lemma always_entails_r P Q `{!PersistentP Q} : (P ⊢ Q) → P ⊢ P ∗ Q.
Proof. by rewrite -(always_always Q); apply always_entails_r'. Qed.
Lemma always_impl_wand P `{!PersistentP P} Q : (P → Q) ⊣⊢ (P -∗ Q).
Proof.
  apply (anti_symm _); auto using impl_wand.
  apply impl_intro_l. by rewrite always_and_sep_l wand_elim_r.
Qed.

(* Persistence *)
Global Instance pure_persistent φ : PersistentP (⌜φ⌝ : uPred M)%I.
Proof. by rewrite /PersistentP always_pure. Qed.
Global Instance pure_impl_persistent φ Q :
  PersistentP Q → PersistentP (⌜φ⌝ → Q)%I.
Proof.
  rewrite /PersistentP pure_impl_forall always_forall. auto using forall_mono.
Qed.
Global Instance pure_wand_persistent φ Q :
  PersistentP Q → PersistentP (⌜φ⌝ -∗ Q)%I.
Proof.
  rewrite /PersistentP -always_impl_wand pure_impl_forall always_forall.
  auto using forall_mono.
Qed.
Global Instance always_persistent P : PersistentP (□ P).
Proof. by intros; apply always_intro'. Qed.
Global Instance and_persistent P Q :
  PersistentP P → PersistentP Q → PersistentP (P ∧ Q).
Proof. by intros; rewrite /PersistentP always_and; apply and_mono. Qed.
Global Instance or_persistent P Q :
  PersistentP P → PersistentP Q → PersistentP (P ∨ Q).
Proof. by intros; rewrite /PersistentP always_or; apply or_mono. Qed.
Global Instance sep_persistent P Q :
  PersistentP P → PersistentP Q → PersistentP (P ∗ Q).
Proof. by intros; rewrite /PersistentP always_sep; apply sep_mono. Qed.
Global Instance forall_persistent {A} (Ψ : A → uPred M) :
  (∀ x, PersistentP (Ψ x)) → PersistentP (∀ x, Ψ x).
Proof. by intros; rewrite /PersistentP always_forall; apply forall_mono. Qed.
Global Instance exist_persistent {A} (Ψ : A → uPred M) :
  (∀ x, PersistentP (Ψ x)) → PersistentP (∃ x, Ψ x).
Proof. by intros; rewrite /PersistentP always_exist; apply exist_mono. Qed.
Global Instance internal_eq_persistent {A : ofeT} (a b : A) :
  PersistentP (a ≡ b : uPred M)%I.
Proof. by intros; rewrite /PersistentP always_internal_eq. Qed.
Global Instance cmra_valid_persistent {A : cmraT} (a : A) :
  PersistentP (✓ a : uPred M)%I.
Proof. by intros; rewrite /PersistentP always_cmra_valid. Qed.
Global Instance later_persistent P : PersistentP P → PersistentP (▷ P).
Proof. by intros; rewrite /PersistentP always_later; apply later_mono. Qed.
Global Instance laterN_persistent n P : PersistentP P → PersistentP (▷^n P).
Proof. induction n; apply _. Qed.
Global Instance ownM_persistent : Persistent a → PersistentP (@uPred_ownM M a).
Proof. intros. by rewrite /PersistentP always_ownM. Qed.
Global Instance from_option_persistent {A} P (Ψ : A → uPred M) (mx : option A) :
  (∀ x, PersistentP (Ψ x)) → PersistentP P → PersistentP (from_option Ψ P mx).
Proof. destruct mx; apply _. Qed.

(* For big ops *)
Global Instance uPred_and_monoid : Monoid (@uPred_and M) :=
  {| monoid_unit := True%I |}.
Global Instance uPred_or_monoid : Monoid (@uPred_or M) :=
  {| monoid_unit := False%I |}.
Global Instance uPred_sep_monoid : Monoid (@uPred_sep M) :=
  {| monoid_unit := True%I |}.

Global Instance uPred_always_and_homomorphism :
  MonoidHomomorphism uPred_and uPred_and (≡) (@uPred_always M).
Proof. split; [split; try apply _|]. apply always_and. apply always_pure. Qed.
Global Instance uPred_always_if_and_homomorphism b :
  MonoidHomomorphism uPred_and uPred_and (≡) (@uPred_always_if M b).
Proof. split; [split; try apply _|]. apply always_if_and. apply always_if_pure. Qed.
Global Instance uPred_later_monoid_and_homomorphism :
  MonoidHomomorphism uPred_and uPred_and (≡) (@uPred_later M).
Proof. split; [split; try apply _|]. apply later_and. apply later_True. Qed.
Global Instance uPred_laterN_and_homomorphism n :
  MonoidHomomorphism uPred_and uPred_and (≡) (@uPred_laterN M n).
Proof. split; [split; try apply _|]. apply laterN_and. apply laterN_True. Qed.
Global Instance uPred_except_0_and_homomorphism :
  MonoidHomomorphism uPred_and uPred_and (≡) (@uPred_except_0 M).
Proof. split; [split; try apply _|]. apply except_0_and. apply except_0_True. Qed.

Global Instance uPred_always_or_homomorphism :
  MonoidHomomorphism uPred_or uPred_or (≡) (@uPred_always M).
Proof. split; [split; try apply _|]. apply always_or. apply always_pure. Qed.
Global Instance uPred_always_if_or_homomorphism b :
  MonoidHomomorphism uPred_or uPred_or (≡) (@uPred_always_if M b).
Proof. split; [split; try apply _|]. apply always_if_or. apply always_if_pure. Qed.
Global Instance uPred_later_monoid_or_homomorphism :
  WeakMonoidHomomorphism uPred_or uPred_or (≡) (@uPred_later M).
Proof. split; try apply _. apply later_or. Qed.
Global Instance uPred_laterN_or_homomorphism n :
  WeakMonoidHomomorphism uPred_or uPred_or (≡) (@uPred_laterN M n).
Proof. split; try apply _. apply laterN_or. Qed.
Global Instance uPred_except_0_or_homomorphism :
  WeakMonoidHomomorphism uPred_or uPred_or (≡) (@uPred_except_0 M).
Proof. split; try apply _. apply except_0_or. Qed. 

Global Instance uPred_always_sep_homomorphism :
  MonoidHomomorphism uPred_sep uPred_sep (≡) (@uPred_always M).
Proof. split; [split; try apply _|]. apply always_sep. apply always_pure. Qed.
Global Instance uPred_always_if_sep_homomorphism b :
  MonoidHomomorphism uPred_sep uPred_sep (≡) (@uPred_always_if M b).
Proof. split; [split; try apply _|]. apply always_if_sep. apply always_if_pure. Qed.
Global Instance uPred_later_monoid_sep_homomorphism :
  MonoidHomomorphism uPred_sep uPred_sep (≡) (@uPred_later M).
Proof. split; [split; try apply _|]. apply later_sep. apply later_True. Qed.
Global Instance uPred_laterN_sep_homomorphism n :
  MonoidHomomorphism uPred_sep uPred_sep (≡) (@uPred_laterN M n).
Proof. split; [split; try apply _|]. apply laterN_sep. apply laterN_True. Qed.
Global Instance uPred_except_0_sep_homomorphism :
  MonoidHomomorphism uPred_sep uPred_sep (≡) (@uPred_except_0 M).
Proof. split; [split; try apply _|]. apply except_0_sep. apply except_0_True. Qed.
Global Instance uPred_ownM_sep_homomorphism :
  MonoidHomomorphism op uPred_sep (≡) (@uPred_ownM M).
Proof. split; [split; try apply _|]. apply ownM_op. apply ownM_empty'. Qed.
End derived.
End uPred.
