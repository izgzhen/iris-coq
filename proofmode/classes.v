From iris.algebra Require Export upred.
From iris.algebra Require Import upred_big_op gmap upred_tactics.
Import uPred.

Section classes.
Context {M : ucmraT}.
Implicit Types P Q : uPred M.

Class FromAssumption (p : bool) (P Q : uPred M) := from_assumption : □?p P ⊢ Q.
Global Arguments from_assumption _ _ _ {_}.
Global Instance from_assumption_exact p P : FromAssumption p P P.
Proof. destruct p; by rewrite /FromAssumption /= ?always_elim. Qed.
Global Instance from_assumption_always_l p P Q :
  FromAssumption p P Q → FromAssumption p (□ P) Q.
Proof. rewrite /FromAssumption=><-. by rewrite always_elim. Qed.
Global Instance from_assumption_always_r P Q :
  FromAssumption true P Q → FromAssumption true P (□ Q).
Proof. rewrite /FromAssumption=><-. by rewrite always_always. Qed.

Class IntoPure (P : uPred M) (φ : Prop) := into_pure : P ⊢ ■ φ.
Global Arguments into_pure : clear implicits.
Global Instance into_pure_pure φ : IntoPure (■ φ) φ.
Proof. done. Qed.
Global Instance into_pure_eq {A : cofeT} (a b : A) :
  Timeless a → IntoPure (a ≡ b) (a ≡ b).
Proof. intros. by rewrite /IntoPure timeless_eq. Qed.
Global Instance into_pure_valid `{CMRADiscrete A} (a : A) : IntoPure (✓ a) (✓ a).
Proof. by rewrite /IntoPure discrete_valid. Qed.

Class FromPure (P : uPred M) (φ : Prop) := from_pure : φ → True ⊢ P.
Global Arguments from_pure : clear implicits.
Global Instance from_pure_pure φ : FromPure (■ φ) φ.
Proof. intros ?. by apply pure_intro. Qed.
Global Instance from_pure_eq {A : cofeT} (a b : A) : FromPure (a ≡ b) (a ≡ b).
Proof. intros ->. apply eq_refl. Qed.
Global Instance from_pure_valid {A : cmraT} (a : A) : FromPure (✓ a) (✓ a).
Proof. intros ?. by apply valid_intro. Qed.

Class IntoPersistentP (P Q : uPred M) := into_persistentP : P ⊢ □ Q.
Global Arguments into_persistentP : clear implicits.
Global Instance into_persistentP_always_trans P Q :
  IntoPersistentP P Q → IntoPersistentP (□ P) Q | 0.
Proof. rewrite /IntoPersistentP=> ->. by rewrite always_always. Qed.
Global Instance into_persistentP_always P : IntoPersistentP (□ P) P | 1.
Proof. done. Qed.
Global Instance into_persistentP_persistent P :
  PersistentP P → IntoPersistentP P P | 100.
Proof. done. Qed.

Class IntoLater (P Q : uPred M) := into_later : P ⊢ ▷ Q.
Global Arguments into_later _ _ {_}.
Class FromLater (P Q : uPred M) := from_later : ▷ Q ⊢ P.
Global Arguments from_later _ _ {_}.

Global Instance into_later_default P : IntoLater P P | 1000.
Proof. apply later_intro. Qed.
Global Instance into_later_later P : IntoLater (▷ P) P.
Proof. done. Qed.
Global Instance into_later_and P1 P2 Q1 Q2 :
  IntoLater P1 Q1 → IntoLater P2 Q2 → IntoLater (P1 ∧ P2) (Q1 ∧ Q2).
Proof. intros ??; red. by rewrite later_and; apply and_mono. Qed.
Global Instance into_later_or P1 P2 Q1 Q2 :
  IntoLater P1 Q1 → IntoLater P2 Q2 → IntoLater (P1 ∨ P2) (Q1 ∨ Q2).
Proof. intros ??; red. by rewrite later_or; apply or_mono. Qed.
Global Instance into_later_sep P1 P2 Q1 Q2 :
  IntoLater P1 Q1 → IntoLater P2 Q2 → IntoLater (P1 ★ P2) (Q1 ★ Q2).
Proof. intros ??; red. by rewrite later_sep; apply sep_mono. Qed.

Global Instance into_later_big_sepM `{Countable K} {A}
    (Φ Ψ : K → A → uPred M) (m : gmap K A) :
  (∀ x k, IntoLater (Φ k x) (Ψ k x)) →
  IntoLater ([★ map] k ↦ x ∈ m, Φ k x) ([★ map] k ↦ x ∈ m, Ψ k x).
Proof.
  rewrite /IntoLater=> ?. rewrite big_sepM_later; by apply big_sepM_mono.
Qed.
Global Instance into_later_big_sepS `{Countable A}
    (Φ Ψ : A → uPred M) (X : gset A) :
  (∀ x, IntoLater (Φ x) (Ψ x)) →
  IntoLater ([★ set] x ∈ X, Φ x) ([★ set] x ∈ X, Ψ x).
Proof.
  rewrite /IntoLater=> ?. rewrite big_sepS_later; by apply big_sepS_mono.
Qed.

Global Instance from_later_later P : FromLater (▷ P) P.
Proof. done. Qed.
Global Instance from_later_and P1 P2 Q1 Q2 :
  FromLater P1 Q1 → FromLater P2 Q2 → FromLater (P1 ∧ P2) (Q1 ∧ Q2).
Proof. intros ??; red. by rewrite later_and; apply and_mono. Qed.
Global Instance from_later_or P1 P2 Q1 Q2 :
  FromLater P1 Q1 → FromLater P2 Q2 → FromLater (P1 ∨ P2) (Q1 ∨ Q2).
Proof. intros ??; red. by rewrite later_or; apply or_mono. Qed.
Global Instance from_later_sep P1 P2 Q1 Q2 :
  FromLater P1 Q1 → FromLater P2 Q2 → FromLater (P1 ★ P2) (Q1 ★ Q2).
Proof. intros ??; red. by rewrite later_sep; apply sep_mono. Qed.

Class IntoWand (R P Q : uPred M) := into_wand : R ⊢ P -★ Q.
Global Arguments into_wand : clear implicits.
Global Instance into_wand_wand P Q : IntoWand (P -★ Q) P Q.
Proof. done. Qed.
Global Instance into_wand_impl P Q : IntoWand (P → Q) P Q.
Proof. apply impl_wand. Qed.
Global Instance into_wand_iff_l P Q : IntoWand (P ↔ Q) P Q.
Proof. by apply and_elim_l', impl_wand. Qed.
Global Instance into_wand_iff_r P Q : IntoWand (P ↔ Q) Q P.
Proof. apply and_elim_r', impl_wand. Qed.
Global Instance into_wand_always R P Q : IntoWand R P Q → IntoWand (□ R) P Q.
Proof. rewrite /IntoWand=> ->. apply always_elim. Qed.

Class FromAnd (P Q1 Q2 : uPred M) := from_and : Q1 ∧ Q2 ⊢ P.
Global Arguments from_and : clear implicits.

Global Instance from_and_and P1 P2 : FromAnd (P1 ∧ P2) P1 P2.
Proof. done. Qed.
Global Instance from_and_sep_persistent_l P1 P2 :
  PersistentP P1 → FromAnd (P1 ★ P2) P1 P2 | 9.
Proof. intros. by rewrite /FromAnd always_and_sep_l. Qed.
Global Instance from_and_sep_persistent_r P1 P2 :
  PersistentP P2 → FromAnd (P1 ★ P2) P1 P2 | 10.
Proof. intros. by rewrite /FromAnd always_and_sep_r. Qed.
Global Instance from_and_always P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (□ P) (□ Q1) (□ Q2).
Proof. rewrite /FromAnd=> <-. by rewrite always_and. Qed.
Global Instance from_and_later P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromAnd=> <-. by rewrite later_and. Qed.

Class FromSep (P Q1 Q2 : uPred M) := from_sep : Q1 ★ Q2 ⊢ P.
Global Arguments from_sep : clear implicits.

Global Instance from_sep_sep P1 P2 : FromSep (P1 ★ P2) P1 P2 | 100.
Proof. done. Qed.
Global Instance from_sep_always P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (□ P) (□ Q1) (□ Q2).
Proof. rewrite /FromSep=> <-. by rewrite always_sep. Qed.
Global Instance from_sep_later P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromSep=> <-. by rewrite later_sep. Qed.

Global Instance from_sep_ownM (a b : M) :
  FromSep (uPred_ownM (a ⋅ b)) (uPred_ownM a) (uPred_ownM b) | 99.
Proof. by rewrite /FromSep ownM_op. Qed.
Global Instance from_sep_big_sepM
    `{Countable K} {A} (Φ Ψ1 Ψ2 : K → A → uPred M) m :
  (∀ k x, FromSep (Φ k x) (Ψ1 k x) (Ψ2 k x)) →
  FromSep ([★ map] k ↦ x ∈ m, Φ k x)
    ([★ map] k ↦ x ∈ m, Ψ1 k x) ([★ map] k ↦ x ∈ m, Ψ2 k x).
Proof.
  rewrite /FromSep=> ?. rewrite -big_sepM_sepM. by apply big_sepM_mono.
Qed.
Global Instance from_sep_big_sepS `{Countable A} (Φ Ψ1 Ψ2 : A → uPred M) X :
  (∀ x, FromSep (Φ x) (Ψ1 x) (Ψ2 x)) →
  FromSep ([★ set] x ∈ X, Φ x) ([★ set] x ∈ X, Ψ1 x) ([★ set] x ∈ X, Ψ2 x).
Proof.
  rewrite /FromSep=> ?. rewrite -big_sepS_sepS. by apply big_sepS_mono.
Qed.

Class IntoSep (p: bool) (P Q1 Q2 : uPred M) := into_sep : □?p P ⊢ □?p (Q1 ★ Q2).
Global Arguments into_sep : clear implicits.
Class IntoOp {A : cmraT} (a b1 b2 : A) := into_op : a ≡ b1 ⋅ b2.
Global Arguments into_op {_} _ _ _ {_}.

Global Instance into_op_op {A : cmraT} (a b : A) : IntoOp (a ⋅ b) a b.
Proof. by rewrite /IntoOp. Qed.
Global Instance into_op_persistent {A : cmraT} (a : A) :
  Persistent a → IntoOp a a a.
Proof. intros; apply (persistent_dup a). Qed.
Global Instance into_op_pair {A B : cmraT} (a b1 b2 : A) (a' b1' b2' : B) :
  IntoOp a b1 b2 → IntoOp a' b1' b2' →
  IntoOp (a,a') (b1,b1') (b2,b2').
Proof. by constructor. Qed.
Global Instance into_op_Some {A : cmraT} (a : A) b1 b2 :
  IntoOp a b1 b2 → IntoOp (Some a) (Some b1) (Some b2).
Proof. by constructor. Qed.

Global Instance into_sep_sep p P Q : IntoSep p (P ★ Q) P Q.
Proof. rewrite /IntoSep. by rewrite always_if_sep. Qed.
Global Instance into_sep_ownM p (a b1 b2 : M) :
  IntoOp a b1 b2 →
  IntoSep p (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof.
  rewrite /IntoOp /IntoSep=> ->. by rewrite ownM_op always_if_sep.
Qed.

Global Instance into_sep_and P Q : IntoSep true (P ∧ Q) P Q.
Proof. by rewrite /IntoSep /= always_and_sep. Qed.
Global Instance into_sep_and_persistent_l P Q :
  PersistentP P → IntoSep false (P ∧ Q) P Q.
Proof. intros; by rewrite /IntoSep /= always_and_sep_l. Qed.
Global Instance into_sep_and_persistent_r P Q :
  PersistentP Q → IntoSep false (P ∧ Q) P Q.
Proof. intros; by rewrite /IntoSep /= always_and_sep_r. Qed.

Global Instance into_sep_later p P Q1 Q2 :
  IntoSep p P Q1 Q2 → IntoSep p (▷ P) (▷ Q1) (▷ Q2).
Proof. by rewrite /IntoSep -later_sep !always_if_later=> ->. Qed.

Global Instance into_sep_big_sepM
    `{Countable K} {A} (Φ Ψ1 Ψ2 : K → A → uPred M) p m :
  (∀ k x, IntoSep p (Φ k x) (Ψ1 k x) (Ψ2 k x)) →
  IntoSep p ([★ map] k ↦ x ∈ m, Φ k x)
    ([★ map] k ↦ x ∈ m, Ψ1 k x) ([★ map] k ↦ x ∈ m, Ψ2 k x).
Proof.
  rewrite /IntoSep=> ?. rewrite -big_sepM_sepM !big_sepM_always_if.
  by apply big_sepM_mono.
Qed.
Global Instance into_sep_big_sepS `{Countable A} (Φ Ψ1 Ψ2 : A → uPred M) p X :
  (∀ x, IntoSep p (Φ x) (Ψ1 x) (Ψ2 x)) →
  IntoSep p ([★ set] x ∈ X, Φ x) ([★ set] x ∈ X, Ψ1 x) ([★ set] x ∈ X, Ψ2 x).
Proof.
  rewrite /IntoSep=> ?. rewrite -big_sepS_sepS !big_sepS_always_if.
  by apply big_sepS_mono.
Qed.

Class Frame (R P Q : uPred M) := frame : R ★ Q ⊢ P.
Global Arguments frame : clear implicits.

Global Instance frame_here R : Frame R R True.
Proof. by rewrite /Frame right_id. Qed.

Class MakeSep (P Q PQ : uPred M) := make_sep : P ★ Q ⊣⊢ PQ.
Global Instance make_sep_true_l P : MakeSep True P P.
Proof. by rewrite /MakeSep left_id. Qed.
Global Instance make_sep_true_r P : MakeSep P True P.
Proof. by rewrite /MakeSep right_id. Qed.
Global Instance make_sep_default P Q : MakeSep P Q (P ★ Q) | 100.
Proof. done. Qed.
Global Instance frame_sep_l R P1 P2 Q Q' :
  Frame R P1 Q → MakeSep Q P2 Q' → Frame R (P1 ★ P2) Q' | 9.
Proof. rewrite /Frame /MakeSep => <- <-. by rewrite assoc. Qed.
Global Instance frame_sep_r R P1 P2 Q Q' :
  Frame R P2 Q → MakeSep P1 Q Q' → Frame R (P1 ★ P2) Q' | 10.
Proof. rewrite /Frame /MakeSep => <- <-. solve_sep_entails. Qed.

Class MakeAnd (P Q PQ : uPred M) := make_and : P ∧ Q ⊣⊢ PQ.
Global Instance make_and_true_l P : MakeAnd True P P.
Proof. by rewrite /MakeAnd left_id. Qed.
Global Instance make_and_true_r P : MakeAnd P True P.
Proof. by rewrite /MakeAnd right_id. Qed.
Global Instance make_and_default P Q : MakeSep P Q (P ★ Q) | 100.
Proof. done. Qed.
Global Instance frame_and_l R P1 P2 Q Q' :
  Frame R P1 Q → MakeAnd Q P2 Q' → Frame R (P1 ∧ P2) Q' | 9.
Proof. rewrite /Frame /MakeAnd => <- <-; eauto 10 with I. Qed.
Global Instance frame_and_r R P1 P2 Q Q' :
  Frame R P2 Q → MakeAnd P1 Q Q' → Frame R (P1 ∧ P2) Q' | 10.
Proof. rewrite /Frame /MakeAnd => <- <-; eauto 10 with I. Qed.

Class MakeOr (P Q PQ : uPred M) := make_or : P ∨ Q ⊣⊢ PQ.
Global Instance make_or_true_l P : MakeOr True P True.
Proof. by rewrite /MakeOr left_absorb. Qed.
Global Instance make_or_true_r P : MakeOr P True True.
Proof. by rewrite /MakeOr right_absorb. Qed.
Global Instance make_or_default P Q : MakeOr P Q (P ∨ Q) | 100.
Proof. done. Qed.
Global Instance frame_or R P1 P2 Q1 Q2 Q :
  Frame R P1 Q1 → Frame R P2 Q2 → MakeOr Q1 Q2 Q → Frame R (P1 ∨ P2) Q.
Proof. rewrite /Frame /MakeOr => <- <- <-. by rewrite -sep_or_l. Qed.

Class MakeLater (P lP : uPred M) := make_later : ▷ P ⊣⊢ lP.
Global Instance make_later_true : MakeLater True True.
Proof. by rewrite /MakeLater later_True. Qed.
Global Instance make_later_default P : MakeLater P (▷ P) | 100.
Proof. done. Qed.

Global Instance frame_later R P Q Q' :
  Frame R P Q → MakeLater Q Q' → Frame R (▷ P) Q'.
Proof.
  rewrite /Frame /MakeLater=><- <-. by rewrite later_sep -(later_intro R).
Qed.

Global Instance frame_exist {A} R (Φ Ψ : A → uPred M) :
  (∀ a, Frame R (Φ a) (Ψ a)) → Frame R (∃ x, Φ x) (∃ x, Ψ x).
Proof. rewrite /Frame=> ?. by rewrite sep_exist_l; apply exist_mono. Qed.
Global Instance frame_forall {A} R (Φ Ψ : A → uPred M) :
  (∀ a, Frame R (Φ a) (Ψ a)) → Frame R (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /Frame=> ?. by rewrite sep_forall_l; apply forall_mono. Qed.

Class FromOr (P Q1 Q2 : uPred M) := from_or : Q1 ∨ Q2 ⊢ P.
Global Arguments from_or : clear implicits.
Global Instance from_or_or P1 P2 : FromOr (P1 ∨ P2) P1 P2.
Proof. done. Qed.

Class IntoOr P Q1 Q2 := into_or : P ⊢ Q1 ∨ Q2.
Global Arguments into_or : clear implicits.
Global Instance into_or_or P Q : IntoOr (P ∨ Q) P Q.
Proof. done. Qed.
Global Instance into_or_later P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /IntoOr=>->. by rewrite later_or. Qed.

Class FromExist {A} (P : uPred M) (Φ : A → uPred M) :=
  from_exist : (∃ x, Φ x) ⊢ P.
Global Arguments from_exist {_} _ _ {_}.
Global Instance from_exist_exist {A} (Φ: A → uPred M): FromExist (∃ a, Φ a) Φ.
Proof. done. Qed.

Lemma tac_exist {A} Δ P (Φ : A → uPred M) :
  FromExist P Φ → (∃ a, Δ ⊢ Φ a) → Δ ⊢ P.
Proof. intros ? [a ?]. rewrite -(from_exist P). eauto using exist_intro'. Qed.

Class IntoExist {A} (P : uPred M) (Φ : A → uPred M) :=
  into_exist : P ⊢ ∃ x, Φ x.
Global Arguments into_exist {_} _ _ {_}.
Global Instance into_exist_exist {A} (Φ : A → uPred M) : IntoExist (∃ a, Φ a) Φ.
Proof. done. Qed.
Global Instance into_exist_later {A} P (Φ : A → uPred M) :
  IntoExist P Φ → Inhabited A → IntoExist (▷ P) (λ a, ▷ (Φ a))%I.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP later_exist. Qed.
Global Instance into_exist_always {A} P (Φ : A → uPred M) :
  IntoExist P Φ → IntoExist (□ P) (λ a, □ (Φ a))%I.
Proof. rewrite /IntoExist=> HP. by rewrite HP always_exist. Qed.
End classes.
