From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type*".
Import uPred.

(** Least and greatest fixpoint of a monotone function, defined entirely inside
    the logic.  *)

Definition uPred_mono_pred {M A} (F : (A → uPred M) → (A → uPred M)) :=
  ∀ Φ Ψ, ((□ ∀ x, Φ x → Ψ x) → ∀ x, F Φ x → F Ψ x)%I.

Definition uPred_least_fixpoint {M A} (F : (A → uPred M) → (A → uPred M))
    (x : A) : uPred M :=
  (∀ Φ, □ (∀ x, F Φ x → Φ x) → Φ x)%I.

Definition uPred_greatest_fixpoint {M A} (F : (A → uPred M) → (A → uPred M))
    (x : A) : uPred M :=
  (∃ Φ, □ (∀ x, Φ x → F Φ x) ∧ Φ x)%I.

Section least.
  Context {M : ucmraT}.
  Context {A} (F : (A → uPred M) → (A → uPred M)) (Hmono : uPred_mono_pred F).

  Lemma least_fixpoint_unfold_2 x : F (uPred_least_fixpoint F) x ⊢ uPred_least_fixpoint F x.
  Proof.
    iIntros "HF" (Φ) "#Hincl".
    iApply "Hincl". iApply (Hmono _ Φ); last done.
    iIntros "!#" (y) "Hy". iApply "Hy". done.
  Qed.

  Lemma least_fixpoint_unfold_1 x :
    uPred_least_fixpoint F x ⊢ F (uPred_least_fixpoint F) x.
  Proof.
    iIntros "HF". iApply "HF". iIntros "!#" (y) "Hy".
    iApply Hmono; last done. iIntros "!#" (z) "?".
    by iApply least_fixpoint_unfold_2.
  Qed.

  Corollary least_fixpoint_unfold x :
    uPred_least_fixpoint F x ≡ F (uPred_least_fixpoint F) x.
  Proof.
    apply (anti_symm _); auto using least_fixpoint_unfold_1, least_fixpoint_unfold_2.
  Qed.

  Lemma least_fixpoint_ind (Φ : A → uPred M) :
    □ (∀ y, F Φ y → Φ y) ⊢ ∀ x, uPred_least_fixpoint F x → Φ x.
  Proof. iIntros "#HΦ" (x) "HF". iApply "HF". done. Qed.
End least.

Section greatest.
  Context {M : ucmraT} {A} (F : (A → uPred M) → (A → uPred M)) (Hmono : uPred_mono_pred F).

  Lemma greatest_fixpoint_unfold_1 x :
    uPred_greatest_fixpoint F x ⊢ F (uPred_greatest_fixpoint F) x.
  Proof.
    iDestruct 1 as (Φ) "[#Hincl HΦ]".
    iApply (Hmono Φ (uPred_greatest_fixpoint F)).
    - iIntros "!#" (y) "Hy". iExists Φ. auto.
    - by iApply "Hincl".
  Qed.

  Lemma greatest_fixpoint_unfold_2 x :
    F (uPred_greatest_fixpoint F) x ⊢ uPred_greatest_fixpoint F x.
  Proof.
    iIntros "HF". iExists (F (uPred_greatest_fixpoint F)).
    iIntros "{$HF} !#" (y) "Hy". iApply (Hmono with "[] Hy").
    iIntros "!#" (z) "?". by iApply greatest_fixpoint_unfold_1.
  Qed.

  Corollary greatest_fixpoint_unfold x :
    uPred_greatest_fixpoint F x ≡ F (uPred_greatest_fixpoint F) x.
  Proof.
    apply (anti_symm _); auto using greatest_fixpoint_unfold_1, greatest_fixpoint_unfold_2.
  Qed.

  Lemma greatest_fixpoint_coind (Φ : A → uPred M) :
    □ (∀ y, Φ y → F Φ y) ⊢ ∀ x, Φ x → uPred_greatest_fixpoint F x.
  Proof. iIntros "#HΦ" (x) "Hx". iExists Φ. by iIntros "{$Hx} !#". Qed.
End greatest.
