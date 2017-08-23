From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type*".
Import uPred.

(** Least and greatest fixpoint of a monotone function, defined entirely inside
    the logic.  *)

Definition uPred_mono_pred {M A} (F : (A → uPred M) → (A → uPred M)) :=
  ∀ P Q, ((□ ∀ x, P x -∗ Q x) -∗ ∀ x, F P x -∗ F Q x)%I.

Definition uPred_least_fixpoint {M A} (F : (A → uPred M) → (A → uPred M)) (x : A) : uPred M :=
  (∀ P, □ (∀ x, F P x -∗ P x) → P x)%I.

Definition uPred_greatest_fixpoint {M A} (F : (A → uPred M) → (A → uPred M)) (x : A) : uPred M :=
  (∃ P, □ (∀ x, P x -∗ F P x) ∧ P x)%I.

Section least.
  Context {M : ucmraT} {A} (F : (A → uPred M) → (A → uPred M)) (Hmono : uPred_mono_pred F).

  Lemma F_fix_implies_least_fixpoint x : F (uPred_least_fixpoint F) x ⊢ uPred_least_fixpoint F x.
  Proof.
    iIntros "HF" (P). iApply wand_impl_always. iIntros "#Hincl".
    iApply "Hincl". iApply (Hmono _ P); last done.
    iIntros "!#" (y) "Hy". iApply "Hy". done.
  Qed.

  Lemma least_fixpoint_implies_F_fix x :
    uPred_least_fixpoint F x ⊢ F (uPred_least_fixpoint F) x.
  Proof.
    iIntros "HF". iApply "HF". iIntros "!#" (y) "Hy".
    iApply Hmono; last done. iIntros "!#" (z) "?".
    by iApply F_fix_implies_least_fixpoint.
  Qed.

  Corollary uPred_least_fixpoint_unfold x :
    uPred_least_fixpoint F x ≡ F (uPred_least_fixpoint F) x.
  Proof.
    apply (anti_symm _); auto using least_fixpoint_implies_F_fix, F_fix_implies_least_fixpoint.
  Qed.

  Lemma uPred_least_fixpoint_ind (P : A → uPred M) (x : A) :
    uPred_least_fixpoint F x -∗ □ (∀ y, F P y -∗ P y) -∗ P x.
  Proof. iIntros "HF #HP". iApply "HF". done. Qed.
End least.

Section greatest.
  Context {M : ucmraT} {A} (F : (A → uPred M) → (A → uPred M)) (Hmono : uPred_mono_pred F).

  Lemma greatest_fixpoint_implies_F_fix x :
    uPred_greatest_fixpoint F x ⊢ F (uPred_greatest_fixpoint F) x.
  Proof.
    iDestruct 1 as (P) "[#Hincl HP]".
    iApply (Hmono P (uPred_greatest_fixpoint F)).
    - iAlways. iIntros (y) "Hy". iExists P. by iSplit.
    - by iApply "Hincl".
  Qed.

  Lemma F_fix_implies_greatest_fixpoint x :
    F (uPred_greatest_fixpoint F) x ⊢ uPred_greatest_fixpoint F x.
  Proof.
    iIntros "HF". iExists (F (uPred_greatest_fixpoint F)).
    iIntros "{$HF} !#"; iIntros (y) "Hy". iApply (Hmono with "[] Hy").
    iAlways. iIntros (z). by iApply greatest_fixpoint_implies_F_fix.
  Qed.

  Corollary uPred_greatest_fixpoint_unfold x :
    uPred_greatest_fixpoint F x ≡ F (uPred_greatest_fixpoint F) x.
  Proof.
    apply (anti_symm _); auto using greatest_fixpoint_implies_F_fix, F_fix_implies_greatest_fixpoint.
  Qed.

  Lemma uPred_greatest_fixpoint_coind (P : A → uPred M) (x : A) :
    □ (∀ y, P y -∗ F P y) -∗ P x -∗ uPred_greatest_fixpoint F x.
  Proof. iIntros "#HP Hx". iExists P. by iIntros "{$Hx} !#". Qed.
End greatest.
