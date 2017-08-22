From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type*".
Import uPred.

(** Greatest fixpoint of a monotone function, defined entirely inside
    the logic.
    TODO: Also do least fixpoint.
*)

Definition uPred_mono_pred {M A} (F : (A → uPred M) → (A → uPred M)) :=
  ∀ P Q, ((□ ∀ x, P x -∗ Q x) -∗ ∀ x, F P x -∗ F Q x)%I.

Definition iGFix {M A} (F : (A → uPred M) → (A → uPred M)) (x : A) : uPred M :=
  (∃ P, □ (∀ x, P x -∗ F P x) ∧ P x)%I.

Section iGFix.
  Context {M : ucmraT} {A} (F : (A → uPred M) → (A → uPred M)) (Hmono : uPred_mono_pred F).

  Lemma iGFix_implies_F_iGFix x : iGFix F x ⊢ F (iGFix F) x.
  Proof.
    iDestruct 1 as (P) "[#Hincl HP]".
    iApply (Hmono P (iGFix F)).
    - iAlways. iIntros (y) "Hy". iExists P. by iSplit.
    - by iApply "Hincl".
  Qed.

  Lemma F_iGFix_implies_iGFix x : F (iGFix F) x ⊢ iGFix F x.
  Proof.
    iIntros "HF". iExists (F (iGFix F)).
    iIntros "{$HF} !#"; iIntros (y) "Hy". iApply (Hmono with "[] Hy").
    iAlways. iIntros (z). by iApply iGFix_implies_F_iGFix.
  Qed.

  Corollary iGFix_unfold x : iGFix F x ≡ F (iGFix F) x.
  Proof.
    apply (anti_symm _); auto using iGFix_implies_F_iGFix, F_iGFix_implies_iGFix.
  Qed.

  Lemma Fix_coind (P : A → uPred M) (x : A) :
    □ (∀ y, P y -∗ F P y) -∗ P x -∗ iGFix F x.
  Proof. iIntros "#HP Hx". iExists P. by iIntros "{$Hx} !#". Qed.
End iGFix.
