From iris.program_logic Require Import ownership.
From iris.program_logic Require Export namespaces.
From iris.proofmode Require Import pviewshifts.
Import uPred.

(** Derived forms and lemmas about them. *)
Definition inv {Λ Σ} (N : namespace) (P : iProp Λ Σ) : iProp Λ Σ :=
  (∃ i, ■ (i ∈ nclose N) ∧ ownI i P)%I.
Instance: Params (@inv) 3.
Typeclasses Opaque inv.

Section inv.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Λ Σ.
Implicit Types Φ : val Λ → iProp Λ Σ.

Global Instance inv_contractive N : Contractive (@inv Λ Σ N).
Proof. intros n ???. apply exist_ne=>i. by apply and_ne, ownI_contractive. Qed.

Global Instance inv_persistent N P : PersistentP (inv N P).
Proof. rewrite /inv; apply _. Qed.

Lemma always_inv N P : □ inv N P ⊣⊢ inv N P.
Proof. by rewrite always_always. Qed.

Lemma inv_alloc N E P : nclose N ⊆ E → ▷ P ⊢ |={E}=> inv N P.
Proof.
  intros. rewrite -(pvs_mask_weaken N) //.
  by rewrite /inv (pvs_allocI N); last apply coPset_suffixes_infinite.
Qed.

(** Invariants can be opened around any frame-shifting assertion. *)
Lemma inv_fsa {A} (fsa : FSA Λ Σ A) `{!FrameShiftAssertion fsaV fsa} E N P Ψ :
  fsaV → nclose N ⊆ E →
  (inv N P ★ (▷ P -★ fsa (E ∖ nclose N) (λ a, ▷ P ★ Ψ a))) ⊢ fsa E Ψ.
Proof.
  iIntros {??} "[#Hinv HΨ]"; rewrite /inv; iDestruct "Hinv" as {i} "[% Hi]".
  iApply (fsa_open_close E (E ∖ {[encode i]})); auto; first by set_solver.
  iPvs (pvs_openI' _ _ with "Hi") as "HP"; [set_solver..|iPvsIntro].
  iApply (fsa_mask_weaken _ (E ∖ N)); first set_solver.
  iApply fsa_wand_r; iSplitL; [by iApply "HΨ"|iIntros {v} "[HP HΨ]"].
  iPvs (pvs_closeI' _ _ P with "[HP]"); [auto|by iSplit|set_solver|done].
Qed.
End inv.
