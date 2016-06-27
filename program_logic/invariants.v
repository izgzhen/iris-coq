From iris.program_logic Require Import ownership.
From iris.program_logic Require Export namespaces.
From iris.proofmode Require Import pviewshifts.
Import uPred.

(** Derived forms and lemmas about them. *)
Definition inv_def {Λ Σ} (N : namespace) (P : iProp Λ Σ) : iProp Λ Σ :=
  (∃ i, ■ (i ∈ nclose N) ∧ ownI i P)%I.
Definition inv_aux : { x | x = @inv_def }. by eexists. Qed.
Definition inv {Λ Σ} := proj1_sig inv_aux Λ Σ.
Definition inv_eq : @inv = @inv_def := proj2_sig inv_aux.
Instance: Params (@inv) 3.
Typeclasses Opaque inv.

Section inv.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Λ Σ.
Implicit Types Φ : val Λ → iProp Λ Σ.

Global Instance inv_contractive N : Contractive (@inv Λ Σ N).
Proof.
  rewrite inv_eq=> n ???. apply exist_ne=>i. by apply and_ne, ownI_contractive.
Qed.

Global Instance inv_persistent N P : PersistentP (inv N P).
Proof. rewrite inv_eq /inv; apply _. Qed.

Lemma always_inv N P : □ inv N P ⊣⊢ inv N P.
Proof. by rewrite always_always. Qed.

Lemma inv_alloc N E P : nclose N ⊆ E → ▷ P ={E}=> inv N P.
Proof.
  intros. rewrite -(pvs_mask_weaken N) //.
  by rewrite inv_eq /inv (pvs_allocI N); last apply coPset_suffixes_infinite.
Qed.

(** Fairly explicit form of opening invariants *)
Lemma inv_open E N P :
  nclose N ⊆ E →
  inv N P ⊢ ∃ E', ■ (E ∖ nclose N ⊆ E' ⊆ E) ★
                    |={E,E'}=> ▷ P ★ (▷ P ={E',E}=★ True).
Proof.
  rewrite inv_eq /inv. iDestruct 1 as {i} "[% #Hi]".
  iExists (E ∖ {[ i ]}). iSplit. { iPureIntro. set_solver. }
  iPvs (pvs_openI' with "Hi") as "HP"; [set_solver..|].
  iPvsIntro. iSplitL "HP"; first done. iIntros "HP".
  iPvs (pvs_closeI' _ _ P with "[HP]"); [set_solver|iSplit; done|set_solver|].
  done.
Qed.

(** Invariants can be opened around any frame-shifting assertion. This is less
    verbose to apply than [inv_open]. *)
Lemma inv_fsa {A} (fsa : FSA Λ Σ A) `{!FrameShiftAssertion fsaV fsa} E N P Ψ :
  fsaV → nclose N ⊆ E →
  inv N P ★ (▷ P -★ fsa (E ∖ nclose N) (λ a, ▷ P ★ Ψ a)) ⊢ fsa E Ψ.
Proof.
  iIntros {??} "[Hinv HΨ]".
  iDestruct (inv_open E N P with "Hinv") as {E'} "[% Hvs]"; first done.
  iApply (fsa_open_close E E'); auto; first set_solver.
  iPvs "Hvs" as "[HP Hvs]"; first set_solver.
  (* TODO: How do I do sth. like [iSpecialize "HΨ HP"]? *)
  iPvsIntro. iApply (fsa_mask_weaken _ (E ∖ N)); first set_solver.
  iApply fsa_wand_r. iSplitR "Hvs"; first by iApply "HΨ"; simpl.
  iIntros {v} "[HP HΨ]". by iPvs ("Hvs" with "HP"); first set_solver.
Qed.
End inv.
