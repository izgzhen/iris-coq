From iris.program_logic Require Export hoare.
From iris.heap_lang.lib.barrier Require Export barrier.
From iris.heap_lang.lib.barrier Require Import proof.
From iris.heap_lang Require Import proofmode.
Import uPred.

Section spec.
Context `{!heapG Σ} `{!barrierG Σ}.

Lemma barrier_spec (N : namespace) :
  heapN ⊥ N →
  ∃ recv send : loc → iProp Σ -n> iProp Σ,
    (∀ P, heap_ctx ⊢ {{ True }} newbarrier #()
                     {{ v, ∃ l : loc, v = #l ★ recv l P ★ send l P }}) ∧
    (∀ l P, {{ send l P ★ P }} signal #l {{ _, True }}) ∧
    (∀ l P, {{ recv l P }} wait #l {{ _, P }}) ∧
    (∀ l P Q, recv l (P ★ Q) ={N}=> recv l P ★ recv l Q) ∧
    (∀ l P Q, (P -★ Q) ⊢ recv l P -★ recv l Q).
Proof.
  intros HN.
  exists (λ l, CofeMor (recv N l)), (λ l, CofeMor (send N l)).
  split_and?; simpl.
  - iIntros (P) "#? !# _". iApply (newbarrier_spec _ P); eauto.
  - iIntros (l P) "!# [Hl HP]". iApply signal_spec; iFrame "Hl HP"; by eauto.
  - iIntros (l P) "!# Hl". iApply wait_spec; iFrame "Hl"; eauto.
  - intros; by apply recv_split.
  - apply recv_weaken.
Qed.
End spec.
