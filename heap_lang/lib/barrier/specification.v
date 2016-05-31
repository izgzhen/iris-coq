From iris.program_logic Require Export hoare.
From iris.heap_lang.lib.barrier Require Export barrier.
From iris.heap_lang.lib.barrier Require Import proof.
From iris.heap_lang Require Import proofmode.
Import uPred.

Section spec.
Context {Σ : gFunctors} `{!heapG Σ} `{!barrierG Σ}. 

Local Notation iProp := (iPropG heap_lang Σ).

Lemma barrier_spec (heapN N : namespace) :
  heapN ⊥ N →
  ∃ recv send : loc → iProp -n> iProp,
    (∀ P, heap_ctx heapN ⊢ {{ True }} newbarrier #() {{ v,
                             ∃ l : loc, v = #l ★ recv l P ★ send l P }}) ∧
    (∀ l P, {{ send l P ★ P }} signal #l {{ _, True }}) ∧
    (∀ l P, {{ recv l P }} wait #l {{ _, P }}) ∧
    (∀ l P Q, recv l (P ★ Q) ={N}=> recv l P ★ recv l Q) ∧
    (∀ l P Q, (P -★ Q) ⊢ recv l P -★ recv l Q).
Proof.
  intros HN.
  exists (λ l, CofeMor (recv heapN N l)), (λ l, CofeMor (send heapN N l)).
  split_and?; simpl.
  - iIntros {P} "#? ! _". iApply (newbarrier_spec _ _ P); first done.
    iSplit; [done|]; iIntros {l} "?"; iExists l; by iSplit.
  - iIntros {l P} "! [Hl HP]". by iApply signal_spec; iFrame "Hl HP".
  - iIntros {l P} "! Hl". iApply wait_spec; iFrame "Hl". by iIntros "?".
  - intros; by apply recv_split.
  - apply recv_weaken.
Qed.
End spec.
