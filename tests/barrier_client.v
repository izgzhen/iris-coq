From iris.heap_lang.lib.barrier Require Import proof.
From iris.heap_lang Require Import par.
From iris.program_logic Require Import auth sts saved_prop hoare ownership.
From iris.heap_lang Require Import proofmode.
Import uPred.

Definition worker (n : Z) : val :=
  λ: "b" "y", ^wait '"b" ;; !'"y" #n.
Definition client : expr [] :=
  let: "y" := ref #0 in
  let: "b" := ^newbarrier #() in
  ('"y" <- (λ: "z", '"z" + #42) ;; ^signal '"b") ||
    (^(worker 12) '"b" '"y" || ^(worker 17) '"b" '"y").

Section client.
  Context {Σ : gFunctors} `{!heapG Σ, !barrierG Σ, !spawnG Σ} (heapN N : namespace).
  Local Notation iProp := (iPropG heap_lang Σ).

  Definition y_inv (q : Qp) (l : loc) : iProp :=
    (∃ f : val, l ↦{q} f ★ □ ∀ n : Z, WP f #n {{ v, v = #(n + 42) }})%I.

  Lemma y_inv_split q l : y_inv q l ⊢ (y_inv (q/2) l ★ y_inv (q/2) l).
  Proof.
    iIntros "Hl"; iDestruct "Hl" as {f} "[[Hl1 Hl2] #Hf]".
    iSplitL "Hl1"; iExists f; by iSplitL; try iAlways.
  Qed.

  Lemma worker_safe q (n : Z) (b y : loc) :
    (heap_ctx heapN ★ recv heapN N b (y_inv q y))
    ⊢ WP worker n #b #y {{ _, True }}.
  Proof.
    iIntros "[#Hh Hrecv]". wp_lam. wp_let.
    wp_apply wait_spec; iFrame "Hrecv".
    iIntros "Hy"; iDestruct "Hy" as {f} "[Hy #Hf]".
    wp_seq. wp_load.
    iApply wp_wand_r; iSplitR; [iApply "Hf"|by iIntros {v} "_"].
  Qed.

  Lemma client_safe : heapN ⊥ N → heap_ctx heapN ⊢ WP client {{ _, True }}.
  Proof.
    iIntros {?} "#Hh"; rewrite /client. wp_alloc y as "Hy". wp_let.
    wp_apply (newbarrier_spec heapN N (y_inv 1 y)); first done.
    iFrame "Hh". iIntros {l} "[Hr Hs]". wp_let.
    iApply (wp_par heapN N (λ _, True%I) (λ _, True%I)); first done.
    iFrame "Hh". iSplitL "Hy Hs".
    - (* The original thread, the sender. *)
      wp_store. wp_seq. iApply signal_spec; iFrame "Hs"; iSplit; [|done].
      iExists _; iSplitL; [done|]. iAlways; iIntros {n}. wp_let. by wp_op.
    - (* The two spawned threads, the waiters. *)
      iSplitL; [|by iIntros {_ _} "_ >"].
      iDestruct (recv_weaken with "[] Hr") as "Hr".
      { iIntros "Hy". by iApply (y_inv_split with "Hy"). }
      iPvs (recv_split with "Hr") as "[H1 H2]"; first done.
      iApply (wp_par heapN N (λ _, True%I) (λ _, True%I)); eauto.
      iFrame "Hh"; iSplitL "H1"; [|iSplitL "H2"; [|by iIntros {_ _} "_ >"]];
        iApply worker_safe; by iSplit.
Qed.
End client.

Section ClosedProofs.
  Definition Σ : gFunctors := #[ heapGF ; barrierGF ; spawnGF ].
  Notation iProp := (iPropG heap_lang Σ).

  Lemma client_safe_closed σ : {{ ownP σ : iProp }} client {{ v, True }}.
  Proof.
    iIntros "! Hσ".
    iPvs (heap_alloc (nroot .@ "Barrier") with "Hσ") as {h} "[#Hh _]"; first done.
    iApply (client_safe (nroot .@ "Barrier") (nroot .@ "Heap")); auto with ndisj.
  Qed.

  Print Assumptions client_safe_closed.
End ClosedProofs.
