From iris.program_logic Require Export global_functor.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

Definition spawn : val :=
  λ: "f",
    let: "c" := ref (InjL #0) in
    Fork ('"c" <- InjR ('"f" #())) ;; '"c".
Definition join : val :=
  rec: "join" "c" :=
    match: !'"c" with
      InjR "x" => '"x"
    | InjL <>  => '"join" '"c"
    end.

(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class spawnG Σ := SpawnG {
  spawn_tokG :> inG heap_lang Σ (exclR unitC);
}.
(** The functor we need. *)
Definition spawnGF : gFunctorList := [GFunctor (constRF (exclR unitC))].
(* Show and register that they match. *)
Instance inGF_spawnG
  `{H : inGFs heap_lang Σ spawnGF} : spawnG Σ.
Proof. destruct H as (?&?). split. apply: inGF_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context {Σ : gFunctors} `{!heapG Σ, !spawnG Σ}.
Context (heapN N : namespace).
Local Notation iProp := (iPropG heap_lang Σ).

Definition spawn_inv (γ : gname) (l : loc) (Ψ : val → iProp) : iProp :=
  (∃ lv, l ↦ lv ★ (lv = InjLV #0 ∨
                   ∃ v, lv = InjRV v ★ (Ψ v ∨ own γ (Excl ()))))%I.

Definition join_handle (l : loc) (Ψ : val → iProp) : iProp :=
  (heapN ⊥ N ★ ∃ γ, heap_ctx heapN ★ own γ (Excl ()) ★
                    inv N (spawn_inv γ l Ψ))%I.

Typeclasses Opaque join_handle.

Global Instance spawn_inv_ne n γ l :
  Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γ l).
Proof. solve_proper. Qed.
Global Instance join_handle_ne n l :
  Proper (pointwise_relation val (dist n) ==> dist n) (join_handle l).
Proof. solve_proper. Qed.

(** The main proofs. *)
Lemma spawn_spec (Ψ : val → iProp) e (f : val) (Φ : val → iProp) :
  to_val e = Some f →
  heapN ⊥ N →
  (heap_ctx heapN ★ WP f #() {{ Ψ }} ★ ∀ l, join_handle l Ψ -★ Φ #l)
  ⊢ WP spawn e {{ Φ }}.
Proof.
  iIntros {<-%of_to_val ?} "(#Hh&Hf&HΦ)". rewrite /spawn.
  wp_let. wp_alloc l as "Hl". wp_let.
  iPvs (own_alloc (Excl ())) as {γ} "Hγ"; first done.
  iPvs (inv_alloc N _ (spawn_inv γ l Ψ) with "[Hl]") as "#?"; first done.
  { iNext. iExists (InjLV #0). iFrame "Hl". by iLeft. }
  wp_apply wp_fork. iSplitR "Hf".
  - wp_seq. iPvsIntro. iApply "HΦ"; rewrite /join_handle.
    iSplit; first done. iExists γ. iFrame "Hγ"; by iSplit.
  - wp_focus (f _). iApply wp_wand_l; iFrame "Hf"; iIntros {v} "Hv".
    iInv N as {v'} "[Hl _]"; first wp_done.
    wp_store. iSplit; [iNext|done].
    iExists (InjRV v); iFrame "Hl"; iRight; iExists v; iSplit; [done|by iLeft].
Qed.

Lemma join_spec (Ψ : val → iProp) l (Φ : val → iProp) :
  (join_handle l Ψ ★ ∀ v, Ψ v -★ Φ v) ⊢ WP join #l {{ Φ }}.
Proof.
  rewrite /join_handle; iIntros "[[% H] Hv]"; iDestruct "H" as {γ} "(#?&Hγ&#?)".
  iLöb as "IH". wp_rec. wp_focus (! _)%E. iInv N as {v} "[Hl Hinv]".
  wp_load. iDestruct "Hinv" as "[%|Hinv]"; subst.
  - iSplitL "Hl"; [iNext; iExists _; iFrame "Hl"; by iLeft|].
    wp_case. wp_seq. iApply ("IH" with "Hγ Hv").
  - iDestruct "Hinv" as {v'} "[% [HΨ|Hγ']]"; subst.
    + iSplitL "Hl Hγ".
      { iNext. iExists _; iFrame "Hl"; iRight.
        iExists _; iSplit; [done|by iRight]. }
      wp_case. wp_let. iPvsIntro. by iApply "Hv".
    + iCombine "Hγ" "Hγ'" as "Hγ". iDestruct (own_valid with "Hγ") as %[].
Qed.
End proof.

Typeclasses Opaque join_handle.
