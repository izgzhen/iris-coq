From iris.heap_lang Require Export lang.
From iris.proofmode Require Import invariants tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl.

Definition spawn : val :=
  λ: "f",
    let: "c" := ref NONE in
    Fork ("c" <- SOME ("f" #())) ;; "c".
Definition join : val :=
  rec: "join" "c" :=
    match: !"c" with
      SOME "x" => "x"
    | NONE => "join" "c"
    end.
Global Opaque spawn join.

(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class spawnG Σ := SpawnG { spawn_tokG :> inG Σ (exclR unitC) }.
(** The functor we need. *)
Definition spawnGF : gFunctorList := [GFunctor (constRF (exclR unitC))].
(* Show and register that they match. *)
Instance inGF_spawnG `{H : inGFs Σ spawnGF} : spawnG Σ.
Proof. destruct H as (?&?). split. apply: inGF_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context `{!heapG Σ, !spawnG Σ} (N : namespace).

Definition spawn_inv (γ : gname) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  (∃ lv, l ↦ lv ★ (lv = NONEV ∨
                   ∃ v, lv = SOMEV v ★ (Ψ v ∨ own γ (Excl ()))))%I.

Definition join_handle (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  (heapN ⊥ N ★ ∃ γ, heap_ctx ★ own γ (Excl ()) ★
                    inv N (spawn_inv γ l Ψ))%I.

Typeclasses Opaque join_handle.

Global Instance spawn_inv_ne n γ l :
  Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γ l).
Proof. solve_proper. Qed.
Global Instance join_handle_ne n l :
  Proper (pointwise_relation val (dist n) ==> dist n) (join_handle l).
Proof. solve_proper. Qed.

(** The main proofs. *)
Lemma spawn_spec (Ψ : val → iProp Σ) e (f : val) (Φ : val → iProp Σ) :
  to_val e = Some f →
  heapN ⊥ N →
  heap_ctx ★ WP f #() {{ Ψ }} ★ (∀ l, join_handle l Ψ -★ Φ #l)
  ⊢ WP spawn e {{ Φ }}.
Proof.
  iIntros (<-%of_to_val ?) "(#Hh & Hf & HΦ)". rewrite /spawn.
  wp_let. wp_alloc l as "Hl". wp_let.
  iVs (own_alloc (Excl ())) as (γ) "Hγ"; first done.
  iVs (inv_alloc N _ (spawn_inv γ l Ψ) with "[Hl]") as "#?".
  { iNext. iExists NONEV. iFrame; eauto. }
  wp_apply wp_fork. iSplitR "Hf".
  - iVsIntro. wp_seq. iVsIntro. iApply "HΦ". rewrite /join_handle. eauto.
  - wp_focus (f _). iApply wp_wand_l. iFrame "Hf"; iIntros (v) "Hv".
    iInv N as (v') "[Hl _]" "Hclose".
    wp_store. iApply "Hclose". iNext. iExists (SOMEV v). iFrame. eauto.
Qed.

Lemma join_spec (Ψ : val → iProp Σ) l (Φ : val → iProp Σ) :
  join_handle l Ψ ★ (∀ v, Ψ v -★ Φ v) ⊢ WP join #l {{ Φ }}.
Proof.
  rewrite /join_handle; iIntros "[[% H] Hv]". iDestruct "H" as (γ) "(#?&Hγ&#?)".
  iLöb as "IH". wp_rec. wp_focus (! _)%E. iInv N as (v) "[Hl Hinv]" "Hclose".
  wp_load. iDestruct "Hinv" as "[%|Hinv]"; subst.
  - iVs ("Hclose" with "[Hl]"); [iNext; iExists _; iFrame; eauto|].
    iVsIntro. wp_match. iApply ("IH" with "Hγ Hv").
  - iDestruct "Hinv" as (v') "[% [HΨ|Hγ']]"; simplify_eq/=.
    + iVs ("Hclose" with "[Hl Hγ]"); [iNext; iExists _; iFrame; eauto|].
      iVsIntro. wp_match. by iApply "Hv".
    + iCombine "Hγ" "Hγ'" as "Hγ". iDestruct (own_valid with "Hγ") as %[].
Qed.
End proof.

Typeclasses Opaque join_handle.
