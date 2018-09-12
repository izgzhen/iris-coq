From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation atomic_heap par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "Type".

(** Show that implementing fetch-and-add on top of CAS preserves logical
atomicity. *)

Section increment.
  Context `{!heapG Σ} {aheap: atomic_heap Σ}.

  Import atomic_heap.notation.

  Definition incr: val :=
    rec: "incr" "l" :=
       let: "oldv" := !"l" in
       if: CAS "l" "oldv" ("oldv" + #1)
         then "oldv" (* return old value if success *)
         else "incr" "l".

  Lemma incr_spec (l: loc) :
    <<< ∀ (v : Z), l ↦ #v >>> incr #l @ ⊤ <<< l ↦ #(v + 1), RET #v >>>.
  Proof.
    iApply wp_atomic_intro. iIntros (Φ) "AU". iLöb as "IH". wp_lam.
    wp_apply load_spec; first by iAccu.
    (* Prove the atomic update for load *)
    iAuIntro. iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (x) "H↦". iAaccIntro with "H↦"; first by eauto with iFrame.
    iIntros "$ !> AU !> _".
    (* Now go on *)
    wp_let. wp_op. wp_apply cas_spec; [done|iAccu|].
    (* Prove the atomic update for CAS *)
    iAuIntro. iApply (aacc_aupd with "AU"); first done.
    iIntros (x') "H↦". iAaccIntro with "H↦"; first by eauto with iFrame.
    iIntros "H↦ !>".
    destruct (decide (#x' = #x)) as [[= ->]|Hx].
    - iRight. iFrame. iIntros "HΦ !> _".
      wp_if. by iApply "HΦ".
    - iLeft. iFrame. iIntros "AU !> _".
      wp_if. iApply "IH". done.
  Qed.

  Definition weak_incr: val :=
    rec: "weak_incr" "l" :=
       let: "oldv" := !"l" in
       "l" <- ("oldv" + #1);;
       "oldv" (* return old value *).

  (* TODO: Generalize to q and 1-q, based on some theory for a "maybe-mapsto"
     connective that works on [option Qp] (the type of 1-q). *)
  Lemma weak_incr_spec (l: loc) (v : Z) :
    l ↦{1/2} #v -∗
    <<< ∀ (v' : Z), l ↦{1/2} #v' >>>
      weak_incr #l @ ⊤
    <<< ⌜v = v'⌝ ∗ l ↦ #(v + 1), RET #v >>>.
  Proof.
    iIntros "Hl". iApply wp_atomic_intro. iIntros (Φ) "AU". wp_lam.
    wp_apply (atomic_wp_seq $! (load_spec _) with "Hl").
    iIntros "Hl". wp_let. wp_op.
    wp_apply store_spec; first by iAccu.
    (* Prove the atomic update for store *)
    iAuIntro. iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (x) "H↦".
    iDestruct (mapsto_agree with "Hl H↦") as %[= <-].
    iCombine "Hl" "H↦" as "Hl". iAaccIntro with "Hl".
    { iIntros "[$ $]"; eauto. }
    iIntros "$ !>". iSplit; first done.
    iIntros "HΦ !> _". wp_seq. done.
  Qed.

End increment.

Section increment_client.
  Context `{!heapG Σ, !spawnG Σ}.

  Existing Instance primitive_atomic_heap.

  Definition incr_client : val :=
    λ: "x",
       let: "l" := ref "x" in
       incr "l" ||| incr "l".

  Lemma incr_client_safe (x: Z):
    WP incr_client #x {{ _, True }}%I.
  Proof using Type*.
    wp_lam. wp_alloc l as "Hl". wp_let.
    iMod (inv_alloc nroot _ (∃x':Z, l ↦ #x')%I with "[Hl]") as "#Hinv"; first eauto.
    (* FIXME: I am only using persistent stuff, so I should be allowed
       to move this to the persisten context even without the additional □. *)
    iAssert (□ WP incr #l {{ _, True }})%I as "#Aupd".
    { iAlways. wp_apply incr_spec; first by iAccu. clear x.
      iAuIntro. iInv nroot as (x) ">H↦". iAaccIntro with "H↦"; first by eauto 10.
      iIntros "H↦ !>". iSplitL "H↦"; first by eauto 10.
      (* The continuation: From after the atomic triple to the postcondition of the WP *)
      done.
    }
    wp_apply wp_par.
    - iAssumption.
    - iAssumption.
    - iIntros (??) "_ !>". done.
  Qed.

End increment_client.
