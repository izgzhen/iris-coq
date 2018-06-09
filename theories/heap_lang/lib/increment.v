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
    iIntros (Q Φ) "HQ AU". iLöb as "IH". wp_let.
    wp_apply (load_spec with "[HQ]"); first by iAccu.
    (* Prove the atomic update for load *)
    iAuIntro. iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (x) "H↦".
    (* FIXME: Oh wow this is bad. *)
    iApply (aacc_intro $! ([tele_arg _; _] : [tele (_:val) (_:Qp)]) with "[H↦]"); [solve_ndisj|done|iSplit].
    { iIntros "$ !> $ !> //". }
    iIntros "$ !> AU !> HQ".
    (* Now go on *)
    wp_let. wp_op. wp_bind (CAS _ _ _)%I.
    wp_apply (cas_spec with "[HQ]"); [done|iAccu|].
    (* Prove the atomic update for CAS *)
    iAuIntro. iApply (aacc_aupd with "AU"); first done.
    iIntros (x') "H↦".
    (* FIXME: Oh wow this is bad. *)
    iApply (aacc_intro $! ([tele_arg _] : [tele (_:val)]) with "[H↦]"); [solve_ndisj|simpl; by auto with iFrame|iSplit].
    { eauto 10 with iFrame. }
    (* FIXME: Manual reduction should not be needed. *)
    reduction.pm_reduce.
    iIntros "H↦ !>".
    destruct (decide (#x' = #x)) as [[= ->]|Hx].
    - iRight. iFrame. iIntros "HΦ !> HQ".
      wp_if. by iApply "HΦ".
    - iLeft. iFrame. iIntros "AU !> HQ".
      wp_if. iApply ("IH" with "HQ"). done.
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
    iIntros "Hl" (Q Φ) "HQ AU". wp_let.
    wp_apply (atomic_wp_seq $! (load_spec _) with "Hl").
    iIntros "Hl". wp_let. wp_op.
    wp_apply (store_spec with "[HQ]"); first by iAccu.
    (* Prove the atomic update for store *)
    iAuIntro. iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (x) "H↦".
    iDestruct (mapsto_agree with "Hl H↦") as %[= <-].
    iCombine "Hl" "H↦" as "Hl".
    (* FIXME: Oh wow this is bad. *)
    iApply (aacc_intro $! ([tele_arg _] : [tele (_:val)]) with "[Hl]"); [solve_ndisj|done|simpl; iSplit].
    { simpl. iIntros "[$ $] !> $ !> //". }
    iIntros "$ !>". iSplit; first done.
    iIntros "HΦ !> HQ". wp_seq. iApply "HΦ". done.
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
    wp_let. wp_alloc l as "Hl". wp_let.
    iMod (inv_alloc nroot _ (∃x':Z, l ↦ #x')%I with "[Hl]") as "#Hinv"; first eauto.
    (* FIXME: I am only using persistent stuff, so I should be allowed
       to move this to the persisten context even without the additional □. *)
    iAssert (□ WP incr #l {{ _, True }})%I as "#Aupd".
    { iAlways. wp_apply (incr_spec with "[]"); first by iAccu. clear x.
      iAuIntro. iInv nroot as (x) ">H↦".
      (* FIXME: Oh wow this is bad. *)
      iApply (aacc_intro $! ([tele_arg _] : [tele (_:Z)]) with "[H↦]"); [solve_ndisj|done|iSplit].
      { by eauto 10. }
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
