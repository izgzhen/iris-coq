From iris.heap_lang Require Export lifting notation.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation atomic_heap.
Set Default Proof Using "Type".

(** Show taht implementing fetch-and-add on top of CAS preserves logical
atomicity. *)

(* TODO: Move this to iris-examples once gen_proofmode is merged. *)
Section increment.
  Context `{!heapG Σ} {aheap: atomic_heap Σ}.

  Definition incr: val :=
    rec: "incr" "l" :=
       let: "oldv" := aheap.(load) "l" in
       if: aheap.(cas) ("l", "oldv", ("oldv" + #1))
         then "oldv" (* return old value if success *)
         else "incr" "l".

  Lemma incr_spec (l: loc) :
        atomic_wp (incr #l)
                  (λ (v: Z), aheap.(mapsto) l 1 #v)%I
                  (λ v (_:()), aheap.(mapsto) l 1 #(v + 1))%I
                  ⊤ ∅
                  (λ v _, #v).
  Proof.
    iIntros (Φ) "AUpd". iLöb as "IH". wp_let.
    wp_apply load_spec.
    (* Prove the atomic shift for load *)
    iDestruct "AUpd" as (F P) "(HF & HP & #AShft)".
    iExists F, P. iFrame. iIntros "!# * % HP".
    iMod ("AShft" with "[%] HP") as (x) "[H↦ Hclose]"; first done.
    iModIntro. iExists (#x, 1%Qp). iFrame. iSplit.
    { iDestruct "Hclose" as "[Hclose _]". iApply "Hclose". }
    iIntros (_) "H↦". iDestruct "Hclose" as "[Hclose _]".
    iMod ("Hclose" with "H↦") as "HP". iIntros "!> HF".
    clear dependent E.
    (* Now go on *)
    wp_let. wp_op. wp_bind (aheap.(cas) _)%I.
    wp_apply cas_spec.
    (* Prove the atomic shift for CAS *)
    iExists F, P. iFrame. iIntros "!# * % HP".
    iMod ("AShft" with "[%] HP") as (x') "[H↦ Hclose]"; first done.
    iModIntro. iExists #x'. iFrame. iSplit.
    { iDestruct "Hclose" as "[Hclose _]". iApply "Hclose". }
    iIntros (_). destruct (decide (#x' = #x)) as [[= Hx]|Hx].
    - iIntros "H↦". iDestruct "Hclose" as "[_ Hclose]". subst.
      iMod ("Hclose" $! () with "H↦") as "HΦ". iIntros "!> HF".
      wp_if. by iApply "HΦ".
    - iDestruct "Hclose" as "[Hclose _]". iIntros "H↦".
      iMod ("Hclose" with "H↦") as "HP". iIntros "!> HF".
      wp_if. iApply "IH". iExists F, P. iFrame. done.
  Qed.

End increment.

