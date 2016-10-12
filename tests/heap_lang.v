(** This file is essentially a bunch of testcases. *)
From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import adequacy.
From iris.program_logic Require Import wsat.
From iris.heap_lang Require Import proofmode notation.

Section LiftingTests.
  Context `{heapG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Definition heap_e  : expr :=
    let: "x" := ref #1 in "x" <- !"x" + #1 ;; !"x".
  Lemma heap_e_spec E :
     nclose heapN ⊆ E → heap_ctx ⊢ WP heap_e @ E {{ v, v = #2 }}.
  Proof.
    iIntros (HN) "#?". rewrite /heap_e.
    wp_alloc l. wp_let. wp_load. wp_op. wp_store. by wp_load.
  Qed.

  Definition heap_e2 : expr :=
    let: "x" := ref #1 in
    let: "y" := ref #1 in
    "x" <- !"x" + #1 ;; !"x".
  Lemma heap_e2_spec E :
     nclose heapN ⊆ E → heap_ctx ⊢ WP heap_e2 @ E {{ v, v = #2 }}.
  Proof.
    iIntros (HN) "#?". rewrite /heap_e2.
    wp_alloc l. wp_let. wp_alloc l'. wp_let.
    wp_load. wp_op. wp_store. wp_load. done.
  Qed.

  Definition FindPred : val :=
    rec: "pred" "x" "y" :=
      let: "yp" := "y" + #1 in
      if: "yp" < "x" then "pred" "x" "yp" else "y".
  Definition Pred : val :=
    λ: "x",
      if: "x" ≤ #0 then -FindPred (-"x" + #2) #0 else FindPred "x" #0.
  Global Opaque FindPred Pred.

  Lemma FindPred_spec n1 n2 E Φ :
    n1 < n2 →
    Φ #(n2 - 1) ⊢ WP FindPred #n2 #n1 @ E {{ Φ }}.
  Proof.
    iIntros (Hn) "HΦ". iLöb as "IH" forall (n1 Hn).
    wp_rec. wp_let. wp_op. wp_let. wp_op=> ?; wp_if.
    - iApply ("IH" with "[%] HΦ"). omega.
    - iApply pvs_intro. by assert (n1 = n2 - 1) as -> by omega.
  Qed.

  Lemma Pred_spec n E Φ : ▷ Φ #(n - 1) ⊢ WP Pred #n @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". wp_lam. wp_op=> ?; wp_if.
    - wp_op. wp_op.
      wp_apply FindPred_spec; first omega.
      wp_op. by replace (n - 1) with (- (-n + 2 - 1)) by omega.
    - wp_apply FindPred_spec; eauto with omega.
  Qed.

  Lemma Pred_user E :
    True ⊢ WP let: "x" := Pred #42 in Pred "x" @ E {{ v, v = #40 }}.
  Proof. iIntros "". wp_apply Pred_spec. wp_let. by wp_apply Pred_spec. Qed.
End LiftingTests.

Lemma heap_e_adequate σ : adequate heap_e σ (λ v, v = #2).
Proof. eapply (heap_adequacy heapΣ)=> ?. by apply heap_e_spec. Qed.
