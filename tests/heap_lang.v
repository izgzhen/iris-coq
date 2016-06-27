(** This file is essentially a bunch of testcases. *)
From iris.program_logic Require Import ownership hoare auth.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

Section LangTests.
  Definition add : expr [] := (#21 + #21)%E.
  Goal ∀ σ, head_step add σ (#42) σ None.
  Proof. intros; do_head_step done. Qed.
  Definition rec_app : expr [] := ((rec: "f" "x" := '"f" '"x") #0)%E.
  Goal ∀ σ, head_step rec_app σ rec_app σ None.
  Proof. intros. rewrite /rec_app. do_head_step done. Qed.
  Definition lam : expr [] := (λ: "x", '"x" + #21)%E.
  Goal ∀ σ, head_step (lam #21)%E σ add σ None.
  Proof. intros. rewrite /lam. do_head_step done. Qed.
End LangTests.

Section LiftingTests.
  Context `{heapG Σ}.
  Local Notation iProp := (iPropG heap_lang Σ).
  Implicit Types P Q : iPropG heap_lang Σ.
  Implicit Types Φ : val → iPropG heap_lang Σ.

  Definition heap_e  : expr [] :=
    let: "x" := ref #1 in '"x" <- !'"x" + #1 ;; !'"x".
  Lemma heap_e_spec E N :
     nclose N ⊆ E → heap_ctx N ⊢ WP heap_e @ E {{ v, v = #2 }}.
  Proof.
    iIntros {HN} "#?". rewrite /heap_e. iApply (wp_mask_weaken N); first done.
    wp_alloc l. wp_let. wp_load. wp_op. wp_store. by wp_load.
  Qed.

  Definition heap_e2  : expr [] :=
    let: "x" := ref #1 in
    let: "y" := ref #1 in
    '"x" <- !'"x" + #1 ;; !'"x".
  Lemma heap_e2_spec E N :
     nclose N ⊆ E → heap_ctx N ⊢ WP heap_e2 @ E {{ v, v = #2 }}.
  Proof.
    iIntros {HN} "#?". rewrite /heap_e2. iApply (wp_mask_weaken N); first done.
    wp_alloc l. wp_let. wp_alloc l'. wp_let.
    wp_load. wp_op. wp_store. wp_load. done.
  Qed.

  Definition FindPred : val :=
    rec: "pred" "x" "y" :=
      let: "yp" := '"y" + #1 in
      if: '"yp" < '"x" then '"pred" '"x" '"yp" else '"y".
  Definition Pred : val :=
    λ: "x",
      if: '"x" ≤ #0 then -^FindPred (-'"x" + #2) #0 else ^FindPred '"x" #0.
  Global Opaque FindPred Pred.

  Lemma FindPred_spec n1 n2 E Φ :
    n1 < n2 →
    Φ #(n2 - 1) ⊢ WP FindPred #n2 #n1 @ E {{ Φ }}.
  Proof.
    iIntros {Hn} "HΦ". iLöb {n1 Hn} as "IH".
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
    (True : iProp) ⊢ WP let: "x" := Pred #42 in ^Pred '"x" @ E {{ v, v = #40 }}.
  Proof. iIntros "". wp_apply Pred_spec. wp_let. by wp_apply Pred_spec. Qed.
End LiftingTests.

Section ClosedProofs.
  Definition Σ : gFunctors := #[ heapGF ].
  Notation iProp := (iPropG heap_lang Σ).

  Lemma heap_e_closed σ : {{ ownP σ : iProp }} heap_e {{ v, v = #2 }}.
  Proof.
    iProof. iIntros "! Hσ".
    iPvs (heap_alloc nroot with "Hσ") as {h} "[? _]"; first by rewrite nclose_nroot.
    iApply heap_e_spec; last done; by rewrite nclose_nroot.
  Qed.
End ClosedProofs.
