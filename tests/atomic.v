From iris.program_logic Require Export hoare weakestpre.
From iris.program_logic Require Export pviewshifts.
From iris.program_logic Require Import ownership.
From iris.algebra Require Import upred_big_op.
From iris.prelude Require Export coPset.
From iris.proofmode Require Import tactics pviewshifts weakestpre.
Import uPred.

Section atomic.
  Context `{irisG Λ Σ}.
  (* <x, α> e @ E_i, E_o <v, β x v> *)
  Definition atomic_triple {A: Type}
             (α: A → iProp Σ)
             (β: A → val _ → iProp Σ)
             (Ei Eo: coPset)
             (e: expr _) : iProp Σ :=
    (∀ P Q, (P ={Eo, Ei}=> ∃ x:A,
                                α x ★
                                ((α x ={Ei, Eo}=★ P) ∧
                                 (∀ v, β x v ={Ei, Eo}=★ Q x v))
            ) -★ {{ P }} e @ ⊤ {{ v, (∃ x: A, Q x v) }})%I.

  Arguments atomic_triple {_} _ _ _ _ _.
End atomic.

From iris.heap_lang Require Export lang.
From iris.proofmode Require Import invariants tactics.
From iris.heap_lang Require Import proofmode notation.

Section demo.
  Context `{!heapG Σ} (N : namespace).

  Definition incr: val :=
    rec: "incr" "l" :=
       let: "oldv" := !"l" in
       if: CAS "l" "oldv" ("oldv" + #1)
         then "oldv" (* return old value if success *)
         else "incr" "l".

  Global Opaque incr.

  (* TODO: Can we have a more WP-style definition and avoid the equality? *)
  Definition incr_triple (l: loc) :=
    atomic_triple (fun (v: Z) => l ↦ #v)%I
                  (fun v ret => ret = #v ★ l ↦ #(v + 1))%I
                  (nclose heapN)
                  ⊤
                  (incr #l).

  Lemma incr_atomic_spec: ∀ (l: loc), heapN ⊥ N → heap_ctx ⊢ incr_triple l.
  Proof.
    iIntros (l HN) "#?".
    rewrite /incr_triple.
    rewrite /atomic_triple.
    iIntros (P Q) "#Hvs".
    iLöb as "IH".
    iIntros "!# HP".
    wp_rec.
    wp_bind (! _)%E.
    iVs ("Hvs" with "HP") as (x) "[Hl [Hvs' _]]".
    wp_load.
    iVs ("Hvs'" with "Hl") as "HP".
    iVsIntro. wp_let. wp_bind (CAS _ _ _). wp_op.
    iVs ("Hvs" with "HP") as (x') "[Hl Hvs']".
    destruct (decide (x = x')).
    - subst.
      iDestruct "Hvs'" as "[_ Hvs']".
      iSpecialize ("Hvs'" $! #x').
      wp_cas_suc.
      iVs ("Hvs'" with "[Hl]") as "HQ"; first by iFrame.
      iVsIntro. wp_if. iVsIntro. by iExists x'.
    - iDestruct "Hvs'" as "[Hvs' _]".
      wp_cas_fail.
      iVs ("Hvs'" with "[Hl]") as "HP"; first by iFrame.
      iVsIntro. wp_if. by iApply "IH".
  Qed.
End demo.
