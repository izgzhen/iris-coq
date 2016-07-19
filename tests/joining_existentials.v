From iris.algebra Require Import csum.
From iris.program_logic Require Import hoare.
From iris.heap_lang.lib.barrier Require Import proof specification.
From iris.heap_lang Require Import notation par proofmode.
From iris.proofmode Require Import invariants.
Import uPred.

Class oneShotG (Λ : language) (Σ : gFunctors) (F : cFunctor) :=
  one_shot_inG :>
    inG Λ Σ (csumR (exclR unitC) (agreeR $ laterC $ F (iPrePropG Λ Σ))).
Definition oneShotGF (F : cFunctor) : gFunctor :=
  GFunctor (csumRF (exclRF unitC) (agreeRF (▶ F))).
Instance inGF_oneShotG  `{inGF Λ Σ (oneShotGF F)} : oneShotG Λ Σ F.
Proof. apply: inGF_inG. Qed.

Definition client eM eW1 eW2 : expr :=
  let: "b" := newbarrier #() in
  (eM ;; signal "b") || ((wait "b" ;; eW1) || (wait "b" ;; eW2)).
Global Opaque client.

Section proof.
Context (G : cFunctor).
Context `{!heapG Σ, !barrierG Σ, !spawnG Σ, !oneShotG heap_lang Σ G}.
Context (N : namespace).
Local Notation iProp := (iPropG heap_lang Σ).
Local Notation X := (G iProp).

Definition barrier_res γ (Φ : X → iProp) : iProp :=
  (∃ x, own γ (Cinr $ to_agree $
               Next (cFunctor_map G (iProp_fold, iProp_unfold) x)) ★ Φ x)%I.

Lemma worker_spec e γ l (Φ Ψ : X → iProp) `{!Closed [] e} :
  recv N l (barrier_res γ Φ) ★ (∀ x, {{ Φ x }} e {{ _, Ψ x }})
  ⊢ WP wait #l ;; e {{ _, barrier_res γ Ψ }}.
Proof.
  iIntros "[Hl #He]". wp_apply wait_spec; iFrame "Hl".
  iDestruct 1 as (x) "[#Hγ Hx]".
  wp_seq. iApply wp_wand_l. iSplitR; [|by iApply "He"].
  iIntros (v) "?"; iExists x; by iSplit.
Qed.

Context (P : iProp) (Φ Φ1 Φ2 Ψ Ψ1 Ψ2 : X -n> iProp).
Context {Φ_split : ∀ x, Φ x ⊢ (Φ1 x ★ Φ2 x)}.
Context {Ψ_join  : ∀ x, (Ψ1 x ★ Ψ2 x) ⊢ Ψ x}.

Lemma P_res_split γ : barrier_res γ Φ ⊢ barrier_res γ Φ1 ★ barrier_res γ Φ2.
Proof.
  iDestruct 1 as (x) "[#Hγ Hx]".
  iDestruct (Φ_split with "Hx") as "[H1 H2]". by iSplitL "H1"; iExists x; iSplit.
Qed.

Lemma Q_res_join γ : barrier_res γ Ψ1 ★ barrier_res γ Ψ2 ⊢ ▷ barrier_res γ Ψ.
Proof.
  iIntros "[Hγ Hγ']";
  iDestruct "Hγ" as (x) "[#Hγ Hx]"; iDestruct "Hγ'" as (x') "[#Hγ' Hx']".
  iAssert (▷ (x ≡ x'))%I as "Hxx" .
  { iCombine "Hγ" "Hγ'" as "Hγ2". iClear "Hγ Hγ'".
    rewrite own_valid csum_validI /= agree_validI agree_equivI later_equivI /=.
    rewrite -{2}[x]cFunctor_id -{2}[x']cFunctor_id.
    rewrite (ne_proper (cFunctor_map G) (cid, cid) (_ ◎ _, _ ◎ _)); last first.
    { by split; intro; simpl; symmetry; apply iProp_fold_unfold. }
    rewrite !cFunctor_compose. iNext. by iRewrite "Hγ2". }
  iNext. iRewrite -"Hxx" in "Hx'".
  iExists x; iFrame "Hγ". iApply Ψ_join; by iSplitL "Hx".
Qed.

Lemma client_spec_new eM eW1 eW2 `{!Closed [] eM, !Closed [] eW1, !Closed [] eW2} :
  heapN ⊥ N →
  heap_ctx ★ P
  ★ {{ P }} eM {{ _, ∃ x, Φ x }}
  ★ (∀ x, {{ Φ1 x }} eW1 {{ _, Ψ1 x }})
  ★ (∀ x, {{ Φ2 x }} eW2 {{ _, Ψ2 x }})
  ⊢ WP client eM eW1 eW2 {{ _, ∃ γ, barrier_res γ Ψ }}.
Proof.
  iIntros (HN) "/= (#Hh&HP&#He&#He1&#He2)"; rewrite /client.
  iPvs (own_alloc (Cinl (Excl ()))) as (γ) "Hγ". done.
  wp_apply (newbarrier_spec N (barrier_res γ Φ)); auto.
  iFrame "Hh". iIntros (l) "[Hr Hs]".
  set (workers_post (v : val) := (barrier_res γ Ψ1 ★ barrier_res γ Ψ2)%I).
  wp_let. wp_apply (wp_par _ (λ _, True)%I workers_post);
    try iFrame "Hh"; first done.
  iSplitL "HP Hs Hγ"; [|iSplitL "Hr"].
  - wp_focus eM. iApply wp_wand_l; iSplitR "HP"; [|by iApply "He"].
    iIntros (v) "HP"; iDestruct "HP" as (x) "HP". wp_let.
    iPvs (own_update _ _ (Cinr (to_agree _)) with "Hγ") as "Hx".
    by apply cmra_update_exclusive.
    iApply signal_spec; iFrame "Hs"; iSplit; last done.
    iExists x; auto.
  - iDestruct (recv_weaken with "[] Hr") as "Hr"; first by iApply P_res_split.
    iPvs (recv_split with "Hr") as "[H1 H2]"; first done.
    wp_apply (wp_par _ (λ _, barrier_res γ Ψ1)%I
      (λ _, barrier_res γ Ψ2)%I); try iFrame "Hh"; first done.
    iSplitL "H1"; [|iSplitL "H2"].
    + iApply worker_spec; auto.
    + iApply worker_spec; auto.
    + auto.
  - iIntros (_ v) "[_ H]"; iPoseProof (Q_res_join with "H"). auto.
Qed.
End proof.
