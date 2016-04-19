From iris.program_logic Require Import saved_one_shot hoare.
From iris.heap_lang.lib.barrier Require Import proof specification.
From iris.heap_lang Require Import notation par proofmode.
From iris.proofmode Require Import invariants.
Import uPred.

Definition client eM eW1 eW2 : expr [] :=
  let: "b" := newbarrier #() in
  (eM ;; ^signal '"b") || ((^wait '"b" ;; eW1) || (^wait '"b" ;; eW2)).

Section proof.
Context (G : cFunctor).
Context {Σ : gFunctors} `{!heapG Σ, !barrierG Σ, !spawnG Σ, !oneShotG heap_lang Σ G}.
Context (heapN N : namespace).
Local Notation iProp := (iPropG heap_lang Σ).
Local Notation X := (G iProp).

Definition barrier_res γ (Φ : X → iProp) : iProp :=
  (∃ x, one_shot_own γ x ★ Φ x)%I.

Lemma worker_spec e γ l (Φ Ψ : X → iProp) :
  (recv heapN N l (barrier_res γ Φ) ★ ∀ x, {{ Φ x }} e {{ _, Ψ x }})
  ⊢ WP wait (%l) ;; e {{ _, barrier_res γ Ψ }}.
Proof.
  iIntros "[Hl #He]". wp_apply wait_spec; iFrame "Hl".
  iIntros "Hγ"; iDestruct "Hγ" as {x} "[#Hγ Hx]".
  wp_seq. iApply wp_wand_l. iSplitR; [|by iApply "He" "!"].
  iIntros {v} "?"; iExists x; by iSplit.
Qed.

Context (P : iProp) (Φ Φ1 Φ2 Ψ Ψ1 Ψ2 : X -n> iProp).
Context {Φ_split : ∀ x, Φ x ⊢ (Φ1 x ★ Φ2 x)}.
Context {Ψ_join  : ∀ x, (Ψ1 x ★ Ψ2 x) ⊢ Ψ x}.

Lemma P_res_split γ : barrier_res γ Φ ⊢ (barrier_res γ Φ1 ★ barrier_res γ Φ2).
Proof.
  iIntros "Hγ"; iDestruct "Hγ" as {x} "[#Hγ Hx]".
  iDestruct Φ_split "Hx" as "[H1 H2]". by iSplitL "H1"; iExists x; iSplit.
Qed.

Lemma Q_res_join γ : (barrier_res γ Ψ1 ★ barrier_res γ Ψ2) ⊢ ▷ barrier_res γ Ψ.
Proof.
  iIntros "[Hγ Hγ']";
  iDestruct "Hγ" as {x} "[#Hγ Hx]"; iDestruct "Hγ'" as {x'} "[#Hγ' Hx']".
  iDestruct (one_shot_agree γ x x') "- !" as "Hxx"; first (by iSplit).
  iNext. iRewrite -"Hxx" in "Hx'".
  iExists x; iFrame "Hγ". iApply Ψ_join; by iSplitL "Hx".
Qed.

Lemma client_spec_new (eM eW1 eW2 : expr []) (eM' eW1' eW2' : expr ("b" :b: [])) :
  heapN ⊥ N → eM' = wexpr' eM → eW1' = wexpr' eW1 → eW2' = wexpr' eW2 →
  (heap_ctx heapN ★ P
  ★ {{ P }} eM {{ _, ∃ x, Φ x }}
  ★ (∀ x, {{ Φ1 x }} eW1 {{ _, Ψ1 x }})
  ★ (∀ x, {{ Φ2 x }} eW2 {{ _, Ψ2 x }}))
  ⊢ WP client eM' eW1' eW2' {{ _, ∃ γ, barrier_res γ Ψ }}.
Proof.
  iIntros {HN -> -> ->} "/= (#Hh&HP&#He&#He1&#He2)"; rewrite /client.
  iPvs one_shot_alloc as {γ} "Hγ".
  wp_apply (newbarrier_spec heapN N (barrier_res γ Φ)); auto.
  iFrame "Hh". iIntros {l} "[Hr Hs]".
  set (workers_post (v : val) := (barrier_res γ Ψ1 ★ barrier_res γ Ψ2)%I).
  wp_let. wp_apply (wp_par _ _ (λ _, True)%I workers_post); first done.
  iFrame "Hh". iSplitL "HP Hs Hγ"; [|iSplitL "Hr"].
  - wp_focus eM. iApply wp_wand_l; iSplitR "HP"; [|iApply "He" "HP"].
    iIntros {v} "HP"; iDestruct "HP" as {x} "HP". wp_let.
    iPvs (one_shot_init _ _ x) "Hγ" as "Hx".
    iApply signal_spec; iFrame "Hs"; iSplit; last done.
    iExists x; by iSplitL "Hx".
  - iDestruct recv_weaken "[] Hr" as "Hr".
    { iIntros "?". by iApply P_res_split "-". }
    iPvs recv_split "Hr" as "[H1 H2]"; first done.
    wp_apply (wp_par _ _ (λ _, barrier_res γ Ψ1)%I
      (λ _, barrier_res γ Ψ2)%I); first done.
    iSplit; [done|]; iSplitL "H1"; [|iSplitL "H2"].
    + by iApply worker_spec; iSplitL "H1".
    + by iApply worker_spec; iSplitL "H2".
    + iIntros {v1 v2} "?". by iNext.
  - iIntros {_ v} "[_ H]"; iPoseProof Q_res_join "H". by iNext; iExists γ.
Qed.
End proof.
