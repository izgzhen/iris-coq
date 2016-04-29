From iris.algebra Require Import one_shot dec_agree.
From iris.program_logic Require Import hoare.
From iris.heap_lang Require Import assert proofmode notation.
From iris.proofmode Require Import invariants ghost_ownership.
Import uPred.

Definition one_shot_example : val := λ: <>,
  let: "x" := ref (InjL #0) in (
  (* tryset *) (λ: "n",
    CAS '"x" (InjL #0) (InjR '"n")),
  (* check  *) (λ: <>,
    let: "y" := !'"x" in λ: <>,
    match: '"y" with
      InjL <> => #()
    | InjR "n" =>
       match: !'"x" with
         InjL <> => Assert #false
       | InjR "m" => Assert ('"n" = '"m")
       end
    end)).

Class one_shotG Σ :=
  OneShotG { one_shot_inG :> inG heap_lang Σ (one_shotR (dec_agreeR Z)) }.
Definition one_shotGF : gFunctorList :=
  [GFunctor (constRF (one_shotR (dec_agreeR Z)))].
Instance inGF_one_shotG Σ : inGFs heap_lang Σ one_shotGF → one_shotG Σ.
Proof. intros [? _]; split; apply: inGF_inG. Qed.

Section proof.
Context {Σ : gFunctors} `{!heapG Σ, !one_shotG Σ}.
Context (heapN N : namespace) (HN : heapN ⊥ N).
Local Notation iProp := (iPropG heap_lang Σ).

Definition one_shot_inv (γ : gname) (l : loc) : iProp :=
  (l ↦ InjLV #0 ★ own γ OneShotPending ∨
  ∃ n : Z, l ↦ InjRV #n ★ own γ (Shot (DecAgree n)))%I.

Lemma wp_one_shot (Φ : val → iProp) :
  (heap_ctx heapN ★ ∀ f1 f2 : val,
    (∀ n : Z, □ WP f1 #n {{ w, w = #true ∨ w = #false }}) ★
    □ WP f2 #() {{ g, □ WP g #() {{ _, True }} }} -★ Φ (f1,f2)%V)
  ⊢ WP one_shot_example #() {{ Φ }}.
Proof.
  iIntros "[#? Hf] /=".
  rewrite /one_shot_example. wp_seq. wp_alloc l as "Hl". wp_let.
  iPvs (own_alloc OneShotPending) as {γ} "Hγ"; first done.
  iPvs (inv_alloc N _ (one_shot_inv γ l) with "[Hl Hγ]") as "#HN"; first done.
  { iNext. iLeft. by iSplitL "Hl". }
  iPvsIntro. iApply "Hf"; iSplit.
  - iIntros {n} "!". wp_let.
    iInv> N as "[[Hl Hγ]|H]"; last iDestruct "H" as {m} "[Hl Hγ]".
    + iApply wp_pvs. wp_cas_suc. iSplitL; [|by iLeft; iPvsIntro].
      iPvs (own_update with "Hγ") as "Hγ".
      { (* FIXME: canonical structures are not working *)
        by apply (one_shot_update_shoot (DecAgree n : dec_agreeR _)). }
      iPvsIntro; iRight; iExists n; by iSplitL "Hl".
    + wp_cas_fail. iSplitL. iRight; iExists m; by iSplitL "Hl". by iRight.
  - iIntros "!". wp_seq. wp_focus (! _)%E. iInv> N as "Hγ".
    iAssert (∃ v, l ↦ v ★ ((v = InjLV #0 ★ own γ OneShotPending) ∨
       ∃ n : Z, v = InjRV #n ★ own γ (Shot (DecAgree n))))%I as "Hv" with "-".
    { iDestruct "Hγ" as "[[Hl Hγ]|Hl]"; last iDestruct "Hl" as {m} "[Hl Hγ]".
      + iExists (InjLV #0). iFrame "Hl". iLeft; by iSplit.
      + iExists (InjRV #m). iFrame "Hl". iRight; iExists m; by iSplit. }
    iDestruct "Hv" as {v} "[Hl Hv]". wp_load.
    iAssert (one_shot_inv γ l ★ (v = InjLV #0 ∨ ∃ n : Z,
      v = InjRV #n ★ own γ (Shot (DecAgree n))))%I as "[$ #Hv]" with "-".
    { iDestruct "Hv" as "[[% ?]|Hv]"; last iDestruct "Hv" as {m} "[% ?]"; subst.
      + iSplit. iLeft; by iSplitL "Hl". by iLeft.
      + iSplit. iRight; iExists m; by iSplitL "Hl". iRight; iExists m; by iSplit. }
    wp_let. iPvsIntro. iIntros "!". wp_seq.
    iDestruct "Hv" as "[%|Hv]"; last iDestruct "Hv" as {m} "[% Hγ']"; subst.
    { wp_case. wp_seq. by iPvsIntro. }
    wp_case. wp_let. wp_focus (! _)%E.
    iInv> N as "[[Hl Hγ]|Hinv]"; last iDestruct "Hinv" as {m'} "[Hl Hγ]".
    { iCombine "Hγ" "Hγ'" as "Hγ". by iDestruct (own_valid with "Hγ") as "%". }
    wp_load.
    iCombine "Hγ" "Hγ'" as "Hγ".
    iDestruct (own_valid with "Hγ !") as % [=->]%dec_agree_op_inv.
    iSplitL "Hl"; [iRight; iExists m; by iSplit|].
    wp_case. wp_let. iApply wp_assert'. wp_op=>?; simplify_eq/=.
    iSplit. done. by iNext.
Qed.

Lemma hoare_one_shot (Φ : val → iProp) :
  heap_ctx heapN ⊢ {{ True }} one_shot_example #()
    {{ ff,
      (∀ n : Z, {{ True }} Fst ff #n {{ w, w = #true ∨ w = #false }}) ★
      {{ True }} Snd ff #() {{ g, {{ True }} g #() {{ _, True }} }}
    }}.
Proof.
  iIntros "#? ! _". iApply wp_one_shot. iSplit; first done.
  iIntros {f1 f2} "[#Hf1 #Hf2]"; iSplit.
  - iIntros {n} "! _". wp_proj. iApply ("Hf1" with "!").
  - iIntros "! _". wp_proj.
    iApply wp_wand_l; iFrame "Hf2". by iIntros {v} "#? ! _".
Qed.
End proof.
