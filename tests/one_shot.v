From iris.algebra Require Import dec_agree csum.
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
Global Opaque one_shot_example.

Class one_shotG Σ :=
  one_shot_inG :> inG heap_lang Σ (csumR (exclR unitC)(dec_agreeR Z)).
Definition one_shotGF : gFunctorList :=
  [GFunctor (constRF (csumR (exclR unitC)(dec_agreeR Z)))].
Instance inGF_one_shotG Σ : inGFs heap_lang Σ one_shotGF → one_shotG Σ.
Proof. intros [? _]; apply: inGF_inG. Qed.

Notation Pending := (Cinl (Excl ())).

Section proof.
Context {Σ : gFunctors} `{!heapG Σ, !one_shotG Σ}.
Context (heapN N : namespace) (HN : heapN ⊥ N).
Local Notation iProp := (iPropG heap_lang Σ).

Definition one_shot_inv (γ : gname) (l : loc) : iProp :=
  (l ↦ InjLV #0 ★ own γ Pending ∨
  ∃ n : Z, l ↦ InjRV #n ★ own γ (Cinr (DecAgree n)))%I.

Lemma wp_one_shot (Φ : val → iProp) :
  heap_ctx heapN ★ (∀ f1 f2 : val,
    (∀ n : Z, □ WP f1 #n {{ w, w = #true ∨ w = #false }}) ★
    □ WP f2 #() {{ g, □ WP g #() {{ _, True }} }} -★ Φ (f1,f2)%V)
  ⊢ WP one_shot_example #() {{ Φ }}.
Proof.
  iIntros "[#? Hf] /=".
  rewrite /one_shot_example. wp_seq. wp_alloc l as "Hl". wp_let.
  iPvs (own_alloc Pending) as {γ} "Hγ"; first done.
  iPvs (inv_alloc N _ (one_shot_inv γ l) with "[Hl Hγ]") as "#HN"; first done.
  { iNext. iLeft. by iSplitL "Hl". }
  iPvsIntro. iApply "Hf"; iSplit.
  - iIntros {n} "!". wp_let.
    iInv> N as "[[Hl Hγ]|H]"; last iDestruct "H" as {m} "[Hl Hγ]".
    + iApply wp_pvs. wp_cas_suc. iSplitL; [|by iLeft; iPvsIntro].
      iPvs (own_update with "Hγ") as "Hγ".
      { by apply cmra_update_exclusive with (y:=Cinr (DecAgree n)). }
      iPvsIntro; iRight; iExists n; by iSplitL "Hl".
    + wp_cas_fail. iSplitL. iRight; iExists m; by iSplitL "Hl". by iRight.
  - iIntros "!". wp_seq. wp_focus (! _)%E. iInv> N as "Hγ".
    iAssert (∃ v, l ↦ v ★ ((v = InjLV #0 ★ own γ Pending) ∨
       ∃ n : Z, v = InjRV #n ★ own γ (Cinr (DecAgree n))))%I with "[-]" as "Hv".
    { iDestruct "Hγ" as "[[Hl Hγ]|Hl]"; last iDestruct "Hl" as {m} "[Hl Hγ]".
      + iExists (InjLV #0). iFrame. eauto.
      + iExists (InjRV #m). iFrame. eauto. }
    iDestruct "Hv" as {v} "[Hl Hv]". wp_load; iPvsIntro.
    iAssert (one_shot_inv γ l ★ (v = InjLV #0 ∨ ∃ n : Z,
      v = InjRV #n ★ own γ (Cinr (DecAgree n))))%I with "[-]" as "[$ #Hv]".
    { iDestruct "Hv" as "[[% ?]|Hv]"; last iDestruct "Hv" as {m} "[% ?]"; subst.
      + iSplit. iLeft; by iSplitL "Hl". eauto.
      + iSplit. iRight; iExists m; by iSplitL "Hl". eauto. }
    wp_let. iPvsIntro. iIntros "!". wp_seq.
    iDestruct "Hv" as "[%|Hv]"; last iDestruct "Hv" as {m} "[% Hγ']"; subst.
    { by wp_match. }
    wp_match. wp_focus (! _)%E.
    iInv> N as "[[Hl Hγ]|Hinv]"; last iDestruct "Hinv" as {m'} "[Hl Hγ]".
    { iCombine "Hγ" "Hγ'" as "Hγ". by iDestruct (own_valid with "Hγ") as "%". }
    wp_load; iPvsIntro.
    iCombine "Hγ" "Hγ'" as "Hγ".
    iDestruct (own_valid with "#Hγ") as %[=->]%dec_agree_op_inv.
    iSplitL "Hl"; [iRight; by eauto|].
    wp_match. iApply wp_assert'. wp_op=>?; iPvsIntro; simplify_eq/=; eauto.
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
  - iIntros {n} "! _". wp_proj. iApply "Hf1".
  - iIntros "! _". wp_proj.
    iApply wp_wand_l; iFrame "Hf2". by iIntros {v} "#? ! _".
Qed.
End proof.
