From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.algebra Require Import excl dec_agree csum.
From iris.heap_lang Require Import assert proofmode notation.
From iris.proofmode Require Import invariants.

Definition one_shot_example : val := λ: <>,
  let: "x" := ref NONE in (
  (* tryset *) (λ: "n",
    CAS "x" NONE (SOME "n")),
  (* check  *) (λ: <>,
    let: "y" := !"x" in λ: <>,
    match: "y" with
      NONE => #()
    | SOME "n" =>
       match: !"x" with
         NONE => assert: #false
       | SOME "m" => assert: "n" = "m"
       end
    end)).
Global Opaque one_shot_example.

Definition one_shotR := csumR (exclR unitC) (dec_agreeR Z).
Definition Pending : one_shotR := (Cinl (Excl ()) : one_shotR).
Definition Shot (n : Z) : one_shotR := (Cinr (DecAgree n) : one_shotR).

Class one_shotG Σ := { one_shot_inG :> inG Σ one_shotR }.
Definition one_shotΣ : gFunctors := #[GFunctor (constRF one_shotR)].
Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section proof.
Context `{!heapG Σ, !one_shotG Σ} (N : namespace) (HN : heapN ⊥ N).

Definition one_shot_inv (γ : gname) (l : loc) : iProp Σ :=
  (l ↦ NONEV ★ own γ Pending ∨ ∃ n : Z, l ↦ SOMEV #n ★ own γ (Shot n))%I.

Lemma wp_one_shot (Φ : val → iProp Σ) :
  heap_ctx ★ (∀ f1 f2 : val,
    (∀ n : Z, □ WP f1 #n {{ w, w = #true ∨ w = #false }}) ★
    □ WP f2 #() {{ g, □ WP g #() {{ _, True }} }} -★ Φ (f1,f2)%V)
  ⊢ WP one_shot_example #() {{ Φ }}.
Proof.
  iIntros "[#? Hf] /=".
  rewrite /one_shot_example. wp_seq. wp_alloc l as "Hl". wp_let.
  iShift (own_alloc Pending) as (γ) "Hγ"; first done.
  iShift (inv_alloc N _ (one_shot_inv γ l) with "[Hl Hγ]") as "#HN".
  { iNext. iLeft. by iSplitL "Hl". }
  iShiftIntro. iApply "Hf"; iSplit.
  - iIntros (n) "!#". wp_let.
    iInv N as ">[[Hl Hγ]|H]" "Hclose"; last iDestruct "H" as (m) "[Hl Hγ]".
    + wp_cas_suc. iShift (own_update with "Hγ") as "Hγ".
      { by apply cmra_update_exclusive with (y:=Shot n). }
      iShift ("Hclose" with "[-]"); last eauto.
      iNext; iRight; iExists n; by iFrame.
    + wp_cas_fail. iShift ("Hclose" with "[-]"); last eauto.
      rewrite /one_shot_inv; eauto 10.
  - iIntros "!#". wp_seq. wp_bind (! _)%E.
    iInv N as ">Hγ" "Hclose".
    iAssert (∃ v, l ↦ v ★ ((v = NONEV ★ own γ Pending) ∨
       ∃ n : Z, v = SOMEV #n ★ own γ (Shot n)))%I with "[Hγ]" as "Hv".
    { iDestruct "Hγ" as "[[Hl Hγ]|Hl]"; last iDestruct "Hl" as (m) "[Hl Hγ]".
      + iExists NONEV. iFrame. eauto.
      + iExists (SOMEV #m). iFrame. eauto. }
    iDestruct "Hv" as (v) "[Hl Hv]". wp_load.
    iAssert (one_shot_inv γ l ★ (v = NONEV ∨ ∃ n : Z,
      v = SOMEV #n ★ own γ (Shot n)))%I with "[Hl Hv]" as "[Hinv #Hv]".
    { iDestruct "Hv" as "[[% ?]|Hv]"; last iDestruct "Hv" as (m) "[% ?]"; subst.
      + iSplit. iLeft; by iSplitL "Hl". eauto.
      + iSplit. iRight; iExists m; by iSplitL "Hl". eauto. }
    iShift ("Hclose" with "[Hinv]") as "_"; eauto; iShiftIntro.
    wp_let. iShiftIntro. iIntros "!#". wp_seq.
    iDestruct "Hv" as "[%|Hv]"; last iDestruct "Hv" as (m) "[% Hγ']"; subst.
    { by wp_match. }
    wp_match. wp_bind (! _)%E.
    iInv N as ">[[Hl Hγ]|H]" "Hclose"; last iDestruct "H" as (m') "[Hl Hγ]".
    { iCombine "Hγ" "Hγ'" as "Hγ". by iDestruct (own_valid with "Hγ") as %?. }
    wp_load.
    iCombine "Hγ" "Hγ'" as "Hγ".
    iDestruct (own_valid with "#Hγ") as %[=->]%dec_agree_op_inv.
    iShift ("Hclose" with "[Hl]") as "_".
    { iNext; iRight; by eauto. }
    iShiftIntro. wp_match. iApply wp_assert. wp_op=>?; simplify_eq/=; eauto.
Qed.

Lemma ht_one_shot (Φ : val → iProp Σ) :
  heap_ctx ⊢ {{ True }} one_shot_example #()
    {{ ff,
      (∀ n : Z, {{ True }} Fst ff #n {{ w, w = #true ∨ w = #false }}) ★
      {{ True }} Snd ff #() {{ g, {{ True }} g #() {{ _, True }} }}
    }}.
Proof.
  iIntros "#? !# _". iApply wp_one_shot. iSplit; first done.
  iIntros (f1 f2) "[#Hf1 #Hf2]"; iSplit.
  - iIntros (n) "!# _". wp_proj. iApply "Hf1".
  - iIntros "!# _". wp_proj.
    iApply wp_wand_l; iFrame "Hf2". by iIntros (v) "#? !# _".
Qed.
End proof.
