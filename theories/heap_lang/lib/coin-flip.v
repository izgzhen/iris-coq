From iris.heap_lang Require Export lifting notation.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "Type".

(** Nondeterminism and Speculation:
    Implementing "Late choice versus early choice" example from
    Logical Relations for Fine-Grained Concurrency by Turon et al. (POPL'13) *)

Definition rand: val :=
    λ: "_",
       let: "y" := ref #false in
       Fork ("y" <- #true) ;;
       !"y".

  Definition earlyChoice: val :=
    λ: "x",
       let: "r" := rand #() in
       "x" <- #0 ;;
       "r".

Section coinflip.

  Definition lateChoice: val :=
    λ: "x",
    "x" <- #0 ;;
     rand #().
    
  Context `{!heapG Σ} (N: namespace).
  
  Lemma rand_spec :
    {{{ True }}} rand #() {{{ (b : bool), RET #b; True }}}.
  Proof using N.
    iIntros (Φ) "_ HP".
    wp_lam. wp_alloc l as "Hl". wp_lam.
    iMod (inv_alloc N _ (∃ (b: bool), l ↦ #b)%I with "[Hl]") as "#Hinv"; first by eauto.
    wp_apply wp_fork. iSplitL.
    - wp_lam. iInv N as (b) ">Hl". wp_load. iModIntro. iSplitL "Hl"; first by eauto.
      iApply "HP". done.
    - iInv N as (b) ">Hl". wp_store. iModIntro. iSplitL; eauto.    
  Qed.

  Lemma earlyChoice_spec (x: loc) :
    <<< x ↦ - >>>
        earlyChoice #x
        @ ⊤
    <<< ∃ (b: bool), x ↦ #0, RET #b >>>.
  Proof using N.
    iApply wp_atomic_intro. iIntros (Φ) "AU". wp_lam.    
    wp_bind (rand _)%E. iApply rand_spec; first done.
    iIntros (b) "!> _". wp_let.
    wp_bind (_ <- _)%E.
    iMod "AU" as "[Hl [_ Hclose]]".
    iDestruct "Hl" as (v) "Hl".
    wp_store.
    iMod ("Hclose" with "[Hl]") as "HΦ"; first by eauto.
    iModIntro. wp_seq. done.
  Qed.

  (* lateChoice can currently not be proved in Iris *)
  Lemma lateChoice_spec (x: loc) :
    <<< x ↦ - >>>
        lateChoice #x
        @ ⊤
    <<< ∃ (b: bool), x ↦ #0, RET #b >>>.
  Proof using N.
    iApply wp_atomic_intro. iIntros (Φ) "AU". wp_lam.
    wp_bind (_ <- _)%E.
    iMod "AU" as "[Hl [_ Hclose]]".
    iDestruct "Hl" as (v) "Hl".
    wp_store.
    (* now we have to "predict" the value of b, which is the result of calling rand.
       but we can't know at this point what that value is. *)
    iMod ("Hclose" $! true with "[Hl]") as "AU"; first by eauto.
    iModIntro. wp_seq.
    iApply rand_spec; first done.
    iIntros (b) "!> _".    
    Abort.

End coinflip.

Section prophecy.

  Context `{!heapG Σ} (N: namespace).

  Record prophecy {Σ} `{!heapG Σ} := Prophecy {
    (* -- operations -- *)
    new_prophecy : val;
    resolve_prophecy : val;
    (* -- predicates -- *)
    is_prophecy : proph -> val -> iProp Σ;
    (* -- general properties -- *)
    new_prophecy_spec:
      {{{ True }}} new_prophecy #() {{{ p, RET #p; ∃ v, is_prophecy p v }}};
    resolve_prophecy_spec p v e w:
      IntoVal e w ->
      {{{ is_prophecy p v }}} resolve_prophecy #p e {{{ RET w; ⌜v = w⌝ }}} 
  }.
    
  Context `{pr: prophecy}.

  Definition val_to_bool v : bool :=
    match v with
    | LitV (LitBool b) => b
    | _                => true
    end.

  Definition lateChoice_proph: val :=
    λ: "x",
      let: "p" := new_prophecy pr #() in
      "x" <- #0 ;;
      let: "r" := rand #() in
      resolve_prophecy pr "p" "r".
  
  Lemma lateChoice_proph_spec (x: loc) :
    <<< x ↦ - >>>
        lateChoice_proph #x
        @ ⊤
    <<< ∃ (b: bool), x ↦ #0, RET #b >>>. 
  Proof using N.
    iApply wp_atomic_intro. iIntros (Φ) "AU". wp_lam.
    wp_apply new_prophecy_spec; first done.
    iIntros (p) "Hp". iDestruct "Hp" as (v) "Hp".
    wp_let.    
    wp_bind (_ <- _)%E.
    iMod "AU" as "[Hl [_ Hclose]]".
    iDestruct "Hl" as (v') "Hl".
    wp_store.
    iMod ("Hclose" $! (val_to_bool v) with "[Hl]") as "HΦ"; first by eauto.
    iModIntro. wp_seq. wp_apply rand_spec; try done.
    iIntros (b') "_". wp_let.
    iApply (resolve_prophecy_spec with "Hp").
    iNext. iIntros (->). done.
  Qed.

End prophecy.
