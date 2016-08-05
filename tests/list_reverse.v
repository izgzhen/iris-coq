(** Correctness of in-place list reversal *)
From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode notation.

Section list_reverse.
Context `{!heapG Σ}.
Implicit Types l : loc.

Fixpoint is_list (hd : val) (xs : list val) : iProp Σ :=
  match xs with
  | [] => hd = NONEV
  | x :: xs => ∃ l hd', hd = SOMEV #l ★ l ↦ (x,hd') ★ is_list hd' xs
  end%I.

Definition rev : val :=
  rec: "rev" "hd" "acc" :=
    match: "hd" with
      NONE => "acc"
    | SOME "l" =>
       let: "tmp1" := Fst !"l" in
       let: "tmp2" := Snd !"l" in
       "l" <- ("tmp1", "acc");;
       "rev" "tmp2" "hd"
    end.
Global Opaque rev.

Lemma rev_acc_wp hd acc xs ys (Φ : val → iProp Σ) :
  heap_ctx ★ is_list hd xs ★ is_list acc ys ★
    (∀ w, is_list w (reverse xs ++ ys) -★ Φ w)
  ⊢ WP rev hd acc {{ Φ }}.
Proof.
  iIntros "(#Hh & Hxs & Hys & HΦ)".
  iLöb (hd acc xs ys Φ) as "IH". wp_rec. wp_let.
  destruct xs as [|x xs]; iSimplifyEq.
  - wp_match. by iApply "HΦ".
  - iDestruct "Hxs" as (l hd') "(% & Hx & Hxs)"; iSimplifyEq.
    wp_match. wp_load. wp_proj. wp_let. wp_load. wp_proj. wp_let. wp_store.
    iApply ("IH" $! hd' (SOMEV #l) xs (x :: ys) with "Hxs [Hx Hys]"); simpl.
    { iExists l, acc; by iFrame. }
    iIntros (w). rewrite cons_middle assoc -reverse_cons. iApply "HΦ".
Qed.

Lemma rev_wp hd xs (Φ : val → iProp Σ) :
  heap_ctx ★ is_list hd xs ★ (∀ w, is_list w (reverse xs) -★ Φ w)
  ⊢ WP rev hd (InjL #()) {{ Φ }}.
Proof.
  iIntros "(#Hh & Hxs & HΦ)".
  iApply (rev_acc_wp hd NONEV xs []); iFrame "Hh Hxs".
  iSplit; first done. iIntros (w). rewrite right_id_L. iApply "HΦ".
Qed.
End list_reverse.
