(* This file contains a formalization of the monotone counter, but with an
explicit contruction of the monoid, as we have also done in the proof mode
paper. A version that uses the authoritative monoid and natural number monoid
under max can be found in `heap_lang/lib/counter.v`. *)
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.program_logic Require Export hoare.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

Definition newcounter : val := λ: <>, ref #0.
Definition inc : val :=
  rec: "inc" "l" :=
    let: "n" := !"l" in
    if: CAS "l" "n" (#1 + "n") then #() else "inc" "l".
Definition read : val := λ: "l", !"l".
Global Opaque newcounter inc read.

(** The CMRA we need. *)
Inductive M := Auth : nat → M | Frag : nat → M | Bot.

Section M.
  Arguments cmra_op _ !_ !_/.
  Arguments op _ _ !_ !_/.
  Arguments core _ _ !_/.

  Canonical Structure M_C : cofeT := leibnizC M.

  Instance M_valid : Valid M := λ x, x ≠ Bot.
  Instance M_op : Op M := λ x y,
    match x, y with
    | Auth n, Frag j | Frag j, Auth n => if decide (j ≤ n)%nat then Auth n else Bot
    | Frag i, Frag j => Frag (max i j)
    | _, _ => Bot
    end.
  Instance M_pcore : PCore M := λ x,
    Some match x with Auth j | Frag j => Frag j | _ => Bot end.
  Instance M_empty : Empty M := Frag 0.

  Definition M_ra_mixin : RAMixin M.
  Proof.
    apply ra_total_mixin; try solve_proper || eauto.
    - intros [n1|i1|] [n2|i2|] [n3|i3|];
        repeat (simpl; case_decide); f_equal/=; lia.
    - intros [n1|i1|] [n2|i2|]; repeat (simpl; case_decide); f_equal/=; lia.
    - intros [n|i|]; repeat (simpl; case_decide); f_equal/=; lia.
    - by intros [n|i|].
    - intros [n1|i1|] y [[n2|i2|] ?]; exists (core y); simplify_eq/=;
        repeat (simpl; case_decide); f_equal/=; lia.
    - intros [n1|i1|] [n2|i2|]; simpl; by try case_decide.
  Qed.
  Canonical Structure M_R : cmraT := discreteR M M_ra_mixin.
  Definition M_ucmra_mixin : UCMRAMixin M.
  Proof.
    split; try (done || apply _).
    intros [?|?|]; simpl; try case_decide; f_equal/=; lia.
  Qed.
  Canonical Structure M_UR : ucmraT := discreteUR M M_ra_mixin M_ucmra_mixin.

  Global Instance frag_persistent n : Persistent (Frag n).
  Proof. by constructor. Qed.
  Lemma auth_frag_valid j n : ✓ (Auth n ⋅ Frag j) → (j ≤ n)%nat.
  Proof. simpl. case_decide. done. by intros []. Qed.
  Lemma auth_frag_op (j n : nat) : (j ≤ n)%nat → Auth n = Auth n ⋅ Frag j.
  Proof. intros. by rewrite /= decide_True. Qed.

  Lemma M_update n : Auth n ~~> Auth (S n).
  Proof.
    apply cmra_discrete_update=>-[m|j|] /= ?; repeat case_decide; done || lia.
  Qed.
End M.

Class counterG Σ := CounterG { counter_tokG :> inG Σ M_UR }.
Definition counterΣ : gFunctors := #[GFunctor (constRF M_UR)].
Instance subG_counterΣ {Σ} : subG counterΣ Σ → counterG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section proof.
Context `{!heapG Σ, !counterG Σ}.
Implicit Types l : loc.

Definition I (γ : gname) (l : loc) : iProp Σ :=
  (∃ c : nat, l ↦ #c ★ own γ (Auth c))%I.

Definition C (l : loc) (n : nat) : iProp Σ :=
  (∃ N γ, heapN ⊥ N ∧ heap_ctx ∧ inv N (I γ l) ∧ own γ (Frag n))%I.

(** The main proofs. *)
Global Instance C_persistent l n : PersistentP (C l n).
Proof. apply _. Qed.

Lemma newcounter_spec N :
  heapN ⊥ N →
  heap_ctx ⊢ {{ True }} newcounter #() {{ v, ∃ l, v = #l ∧ C l 0 }}.
Proof.
  iIntros (?) "#Hh !# _ /=". rewrite /newcounter /=. wp_seq. wp_alloc l as "Hl".
  iUpd (own_alloc (Auth 0)) as (γ) "Hγ"; first done.
  rewrite (auth_frag_op 0 0) //; iDestruct "Hγ" as "[Hγ Hγf]".
  iUpd (inv_alloc N _ (I γ l) with "[Hl Hγ]") as "#?".
  { iIntros "!>". iExists 0%nat. by iFrame. }
  iUpdIntro. rewrite /C; eauto 10.
Qed.

Lemma inc_spec l n :
  {{ C l n }} inc #l {{ v, v = #() ∧ C l (S n) }}.
Proof.
  iIntros "!# Hl /=". iLöb as "IH". wp_rec.
  iDestruct "Hl" as (N γ) "(% & #Hh & #Hinv & Hγf)".
  wp_bind (! _)%E; iInv N as (c) "[Hl Hγ]" "Hclose".
  wp_load. iUpd ("Hclose" with "[Hl Hγ]"); [iNext; iExists c; by iFrame|].
  iUpdIntro. wp_let. wp_op.
  wp_bind (CAS _ _ _). iInv N as (c') ">[Hl Hγ]" "Hclose".
  destruct (decide (c' = c)) as [->|].
  - iCombine "Hγ" "Hγf" as "Hγ".
    iDestruct (own_valid with "Hγ") as %?%auth_frag_valid; rewrite -auth_frag_op //.
    iUpd (own_update with "Hγ") as "Hγ"; first apply M_update.
    rewrite (auth_frag_op (S n) (S c)); last lia; iDestruct "Hγ" as "[Hγ Hγf]".
    wp_cas_suc. iUpd ("Hclose" with "[Hl Hγ]").
    { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
    iUpdIntro. wp_if. iUpdIntro; rewrite {3}/C; eauto 10.
  - wp_cas_fail; first (intros [=]; abstract omega).
    iUpd ("Hclose" with "[Hl Hγ]"); [iNext; iExists c'; by iFrame|].
    iUpdIntro. wp_if. iApply ("IH" with "[Hγf]"). rewrite {3}/C; eauto 10.
Qed.

Lemma read_spec l n :
  {{ C l n }} read #l {{ v, ∃ m : nat, ■ (v = #m ∧ n ≤ m) ∧ C l m }}.
Proof.
  iIntros "!# Hl /=". iDestruct "Hl" as (N γ) "(% & #Hh & #Hinv & Hγf)".
  rewrite /read /=. wp_let. iInv N as (c) "[Hl Hγ]" "Hclose". wp_load.
  iDestruct (own_valid γ (Frag n ⋅ Auth c) with "[-]") as % ?%auth_frag_valid.
  { iApply own_op. by iFrame. }
  rewrite (auth_frag_op c c); last lia; iDestruct "Hγ" as "[Hγ Hγf']".
  iUpd ("Hclose" with "[Hl Hγ]"); [iNext; iExists c; by iFrame|].
  iUpdIntro; rewrite /C; eauto 10 with omega.
Qed.
End proof.
