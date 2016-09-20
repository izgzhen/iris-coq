From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.heap_lang Require Import proofmode notation.

Definition newcounter : val := λ: <>, ref #0.
Definition inc : val :=
  rec: "inc" "l" :=
    let: "n" := !"l" in
    if: CAS "l" "n" (#1 + "n") then #() else "inc" "l".
Definition read : val := λ: "l", !"l".
Global Opaque newcounter inc get.

(** The CMRA we need. *)
Class counterG Σ := CounterG { counter_tokG :> inG Σ (authR mnatUR) }.
Definition counterΣ : gFunctors := #[GFunctor (constRF (authR mnatUR))].

Instance subG_counterΣ {Σ} : subG counterΣ Σ → counterG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section proof.
Context `{!heapG Σ, !counterG Σ} (N : namespace).

Definition counter_inv (γ : gname) (l : loc) : iProp Σ :=
  (∃ n, own γ (● (n : mnat)) ★ l ↦ #n)%I.

Definition counter (l : loc) (n : nat) : iProp Σ :=
  (∃ γ, heapN ⊥ N ∧ heap_ctx ∧
        inv N (counter_inv γ l) ∧ own γ (◯ (n : mnat)))%I.

(** The main proofs. *)
Global Instance counter_persistent l n : PersistentP (counter l n).
Proof. apply _. Qed.

Lemma newcounter_spec (R : iProp Σ) Φ :
  heapN ⊥ N →
  heap_ctx ★ (∀ l, counter l 0 -★ Φ #l) ⊢ WP newcounter #() {{ Φ }}.
Proof.
  iIntros (?) "[#Hh HΦ]". rewrite /newcounter /=. wp_seq. wp_alloc l as "Hl".
  iVs (own_alloc (● (O:mnat) ⋅ ◯ (O:mnat))) as (γ) "[Hγ Hγ']"; first done.
  iVs (inv_alloc N _ (counter_inv γ l) with "[Hl Hγ]").
  { iNext. iExists 0%nat. by iFrame. }
  iVsIntro. iApply "HΦ". rewrite /counter; eauto 10.
Qed.

Lemma inc_spec l n (Φ : val → iProp Σ) :
  counter l n ★ (counter l (S n) -★ Φ #()) ⊢ WP inc #l {{ Φ }}.
Proof.
  iIntros "[Hl HΦ]". iLöb as "IH". wp_rec.
  iDestruct "Hl" as (γ) "(% & #? & #Hinv & Hγf)".
  wp_bind (! _)%E. iInv N as (c) ">[Hγ Hl]" "Hclose".
  wp_load. iVs ("Hclose" with "[Hl Hγ]") as "_"; [iNext; iExists c; by iFrame|].
  iVsIntro. wp_let. wp_op.
  wp_bind (CAS _ _ _). iInv N as (c') ">[Hγ Hl]" "Hclose".
  destruct (decide (c' = c)) as [->|].
  - iDestruct (own_valid_2 with "[$Hγ $Hγf]")
      as %[?%mnat_included _]%auth_valid_discrete_2.
    iVs (own_update_2 with "[$Hγ $Hγf]") as "[Hγ Hγf]".
    { apply auth_update, (mnat_local_update _ _ (S c)); auto. } 
    wp_cas_suc. iVs ("Hclose" with "[Hl Hγ]") as "_".
    { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
    iVsIntro. wp_if. iApply "HΦ"; iExists γ; repeat iSplit; eauto.
    iApply (own_mono with "Hγf"). apply: auth_frag_mono.
    by apply mnat_included, le_n_S.
  - wp_cas_fail; first (by intros [= ?%Nat2Z.inj]).
    iVs ("Hclose" with "[Hl Hγ]") as "_"; [iNext; iExists c'; by iFrame|].
    iVsIntro. wp_if. iApply ("IH" with "[Hγf] HΦ"). rewrite {3}/counter; eauto 10.
Qed.

Lemma read_spec l j (Φ : val → iProp Σ) :
  counter l j ★ (∀ i, ■ (j ≤ i)%nat → counter l i -★ Φ #i)
  ⊢ WP read #l {{ Φ }}.
Proof.
  iIntros "[Hc HΦ]". iDestruct "Hc" as (γ) "(% & #? & #Hinv & Hγf)".
  rewrite /read /=. wp_let. iInv N as (c) ">[Hγ Hl]" "Hclose". wp_load.
  iDestruct (own_valid_2 with "[$Hγ $Hγf]")
    as %[?%mnat_included _]%auth_valid_discrete_2.
  iVs (own_update_2 with "[$Hγ $Hγf]") as "[Hγ Hγf]".
  { apply auth_update, (mnat_local_update _ _ c); auto. }
  iVs ("Hclose" with "[Hl Hγ]") as "_"; [iNext; iExists c; by iFrame|].
  iApply ("HΦ" with "[%]"); rewrite /counter; eauto 10.
Qed.
End proof.
