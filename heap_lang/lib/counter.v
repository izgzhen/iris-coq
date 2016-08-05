From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import invariants tactics.
From iris.program_logic Require Import auth.
From iris.heap_lang Require Import proofmode notation.

Definition newcounter : val := λ: <>, ref #0.
Definition inc : val :=
  rec: "inc" "l" :=
    let: "n" := !"l" in
    if: CAS "l" "n" (#1 + "n") then #() else "inc" "l".
Definition read : val := λ: "l", !"l".
Global Opaque newcounter inc get.

(** The CMRA we need. *)
Class counterG Σ := CounterG { counter_tokG :> authG Σ mnatUR }.
Definition counterGF : gFunctorList := [authGF mnatUR].
Instance inGF_counterG `{H : inGFs Σ counterGF} : counterG Σ.
Proof. destruct H; split; apply _. Qed.

Section proof.
Context `{!heapG Σ, !counterG Σ} (N : namespace).

Definition counter_inv (l : loc) (n : mnat) : iProp Σ := (l ↦ #n)%I.

Definition counter (l : loc) (n : nat) : iProp Σ :=
  (∃ γ, heapN ⊥ N ∧ heap_ctx ∧
        auth_ctx γ N (counter_inv l) ∧ auth_own γ (n:mnat))%I.

(** The main proofs. *)
Global Instance counter_persistent l n : PersistentP (counter l n).
Proof. apply _. Qed.

Lemma newcounter_spec (R : iProp Σ) Φ :
  heapN ⊥ N →
  heap_ctx ★ (∀ l, counter l 0 -★ Φ #l) ⊢ WP newcounter #() {{ Φ }}.
Proof.
  iIntros (?) "[#Hh HΦ]". rewrite /newcounter. wp_seq. wp_alloc l as "Hl".
  iVs (auth_alloc (counter_inv l) N _ (O:mnat) with "[Hl]")
    as (γ) "[#? Hγ]"; try by auto.
  iVsIntro. iApply "HΦ". rewrite /counter; eauto 10.
Qed.

Lemma inc_spec l j (Φ : val → iProp Σ) :
  counter l j ★ (counter l (S j) -★ Φ #()) ⊢ WP inc #l {{ Φ }}.
Proof.
  iIntros "[Hl HΦ]". iLöb as "IH". wp_rec.
  iDestruct "Hl" as (γ) "(% & #? & #Hγ & Hγf)".
  wp_focus (! _)%E.
  iVs (auth_open (counter_inv l) with "[Hγf]") as (j') "(% & Hl & Hclose)"; auto.
  rewrite {2}/counter_inv.
  wp_load. iVs ("Hclose" $! j with "[Hl]") as "Hγf"; eauto.
  iVsIntro. wp_let; wp_op. wp_focus (CAS _ _ _).
  iVs (auth_open (counter_inv l) with "[Hγf]") as (j'') "(% & Hl & Hclose)"; auto.
  rewrite {2}/counter_inv.
  destruct (decide (j `max` j'' = j `max` j')) as [Hj|Hj].
  - wp_cas_suc; first (by do 3 f_equal).
    iVs ("Hclose" $! (1 + j `max` j')%nat with "[Hl]") as "Hγf".
    { iSplit; [iPureIntro|iNext].
      { apply mnat_local_update. abstract lia. }
      rewrite {2}/counter_inv !mnat_op_max (Nat.max_l (S _)); last abstract lia.
      by rewrite Nat2Z.inj_succ -Z.add_1_l. }
    iVsIntro. wp_if.
    iVsIntro; iApply "HΦ"; iExists γ; repeat iSplit; eauto.
    iApply (auth_own_mono with "Hγf"). apply mnat_included. abstract lia.
  - wp_cas_fail; first (rewrite !mnat_op_max; by intros [= ?%Nat2Z.inj]).
    iVs ("Hclose" $! j with "[Hl]") as "Hγf"; eauto.
    iVsIntro. wp_if. iApply ("IH" with "[Hγf] HΦ"). rewrite {3}/counter; eauto 10.
Qed.

Lemma read_spec l j (Φ : val → iProp Σ) :
  counter l j ★ (∀ i, ■ (j ≤ i)%nat → counter l i -★ Φ #i)
  ⊢ WP read #l {{ Φ }}.
Proof.
  iIntros "[Hc HΦ]". iDestruct "Hc" as (γ) "(% & #? & #Hγ & Hγf)".
  rewrite /read. wp_let.
  iVs (auth_open (counter_inv l) with "[Hγf]") as (j') "(% & Hl & Hclose)"; auto.
  wp_load.
  iVs ("Hclose" $! (j `max` j') with "[Hl]") as "Hγf".
  { iSplit; [iPureIntro|iNext].
    { apply mnat_local_update; abstract lia. }
    by rewrite !mnat_op_max -Nat.max_assoc Nat.max_idempotent. }
  iVsIntro. rewrite !mnat_op_max.
  iApply ("HΦ" with "[%]"); first abstract lia. rewrite /counter; eauto 10.
Qed.
End proof.
