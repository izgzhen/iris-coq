(* Monotone counter, but using an explicit CMRA instead of auth *)
From iris.program_logic Require Export global_functor.
From iris.program_logic Require Import auth.
From iris.proofmode Require Import invariants ghost_ownership coq_tactics.
From iris.heap_lang Require Import proofmode notation.
Import uPred.

Definition newcounter : val := λ: <>, ref #0.
Definition inc : val :=
  rec: "inc" "l" :=
    let: "n" := !"l" in
    if: CAS "l" "n" (#1 + "n") then #() else "inc" "l".
Definition read : val := λ: "l", !"l".
Global Opaque newcounter inc get.

(** The CMRA we need. *)
Class counterG Σ := CounterG { counter_tokG :> authG heap_lang Σ mnatUR }.
Definition counterGF : gFunctorList := [authGF mnatUR].
Instance inGF_counterG `{H : inGFs heap_lang Σ counterGF} : counterG Σ.
Proof. destruct H; split; apply _. Qed.

Section proof.
Context {Σ : gFunctors} `{!heapG Σ, !counterG Σ}.
Context (heapN : namespace).
Local Notation iProp := (iPropG heap_lang Σ).

Definition counter_inv (l : loc) (n : mnat) : iProp := (l ↦ #n)%I.

Definition counter (l : loc) (n : nat) : iProp :=
  (∃ N γ, heapN ⊥ N ∧ heap_ctx heapN ∧
          auth_ctx γ N (counter_inv l) ∧ auth_own γ (n:mnat))%I.

(** The main proofs. *)
Global Instance counter_persistent l n : PersistentP (counter l n).
Proof. apply _. Qed.

Lemma newcounter_spec N (R : iProp) Φ :
  heapN ⊥ N →
  heap_ctx heapN ★ (∀ l, counter l 0 -★ Φ #l) ⊢ WP newcounter #() {{ Φ }}.
Proof.
  iIntros (?) "[#Hh HΦ]". rewrite /newcounter. wp_seq. wp_alloc l as "Hl".
  iPvs (auth_alloc (counter_inv l) N _ (O:mnat) with "[Hl]")
    as (γ) "[#? Hγ]"; try by auto.
  iPvsIntro. iApply "HΦ". rewrite /counter; eauto 10.
Qed.

Lemma inc_spec l j (Φ : val → iProp) :
  counter l j ★ (counter l (S j) -★ Φ #()) ⊢ WP inc #l {{ Φ }}.
Proof.
  iIntros "[Hl HΦ]". iLöb as "IH". wp_rec.
  iDestruct "Hl" as (N γ) "(% & #? & #Hγ & Hγf)".
  wp_focus (! _)%E.
  iApply (auth_fsa (counter_inv l) (wp_fsa _) _ N); auto with fsaV.
  iIntros "{$Hγ $Hγf}"; iIntros (j') "[% Hl] /="; rewrite {2}/counter_inv.
  wp_load; iPvsIntro; iExists j; iSplit; [done|iIntros "{$Hl} Hγf"].
  wp_let; wp_op. wp_focus (CAS _ _ _).
  iApply (auth_fsa (counter_inv l) (wp_fsa _) _ N); auto with fsaV.
  iIntros "{$Hγ $Hγf}"; iIntros (j'') "[% Hl] /="; rewrite {2}/counter_inv.
  destruct (decide (j `max` j'' = j `max` j')) as [Hj|Hj].
  - wp_cas_suc; first (by do 3 f_equal); iPvsIntro.
    iExists (1 + j `max` j')%nat; iSplit.
    { iPureIntro. apply mnat_local_update. abstract lia. }
    rewrite {2}/counter_inv !mnat_op_max (Nat.max_l (S _)); last abstract lia.
    rewrite Nat2Z.inj_succ -Z.add_1_l.
    iIntros "{$Hl} Hγf". wp_if.
    iPvsIntro; iApply "HΦ"; iExists N, γ; repeat iSplit; eauto.
    iApply (auth_own_mono with "Hγf"). apply mnat_included. abstract lia.
  - wp_cas_fail; first (rewrite !mnat_op_max; by intros [= ?%Nat2Z.inj]).
    iPvsIntro. iExists j; iSplit; [done|iIntros "{$Hl} Hγf"].
    wp_if. iApply ("IH" with "[Hγf] HΦ"). rewrite {3}/counter; eauto 10.
Qed.

Lemma read_spec l j (Φ : val → iProp) :
  counter l j ★ (∀ i, ■ (j ≤ i)%nat → counter l i -★ Φ #i)
  ⊢ WP read #l {{ Φ }}.
Proof.
  iIntros "[Hc HΦ]". iDestruct "Hc" as (N γ) "(% & #? & #Hγ & Hγf)".
  rewrite /read. wp_let.
  iApply (auth_fsa (counter_inv l) (wp_fsa _) _ N); auto with fsaV.
  iIntros "{$Hγ $Hγf}"; iIntros (j') "[% Hl] /=".
  wp_load; iPvsIntro; iExists (j `max` j'); iSplit.
  { iPureIntro; apply mnat_local_update; abstract lia. }
  rewrite !mnat_op_max -Nat.max_assoc Nat.max_idempotent; iIntros "{$Hl} Hγf".
  iApply ("HΦ" with "[%]"); first abstract lia; rewrite /counter; eauto 10.
Qed.
End proof.
