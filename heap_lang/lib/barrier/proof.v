From iris.prelude Require Import functions.
From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Import saved_prop sts.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang.lib.barrier Require Export barrier.
From iris.heap_lang.lib.barrier Require Import protocol.

(** The CMRAs we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class barrierG Σ := BarrierG {
  barrier_stsG :> stsG Σ sts;
  barrier_savedPropG :> savedPropG Σ idCF;
}.
(** The Functors we need. *)
Definition barrierGF : gFunctorList := [stsGF sts; savedPropGF idCF].
(* Show and register that they match. *)
Instance inGF_barrierG `{H : inGFs Σ barrierGF} : barrierG Σ.
Proof. destruct H as (?&?&?). split; apply _. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context `{!heapG Σ, !barrierG Σ} (N : namespace).
Implicit Types I : gset gname.

Definition ress (P : iProp Σ) (I : gset gname) : iProp Σ :=
  (∃ Ψ : gname → iProp Σ,
    ▷ (P -★ [★ set] i ∈ I, Ψ i) ★ [★ set] i ∈ I, saved_prop_own i (Ψ i))%I.

Coercion state_to_val (s : state) : val :=
  match s with State Low _ => #0 | State High _ => #1 end.
Arguments state_to_val !_ / : simpl nomatch.

Definition state_to_prop (s : state) (P : iProp Σ) : iProp Σ :=
  match s with State Low _ => P | State High _ => True%I end.
Arguments state_to_prop !_ _ / : simpl nomatch.

Definition barrier_inv (l : loc) (P : iProp Σ) (s : state) : iProp Σ :=
  (l ↦ s ★ ress (state_to_prop s P) (state_I s))%I.

Definition barrier_ctx (γ : gname) (l : loc) (P : iProp Σ) : iProp Σ :=
  (■ (heapN ⊥ N) ★ heap_ctx ★ sts_ctx γ N (barrier_inv l P))%I.

Definition send (l : loc) (P : iProp Σ) : iProp Σ :=
  (∃ γ, barrier_ctx γ l P ★ sts_ownS γ low_states {[ Send ]})%I.

Definition recv (l : loc) (R : iProp Σ) : iProp Σ :=
  (∃ γ P Q i,
    barrier_ctx γ l P ★ sts_ownS γ (i_states i) {[ Change i ]} ★
    saved_prop_own i Q ★ ▷ (Q -★ R))%I.

Global Instance barrier_ctx_persistent (γ : gname) (l : loc) (P : iProp Σ) :
  PersistentP (barrier_ctx γ l P).
Proof. apply _. Qed.

Typeclasses Opaque barrier_ctx send recv.

(** Setoids *)
Global Instance ress_ne n : Proper (dist n ==> (=) ==> dist n) ress.
Proof. solve_proper. Qed.
Global Instance state_to_prop_ne n s :
  Proper (dist n ==> dist n) (state_to_prop s).
Proof. solve_proper. Qed.
Global Instance barrier_inv_ne n l :
  Proper (dist n ==> eq ==> dist n) (barrier_inv l).
Proof. solve_proper. Qed.
Global Instance barrier_ctx_ne n γ l : Proper (dist n ==> dist n) (barrier_ctx γ l).
Proof. solve_proper. Qed. 
Global Instance send_ne n l : Proper (dist n ==> dist n) (send l).
Proof. solve_proper. Qed.
Global Instance recv_ne n l : Proper (dist n ==> dist n) (recv l).
Proof. solve_proper. Qed.

(** Helper lemmas *)
Lemma ress_split i i1 i2 Q R1 R2 P I :
  i ∈ I → i1 ∉ I → i2 ∉ I → i1 ≠ i2 →
  saved_prop_own i Q ★ saved_prop_own i1 R1 ★ saved_prop_own i2 R2 ★
    (Q -★ R1 ★ R2) ★ ress P I
  ⊢ ress P ({[i1;i2]} ∪ I ∖ {[i]}).
Proof.
  iIntros (????) "(#HQ&#H1&#H2&HQR&H)"; iDestruct "H" as (Ψ) "[HPΨ HΨ]".
  iDestruct (big_sepS_delete _ _ i with "HΨ") as "[#HΨi HΨ]"; first done.
  iExists (<[i1:=R1]> (<[i2:=R2]> Ψ)). iSplitL "HQR HPΨ".
  - iPoseProof (saved_prop_agree i Q (Ψ i) with "[#]") as "Heq"; first by iSplit.
    iNext. iRewrite "Heq" in "HQR". iIntros "HP". iSpecialize ("HPΨ" with "HP").
    iDestruct (big_sepS_delete _ _ i with "HPΨ") as "[HΨ HPΨ]"; first done.
    iDestruct ("HQR" with "HΨ") as "[HR1 HR2]".
    rewrite -assoc_L !big_sepS_fn_insert'; [|abstract set_solver ..].
    by iFrame.
  - rewrite -assoc_L !big_sepS_fn_insert; [|abstract set_solver ..]. eauto.
Qed.

(** Actual proofs *)
Lemma newbarrier_spec (P : iProp Σ) (Φ : val → iProp Σ) :
  heapN ⊥ N →
  heap_ctx ★ (∀ l, recv l P ★ send l P -★ Φ #l) ⊢ WP newbarrier #() {{ Φ }}.
Proof.
  iIntros (HN) "[#? HΦ]".
  rewrite /newbarrier. wp_seq. wp_alloc l as "Hl".
  iApply ("HΦ" with "==>[-]").
  iVs (saved_prop_alloc (F:=idCF) P) as (γ) "#?".
  iVs (sts_alloc (barrier_inv l P) _ N (State Low {[ γ ]}) with "[-]")
    as (γ') "[#? Hγ']"; eauto.
  { iNext. rewrite /barrier_inv /=. iFrame.
    iExists (const P). rewrite !big_sepS_singleton /=. eauto. }
  iAssert (barrier_ctx γ' l P)%I as "#?".
  { rewrite /barrier_ctx. by repeat iSplit. }
  iAssert (sts_ownS γ' (i_states γ) {[Change γ]}
    ★ sts_ownS γ' low_states {[Send]})%I with "==>[-]" as "[Hr Hs]".
  { iApply sts_ownS_op; eauto using i_states_closed, low_states_closed.
    - set_solver.
    - iApply (sts_own_weaken with "Hγ'");
        auto using sts.closed_op, i_states_closed, low_states_closed;
        abstract set_solver. }
  iVsIntro. rewrite /recv /send. iSplitL "Hr".
  - iExists γ', P, P, γ. iFrame. auto.
  - auto.
Qed.

Lemma signal_spec l P (Φ : val → iProp Σ) :
  send l P ★ P ★ Φ #() ⊢ WP signal #l {{ Φ }}.
Proof.
  rewrite /signal /send /barrier_ctx.
  iIntros "(Hs&HP&HΦ)"; iDestruct "Hs" as (γ) "[#(%&Hh&Hsts) Hγ]". wp_let.
  iVs (sts_openS (barrier_inv l P) _ _ γ with "[Hγ]")
    as ([p I]) "(% & [Hl Hr] & Hclose)"; eauto.
  destruct p; [|done]. wp_store. iFrame "HΦ".
  iVs ("Hclose" $! (State High I) (∅ : set token) with "[-]"); last done.
  iSplit; [iPureIntro; by eauto using signal_step|].
  iNext. rewrite {2}/barrier_inv /ress /=; iFrame "Hl".
  iDestruct "Hr" as (Ψ) "[Hr Hsp]"; iExists Ψ; iFrame "Hsp".
  iIntros "!> _"; by iApply "Hr".
Qed.

Lemma wait_spec l P (Φ : val → iProp Σ) :
  recv l P ★ (P -★ Φ #()) ⊢ WP wait #l {{ Φ }}.
Proof.
  rename P into R; rewrite /recv /barrier_ctx.
  iIntros "[Hr HΦ]"; iDestruct "Hr" as (γ P Q i) "(#(%&Hh&Hsts)&Hγ&#HQ&HQR)".
  iLöb as "IH". wp_rec. wp_focus (! _)%E.
  iVs (sts_openS (barrier_inv l P) _ _ γ with "[Hγ]")
    as ([p I]) "(% & [Hl Hr] & Hclose)"; eauto.
  wp_load. destruct p.
  - iVs ("Hclose" $! (State Low I) {[ Change i ]} with "[Hl Hr]") as "Hγ".
    { iSplit; first done. iNext. rewrite {2}/barrier_inv /=. by iFrame. }
    iAssert (sts_ownS γ (i_states i) {[Change i]})%I with "==>[Hγ]" as "Hγ".
    { iApply (sts_own_weaken with "Hγ"); eauto using i_states_closed. }
    iVsIntro. wp_op=> ?; simplify_eq; wp_if.
    iApply ("IH" with "Hγ [HQR] HΦ"). auto.
  - (* a High state: the comparison succeeds, and we perform a transition and
    return to the client *)
    iDestruct "Hr" as (Ψ) "[HΨ Hsp]".
    iDestruct (big_sepS_delete _ _ i with "Hsp") as "[#HΨi Hsp]"; first done.
    iAssert (▷ Ψ i ★ ▷ [★ set] j ∈ I ∖ {[i]}, Ψ j)%I with "[HΨ]" as "[HΨ HΨ']".
    { iNext. iApply (big_sepS_delete _ _ i); first done. by iApply "HΨ". }
    iVs ("Hclose" $! (State High (I ∖ {[ i ]})) (∅ : set token) with "[HΨ' Hl Hsp]").
    { iSplit; [iPureIntro; by eauto using wait_step|].
      iNext. rewrite {2}/barrier_inv /=; iFrame "Hl". iExists Ψ; iFrame. auto. }
    iPoseProof (saved_prop_agree i Q (Ψ i) with "[#]") as "Heq"; first by auto.
    iVsIntro. wp_op=> ?; simplify_eq/=; wp_if.
    iVsIntro. iApply "HΦ". iApply "HQR". by iRewrite "Heq".
Qed.

Lemma recv_split E l P1 P2 :
  nclose N ⊆ E → recv l (P1 ★ P2) ={E}=> recv l P1 ★ recv l P2.
Proof.
  rename P1 into R1; rename P2 into R2. rewrite {1}/recv /barrier_ctx.
  iIntros (?). iDestruct 1 as (γ P Q i) "(#(%&Hh&Hsts)&Hγ&#HQ&HQR)".
  iVs (sts_openS (barrier_inv l P) _ _ γ with "[Hγ]")
    as ([p I]) "(% & [Hl Hr] & Hclose)"; eauto.
  iVs (saved_prop_alloc_strong (R1: ∙%CF (iProp Σ)) I) as (i1) "[% #Hi1]".
  iVs (saved_prop_alloc_strong (R2: ∙%CF (iProp Σ)) (I ∪ {[i1]}))
    as (i2) "[Hi2' #Hi2]"; iDestruct "Hi2'" as %Hi2.
  rewrite ->not_elem_of_union, elem_of_singleton in Hi2; destruct Hi2.
  iVs ("Hclose" $! (State p ({[i1; i2]} ∪ I ∖ {[i]}))
                   {[Change i1; Change i2 ]} with "[-]") as "Hγ".
  { iSplit; first by eauto using split_step.
    iNext. rewrite {2}/barrier_inv /=. iFrame "Hl".
    iApply (ress_split _ _ _ Q R1 R2); eauto. iFrame; auto. }
  iAssert (sts_ownS γ (i_states i1) {[Change i1]}
    ★ sts_ownS γ (i_states i2) {[Change i2]})%I with "==>[-]" as "[Hγ1 Hγ2]".
  { iApply sts_ownS_op; eauto using i_states_closed, low_states_closed.
    - abstract set_solver.
    - iApply (sts_own_weaken with "Hγ");
        eauto using sts.closed_op, i_states_closed.
      abstract set_solver. }
  iVsIntro; iSplitL "Hγ1"; rewrite /recv /barrier_ctx.
  - iExists γ, P, R1, i1. iFrame; auto.
  - iExists γ, P, R2, i2. iFrame; auto.
Qed.

Lemma recv_weaken l P1 P2 : (P1 -★ P2) ⊢ recv l P1 -★ recv l P2.
Proof.
  rewrite /recv.
  iIntros "HP HP1"; iDestruct "HP1" as (γ P Q i) "(#Hctx&Hγ&Hi&HP1)".
  iExists γ, P, Q, i. iFrame "Hctx Hγ Hi".
  iIntros "!> HQ". by iApply "HP"; iApply "HP1".
Qed.

Lemma recv_mono l P1 P2 : (P1 ⊢ P2) → recv l P1 ⊢ recv l P2.
Proof. iIntros (HP) "H". iApply (recv_weaken with "[] H"). iApply HP. Qed.
End proof.

Typeclasses Opaque barrier_ctx send recv.
