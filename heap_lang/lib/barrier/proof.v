From iris.prelude Require Import functions.
From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Import saved_prop.
From iris.heap_lang Require Import proofmode.
From iris.proofmode Require Import sts.
From iris.heap_lang.lib.barrier Require Export barrier.
From iris.heap_lang.lib.barrier Require Import protocol.
Import uPred.

(** The CMRAs we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class barrierG Σ := BarrierG {
  barrier_stsG :> stsG heap_lang Σ sts;
  barrier_savedPropG :> savedPropG heap_lang Σ idCF;
}.
(** The Functors we need. *)
Definition barrierGF : gFunctorList := [stsGF sts; savedPropGF idCF].
(* Show and register that they match. *)
Instance inGF_barrierG `{H : inGFs heap_lang Σ barrierGF} : barrierG Σ.
Proof. destruct H as (?&?&?). split; apply _. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context {Σ : gFunctors} `{!heapG Σ, !barrierG Σ}.
Context (heapN N : namespace).
Implicit Types I : gset gname.
Local Notation iProp := (iPropG heap_lang Σ).

Definition ress (P : iProp) (I : gset gname) : iProp :=
  (∃ Ψ : gname → iProp,
    ▷ (P -★ Π★{set I} Ψ) ★ Π★{set I} (λ i, saved_prop_own i (Ψ i)))%I.

Coercion state_to_val (s : state) : val :=
  match s with State Low _ => #0 | State High _ => #1 end.
Arguments state_to_val !_ / : simpl nomatch.

Definition state_to_prop (s : state) (P : iProp) : iProp :=
  match s with State Low _ => P | State High _ => True%I end.
Arguments state_to_prop !_ _ / : simpl nomatch.

Definition barrier_inv (l : loc) (P : iProp) (s : state) : iProp :=
  (l ↦ s ★ ress (state_to_prop s P) (state_I s))%I.

Definition barrier_ctx (γ : gname) (l : loc) (P : iProp) : iProp :=
  (■ (heapN ⊥ N) ★ heap_ctx heapN ★ sts_ctx γ N (barrier_inv l P))%I.

Definition send (l : loc) (P : iProp) : iProp :=
  (∃ γ, barrier_ctx γ l P ★ sts_ownS γ low_states {[ Send ]})%I.

Definition recv (l : loc) (R : iProp) : iProp :=
  (∃ γ P Q i,
    barrier_ctx γ l P ★ sts_ownS γ (i_states i) {[ Change i ]} ★
    saved_prop_own i Q ★ ▷ (Q -★ R))%I.

Global Instance barrier_ctx_persistent (γ : gname) (l : loc) (P : iProp) :
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
  (saved_prop_own i Q ★ saved_prop_own i1 R1 ★ saved_prop_own i2 R2 ★
    (Q -★ R1 ★ R2) ★ ress P I)
  ⊢ ress P ({[i1]} ∪ ({[i2]} ∪ (I ∖ {[i]}))).
Proof.
  iIntros {????} "(#HQ&#H1&#H2&HQR&H)"; iDestruct "H" as {Ψ} "[HPΨ HΨ]".
  iDestruct (big_sepS_delete _ _ i with "HΨ") as "[#HΨi HΨ]"; first done.
  iExists (<[i1:=R1]> (<[i2:=R2]> Ψ)). iSplitL "HQR HPΨ".
  - iPoseProof (saved_prop_agree i Q (Ψ i) with "[#]") as "Heq"; first by iSplit.
    iNext. iRewrite "Heq" in "HQR". iIntros "HP". iSpecialize ("HPΨ" with "HP").
    iDestruct (big_sepS_delete _ _ i with "HPΨ") as "[HΨ HPΨ]"; first done.
    iDestruct ("HQR" with "HΨ") as "[HR1 HR2]".
    rewrite !big_sepS_insert''; [|abstract set_solver ..]. by iFrame "HR1 HR2".
  - rewrite !big_sepS_insert'; [|abstract set_solver ..]. by repeat iSplit.
Qed.

(** Actual proofs *)
Lemma newbarrier_spec (P : iProp) (Φ : val → iProp) :
  heapN ⊥ N →
  (heap_ctx heapN ★ ∀ l, recv l P ★ send l P -★ Φ #l)
  ⊢ WP newbarrier #() {{ Φ }}.
Proof.
  iIntros {HN} "[#? HΦ]".
  rewrite /newbarrier. wp_seq. iApply wp_pvs. wp_alloc l as "Hl".
  iApply "HΦ".
  iPvs (saved_prop_alloc (F:=idCF) _ P) as {γ} "#?".
  iPvs (sts_alloc (barrier_inv l P) _ N (State Low {[ γ ]}) with "[-]")
    as {γ'} "[#? Hγ']"; eauto.
  { iNext. rewrite /barrier_inv /=. iFrame "Hl".
    iExists (const P). rewrite !big_sepS_singleton /=.
    iSplit; [|done]. by iIntros "> ?". }
  iAssert (barrier_ctx γ' l P)%I as "#?".
  { rewrite /barrier_ctx. by repeat iSplit. }
  iPvsAssert (sts_ownS γ' (i_states γ) {[Change γ]}
    ★ sts_ownS γ' low_states {[Send]})%I as "[Hr Hs]" with "[-]".
  { iApply sts_ownS_op; eauto using i_states_closed, low_states_closed.
    + set_solver.
    + iApply (sts_own_weaken with "Hγ'");
        auto using sts.closed_op, i_states_closed, low_states_closed;
        abstract set_solver. }
  iPvsIntro. rewrite /recv /send. iSplitL "Hr".
  - iExists γ', P, P, γ. iFrame "Hr". repeat iSplit; auto. by iIntros "> ?".
  - iExists γ'. by iSplit.
Qed.

Lemma signal_spec l P (Φ : val → iProp) :
  (send l P ★ P ★ Φ #()) ⊢ WP signal #l {{ Φ }}.
Proof.
  rewrite /signal /send /barrier_ctx.
  iIntros "(Hs&HP&HΦ)"; iDestruct "Hs" as {γ} "[#(%&Hh&Hsts) Hγ]". wp_let.
  iSts γ as [p I]; iDestruct "Hγ" as "[Hl Hr]".
  wp_store. destruct p; [|done].
  iExists (State High I), (∅ : set token).
  iSplit; [iPureIntro; by eauto using signal_step|].
  iSplitR "HΦ"; [iNext|by iIntros "?"].
  rewrite {2}/barrier_inv /ress /=; iFrame "Hl".
  iDestruct "Hr" as {Ψ} "[Hr Hsp]"; iExists Ψ; iFrame "Hsp".
  iIntros "> _"; by iApply "Hr".
Qed.

Lemma wait_spec l P (Φ : val → iProp) :
  (recv l P ★ (P -★ Φ #())) ⊢ WP wait #l {{ Φ }}.
Proof.
  rename P into R; rewrite /recv /barrier_ctx.
  iIntros "[Hr HΦ]"; iDestruct "Hr" as {γ P Q i} "(#(%&Hh&Hsts)&Hγ&#HQ&HQR)".
  iLöb as "IH". wp_rec. wp_focus (! _)%E.
  iSts γ as [p I]; iDestruct "Hγ" as "[Hl Hr]".
  wp_load. destruct p.
  - (* a Low state. The comparison fails, and we recurse. *)
    iExists (State Low I), {[ Change i ]}; iSplit; [done|iSplitL "Hl Hr"].
    { iNext. rewrite {2}/barrier_inv /=. by iFrame "Hl". }
    iIntros "Hγ".
    iPvsAssert (sts_ownS γ (i_states i) {[Change i]})%I as "Hγ" with "[Hγ]".
    { iApply (sts_own_weaken with "Hγ"); eauto using i_states_closed. }
    wp_op=> ?; simplify_eq; wp_if. iApply ("IH" with "Hγ [HQR] HΦ"). by iNext.
  - (* a High state: the comparison succeeds, and we perform a transition and
    return to the client *)
    iExists (State High (I ∖ {[ i ]})), (∅ : set token).
    iSplit; [iPureIntro; by eauto using wait_step|].
    iDestruct "Hr" as {Ψ} "[HΨ Hsp]".
    iDestruct (big_sepS_delete _ _ i with "Hsp") as "[#HΨi Hsp]"; first done.
    iAssert (▷ Ψ i ★ ▷ Π★{set (I ∖ {[i]})} Ψ)%I as "[HΨ HΨ']" with "[HΨ]".
    { iNext. iApply (big_sepS_delete _ _ i); first done. by iApply "HΨ". }
    iSplitL "HΨ' Hl Hsp"; [iNext|].
    + rewrite {2}/barrier_inv /=; iFrame "Hl".
      iExists Ψ; iFrame "Hsp". by iIntros "> _".
    + iPoseProof (saved_prop_agree i Q (Ψ i) with "[#]") as "Heq"; first by iSplit.
      iIntros "_". wp_op=> ?; simplify_eq/=; wp_if.
      iPvsIntro. iApply "HΦ". iApply "HQR". by iRewrite "Heq".
Qed.

Lemma recv_split E l P1 P2 :
  nclose N ⊆ E → recv l (P1 ★ P2) ⊢ |={E}=> recv l P1 ★ recv l P2.
Proof.
  rename P1 into R1; rename P2 into R2. rewrite {1}/recv /barrier_ctx.
  iIntros {?} "Hr"; iDestruct "Hr" as {γ P Q i} "(#(%&Hh&Hsts)&Hγ&#HQ&HQR)".
  iApply pvs_trans'.
  iSts γ as [p I]; iDestruct "Hγ" as "[Hl Hr]".
  iPvs (saved_prop_alloc_strong _ (R1: ∙%CF iProp) I) as {i1} "[% #Hi1]".
  iPvs (saved_prop_alloc_strong _ (R2: ∙%CF iProp) (I ∪ {[i1]}))
    as {i2} "[Hi2' #Hi2]"; iDestruct "Hi2'" as %Hi2; iPvsIntro.
  rewrite ->not_elem_of_union, elem_of_singleton in Hi2; destruct Hi2.
  iExists (State p ({[i1]} ∪ ({[i2]} ∪ (I ∖ {[i]})))).
  iExists ({[Change i1 ]} ∪ {[ Change i2 ]}).
  iSplit; [by eauto using split_step|iSplitL].
  - iNext. rewrite {2}/barrier_inv /=. iFrame "Hl".
    iApply (ress_split _ _ _ Q R1 R2); eauto. iFrame "Hr HQR". by repeat iSplit.
  - iIntros "Hγ".
    iPvsAssert (sts_ownS γ (i_states i1) {[Change i1]}
      ★ sts_ownS γ (i_states i2) {[Change i2]})%I as "[Hγ1 Hγ2]" with "[-]".
    { iApply sts_ownS_op; eauto using i_states_closed, low_states_closed.
      + set_solver.
      + iApply (sts_own_weaken with "Hγ");
          eauto using sts.closed_op, i_states_closed.
        abstract set_solver. }
    iPvsIntro; iSplitL "Hγ1"; rewrite /recv /barrier_ctx.
    + iExists γ, P, R1, i1. iFrame "Hγ1 Hi1". repeat iSplit; auto.
      by iIntros "> ?".
    + iExists γ, P, R2, i2. iFrame "Hγ2 Hi2". repeat iSplit; auto.
      by iIntros "> ?".
Qed.

Lemma recv_weaken l P1 P2 : (P1 -★ P2) ⊢ (recv l P1 -★ recv l P2).
Proof.
  rewrite /recv.
  iIntros "HP HP1"; iDestruct "HP1" as {γ P Q i} "(#Hctx&Hγ&Hi&HP1)".
  iExists γ, P, Q, i; iFrame "Hctx Hγ Hi".
  iIntros "> HQ". by iApply "HP"; iApply "HP1".
Qed.

Lemma recv_mono l P1 P2 : P1 ⊢ P2 → recv l P1 ⊢ recv l P2.
Proof.
  intros HP%entails_wand. apply wand_entails. rewrite HP. apply recv_weaken.
Qed.
End proof.

Typeclasses Opaque barrier_ctx send recv.
