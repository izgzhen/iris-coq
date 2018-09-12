From iris.heap_lang Require Export lifting notation.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "Type".

(** A general logically atomic interface for a heap. *)
Class atomic_heap {Σ} `{!heapG Σ} := AtomicHeap {
  (* -- operations -- *)
  alloc : val;
  load : val;
  store : val;
  cas : val;
  (* -- predicates -- *)
  mapsto (l : loc) (q: Qp) (v : val) : iProp Σ;
  (* -- mapsto properties -- *)
  mapsto_timeless l q v :> Timeless (mapsto l q v);
  mapsto_fractional l v :> Fractional (λ q, mapsto l q v);
  mapsto_as_fractional l q v :>
    AsFractional (mapsto l q v) (λ q, mapsto l q v) q;
  mapsto_agree l q1 q2 v1 v2 :> mapsto l q1 v1 -∗ mapsto l q2 v2 -∗ ⌜v1 = v2⌝;
  (* -- operation specs -- *)
  alloc_spec (v : val) :
    {{{ True }}} alloc v {{{ l, RET #l; mapsto l 1 v }}};
  load_spec (l : loc) :
    <<< ∀ (v : val) q, mapsto l q v >>> load #l @ ⊤ <<< mapsto l q v, RET v >>>;
  store_spec (l : loc) (w : val) :
    <<< ∀ v, mapsto l 1 v >>> store #l w @ ⊤
    <<< mapsto l 1 w, RET #() >>>;
  (* This spec is slightly weaker than it could be: It is sufficient for [w1]
  *or* [v] to be unboxed.  However, by writing it this way the [val_is_unboxed]
  is outside the atomic triple, which makes it much easier to use -- and the
  spec is still good enough for all our applications. *)
  cas_spec (l : loc) (w1 w2 : val) :
    val_is_unboxed w1 →
    <<< ∀ v, mapsto l 1 v >>> cas #l w1 w2 @ ⊤
    <<< if decide (v = w1) then mapsto l 1 w2 else mapsto l 1 v,
        RET #(if decide (v = w1) then true else false) >>>;
}.
Arguments atomic_heap _ {_}.

(** Notation for heap primitives, in a module so you can import it separately. *)
Module notation.
Notation "l ↦{ q } v" := (mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" := (mapsto l 1 v) (at level 20) : bi_scope.

Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Notation "'ref' e" := (alloc e) : expr_scope.
Notation "! e" := (load e) : expr_scope.
Notation "e1 <- e2" := (store e1 e2) : expr_scope.

Notation CAS e1 e2 e3 := (cas e1 e2 e3).

End notation.

(** Proof that the primitive physical operations of heap_lang satisfy said interface. *)
Definition primitive_alloc : val :=
  λ: "v", ref "v".
Definition primitive_load : val :=
  λ: "l", !"l".
Definition primitive_store : val :=
  λ: "l" "x", "l" <- "x".
Definition primitive_cas : val :=
  λ: "l" "e1" "e2", CAS "l" "e1" "e2".

Section proof.
  Context `{!heapG Σ}.

  Lemma primitive_alloc_spec (v : val) :
    {{{ True }}} primitive_alloc v {{{ l, RET #l; l ↦ v }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_alloc l. iApply "HΦ". done.
  Qed.

  Lemma primitive_load_spec (l : loc) :
    <<< ∀ (v : val) q, l ↦{q} v >>> primitive_load #l @ ⊤
    <<< l ↦{q} v, RET v >>>.
  Proof.
    iIntros (Q Φ) "? AU". wp_lam.
    iMod "AU" as (v q) "[H↦ [_ Hclose]]".
    wp_load. iMod ("Hclose" with "H↦") as "HΦ". by iApply "HΦ".
  Qed.

  Lemma primitive_store_spec (l : loc) (w : val) :
    <<< ∀ v, l ↦ v >>> primitive_store #l w @ ⊤
    <<< l ↦ w, RET #() >>>.
  Proof.
    iIntros (Q Φ) "? AU". wp_lam. wp_let.
    iMod "AU" as (v) "[H↦ [_ Hclose]]".
    wp_store. iMod ("Hclose" with "H↦") as "HΦ". by iApply "HΦ".
  Qed.

  Lemma primitive_cas_spec (l : loc) (w1 w2 : val) :
    val_is_unboxed w1 →
    <<< ∀ (v : val), l ↦ v >>>
      primitive_cas #l w1 w2 @ ⊤
    <<< if decide (v = w1) then l ↦ w2 else l ↦ v,
        RET #(if decide (v = w1) then true else false) >>>.
  Proof.
    iIntros (? Q Φ) "? AU". wp_lam. wp_let. wp_let.
    iMod "AU" as (v) "[H↦ [_ Hclose]]".
    destruct (decide (v = w1)) as [<-|Hv]; [wp_cas_suc|wp_cas_fail];
    iMod ("Hclose" with "H↦") as "HΦ"; by iApply "HΦ".
  Qed.
End proof.

(* NOT an instance because users should choose explicitly to use it
     (using [Explicit Instance]). *)
Definition primitive_atomic_heap `{!heapG Σ} : atomic_heap Σ :=
  {| alloc_spec := primitive_alloc_spec;
     load_spec := primitive_load_spec;
     store_spec := primitive_store_spec;
     cas_spec := primitive_cas_spec;
     mapsto_agree := gen_heap.mapsto_agree  |}.
