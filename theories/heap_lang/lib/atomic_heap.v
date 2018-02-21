From iris.heap_lang Require Export lifting notation.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

(** A general logically atomic interface for a heap. *)
Structure atomic_heap {Σ} `{!heapG Σ} := AtomicHeap {
  (* -- operations -- *)
  alloc : val;
  load : val;
  store : val;
  cas : val;
  (* -- predicates -- *)
  (* name is used to associate locked with is_lock *)
  mapsto (l : loc) (q: Qp) (v : val) : iProp Σ;
  (* -- general properties -- *)
  mapsto_timeless l q v : Timeless (mapsto l q v);
  (* -- operation specs -- *)
  alloc_spec v :
    {{{ True }}} alloc v {{{ l, RET #l; mapsto l 1 v }}};
  load_spec (l : loc) :
    atomic_wp (load #l)%E
              (λ '(v, q), mapsto l q v)
              (λ '(v, q) (_:()), mapsto l q v)
              ⊤ ∅
              (λ '(v, q) _, v);
  store_spec (l : loc) (e : expr) (w : val) :
    IntoVal e w →
    atomic_wp (store (#l, e))%E
              (λ v, mapsto l 1 v)
              (λ v (_:()), mapsto l 1 w)
              ⊤ ∅
              (λ _ _, #()%V);
  cas_spec (l : loc) (e1 e2 : expr) (w1 w2 : val) :
    IntoVal e1 w1 → IntoVal e2 w2 →
    atomic_wp (cas (#l, e1, e2))%E
              (λ v, mapsto l 1 v)
              (λ v (_:()), if decide (v = w1) then mapsto l 1 w2 else mapsto l 1 v)
              ⊤ ∅
              (λ v _, #(if decide (v = w1) then true else false)%V);
}.
Arguments atomic_heap _ {_}.

(** Proof that the primitive physical operations of heap_lang satisfy said interface. *)
Definition primitive_alloc : val :=
  λ: "v", ref "v".
Definition primitive_load : val :=
  λ: "l", !"l".
Definition primitive_store : val :=
  λ: "p", (Fst "p") <- (Snd "p").
Definition primitive_cas : val :=
  λ: "p", CAS (Fst (Fst "p")) (Snd (Fst "p")) (Snd "p").

Section proof.
  Context `{!heapG Σ}.

  Lemma primitive_alloc_spec v :
    {{{ True }}} primitive_alloc v {{{ l, RET #l; l ↦ v }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_let. wp_alloc l. iApply "HΦ". done.
  Qed.

  Lemma primitive_load_spec (l : loc) :
    atomic_wp (primitive_load #l)%E
              (λ '(v, q), l ↦{q} v)%I
              (λ '(v, q) (_:()), l ↦{q} v)%I
              ⊤ ∅
              (λ '(v, q) _, v).
  Proof.
    iIntros (Φ) "Aupd". wp_let.
    iMod (aupd_acc with "Aupd") as ((v, q)) "[H↦ [_ Hclose]]"; first solve_ndisj.
    wp_load. iMod ("Hclose" $! () with "H↦"). done.
  Qed.

  Lemma primitive_store_spec (l : loc) (e : expr) (w : val) :
    IntoVal e w →
    atomic_wp (primitive_store (#l, e))%E
              (λ v, l ↦ v)%I
              (λ v (_:()), l ↦ w)%I
              ⊤ ∅
              (λ _ _, #()%V).
  Proof.
    iIntros (<-%of_to_val Φ) "Aupd". wp_let. wp_proj. wp_proj.
    iMod (aupd_acc with "Aupd") as (v) "[H↦ [_ Hclose]]"; first solve_ndisj.
    wp_store. iMod ("Hclose" $! () with "H↦"). done.
  Qed.

  Lemma primitive_cas_spec (l : loc) e1 e2 (w1 w2 : val) :
    IntoVal e1 w1 → IntoVal e2 w2 →
    atomic_wp (primitive_cas (#l, e1, e2))%E
              (λ v, l ↦ v)%I
              (λ v (_:()), if decide (v = w1) then l ↦ w2 else l ↦ v)%I
              ⊤ ∅
              (λ v _, #(if decide (v = w1) then true else false)%V).
  Proof.
    iIntros (<-%of_to_val <-%of_to_val Φ) "Aupd". wp_let. repeat wp_proj.
    iMod (aupd_acc with "Aupd") as (v) "[H↦ [_ Hclose]]"; first solve_ndisj.
    destruct (decide (v = w1)) as [Hv|Hv]; [wp_cas_suc|wp_cas_fail];
    iMod ("Hclose" $! () with "H↦"); done.
  Qed.

  Definition primitive_atomic_heap : atomic_heap Σ :=
    {| alloc_spec := primitive_alloc_spec;
       load_spec := primitive_load_spec;
       store_spec := primitive_store_spec;
       cas_spec := primitive_cas_spec |}.
End proof.
