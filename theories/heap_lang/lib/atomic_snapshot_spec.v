From iris.algebra Require Import excl auth list.
From iris.heap_lang Require Export lifting notation.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "Type".

(** Specifying snapshots with histories
    Implementing atomic pair snapshot data structure from Sergey et al. (ESOP 2015) *)

Section atomic_snapshot_spec.

  Record atomic_snapshot {Σ} `{!heapG Σ} := AtomicSnapshot {
    newPair : val;
    writeX : val;
    writeY : val;
    readPair : val;
    (* other data *)
    name: Type;
    (* predicates *)
    is_pair (N : namespace) (γ : name) (p : val) : iProp Σ;
    pair_content (γ : name) (a: val * val) : iProp Σ;
    (* predicate properties *)
    is_pair_persistent N γ p : Persistent (is_pair N γ p);
    pair_content_timeless γ a : Timeless (pair_content γ a);
    pair_content_exclusive γ a1 a2 :
      pair_content γ a1 -∗ pair_content γ a2 -∗ False;
    (* specs *)
    newPair_spec N (e : expr) (v1 v2 : val) :
      IntoVal e (v1, v2) ->
      {{{ True }}} newPair e {{{ γ p, RET p; is_pair N γ p ∗ pair_content γ (v1, v2) }}};
    writeX_spec N e (v: val) p γ :
      IntoVal e v ->
      is_pair N γ p -∗
      <<< ∀ v1 v2 : val, pair_content γ (v1, v2) >>>
        writeX (p, e)
        @ ⊤∖↑N
      <<< pair_content γ (v, v2), RET #() >>>;
    writeY_spec N e (v: val) p γ:
      IntoVal e v ->
      is_pair N γ p -∗
      <<< ∀ v1 v2 : val, pair_content γ (v1, v2)  >>>
        writeY (p, e)
        @ ⊤∖↑N
      <<< pair_content γ (v1, v), RET #() >>>;
    readPair_spec N γ p :
      is_pair N γ p -∗
      <<< ∀ v1 v2 : val, pair_content γ (v1, v2) >>>
        readPair p
        @ ⊤∖↑N
      <<< pair_content γ (v1, v2), RET (v1, v2) >>>;
    }.

  End atomic_snapshot_spec.
