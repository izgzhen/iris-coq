From iris.heap_lang Require Export lifting notation.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "Type".

Section prophecy.

  Context `{!heapG Σ} (N: namespace).

  Record prophecy {Σ} `{!heapG Σ} := Prophecy {
    (* -- operations -- *)
    new_prophecy : val;
    resolve_prophecy : val;
    (* -- predicates -- *)
    is_prophecy : proph -> val -> iProp Σ;
    (* -- general properties -- *)
    new_prophecy_spec:
      {{{ True }}} new_prophecy #() {{{ p, RET #p; ∃ v, is_prophecy p v }}};
    resolve_prophecy_spec p v e w:
      IntoVal e w ->
      {{{ is_prophecy p v }}} resolve_prophecy #p e {{{ RET w; ⌜v = w⌝ }}} 
  }.

End prophecy.
