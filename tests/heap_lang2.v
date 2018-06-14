(* Test yet another way of importing heap_lang modules that used to break
printing *)
From iris.heap_lang Require Export lifting notation.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Section printing_tests.
  Context `{heapG Σ}.

  Lemma wp_print_long_expr (fun1 fun2 fun3 : expr) :
    True -∗ WP let: "val1" := fun1 #() in
       let: "val2" := fun2 "val1" in
       let: "val3" := fun3 "val2" in
       if: "val1" = "val2" then "val" else "val3"  {{ _, True }}.
  Proof.
    iIntros "_". Show.
  Abort.

End printing_tests.
