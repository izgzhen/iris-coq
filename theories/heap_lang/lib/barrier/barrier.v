From iris.heap_lang Require Export notation.

Definition newbarrier : val := λ: <>, ref #false.
Definition signal : val := λ: "x", "x" <- #true.
Definition wait : val :=
  rec: "wait" "x" := if: !"x" then #() else "wait" "x".
