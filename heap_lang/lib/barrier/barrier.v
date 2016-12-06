From iris.heap_lang Require Export notation.

Definition newbarrier : val := locked (λ: <>, ref #false)%V.
Definition signal : val := locked (λ: "x", "x" <- #true)%V.
Definition wait : val :=
  locked (rec: "wait" "x" := if: !"x" then #() else "wait" "x")%V.
