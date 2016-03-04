From heap_lang Require Export notation.

Definition newbarrier : val := λ: <>, ref #0.
Definition signal : val := λ: "x", '"x" <- #1.
Definition wait : val :=
  rec: "wait" "x" := if: !'"x" = #1 then #() else '"wait" '"x".
