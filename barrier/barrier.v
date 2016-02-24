From heap_lang Require Export notation.

Definition newchan := (λ: "", ref '0)%L.
Definition signal := (λ: "x", "x" <- '1)%L.
Definition wait := (rec: "wait" "x" :=if: !"x" = '1 then '() else "wait" "x")%L.
