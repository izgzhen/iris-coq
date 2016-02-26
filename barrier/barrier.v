From heap_lang Require Export substitution notation.

Definition newchan : val := λ: "", ref '0.
Definition signal : val := λ: "x", "x" <- '1.
Definition wait : val :=
  rec: "wait" "x" := if: !"x" = '1 then '() else "wait" "x".

Instance newchan_closed : Closed newchan. Proof. solve_closed. Qed.
Instance signal_closed : Closed signal. Proof. solve_closed. Qed.
Instance wait_closed : Closed wait. Proof. solve_closed. Qed.