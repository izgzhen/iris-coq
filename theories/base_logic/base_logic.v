From iris.base_logic Require Export derived.
From iris.bi Require Export bi.
Set Default Proof Using "Type".

Module Import uPred.
  Export upred.uPred.
  Export derived.uPred.
  Export bi.
End uPred.

(* Hint DB for the logic *)
Hint Resolve pure_intro : I.
Hint Resolve or_elim or_intro_l' or_intro_r' : I.
Hint Resolve and_intro and_elim_l' and_elim_r' : I.
Hint Resolve persistently_mono : I.
Hint Resolve sep_mono : I. (* sep_elim_l' sep_elim_r'  *)
Hint Immediate True_intro False_elim : I.
Hint Immediate iff_refl internal_eq_refl : I.
