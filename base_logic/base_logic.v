From iris.base_logic Require Export derived.

Module uPred.
  Include uPred_entails.
  Include uPred_primitive.
  Include uPred_derived.
End uPred.

(* Hint DB for the logic *)
Import uPred.
Hint Resolve pure_intro.
Hint Resolve or_elim or_intro_l' or_intro_r' : I.
Hint Resolve and_intro and_elim_l' and_elim_r' : I.
Hint Resolve always_mono : I.
Hint Resolve sep_elim_l' sep_elim_r' sep_mono : I.
Hint Immediate True_intro False_elim : I.
Hint Immediate iff_refl eq_refl' : I.
