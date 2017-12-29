From iris.bi Require Export derived_laws big_op updates embedding.
Set Default Proof Using "Type".

Module Import bi.
  Export bi.interface.bi.
  Export bi.derived_laws.bi.
  Export bi.big_op.bi.
End bi.

(* Hint DB for the logic *)
Hint Resolve pure_intro.
Hint Resolve or_elim or_intro_l' or_intro_r' : BI.
Hint Resolve and_intro and_elim_l' and_elim_r' : BI.
Hint Resolve persistently_mono : BI.
Hint Resolve sep_elim_l sep_elim_r sep_mono : BI.
Hint Immediate True_intro False_elim : BI.
(*
Hint Immediate iff_refl internal_eq_refl' : BI.
*)