From iris.bi Require Import bi telescopes.
From iris.proofmode Require Import base environments.

Declare Reduction pm_cbv := cbv [
  (* base *)
  base.beq base.Pos_succ base.ascii_beq base.string_beq base.positive_beq base.ident_beq
  (* environments *)
  env_lookup env_lookup_delete env_delete env_app env_replace
  env_dom env_intuitionistic env_spatial env_counter env_spatial_is_nil envs_dom
  envs_lookup envs_lookup_delete envs_delete envs_snoc envs_app
  envs_simple_replace envs_replace envs_split
  envs_clear_spatial envs_clear_persistent envs_incr_counter
  envs_split_go envs_split prop_of_env
].
(* Some things should only be unfolded according to cbn rules, when
   certain arguments are constructors. This is because they can appear in
   the user side of proofs as well. *)
Declare Reduction pm_cbn := cbn [
  (* PM option combinators *)
  pm_option_bind pm_from_option pm_option_fun
  (* telescope combinators *)
  tele_fold tele_bind tele_app
  (* BI connectives *)
  bi_persistently_if bi_affinely_if bi_intuitionistically_if
  bi_wandM sbi_laterN big_opL
  bi_tforall bi_texist
].
Ltac pm_eval t :=
  let u := eval pm_cbv in t in
  let v := eval pm_cbn in u in
  v.
Ltac pm_reduce :=
  match goal with |- ?u => let v := pm_eval u in change v end.
Ltac pm_reflexivity := pm_reduce; exact eq_refl.

(** Called e.g. by iApply for redexes that are created by instantiation.
    This cannot create any envs redexes so we just to the cbn part. *)
Ltac pm_prettify :=
  match goal with |- ?u => let v := eval pm_cbn in u in change v end.
