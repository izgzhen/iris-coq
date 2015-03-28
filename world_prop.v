(** In this file, we we define what it means to be a solution of the recursive
    domain equations to build a higher-order separation logic *)
Require Import ModuRes.PreoMet ModuRes.Finmap.
Require Import ModuRes.RA ModuRes.RAConstr ModuRes.SPred.

Local Open Scope type.

(* This interface keeps some of the details of the solution opaque *)
Module Type WORLD_PROP (Res : RA_T).
  (* We need a metric for the base resources. The discrete CMRA will be infered. *)
  Instance res_metric : metric Res.res := discreteMetric.
  Instance res_cmetric : cmetric Res.res := discreteCMetric.
  
  (* PreProp: The solution to the recursive equation. Equipped with a discrete order. *)
  Parameter PreProp    : Type.
  Declare Instance PProp_t  : Setoid PreProp.
  Declare Instance PProp_m  : metric PreProp.
  Declare Instance PProp_cm : cmetric PreProp.
  Instance PProp_preo  : preoType PreProp   := disc_preo PreProp.
  Instance PProp_pcm   : pcmType PreProp    := disc_pcm PreProp.

  (* Defines Worlds, and make sure their order comes from the RA. *)
  Definition Wld := (nat -f> ra_agree PreProp) * Res.res.
  Instance WldRA : RA Wld := _.
  Instance WldPO : preoType Wld := pord_ra. (* disambiguate the order *)

  (* Now we are ready to define Propositions. *)
  Definition Props    := Wld -m> SPred.
  Instance Props_ty   : Setoid Props   := _.
  Instance Props_m    : metric Props   := _.
  Instance Props_cm   : cmetric Props  := _.
  Instance Props_preo : preoType Props := _.
  Instance Props_pcm  : pcmType Props  := _.

  (* Require recursion isomorphisms *)
  Parameter ı  : PreProp -n> halve Props.
  Parameter ı' : halve Props -n> PreProp.
  Axiom iso : forall P, ı' (ı P) == P.
  Axiom isoR: forall T, ı (ı' T) == T.
End WORLD_PROP.
