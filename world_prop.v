(** In this file, we we define what it means to be a solution of the recursive
    domain equations to build a higher-order separation logic *)
Require Import ModuRes.PreoMet.
Require Import ModuRes.Finmap ModuRes.Constr.
Require Import ModuRes.RA ModuRes.UPred.

(* This interface keeps some of the details of the solution opaque *)
Module Type WORLD_PROP (Res : RA_T).
  Definition pres := ra_pos Res.res.
  
  (* PreProp: The solution to the recursive equation. Equipped with a discrete order. *)
  Parameter PreProp    : cmtyp.
  Instance PProp_preo  : preoType PreProp   := disc_preo PreProp.
  Instance PProp_pcm   : pcmType PreProp    := disc_pcm PreProp.
  Instance PProp_ext   : extensible PreProp := disc_ext PreProp.

  (* Defines Worlds, Propositions *)
  Definition Wld       := nat -f> PreProp.
  Definition Props     := Wld -m> UPred pres.

  (* Define all the things on Props, so they have names - this shortens the terms later. *)
  Instance Props_ty   : Setoid Props  | 1 := _.
  Instance Props_m    : metric Props  | 1 := _.
  Instance Props_cm   : cmetric Props | 1 := _.
  Instance Props_preo : preoType Props| 1 := _.
  Instance Props_pcm  : pcmType Props | 1 := _.

  (* Establish the recursion isomorphism *)
  Parameter ı  : PreProp -n> halve (cmfromType Props).
  Parameter ı' : halve (cmfromType Props) -n> PreProp.
  Axiom iso : forall P, ı' (ı P) == P.
  Axiom isoR: forall T, ı (ı' T) == T.
End WORLD_PROP.
