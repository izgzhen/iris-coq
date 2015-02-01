(* For some reason, the order matters. We cannot import Constr last. *)
Require Import ModuRes.Finmap ModuRes.Constr ModuRes.MetricRec.
Require Import ModuRes.PCM ModuRes.UPred ModuRes.BI ModuRes.PreoMet.


Module Type WORLD_PROP (Res : PCM_T).
  Import Res.

  (* PreProp: The solution to the recursive equation. Equipped with a discrete order *)
  Parameter PreProp    : cmtyp.
  Instance PProp_preo: preoType PreProp   := disc_preo PreProp.
  Instance PProp_pcm : pcmType PreProp    := disc_pcm PreProp.
  Instance PProp_ext : extensible PreProp := disc_ext PreProp.

  (* Defines Worlds, Propositions *)
  Definition Wld       := nat -f> PreProp.
  Definition Props     := Wld -m> UPred res.

  (* Establish the recursion isomorphism *)
  Parameter ı  : PreProp -t> halve (cmfromType Props).
  Parameter ı' : halve (cmfromType Props) -t> PreProp.
  Axiom iso : forall P, ı' (ı P) == P.
  Axiom isoR: forall T, ı (ı' T) == T.

  (* Define all the things on Props, so they have names - this shortens the terms later *)
  Instance Props_ty   : Setoid Props := _.
  Instance Props_m    : metric Props := _.
  Instance Props_cm   : cmetric Props := _.
  Instance Props_preo : preoType Props := _.
  Instance Props_pcm  : pcmType Props := _.
End WORLD_PROP.
