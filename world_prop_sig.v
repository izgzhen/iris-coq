(* For some reason, the order matters. We cannot import Constr last. *)
Require Import ModuRes.Finmap ModuRes.Constr ModuRes.PCM ModuRes.UPred ModuRes.BI ModuRes.PreoMet.


Module Type WorldPropSig (Res : PCM_T).

  (** The construction is parametric in the monoid we choose *)
  Import Res.

  (* The functor is fixed *)
  Section Definitions.
    (** We'll be working with complete metric spaces, so whenever
        something needs an additional preorder, we'll just take a
        discrete one. *)
    Local Instance pt_disc P `{cmetric P} : preoType P | 2000 := disc_preo P.
    Local Instance pcm_disc P `{cmetric P} : pcmType P | 2000 := disc_pcm P.

    Definition FProp P `{cmP : cmetric P} :=
      (nat -f> P) -m> UPred res.
  End Definitions.

  Parameter PreProp  : Type.
  Parameter PrePropS : Setoid PreProp.
  Parameter PrePropM : metric PreProp.
  Parameter PrePropCM: cmetric PreProp.
  
  Definition Props     := FProp PreProp.
  Parameter PropS      : Setoid Props.
  Parameter PropM      : metric Props.
  Parameter PropCM     : cmetric Props.
  
  Definition Wld     := (nat -f> PreProp).

  Parameter ı  : PreProp -> halve (cmfromType Props).
  Parameter ı' : halve (cmfromType Props) -> PreProp.

  Axiom iso : forall P, ı' (ı P) == P.
  Axiom isoR : forall T, ı (ı' T) == T.

(*Parameter PProp_preo : preoType PreProp.
  Parameter PProp_pcm  : pcmType PreProp.
  Parameter PProp_ext  : extensible PreProp.*)

End WorldPropSig.
