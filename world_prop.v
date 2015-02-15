(** In this file, we show how we can use the solution of the recursive
    domain equations to build a higher-order separation logic *)
Require Import ModuRes.PreoMet ModuRes.MetricRec ModuRes.CBUltInst.
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


(* Now we come to the actual implementation *)
Module WorldProp (Res : RA_T) : WORLD_PROP Res.

  (** The construction is parametric in the monoid we choose *)
  Definition pres := ra_pos Res.res.

  (** We need to build a functor that would describe the following
      recursive domain equation:
        Prop ≃ (Loc -f> Prop) -m> UPred (Res)
      As usual, we split the negative and (not actually occurring)
      positive occurrences of Prop. *)

  Section Definitions.
    (** We'll be working with complete metric spaces, so whenever
        something needs an additional preorder, we'll just take a
        discrete one. *)
    Local Instance pt_disc P `{cmetric P} : preoType P | 2000 := disc_preo P.
    Local Instance pcm_disc P `{cmetric P} : pcmType P | 2000 := disc_pcm P.

    Definition FProp P `{cmP : cmetric P} :=
      (nat -f> P) -m> UPred pres.

    Context {U V} `{cmU : cmetric U} `{cmV : cmetric V}.

    Definition PropMorph (m : V -n> U) : FProp U -n> FProp V :=
      fdMap (disc_m m) ▹.

  End Definitions.

  Module F <: SimplInput (CBUlt).
    Import CBUlt.
    Open Scope cat_scope.

    Definition F (T1 T2 : cmtyp) := cmfromType (FProp T1).
    Program Instance FArr : BiFMap F :=
      fun P1 P2 P3 P4 => n[(PropMorph)] <M< Mfst.
    Next Obligation.
      intros m1 m2 Eqm; unfold PropMorph, equiv in *.
      rewrite Eqm; reflexivity.
    Qed.

    Instance FFun : BiFunctor F.
    Proof.
      split; intros; unfold fmorph; simpl morph; unfold PropMorph.
      - rewrite disc_m_comp, <- fdMap_comp, <- ucomp_precomp.
        intros x; simpl morph; reflexivity.
      - rewrite disc_m_id, fdMap_id, pid_precomp.
        intros x; simpl morph; reflexivity.
    Qed.

    Definition F_ne : 1 -t> F 1 1 :=
      umconst (pcmconst (up_cr (const True))).
  End F.

  Module F_In := InputHalve(F).
  Module Import Fix := Solution(CBUlt)(F_In).

  (** Now we can name the two isomorphic spaces of propositions, and
      the space of worlds. We'll store the actual solutions in the
      worlds, and use the action of the FPropO on them as the space we
      normally work with. *)
  Definition PreProp := DInfO.
  Definition Props   := FProp PreProp.
  Definition Wld     := (nat -f> PreProp).

  (* Define an order on PreProp. *)
  Instance PProp_preo: preoType PreProp   := disc_preo PreProp.
  Instance PProp_pcm : pcmType PreProp    := disc_pcm PreProp.
  Instance PProp_ext : extensible PreProp := disc_ext PreProp.

  (* Give names to the things for Props, so the terms can get shorter. *)
  Instance Props_ty   : Setoid Props     := _.
  Instance Props_m    : metric Props     := _.
  Instance Props_cm   : cmetric Props    := _.
  Instance Props_preo : preoType Props   := _.
  Instance Props_pcm  : pcmType Props    := _.

  (* Establish the isomorphism *)
  Definition ı  : PreProp -t> halve (cmfromType Props) := Unfold.
  Definition ı' : halve (cmfromType Props) -t> PreProp := Fold.

  Lemma iso P : ı' (ı P) == P.
  Proof. apply (FU_id P). Qed.
  Lemma isoR T : ı (ı' T) == T.
  Proof. apply (UF_id T). Qed.

End WorldProp.
