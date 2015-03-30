(** In this file, we show how we can obtain a solution of the recursive
    domain equations to build a higher-order separation logic *)
Require Import ModuRes.PreoMet ModuRes.Finmap ModuRes.RA ModuRes.Agreement ModuRes.SPred.
Require Import ModuRes.CatBasics ModuRes.MetricRec ModuRes.CBUltInst.
Require Import world_prop.

(* Now we come to the actual implementation *)
Module WorldProp (Res : RA_T) : WORLD_PROP Res.
  (** The construction is parametric in the monoid we choose *)

  (** We need to build a functor that would describe the following
      recursive domain equation:
        Prop ≃ (Loc -f> ra_agree Prop) * Res -m> SPred
      As usual, we split the negative and (not actually occurring)
      positive occurrences of Prop. *)

  Local Open Scope type.

  (** We need a metric for the base resources. The discrete CMRA will be infered. *)
  Local Instance res_metric : metric Res.res := discreteMetric.
  Local Instance res_cmetric : cmetric Res.res := discreteCMetric.

  (** Finally, we need the right pcmType for the entire resource *)
  Definition FRes P `{metric P} := (nat -f> ra_agree P) * Res.res.
  Local Instance FResCMRA P `{cmetric P} : CMRA (FRes P) := _.
  Local Instance FResPO P `{cmetric P} : preoType (FRes P) := pord_ra. (* disambiguate the order *)

  Section Definitions.
    (** We'll be working with complete metric spaces, so whenever
        something needs an additional preorder, we'll just take a
        discrete one. *)
    Local Instance pt_disc P `{cmetric P} : preoType P | 2000 := disc_preo P.
    Local Instance pcm_disc P `{cmetric P} : pcmType P | 2000 := disc_pcm P.

    Section ObjectAction.
      Context (P: Type) `{cmP: cmetric P}.
      
      Definition FProp :=
        FRes P -m> SPred.
    End ObjectAction.

    Section ArrowAction.
      Context {U V} `{cmU : cmetric U} `{cmV : cmetric V}.

      Context (m: V -n> U).
      Let InvMap : FRes V -m> FRes U :=
        RAprod_map (fdRAMap (ra_agree_map m)) (pid _).
      Definition PropMorph : FProp U -n> FProp V :=
        InvMap ▹. (* this "later" is post-composition *)
    End ArrowAction.

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
      - eapply precomp_by_comp. rewrite <-ra_agree_map_comp, <-fdRAMap_comp. eapply RAprod_map_comp_fst.
      - eapply precomp_by_id. unfold tid, MId. rewrite ra_agree_map_id, fdRAMap_id.
        eapply RAprod_map_id.
    Qed.

    Definition F_ne : 1 -t> F 1 1 :=
      umconst (pcmconst (sp_c True)).
  End F.

  Module F_In := InputHalve(F).
  Module Import Fix := Solution(CBUlt)(F_In).

  (** Now we can name the two isomorphic spaces of propositions, and
      the space of worlds. We'll store the actual solutions in the
      worlds, and use the action of FProp on them as the space we
      normally work with. *)
  Definition PreProp : Type := DInfO.
  Instance PProp_t  : Setoid PreProp := _.
  Instance PProp_m  : metric PreProp := _.
  Instance PProp_cm : cmetric PreProp := _.
  Instance PProp_preo: preoType PreProp   := disc_preo PreProp.
  Instance PProp_pcm : pcmType PreProp    := disc_pcm PreProp.

  (* Define worlds *)
  Definition Wld     := FRes PreProp.
  Instance WldRA : RA Wld := _.
  Instance WldPO : preoType Wld := _.

  (* Define propositions *)
  Definition Props   := FProp PreProp.
  Instance Props_ty   : Setoid Props     := _.
  Instance Props_m    : metric Props     := _.
  Instance Props_cm   : cmetric Props    := _.
  Instance Props_preo : preoType Props   := _.
  Instance Props_pcm  : pcmType Props    := _.

  (* Establish the isomorphism *)
  Definition ı  : DInfO -t> halveCM (cmfromType Props) := Unfold.
  Definition ı' : halveCM (cmfromType Props) -t> DInfO := Fold.

  Lemma iso P : ı' (ı P) == P.
  Proof. apply (FU_id P). Qed.
  Lemma isoR T : ı (ı' T) == T.
  Proof. apply (UF_id T). Qed.

End WorldProp.
