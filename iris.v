Require Import world_prop core_lang lang masks.
Require Import RecDom.PCM RecDom.UPred RecDom.BI RecDom.PreoMet.

Module Iris (RP RL : PCM_T) (C : CORE_LANG RP).

  Module Import L  := Lang RP RL C.
  Module R : PCM_T.
    Definition res := (RP.res * RL.res)%type.
    Instance res_op   : PCM_op res := _.
    Instance res_unit : PCM_unit res := _.
    Instance res_pcm  : PCM res := _.
  End R.
  Module Import WP := WorldProp R.

  (** The final thing we'd like to check is that the space of
      propositions does indeed form a complete BI algebra.

      The following instance declaration checks that an instance of
      the complete BI class can be found for Props (and binds it with
      a low priority to potentially speed up the proof search).
   *)

  Instance Props_BI : ComplBI Props | 0 := _.
  Instance Props_Later : Later Props | 0 := _.

  (** And now we're ready to build the IRIS-specific connectives! *)

  Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

  (** Always (could also be moved to BI, since works for any UPred
      over a monoid). *)
  Program Definition always : Props -n> Props :=
    n[(fun p => m[(fun w => mkUPred (fun n r => p w n (pcm_unit _)) _)])].
  Next Obligation.
    intros n m r s HLe _ Hp; rewrite HLe; assumption.
  Qed.
  Next Obligation.
    intros w1 w2 EQw m r HLt; simpl.
    eapply (met_morph_nonexp _ _ p); eassumption.
  Qed.
  Next Obligation.
    intros w1 w2 Subw n r; simpl.
    apply p; assumption.
  Qed.
  Next Obligation.
    intros p1 p2 EQp w m r HLt; simpl.
    apply EQp; assumption.
  Qed.

End Iris.