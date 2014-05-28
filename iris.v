Require Import world_prop core_lang lang masks.
Require Import RecDom.PCM RecDom.UPred RecDom.BI RecDom.PreoMet RecDom.Finmap.

Module Iris (RP RL : PCM_T) (C : CORE_LANG RP).

  Module Import L  := Lang RP RL C.
  Module R <: PCM_T.
    Definition res := (RP.res * RL.res)%type.
    Instance res_op   : PCM_op res := _.
    Instance res_unit : PCM_unit res := _.
    Instance res_pcm  : PCM res := _.
  End R.
  Module Import WP := WorldProp R.

  Delimit Scope iris_scope with iris.
  Local Open Scope iris_scope.

  (** The final thing we'd like to check is that the space of
      propositions does indeed form a complete BI algebra.

      The following instance declaration checks that an instance of
      the complete BI class can be found for Props (and binds it with
      a low priority to potentially speed up the proof search).
   *)

  Instance Props_BI : ComplBI Props | 0 := _.
  Instance Props_Later : Later Props | 0 := _.

  (** And now we're ready to build the IRIS-specific connectives! *)

  Section Necessitation.
    (** Note: this could be moved to BI, since it's possible to define
        for any UPred over a monoid. **)

    Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

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

  End Necessitation.

  (** "Internal" equality **)
  Section IntEq.
    Context {T} `{mT : metric T}.

    Program Definition intEqP (t1 t2 : T) : UPred R.res :=
      mkUPred (fun n r => t1 = S n = t2) _.
    Next Obligation.
      intros n1 n2 _ _ HLe _; apply mono_dist; now auto with arith.
    Qed.

    Program Definition intEq (t1 t2 : T) : Props := pcmconst (intEqP t1 t2).

    Instance intEq_equiv : Proper (equiv ==> equiv ==> equiv) intEqP.
    Proof.
      intros l1 l2 EQl r1 r2 EQr n r.
      split; intros HEq; do 2 red.
      - rewrite <- EQl, <- EQr; assumption.
      - rewrite EQl, EQr; assumption.
    Qed.

    Instance intEq_dist n : Proper (dist n ==> dist n ==> dist n) intEqP.
    Proof.
      intros l1 l2 EQl r1 r2 EQr m r HLt.
      split; intros HEq; do 2 red.
      - etransitivity; [| etransitivity; [apply HEq |] ];
        apply mono_dist with n; eassumption || now auto with arith.
      - etransitivity; [| etransitivity; [apply HEq |] ];
        apply mono_dist with n; eassumption || now auto with arith.
    Qed.

  End IntEq.

  Notation "t1 '===' t2" := (intEq t1 t2) (at level 70) : iris_scope.

  (** Invariants **)
  Definition invP (i : nat) (p : Props) (w : Wld) : UPred R.res :=
    intEqP (w i) (Some (ı' p)).
  Program Definition inv i : Props -n> Props :=
    n[(fun p => m[(invP i p)])].
  Next Obligation.
    intros w1 w2 EQw; unfold equiv, invP in *.
    apply intEq_equiv; [apply EQw | reflexivity].
  Qed.
  Next Obligation.
    intros w1 w2 EQw; unfold invP; simpl morph.
    destruct n; [apply dist_bound |].
    apply intEq_dist; [apply EQw | reflexivity].
  Qed.
  Next Obligation.
    intros w1 w2 Sw; unfold invP; simpl morph.
    intros n r HP; do 2 red; specialize (Sw i); do 2 red in HP.
    destruct (w1 i) as [μ1 |]; [| contradiction].
    destruct (w2 i) as [μ2 |]; [| contradiction]; simpl in Sw.
    rewrite <- Sw; assumption.
  Qed.
  Next Obligation.
    intros p1 p2 EQp w; unfold equiv, invP in *; simpl morph.
    apply intEq_equiv; [reflexivity |].
    rewrite EQp; reflexivity.
  Qed.
  Next Obligation.
    intros p1 p2 EQp w; unfold invP; simpl morph.
    apply intEq_dist; [reflexivity |].
    apply dist_mono, (met_morph_nonexp _ _ ı'), EQp.
  Qed.

  (** Ownership **)
  Definition own (r : R.res) : Props :=
    pcmconst (up_cr (pord r)).

  (** Physical part **)
  Definition ownP (r : RP.res) : Props :=
    own (r, pcm_unit _).

  (** Logical part **)
  Definition ownL (r : RL.res) : Props :=
    own (pcm_unit _, r).

End Iris.
