Require Import ssreflect.
Require Import world_prop core_lang lang masks iris_core iris_plog iris_vs_rules iris_ht_rules.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_DERIVED_RULES (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) (VS_RULES: IRIS_VS_RULES RL C R WP CORE PLOG) (HT_RULES: IRIS_HT_RULES RL C R WP CORE PLOG).
  Export VS_RULES.
  Export HT_RULES.

  Local Open Scope lang_scope.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.

  (* Ideally, these rules should never talk about worlds or such.
     At the very least, they should not open the definition of the complex assertrtions:
     invariants, primitive view shifts, weakest pre. *)

  Section DerivedVSRules.

    Implicit Types (P : Props) (i : nat) (m : mask) (e : expr) (r : res).

    Lemma vsFalse m1 m2 :
      valid (vs m1 m2 ⊥ ⊥).
    Proof.
      rewrite ->valid_iff, box_top.
      unfold vs; apply box_intro.
      rewrite <- and_impl, and_projR.
      apply bot_false.
    Qed.

    Lemma vsNotOwnInvalid m1 m2 r
       (Hnval: ~↓r):
      valid (vs m1 m2 (ownR r) ⊥).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ Hown.
      eapply pvsNotOwnInvalid; eassumption.
    Qed.

    Lemma vsTimeless m P :
      timeless P ⊑ vs m m (▹P) P.
    Proof.
      move=>w0 n0 r0 Htl w1 Hw01 n1 r1 Hn01 _ HP.
      eapply pvsTimeless. split; last assumption.
      eapply propsMWN, Htl; eassumption.
    Qed.

    Lemma vsTrans P Q R m1 m2 m3 (HMS : m2 ⊆ m1 ∪ m3) :
      vs m1 m2 P Q ∧ vs m2 m3 Q R ⊑ vs m1 m3 P R.
    Proof.
      move=> w0 n0 r0 [HPQ HQR] w1 HSub n1 r1 Hlt _ HP.
      eapply pvsTrans; first by eauto.
      eapply pvsImpl; split; first eapply propsMWN; 
      [eassumption | eassumption | exact HQR | ].
      eapply HPQ; by eauto using unit_min.
    Qed.

    Lemma vsEnt P Q m :
      □(P → Q) ⊑ vs m m P Q.
    Proof.
      move => w0 n r0 HPQ w1 HSub n1 r1 Hlt _ /(HPQ _ HSub _ _ Hlt) HQ.
      eapply pvsEnt, HQ; exact unit_min.
    Qed.

    (* A weaker version of pvsImpl, not giving the implication the chance to only hold in some worlds *)
    Lemma pvsByImpl P Q m1 m2 :
      (P ⊑ Q) -> pvs m1 m2 P ⊑ pvs m1 m2 Q.
    Proof.
      move=> HPQ w0 n0 r0 Hpvs.
      eapply pvsImpl. split; last eassumption.
      move=>{Hpvs} w1 Hw01 n1 r1 Hn01 _ HP.
      eapply HPQ, HP.
    Qed.

    Existing Instance LP_res.

    Lemma vsGhostUpd m rl (P : RL.res -> Prop) (HU : rl ⇝∈ P) :
      valid (vs m m (ownL rl) (xist (ownLP P))).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ Hown.
      eapply pvsGhostUpd, Hown. assumption.
    Qed.

    Lemma pvsGhostStep m (rl rl': RL.res) (HU : rl ⇝ rl') :
      ownL rl ⊑ pvs m m (ownL rl').
    Proof.
      etransitivity.
      - pose(P:= fun r:RL.res => r = rl').
        eapply pvsGhostUpd with (P:=P).
        clear -HU. move=>rf Hval. exists rl'.
        split; first reflexivity.
        by eapply HU.
      - intros w0 n0 r0 Hpvs.
        eapply pvsByImpl; last eassumption.
        move=>{Hpvs w0 n0 r0} w0 n0 r0 [[rl'' Hrl''] Hown].
        subst rl''. exact Hown.
    Qed.

    Lemma vsGhostStep m (rl rl': RL.res) (HU : rl ⇝ rl') :
      valid (vs m m (ownL rl) (ownL rl')).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ Hown.
      eapply pvsGhostStep, Hown. assumption.
    Qed.

    Lemma vsOpen i P :
      valid (vs (mask_sing i) mask_emp (inv i P) (▹P)).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ Hinv.
      eapply pvsOpen, Hinv.
    Qed.

    Lemma vsClose i P :
      valid (vs mask_emp (mask_sing i) (inv i P ∧ ▹P) ⊤).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ Hpre.
      eapply pvsClose, Hpre.
    Qed.

    Existing Instance LP_mask.

    Lemma vsNewInv P m (HInf : mask_infinite m) :
      valid (vs m m (▹P) (xist (inv' m P))).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ HP.
      eapply pvsNewInv; eassumption.
    Qed.

  End DerivedVSRules.

  Section DerivedHTRules.

    Existing Instance LP_isval.

    Implicit Types (P : Props) (i : nat) (m : mask) (e : expr) (r : res) (φ Q : vPred) (w : Wld) (n k : nat).

    Lemma htRet e (HV : is_value e) safe m :
      valid (ht safe m ⊤ e (eqV (exist _ e HV))).
    Proof.
      move=>w0 n0 _ w1 Hw01 n1 r1 Hn01 _ _.
      eapply wpRet.
    Qed.
    
    (** Quantification in the logic works over nonexpansive maps, so
        we need to show that plugging the value into the postcondition
        and context is nonexpansive. *)
    Program Definition plugCtxHt safe m Q Q' K :=
      n[(fun v : value => ht safe m (Q v) (fill K v) Q' )].
    Next Obligation.
      intros v1 v2 EQv; unfold ht; eapply (met_morph_nonexp box).
      eapply (impl_dist (ComplBI := Props_BI)).
      - apply Q; assumption.
      - destruct n as [| n]; [apply dist_bound | simpl in EQv].
        rewrite EQv; reflexivity.
    Qed.

    Lemma htBind P Q R K e safe m :
      ht safe m P e Q ∧ all (plugCtxHt safe m Q R K) ⊑ ht safe m P (fill K e) R.
    Proof.
      move=>w0 n0 r0 [He HK] w1 Hw01 n1 r1 Hn01 _ HP.
      eapply wpBind. eapply wpImpl. split; last first.
      - unfold ht in He. specialize (He _ Hw01 _ _ Hn01 unit_min HP). eexact He. (* Why does eapply He not work? *)
      - intros v w2 Hw12 n2 r2 Hn12 _ HQ. simpl. unfold plugCtxHt in HK.
        move:HK. move/(_ v _ _ _ _ _ _ HQ)=>HK. apply HK. (* TODO: Nicer way to get these as goals (not requiring the current goal to match)? *)
        + etransitivity; eassumption.
        + omega.
        + apply: unit_min.
    Qed.

    (** Much like in the case of the plugging, we need to show that
        the map from a value to a view shift between the applied
        postconditions is nonexpansive *)
    Program Definition vsLift m1 m2 (φ φ' : vPred) :=
      n[(fun v => vs m1 m2 (φ v) (φ' v))].
    Next Obligation.
      intros v1 v2 EQv; unfold vs.
      rewrite ->EQv; reflexivity.
    Qed.

    Lemma pvsWpCompose {safe m m' P e φ}:
      pvs m m' P ∧ ht safe m' P e φ ⊑ pvs m m' (wp safe m' e φ).
    Proof.
      move=>w0 n0 r0 [Hpvs Hht]. unfold vsLift, vs, ht in *.
      eapply pvsImpl. split; eassumption.
    Qed.

    Lemma wpPvsCompose {safe m m' e φ φ'}:
      wp safe m' e φ ∧ all (vsLift m' m φ φ') ⊑ wp safe m' e (pvs m' m <M< φ').
    Proof.
      move=>w0 n0 r0 [Hwp Hvs]. unfold vsLift, vs, ht in *.
      eapply wpImpl. split; last eassumption.
      move=>v w1 Hw01 n1 r1 Hn01 _ Hφ. change (pvs m' m (φ' v) w1 n1 r1).
      specialize (Hvs v). apply: Hvs Hφ; [assumption|by apply:unit_min].
    Qed.

    Lemma htCons P P' Q Q' safe m e :
      vs m m P P' ∧ ht safe m P' e Q' ∧ all (vsLift m m Q' Q) ⊑ ht safe m P e Q.
    Proof.
      move=>w0 n0 r0 [HvsP [Hht HvsQ]] w1 Hw01 n1 r1 Hn01 _ HP.
      eapply wpPostVS, wpPvsCompose. split; last first.
      { eapply propsMWN; last apply: HvsQ; assumption. }
      eapply wpPreVS, pvsWpCompose. split; last first.
      { eapply propsMWN; last apply: Hht; assumption. }
      unfold vs in HvsP=>{Hht HvsQ}. eapply HvsP; (assumption || by apply: unit_min).
    Qed.

    Lemma htACons safe m m' e P P' Q Q'
          (HAt   : atomic e)
          (HSub  : m' ⊆ m) :
      vs m m' P P' ∧ ht safe m' P' e Q' ∧ all (vsLift m' m Q' Q) ⊑ ht safe m P e Q.
    Proof.
      move=>w0 n0 r0 [HvsP [Hht HvsQ]] w1 Hw01 n1 r1 Hn01 _ HP.
      unfold vsLift, vs, ht in *.
      eapply wpACons;[eassumption|eassumption|].
      eapply pvsWpCompose. split.
      { apply: HvsP; (assumption || by apply: unit_min). }
      move=>w2 Hw12 n2 r2 Hn12 Hr12 HP'.
      eapply wpPvsCompose. split; last first.
      { eapply propsMWN; last apply: HvsQ; (etransitivity;eassumption). }
      (* TODO: This next step is slow. It's still the most sensible script though. *)
      eapply Hht, HP'; ((etransitivity;eassumption) || by apply: unit_min).
    Qed.

    Lemma htFrame safe m m' P R e Q (HD : m # m') :
      ht safe m P e Q ⊑ ht safe (m ∪ m') (P * R) e (lift_bin sc Q (umconst R)).
    Proof.
      move=>w0 n0 r0 Hht w1 Hw01 n1 r1 Hn01 _ [r1_1 [r1_2 [HEQr [HP HR]]]].
      eapply wpFrameMask; first by assumption.
      eapply wpFrameRes. exists r1_1 r1_2. split; first assumption. split.
      - unfold ht in Hht. specialize (Hht _ Hw01 _ _ Hn01 unit_min HP). assumption.
      - assumption.
    Qed.

    Lemma htAFrame safe m m' P R e Q
          (HD  : m # m')
          (HAt : atomic e) :
      ht safe m P e Q ⊑ ht safe (m ∪ m') (P * ▹R) e (lift_bin sc Q (umconst R)).
    Proof.
      move=>w0 n0 r0 Hht w1 Hw01 n1 r1 Hn01 _ [r1_1 [r1_2 [HEQr [HP HLR]]]].
      eapply wpFrameMask; first by assumption.
      eapply wpAFrameRes; first assumption. exists r1_1 r1_2. split; first assumption. split.
      - unfold ht in Hht. specialize (Hht _ Hw01 _ _ Hn01 unit_min HP). assumption.
      - assumption.
    Qed.

    Lemma htFork safe m P R e :
      ht safe m P e (umconst ⊤) ⊑ ht safe m (▹P * ▹R) (fork e) (lift_bin sc (eqV (exist _ fork_ret fork_ret_is_value)) (umconst R)).
    Proof.
      move=>w0 n0 r0 Hht w1 Hw01 n1 r1 Hn01 _ [r1_1 [r1_2 [HEQr [HLP HLR]]]].
      eapply wpFork. exists r1_1 r1_2. split; first assumption. split.
      - eapply laterM. split; last by eapply HLP. move=> w2 Hw12 n2 r2 Hn12 Hr12 HP.
        move:Hht. move/(_ _ _ _ _ _ _ HP)=>{HP}HP. apply HP.
        + etransitivity; eassumption.
        + omega.
        + apply: unit_min.
      - assumption.
    Qed.

    Lemma htUnsafe {m P e Q} :
      ht true m P e Q ⊑ ht false m P e Q.
    Proof.
      move=>w0 n0 r0 Hht w1 Hw01 n1 r1 Hn01 _ HP.
      eapply wpUnsafe. move:Hht. move/(_ _ _ _ _ _ _ HP)=>{HP}HP. apply HP.
      + assumption.
      + apply: unit_min.
    Qed.

  End DerivedHTRules.

End IRIS_DERIVED_RULES.

Module IrisDerivedRules (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) (VS_RULES: IRIS_VS_RULES RL C R WP CORE PLOG) (HT_RULES: IRIS_HT_RULES RL C R WP CORE PLOG) : IRIS_DERIVED_RULES RL C R WP CORE PLOG VS_RULES HT_RULES.
  Include IRIS_DERIVED_RULES RL C R WP CORE PLOG VS_RULES HT_RULES.
End IrisDerivedRules.
