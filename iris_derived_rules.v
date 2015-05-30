Require Import ssreflect.
Require Import world_prop core_lang lang iris_core iris_plog iris_vs_rules iris_ht_rules.
Require Import ModuRes.RA ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.CMRA ModuRes.DecEnsemble.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_DERIVED_RULES (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) (VS_RULES: IRIS_VS_RULES RL C R WP CORE PLOG) (HT_RULES: IRIS_HT_RULES RL C R WP CORE PLOG).
  Export VS_RULES.
  Export HT_RULES.

  Local Open Scope lang_scope.
  Local Open Scope ra_scope.
  Local Open Scope de_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.

  (* Ideally, these rules should never talk about worlds or such.
     At the very least, they should not open the definition of the complex assertions:
     invariants, primitive view shifts, weakest pre. *)

  Section DerivedVSRules.

    Implicit Types (P : Props) (i : nat) (m : DecEnsemble nat) (e : expr) (r : res) (l: RL.res).

    Lemma pvsImpl P Q m1 m2 : 
      □ (P → Q) ∧ pvs m1 m2 P ⊑ pvs m1 m2 Q.
    Proof.
      rewrite -box_conj_star comm. rewrite ->pvsFrameRes. eapply pvsMon.
      rewrite comm box_conj_star. apply and_impl, box_elim.
    Qed.

    Lemma vsIntro R m1 m2 P Q:
      □R ⊑ vs m1 m2 P Q <-> □R ∧ P ⊑ pvs m1 m2 Q.
    Proof.
      split=>H.
      - unfold vs in H.
        apply and_impl. etransitivity; last by eapply box_elim. assumption.
      - unfold vs; apply box_intro. rewrite <-and_impl. assumption.
    Qed.

    Lemma vsValid m1 m2 P Q:
      valid (vs m1 m2 P Q) <-> P ⊑ pvs m1 m2 Q.
    Proof.
      rewrite ->top_valid, box_top. split=>H.
      - etransitivity; last by erewrite <-vsIntro. apply and_R; split; last reflexivity.
        rewrite <-box_top. apply top_true.
      - etransitivity; first apply vsIntro; last reflexivity.
        rewrite <-H. apply and_projR.
    Qed.

    Lemma vsFalse m1 m2 :
      valid (vs m1 m2 ⊥ ⊥).
    Proof.
      apply vsValid. apply bot_false.
    Qed.

    Lemma vsNotOwnInvalid m1 m2 l
       (Hnval: ~↓l):
      valid (vs m1 m2 (ownL l) ⊥).
    Proof.
      apply vsValid. etransitivity.
      { rewrite ownL_iff /own_ghost. reflexivity. }
      apply xist_L=>I. apply xist_L=>S. rewrite {1}/met_morph /mkNMorph {1}/morph. 
      etransitivity; last by eapply pvsNotOwnInvalid.
      apply and_R; split; last reflexivity.
      apply and_impl.
      (* We now prove this in the model. It does not really warrant it's own metatheory... *)
      move=>w n. destruct n; first (intro; exact:bpred).
      intros [[Hw' Heq] Hval]. simpl in *.
      tauto.
    Qed.

    (* TODO RJ: ownS * ownS => ⊥ *)

    Lemma vsTimeless m P : (* TODO RJ: the box is missing in the appendix? timeless will become a modality anyway. *)
      □(timeless P) ⊑ vs m m (▹P) P.
    Proof.
      apply vsIntro. etransitivity; last by eapply pvsTimeless.
      apply and_pord; last reflexivity.
      apply box_elim.
    Qed.

    Lemma vsTrans P Q R m1 m2 m3 (HMS : m2 ⊑ m1 ∪ m3) :
      vs m1 m2 P Q ∧ vs m2 m3 Q R ⊑ vs m1 m3 P R.
    Proof.
      rewrite {1 2}/vs -box_conj. apply vsIntro.
      etransitivity; last by eapply pvsTrans.
      etransitivity; last by eapply pvsImpl. apply and_R; split.
      - rewrite ->and_projL, box_conj. apply and_projR.
      - eapply modus_ponens; last first.
        + rewrite ->and_projL, box_conj, ->and_projL.
          now apply box_elim.
        + now apply and_projR.
    Qed.

    Lemma vsEnt P Q m :
      □(P → Q) ⊑ vs m m P Q.
    Proof.
      apply vsIntro.
      etransitivity; last by eapply pvsEnt.
      apply and_impl, box_elim.
    Qed.

    Lemma vsGhostUpd m rl (P : RL.res -> Prop) (HU : rl ⇝∈ P) :
      valid (vs m m (ownL rl) (xist (ownLP P))).
    Proof.
      apply vsValid.
      eapply pvsGhostUpd; assumption.
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
      - eapply pvsMon. apply xist_L=>s. case:s=>[s Heq]. subst s.
        rewrite /ownLP. simpl. reflexivity.
    Qed.

    Lemma vsGhostStep m (rl rl': RL.res) (HU : rl ⇝ rl') :
      valid (vs m m (ownL rl) (ownL rl')).
    Proof.
      apply vsValid.
      eapply pvsGhostStep; assumption.
    Qed.

    Lemma vsOpen i m P :
      i ∈ m = false ->
      valid (vs (de_sing i ∪ m) m (inv i P) (▹P)).
    Proof.
      intros Hm.
      apply vsValid. etransitivity; first by apply pvsOpen.
      etransitivity; last eapply pordR.
      - eapply pvsFrameMask with (mf:=m). move=>j. de_tauto.
      - eapply pvs_mproper; move=>j; de_tauto.
    Qed.

    Lemma vsClose i m P :
      i ∈ m = false ->
      valid (vs m (de_sing i ∪ m) (inv i P ∧ ▹P) ⊤).
    Proof.
      intros Hm. apply vsValid.
      etransitivity; first by apply pvsClose.
      etransitivity; last eapply pordR.
      - eapply pvsFrameMask with (mf:=m). move=>j. de_tauto.
      - eapply pvs_mproper; move=>j; de_tauto.
    Qed.

    Lemma vsNewInv P m (HInf : de_infinite m) :
      valid (vs m m (▹P) (xist (inv' m P))).
    Proof.
      apply vsValid. eapply pvsNewInv. assumption.
    Qed.

    Lemma vsFrame m1 m2 mf P Q R:
      mf # m1 ∪ m2 ->
      vs m1 m2 P Q ⊑ vs (m1 ∪ mf) (m2 ∪ mf) (P * R) (Q * R).
    Proof.
      move=>H. rewrite {1}/vs. apply vsIntro.
      etransitivity; last eapply pvsFrameRes.
      etransitivity; last first.
      { eapply sc_pord; last reflexivity. eapply pvsFrameMask. assumption. }
      rewrite -box_conj_star assoc. apply sc_pord; last reflexivity.
      rewrite box_conj_star. apply and_impl, box_elim.
    Qed.

  End DerivedVSRules.

  Section DerivedHTRules.

    Existing Instance LP_isval.

    Implicit Types (P : Props) (i : nat) (m : DecEnsemble nat) (e : expr) (r : res) (φ Q : vPred) (w : Wld) (n k : nat).

    Lemma htIntro R safe m e P Q:
      □R ⊑ ht safe m P e Q <-> □R ∧ P ⊑ wp safe m e Q.
    Proof.
      split=>H.
      - unfold vs in H.
        apply and_impl. etransitivity; last by eapply box_elim. assumption.
      - unfold vs; apply box_intro. rewrite <-and_impl. assumption.
    Qed.

    Lemma htValid safe m e P Q:
      valid (ht safe m P e Q) <-> P ⊑ ht safe m e Q.
    Proof.
      rewrite ->top_valid, box_top. split=>H.
      - etransitivity; last by erewrite <-vsIntro. apply and_R; split; last reflexivity.
        rewrite <-box_top. apply top_true.
      - etransitivity; first apply vsIntro; last reflexivity.
        rewrite <-H. apply and_projR.
    Qed.


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

Module IrisDerivedRules (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) (VS_RULES: IRIS_VS_RULES RL C R WP CORE PLOG) (HT_RULES: IRIS_HT_RULES RL C R WP CORE PLOG) : IRIS_DERIVED_RULES RL C R WP CORE PLOG VS_RULES HT_RULES.
  Include IRIS_DERIVED_RULES RL C R WP CORE PLOG VS_RULES HT_RULES.
End IrisDerivedRules.
