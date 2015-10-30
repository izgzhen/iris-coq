Require Import Ssreflect.ssreflect.
Require Import world_prop core_lang lang iris_core iris_plog iris_vs_rules iris_ht_rules.
Require Import ModuRes.RA ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.CMRA ModuRes.DecEnsemble.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_DERIVED_RULES (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) (VS_RULES: IRIS_VS_RULES RL C R WP CORE PLOG) (HT_RULES: IRIS_HT_RULES RL C R WP CORE PLOG).
  Export VS_RULES.
  Export HT_RULES.

  Local Open Scope ra_scope.
  Local Open Scope de_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.

  (* These rules and their proofs should never talk about worlds or step-indices. *)

  Section DerivedVSRules.

    Implicit Types (P : Props) (i : nat) (m : DecEnsemble nat) (e : expr) (r : res) (l: RL.res).

    Lemma pvsImpl P Q m1 m2 : 
      □ (P → Q) ∧ pvs m1 m2 P ⊑ pvs m1 m2 Q.
    Proof.
      rewrite -box_conj_star comm. rewrite ->pvsFrameRes. eapply pvsMon.
      rewrite comm box_conj_star. apply and_impl, box_elim.
    Qed.

    Lemma pvsWeakenMask P m m' (HIncl: m ⊑ m'):
      pvs m m P ⊑ pvs m' m' P.
    Proof.
      etransitivity; first eapply pvsFrameMask with (mf := m' \ m); first by de_auto_eq.
      apply pordR. eapply pvs_mproper; de_auto_eq.
    Qed.

    Lemma vsFalse m1 m2 :
      valid (vs m1 m2 ⊥ ⊥).
    Proof.
      apply vsValid. apply bot_false.
    Qed.

    Lemma vsOwnValid m l:
      valid (vs m m (ownL l) (ownL l ∧ pcmconst (sp_const (↓l)))).
    Proof.
      apply vsValid. etransitivity.
      { rewrite ownL_iff /own_ghost. reflexivity. }
      apply xist_L=>I. apply xist_L=>S. rewrite {1}/met_morph /mkNMorph {1}/morph. 
      etransitivity; first by eapply pvsOwnValid.
      eapply pvsMon. apply and_pord.
      - rewrite ownL_iff. apply (xist_R I). apply (xist_R S). reflexivity.
      - (* We now prove this in the model. It does not really warrant it's own metatheory... *)
        move=>w n. destruct n; first (intro; exact:bpred). simpl. tauto.
    Qed.

    Lemma vsOwnSTwice m σ1 σ2:
      valid (vs m m (ownS σ1 * ownS σ2) ⊥).
    Proof.
      apply vsValid. etransitivity.
      { rewrite !ownS_iff /own_state. reflexivity. }
      etransitivity; first apply xist_sc. apply xist_L=>I1. simpl.
      etransitivity; first apply xist_sc. apply xist_L=>g1. simpl.
      etransitivity; first apply xist_sc_r. apply xist_L=>I2. simpl.
      etransitivity; first apply xist_sc_r. apply xist_L=>g2. simpl.
      rewrite /const. rewrite- own_sc. etransitivity; first eapply pvsOwnValid.
      eapply pvsMon. rewrite ->and_projR.
      (* We now prove this in the model. It does not really warrant it's own metatheory... *)
      move=>w n [_ [HSval _]]. destruct n; first exact:bpred.
      destruct HSval.
    Qed.

    Lemma vsTimeless m P : (* TODO RJ: the box is missing in the appendix? timeless will become a modality anyway. *)
      □(timeless P) ⊑ vs m m (▹P) P.
    Proof.
      apply vsIntro. etransitivity; last by eapply pvsTimeless.
      rewrite ->box_elim. reflexivity.
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
      etransitivity; last by eapply pvsFrameRes.
      etransitivity; last first.
      { eapply sc_pord; last reflexivity. eapply pvsFrameMask. assumption. }
      rewrite -box_conj_star assoc. apply sc_pord; last reflexivity.
      rewrite box_conj_star. apply and_impl, box_elim.
    Qed.

  End DerivedVSRules.

  Section DerivedHTRules.

    Implicit Types (P : Props) (i : nat) (m : DecEnsemble nat) (e : expr) (r : res) (φ Q : vPred) (w : Wld) (n k : nat).

    Lemma wpImpl safe m e φ φ':
      (□all (lift_bin BI.impl φ φ')) ∧ wp safe m e φ ⊑ wp safe m e φ'.
    Proof.
      rewrite -box_conj_star comm. rewrite ->wpFrameRes. eapply wpMon.
      move=>v. rewrite /lift_bin [box]lock /= /const /= -lock.
      rewrite comm box_conj_star.
      eapply modus_ponens; first by apply and_projR.
      etransitivity; first by apply and_projL.
      etransitivity; first by apply box_elim.
      apply (all_L v). reflexivity.
    Qed.

    Lemma wpFrameMask safe m1 m2 e φ (*HD : m1 # m2*) :
      wp safe m1 e φ ⊑ wp safe (m1 ∪ m2) e φ.
    Proof.
      eapply wpWeakenMask. de_auto_eq.
    Qed.

    Lemma htRet e (HV : is_value e) safe m :
      valid (ht safe m ⊤ e (eqV (exist _ e HV))).
    Proof.
      apply htValid. etransitivity; last eapply wpMon.
      - apply top_valid. eapply wpRet.
      - intros v. eapply pvsEnt.
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

    Program Definition pvsLift m1 m2 (φ φ' : vPred) :=
      n[(fun v => φ v → pvs m1 m2 (φ' v))].
    Next Obligation.
      intros v1 v2 EQv. apply impl_dist; first now rewrite EQv.
      apply (met_morph_nonexp (pvs m1 m2)). now rewrite EQv.
    Qed.

    Lemma pvsWpCompose {safe m m' P e φ}:
      pvs m m' P ∧ ht safe m' P e φ ⊑ pvs m m' (wp safe m' e (pvs m' m' <M< φ)).
    Proof.
      rewrite /ht comm. etransitivity; first by apply pvsImpl.
      apply pvsMon. reflexivity.
    Qed.

    Lemma vsLiftBox m' m φ φ':
      □all (pvsLift m' m φ φ') == all (vsLift m' m φ φ').
    Proof.
      etransitivity; first by eapply (box_all (pvsLift m' m φ φ')).
      apply all_equiv=>v. reflexivity.
    Qed.

    Lemma wpPvsCompose {safe m m' e φ φ'}:
      wp safe m' e φ ∧ all (vsLift m' m φ φ') ⊑ wp safe m' e (pvs m' m <M< φ').
    Proof.
      rewrite -vsLiftBox /vs.
      rewrite comm. etransitivity; last by apply wpImpl.
      eapply and_pord; last reflexivity. apply pordR.
      apply box_equiv. apply all_equiv=>v. reflexivity.
    Qed.

    Lemma wpPreVS' m safe e φ:
      pvs m m (wp safe m e (pvs m m <M< φ)) ⊑ wp safe m e (pvs m m <M< φ).
    Proof.
      etransitivity; first eapply wpPreVS. eapply wpMon=>v. simpl morph. eapply pvsTrans.
      de_auto_eq.
    Qed.

    (* pvs before and after the hoare triple can be collapsed into it *)
    Lemma htMCons m m' safe e P P' Q Q':
      □((P → (pvs m m') P')
        ∧ (P' → (((wp safe) m') e) (pvs m' m' <M< Q')) ∧ all (pvsLift m' m Q' Q))
      ∧ P ⊑ (pvs m m') ((((wp safe) m') e) (pvs m' m <M< Q)).
    Proof. (* Stupid Coq makes me write out these things... *)
      transitivity ((pvs m m') P' ∧ □((P' → (((wp safe) m') e) (pvs m' m' <M< Q')) ∧ all (pvsLift m' m Q' Q))). 
      - apply and_R; split.
        + apply and_impl. rewrite ->box_elim. apply and_projL.
        + rewrite ->and_projL. apply box_intro. rewrite ->box_elim. apply and_projR.
      - etransitivity; last eapply pvsImpl. apply and_R; split; last by apply and_projL.
        rewrite ->and_projR. apply box_intro. rewrite ->box_conj, ->box_elim. rewrite -and_impl.
        transitivity ((□all (pvsLift m' m Q' Q)) ∧ (((wp safe) m') e) (pvs m' m' <M< Q') ).
        + apply and_R; split.
          * rewrite ->and_projL. apply and_projR.
          * apply and_impl. apply and_projL.
        + etransitivity; last eapply wpImpl. apply and_R; split; last by apply and_projR.
          rewrite ->and_projL. apply box_intro. apply all_R. intros v.
          apply and_impl. etransitivity; last eapply pvsTrans with (m2:=m'); last by de_auto_eq.
          etransitivity; last eapply pvsImpl. apply and_R; split; last first.
          * apply and_projR.
          * rewrite ->and_projL. apply box_intro. rewrite ->box_elim. apply (all_L v). reflexivity.
    Qed.

    Lemma htCons P P' Q Q' safe m e :
      vs m m P P' ∧ ht safe m P' e Q' ∧ all (vsLift m m Q' Q) ⊑ ht safe m P e Q.
    Proof.
      rewrite /vs {1}/ht -vsLiftBox -!box_conj. apply htIntro.
      etransitivity; first by eapply htMCons. etransitivity; first by eapply wpPreVS'.
      reflexivity.
    Qed.

    Lemma htACons safe m m' e P P' Q Q'
          (HAt   : atomic e)
          (HSub  : m' ⊑ m) :
      vs m m' P P' ∧ ht safe m' P' e Q' ∧ all (vsLift m' m Q' Q) ⊑ ht safe m P e Q.
    Proof.
      rewrite /vs {1}/ht -vsLiftBox -!box_conj. apply htIntro.
      etransitivity; last (eapply wpACons; eassumption).
      eapply htMCons.
    Qed.


    Section Bind.
      (** Quantification in the logic works over nonexpansive maps, so
        we need to show that plugging the value into the postcondition
        and context is nonexpansive. *)
      Program Definition plug_bind (fill: expr -> expr) safe m Q Q' :=
        n[(fun v : value => ht safe m (Q v) (fill v) Q' )].
      Next Obligation.
        intros v1 v2 EQv; unfold ht; eapply box_dist.
        eapply impl_dist.
        - apply Q; assumption.
        - destruct n as [| n]; [apply dist_bound | hnf in EQv].
          rewrite EQv; reflexivity.
      Qed.

      Lemma htBind fill P Q R e safe m (HFill: IsFill fill) :
        ht safe m P e Q ∧ all (plug_bind fill safe m Q R) ⊑ ht safe m P (fill e) R.
      Proof.
        rewrite /plug_bind {1 2}/ht. etransitivity; last eapply htIntro.
        { erewrite box_conj. apply and_pord; first reflexivity.
          erewrite (box_all (plug_bind fill safe m (pvs m m <M< Q) R)). apply all_pord=>v. simpl morph.
          rewrite /ht. apply box_intro, box_intro. apply and_impl.
          etransitivity; last eapply wpPreVS'. etransitivity; first by eapply pvsImpl. reflexivity.  }
        etransitivity; last by eapply wpBind.
        etransitivity; last eapply wpImpl with (φ:=pvs m m <M< Q). apply and_R; split.
        - rewrite ->and_projL. apply box_intro. rewrite ->box_elim, ->and_projR.
          apply all_pord=>v. simpl morph. rewrite /ht. rewrite ->box_elim. reflexivity.
        - eapply modus_ponens; first by apply and_projR.
          rewrite ->and_projL, ->box_elim, and_projL. reflexivity.
      Qed.
    End Bind.


    Lemma htWeakenMask safe m m' P e Q (HD: m ⊑ m'):
      ht safe m P e Q ⊑ ht safe m' P e Q.
    Proof.
      rewrite {1}/ht. apply htIntro.
      etransitivity; last by eapply wpWeakenMask.
      eapply and_impl. rewrite ->box_elim. eapply impl_pord; first reflexivity.
      eapply wpMon. intros v. by eapply pvsWeakenMask.
    Qed.

    Lemma htFrame safe m m' P R e Q (*HD: m # m' *):
      ht safe m P e Q ⊑ ht safe (m ∪ m') (P * R) e (lift_bin sc Q (umconst R)).
    Proof.
      etransitivity; first eapply htWeakenMask with (m' := m ∪ m').
      { de_auto_eq. }
      rewrite {1}/ht. apply htIntro.
      transitivity ((wp safe (m ∪ m') e) (lift_bin sc (pvs (m ∪ m') (m ∪ m') <M< Q) (umconst R))); last first.
      { eapply wpMon. intros v. transitivity ((pvs (m ∪ m') (m ∪ m') (Q v) * R)); first reflexivity. (* ARGH! *)
        etransitivity; first eapply pvsFrameRes. reflexivity. }
      etransitivity; last eapply wpFrameRes.
      rewrite -box_conj_star assoc. apply sc_pord; last reflexivity.
      rewrite box_conj_star. apply and_impl, box_elim.
    Qed.
      
    Lemma htSFrame safe m m' P R e Q
          (HD  : m # m')
          (HNv : ~is_value e) :
      ht safe m P e Q ⊑ ht safe (m ∪ m') (P * ▹R) e (lift_bin sc Q (umconst R)).
    Proof.
      rewrite {1}/ht. apply htIntro.
      transitivity ((wp safe (m ∪ m') e) (lift_bin sc (pvs (m ∪ m') (m ∪ m') <M< Q) (umconst R))); last first.
      { eapply wpMon. intros v. transitivity ((pvs (m ∪ m') (m ∪ m') (Q v) * R)); first reflexivity. (* ARGH! *)
        etransitivity; first eapply pvsFrameRes. reflexivity. }
      etransitivity; last (eapply wpSFrameRes; assumption).
      etransitivity; last first.
      { eapply sc_pord; last reflexivity. eapply wpFrameMask. }
      rewrite -box_conj_star assoc. apply sc_pord; last reflexivity.
      rewrite box_conj_star. eapply and_impl. rewrite ->box_elim. eapply impl_pord; first reflexivity.
      eapply wpMon. intros v. eapply pvsWeakenMask. de_auto_eq.
    Qed.

    Lemma htUnsafe {m P e Q} :
      ht true m P e Q ⊑ ht false m P e Q.
    Proof.
      rewrite {1}/ht. apply htIntro. eapply and_impl. rewrite ->box_elim.
      eapply impl_pord; first reflexivity.
      by eapply wpUnsafe.
    Qed.

  End DerivedHTRules.

End IRIS_DERIVED_RULES.

Module IrisDerivedRules (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) (VS_RULES: IRIS_VS_RULES RL C R WP CORE PLOG) (HT_RULES: IRIS_HT_RULES RL C R WP CORE PLOG) : IRIS_DERIVED_RULES RL C R WP CORE PLOG VS_RULES HT_RULES.
  Include IRIS_DERIVED_RULES RL C R WP CORE PLOG VS_RULES HT_RULES.
End IrisDerivedRules.
