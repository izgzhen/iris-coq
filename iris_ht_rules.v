Require Import Ssreflect.ssreflect Ssreflect.ssrfun Omega.
Require Import world_prop core_lang lang iris_core iris_plog.
Require Import ModuRes.RA ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.Agreement ModuRes.DecEnsemble ModuRes.CMRA.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_HT_RULES (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE).
  Export PLOG.

  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.
  Local Open Scope de_scope.
  
  Section HoareTripleProperties.

    Implicit Types (P : Props) (i : nat) (safe : bool) (m : DecEnsemble nat) (e : expr) (Q φ : vPred) (r : res) (σ : state) (g : RL.res).

    Lemma wpMon safe m e φ φ':
      φ ⊑ φ' -> wp safe m e φ ⊑ wp safe m e φ'.
    Proof.
      move=>Himpl w n. move: n w e. elim/wf_nat_ind=>n0 IH w0 e.
      rewrite ->unfold_wp. intros [HV Hwp]. split; intros.
      { eapply Himpl, HV. }
      edestruct (Hwp wf) as [Hstep Hsafe]; try eassumption; [].
      split; last assumption.
      move=>σ' ei' ef Hpstep. destruct (Hstep _ _ _ Hpstep) as (w2 & w2f & Hnext & Hnextf & Hsat)=>{Hstep Hsafe}.
      exists w2 w2f. split; last (split; last assumption).
      - eapply IH; assumption.
      - assumption.
    Qed.

    (** Ret **)
    Program Definition eqV v : vPred :=
      n[(fun v' : value => v === v')].
    Next Obligation.
      intros v1 v2 EQv. apply intEq_dist; reflexivity || assumption.
    Qed.

    Lemma wpRet e (HV : is_value e) safe m :
      valid (wp safe m e (eqV (exist _ e HV))).
    Proof.
      intros w n. eapply wpValue.
      destruct n; first exact:bpred.
      simpl. reflexivity.
    Grab Existential Variables.
    { assumption. }  
    Qed.

    (** Consequence **)
    Lemma wpPreVS m safe e φ:
      pvs m m (wp safe m e φ) ⊑ wp safe m e (pvs m m <M< φ).
    Proof.
      move=>w0 n0 Hvswp. rewrite ->unfold_wp. split; intros.
      { rewrite ->wpValue in Hvswp. eapply spredNE, Hvswp. eapply dist_refl. simpl. reflexivity. }
      move:Hvswp. case/(_ wf k mf σ HLt _ HE); last move=>w2 [Hwp Hsat].
      { de_auto_eq. }
      assert (Hwp': wp safe m e (pvs m m <M< φ) w2 (S (S k))).
      { eapply wpMon, Hwp. intros v. eapply pvsEnt. }
      clear Hwp. rewrite ->unfold_wp in Hwp'. destruct Hwp' as [_ Hwp]. move: Hwp.
      case/(_ wf k mf σ _ _ Hsat)/Wrap; last move=>Hcases {HE Hsat}.
      - omega.
      - assumption.
      - apply Hcases.
    Qed.

    Lemma wpACons safe m m' e φ
          (HAt   : atomic e)
          (HSub  : m' ⊑ m) :
      pvs m m' (wp safe m' e ((pvs m' m) <M< φ)) ⊑ wp safe m e (pvs m m <M< φ).
    Proof.
      move=>w0 n0 Hvswpvs. rewrite->unfold_wp. split; intros.
      { contradiction (atomic_not_value e). }
      edestruct (Hvswpvs wf k mf) as (w2 & Hwpvs & Hsat2);[eassumption|de_auto_eq|eassumption|].
      rewrite->unfold_wp in Hwpvs. destruct Hwpvs as [_ Hwpvs].
      edestruct (Hwpvs wf k mf) as (Hwpstep & Hwpsafe);[|de_auto_eq|eassumption|]; first omega.
      split; last assumption.
      move=>e' σ' ef' Hstep {Hwpsafe Hvswpvs Hwpvs Hsat2 HE}.
      destruct (Hwpstep _ _ _ Hstep) as (w3 & w3f & Hwpvs & Hwpf & Hsat3)=>{Hwpstep}.
      assert (HVal := atomic_step _ HAt Hstep)=>{Hstep e HAt σ}.
      edestruct Hwpvs as (Hvs & _)=>{Hwpvs}. specialize (Hvs HVal).
      destruct k.
      { exists w3 w3f. split; last (split; [assumption|exact I]). rewrite wpValue. intro; intros.
        exfalso. omega. }
      edestruct (Hvs (w3f · wf) k mf) as (w4 & Hφ & Hsat4); first omega; first de_auto_eq.
      { eapply spredNE, Hsat3. eapply dist_refl, wsat_equiv; first reflexivity.
        rewrite assoc (comm _ w3). reflexivity. }
      exists w4 w3f. split; last (split; first assumption).
      - rewrite wpValue. eapply pvsEnt. eassumption.
      - eapply spredNE, Hsat4. eapply dist_refl, wsat_equiv; first reflexivity.
        rewrite assoc (comm _ w4). reflexivity.
    Grab Existential Variables.
    { assumption. }
    Qed.

    (** Bind - in general **)
    Section Bind.
      Definition IsFill (fill: expr -> expr): Prop :=
        (forall e, is_value (fill e) -> is_value e) /\
        (forall e1 σ1 e2 σ2 ef, prim_step (e1, σ1) (e2, σ2) ef -> prim_step (fill e1, σ1) (fill e2, σ2) ef) /\
        (forall e1 σ1 e2 σ2 ef, ~is_value e1 -> prim_step (fill e1, σ1) (e2, σ2) ef ->
                                exists e2', e2 = fill e2' /\ prim_step (e1, σ1) (e2', σ2) ef).

      Program Definition plug_bind (fill: expr -> expr) safe m φ :=
        n[(fun v : value => wp safe m (fill v) φ )].
      Next Obligation.
        intros v1 v2 EQv.
        destruct n as [|n]; first by apply: dist_bound.
        hnf in EQv. now rewrite EQv.
      Qed.

      Lemma wpBind (fill: expr -> expr) φ e safe m (HFill: IsFill fill):
        wp safe m e (plug_bind fill safe m φ) ⊑ wp safe m (fill e) φ.
      Proof.
        intros w n He. destruct HFill as (HFval & HFstep & HFfstep).
        revert e w He; induction n using wf_nat_ind; intros; rename H into IH.
        (* We need to actually decide whether e is a value, to establish safety in the case that
           it is not. *)
        destruct (is_value_dec e) as [HVal | HNVal]; [clear IH |].
        - eapply (wpValue _ HVal) in He. exact:He.
        - rewrite ->unfold_wp in He; rewrite unfold_wp. split; intros.
          { exfalso. apply HNVal, HFval, HV. }
          edestruct He as [_ He']; try eassumption; []; clear He.
          edestruct He' as [HS HSf]; try eassumption; []; clear He' HE HD.
          split; last first.
          { intros Heq. destruct (HSf Heq) as [?|[σ' [e' [ef Hstep]]]]; first contradiction.
            right. do 3 eexists. eapply HFstep. eassumption. }
          intros. edestruct (HFfstep e σ e' σ' ef) as (e'' & Heq' & Hstep'); first done; first done.
          destruct (HS _ _ _ Hstep') as (wret & wfk & Hret & Hfk & HE). subst e'.
          exists wret wfk. split; last tauto.
          clear Hfk HE. eapply IH; assumption.
      Qed.
    End Bind.

    (** Mask weakening **)
    Lemma wpWeakenMask safe m1 m2 e φ (HD : m1 ⊑ m2) :
      wp safe m1 e φ ⊑ wp safe m2 e φ.
    Proof.
      intros w n; revert w e φ; induction n using wf_nat_ind; rename H into HInd; intros w e φ.
      rewrite unfold_wp. intros [HV HW]. split; intros; first done.
      edestruct HW with (mf := mf ∪ (m2 \ m1)) as [HS HSf]; try eassumption;
      [| eapply wsat_equiv, HE; try reflexivity; de_auto_eq |]; first de_auto_eq.
      clear HW HE; split; [intros; clear HV | intros; clear HV HS].
      - destruct (HS _ _ _ HStep) as [wret [wfk [HWR [HWF HE]]]]; clear HS.
        do 2 eexists. split; [eapply HInd; eassumption|].
        split; first eassumption.
        eapply wsat_equiv, HE; try reflexivity; clear; de_auto_eq.
      - now auto.
    Qed.

    (** Framing **)
    Lemma wpFrameRes safe m e φ R:
      (wp safe m e φ) * R ⊑ wp safe m e (lift_bin sc φ (umconst R)).
    Proof.
      move=> w n; revert w e φ R; induction n using wf_nat_ind; rename H into HInd; intros w e φ R HW.
      destruct n; first exact:bpred.
      rewrite unfold_wp; rewrite ->unfold_wp in HW.
      destruct HW as [[w1 w2] [EQw [[HV Hwp] HR]]].
      split; intros.
      { exists (w1, w2). split; first assumption. split; last exact HR. apply HV. }
      simpl in EQw. pose (wf' := w2 · wf).
      edestruct Hwp with (wf:=wf') as [HS HSf]; try eassumption; [|].
      { eapply wsat_dist, HE; first reflexivity; last reflexivity.
        simpl morph. rewrite /wf' assoc. apply cmra_op_dist; last reflexivity.
        eapply mono_dist, EQw. omega. }
      clear Hwp HE; split; last by auto. clear HSf HV. intros.
      destruct (HS _ _ _ HStep) as [wret [wfk [HWR [HWF HE]]]]; clear HS.
      do 2 eexists. split; last split.
      - eapply HInd; first omega.
        exists (wret, w2). simpl. split; first reflexivity.
        split; first assumption.
        eapply propsMN, HR; omega.
      - eassumption.
      - eapply wsat_equiv, HE; try reflexivity.
        rewrite /wf'. now rewrite !assoc.
    Qed.

    Lemma wpSFrameRes safe m R e φ
          (HNv : ~is_value e) :
      (wp safe m e φ) * ▹R ⊑ wp safe m e (lift_bin sc φ (umconst R)).
    Proof.
      intros w n. destruct n; first (intro; exact:bpred).
      move=>[[w1 w2] [/= EQr [Hwp HLR]]].
      rewrite->unfold_wp; rewrite ->unfold_wp in Hwp.
      split; intros; first by contradiction.
      destruct Hwp as [_ Hwp].
      edestruct (Hwp (w2 · wf) k mf) as [HS HSf]; [omega|assumption| |].
      { eapply wsat_dist, HE; first reflexivity; last reflexivity.
        rewrite assoc. apply cmra_op_dist; last reflexivity.
        eapply mono_dist, EQr. omega. }
      split; last by auto. intros.
      edestruct (HS _ _ _ HStep) as [wret [wfk [He' [Ht' HE']]]]; try eassumption; [].
      clear HE Hwp HS; rewrite ->assoc in HE'.
      exists (wret · w2) wfk. split; [| split; rewrite ->?assoc; eassumption].
      eapply wpFrameRes. exists (wret, w2).
      split; first (apply sp_eq_iff; reflexivity).
      split; first assumption.
      eapply dpred, HLR. omega.
    Qed.

    (* Unsafe and safe weakest-pre *)
    Lemma wpUnsafe {m e φ} : wp true m e φ ⊑ wp false m e φ.
    Proof.
      move=> w n. move: n w e φ m; elim/wf_nat_ind. move=> n IH w e φ m.
      rewrite unfold_wp. move=>[HV HW]. rewrite unfold_wp. split; intros; first by auto.
      move/(_ _ HLt): IH => IH.
      move/(_ _ _ _ _ HLt HD HE): HW => [HS _] {HLt HD HE HV}.
      split; [ | done].
      - move=> e' σ' ef HStep.
        move/(_ _ _ _ HStep): HS => [wret [wfk [Hk [He' HW']]]] {HStep}.
        exists wret wfk. split; [exact: IH | split; [case:ef He'=>[ef|]; [exact: IH|done] | done] ].
    Qed.

  End HoareTripleProperties.

  Global Opaque pvs.
  Global Opaque wpF.

End IRIS_HT_RULES.

Module IrisHTRules (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) : IRIS_HT_RULES RL C R WP CORE PLOG.
  Include IRIS_HT_RULES RL C R WP CORE PLOG.
End IrisHTRules.
