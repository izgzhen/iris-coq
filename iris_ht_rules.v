Require Import Ssreflect.ssreflect Ssreflect.ssrfun Omega.
Require Import world_prop core_lang lang iris_core iris_plog.
Require Import ModuRes.RA ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.Agreement ModuRes.DecEnsemble ModuRes.CMRA.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_HT_RULES (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE).
  Export PLOG.

  Local Open Scope lang_scope.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.
  Local Open Scope de_scope.
  
  Section HoareTripleProperties.

    Implicit Types (P : Props) (i : nat) (safe : bool) (m : DecEnsemble nat) (e : expr) (Q φ : vPred) (r : res) (σ : state) (g : RL.res).

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

    (** Bind **)

    (** Quantification in the logic works over nonexpansive maps, so
        we need to show that plugging the value into the postcondition
        and context is nonexpansive. *)
    Program Definition plugCtxWp safe m K φ :=
      n[(fun v : value => wp safe m (fill K v) φ )].
    Next Obligation.
      intros v1 v2 EQv.
      destruct n as [|n]; first by apply: dist_bound.
      hnf in EQv. now rewrite EQv.
    Qed.

    Lemma wpBind φ K e safe m :
      wp safe m e (plugCtxWp safe m K φ) ⊑ wp safe m (fill K e) φ.
    Proof.
      intros w n He.
      revert e w He; induction n using wf_nat_ind; intros; rename H into IH.
      rewrite ->unfold_wp in He; rewrite unfold_wp.
      destruct (is_value_dec e) as [HVal | HNVal]; [clear IH |].
      - intros wf; intros; edestruct He as [HV _]; try eassumption; [].
        clear He HE; specialize (HV HVal); destruct HV as [w' [Hφ HE]].
        (* Fold the goal back into a wp *)
        change (wp safe m (fill K e) φ w' (S (S k))) in Hφ.
        rewrite ->unfold_wp in Hφ. eapply Hφ ; [omega | de_auto_eq | eassumption ].
      - intros wf; intros; edestruct He as [_ [HS [HF HS'] ] ]; try eassumption; [].
        split; [ | split; [| split]; intros].
        + intros HVal; contradiction (HNVal (fill_value HVal)).
        + clear He HF HE; edestruct step_by_value as [K' EQK];
          [eassumption | repeat eexists; eassumption | eassumption |].
          subst K0; rewrite <- fill_comp in HDec; apply fill_inj_r in HDec.
          edestruct HS as [w' [He HE]]; try eassumption; [].
          subst e; clear HStep HS.
          eexists. split; last eassumption.
          rewrite <- fill_comp. apply IH; assumption.
        + clear He HS HE; edestruct fork_by_value as [K' EQK]; try eassumption; [].
          subst K0; rewrite <- fill_comp in HDec; apply fill_inj_r in HDec.
          edestruct HF as [wfk [wret [HWR [HWF HE]]]];
            try eassumption; []; subst e; clear HF.
          do 2 eexists; split; [| split; eassumption].
          rewrite <- fill_comp; apply IH; assumption.
        + clear IH He HS HE HF; specialize (HS' HSafe); clear HSafe.
          destruct HS' as [HV | [HS | HF] ].
          { contradiction. }
          { right; left; destruct HS as [σ' [ei [ei' [K0 [HE HS] ] ] ] ].
            exists σ' ei ei' (K ∘ K0); rewrite -> HE, fill_comp. auto. }
          { right; right; destruct HF as [e' [K0 HE] ].
            exists e' (K ∘ K0). rewrite -> HE, fill_comp. auto. }
    Qed.

    (** Fork **)
    Lemma wpFork safe m R e :
      ▹wp safe de_full e (umconst ⊤) * ▹R ⊑ wp safe m (fork e) (lift_bin sc (eqV (exist _ fork_ret fork_ret_is_value)) (umconst R)).	(* PDS: Why sc not and? RJ: 'cause sc is stronger. *)
    Proof.
      intros w n. destruct n; first (intro; exact:bpred).
      intros [[w1 w2] [EQw [Hwp HLR]]].
      rewrite ->unfold_wp; intros w'; intros.
      split; [| split; intros; [exfalso | split; intros ] ].
      - intros. contradiction (fork_not_value HV).
      - assert (HT := fill_fork HDec); subst K; rewrite ->fill_empty in HDec; subst.
        eapply fork_stuck with (K := ε); [| repeat eexists; eassumption ]; reflexivity.
      - assert (HT := fill_fork HDec); subst K; rewrite ->fill_empty in HDec.
        apply fork_inj in HDec; subst e'. simpl in EQw.
        unfold lt in HLt. simpl in Hwp.
        simpl in HLR; rewrite <- Le.le_n_Sn in HE.
        do 2 eexists. split; last first.
        { split.
          - eapply propsMN, Hwp. omega.
          - eapply wsat_dist, HE; try reflexivity; [].
            apply cmra_op_dist; last reflexivity.
            eapply mono_dist, EQw; omega. }
        rewrite ->fill_empty; rewrite <- (le_S_n _ _ HLt) in HLR.
        eapply wpValue. exists (1 w2, w2). simpl. split_conjs.
        + now rewrite ra_op_unit.
        + reflexivity.
        + eexact HLR.
      - right; right; exists e empty_ctx; rewrite ->fill_empty; reflexivity.
    Grab Existential Variables.
    { exact:fork_ret_is_value. }
    Qed.

    (** Consequence **)
    Lemma wpMon safe m e φ φ':
      φ ⊑ φ' -> wp safe m e φ ⊑ wp safe m e φ'.
    Proof.
      move=>Himpl w n. move: n w e. elim/wf_nat_ind=>n0 IH w0 e Hwp.
      rewrite ->unfold_wp in Hwp. rewrite unfold_wp. intros wf; intros.
      edestruct (Hwp wf) as [Hval [Hstep [Hfork Hsafe]]]; try eassumption; [].
      split; last split; last split; last assumption.
      - move=>Hisval. destruct (Hval Hisval) as [w2 [Hφ Hsat]]=>{Hval Hstep Hfork Hsafe}.
        exists w2. split; last assumption.
        eapply Himpl, Hφ.
      - move=>σ' ei ei' K Hfill Hpstep. destruct (Hstep _ _ _ _ Hfill Hpstep) as [w2 [Hnext Hsat]]=>{Hval Hstep Hfork Hsafe}.
        exists w2. split; last assumption.
        eapply IH; assumption.
      - move=>? ? Heq. destruct (Hfork _ _ Heq) as (wfk & wret & Hnext1 & Hnext2 & Hsat)=>{Hval Hstep Hfork Hsafe}.
        exists wfk wret. split; last (split; assumption).
        eapply IH; assumption.
    Qed.

    Lemma wpPreVS m safe e φ:
      pvs m m (wp safe m e φ) ⊑ wp safe m e φ.
    Proof.
      move=>w0 n0 Hvswp. rewrite ->unfold_wp. intro wf; intros.
      move:Hvswp. case/(_ wf k mf σ HLt _ HE); last move=>w2 [Hwp Hsat].
      { de_auto_eq. }
      rewrite ->unfold_wp in Hwp. move: Hwp.
      case/(_ wf k mf σ _ _ Hsat)/Wrap; last move=>Hcases {HE Hsat}.
      - omega.
      - assumption.
      - apply Hcases.
    Qed.

    Lemma wpPostVS m safe e φ:
      wp safe m e ((pvs m m) <M< φ) ⊑ wp safe m e φ.
    Proof.
      move=>w0 n0. move: n0 w0 e. elim/wf_nat_ind=>n0 IH w0 e Hwpvs.
      rewrite ->unfold_wp. intros wf; intros. rewrite->unfold_wp in Hwpvs.
      edestruct Hwpvs as (Hwpval & Hwpstep & Hwpfork & Hwpsafe); [eassumption|eassumption|eassumption|].
      split; last split; last split; last assumption.
      - move=>Hval. destruct (Hwpval Hval) as (w2 & Hvsφ & Hsat).
        edestruct Hvsφ as (w3 & Hφ & Hsat');[| |eassumption|].
        + omega.
        + de_auto_eq.
        + exists w3. split; assumption.
      - move=>? ? ? ? Hfill Hstep. destruct (Hwpstep _ _ _ _ Hfill Hstep) as (w2 & Hwp & Hsat)=>{Hwpval Hwpstep Hwpfork Hwpsafe}.
        exists w2. split; last assumption.
        eapply IH, Hwp. omega.
      - move=>? ? Hfill. destruct (Hwpfork _ _ Hfill) as (wfk & wret & Hwpret & Hwpk & Hsat)=>{Hwpval Hwpstep Hwpfork Hwpsafe}.
        exists wfk wret. split; last (split; assumption).
        eapply IH, Hwpret. omega.
    Qed.

    Lemma wpACons safe m m' e φ
          (HAt   : atomic e)
          (HSub  : m' ⊑ m) :
      pvs m m' (wp safe m' e ((pvs m' m) <M< φ)) ⊑ wp safe m e φ.
    Proof.
      move=>w0 n0 Hvswpvs. rewrite->unfold_wp. intros wf; intros.
      split; [intros HV; now contradiction (atomic_not_value e) |].
      edestruct (Hvswpvs wf k mf) as (w2 & Hwpvs & Hsat2);[eassumption|de_auto_eq|eassumption|].
      rewrite->unfold_wp in Hwpvs.
      edestruct (Hwpvs wf k mf) as (Hwpval & Hwpstep & Hwpfork & Hwpsafe);[|de_auto_eq|eassumption|]; first omega.
      split; last (split; [intros e' K ?; subst; contradiction (fork_not_atomic K e') |assumption]).
      move=>σ' ei ei' K Hfill Hstep {Hwpval Hwpfork Hwpsafe Hvswpvs Hwpvs Hsat2 HE}.
      destruct (Hwpstep _ _ _ _ Hfill Hstep) as (w3 & Hwpvs & Hsat3)=>{Hwpstep}.
      assert (HNV : ~ is_value ei).
      { intros HV. eapply (values_stuck HV); [symmetry; apply fill_empty | repeat eexists; eassumption]. }
      subst e; assert (HT := atomic_fill HAt HNV); subst K; clear HNV.
      rewrite ->fill_empty in *; rename ei into e. rewrite->unfold_wp in Hwpvs.
      assert (HVal := atomic_step HAt Hstep)=>{Hstep e HAt σ}.
      destruct k.
      { exists w3. split; first exact:wp1. exact I. }
      edestruct Hwpvs as (Hwpval & _); [| |eassumption|]=>{Hwpvs Hsat3}; first omega; first de_auto_eq.
      destruct (Hwpval HVal) as (w4 & Hvs & Hsat4)=>{Hwpval}.
      edestruct (Hvs wf k mf) as (w5 & Hφ & Hsat5); [| |eassumption|]=>{Hvs Hsat4}; first omega; first de_auto_eq.
      exists w5. split; last assumption.
      eapply wpValue. eassumption.
    Qed.

    Lemma wpAConsFork safe m m' e φ
          (HSub  : m' ⊑ m) :
      pvs m m' (wp safe m' (fork e) ((pvs m' m) <M< φ)) ⊑ wp safe m (fork e) φ.
    Proof.
      move=>w0 n0 Hvswpvs. rewrite->unfold_wp. intros wf; intros.
      split; [intros HV; now contradiction (@fork_not_value e) |].
      edestruct (Hvswpvs wf k mf) as (w2 & Hwpvs & Hsat2);[eassumption|de_auto_eq|eassumption|].
      rewrite->unfold_wp in Hwpvs.
      edestruct (Hwpvs wf k mf) as (Hwpval & Hwpstep & Hwpfork & Hwpsafe);[|de_auto_eq|eassumption|]; first omega.
      split.
      { move=>? ? ? ? Hfill Hstep. exfalso. eapply (fork_stuck empty_ctx e).
        - rewrite Hfill. erewrite fill_comp. reflexivity.
        - do 2 eexists; eassumption. }
      split; last assumption.
      move=>ei' K Hfill {Hwpval Hwpstep Hwpsafe Hvswpvs Hwpvs Hsat2 HE}.
      destruct (Hwpfork _ _ Hfill) as (w3 & w3' & Hwpvs & Hwpforked & Hsat3)=>{Hwpfork}.
      move:(fill_fork Hfill) =>Hctx. subst K.
      rewrite fill_empty in Hfill. apply fork_inj in Hfill. subst ei'.
      destruct k.
      { exists w3 w3'. split; first exact:wp1. split; first assumption. exact I. }
      rewrite->unfold_wp in Hwpvs.
      move: Hsat3. rewrite (comm w3) -(assoc) => Hsat3.
      edestruct Hwpvs as (Hwpval & _); [| |eassumption|]=>{Hwpvs Hsat3}; first omega; first de_auto_eq.
      move:  Hwpval. rewrite fill_empty=>Hwpval.
      destruct (Hwpval fork_ret_is_value) as (w4 & Hvs & Hsat4)=>{Hwpval}.
      edestruct (Hvs (w3 · wf) k mf) as (w5 & Hφ & Hsat5); [| |eassumption|]=>{Hvs Hsat4}; first omega; first de_auto_eq.
      exists w3 w5. split; last split.
      - eapply wpValue. eassumption.
      - assumption.
      - rewrite (comm w3) -assoc. assumption.
    Qed.

    (** Framing **)
    Lemma wpFrameMask safe m1 m2 e φ (*HD : m1 # m2*) :
      wp safe m1 e φ ⊑ wp safe (m1 ∪ m2) e φ.
    Proof.
      eapply wpWeakenMask. de_auto_eq.
    Qed.

    Lemma wpFrameRes safe m e φ R:
      (wp safe m e φ) * R ⊑ wp safe m e (lift_bin sc φ (umconst R)).
    Proof.
      move=> w n; revert w e φ R; induction n using wf_nat_ind; rename H into HInd; intros w e φ R HW.
      destruct n; first exact:bpred.
      rewrite unfold_wp; rewrite ->unfold_wp in HW; intros wf; intros.
      destruct HW as [[w1 w2] [EQw [Hwp HR]]]. simpl in EQw. pose (wf' := w2 · wf).
      edestruct Hwp with (wf:=wf') as [HV [HS [HF HS'] ] ]; try eassumption.
      { eapply wsat_dist, HE; first reflexivity; last reflexivity.
        simpl morph. rewrite /wf' assoc. apply cmra_op_dist; last reflexivity.
        eapply mono_dist, EQw. omega. }
      clear Hwp HE; split; [intros HVal; clear HS HF HInd | split; [intros; clear HV HF | split; [intros; clear HV HS | intros; clear HV HS HF] ] ].
      - specialize (HV HVal); destruct HV as [w'' [Hφ HE]].
        eexists; split.
        + exists (w'', w2). split; first (simpl; reflexivity).
          split; first assumption.
          eapply propsMN, HR; omega.
        + eapply wsat_equiv, HE; try reflexivity.
          now rewrite /wf' assoc.
      - edestruct HS as [w'' [HW HE]]; try eassumption; []; clear HS.
        eexists; split.
        + eapply HInd; [omega|].
          exists (w'', w2). split; first (simpl; reflexivity). simpl.
          split; first by eapply HW.
          eapply propsMN, HR; omega.
        + eapply wsat_equiv, HE; try reflexivity.
          * rewrite assoc. reflexivity.
      - destruct (HF _ _ HDec) as [wfk [wret [HWR [HWF HE]]]]; clear HF.
        do 2 eexists.
        split; last split.
        + eapply HInd; first omega.
          exists (wret, w2). simpl. split; first reflexivity.
          split; first assumption.
          eapply propsMN, HR; omega.
        + eassumption.
        + eapply wsat_equiv, HE; try reflexivity.
          rewrite /wf'. now rewrite !assoc.
      - auto.
    Qed.

    Lemma wpAFrameRes safe m R e φ
          (HNv : ~is_value e) :
      (wp safe m e φ) * ▹R ⊑ wp safe m e (lift_bin sc φ (umconst R)).
    Proof.
      intros w n. destruct n; first (intro; exact:bpred).
      move=>[[w1 w2] [/= EQr [Hwp HLR]]].
      rewrite->unfold_wp; intros wf; intros.
      rewrite ->unfold_wp in Hwp. 
      edestruct (Hwp (w2 · wf) k mf) as [_ [HeS [HeF Hsafe]]]; [omega|assumption| |].
      { eapply wsat_dist, HE; first reflexivity; last reflexivity.
        rewrite assoc. apply cmra_op_dist; last reflexivity.
        eapply mono_dist, EQr. omega. }
      split; [intros; exfalso | split; intros; [| split; intros  ] ].
      - contradiction.
      - edestruct HeS as [w'' [He' HE']]; try eassumption; [].
        clear HE Hwp HeS HeF; rewrite ->assoc in HE'.
        exists (w'' · w2). split; [| eassumption]. subst e.
        eapply wpFrameRes. exists (w'', w2).
        split; first (apply sp_eq_iff; reflexivity).
        split; first assumption.
        eapply dpred, HLR. omega.
      - edestruct HeF as [wfk [wret [He' [Ht' HE']]]]; try eassumption; [].
        clear HE Hwp HeS HeF; rewrite ->assoc in HE'. subst e.
        exists wfk (wret · w2). split; [| split; rewrite ->?assoc; eassumption].
        eapply wpFrameRes. exists (wret, w2).
        split; first (apply sp_eq_iff; reflexivity).
        split; first assumption.
        eapply dpred, HLR. omega.
      - now auto.
    Qed.

    (* Unsafe and safe weakest-pre *)
    Lemma wpUnsafe {m e φ} : wp true m e φ ⊑ wp false m e φ.
    Proof.
      move=> w n. move: n w e φ m; elim/wf_nat_ind. move=> n IH w e φ m He.
      rewrite unfold_wp; move=> wf k mf σ HLt HD HW.
      move/(_ _ HLt): IH => IH.
      move/unfold_wp/(_ _ _ _ _ HLt HD HW): He => [HV [HS [HF _] ] ] {HLt HD HW}.
      split; [done | clear HV; split; [clear HF | split; [clear HS | done] ] ].
      - move=> σ' ei ei' K HK Hs.
        move/(_ _ _ _ _ HK Hs): HS => [w'' [He' Hw']] {Hs HK}.
        exists w''. split; [ by apply:IH | done].
      - move=> e' K HK.
        move/(_ _ _ HK): HF => [wfk [wret [Hk [He' HW']]]]   {HK}.
        exists wfk wret. split; [exact: IH | split; [exact: IH | done] ].
    Qed.

  End HoareTripleProperties.

  Global Opaque pvs.
  Global Opaque wpF.

End IRIS_HT_RULES.

Module IrisHTRules (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) : IRIS_HT_RULES RL C R WP CORE PLOG.
  Include IRIS_HT_RULES RL C R WP CORE PLOG.
End IrisHTRules.
