Require Import Ssreflect.ssreflect Ssreflect.ssrfun Omega.
Require Import world_prop core_lang lang masks iris_core iris_plog.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_HT_RULES (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE).
  Export PLOG.

  Local Open Scope lang_scope.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.
  
  Section HoareTripleProperties.

    Existing Instance LP_isval.

    Implicit Types (P : Props) (i : nat) (safe : bool) (m : mask) (e : expr) (Q φ : vPred) (r : res).

    (** Ret **)
    Program Definition eqV v : vPred :=
      n[(fun v' : value => v === v')].
    Next Obligation.
      intros v1 v2 EQv w m r HLt; destruct n as [| n]; [now inversion HLt | simpl in *].
      split; congruence.
    Qed.

    Lemma wpRet e (HV : is_value e) safe m :
      valid (wp safe m e (eqV (exist _ e HV))).
    Proof.
      intros w n r'.
      rewrite unfold_wp; intros w'; intros; split; [| split; [| split] ]; intros.
      - exists w' r'; split; [reflexivity | split; [| assumption] ].
        simpl; reflexivity.
      - contradiction (values_stuck HV HDec).
        repeat eexists; eassumption.
      - subst e; assert (HT := fill_value HV); subst K.
        revert HV; rewrite fill_empty; intros.
        contradiction (fork_not_value _ HV).
      - unfold safeExpr. auto.
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
      simpl in EQv. rewrite EQv. reflexivity.
    Qed.

    Lemma wpBind φ K e safe m :
      wp safe m e (plugCtxWp safe m K φ) ⊑ wp safe m (fill K e) φ.
    Proof.
      intros w n r He.
      revert e w r He; induction n using wf_nat_ind; intros; rename H into IH.
      rewrite ->unfold_wp in He; rewrite unfold_wp.
      destruct (is_value_dec e) as [HVal | HNVal]; [clear IH |].
      - intros w'; intros; edestruct He as [HV _]; try eassumption; [].
        clear He HE; specialize (HV HVal); destruct HV as [w'' [r' [HSw' [Hφ HE] ] ] ].
        (* Fold the goal back into a wp *)
        setoid_rewrite HSw'.
        assert (HT : wp safe m (fill K e) φ w'' (S k) r');
          [| rewrite ->unfold_wp in HT; eapply HT; [reflexivity | unfold lt; reflexivity | eassumption | eassumption] ].
        exact Hφ.
      - intros w'; intros; edestruct He as [_ [HS [HF HS'] ] ]; try eassumption; [].
        split; [intros HVal; contradiction HNVal; assert (HT := fill_value HVal);
                subst K; rewrite fill_empty in HVal; assumption | split; [| split]; intros].
        + clear He HF HE; edestruct step_by_value as [K' EQK];
          [eassumption | repeat eexists; eassumption | eassumption |].
          subst K0; rewrite <- fill_comp in HDec; apply fill_inj2 in HDec.
          edestruct HS as [w'' [r' [HSw' [He HE] ] ] ]; try eassumption; [].
          subst e; clear HStep HS.
          do 2 eexists; split; [eassumption | split; [| eassumption] ].
          rewrite <- fill_comp. apply IH; assumption.
        + clear He HS HE; edestruct fork_by_value as [K' EQK]; try eassumption; [].
          subst K0; rewrite <- fill_comp in HDec; apply fill_inj2 in HDec.
          edestruct HF as [w'' [rfk [rret [HSw' [HWR [HWF HE] ] ] ] ] ];
            try eassumption; []; subst e; clear HF.
          do 3 eexists; split; [eassumption | split; [| split; eassumption] ].
          rewrite <- fill_comp; apply IH; assumption.
        + clear IH He HS HE HF; specialize (HS' HSafe); clear HSafe.
          destruct HS' as [HV | [HS | HF] ].
          { contradiction. }
          { right; left; destruct HS as [σ' [ei [ei' [K0 [HE HS] ] ] ] ].
            exists σ' ei ei' (K ∘ K0); rewrite -> HE, fill_comp. auto. }
          { right; right; destruct HF as [e' [K0 HE] ].
            exists e' (K ∘ K0). rewrite -> HE, fill_comp. auto. }
    Qed.

    (** Consequence **)
    Lemma wpImpl safe m e φ φ':
      (□all (lift_bin BI.impl φ φ')) ∧ wp safe m e φ ⊑ wp safe m e φ'.
    Proof.
      move=>w n. move: n w e. elim/wf_nat_ind=>n0 IH w0 e r0 [Himpl Hwp].
      rewrite ->unfold_wp in Hwp. rewrite unfold_wp. intros w1; intros.
      edestruct Hwp as [Hval [Hstep [Hfork Hsafe]]]; [eassumption|eassumption|eassumption|eassumption|].
      split; last split; last split.
      - move=>Hisval. destruct (Hval Hisval) as [w2 [r2 [Hw01 [Hφ Hsat]]]]=>{Hval Hstep Hfork Hsafe}.
        exists w2 r2. split; first assumption. split; last assumption.
        eapply (Himpl (exist _ e Hisval)), Hφ.
        + etransitivity; eassumption.
        + omega.
        + by apply: unit_min.
      - move=>σ' ei ei' K Hfill Hpstep. destruct (Hstep _ _ _ _ Hfill Hpstep) as [w2 [r2 [Hw12 [Hnext Hsat]]]]=>{Hval Hstep Hfork Hsafe}.
        exists w2 r2. split; first assumption. split; last assumption.
        eapply IH; last split; last eassumption.
        + omega.
        + eapply (propsM (r:=1)); last apply: Himpl; [etransitivity; eassumption|omega|by apply: unit_min].
      - move=>? ? Heq. destruct (Hfork _ _ Heq) as (w2 & rfk & rret & Hw12 & Hnext1 & Hnext2 & Hsat)=>{Hval Hstep Hfork Hsafe}.
        exists w2 rfk rret. split; first assumption. split; last (split; assumption).
        eapply IH; last split; last eassumption.
        + omega.
        + eapply (propsM (r:=1)); last apply: Himpl; [etransitivity; eassumption|omega|by apply: unit_min].
      - assumption.
    Qed.

    Lemma wpPreVS m safe e φ:
      pvs m m (wp safe m e φ) ⊑ wp safe m e φ.
    Proof.
      rewrite -> unfold_wp.
      move=>w0 n0 r0 Hvswp w1. intros.
      move:Hvswp. case/(_ w1 rf mf σ k HSw HLt _ HE); last move=>w2 [r2 [Hw12 [Hwp Hsat]]].
      { intros j. clear -HD. specialize (HD j). unfold mcup. tauto. }
      move: Hwp. case/(_ w2 k rf mf σ _ _ _ Hsat)/Wrap; last move=>[Hval [Hstep [Hfork Hsafe]]] {HE Hsat}.
      - reflexivity.
      - omega.
      - assumption.
      - split; last split; last split; last assumption.
        + move=>Hisval. destruct (Hval Hisval) as (w3 & r3 & Hw23 & Hrem).
          exists w3 r3. split; first (etransitivity; eassumption). assumption.
        + move=> ? ? ? ? Hfill Hpstep. destruct (Hstep _ _ _ _ Hfill Hpstep) as (w3 & r3 & Hw23 & Hrem).
          exists w3 r3. split; last assumption. etransitivity; eassumption.
        + move=> ? ? Hfill. destruct (Hfork _ _ Hfill) as (w3 & rfk & rret & Hw23 &Hrem).
          do 3 eexists. split; last eassumption. etransitivity; eassumption.
    Qed.

    Lemma wpPostVS m safe e φ:
      wp safe m e ((pvs m m) <M< φ) ⊑ wp safe m e φ.
    Proof.
      move=>w0 n0. move: n0 w0 e. elim/wf_nat_ind=>n0 IH w0 e r0 Hwpvs.
      rewrite ->unfold_wp. intros w1; intros. rewrite->unfold_wp in Hwpvs.
      edestruct Hwpvs as (Hwpval & Hwpstep & Hwpfork & Hwpsafe); [eassumption|eassumption|eassumption|eassumption|].
      split; last split; last split; last assumption.
      - move=>Hval. destruct (Hwpval Hval) as (w2 & r2 & Hw12 & Hvsφ & Hsat).
        edestruct Hvsφ as (w3 & r3 & Hw23 & Hφ & Hsat');[| | |eassumption|].
        + reflexivity.
        + omega.
        + clear-HD. intros j. specialize (HD j). unfold mcup. tauto.
        + exists w3 r3. split; first (etransitivity;eassumption). split; assumption.
      - move=>? ? ? ? Hfill Hstep. destruct (Hwpstep _ _ _ _ Hfill Hstep) as (w2 & r2 & Hw12 & Hwp & Hsat)=>{Hwpval Hwpstep Hwpfork Hwpsafe}.
        exists w2 r2. split; first assumption. split; last assumption.
        eapply IH, Hwp. omega.
      - move=>? ? Hfill. destruct (Hwpfork _ _ Hfill) as (w2 & rfk & rret & Hw12 & Hwpret & Hwpk & Hsat)=>{Hwpval Hwpstep Hwpfork Hwpsafe}.
        exists w2 rfk rret. split; first assumption. split; last (split; assumption).
        eapply IH, Hwpret. omega.
    Qed.

    Lemma wpACons safe m m' e φ
          (HAt   : atomic e)
          (HSub  : m' ⊆ m) :
      pvs m m' (wp safe m' e ((pvs m' m) <M< φ)) ⊑ wp safe m e φ.
    Proof.
      move=>w0 n0 r0 Hvswpvs. rewrite->unfold_wp. intros w1; intros.
      split; [intros HV; contradiction (atomic_not_value e) |].
      edestruct Hvswpvs as (w2 & r2 & Hw12 & Hwpvs & Hsat2);[eassumption|eassumption| |eassumption|].
      { clear-HD HSub. intros j. specialize (HD j). specialize (HSub j). unfold mcup. tauto. }
      rewrite->unfold_wp in Hwpvs.
      edestruct Hwpvs as (Hwpval & Hwpstep & Hwpfork & Hwpsafe);[reflexivity| | |eassumption|]; first omega.
      { clear-HD HSub. intros j. specialize (HD j). specialize (HSub j). tauto. }
      split; last (split; [intros e' K ?; subst; contradiction (fork_not_atomic K e') |assumption]).
      move=>σ' ei ei' K Hfill Hstep {Hwpval Hwpfork Hwpsafe Hvswpvs Hwpvs Hsat2 HE}.
      destruct k as [| k]; [exists w1 r0; split; [reflexivity | split; [apply wpO | exact I] ] |].
      destruct (Hwpstep _ _ _ _ Hfill Hstep) as (w3 & r3 & Hw23 & Hwpvs & Hsat3)=>{Hwpstep}.
      assert (HNV : ~ is_value ei)
          by (intros HV; eapply (values_stuck HV); [symmetry; apply fill_empty | repeat eexists; eassumption]).
      subst e; assert (HT := atomic_fill HAt HNV); subst K; clear HNV.
      rewrite ->fill_empty in *; rename ei into e. rewrite->unfold_wp in Hwpvs.
      assert (HVal := atomic_step HAt Hstep)=>{Hstep e HAt σ}.
      edestruct Hwpvs as (Hwpval & _); [reflexivity| | |eassumption|]=>{Hwpvs Hsat3}; first omega.
      { clear-HD HSub. intros j. specialize (HD j). specialize (HSub j). tauto. }
      destruct (Hwpval HVal) as (w4 & r4 & Hw34 & Hvs & Hsat4)=>{Hwpval}.
      edestruct Hvs as (w5 & r5 & Hw45 & Hφ & Hsat5); [reflexivity| | |eassumption|]=>{Hvs Hsat4}; first omega.
      { clear-HD HSub. intros j. specialize (HD j). specialize (HSub j). unfold mcup. tauto. }
      exists w5 r5.
      split.
      { rewrite ->Hw12, Hw23, Hw34. assumption. }
      split; last assumption.
      rewrite unfold_wp. move=>w6 n6 rf6 mf6 σ6 Hw56 Hn56 Hmf6 Hsat6.
      split; last split; last split.
      - do 2 eexists; split; [reflexivity | split; [| eassumption] ].
        assert (Heq: ((exist _ ei' HVal):value) == (exist _ ei' HV)) by reflexivity. (* TODO can we do without this? *)
        rewrite -Heq. eapply propsMWN, Hφ.
        + assumption.
        + omega.
      - intros. exfalso. eapply values_stuck; [.. | repeat eexists]; eassumption.
      - intros. exfalso. clear - HDec HVal; subst; assert (HT := fill_value HVal); subst.
        rewrite ->fill_empty in HVal; now apply fork_not_value in HVal.
      - intros; left; assumption.
    Qed.

    (** Framing **)
    Lemma wpFrameMask safe m1 m2 e φ (HD : m1 # m2) :
      wp safe m1 e φ ⊑ wp safe (m1 ∪ m2) e φ.
    Proof.
      intros w n; revert w e φ; induction n using wf_nat_ind; rename H into HInd; intros w e φ r HW.
      rewrite unfold_wp; rewrite ->unfold_wp in HW; intros w'; intros.
      edestruct HW with (mf := mf ∪ m2) as [HV [HS [HF HS'] ] ]; try eassumption;
      [| eapply wsat_equiv, HE; try reflexivity; [] |].
      { intros j [ [Hmf | Hm'] Hm]; [unfold mcup in HD0; apply (HD0 j) | apply (HD j) ]; tauto.
      }
      { clear; intros j; unfold mcup; tauto.
      }
      clear HW HE; split; [intros HVal; clear HS HF HInd | split; [intros; clear HV HF | split; [intros; clear HV HS | intros; clear HV HS HF] ] ].
      - specialize (HV HVal); destruct HV as [w'' [r' [HSW [Hφ HE] ] ] ].
        do 2 eexists; split; [eassumption | split; [eassumption |] ].
        eapply wsat_equiv, HE; try reflexivity; [].
        intros j; unfold mcup; tauto.
      - edestruct HS as [w'' [r' [HSW [HW HE] ] ] ]; try eassumption; []; clear HS.
        do 2 eexists; split; [eassumption | split; [eapply HInd, HW; assumption |] ].
        eapply wsat_equiv, HE; try reflexivity; [].
        intros j; unfold mcup; tauto.
      - destruct (HF _ _ HDec) as [w'' [rfk [rret [HSW [HWR [HWF HE] ] ] ] ] ]; clear HF.
        do 3 eexists; split; [eassumption |].
        do 2 (split; [apply HInd; eassumption |]).
        eapply wsat_equiv, HE; try reflexivity; [].
        intros j; unfold mcup; tauto.
      - auto.
    Qed.

    Lemma wpFrameRes safe m e φ R:
      (wp safe m e φ) * R ⊑ wp safe m e (lift_bin sc φ (umconst R)).
    Proof.
      move=> w n; revert w e φ R; induction n using wf_nat_ind; rename H into HInd; intros w e φ R r HW.
      rewrite unfold_wp; rewrite ->unfold_wp in HW; intros w'; intros.
      destruct HW as [r1 [r2 [EQr [Hwp HR]]]]. pose (rf' := r2 · rf).
      edestruct Hwp with (rf:=rf') as [HV [HS [HF HS'] ] ]; try eassumption.
      { eapply wsat_equiv, HE; last reflexivity.
        - clear; intros j; unfold mcup; tauto.
        - unfold rf'. rewrite -EQr assoc. reflexivity. }
      subst rf'.
      clear Hwp HE; split; [intros HVal; clear HS HF HInd | split; [intros; clear HV HF | split; [intros; clear HV HS | intros; clear HV HS HF] ] ].
      - specialize (HV HVal); destruct HV as [w'' [r' [HSW [Hφ HE] ] ] ].
        do 2 eexists; split; [eassumption | split ].
        + exists r' r2. split; first reflexivity.
          split; first assumption.
          eapply propsMWN, HR; [etransitivity; eassumption|omega].
        + eapply wsat_equiv, HE; try reflexivity.
          * rewrite assoc. reflexivity.
      - edestruct HS as [w'' [r' [HSW [HW HE] ] ] ]; try eassumption; []; clear HS.
        do 2 eexists; split; [eassumption | split ].
        + eapply HInd; [omega|].
          exists r' r2. split; first reflexivity.
          split; first by eapply HW.
          eapply propsMWN, HR; [etransitivity; eassumption|omega].
        + eapply wsat_equiv, HE; try reflexivity.
          * rewrite assoc. reflexivity.
      - destruct (HF _ _ HDec) as [w'' [rfk [rret [HSW [HWR [HWF HE] ] ] ] ] ]; clear HF.
        do 3 eexists; split; [eassumption |].
        split; last split.
        + eapply HInd; first omega.
          exists rret r2. split; first reflexivity.
          split; first assumption.
          eapply propsMWN, HR; [etransitivity; eassumption|omega].
        + assert (Heq: umconst ⊤ == lift_bin sc (umconst ⊤) (umconst ⊤)).
          { clear. move=>v. change ((⊤:Props) == ⊤*⊤). rewrite sc_top_unit. reflexivity. }
          rewrite Heq=>{Heq}. eapply HInd; first omega.
          exists rfk ra_unit. split; first reflexivity.
          split; first assumption.
          exact I.
        + eapply wsat_equiv, HE; try reflexivity.
          * rewrite ->ra_op_unit2, !assoc. reflexivity.
      - auto.
    Qed.

    Lemma wpAFrameRes safe m R e φ
          (HAt : atomic e) :
      (wp safe m e φ) * ▹R ⊑ wp safe m e (lift_bin sc φ (umconst R)).
    Proof.
      intros w n r [r1 [r2 [EQr [Hwp HLR]]]].
      rewrite->unfold_wp; intros w'; intros.
      split; [intros; exfalso | split; intros; [| split; intros; [exfalso| ] ] ].
      - contradiction (atomic_not_value e).
      - destruct k as [| k];
        [exists w' r; split; [reflexivity | split; [apply wpO | exact I] ] |].
        rewrite ->unfold_wp in Hwp. rewrite <- EQr, <- assoc in HE.
        edestruct Hwp as [_ [HeS _] ]; try eassumption; [].
        edestruct HeS as [w'' [r1' [HSw' [He' HE'] ] ] ]; try eassumption; [].
        clear HE Hwp HeS; rewrite ->assoc in HE'.
        exists w'' (r1' · r2).
        split; [eassumption | split; [| eassumption] ].
        assert (HNV : ~ is_value ei)
          by (intros HV; eapply (values_stuck HV); [symmetry; apply fill_empty | repeat eexists; eassumption]).
        subst e; assert (HT := atomic_fill HAt HNV); subst K; clear HNV.
        rewrite ->fill_empty in *.
        unfold lt in HLt; rewrite <- HLt, HSw, HSw' in HLR; simpl in HLR.
        assert (HVal := atomic_step HAt HStep).
        clear - He' HVal HLR; rename w'' into w; rewrite ->unfold_wp; intros w'; intros.
        split; [intros HV; clear HVal | split; intros; [exfalso| split; intros; [exfalso |] ] ].
        + rewrite ->unfold_wp in He'. rewrite <-assoc in HE.
          edestruct He' as [HVal _]; try eassumption; [].
          specialize (HVal HV); destruct HVal as [w'' [r1'' [HSw' [Hφ HE'] ] ] ].
          rewrite ->assoc in HE'.
          exists w'' (r1'' · r2).
          split; [eassumption | split; [| eassumption] ].
          exists r1'' r2; split; [reflexivity | split; [assumption |] ].
          unfold lt in HLt; rewrite <- HLt, HSw, HSw' in HLR; apply HLR.
        + eapply values_stuck; [.. | repeat eexists]; eassumption.
        + subst; clear -HVal.
          assert (HT := fill_value HVal); subst K; rewrite ->fill_empty in HVal.
          contradiction (fork_not_value e').
        + unfold safeExpr. now auto.
      - subst; eapply fork_not_atomic; eassumption.
      - rewrite <- EQr, <- assoc in HE; rewrite ->unfold_wp in Hwp.
        specialize (Hwp w' k (r2 · rf) mf σ HSw HLt HD HE); clear HE.
        destruct Hwp as [_ [_ [_ HS'] ] ]; auto.
    Qed.

    (** Fork **)
    Lemma wpFork safe m R e :
      ▹wp safe m e (umconst ⊤) * ▹R ⊑ wp safe m (fork e) (lift_bin sc (eqV (exist _ fork_ret fork_ret_is_value)) (umconst R)).	(* PDS: Why sc not and? *)
    Proof.
      intros w n r [r1 [r2 [EQr [Hwp HLR] ] ] ].
      destruct n as [| n]; [apply wpO |].
      rewrite ->unfold_wp; intros w'; intros.
      split; [intros; contradiction (fork_not_value e) | split; intros; [exfalso | split; intros ] ].
      - assert (HT := fill_fork HDec); subst K; rewrite ->fill_empty in HDec; subst.
        eapply fork_stuck with (K := ε); [| repeat eexists; eassumption ]; reflexivity.
      - assert (HT := fill_fork HDec); subst K; rewrite ->fill_empty in HDec.
        apply fork_inj in HDec; subst e'; rewrite <- EQr in HE.
        unfold lt in HLt. simpl in Hwp.
        simpl in HLR; rewrite <- Le.le_n_Sn in HE.
        do 3 eexists; split; [reflexivity | split; [| split; [eapply propsMWN, Hwp;[eassumption|omega]| eassumption]]].
        rewrite ->fill_empty; rewrite ->unfold_wp; rewrite <- (le_S_n _ _ HLt), HSw in HLR.
        clear - HLR; intros w''; intros; split; [intros | split; intros; [exfalso | split; intros; [exfalso |] ] ].
        + do 2 eexists; split; [reflexivity | split; [| eassumption] ].
          exists 1 r2; split; [simpl; now erewrite ra_op_unit by apply _ |].
          split; [| unfold lt in HLt; rewrite <- HLt, HSw in HLR; apply HLR].
          simpl; reflexivity.
        + eapply values_stuck; [exact fork_ret_is_value | eassumption | repeat eexists; eassumption].
        + assert (HV := fork_ret_is_value); rewrite ->HDec in HV; clear HDec.
          assert (HT := fill_value HV);subst K; rewrite ->fill_empty in HV.
          eapply fork_not_value; eassumption.
        + left; apply fork_ret_is_value.
      - right; right; exists e empty_ctx; rewrite ->fill_empty; reflexivity.
    Qed.

    Lemma wpUnsafe {m e φ} : wp true m e φ ⊑ wp false m e φ.
    Proof.
      move=> w n. move: n w e φ; elim/wf_nat_ind. move=> n IH w e φ r He.
      rewrite unfold_wp; move=> w' k rf mf σ HSw HLt HD HW.
      move/(_ _ HLt): IH => IH.
      move/unfold_wp/(_ _ _ _ _ _ HSw HLt HD HW): He => [HV [HS [HF _] ] ] {HSw HLt HD HW}.
      split; [done | clear HV; split; [clear HF | split; [clear HS | done] ] ].
      - move=> σ' ei ei' K HK Hs.
        move/(_ _ _ _ _ HK Hs): HS => [w'' [r' [HSw' [He' Hw'] ] ] ] {Hs HK}.
        exists w'' r'. split; [done | split; [ by apply:IH | done] ].
      - move=> e' K HK.
        move/(_ _ _ HK): HF => [w'' [rfk [rret [HSw' [Hk [He' HW']]]]]] {HK}.
        exists w'' rfk rret. split; [done | split; [exact: IH | split; [exact: IH | done] ] ].
    Qed.

  End HoareTripleProperties.

End IRIS_HT_RULES.

Module IrisHTRules (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) : IRIS_HT_RULES RL C R WP CORE PLOG.
  Include IRIS_HT_RULES RL C R WP CORE PLOG.
End IrisHTRules.
