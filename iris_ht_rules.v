Require Import ssreflect.
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

    Implicit Types (P : Props) (i : nat) (safe : bool) (m : mask) (e : expr) (Q : vPred) (r : res).

    (** Ret **)
    Program Definition eqV v : vPred :=
      n[(fun v' : value => v === v')].
    Next Obligation.
      intros v1 v2 EQv w m r HLt; destruct n as [| n]; [now inversion HLt | simpl in *].
      split; congruence.
    Qed.

    Lemma htRet e (HV : is_value e) safe m :
      valid (ht safe m ⊤ e (eqV (exist _ e HV))).
    Proof.
      intros w' nn rr w _ n r' _ _ _; clear w' nn rr.
      rewrite unfold_wp; intros w'; intros; split; [| split; [| split] ]; intros.
      - exists w' r'; split; [reflexivity | split; [| assumption] ].
        simpl; reflexivity.
      - contradiction (values_stuck _ HV _ _ HDec).
        repeat eexists; eassumption.
      - subst e; assert (HT := fill_value _ _ HV); subst K.
        revert HV; rewrite fill_empty; intros.
        contradiction (fork_not_value _ HV).
      - unfold safeExpr. auto.
    Qed.

    (** Bind **)

    (** Quantification in the logic works over nonexpansive maps, so
        we need to show that plugging the value into the postcondition
        and context is nonexpansive. *)
    Program Definition plugV safe m Q Q' K :=
      n[(fun v : value => ht safe m (Q v) (K [[` v]]) Q')].
    Next Obligation.
      intros v1 v2 EQv; unfold ht; eapply (met_morph_nonexp _ _ box).
      eapply (impl_dist (ComplBI := Props_BI)).
      - apply Q; assumption.
      - destruct n as [| n]; [apply dist_bound | simpl in EQv].
        rewrite EQv; reflexivity.
    Qed.

    Lemma htBind P Q R K e safe m :
      ht safe m P e Q ∧ all (plugV safe m Q R K) ⊑ ht safe m P (K [[ e ]]) R.
    Proof.
      intros wz nz rz [He HK] w HSw n r HLe _ HP.
      specialize (He _ HSw _ _ HLe (unit_min _ _) HP).
      rewrite ->HSw, <- HLe in HK; clear wz nz HSw HLe HP.
      revert e w r He HK; induction n using wf_nat_ind; intros; rename H into IH.
      rewrite ->unfold_wp in He; rewrite unfold_wp.
      destruct (is_value_dec e) as [HVal | HNVal]; [clear IH |].
      - intros w'; intros; edestruct He as [HV _]; try eassumption; [].
        clear He HE; specialize (HV HVal); destruct HV as [w'' [r' [HSw' [Hφ HE] ] ] ].
        (* Fold the goal back into a wp *)
        setoid_rewrite HSw'.
        assert (HT : wp safe m (K [[ e ]]) R w'' (S k) r');
          [| rewrite ->unfold_wp in HT; eapply HT; [reflexivity | unfold lt; reflexivity | eassumption | eassumption] ].
        clear HE; specialize (HK (exist _ e HVal)).
        do 30 red in HK; unfold proj1_sig in HK.
        apply HK; [etransitivity; eassumption | apply HLt | apply unit_min | assumption].
      - intros w'; intros; edestruct He as [_ [HS [HF HS'] ] ]; try eassumption; [].
        split; [intros HVal; contradiction HNVal; assert (HT := fill_value _ _ HVal);
                subst K; rewrite fill_empty in HVal; assumption | split; [| split]; intros].
        + clear He HF HE; edestruct step_by_value as [K' EQK];
          [eassumption | repeat eexists; eassumption | eassumption |].
          subst K0; rewrite <- fill_comp in HDec; apply fill_inj2 in HDec.
          edestruct HS as [w'' [r' [HSw' [He HE] ] ] ]; try eassumption; [].
          subst e; clear HStep HS.
          do 2 eexists; split; [eassumption | split; [| eassumption] ].
          rewrite <- fill_comp. apply IH; try assumption; [].
          unfold lt in HLt; rewrite <- HSw', <- HSw, Le.le_n_Sn, HLt; apply HK.
        + clear He HS HE; edestruct fork_by_value as [K' EQK]; try eassumption; [].
          subst K0; rewrite <- fill_comp in HDec; apply fill_inj2 in HDec.
          edestruct HF as [w'' [rfk [rret [HSw' [HWR [HWF HE] ] ] ] ] ];
            try eassumption; []; subst e; clear HF.
          do 3 eexists; split; [eassumption | split; [| split; eassumption] ].
          rewrite <- fill_comp; apply IH; try assumption; [].
          unfold lt in HLt; rewrite <- HSw', <- HSw, Le.le_n_Sn, HLt; apply HK.
        + clear IH He HS HE HF; specialize (HS' HSafe); clear HSafe.
          destruct HS' as [HV | [HS | HF] ].
          { contradiction. }
          { right; left; destruct HS as [σ' [ei [ei' [K0 [HE HS] ] ] ] ].
            exists σ' ei ei' (K ∘ K0); rewrite -> HE, fill_comp. auto. }
          { right; right; destruct HF as [e' [K0 HE] ].
            exists e' (K ∘ K0). rewrite -> HE, fill_comp. auto. }
    Qed.

    (** Consequence **)

    (** Much like in the case of the plugging, we need to show that
        the map from a value to a view shift between the applied
        postconditions is nonexpansive *)
    Program Definition vsLift m1 m2 (φ φ' : vPred) :=
      n[(fun v => vs m1 m2 (φ v) (φ' v))].
    Next Obligation.
      intros v1 v2 EQv; unfold vs.
      rewrite ->EQv; reflexivity.
    Qed.

    Lemma htCons P P' Q Q' safe m e :
      vs m m P P' ∧ ht safe m P' e Q' ∧ all (vsLift m m Q' Q) ⊑ ht safe m P e Q.
    Proof.
      intros wz nz rz [ [HP He] HQ] w HSw n r HLe _ Hp.
      specialize (HP _ HSw _ _ HLe (unit_min _ _) Hp); rewrite unfold_wp.
      rewrite <- HLe, HSw in He, HQ; clear wz nz HSw HLe Hp.
      intros w'; intros. edestruct HP with (mf:=mf) as [w'' [r' [HSw' [Hp' HE'] ] ] ]; try eassumption; [now rewrite mask_union_idem |].
      clear HP HE; rewrite ->HSw in He; specialize (He w'' HSw' _ r' HLt (unit_min _ _) Hp').
      setoid_rewrite HSw'.
      assert (HT : wp safe m e Q w'' (S k) r');
        [| rewrite ->unfold_wp in HT; eapply HT; [reflexivity | apply le_n | eassumption | eassumption] ].
      unfold lt in HLt; rewrite ->HSw, HSw', <- HLt in HQ; clear - He HQ.
      (* Second phase of the proof: got rid of the preconditions,
         now induction takes care of the evaluation. *)
      rename r' into r; rename w'' into w.
      revert w r e He HQ; generalize (S k) as n; clear k; induction n using wf_nat_ind.
      rename H into IH; intros; rewrite ->unfold_wp; rewrite ->unfold_wp in He.
      intros w'; intros; edestruct He as [HV [HS [HF HS'] ] ]; try eassumption; [].
      split; [intros HVal; clear HS HF IH HS' | split; intros; [clear HV HF HS' | split; [intros; clear HV HS HS' | clear HV HS HF ] ] ].
      - clear He HE; specialize (HV HVal); destruct HV as [w'' [r' [HSw' [HQ' HE] ] ] ].
        eapply HQ in HQ'; [| etransitivity; eassumption | apply HLt | apply unit_min].
        clear w n HSw HQ HLt; edestruct HQ' as [w [r'' [HSw [HQ HE'] ] ] ];
        [reflexivity | apply le_n | rewrite mask_union_idem; eassumption | eassumption |].
        exists w r''; split; [etransitivity; eassumption | split; assumption].
      - clear HE He; edestruct HS as [w'' [r' [HSw' [He HE] ] ] ];
        try eassumption; clear HS.
        do 2 eexists; split; [eassumption | split; [| eassumption] ].
        apply IH; try assumption; [].
        unfold lt in HLt; rewrite ->Le.le_n_Sn, HLt, <- HSw', <- HSw; apply HQ.
      - clear HE He; edestruct HF as [w'' [rfk [rret [HSw' [HWF [HWR HE] ] ] ] ] ]; [eassumption |].
        clear HF; do 3 eexists; split; [eassumption | split; [| split; eassumption] ].
        apply IH; try assumption; [].
        unfold lt in HLt; rewrite ->Le.le_n_Sn, HLt, <- HSw', <- HSw; apply HQ.
      - assumption.
    Qed.

    Lemma htACons safe m m' e P P' Q Q'
          (HAt   : atomic e)
          (HSub  : m' ⊆ m) :
      vs m m' P P' ∧ ht safe m' P' e Q' ∧ all (vsLift m' m Q' Q) ⊑ ht safe m P e Q.
    Proof.
      intros wz nz rz [ [HP He] HQ] w HSw n r HLe _ Hp.
      specialize (HP _ HSw _ _ HLe (unit_min _ _) Hp); rewrite unfold_wp.
      split; [intros HV; contradiction (atomic_not_value e) |].
      edestruct HP as [w'' [r' [HSw' [Hp' HE'] ] ] ]; try eassumption; [|]; clear HP.
      { intros j [Hmf Hmm']; apply (HD j); split; [assumption |].
        destruct Hmm'; [| apply HSub]; assumption.
      }
      split; [| split; [intros; subst; contradiction (fork_not_atomic K e') |] ].
      - intros; rewrite <- HLe, HSw in He, HQ; clear wz nz HSw HLe Hp.
        clear HE; rewrite ->HSw0 in He; specialize (He w'' HSw' _ r' HLt (unit_min _ _) Hp').
        unfold lt in HLt; rewrite ->HSw0, <- HLt in HQ; clear w n HSw0 HLt Hp'.
        rewrite ->unfold_wp in He; edestruct He as [_ [HS _] ];
          [reflexivity | apply le_n | rewrite ->HSub; eassumption | eassumption |].
        edestruct HS as [w [r'' [HSw [He' HE] ] ] ]; try eassumption; clear He HS HE'.
        destruct k as [| k]; [exists w' r'; split; [reflexivity | split; [apply wpO | exact I] ] |].
        assert (HNV : ~ is_value ei)
          by (intros HV; eapply (values_stuck _ HV); [symmetry; apply fill_empty | repeat eexists; eassumption]).
        subst e; assert (HT := atomic_fill _ _ HAt HNV); subst K; clear HNV.
        rewrite ->fill_empty in *; rename ei into e.
        setoid_rewrite HSw'; setoid_rewrite HSw.
        assert (HVal := atomic_step _ _ _ _ HAt HStep).
        rewrite ->HSw', HSw in HQ; clear - HE He' HQ HSub HVal HD.
        rewrite ->unfold_wp in He'; edestruct He' as [HV _];
        [reflexivity | apply le_n | rewrite ->HSub; eassumption | eassumption |].
        clear HE He'; specialize (HV HVal); destruct HV as [w' [r [HSw [HQ' HE] ] ] ].
        eapply HQ in HQ'; [| assumption | apply Le.le_n_Sn | apply unit_min].
        clear HQ; edestruct HQ' as [w'' [r' [HSw' [HQ HE'] ] ] ];
          [reflexivity | apply le_n | | eassumption |].
        { intros j [Hmf Hmm']; apply (HD j); split; [assumption |].
          destruct Hmm'; [apply HSub |]; assumption.
        }
        clear HQ' HE; exists w'' r'; split;
        [etransitivity; eassumption | split; [| eassumption] ].
        clear - HQ; rewrite ->unfold_wp; intros w; intros; split; [intros HVal' | split; intros; [intros; exfalso|split; [intros |] ] ].
        + do 2 eexists; split; [reflexivity | split; [| eassumption] ].
          unfold lt in HLt; rewrite ->HLt, <- HSw.
          eapply Q, HQ; [| apply le_n]; simpl; reflexivity.
        + eapply values_stuck; [.. | repeat eexists]; eassumption.
        + clear - HDec HVal; subst; assert (HT := fill_value _ _ HVal); subst.
          rewrite ->fill_empty in HVal; now apply fork_not_value in HVal.
        + intros; left; assumption.
      - clear HQ; intros; rewrite <- HLe, HSw in He; clear HLe HSw.
        specialize (He w'' (transitivity HSw0 HSw') _ r' HLt (unit_min _ _) Hp').
        rewrite ->unfold_wp in He; edestruct He as [_ [_ [_ HS'] ] ];
          [reflexivity | apply le_n | rewrite ->HSub; eassumption | eassumption |].
        auto.
    Qed.

    (** Framing **)

    (** Helper lemma to weaken the region mask *)
    Lemma wp_mask_weaken safe m1 m2 e φ (HD : m1 # m2) :
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

    Lemma htFrame safe m m' P R e Q (HD : m # m') :
      ht safe m P e Q ⊑ ht safe (m ∪ m') (P * R) e (lift_bin sc Q (umconst R)).
    Proof.
      intros w n rz He w' HSw n' r HLe _ [r1 [r2 [EQr [HP HLR] ] ] ].
      specialize (He _ HSw _ _ HLe (unit_min _ _) HP).
      clear P w n rz HSw HLe HP; rename w' into w; rename n' into n.
      apply wp_mask_weaken; [assumption |]; revert e w r1 r EQr HLR He.
      induction n using wf_nat_ind; intros; rename H into IH.
      rewrite ->unfold_wp; rewrite ->unfold_wp in He; intros w'; intros.
      rewrite <- EQr, <- assoc in HE; edestruct He as [HV [HS [HF HS'] ] ]; try eassumption; [].
      clear He; split; [intros HVal; clear HS HF IH HE | split; [clear HV HF HE | clear HV HS HE; split; [clear HS' | clear HF] ]; intros ].
      - specialize (HV HVal); destruct HV as [w'' [r1' [HSw' [Hφ HE] ] ] ].
        rewrite ->assoc in HE. exists w'' (r1' · r2).
        split; [eassumption | split; [| eassumption ] ].
        exists r1' r2; split; [reflexivity | split; [assumption |] ].
        unfold lt in HLt; rewrite ->HLt, <- HSw', <- HSw; apply HLR.
      - edestruct HS as [w'' [r1' [HSw' [He HE] ] ] ]; try eassumption; []; clear HS.
        destruct k as [| k]; [exists w' r1'; split; [reflexivity | split; [apply wpO | exact I] ] |].
        rewrite ->assoc in HE. exists w'' (r1' · r2).
        split; [eassumption | split; [| eassumption] ].
        eapply IH; try eassumption; [ reflexivity |].
        unfold lt in HLt; rewrite ->Le.le_n_Sn, HLt, <- HSw', <- HSw; apply HLR.
      - specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [HSw' [HWF [HWR HE] ] ] ] ] ].
        destruct k as [| k]; [exists w' rfk rret; split; [reflexivity | split; [apply wpO | split; [apply wpO | exact I] ] ] |].
        rewrite ->assoc, <- (assoc rfk) in HE.
        exists w''. exists rfk (rret · r2).
        split; [eassumption | split; [| split; eassumption] ].
        eapply IH; try eassumption; [ reflexivity |].
        unfold lt in HLt; rewrite ->Le.le_n_Sn, HLt, <- HSw', <- HSw; apply HLR.
      - auto.
    Qed.

    Lemma htAFrame safe m m' P R e Q
          (HD  : m # m')
          (HAt : atomic e) :
      ht safe m P e Q ⊑ ht safe (m ∪ m') (P * ▹R) e (lift_bin sc Q (umconst R)).
    Proof.
      intros w n rz He w' HSw n' r HLe _ [r1 [r2 [EQr [HP HLR] ] ] ].
      specialize (He _ HSw _ _ HLe (unit_min _ _) HP).
      clear rz n HLe; apply wp_mask_weaken; [assumption |]; rewrite ->unfold_wp.
      clear w HSw; rename n' into n; rename w' into w; intros w'; intros.
      split; [intros; exfalso | split; intros; [| split; intros; [exfalso| ] ] ].
      - contradiction (atomic_not_value e).
      - destruct k as [| k];
        [exists w' r; split; [reflexivity | split; [apply wpO | exact I] ] |].
        rewrite ->unfold_wp in He; rewrite <- EQr, <- assoc in HE.
        edestruct He as [_ [HeS _] ]; try eassumption; [].
        edestruct HeS as [w'' [r1' [HSw' [He' HE'] ] ] ]; try eassumption; [].
        clear HE He HeS; rewrite ->assoc in HE'.
        exists w'' (r1' · r2).
        split; [eassumption | split; [| eassumption] ].
        assert (HNV : ~ is_value ei)
          by (intros HV; eapply (values_stuck _ HV); [symmetry; apply fill_empty | repeat eexists; eassumption]).
        subst e; assert (HT := atomic_fill _ _ HAt HNV); subst K; clear HNV.
        rewrite ->fill_empty in *.
        unfold lt in HLt; rewrite <- HLt, HSw, HSw' in HLR; simpl in HLR.
        assert (HVal := atomic_step _ _ _ _ HAt HStep).
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
          assert (HT := fill_value _ _ HVal); subst K; rewrite ->fill_empty in HVal.
          contradiction (fork_not_value e').
        + unfold safeExpr. now auto.
      - subst; eapply fork_not_atomic; eassumption.
      - rewrite <- EQr, <- assoc in HE; rewrite ->unfold_wp in He.
        specialize (He w' k (r2 · rf) mf σ HSw HLt HD0 HE); clear HE.
        destruct He as [_ [_ [_ HS'] ] ]; auto.
    Qed.

    (** Fork **)
    Lemma htFork safe m P R e :
      ht safe m P e (umconst ⊤) ⊑ ht safe m (▹P * ▹R) (fork e) (lift_bin sc (eqV (exist _ fork_ret fork_ret_is_value)) (umconst R)).
    Proof.
      intros w n rz He w' HSw n' r HLe _ [r1 [r2 [EQr [HP HLR] ] ] ].
      destruct n' as [| n']; [apply wpO |].
      simpl in HP; specialize (He _ HSw _ _ (Le.le_Sn_le _ _ HLe) (unit_min _ _) HP).
      clear rz n HLe; rewrite ->unfold_wp.
      clear w HSw HP; rename n' into n; rename w' into w; intros w'; intros.
      split; [intros; contradiction (fork_not_value e) | split; intros; [exfalso | split; intros ] ].
      - assert (HT := fill_fork _ _ _ HDec); subst K; rewrite ->fill_empty in HDec; subst.
        eapply fork_stuck with (K := ε); [| repeat eexists; eassumption ]; reflexivity.
      - assert (HT := fill_fork _ _ _ HDec); subst K; rewrite ->fill_empty in HDec.
        apply fork_inj in HDec; subst e'; rewrite <- EQr in HE.
        unfold lt in HLt; rewrite <- (le_S_n _ _ HLt), HSw in He.
        simpl in HLR; rewrite <- Le.le_n_Sn in HE.
        do 3 eexists; split; [reflexivity | split; [| split; eassumption] ].
        rewrite ->fill_empty; rewrite ->unfold_wp; rewrite <- (le_S_n _ _ HLt), HSw in HLR.
        clear - HLR; intros w''; intros; split; [intros | split; intros; [exfalso | split; intros; [exfalso |] ] ].
        + do 2 eexists; split; [reflexivity | split; [| eassumption] ].
          exists 1 r2; split; [simpl; now erewrite ra_op_unit by apply _ |].
          split; [| unfold lt in HLt; rewrite <- HLt, HSw in HLR; apply HLR].
          simpl; reflexivity.
        + eapply values_stuck; [exact fork_ret_is_value | eassumption | repeat eexists; eassumption].
        + assert (HV := fork_ret_is_value); rewrite ->HDec in HV; clear HDec.
          assert (HT := fill_value _ _ HV);subst K; rewrite ->fill_empty in HV.
          eapply fork_not_value; eassumption.
        + left; apply fork_ret_is_value.
      - right; right; exists e empty_ctx; rewrite ->fill_empty; reflexivity.
    Qed.

    Lemma htUnsafe {m P e Q} : ht true m P e Q ⊑ ht false m P e Q.
    Proof.
      move=> wz nz rz He w HSw n r HLe _ HP.
      move: {He P wz nz rz HSw HLe HP} (He _ HSw _ _ HLe (unit_min _ _) HP).
      move: n e Q w r; elim/wf_nat_ind; move=> n IH e Q w r He.
      rewrite unfold_wp; move=> w' k rf mf σ HSw HLt HD HW.
      move/(_ _ HLt): IH => IH.
      move/unfold_wp/(_ _ _ _ _ _ HSw HLt HD HW): He => [HV [HS [HF _] ] ] {HSw HLt HD HW}.
      split; [done | clear HV; split; [clear HF | split; [clear HS | done] ] ].
      - move=> σ' ei ei' K HK Hs.
        move/(_ _ _ _ _ HK Hs): HS => [w'' [r' [HSw' [He' Hw'] ] ] ] {Hs HK}.
        exists w'' r'. split; [done | split; [exact: IH | done] ].
      - move=> e' K HK.
        move/(_ _ _ HK): HF => [w'' [rfk [rret [HSw' [Hk [He' HW'] ] ] ] ] ] {HK}.
        exists w'' rfk rret. split; [done | split; [exact: IH | split; [exact: IH | done] ] ].
    Qed.

  End HoareTripleProperties.

End IRIS_HT_RULES.

Module IrisHTRules (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) : IRIS_HT_RULES RL C R WP CORE PLOG.
  Include IRIS_HT_RULES RL C R WP CORE PLOG.
End IrisHTRules.
