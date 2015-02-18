Require Import ssreflect.
Require Import world_prop core_lang masks iris_core.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Bullet Behavior "Strict Subproofs".

Module IrisVS (RL : RA_T) (C : CORE_LANG).
  Module Export CORE := IrisCore RL C.

  Delimit Scope iris_scope with iris.
  Local Open Scope iris_scope.

  Section ViewShifts.
    Local Open Scope mask_scope.
    Local Open Scope ra_scope.
    Local Obligation Tactic := intros.

    Program Definition preVS (m1 m2 : mask) (p : Props) (w : Wld) : UPred pres :=
      mkUPred (fun n r => forall w1 (rf: res) mf σ k (HSub : w ⊑ w1) (HLe : k < n)
                                 (HD : mf # m1 ∪ m2)
                                 (HE : wsat σ (m1 ∪ mf) (ra_proj r · rf) w1 @ S k),
                          exists w2 r',
                            w1 ⊑ w2 /\ p w2 (S k) r'
                            /\ wsat σ (m2 ∪ mf) (r' · rf) w2 @ S k) _.
    Next Obligation.
      intros n1 n2 r1 r2 HLe [rd HR] HP; intros.
      destruct (HP w1 (rd · rf) mf σ k) as [w2 [r1' [HW [HP' HE'] ] ] ];
        try assumption; [now eauto with arith | |].
      - eapply wsat_equiv, HE; try reflexivity.
        rewrite ->assoc, (comm (_ r1)), HR; reflexivity.
      - rewrite ->assoc, (comm (_ r1')) in HE'.
        exists w2. exists✓ (rd · ra_proj r1').
        { apply wsat_valid in HE'. auto_valid. }
        split; [assumption | split; [| assumption] ].
        eapply uni_pred, HP'; [reflexivity|]. exists rd. reflexivity.
    Qed.

    Program Definition pvs (m1 m2 : mask) : Props -n> Props :=
      n[(fun p => m[(preVS m1 m2 p)])].
    Next Obligation.
      intros w1 w2 EQw n' r HLt; destruct n as [| n]; [now inversion HLt |]; split; intros HP w2'; intros.
      - symmetry in EQw; assert (HDE := extend_dist _ _ _ _ EQw HSub).
        assert (HSE := extend_sub _ _ _ _ EQw HSub); specialize (HP (extend w2' w1)).
        edestruct HP as [w1'' [r' [HW HH] ] ]; try eassumption; clear HP; [ | ].
        + eapply wsat_dist, HE; [symmetry; eassumption | omega].
        + symmetry in HDE; assert (HDE' := extend_dist _ _ _ _ HDE HW).
          assert (HSE' := extend_sub _ _ _ _ HDE HW); destruct HH as [HP HE'];
          exists (extend w1'' w2') r'; split; [assumption | split].
          * eapply (met_morph_nonexp _ _ p), HP ; [symmetry; eassumption | omega].
          * eapply wsat_dist, HE'; [symmetry; eassumption | omega].
      - assert (HDE := extend_dist _ _ _ _ EQw HSub); assert (HSE := extend_sub _ _ _ _ EQw HSub); specialize (HP (extend w2' w2)).
        edestruct HP as [w1'' [r' [HW HH] ] ]; try eassumption; clear HP; [ | ].
        + eapply wsat_dist, HE; [symmetry; eassumption | omega].
        + symmetry in HDE; assert (HDE' := extend_dist _ _ _ _ HDE HW).
          assert (HSE' := extend_sub _ _ _ _ HDE HW); destruct HH as [HP HE'];
          exists (extend w1'' w2') r'; split; [assumption | split].
          * eapply (met_morph_nonexp _ _ p), HP ; [symmetry; eassumption | omega].
          * eapply wsat_dist, HE'; [symmetry; eassumption | omega].
    Qed.
    Next Obligation.
      intros w1 w2 EQw n r HP w2'; intros; eapply HP; try eassumption; [].
      etransitivity; eassumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w n' r HLt; split; intros HP w1; intros.
      - edestruct HP as [w2 [r' [HW [HP' HE'] ] ] ]; try eassumption; [].
        clear HP; repeat (eexists; try eassumption); [].
        apply EQp; [now eauto with arith | assumption].
      - edestruct HP as [w2 [r' [HW [HP' HE'] ] ] ]; try eassumption; [].
        clear HP; repeat (eexists; try eassumption); [].
        apply EQp; [now eauto with arith | assumption].
    Qed.

    Definition vs (m1 m2 : mask) (p q : Props) : Props :=
      □ (p → pvs m1 m2 q).

  End ViewShifts.

  Section ViewShiftProps.
    Local Open Scope mask_scope.
    Local Open Scope ra_scope.
    Local Open Scope bi_scope.

    Implicit Types (p q r : Props) (i : nat) (m : mask).

    Definition mask_sing i := mask_set mask_emp i True.

    Lemma vsTimeless m p :
      timeless p ⊑ vs m m (▹ p) p.
    Proof.
      intros w' n r1 HTL w HSub; rewrite ->HSub in HTL; clear w' HSub.
      intros np rp HLe HS Hp w1; intros.
      exists w1 rp; split; [reflexivity | split; [| assumption] ]; clear HE HD.
      destruct np as [| np]; [now inversion HLe0 |]; simpl in Hp.
      unfold lt in HLe0; rewrite ->HLe0.
      rewrite <- HSub; apply HTL, Hp; [reflexivity | assumption].
    Qed.

    Lemma vsOpen i p :
      valid (vs (mask_sing i) mask_emp (inv i p) (▹ p)).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ HInv w'; clear nn; intros.
      do 14 red in HInv; destruct (w i) as [μ |] eqn: HLu; [| contradiction].
      apply ı in HInv; rewrite ->(isoR p) in HInv.
      (* get rid of the invisible 1/2 *)
      do 8 red in HInv.
      destruct HE as [rs [HE HM] ].
      destruct (rs i) as [ri |] eqn: HLr.
      - rewrite ->comp_map_remove with (i := i) (r := ri) in HE by (rewrite HLr; reflexivity).
        rewrite ->assoc, <- (assoc (_ r)), (comm rf), assoc in HE.
        exists w'.
        exists✓ (ra_proj r · ra_proj ri). { destruct HE as [HE _]. eapply ra_op_valid, ra_op_valid; eauto with typeclass_instances. }
        split; [reflexivity |].
        split.
        + simpl; eapply HInv; [now auto with arith |].
          eapply uni_pred, HM with i;
            [| exists (ra_proj r) | | | rewrite HLr]; try reflexivity; [reflexivity| |].
          * left; unfold mask_sing, mask_set.
            destruct (Peano_dec.eq_nat_dec i i); tauto.
          * specialize (HSub i); rewrite HLu in HSub.
            symmetry; destruct (w' i); [assumption | contradiction].
        + exists (fdRemove i rs); split; [assumption | intros j Hm].
          destruct Hm as [| Hm]; [contradiction |]; specialize (HD j); simpl in HD.
          unfold mask_sing, mask_set, mcup in HD; destruct (Peano_dec.eq_nat_dec i j);
          [subst j; contradiction HD; tauto | clear HD].
          rewrite fdLookup_in; setoid_rewrite (fdRemove_neq _ _ _ n0); rewrite <- fdLookup_in; unfold mcup in HM; now auto.
      - rewrite <- fdLookup_notin_strong in HLr; contradiction HLr; clear HLr.
        specialize (HSub i); rewrite HLu in HSub; clear - HM HSub.
        destruct (HM i) as [HD _]; [left | rewrite ->HD, fdLookup_in_strong; destruct (w' i); [eexists; reflexivity | contradiction] ].
        clear; unfold mask_sing, mask_set.
        destruct (Peano_dec.eq_nat_dec i i); tauto.
    Qed.

    Lemma vsClose i p :
      valid (vs mask_emp (mask_sing i) (inv i p * ▹ p) ⊤).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ [r1 [r2 [HR [HInv HP] ] ] ] w'; clear nn; intros.
      do 14 red in HInv; destruct (w i) as [μ |] eqn: HLu; [| contradiction].
      apply ı in HInv; rewrite ->(isoR p) in HInv.
      (* get rid of the invisible 1/2 *)
      do 8 red in HInv.
      destruct HE as [rs [HE HM] ].
      exists w' ra_pos_unit; split; [reflexivity | split; [exact I |] ].
      rewrite ->(comm (_ r)), <-assoc in HE.
      remember (match rs i with Some ri => ri | None => ra_pos_unit end) as ri eqn: EQri.
      pose✓ rri := (ra_proj ri · ra_proj r).
      { destruct (rs i) as [rsi |] eqn: EQrsi; subst;
        [| simpl; rewrite ->ra_op_unit by apply _; now apply ra_pos_valid].
        clear - HE EQrsi. destruct HE as [HE _].
        rewrite ->comp_map_remove with (i:=i) in HE by (erewrite EQrsi; reflexivity).
        rewrite ->(assoc (_ r)), (comm (_ r)), comm, assoc, <-(assoc (_ rsi) _), (comm _ (ra_proj r)), assoc in HE.
        eapply ra_op_valid, ra_op_valid; now eauto with typeclass_instances.
      }
      exists (fdUpdate i rri rs); split; [| intros j Hm].
      - simpl. erewrite ra_op_unit by apply _.
        clear - HE EQri. destruct (rs i) as [rsi |] eqn: EQrsi.
        + subst rsi. erewrite <-comp_map_insert_old; [ eassumption | rewrite EQrsi; reflexivity | reflexivity ].
        + unfold rri. subst ri. simpl. erewrite <-comp_map_insert_new; [|rewrite EQrsi; reflexivity]. simpl.
          erewrite ra_op_unit by apply _. assumption.
      - specialize (HD j); unfold mask_sing, mask_set, mcup in *; simpl in Hm, HD.
        destruct (Peano_dec.eq_nat_dec i j);
          [subst j; clear Hm |
           destruct Hm as [Hm | Hm]; [contradiction | rewrite ->fdLookup_in_strong, fdUpdate_neq, <- fdLookup_in_strong by assumption; now auto] ].
        rewrite ->!fdLookup_in_strong, fdUpdate_eq.
        destruct n as [| n]; [now inversion HLe | simpl in HP].
        rewrite ->HSub in HP; specialize (HSub i); rewrite HLu in HSub.
        destruct (w' i) as [π' |]; [| contradiction].
        split; [intuition now eauto | intros].
        simpl in HLw, HSub. change (equiv rri ri0) in HLrs. rewrite <- HLw, <- HSub.
        apply HInv; [now auto with arith |].
        eapply uni_pred, HP; [now auto with arith |].
        rewrite <-HLrs. clear dependent ri0.
        exists (ra_proj ri · ra_proj r1).
        subst rri.
        (* Coq, are you serious?!?? *)
        change (ra_proj ri · ra_proj r1 · ra_proj r2 == (ra_proj ri · ra_proj r)).
        rewrite <-HR, assoc. reflexivity.
    Qed.

    Lemma vsTrans p q r m1 m2 m3 (HMS : m2 ⊆ m1 ∪ m3) :
      vs m1 m2 p q ∧ vs m2 m3 q r ⊑ vs m1 m3 p r.
    Proof.
      intros w' n r1 [Hpq Hqr] w HSub; specialize (Hpq _ HSub); rewrite ->HSub in Hqr; clear w' HSub.
      intros np rp HLe HS Hp w1; intros; specialize (Hpq _ _ HLe HS Hp).
      edestruct Hpq as [w2 [rq [HSw12 [Hq HEq] ] ] ]; try eassumption; [|].
      { clear - HD HMS; intros j [Hmf Hm12]; apply (HD j); split; [assumption |].
        destruct Hm12 as [Hm1 | Hm2]; [left; assumption | apply HMS, Hm2].
      }
      rewrite <- HLe, HSub in Hqr; specialize (Hqr _ HSw12); clear Hpq HE w HSub Hp.
      edestruct (Hqr (S k) _ HLe0 (unit_min _ _) Hq w2) as [w3 [rR [HSw23 [Hr HEr] ] ] ];
        try (reflexivity || eassumption); [now auto with arith | |].
      { clear - HD HMS; intros j [Hmf Hm23]; apply (HD j); split; [assumption |].
        destruct Hm23 as [Hm2 | Hm3]; [apply HMS, Hm2 | right; assumption].
      }
      clear HEq Hq HS.
      setoid_rewrite HSw12; eauto 8.
    Qed.

    Lemma vsEnt p q m :
      □ (p → q) ⊑ vs m m p q.
    Proof.
      intros w' n r1 Himp w HSub; rewrite ->HSub in Himp; clear w' HSub.
      intros np rp HLe HS Hp w1; intros.
      exists w1 rp; split; [reflexivity | split; [| assumption ] ].
      eapply Himp; [assumption | now eauto with arith | now apply ord_res_pres, unit_min | ].
      unfold lt in HLe0; rewrite ->HLe0, <- HSub; assumption.
    Qed.

    Lemma vsFrame p q r m1 m2 mf (HDisj : mf # m1 ∪ m2) :
      vs m1 m2 p q ⊑ vs (m1 ∪ mf) (m2 ∪ mf) (p * r) (q * r).
    Proof.
      intros w' n r1 HVS w HSub; specialize (HVS _ HSub); clear w' r1 HSub.
      intros np rpr HLe _ [rp [rr [HR [Hp Hr] ] ] ] w'; intros.
      assert (HS : ra_unit _ ⊑ ra_proj rp) by (eapply unit_min).
      specialize (HVS _ _ HLe HS Hp w' (ra_proj rr · rf) (mf ∪ mf0) σ k); clear HS.
      destruct HVS as [w'' [rq [HSub' [Hq HEq] ] ] ]; try assumption; [| |].
      - (* disjointness of masks: possible lemma *)
        clear - HD HDisj; intros i [ [Hmf | Hmf] Hm12]; [eapply HDisj; now eauto |].
        unfold mcup in *; eapply HD; split; [eassumption | tauto].
      - rewrite ->assoc, HR; eapply wsat_equiv, HE; try reflexivity; [].
        clear; intros i; unfold mcup; tauto.
      - rewrite ->assoc in HEq.
        exists w''. exists✓ (ra_proj rq · ra_proj rr).
        { apply wsat_valid in HEq. auto_valid. }
        split; [assumption | split].
        + unfold lt in HLe0; rewrite ->HSub, HSub', <- HLe0 in Hr; exists rq rr.
          split; now auto.
        + eapply wsat_equiv, HEq; try reflexivity; [].
          clear; intros i; unfold mcup; tauto.
    Qed.

    Instance LP_res (P : RL.res -> Prop) : LimitPreserving P.
    Proof.
      intros σ σc HPc; simpl. unfold discreteCompl.
      now auto.
    Qed.

    Definition ownLP (P : RL.res -> Prop) : {s : RL.res | P s} -n> Props :=
      ownL <M< inclM.

    Lemma vsGhostUpd m rl (P : RL.res -> Prop)
          (HU : forall rf (HD : ✓(rl · rf)), exists sl, P sl /\ ✓(sl · rf)) :
      valid (vs m m (ownL rl) (xist (ownLP P))).
    Proof.
      unfold ownLP; intros _ _ _ w _ n [ [rp' rl'] Hrval] _ _ HG w'; intros.
      destruct HE as [rs [ Hsat HE] ]. rewrite <-assoc in Hsat. simpl in Hsat. destruct Hsat as [Hval Hst].
      destruct HG as [ [rdp rdl] [_ EQrl] ]. simpl in EQrl. clear rdp.
      destruct (HU (rdl · snd(rf · comp_map rs))) as [rsl [HPrsl HCrsl] ].
      - clear - Hval EQrl. eapply ra_prod_valid2 in Hval. destruct Hval as [_ Hsnd].
        rewrite ->assoc, (comm rl), EQrl.
        rewrite ra_op_prod_snd in Hsnd. exact Hsnd.
      - exists w'. exists✓ (rp', rsl).
        { clear - Hval HCrsl.
          apply ra_prod_valid. split; [|auto_valid].
          eapply ra_prod_valid2 in Hval. destruct Hval as [Hfst _].
          rewrite ra_op_prod_fst in Hfst. auto_valid. }
        split; first reflexivity. split.
        + exists (exist _ rsl HPrsl). simpl.
          exists (rp', 1:RL.res). simpl.
          rewrite ra_op_unit ra_op_unit2. split; reflexivity.
        + exists rs. split; [| assumption]; clear HE. rewrite <-assoc. split; [eapply ra_prod_valid2; split|].
          * clear - Hval. eapply ra_prod_valid2 in Hval. destruct Hval as [Hfst _].
            rewrite ra_op_prod_fst in Hfst.
            rewrite ra_op_prod_fst. exact Hfst.
          * clear -HCrsl. rewrite ->!assoc, (comm rsl), <-assoc in HCrsl.
            apply ra_op_valid2 in HCrsl. rewrite ra_op_prod_snd. exact HCrsl.
          * clear -Hst. rewrite ra_op_prod_fst. rewrite ra_op_prod_fst in Hst. exact Hst.
    Qed.

    Program Definition inv' m : Props -n> {n : nat | m n} -n> Props :=
      n[(fun p => n[(fun n => inv n p)])].
    Next Obligation.
      intros i i' EQi; destruct n as [| n]; [apply dist_bound |].
      simpl in EQi; rewrite EQi; reflexivity.
    Qed.
    Next Obligation.
      intros p1 p2 EQp i; simpl morph.
      apply (inv (` i)); assumption.
    Qed.

    Lemma fresh_region (w : Wld) m (HInf : mask_infinite m) :
      exists i, m i /\ w i = None.
    Proof.
      destruct (HInf (S (List.last (dom w) 0%nat))) as [i [HGe Hm] ];
      exists i; split; [assumption |]; clear - HGe.
      rewrite <- fdLookup_notin_strong.
      destruct w as [ [| [n v] w] wP]; unfold dom in *; simpl findom_t in *; [tauto |].
      simpl List.map in *; rewrite last_cons in HGe.
      unfold ge in HGe; intros HIn; eapply Gt.gt_not_le, HGe.
      apply Le.le_n_S, SS_last_le; assumption.
    Qed.

    Instance LP_mask m : LimitPreserving m.
    Proof.
      intros σ σc Hp; apply Hp.
    Qed.

    Lemma vsNewInv p m (HInf : mask_infinite m) :
      valid (vs m m (▹ p) (xist (inv' m p))).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ HP w'; clear nn; intros.
      destruct n as [| n]; [now inversion HLe | simpl in HP].
      rewrite ->HSub in HP; clear w HSub; rename w' into w.
      destruct (fresh_region w m HInf) as [i [Hm HLi] ].
      assert (HSub : w ⊑ fdUpdate i (ı' p) w).
      { intros j; destruct (Peano_dec.eq_nat_dec i j); [subst j; rewrite HLi; exact I|].
        now rewrite ->fdUpdate_neq by assumption.
      }
      exists (fdUpdate i (ı' p) w) (ra_pos_unit); split; [assumption | split].
      - exists (exist _ i Hm). do 22 red.
        unfold proj1_sig. rewrite fdUpdate_eq; reflexivity.
      - unfold ra_pos_unit, proj1_sig. erewrite ra_op_unit by apply _.
        destruct HE as [rs [HE HM] ].
        exists (fdUpdate i r rs).
        assert (HRi : rs i = None).
        { destruct (HM i) as [HDom _]; unfold mcup; [tauto |].
          rewrite <- fdLookup_notin_strong, HDom, fdLookup_notin_strong; assumption.
        }
        split.
        {
          rewrite <-comp_map_insert_new by (rewrite HRi; reflexivity).
          rewrite ->assoc, (comm rf). assumption.
        }
        intros j Hm'.
        rewrite !fdLookup_in_strong; destruct (Peano_dec.eq_nat_dec i j).
        + subst j; rewrite !fdUpdate_eq; split; [intuition now eauto | intros].
          simpl in HLw. do 3 red in HLrs. rewrite <- HLw, isoR, <- HSub.
          eapply uni_pred, HP; [now auto with arith |]. rewrite HLrs. reflexivity.
        + rewrite ->!fdUpdate_neq, <- !fdLookup_in_strong by assumption.
          setoid_rewrite <- HSub.
          apply HM; assumption.
    Qed.

  End ViewShiftProps.

End IrisVS.
