Require Import world_prop core_lang masks iris_core.
Require Import ModuRes.PCM ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Module IrisVS (RL : PCM_T) (C : CORE_LANG).
  Module Export CORE := IrisCore RL C.

  Delimit Scope iris_scope with iris.
  Local Open Scope iris_scope.

  Section ViewShifts.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Obligation Tactic := intros.

    Program Definition preVS (m1 m2 : mask) (p : Props) (w : Wld) : UPred res :=
      mkUPred (fun n r => forall w1 rf s mf σ k (HSub : w ⊑ w1) (HLe : k < n)
                                 (HD : mf # m1 ∪ m2)
                                 (HE : erasure σ (m1 ∪ mf) (Some r · rf) s w1 @ S k),
                          exists w2 r' s',
                            w1 ⊑ w2 /\ p w2 (S k) r'
                            /\ erasure σ (m2 ∪ mf) (Some r' · rf) s' w2 @ S k) _.
    Next Obligation.
      intros n1 n2 r1 r2 HLe [rd HR] HP; intros.
      destruct (HP w1 (Some rd · rf) s mf σ k) as [w2 [r1' [s' [HW [HP' HE'] ] ] ] ];
        try assumption; [now eauto with arith | |].
      - eapply erasure_equiv, HE; try reflexivity.
        rewrite assoc, (comm (Some r1)), HR; reflexivity.
      - rewrite assoc, (comm (Some r1')) in HE'.
        destruct (Some rd · Some r1') as [r2' |] eqn: HR';
          [| apply erasure_not_empty in HE'; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        exists w2 r2' s'; split; [assumption | split; [| assumption] ].
        eapply uni_pred, HP'; [| exists rd; rewrite HR']; reflexivity.
    Qed.

    Program Definition pvs (m1 m2 : mask) : Props -n> Props :=
      n[(fun p => m[(preVS m1 m2 p)])].
    Next Obligation.
      intros w1 w2 EQw n r; split; intros HP w2'; intros.
      - eapply HP; try eassumption; [].
        rewrite EQw; assumption.
      - eapply HP; try eassumption; [].
        rewrite <- EQw; assumption.
    Qed.
    Next Obligation.
      intros w1 w2 EQw n' r HLt; destruct n as [| n]; [now inversion HLt |]; split; intros HP w2'; intros.
      - symmetry in EQw; assert (HDE := extend_dist _ _ _ _ EQw HSub).
        assert (HSE := extend_sub _ _ _ _ EQw HSub); specialize (HP (extend w2' w1)).
        edestruct HP as [w1'' [r' [s' [HW HH] ] ] ]; try eassumption; clear HP; [ | ].
        + eapply erasure_dist, HE; [symmetry; eassumption | now eauto with arith].
        + symmetry in HDE; assert (HDE' := extend_dist _ _ _ _ HDE HW).
          assert (HSE' := extend_sub _ _ _ _ HDE HW); destruct HH as [HP HE'];
          exists (extend w1'' w2') r' s'; split; [assumption | split].
          * eapply (met_morph_nonexp _ _ p), HP ; [symmetry; eassumption | now eauto with arith].
          * eapply erasure_dist, HE'; [symmetry; eassumption | now eauto with arith].
      - assert (HDE := extend_dist _ _ _ _ EQw HSub); assert (HSE := extend_sub _ _ _ _ EQw HSub); specialize (HP (extend w2' w2)).
        edestruct HP as [w1'' [r' [s' [HW HH] ] ] ]; try eassumption; clear HP; [ | ].
        + eapply erasure_dist, HE; [symmetry; eassumption | now eauto with arith].
        + symmetry in HDE; assert (HDE' := extend_dist _ _ _ _ HDE HW).
          assert (HSE' := extend_sub _ _ _ _ HDE HW); destruct HH as [HP HE'];
          exists (extend w1'' w2') r' s'; split; [assumption | split].
          * eapply (met_morph_nonexp _ _ p), HP ; [symmetry; eassumption | now eauto with arith].
          * eapply erasure_dist, HE'; [symmetry; eassumption | now eauto with arith].
    Qed.
    Next Obligation.
      intros w1 w2 EQw n r HP w2'; intros; eapply HP; try eassumption; [].
      etransitivity; eassumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w n r; split; intros HP w1; intros.
      - setoid_rewrite <- EQp; eapply HP; eassumption.
      - setoid_rewrite EQp; eapply HP; eassumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w n' r HLt; split; intros HP w1; intros.
      - edestruct HP as [w2 [r' [s' [HW [HP' HE'] ] ] ] ]; try eassumption; [].
        clear HP; repeat (eexists; try eassumption); [].
        apply EQp; [now eauto with arith | assumption].
      - edestruct HP as [w2 [r' [s' [HW [HP' HE'] ] ] ] ]; try eassumption; [].
        clear HP; repeat (eexists; try eassumption); [].
        apply EQp; [now eauto with arith | assumption].
    Qed.

    Definition vs (m1 m2 : mask) (p q : Props) : Props :=
      □ (p → pvs m1 m2 q).

  End ViewShifts.

  Section ViewShiftProps.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.

    Implicit Types (p q r : Props) (i : nat) (m : mask).

    Definition mask_sing i := mask_set mask_emp i True.

    Lemma vsTimeless m p :
      timeless p ⊑ vs m m (▹ p) p.
    Proof.
      intros w' n r1 HTL w HSub; rewrite HSub in HTL; clear w' HSub.
      intros np rp HLe HS Hp w1; intros.
      exists w1 rp s; split; [reflexivity | split; [| assumption] ]; clear HE HD.
      destruct np as [| np]; [now inversion HLe0 |]; simpl in Hp.
      unfold lt in HLe0; rewrite HLe0.
      rewrite <- HSub; apply HTL, Hp; [reflexivity | assumption].
    Qed.

    Lemma vsOpen i p :
      valid (vs (mask_sing i) mask_emp (inv i p) (▹ p)).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ HInv w'; clear nn; intros.
      do 12 red in HInv; destruct (w i) as [μ |] eqn: HLu; [| contradiction].
      apply ı in HInv; rewrite (isoR p) in HInv.
      (* get rid of the invisible 1/2 *)
      do 8 red in HInv.
      destruct HE as [HES [rs [HE HM] ] ].
      destruct (rs i) as [ri |] eqn: HLr.
      - rewrite erase_remove with (i := i) (r := ri) in HE by assumption.
        assert (HR : Some r · rf · s == Some r · Some ri · rf · erase (fdRemove i rs))
          by (rewrite <- HE, assoc, <- (assoc (Some r)), (comm rf), assoc; reflexivity).
        apply ores_equiv_eq in HR; setoid_rewrite HR in HES; clear HR.
        destruct (Some r · Some ri) as [rri |] eqn: HR;
          [| erewrite !pcm_op_zero in HES by apply _; now contradiction].
        exists w' rri (erase (fdRemove i rs)); split; [reflexivity |].
        split; [| split; [assumption |] ].
        + simpl; eapply HInv; [now auto with arith |].
          eapply uni_pred, HM with i;
            [| exists r; rewrite <- HR | | | rewrite HLr]; try reflexivity; [|].
          * left; unfold mask_sing, mask_set.
            destruct (Peano_dec.eq_nat_dec i i); tauto.
          * specialize (HSub i); rewrite HLu in HSub.
            symmetry; destruct (w' i); [assumption | contradiction].
        + exists (fdRemove i rs); split; [reflexivity | intros j Hm].
          destruct Hm as [| Hm]; [contradiction |]; specialize (HD j); simpl in HD.
          unfold mask_sing, mask_set in HD; destruct (Peano_dec.eq_nat_dec i j);
          [subst j; contradiction HD; tauto | clear HD].
          rewrite fdLookup_in; setoid_rewrite (fdRemove_neq _ _ _ n0); rewrite <- fdLookup_in; now auto.
      - rewrite <- fdLookup_notin_strong in HLr; contradiction HLr; clear HLr.
        specialize (HSub i); rewrite HLu in HSub; clear - HM HSub.
        destruct (HM i) as [HD _]; [left | rewrite HD, fdLookup_in_strong; destruct (w' i); [eexists; reflexivity | contradiction] ].
        clear; unfold mask_sing, mask_set.
        destruct (Peano_dec.eq_nat_dec i i); tauto.
    Qed.

    Lemma vsClose i p :
      valid (vs mask_emp (mask_sing i) (inv i p * ▹ p) ⊤).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ [r1 [r2 [HR [HInv HP] ] ] ] w'; clear nn; intros.
      do 12 red in HInv; destruct (w i) as [μ |] eqn: HLu; [| contradiction].
      apply ı in HInv; rewrite (isoR p) in HInv.
      (* get rid of the invisible 1/2 *)
      do 8 red in HInv.
      destruct HE as [HES [rs [HE HM] ] ].
      exists w' (pcm_unit _) (Some r · s); split; [reflexivity | split; [exact I |] ].
      assert (HR' : Some r · rf · s = rf · (Some r · s))
        by (eapply ores_equiv_eq; rewrite assoc, (comm rf); reflexivity).
      setoid_rewrite HR' in HES; erewrite pcm_op_unit by apply _.
      split; [assumption |].
      remember (match rs i with Some ri => ri | None => pcm_unit _ end) as ri eqn: EQri.
      destruct (Some ri · Some r) as [rri |] eqn: EQR.
      - exists (fdUpdate i rri rs); split; [| intros j Hm].
        + symmetry; rewrite <- HE; clear - EQR EQri; destruct (rs i) as [rsi |] eqn: EQrsi; subst;
          [eapply erase_insert_old; [eassumption | rewrite <- EQR; reflexivity] |].
          erewrite pcm_op_unit in EQR by apply _; rewrite EQR.
          now apply erase_insert_new.
        + specialize (HD j); unfold mask_sing, mask_set in *; simpl in Hm, HD.
          destruct (Peano_dec.eq_nat_dec i j);
            [subst j; clear Hm |
             destruct Hm as [Hm | Hm]; [contradiction | rewrite fdLookup_in_strong, fdUpdate_neq, <- fdLookup_in_strong by assumption; now auto] ].
          rewrite !fdLookup_in_strong, fdUpdate_eq.
          destruct n as [| n]; [now inversion HLe | simpl in HP].
          rewrite HSub in HP; specialize (HSub i); rewrite HLu in HSub.
          destruct (w' i) as [π' |]; [| contradiction].
          split; [intuition now eauto | intros].
          simpl in HLw, HLrs, HSub; subst ri0; rewrite <- HLw, <- HSub.
          apply HInv; [now auto with arith |].
          eapply uni_pred, HP; [now auto with arith |].
          assert (HT : Some ri · Some r1 · Some r2 == Some rri)
            by (rewrite <- EQR, <- HR, assoc; reflexivity); clear - HT.
          destruct (Some ri · Some r1) as [rd |];
            [| now erewrite pcm_op_zero in HT by apply _].
          exists rd; assumption.
      - destruct (rs i) as [rsi |] eqn: EQrsi; subst;
        [| erewrite pcm_op_unit in EQR by apply _; discriminate].
        clear - HE HES EQrsi EQR.
        assert (HH : rf · (Some r · s) = 0); [clear HES | rewrite HH in HES; contradiction].
        eapply ores_equiv_eq; rewrite <- HE, erase_remove by eassumption.
        rewrite (assoc (Some r)), (comm (Some r)), EQR, comm.
        erewrite !pcm_op_zero by apply _; reflexivity.
    Qed.

    Lemma vsTrans p q r m1 m2 m3 (HMS : m2 ⊆ m1 ∪ m3) :
      vs m1 m2 p q ∧ vs m2 m3 q r ⊑ vs m1 m3 p r.
    Proof.
      intros w' n r1 [Hpq Hqr] w HSub; specialize (Hpq _ HSub); rewrite HSub in Hqr; clear w' HSub.
      intros np rp HLe HS Hp w1; intros; specialize (Hpq _ _ HLe HS Hp).
      edestruct Hpq as [w2 [rq [sq [HSw12 [Hq HEq] ] ] ] ]; try eassumption; [|].
      { clear - HD HMS; intros j [Hmf Hm12]; apply (HD j); split; [assumption |].
        destruct Hm12 as [Hm1 | Hm2]; [left; assumption | apply HMS, Hm2].
      }
      clear HS; assert (HS : pcm_unit _ ⊑ rq) by (exists rq; now erewrite comm, pcm_op_unit by apply _).
      rewrite <- HLe, HSub in Hqr; specialize (Hqr _ HSw12); clear Hpq HE w HSub Hp.
      edestruct (Hqr (S k) _ HLe0 HS Hq w2) as [w3 [rR [sR [HSw23 [Hr HEr] ] ] ] ];
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
      intros w' n r1 Himp w HSub; rewrite HSub in Himp; clear w' HSub.
      intros np rp HLe HS Hp w1; intros.
      exists w1 rp s; split; [reflexivity | split; [| assumption ] ].
      eapply Himp; [assumption | now eauto with arith | exists rp; now erewrite comm, pcm_op_unit by apply _ |].
      unfold lt in HLe0; rewrite HLe0, <- HSub; assumption.
    Qed.

    Lemma vsFrame p q r m1 m2 mf (HDisj : mf # m1 ∪ m2) :
      vs m1 m2 p q ⊑ vs (m1 ∪ mf) (m2 ∪ mf) (p * r) (q * r).
    Proof.
      intros w' n r1 HVS w HSub; specialize (HVS _ HSub); clear w' r1 HSub.
      intros np rpr HLe _ [rp [rr [HR [Hp Hr] ] ] ] w'; intros.
      assert (HS : pcm_unit _ ⊑ rp) by (exists rp; now erewrite comm, pcm_op_unit by apply _).
      specialize (HVS _ _ HLe HS Hp w' (Some rr · rf) s (mf ∪ mf0) σ k); clear HS.
      destruct HVS as [w'' [rq [s' [HSub' [Hq HEq] ] ] ] ]; try assumption; [| |].
      - (* disjointness of masks: possible lemma *)
        clear - HD HDisj; intros i [ [Hmf | Hmf] Hm12]; [eapply HDisj; now eauto |].
        eapply HD; split; [eassumption | tauto].
      - rewrite assoc, HR; eapply erasure_equiv, HE; try reflexivity; [].
        clear; intros i; tauto.
      - rewrite assoc in HEq; destruct (Some rq · Some rr) as [rqr |] eqn: HR';
        [| apply erasure_not_empty in HEq; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        exists w'' rqr s'; split; [assumption | split].
        + unfold lt in HLe0; rewrite HSub, HSub', <- HLe0 in Hr; exists rq rr.
          rewrite HR'; split; now auto.
        + eapply erasure_equiv, HEq; try reflexivity; [].
          clear; intros i; tauto.
    Qed.

    Instance LP_optres (P : option RL.res -> Prop) : LimitPreserving P.
    Proof.
      intros σ σc HPc; simpl; unfold option_compl.
      generalize (@eq_refl _ (σ 1%nat)).
      pattern (σ 1%nat) at 1 3; destruct (σ 1%nat); [| intros HE; rewrite HE; apply HPc].
      intros HE; simpl; unfold discreteCompl, unSome.
      generalize (@eq_refl _ (σ 2)); pattern (σ 2) at 1 3; destruct (σ 2).
      + intros HE'; rewrite HE'; apply HPc.
      + intros HE'; exfalso; specialize (σc 1 1 2)%nat.
        rewrite <- HE, <- HE' in σc; contradiction σc; auto with arith.
    Qed.

    Definition ownLP (P : option RL.res -> Prop) : {s : option RL.res | P s} -n> Props :=
      ownL <M< inclM.

Lemma pcm_op_split rp1 rp2 rp sp1 sp2 sp :
  Some (rp1, sp1) · Some (rp2, sp2) == Some (rp, sp) <->
  Some rp1 · Some rp2 == Some rp /\ Some sp1 · Some sp2 == Some sp.
Proof.
  unfold pcm_op at 1, res_op at 2, pcm_op_prod at 1.
  destruct (Some rp1 · Some rp2) as [rp' |]; [| simpl; tauto].
  destruct (Some sp1 · Some sp2) as [sp' |]; [| simpl; tauto].
  simpl; split; [| intros [EQ1 EQ2]; subst; reflexivity].
  intros EQ; inversion EQ; tauto.
Qed.

    Lemma vsGhostUpd m rl (P : option RL.res -> Prop)
          (HU : forall rf (HD : rl · rf <> None), exists sl, P sl /\ sl · rf <> None) :
      valid (vs m m (ownL rl) (xist (ownLP P))).
    Proof.
      unfold ownLP; intros _ _ _ w _ n [rp' rl'] _ _ HG w'; intros.
      destruct rl as [rl |]; simpl in HG; [| contradiction].
      destruct HG as [ [rdp rdl] EQr]; rewrite pcm_op_split in EQr; destruct EQr as [EQrp EQrl].
      erewrite comm, pcm_op_unit in EQrp by apply _; simpl in EQrp; subst rp'.
      destruct (Some (rdp, rl') · rf · s) as [t |] eqn: EQt;
        [| destruct HE as [HES _]; setoid_rewrite EQt in HES; contradiction].
      assert (EQt' : Some (rdp, rl') · rf · s == Some t) by (rewrite EQt; reflexivity).
      clear EQt; rename EQt' into EQt.
      destruct rf as [ [rfp rfl] |]; [| now erewrite (comm _ 0), !pcm_op_zero in EQt by apply _].
      destruct s as [ [sp sl] |]; [| now erewrite (comm _ 0), pcm_op_zero in EQt by apply _].
      destruct (Some (rdp, rl') · Some (rfp, rfl)) as [ [rdfp rdfl] |] eqn: EQdf;
        setoid_rewrite EQdf in EQt; [| now erewrite pcm_op_zero in EQt by apply _].
      destruct (HU (Some rdl · Some rfl · Some sl)) as [rsl [HPrsl HCrsl] ].
      - intros HEq; destruct t as [tp tl]; apply pcm_op_split in EQt; destruct EQt as [_ EQt].
        assert (HT : Some (rdp, rl') · Some (rfp, rfl) == Some (rdfp, rdfl)) by (rewrite EQdf; reflexivity); clear EQdf.
        apply pcm_op_split in HT; destruct HT as [_ EQdf].
        now rewrite <- EQdf, <- EQrl, (comm (Some rdl)), <- (assoc (Some rl)), <- assoc, HEq in EQt.
      - destruct (rsl · Some rdl) as [rsl' |] eqn: EQrsl;
        [| contradiction HCrsl; eapply ores_equiv_eq; now erewrite !assoc, EQrsl, !pcm_op_zero by apply _ ].
        exists w' (rdp, rsl') (Some (sp, sl)); split; [reflexivity | split].
        + exists (exist _ rsl HPrsl); destruct rsl as [rsl |];
          [simpl | now erewrite pcm_op_zero in EQrsl by apply _].
          exists (rdp, rdl); rewrite pcm_op_split.
          split; [now erewrite comm, pcm_op_unit by apply _ | now rewrite comm, EQrsl].
        + destruct HE as [HES HEL]; split; [| assumption]; clear HEL.
          assert (HT := ores_equiv_eq _ _ _ EQt); setoid_rewrite EQdf in HES;
          setoid_rewrite HT in HES; clear HT; destruct t as [tp tl].
          destruct (rsl · (Some rdl · Some rfl · Some sl)) as [tl' |] eqn: EQtl;
          [| now contradiction HCrsl]; clear HCrsl.
          assert (HT : Some (rdp, rsl') · Some (rfp, rfl) · Some (sp, sl) = Some (tp, tl')); [| setoid_rewrite HT; apply HES].
          rewrite <- EQdf, <- assoc in EQt; clear EQdf; eapply ores_equiv_eq; rewrite <- assoc.
          destruct (Some (rfp, rfl) · Some (sp, sl)) as [ [up ul] |] eqn: EQu;
            setoid_rewrite EQu in EQt; [| now erewrite comm, pcm_op_zero in EQt by apply _].
          apply pcm_op_split in EQt; destruct EQt as [EQt _]; apply pcm_op_split; split; [assumption |].
          assert (HT : Some rfl · Some sl == Some ul);
            [| now rewrite <- EQrsl, <- EQtl, <- HT, !assoc].
          apply (proj2 (A := Some rfp · Some sp == Some up)), pcm_op_split.
          now erewrite EQu.
    Qed.
    (* The above proof is rather ugly in the way it handles the monoid elements,
       but it works *)

    Global Instance nat_type : Setoid nat := discreteType.
    Global Instance nat_metr : metric nat := discreteMetric.
    Global Instance nat_cmetr : cmetric nat := discreteCMetric.

    Program Definition inv' m : Props -n> {n : nat | m n} -n> Props :=
      n[(fun p => n[(fun n => inv n p)])].
    Next Obligation.
      intros i i' EQi; simpl in EQi; rewrite EQi; reflexivity.
    Qed.
    Next Obligation.
      intros i i' EQi; destruct n as [| n]; [apply dist_bound |].
      simpl in EQi; rewrite EQi; reflexivity.
    Qed.
    Next Obligation.
      intros p1 p2 EQp i; simpl morph.
      apply (morph_resp (inv (` i))); assumption.
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
      rewrite HSub in HP; clear w HSub; rename w' into w.
      destruct (fresh_region w m HInf) as [i [Hm HLi] ].
      assert (HSub : w ⊑ fdUpdate i (ı' p) w).
      { intros j; destruct (Peano_dec.eq_nat_dec i j); [subst j; rewrite HLi; exact I|].
        now rewrite fdUpdate_neq by assumption.
      }
      exists (fdUpdate i (ı' p) w) (pcm_unit _) (Some r · s); split; [assumption | split].
      - exists (exist _ i Hm); do 16 red.
        unfold proj1_sig; rewrite fdUpdate_eq; reflexivity.
      - erewrite pcm_op_unit by apply _.
        assert (HR : rf · (Some r · s) = Some r · rf · s)
          by (eapply ores_equiv_eq; rewrite assoc, (comm rf); reflexivity).
        destruct HE as [HES [rs [HE HM] ] ].
        split; [setoid_rewrite HR; assumption | clear HR].
        assert (HRi : rs i = None).
        { destruct (HM i) as [HDom _]; [tauto |].
          rewrite <- fdLookup_notin_strong, HDom, fdLookup_notin_strong; assumption.
        }
        exists (fdUpdate i r rs); split; [now rewrite <- erase_insert_new, HE by assumption | intros j Hm'].
        rewrite !fdLookup_in_strong; destruct (Peano_dec.eq_nat_dec i j).
        + subst j; rewrite !fdUpdate_eq; split; [intuition now eauto | intros].
          simpl in HLw, HLrs; subst ri; rewrite <- HLw, isoR, <- HSub.
          eapply uni_pred, HP; [now auto with arith | reflexivity].
        + rewrite !fdUpdate_neq, <- !fdLookup_in_strong by assumption.
          setoid_rewrite <- HSub.
          apply HM; assumption.
    Qed.

  End ViewShiftProps.

End IrisVS.
