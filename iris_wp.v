Require Import world_prop core_lang masks iris_vs.
Require Import ModuRes.PCM ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Module IrisWP (RL : PCM_T) (C : CORE_LANG).
  Module Export VS := IrisVS RL C.

  Delimit Scope iris_scope with iris.
  Local Open Scope iris_scope.

  Section HoareTriples.
  (* Quadruples, really *)
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.
    Local Open Scope lang_scope.

    Global Instance expr_type : Setoid expr := discreteType.
    Global Instance expr_metr : metric expr := discreteMetric.
    Global Instance expr_cmetr : cmetric expr := discreteCMetric.
    Instance LP_isval : LimitPreserving is_value.
    Proof.
      intros σ σc HC; apply HC.
    Qed.

    Implicit Types (P Q R : Props) (i : nat) (m : mask) (e : expr) (w : Wld) (φ : value -n> Props) (r : res).

    Local Obligation Tactic := intros; eauto with typeclass_instances.

    Definition wpFP safe m (WP : expr -n> (value -n> Props) -n> Props) e φ w n r :=
      forall w' k rf mf σ (HSw : w ⊑ w') (HLt : k < n) (HD : mf # m)
             (HE : wsat σ (m ∪ mf) (Some r · rf) w' @ S k),
        (forall (HV : is_value e),
         exists w'' r', w' ⊑ w'' /\ φ (exist _ e HV) w'' (S k) r'
                           /\ wsat σ (m ∪ mf) (Some r' · rf) w'' @ S k) /\
        (forall σ' ei ei' K (HDec : e = K [[ ei ]])
                (HStep : prim_step (ei, σ) (ei', σ')),
         exists w'' r', w' ⊑ w'' /\ WP (K [[ ei' ]]) φ w'' k r'
                           /\ wsat σ' (m ∪ mf) (Some r' · rf) w'' @ k) /\
        (forall e' K (HDec : e = K [[ fork e' ]]),
         exists w'' rfk rret, w' ⊑ w''
                                 /\ WP (K [[ fork_ret ]]) φ w'' k rret
                                 /\ WP e' (umconst ⊤) w'' k rfk
                                 /\ wsat σ (m ∪ mf) (Some rfk · Some rret · rf) w'' @ k) /\
        (forall HSafe : safe = true,
         is_value e \/
         (exists σ' ei ei' K, e = K [[ ei ]] /\ prim_step (ei, σ) (ei', σ')) \/
         (exists e' K, e = K [[ fork e' ]])).

    Program Definition wpF safe m : (expr -n> (value -n> Props) -n> Props) -n> expr -n> (value -n> Props) -n> Props :=
      n[(fun WP => n[(fun e => n[(fun φ => m[(fun w => mkUPred (wpFP safe m WP e φ w) _)])])])].
    Next Obligation.
      intros n1 n2 r1 r2 HLe [rd EQr] Hp w' k rf mf σ HSw HLt HD HE.
      rewrite <- EQr, (comm (Some rd)), <- assoc in HE.
      specialize (Hp w' k (Some rd · rf) mf σ); destruct Hp as [HV [HS [HF HS' ] ] ];
      [| now eauto with arith | ..]; try assumption; [].      
      split; [clear HS HF | split; [clear HV HF | split; clear HV HS; [| clear HF ] ] ]; intros.
      - specialize (HV HV0); destruct HV as [w'' [r1' [HSw' [Hφ HE'] ] ] ].
        rewrite assoc, (comm (Some r1')) in HE'.
        destruct (Some rd · Some r1') as [r2' |] eqn: HR;
          [| apply wsat_not_empty in HE'; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        exists w'' r2'; split; [assumption | split; [| assumption] ].
        eapply uni_pred, Hφ; [| eexists; rewrite <- HR]; reflexivity.
      - specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r1' [HSw' [HWP HE'] ] ] ].
        rewrite assoc, (comm (Some r1')) in HE'.
        destruct k as [| k]; [exists w'' r1'; simpl wsat; tauto |].
        destruct (Some rd · Some r1') as [r2' |] eqn: HR;
          [| apply wsat_not_empty in HE'; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        exists w'' r2'; split; [assumption | split; [| assumption] ].
        eapply uni_pred, HWP; [| eexists; rewrite <- HR]; reflexivity.
      - specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret1 [HSw' [HWR [HWF HE'] ] ] ] ] ].
        destruct k as [| k]; [exists w'' rfk rret1; simpl wsat; tauto |].
        rewrite assoc, <- (assoc (Some rfk)), (comm (Some rret1)) in HE'.
        destruct (Some rd · Some rret1) as [rret2 |] eqn: HR;
          [| apply wsat_not_empty in HE'; [contradiction | now erewrite (comm _ 0), !pcm_op_zero by apply _] ].
        exists w'' rfk rret2; repeat (split; try assumption); [].
        eapply uni_pred, HWR; [| eexists; rewrite <- HR]; reflexivity.
      - auto.
    Qed.
    Next Obligation.
      intros w1 w2 EQw n r; simpl.
      split; intros Hp w'; intros; eapply Hp; try eassumption.
      - rewrite EQw; assumption.
      - rewrite <- EQw; assumption.
    Qed.
    Next Obligation.
      intros w1 w2 EQw n' r HLt; simpl; destruct n as [| n]; [now inversion HLt |]; split; intros Hp w2'; intros.
      - symmetry in EQw; assert (EQw' := extend_dist _ _ _ _ EQw HSw); assert (HSw' := extend_sub _ _ _ _ EQw HSw); symmetry in EQw'.
        edestruct (Hp (extend w2' w1)) as [HV [HS [HF HS'] ] ]; try eassumption;
        [eapply wsat_dist, HE; [eassumption | now eauto with arith] |].
        split; [clear HS HF | split; [clear HV HF | split; clear HV HS; [| clear HF ] ] ]; intros.
        + specialize (HV HV0); destruct HV as [w1'' [r' [HSw'' [Hφ HE'] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') r'; split; [assumption |].
          split; [| eapply wsat_dist, HE'; [eassumption | now eauto with arith] ].
          eapply (met_morph_nonexp _ _ (φ _)), Hφ; [eassumption | now eauto with arith].
        + specialize (HS _ _ _ _ HDec HStep); destruct HS as [w1'' [r' [HSw'' [HWP HE'] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') r'; split; [assumption |].
          split; [| eapply wsat_dist, HE'; [eassumption | now eauto with arith] ].
          eapply (met_morph_nonexp _ _ (WP _ _)), HWP; [eassumption | now eauto with arith].
        + specialize (HF _ _ HDec); destruct HF as [w1'' [rfk [rret [HSw'' [HWR [HWF HE'] ] ] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') rfk rret; split; [assumption |].
          split; [| split; [| eapply wsat_dist, HE'; [eassumption | now eauto with arith] ] ];
          eapply (met_morph_nonexp _ _ (WP _ _)); try eassumption; now eauto with arith.
        + auto.
      - assert (EQw' := extend_dist _ _ _ _ EQw HSw); assert (HSw' := extend_sub _ _ _ _ EQw HSw); symmetry in EQw'.
        edestruct (Hp (extend w2' w2)) as [HV [HS [HF HS'] ] ]; try eassumption;
        [eapply wsat_dist, HE; [eassumption | now eauto with arith] |].
        split; [clear HS HF | split; [clear HV HF | split; clear HV HS; [| clear HF] ] ]; intros.
        + specialize (HV HV0); destruct HV as [w1'' [r' [HSw'' [Hφ HE'] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') r'; split; [assumption |].
          split; [| eapply wsat_dist, HE'; [eassumption | now eauto with arith] ].
          eapply (met_morph_nonexp _ _ (φ _)), Hφ; [eassumption | now eauto with arith].
        + specialize (HS _ _ _ _ HDec HStep); destruct HS as [w1'' [r' [HSw'' [HWP HE'] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') r'; split; [assumption |].
          split; [| eapply wsat_dist, HE'; [eassumption | now eauto with arith] ].
          eapply (met_morph_nonexp _ _ (WP _ _)), HWP; [eassumption | now eauto with arith].
        + specialize (HF _ _ HDec); destruct HF as [w1'' [rfk [rret [HSw'' [HWR [HWF HE'] ] ] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') rfk rret; split; [assumption |].
          split; [| split; [| eapply wsat_dist, HE'; [eassumption | now eauto with arith] ] ];
          eapply (met_morph_nonexp _ _ (WP _ _)); try eassumption; now eauto with arith.
        + auto.
    Qed.
    Next Obligation.
      intros w1 w2 Sw n r; simpl; intros Hp w'; intros; eapply Hp; try eassumption.
      etransitivity; eassumption.
    Qed.
    Next Obligation.
      intros φ1 φ2 EQφ w n r; simpl.
      unfold wpFP; setoid_rewrite EQφ; reflexivity.
    Qed.
    Next Obligation.
      intros φ1 φ2 EQφ w k r HLt; simpl; destruct n as [| n]; [now inversion HLt |].
      split; intros Hp w'; intros; edestruct Hp as [HV [HS [HF HS'] ] ]; try eassumption; [|].
      - split; [| split; [| split] ]; intros.
        + clear HS HF; specialize (HV HV0); destruct HV as [w'' [r' [HSw' [Hφ HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          apply EQφ, Hφ; now eauto with arith.
        + clear HV HF; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [HSw' [Hφ HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          eapply (met_morph_nonexp _ _ (WP _)), Hφ; [symmetry; eassumption | now eauto with arith].
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [HSw' [HWR [HWF HE'] ] ] ] ] ].
          exists w'' rfk rret ; repeat (split; try assumption); [].
          eapply (met_morph_nonexp _ _ (WP _)), HWR; [symmetry; eassumption | now eauto with arith].
        + auto.
      - split; [| split; [| split] ]; intros.
        + clear HS HF; specialize (HV HV0); destruct HV as [w'' [r' [HSw' [Hφ HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          apply EQφ, Hφ; now eauto with arith.
        + clear HV HF; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [HSw' [Hφ HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          eapply (met_morph_nonexp _ _ (WP _)), Hφ; [eassumption | now eauto with arith].
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [HSw' [HWR [HWF HE'] ] ] ] ] ].
          exists w'' rfk rret; repeat (split; try assumption); [].
          eapply (met_morph_nonexp _ _ (WP _)), HWR; [eassumption | now eauto with arith].
        + auto.
    Qed.
    Next Obligation.
      intros e1 e2 EQe φ w n r; simpl.
      simpl in EQe; subst e2; reflexivity.
    Qed.
    Next Obligation.
      intros e1 e2 EQe φ w k r HLt; destruct n as [| n]; [now inversion HLt | simpl].
      simpl in EQe; subst e2; reflexivity.
    Qed.
    Next Obligation.
      intros WP1 WP2 EQWP e φ w n r; simpl.
      unfold wpFP; setoid_rewrite EQWP; reflexivity.
    Qed.
    Next Obligation.
      intros WP1 WP2 EQWP e φ w k r HLt; destruct n as [| n]; [now inversion HLt | simpl].
      split; intros Hp w'; intros; edestruct Hp as [HF [HS [HV HS'] ] ]; try eassumption; [|].
      - split; [assumption | split; [| split]; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [HSw' [HWP HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          eapply (EQWP _ _ _), HWP; now eauto with arith.
        + clear HF HS; specialize (HV _ _ HDec); destruct HV as [w'' [rfk [rret [HSw' [HWR [HWF HE'] ] ] ] ] ].
          exists w'' rfk rret; split; [assumption |].
          split; [| split; [| assumption] ]; eapply EQWP; try eassumption; now eauto with arith.
        + auto.
      - split; [assumption | split; [| split]; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [HSw' [HWP HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          eapply (EQWP _ _ _), HWP; now eauto with arith.
        + clear HF HS; specialize (HV _ _ HDec); destruct HV as [w'' [rfk [rret [HSw' [HWR [HWF HE'] ] ] ] ] ].
          exists w'' rfk rret; split; [assumption |].
          split; [| split; [| assumption] ]; eapply EQWP; try eassumption; now eauto with arith.
        + auto.
    Qed.

    Instance contr_wpF safe m : contractive (wpF safe m).
    Proof.
      intros n WP1 WP2 EQWP e φ w k r HLt.
      split; intros Hp w'; intros; edestruct Hp as [HV [HS [HF HS'] ] ]; try eassumption; [|].
      - split; [assumption | split; [| split]; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [HSw' [HWP HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          eapply EQWP, HWP; now eauto with arith.
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [HSw' [HWR [HWF HE'] ] ] ] ] ].
          exists w'' rfk rret; split; [assumption |].
          split; [| split; [| assumption] ]; eapply EQWP; try eassumption; now eauto with arith.
        + auto.
      - split; [assumption | split; [| split]; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [HSw' [HWP HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          eapply EQWP, HWP; now eauto with arith.
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [HSw' [HWR [HWF HE'] ] ] ] ] ].
          exists w'' rfk rret; split; [assumption |].
          split; [| split; [| assumption] ]; eapply EQWP; try eassumption; now eauto with arith.
        + auto.
    Qed.

    Definition wp safe m : expr -n> (value -n> Props) -n> Props :=
      fixp (wpF safe m) (umconst (umconst ⊤)).

    Definition ht safe m P e φ := □ (P → wp safe m e φ).

  End HoareTriples.

  Section Adequacy.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.
    Local Open Scope lang_scope.
    Local Open Scope list_scope.

    Inductive stepn : nat -> cfg -> cfg -> Prop :=
    | stepn_O ρ : stepn O ρ ρ
    | stepn_S ρ1 ρ2 ρ3 n
              (HS  : step ρ1 ρ2)
              (HSN : stepn n ρ2 ρ3) :
        stepn (S n) ρ1 ρ3.

    (* weakest-pre for a threadpool *)
    Inductive wptp (safe : bool) (m : mask) (w : Wld) (n : nat) : tpool -> list res -> Prop :=
    | wp_emp : wptp safe m w n nil nil
    | wp_cons e r tp rs
              (WPE  : wp safe m e (umconst ⊤) w n r)
              (WPTP : wptp safe m w n tp rs) :
        wptp safe m w n (e :: tp) (r :: rs).

    (* Trivial lemmas about split over append *)
    Lemma wptp_app safe m w n tp1 tp2 rs1 rs2
          (HW1 : wptp safe m w n tp1 rs1)
          (HW2 : wptp safe m w n tp2 rs2) :
      wptp safe m w n (tp1 ++ tp2) (rs1 ++ rs2).
    Proof.
      induction HW1; [| constructor]; now trivial.
    Qed.

    Lemma wptp_app_tp safe m w n t1 t2 rs
          (HW : wptp safe m w n (t1 ++ t2) rs) :
      exists rs1 rs2, rs1 ++ rs2 = rs /\ wptp safe m w n t1 rs1 /\ wptp safe m w n t2 rs2.
    Proof.
      revert rs HW; induction t1; intros; inversion HW; simpl in *; subst; clear HW.
      - exists (@nil res) (@nil res); now auto using wptp.
      - exists (@nil res); simpl; now eauto using wptp.
      - apply IHt1 in WPTP; destruct WPTP as [rs1 [rs2 [EQrs [WP1 WP2] ] ] ]; clear IHt1.
        exists (r :: rs1) rs2; simpl; subst; now auto using wptp.
    Qed.

    Lemma comp_list_app rs1 rs2 :
      comp_list (rs1 ++ rs2) == comp_list rs1 · comp_list rs2.
    Proof.
      induction rs1; simpl comp_list; [now rewrite pcm_op_unit by apply _ |].
      now rewrite IHrs1, assoc.
    Qed.

    (* Closure under future worlds and smaller steps *)
    Lemma wptp_closure safe m (w1 w2 : Wld) n1 n2 tp rs
          (HSW : w1 ⊑ w2) (HLe : n2 <= n1)
          (HW : wptp safe m w1 n1 tp rs) :
      wptp safe m w2 n2 tp rs.
    Proof.
      induction HW; constructor; [| assumption].
      eapply uni_pred; [eassumption | reflexivity |].
      rewrite <- HSW; assumption.
    Qed.

    Definition wf_nat_ind := well_founded_induction Wf_nat.lt_wf.

    Lemma unfold_wp safe m :
      wp safe m == (wpF safe m) (wp safe m).
    Proof.
      unfold wp; apply fixp_eq.
    Qed.

    Lemma adequate_tp safe m n k e e' tp tp' σ σ' φ w r rs
          (HSN  : stepn n (e :: tp, σ) (e' :: tp', σ'))
          (HV   : is_value e')
          (HWE  : wp safe m e φ w (n + S k) r)
          (HWTP : wptp safe m w (n + S k) tp rs)
          (HE   : wsat σ m (Some r · comp_list rs) w @ n + S k) :
      exists w' r',
        w ⊑ w' /\ φ (exist _ e' HV) w' (S k) r' /\ wsat σ' m (Some r') w' @ S k.
    Proof.
      revert e tp σ w r rs HSN HWE HWTP HE; induction n using wf_nat_ind; rename H into HInd.
      intros; inversion HSN; subst; clear HSN.
      (* e is a value *)
      { rename e' into e; clear HInd HWTP; simpl plus in *; rewrite unfold_wp in HWE.
        edestruct (HWE w k) as [HVal _];
          [reflexivity | unfold lt; reflexivity | apply mask_emp_disjoint
           | rewrite mask_emp_union; eassumption |].
        specialize (HVal HV); destruct HVal as [w' [r' [HSW [Hφ HE'] ] ] ].
        rewrite mask_emp_union in HE'; destruct (Some r' · comp_list rs) as [r'' |] eqn: EQr.
        - exists w' r''; split; [assumption | split; [| assumption] ].
          eapply uni_pred, Hφ; [reflexivity |].
          rewrite ord_res_optRes; exists (comp_list rs); rewrite comm, EQr; reflexivity.
        - exfalso; eapply wsat_not_empty, HE'. reflexivity.
      }
      rename n0 into n; specialize (HInd n (le_n _)); inversion HS; subst; clear HS.
      (* atomic step *)
      { destruct t1 as [| ee t1]; inversion H0; subst; clear H0.
        (* step in e *)
        - simpl in HSN0; rewrite unfold_wp in HWE; edestruct (HWE w (n + S k)) as [_ [HS _] ];
          [reflexivity | apply le_n | apply mask_emp_disjoint | rewrite mask_emp_union; eassumption |].
          edestruct HS as [w' [r' [HSW [HWE' HE'] ] ] ]; [reflexivity | eassumption | clear HS HWE HE].
          rewrite mask_emp_union in HE'; setoid_rewrite HSW; eapply HInd; try eassumption.
          eapply wptp_closure, HWTP; [assumption | now auto with arith].
        (* step in a spawned thread *)
        - apply wptp_app_tp in HWTP; destruct HWTP as [rs1 [rs2 [EQrs [HWTP1 HWTP2] ] ] ].
          inversion HWTP2; subst; clear HWTP2; rewrite unfold_wp in WPE.
          edestruct (WPE w (n + S k) (Some r · comp_list (rs1 ++ rs0))) as [_ [HS _] ];
            [reflexivity | apply le_n | apply mask_emp_disjoint
             | eapply wsat_equiv, HE; try reflexivity; [apply mask_emp_union |] |].
          + rewrite !comp_list_app; simpl comp_list; unfold equiv.
            rewrite assoc, (comm (Some r0)), <- assoc; apply pcm_op_equiv; [reflexivity |].
            now rewrite assoc, (comm (Some r0)), <- assoc.
          + edestruct HS as [w' [r0' [HSW [WPE' HE'] ] ] ];
            [reflexivity | eassumption | clear WPE HS].
            setoid_rewrite HSW; eapply HInd; try eassumption; [| |].
            * rewrite <- HSW; eapply uni_pred, HWE; [now auto with arith | reflexivity].
            * apply wptp_app; [eapply wptp_closure, HWTP1; [assumption | now auto with arith] |].
            constructor; [eassumption | eapply wptp_closure, WPTP; [assumption | now auto with arith] ].
          * eapply wsat_equiv, HE'; try reflexivity; [symmetry; apply mask_emp_union |].
            rewrite assoc, (comm (Some r0')), <- assoc; apply pcm_op_equiv; [reflexivity |].
            rewrite !comp_list_app; simpl comp_list.
            now rewrite assoc, (comm (comp_list rs1)), <- assoc.
      }
      (* fork *)
      destruct t1 as [| ee t1]; inversion H; subst; clear H.
      (* fork from e *)
      - simpl in HSN0; rewrite unfold_wp in HWE; edestruct (HWE w (n + S k)) as [_ [_ [HF _] ] ];
        [reflexivity | apply le_n | apply mask_emp_disjoint | rewrite mask_emp_union; eassumption |].
        specialize (HF _ _ eq_refl); destruct HF as [w' [rfk [rret [HSW [HWE' [HWFK HE'] ] ] ] ] ].
        clear HWE HE; setoid_rewrite HSW; eapply HInd with (rs := rs ++ [rfk]); try eassumption; [|].
        + apply wptp_app; [| now auto using wptp].
          eapply wptp_closure, HWTP; [assumption | now auto with arith].
        + eapply wsat_equiv, HE'; try reflexivity; [symmetry; apply mask_emp_union |].
          rewrite (comm (Some rfk)), <- assoc; apply pcm_op_equiv; [reflexivity |].
          rewrite comp_list_app; simpl comp_list; rewrite comm.
          now erewrite (comm _ 1), pcm_op_unit by apply _.
      (* fork from a spawned thread *)
      - apply wptp_app_tp in HWTP; destruct HWTP as [rs1 [rs2 [EQrs [HWTP1 HWTP2] ] ] ].
        inversion HWTP2; subst; clear HWTP2; rewrite unfold_wp in WPE.
        edestruct (WPE w (n + S k) (Some r · comp_list (rs1 ++ rs0))) as [_ [_ [HF _] ] ];
          [reflexivity | apply le_n | apply mask_emp_disjoint
           | eapply wsat_equiv, HE; try reflexivity; [apply mask_emp_union |] |].
        + rewrite assoc, (comm (Some r0)), <- assoc; apply pcm_op_equiv; [reflexivity |].
          rewrite !comp_list_app; simpl comp_list; now rewrite assoc, (comm (Some r0)), <- assoc.
        + specialize (HF _ _ eq_refl); destruct HF as [w' [rfk [rret [HSW [WPE' [WPS HE'] ] ] ] ] ]; clear WPE.
          setoid_rewrite HSW; eapply HInd; try eassumption; [| |].
          * rewrite <- HSW; eapply uni_pred, HWE; [now auto with arith | reflexivity].
          * apply wptp_app; [eapply wptp_closure, HWTP1; [assumption | now auto with arith] |].
            constructor; [eassumption | apply wptp_app; [| now eauto using wptp] ].
            eapply wptp_closure, WPTP; [assumption | now auto with arith].
          * eapply wsat_equiv, HE'; try reflexivity; [symmetry; apply mask_emp_union |].
            rewrite (assoc _ (Some r)), (comm _ (Some r)), <- assoc.
            apply pcm_op_equiv; [reflexivity |].
            rewrite (comm (Some rfk)), <- assoc, comp_list_app; simpl comp_list.
            rewrite assoc, (comm _ (Some rret)), <- assoc.
            apply pcm_op_equiv; [reflexivity |].
            rewrite (comm (Some rfk)), !comp_list_app; simpl comp_list.
            rewrite assoc; apply pcm_op_equiv; [reflexivity |].
            now erewrite comm, pcm_op_unit by apply _.
    Qed.

    Lemma unit_min r : pcm_unit _ ⊑ r.
    Proof.
      exists r; now erewrite comm, pcm_op_unit by apply _.
    Qed.

    (** This is a (relatively) generic adequacy statement for all postconditions; one can
        simplify it for certain classes of assertions (e.g.,
        independent of the worlds) and obtain easy corollaries. *)
    Theorem adequacy_post safe m e p φ n k e' tp σ σ' w r
            (HT  : valid (ht safe m p e φ))
            (HSN : stepn n ([e], σ) (e' :: tp, σ'))
            (HV  : is_value e')
            (HP  : p w (n + S k) r)
            (HE  : wsat σ m (Some r) w @ n + S k) :
      exists w' r',
        w ⊑ w' /\ φ (exist _ e' HV) w' (S k) r' /\ wsat σ' m (Some r') w' @ S k.
    Proof.
      specialize (HT w (n + S k) r).
      eapply adequate_tp; [eassumption | | constructor | eapply wsat_equiv, HE; try reflexivity; [] ].
      - apply HT in HP; try reflexivity; [eassumption | apply unit_min].
      - simpl comp_list; now erewrite comm, pcm_op_unit by apply _.
    Qed.

    Program Definition cons_pred (φ : value -=> Prop): value -n> Props :=
      n[(fun v => pcmconst (mkUPred (fun n r => φ v) _))].
    Next Obligation.
      firstorder.
    Qed.
    Next Obligation.
      intros x y  H_xy P n r. simpl. rewrite H_xy. tauto.
    Qed.
    Next Obligation.
      intros x y H_xy P m r. simpl in H_xy. destruct n.
      - intros LEZ. exfalso. omega.
      - intros _. simpl. assert(H_xy': equiv x y) by assumption. rewrite H_xy'. tauto.
    Qed.

    (* Adequacy as stated in the paper: for observations of the return value *)
    Theorem adequacy_obs safe m e (φ : value -=> Prop) n e' tp σ σ'
            (HT  : valid (ht safe m (ownS σ) e (cons_pred φ)))
            (HSN : stepn n ([e], σ) (e' :: tp, σ'))
            (HV : is_value e') :
        φ (exist _ e' HV).
    Proof.
      edestruct (adequacy_post _ _ _ _ _ _ 0 _ _ _ _ fdEmpty (ex_own _ σ, pcm_unit _) HT HSN) as [w [r [H_wle [H_phi _] ] ] ].
      - exists (pcm_unit _); now rewrite pcm_op_unit by apply _.
      - hnf. rewrite Plus.plus_comm. exists (fdEmpty (V:=res)). split.
        + assert (HS : Some (ex_own _ σ, pcm_unit _) · 1 = Some (ex_own _ σ, pcm_unit _));
          [| now setoid_rewrite HS].
          eapply ores_equiv_eq; now erewrite comm, pcm_op_unit by apply _.
        + intros i _; split; [reflexivity |].
          intros _ _ [].
      - exact H_phi.
    Qed.

  End Adequacy.

  Section HoareTripleProperties.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.
    Local Open Scope lang_scope.

    Existing Instance LP_isval.

    Implicit Types (P Q R : Props) (i : nat) (safe : bool) (m : mask) (e : expr) (φ : value -n> Props) (r : res).

    (** Ret **)
    Program Definition eqV v : value -n> Props :=
      n[(fun v' : value => v === v')].
    Next Obligation.
      intros v1 v2 EQv w n r; simpl in *; split; congruence.
    Qed.
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
      - auto.
    Qed.

    Lemma wpO safe m e φ w r : wp safe m e φ w O r.
    Proof.
      rewrite unfold_wp; intros w'; intros; now inversion HLt.
    Qed.

    (** Bind **)

    (** Quantification in the logic works over nonexpansive maps, so
        we need to show that plugging the value into the postcondition
        and context is nonexpansive. *)
    Program Definition plugV safe m φ φ' K :=
      n[(fun v : value => ht safe m (φ v) (K [[` v]]) φ')].
    Next Obligation.
      intros v1 v2 EQv w n r; simpl.
      setoid_rewrite EQv at 1.
      simpl in EQv; rewrite EQv; reflexivity.
    Qed.
    Next Obligation.
      intros v1 v2 EQv; unfold ht; eapply (met_morph_nonexp _ _ box).
      eapply (impl_dist (ComplBI := Props_BI)).
      - apply φ; assumption.
      - destruct n as [| n]; [apply dist_bound | simpl in EQv].
        rewrite EQv; reflexivity.
    Qed.

    Lemma htBind P φ φ' K e safe m :
      ht safe m P e φ ∧ all (plugV safe m φ φ' K) ⊑ ht safe m P (K [[ e ]]) φ'.
    Proof.
      intros wz nz rz [He HK] w HSw n r HLe _ HP.
      specialize (He _ HSw _ _ HLe (unit_min _) HP).
      rewrite HSw, <- HLe in HK; clear wz nz HSw HLe HP.
      revert e w r He HK; induction n using wf_nat_ind; intros; rename H into IH.
      rewrite unfold_wp in He; rewrite unfold_wp.
      destruct (is_value_dec e) as [HVal | HNVal]; [clear IH |].
      - intros w'; intros; edestruct He as [HV _]; try eassumption; [].
        clear He HE; specialize (HV HVal); destruct HV as [w'' [r' [HSw' [Hφ HE] ] ] ].
        (* Fold the goal back into a wp *)
        setoid_rewrite HSw'.
        assert (HT : wp safe m (K [[ e ]]) φ' w'' (S k) r');
          [| rewrite unfold_wp in HT; eapply HT; [reflexivity | unfold lt; reflexivity | eassumption | eassumption] ].
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
          rewrite <- fill_comp; apply IH; try assumption; [].
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
    Program Definition vsLift m1 m2 φ φ' :=
      n[(fun v => vs m1 m2 (φ v) (φ' v))].
    Next Obligation.
      intros v1 v2 EQv; unfold vs.
      rewrite EQv; reflexivity.
    Qed.
    Next Obligation.
      intros v1 v2 EQv; unfold vs.
      rewrite EQv; reflexivity.
    Qed.

    Lemma htCons P P' φ φ' safe m e :
      vs m m P P' ∧ ht safe m P' e φ' ∧ all (vsLift m m φ' φ) ⊑ ht safe m P e φ.
    Proof.
      intros wz nz rz [ [HP He] Hφ] w HSw n r HLe _ Hp.
      specialize (HP _ HSw _ _ HLe (unit_min _) Hp); rewrite unfold_wp.
      rewrite <- HLe, HSw in He, Hφ; clear wz nz HSw HLe Hp.
      intros w'; intros; edestruct HP as [w'' [r' [HSw' [Hp' HE'] ] ] ]; try eassumption; [now rewrite mask_union_idem |].
      clear HP HE; rewrite HSw in He; specialize (He w'' HSw' _ r' HLt (unit_min _) Hp').
      setoid_rewrite HSw'.
      assert (HT : wp safe m e φ w'' (S k) r');
        [| rewrite unfold_wp in HT; eapply HT; [reflexivity | apply le_n | eassumption | eassumption] ].
      unfold lt in HLt; rewrite HSw, HSw', <- HLt in Hφ; clear - He Hφ.
      (* Second phase of the proof: got rid of the preconditions,
         now induction takes care of the evaluation. *)
      rename r' into r; rename w'' into w.
      revert w r e He Hφ; generalize (S k) as n; clear k; induction n using wf_nat_ind.
      rename H into IH; intros; rewrite unfold_wp; rewrite unfold_wp in He.
      intros w'; intros; edestruct He as [HV [HS [HF HS'] ] ]; try eassumption; [].
      split; [intros HVal; clear HS HF IH HS' | split; intros; [clear HV HF HS' | split; [intros; clear HV HS HS' | clear HV HS HF ] ] ].
      - clear He HE; specialize (HV HVal); destruct HV as [w'' [r' [HSw' [Hφ' HE] ] ] ].
        eapply Hφ in Hφ'; [| etransitivity; eassumption | apply HLt | apply unit_min].
        clear w n HSw Hφ HLt; edestruct Hφ' as [w [r'' [HSw [Hφ HE'] ] ] ];
        [reflexivity | apply le_n | rewrite mask_union_idem; eassumption | eassumption |].
        exists w r''; split; [etransitivity; eassumption | split; assumption].
      - clear HE He; edestruct HS as [w'' [r' [HSw' [He HE] ] ] ];
        try eassumption; clear HS.
        do 2 eexists; split; [eassumption | split; [| eassumption] ].
        apply IH; try assumption; [].
        unfold lt in HLt; rewrite Le.le_n_Sn, HLt, <- HSw', <- HSw; apply Hφ.
      - clear HE He; edestruct HF as [w'' [rfk [rret [HSw' [HWF [HWR HE] ] ] ] ] ]; [eassumption |].
        clear HF; do 3 eexists; split; [eassumption | split; [| split; eassumption] ].
        apply IH; try assumption; [].
        unfold lt in HLt; rewrite Le.le_n_Sn, HLt, <- HSw', <- HSw; apply Hφ.
      - assumption.
    Qed.

    Lemma htACons safe m m' e P P' φ φ'
          (HAt   : atomic e)
          (HSub  : m' ⊆ m) :
      vs m m' P P' ∧ ht safe m' P' e φ' ∧ all (vsLift m' m φ' φ) ⊑ ht safe m P e φ.
    Proof.
      intros wz nz rz [ [HP He] Hφ] w HSw n r HLe _ Hp.
      specialize (HP _ HSw _ _ HLe (unit_min _) Hp); rewrite unfold_wp.
      split; [intros HV; contradiction (atomic_not_value e) |].
      edestruct HP as [w'' [r' [HSw' [Hp' HE'] ] ] ]; try eassumption; [|]; clear HP.
      { intros j [Hmf Hmm']; apply (HD j); split; [assumption |].
        destruct Hmm'; [| apply HSub]; assumption.
      }
      split; [| split; [intros; subst; contradiction (fork_not_atomic K e') |] ].
      - intros; rewrite <- HLe, HSw in He, Hφ; clear wz nz HSw HLe Hp.
        clear HE; rewrite HSw0 in He; specialize (He w'' HSw' _ r' HLt (unit_min _) Hp').
        unfold lt in HLt; rewrite HSw0, <- HLt in Hφ; clear w n HSw0 HLt Hp'.
        rewrite unfold_wp in He; edestruct He as [_ [HS _] ];
          [reflexivity | apply le_n | rewrite HSub; eassumption | eassumption |].
        edestruct HS as [w [r'' [HSw [He' HE] ] ] ]; try eassumption; clear He HS HE'.
        destruct k as [| k]; [exists w' r'; split; [reflexivity | split; [apply wpO | exact I] ] |].
        assert (HNV : ~ is_value ei)
          by (intros HV; eapply (values_stuck _ HV); [symmetry; apply fill_empty | repeat eexists; eassumption]).
        subst e; assert (HT := atomic_fill _ _ HAt HNV); subst K; clear HNV.
        rewrite fill_empty in *; rename ei into e.
        setoid_rewrite HSw'; setoid_rewrite HSw.
        assert (HVal := atomic_step _ _ _ _ HAt HStep).
        rewrite HSw', HSw in Hφ; clear - HE He' Hφ HSub HVal HD.
        rewrite unfold_wp in He'; edestruct He' as [HV _];
        [reflexivity | apply le_n | rewrite HSub; eassumption | eassumption |].
        clear HE He'; specialize (HV HVal); destruct HV as [w' [r [HSw [Hφ' HE] ] ] ].
        eapply Hφ in Hφ'; [| assumption | apply Le.le_n_Sn | apply unit_min].
        clear Hφ; edestruct Hφ' as [w'' [r' [HSw' [Hφ HE'] ] ] ];
          [reflexivity | apply le_n | | eassumption |].
        { intros j [Hmf Hmm']; apply (HD j); split; [assumption |].
          destruct Hmm'; [apply HSub |]; assumption.
        }
        clear Hφ' HE; exists w'' r'; split;
        [etransitivity; eassumption | split; [| eassumption] ].
        clear - Hφ; rewrite unfold_wp; intros w; intros; split; [intros HVal' | split; intros; [intros; exfalso|split; [intros |] ] ].
        + do 2 eexists; split; [reflexivity | split; [| eassumption] ].
          unfold lt in HLt; rewrite HLt, <- HSw.
          eapply φ, Hφ; [| apply le_n]; simpl; reflexivity.
        + eapply values_stuck; [.. | repeat eexists]; eassumption.
        + clear - HDec HVal; subst; assert (HT := fill_value _ _ HVal); subst.
          rewrite fill_empty in HVal; now apply fork_not_value in HVal.
        + intros; left; assumption.
      - clear Hφ; intros; rewrite <- HLe, HSw in He; clear HLe HSw.
        specialize (He w'' (transitivity HSw0 HSw') _ r' HLt (unit_min _) Hp').
        rewrite unfold_wp in He; edestruct He as [_ [_ [_ HS'] ] ];
          [reflexivity | apply le_n | rewrite HSub; eassumption | eassumption |].
        auto.
    Qed.

    (** Framing **)

    (** Helper lemma to weaken the region mask *)
    Lemma wp_mask_weaken safe m1 m2 e φ (HD : m1 # m2) :
      wp safe m1 e φ ⊑ wp safe (m1 ∪ m2) e φ.
    Proof.
      intros w n; revert w e φ; induction n using wf_nat_ind; rename H into HInd; intros w e φ r HW.
      rewrite unfold_wp; rewrite unfold_wp in HW; intros w'; intros.
      edestruct HW with (mf := mf ∪ m2) as [HV [HS [HF HS'] ] ]; try eassumption;
      [| eapply wsat_equiv, HE; try reflexivity; [] |].
      { intros j [ [Hmf | Hm'] Hm]; [apply (HD0 j) | apply (HD j) ]; tauto.
      }
      { clear; intros j; tauto.
      }
      clear HW HE; split; [intros HVal; clear HS HF HInd | split; [intros; clear HV HF | split; [intros; clear HV HS | intros; clear HV HS HF] ] ].
      - specialize (HV HVal); destruct HV as [w'' [r' [HSW [Hφ HE] ] ] ].
        do 2 eexists; split; [eassumption | split; [eassumption |] ].
        eapply wsat_equiv, HE; try reflexivity; [].
        intros j; tauto.
      - edestruct HS as [w'' [r' [HSW [HW HE] ] ] ]; try eassumption; []; clear HS.
        do 2 eexists; split; [eassumption | split; [eapply HInd, HW; assumption |] ].
        eapply wsat_equiv, HE; try reflexivity; [].
        intros j; tauto.
      - destruct (HF _ _ HDec) as [w'' [rfk [rret [HSW [HWR [HWF HE] ] ] ] ] ]; clear HF.
        do 3 eexists; split; [eassumption |].
        do 2 (split; [apply HInd; eassumption |]).
        eapply wsat_equiv, HE; try reflexivity; [].
        intros j; tauto.
      - auto.
    Qed.

    Lemma htFrame safe m m' P R e φ (HD : m # m') :
      ht safe m P e φ ⊑ ht safe (m ∪ m') (P * R) e (lift_bin sc φ (umconst R)).
    Proof.
      intros w n rz He w' HSw n' r HLe _ [r1 [r2 [EQr [HP HLR] ] ] ].
      specialize (He _ HSw _ _ HLe (unit_min _) HP).
      clear P w n rz HSw HLe HP; rename w' into w; rename n' into n.
      apply wp_mask_weaken; [assumption |]; revert e w r1 r EQr HLR He.
      induction n using wf_nat_ind; intros; rename H into IH.
      rewrite unfold_wp; rewrite unfold_wp in He; intros w'; intros.
      rewrite <- EQr, <- assoc in HE; edestruct He as [HV [HS [HF HS'] ] ]; try eassumption; [].
      clear He; split; [intros HVal; clear HS HF IH HE | split; [clear HV HF HE | clear HV HS HE; split; [clear HS' | clear HF] ]; intros ].
      - specialize (HV HVal); destruct HV as [w'' [r1' [HSw' [Hφ HE] ] ] ].
        rewrite assoc in HE; destruct (Some r1' · Some r2) as [r' |] eqn: EQr';
        [| eapply wsat_not_empty in HE; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        do 2 eexists; split; [eassumption | split; [| eassumption ] ].
        exists r1' r2; split; [now rewrite EQr' | split; [assumption |] ].
        unfold lt in HLt; rewrite HLt, <- HSw', <- HSw; apply HLR.
      - edestruct HS as [w'' [r1' [HSw' [He HE] ] ] ]; try eassumption; []; clear HS.
        destruct k as [| k]; [exists w' r1'; split; [reflexivity | split; [apply wpO | exact I] ] |].
        rewrite assoc in HE; destruct (Some r1' · Some r2) as [r' |] eqn: EQr';
        [| eapply wsat_not_empty in HE; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        do 2 eexists; split; [eassumption | split; [| eassumption] ].
        eapply IH; try eassumption; [rewrite <- EQr'; reflexivity |].
        unfold lt in HLt; rewrite Le.le_n_Sn, HLt, <- HSw', <- HSw; apply HLR.
      - specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [HSw' [HWF [HWR HE] ] ] ] ] ].
        destruct k as [| k]; [exists w' rfk rret; split; [reflexivity | split; [apply wpO | split; [apply wpO | exact I] ] ] |].
        rewrite assoc, <- (assoc (Some rfk)) in HE; destruct (Some rret · Some r2) as [rret' |] eqn: EQrret;
        [| eapply wsat_not_empty in HE; [contradiction | now erewrite (comm _ 0), !pcm_op_zero by apply _] ].
        do 3 eexists; split; [eassumption | split; [| split; eassumption] ].
        eapply IH; try eassumption; [rewrite <- EQrret; reflexivity |].
        unfold lt in HLt; rewrite Le.le_n_Sn, HLt, <- HSw', <- HSw; apply HLR.
      - auto.
    Qed.

    Lemma htAFrame safe m m' P R e φ
          (HD  : m # m')
          (HAt : atomic e) :
      ht safe m P e φ ⊑ ht safe (m ∪ m') (P * ▹ R) e (lift_bin sc φ (umconst R)).
    Proof.
      intros w n rz He w' HSw n' r HLe _ [r1 [r2 [EQr [HP HLR] ] ] ].
      specialize (He _ HSw _ _ HLe (unit_min _) HP).
      clear rz n HLe; apply wp_mask_weaken; [assumption |]; rewrite unfold_wp.
      clear w HSw; rename n' into n; rename w' into w; intros w'; intros.
      split; [intros; exfalso | split; intros; [| split; intros; [exfalso| ] ] ].
      - contradiction (atomic_not_value e).
      - destruct k as [| k];
        [exists w' r; split; [reflexivity | split; [apply wpO | exact I] ] |].
        rewrite unfold_wp in He; rewrite <- EQr, <- assoc in HE.
        edestruct He as [_ [HeS _] ]; try eassumption; [].
        edestruct HeS as [w'' [r1' [HSw' [He' HE'] ] ] ]; try eassumption; [].
        clear HE He HeS; rewrite assoc in HE'.
        destruct (Some r1' · Some r2) as [r' |] eqn: EQr';
          [| eapply wsat_not_empty in HE';
             [contradiction | now erewrite !pcm_op_zero by apply _] ].
        do 2 eexists; split; [eassumption | split; [| eassumption] ].
        assert (HNV : ~ is_value ei)
          by (intros HV; eapply (values_stuck _ HV); [symmetry; apply fill_empty | repeat eexists; eassumption]).
        subst e; assert (HT := atomic_fill _ _ HAt HNV); subst K; clear HNV.
        rewrite fill_empty in *.
        unfold lt in HLt; rewrite <- HLt, HSw, HSw' in HLR; simpl in HLR.
        assert (HVal := atomic_step _ _ _ _ HAt HStep).
        clear - He' HVal EQr' HLR; rename w'' into w; rewrite unfold_wp; intros w'; intros.
        split; [intros HV; clear HVal | split; intros; [exfalso| split; intros; [exfalso |] ] ].
        + rewrite unfold_wp in He'; rewrite <- EQr', <- assoc in HE; edestruct He' as [HVal _]; try eassumption; [].
          specialize (HVal HV); destruct HVal as [w'' [r1'' [HSw' [Hφ HE'] ] ] ].
          rewrite assoc in HE'; destruct (Some r1'' · Some r2) as [r'' |] eqn: EQr'';
          [| eapply wsat_not_empty in HE';
             [contradiction | now erewrite !pcm_op_zero by apply _] ].
          do 2 eexists; split; [eassumption | split; [| eassumption] ].
          exists r1'' r2; split; [now rewrite EQr'' | split; [assumption |] ].
          unfold lt in HLt; rewrite <- HLt, HSw, HSw' in HLR; apply HLR.
        + eapply values_stuck; [.. | repeat eexists]; eassumption.
        + subst; clear -HVal.
          assert (HT := fill_value _ _ HVal); subst K; rewrite fill_empty in HVal.
          contradiction (fork_not_value e').
        + auto.
      - subst; eapply fork_not_atomic; eassumption.
      - rewrite <- EQr, <- assoc in HE; rewrite unfold_wp in He.
        specialize (He w' k (Some r2 · rf) mf σ HSw HLt HD0 HE); clear HE.
        destruct He as [_ [_ [_ HS'] ] ]; auto.
    Qed.

    (** Fork **)
    Lemma htFork safe m P R e :
      ht safe m P e (umconst ⊤) ⊑ ht safe m (▹ P * ▹ R) (fork e) (lift_bin sc (eqV (exist _ fork_ret fork_ret_is_value)) (umconst R)).
    Proof.
      intros w n rz He w' HSw n' r HLe _ [r1 [r2 [EQr [HP HLR] ] ] ].
      destruct n' as [| n']; [apply wpO |].
      simpl in HP; specialize (He _ HSw _ _ (Le.le_Sn_le _ _ HLe) (unit_min _) HP).
      clear rz n HLe; rewrite unfold_wp.
      clear w HSw HP; rename n' into n; rename w' into w; intros w'; intros.
      split; [intros; contradiction (fork_not_value e) | split; intros; [exfalso | split; intros ] ].
      - assert (HT := fill_fork _ _ _ HDec); subst K; rewrite fill_empty in HDec; subst.
        eapply fork_stuck with (K := ε); [| repeat eexists; eassumption ]; reflexivity.
      - assert (HT := fill_fork _ _ _ HDec); subst K; rewrite fill_empty in HDec.
        apply fork_inj in HDec; subst e'; rewrite <- EQr in HE.
        unfold lt in HLt; rewrite <- (le_S_n _ _ HLt), HSw in He.
        simpl in HLR; rewrite <- Le.le_n_Sn in HE.
        do 3 eexists; split; [reflexivity | split; [| split; eassumption] ].
        rewrite fill_empty; rewrite unfold_wp; rewrite <- (le_S_n _ _ HLt), HSw in HLR.
        clear - HLR; intros w''; intros; split; [intros | split; intros; [exfalso | split; intros; [exfalso |] ] ].
        + do 2 eexists; split; [reflexivity | split; [| eassumption] ].
          exists (pcm_unit _) r2; split; [now erewrite pcm_op_unit by apply _ |].
          split; [| unfold lt in HLt; rewrite <- HLt, HSw in HLR; apply HLR].
          simpl; reflexivity.
        + eapply values_stuck; [exact fork_ret_is_value | eassumption | repeat eexists; eassumption].
        + assert (HV := fork_ret_is_value); rewrite HDec in HV; clear HDec.
          assert (HT := fill_value _ _ HV);subst K; rewrite fill_empty in HV.
          eapply fork_not_value; eassumption.
        + left; apply fork_ret_is_value.
      - right; right; exists e empty_ctx; rewrite fill_empty; reflexivity.
    Qed.

  End HoareTripleProperties.

  Section DerivedRules.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.
    Local Open Scope lang_scope.

    Existing Instance LP_isval.

    Implicit Types (P Q R : Props) (i : nat) (m : mask) (e : expr) (φ : value -n> Props) (r : res).

    Lemma vsFalse m1 m2 :
      valid (vs m1 m2 ⊥ ⊥).
    Proof.
      rewrite valid_iff, box_top.
      unfold vs; apply box_intro.
      rewrite <- and_impl, and_projR.
      apply bot_false.
    Qed.

  End DerivedRules.

End IrisWP.
