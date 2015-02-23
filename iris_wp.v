Require Import ssreflect.
Require Import world_prop core_lang lang masks iris_core.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_HT (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP).
  Export CORE.
  Module Export L  := Lang C.

  Local Open Scope lang_scope.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.

  Section HoareTriples.
  (* Quadruples, really *)

    Instance LP_isval : LimitPreserving is_value.
    Proof.
      intros σ σc HC; apply HC.
    Qed.

    Implicit Types (P : Props) (i : nat) (m : mask) (e : expr) (w : Wld) (φ : vPred) (r : pres).

    Local Obligation Tactic := intros; eauto with typeclass_instances.

    Definition safeExpr e σ :=
      is_value e \/
         (exists σ' ei ei' K, e = K [[ ei ]] /\ prim_step (ei, σ) (ei', σ')) \/
         (exists e' K, e = K [[ fork e' ]]).

    Definition wpFP safe m (WP : expr -n> vPred -n> Props) e φ w n r :=
      forall w' k rf mf σ (HSw : w ⊑ w') (HLt : k < n) (HD : mf # m)
             (HE : wsat σ (m ∪ mf) (ra_proj r · rf) w' @ S k),
        (forall (HV : is_value e),
         exists w'' r', w' ⊑ w'' /\ φ (exist _ e HV) w'' (S k) r'
                           /\ wsat σ (m ∪ mf) (ra_proj r' · rf) w'' @ S k) /\
        (forall σ' ei ei' K (HDec : e = K [[ ei ]])
                (HStep : prim_step (ei, σ) (ei', σ')),
         exists w'' r', w' ⊑ w'' /\ WP (K [[ ei' ]]) φ w'' k r'
                           /\ wsat σ' (m ∪ mf) (ra_proj r' · rf) w'' @ k) /\
        (forall e' K (HDec : e = K [[ fork e' ]]),
         exists w'' rfk rret, w' ⊑ w''
                                 /\ WP (K [[ fork_ret ]]) φ w'' k rret
                                 /\ WP e' (umconst ⊤) w'' k rfk
                                 /\ wsat σ (m ∪ mf) (ra_proj rfk · ra_proj rret · rf) w'' @ k) /\
        (forall HSafe : safe = true, safeExpr e σ).

    (* Define the function wp will be a fixed-point of *)
    Program Definition wpF safe m : (expr -n> vPred -n> Props) -> (expr -n> vPred -n> Props) :=
      fun WP => n[(fun e => n[(fun φ => m[(fun w => mkUPred (wpFP safe m WP e φ w) _)])])].
    Next Obligation.
      intros n1 n2 r1 r2 HLe [rd EQr] Hp w' k rf mf σ HSw HLt HD HE.
      rewrite <- EQr, (comm rd), <- assoc in HE.
      specialize (Hp w' k (rd · rf) mf σ); destruct Hp as [HV [HS [HF HS' ] ] ];
      [| omega | ..]; try assumption; [].      
      split; [clear HS HF | split; [clear HV HF | split; clear HV HS; [| clear HF ] ] ]; intros.
      - specialize (HV HV0); destruct HV as [w'' [r1' [HSw' [Hφ HE'] ] ] ].
        rewrite ->assoc, (comm (_ r1')) in HE'.
        exists w''. exists↓ (rd · ra_proj r1').
        { clear -HE'. apply wsat_valid in HE'. auto_valid. }
        split; [assumption | split; [| assumption] ].
        eapply uni_pred, Hφ; [| exists rd]; reflexivity.
      - specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r1' [HSw' [HWP HE'] ] ] ].
        rewrite ->assoc, (comm (_ r1')) in HE'. exists w''.
        destruct k as [| k]; [exists r1'; simpl wsat; tauto |].
        exists↓ (rd · ra_proj r1').
        { clear- HE'. apply wsat_valid in HE'. auto_valid. }
        split; [assumption | split; [| assumption] ].
        eapply uni_pred, HWP; [| exists rd]; reflexivity.
      - specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret1 [HSw' [HWR [HWF HE'] ] ] ] ] ].
        destruct k as [| k]; [exists w'' rfk rret1; simpl wsat; tauto |].
        rewrite ->assoc, <- (assoc (_ rfk)) in HE'.
        exists w''. exists rfk. exists↓ (rd · ra_proj rret1).
        { clear- HE'. apply wsat_valid in HE'. rewrite comm. eapply ra_op_valid, ra_op_valid; try now apply _.
          rewrite ->(comm (_ rfk)) in HE'. eassumption. }
        repeat (split; try assumption).
        + eapply uni_pred, HWR; [| exists rd]; reflexivity.
        + clear -HE'. unfold ra_proj. rewrite ->(comm _ rd) in HE'. exact HE'.
      - auto.
    Qed.
    Next Obligation.
      intros w1 w2 EQw n' r HLt; simpl; destruct n as [| n]; [now inversion HLt |]; split; intros Hp w2'; intros.
      - symmetry in EQw; assert (EQw' := extend_dist _ _ _ _ EQw HSw); assert (HSw' := extend_sub _ _ _ _ EQw HSw); symmetry in EQw'.
        edestruct (Hp (extend w2' w1)) as [HV [HS [HF HS'] ] ]; try eassumption;
        [eapply wsat_dist, HE; [eassumption | omega] |].
        split; [clear HS HF | split; [clear HV HF | split; clear HV HS; [| clear HF ] ] ]; intros.
        + specialize (HV HV0); destruct HV as [w1'' [r' [HSw'' [Hφ HE'] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') r'; split; [assumption |].
          split; [| eapply wsat_dist, HE'; [eassumption | omega] ].
          eapply (met_morph_nonexp _ _ (φ _)), Hφ; [eassumption | omega].
        + specialize (HS _ _ _ _ HDec HStep); destruct HS as [w1'' [r' [HSw'' [HWP HE'] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') r'; split; [assumption |].
          split; [| eapply wsat_dist, HE'; [eassumption | omega] ].
          eapply (met_morph_nonexp _ _ (WP _ _)), HWP; [eassumption | omega].
        + specialize (HF _ _ HDec); destruct HF as [w1'' [rfk [rret [HSw'' [HWR [HWF HE'] ] ] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') rfk rret; split; [assumption |].
          split; [| split; [| eapply wsat_dist, HE'; [eassumption | omega] ] ];
          eapply (met_morph_nonexp _ _ (WP _ _)); try eassumption; omega.
        + auto.
      - assert (EQw' := extend_dist _ _ _ _ EQw HSw); assert (HSw' := extend_sub _ _ _ _ EQw HSw); symmetry in EQw'.
        edestruct (Hp (extend w2' w2)) as [HV [HS [HF HS'] ] ]; try eassumption;
        [eapply wsat_dist, HE; [eassumption | omega] |].
        split; [clear HS HF | split; [clear HV HF | split; clear HV HS; [| clear HF] ] ]; intros.
        + specialize (HV HV0); destruct HV as [w1'' [r' [HSw'' [Hφ HE'] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') r'; split; [assumption |].
          split; [| eapply wsat_dist, HE'; [eassumption | omega] ].
          eapply (met_morph_nonexp _ _ (φ _)), Hφ; [eassumption | omega].
        + specialize (HS _ _ _ _ HDec HStep); destruct HS as [w1'' [r' [HSw'' [HWP HE'] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') r'; split; [assumption |].
          split; [| eapply wsat_dist, HE'; [eassumption | omega] ].
          eapply (met_morph_nonexp _ _ (WP _ _)), HWP; [eassumption | omega].
        + specialize (HF _ _ HDec); destruct HF as [w1'' [rfk [rret [HSw'' [HWR [HWF HE'] ] ] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') rfk rret; split; [assumption |].
          split; [| split; [| eapply wsat_dist, HE'; [eassumption | omega] ] ];
          eapply (met_morph_nonexp _ _ (WP _ _)); try eassumption; omega.
        + auto.
    Qed.
    Next Obligation.
      intros w1 w2 Sw n r; simpl; intros Hp w'; intros; eapply Hp; try eassumption.
      etransitivity; eassumption.
    Qed.
    Next Obligation.
      intros φ1 φ2 EQφ w k r HLt; simpl; destruct n as [| n]; [now inversion HLt |].
      split; intros Hp w'; intros; edestruct Hp as [HV [HS [HF HS'] ] ]; try eassumption; [|].
      - split; [| split; [| split] ]; intros.
        + clear HS HF; specialize (HV HV0); destruct HV as [w'' [r' [HSw' [Hφ HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          apply EQφ, Hφ; omega.
        + clear HV HF; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [HSw' [Hφ HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          eapply (met_morph_nonexp _ _ (WP _)), Hφ; [symmetry; eassumption | omega].
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [HSw' [HWR [HWF HE'] ] ] ] ] ].
          exists w'' rfk rret ; repeat (split; try assumption); [].
          eapply (met_morph_nonexp _ _ (WP _)), HWR; [symmetry; eassumption | omega].
        + auto.
      - split; [| split; [| split] ]; intros.
        + clear HS HF; specialize (HV HV0); destruct HV as [w'' [r' [HSw' [Hφ HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          apply EQφ, Hφ; omega.
        + clear HV HF; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [HSw' [Hφ HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          eapply (met_morph_nonexp _ _ (WP _)), Hφ; [eassumption | omega].
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [HSw' [HWR [HWF HE'] ] ] ] ] ].
          exists w'' rfk rret; repeat (split; try assumption); [].
          eapply (met_morph_nonexp _ _ (WP _)), HWR; [eassumption | omega].
        + auto.
    Qed.
    Next Obligation.
      intros e1 e2 EQe φ w k r HLt; destruct n as [| n]; [now inversion HLt | simpl].
      simpl in EQe; subst e2; reflexivity.
    Qed.

    Instance contr_wpF safe m : contractive (wpF safe m).
    Proof.
      intros n WP1 WP2 EQWP e φ w k r HLt.
      split; intros Hp w'; intros; edestruct Hp as [HV [HS [HF HS'] ] ]; try eassumption; [|].
      - split; [assumption | split; [| split]; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [HSw' [HWP HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          eapply EQWP, HWP; omega.
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [HSw' [HWR [HWF HE'] ] ] ] ] ].
          exists w'' rfk rret; split; [assumption |].
          split; [| split; [| assumption] ]; eapply EQWP; try eassumption; omega.
        + auto.
      - split; [assumption | split; [| split]; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [HSw' [HWP HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          eapply EQWP, HWP; omega.
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [HSw' [HWR [HWF HE'] ] ] ] ] ].
          exists w'' rfk rret; split; [assumption |].
          split; [| split; [| assumption] ]; eapply EQWP; try eassumption; omega.
        + auto.
    Qed.

    Definition wp safe m : expr -n> vPred -n> Props :=
      fixp (wpF safe m) (umconst (umconst ⊤)).

    Lemma unfold_wp safe m :
      wp safe m == (wpF safe m) (wp safe m).
    Proof.
      unfold wp; apply fixp_eq.
    Qed.

    Opaque wp.

    Lemma wpO {safe m e Q w r} : wp safe m e Q w O r.
    Proof.
      rewrite unfold_wp; intros w'; intros; now inversion HLt.
    Qed.

    Definition ht safe m P e Q := □(P → wp safe m e Q).

  End HoareTriples.

End IRIS_HT.

Module IrisHT (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) : IRIS_HT RL C R WP CORE.
  Include IRIS_HT RL C R WP CORE.
End IrisHT.
