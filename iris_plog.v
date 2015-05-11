Require Import Ssreflect.ssreflect Omega.
Require Import world_prop core_lang lang iris_core.
Require Import ModuRes.DecEnsemble ModuRes.RA ModuRes.CMRA ModuRes.SPred ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.RAConstr ModuRes.Agreement.

Set Bullet Behavior "Strict Subproofs".

(* This enriches the Iris core logic with program logic features:
   Invariants, View Shifts, and Hoare Triples. The last two make use
   of a notion of "world satisfaction" (which you can also think of
   as the erasure from logical states to physical ones). *)
Module Type IRIS_PLOG (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP).
  Export CORE.
  Module Export L  := Lang C.

  Local Open Scope lang_scope.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.
  
  Implicit Types (P : Props) (u v w : Wld) (n i k : nat) (m : DecEnsemble nat) (r : res) (σ : state) (φ : vPred).

  Section WorldSatisfaction.

    (* First, we need to compose the resources of a finite map. This won't be pretty, for
       now, since the library does not provide enough
       constructs. Hopefully we can provide a fold that'd work for
       that at some point
     *)
    Fixpoint comp_list w m (xs : list Wld) : Wld :=
      match xs with
        | nil => w
        | (x :: xs)%list => x · comp_list w xs
      end.

    Lemma comp_list_unit w xs :
      comp_list w xs == 1 w · comp_list w xs.
    Proof.
      induction xs; first now rewrite ra_unit_dup.
      now rewrite [_ w _]/= {1}IHxs !assoc (comm _ (1 _)).
    Qed.

    Lemma comp_list_app w rs1 rs2 :
      comp_list w (rs1 ++ rs2) == comp_list w rs1 · comp_list w rs2.
    Proof.
      induction rs1; simpl comp_list; [now rewrite {1}comp_list_unit |].
      now rewrite ->IHrs1, assoc.
    Qed.

    Definition cod (m : nat -f> Wld) : list Wld := List.map snd (findom_t m).
    Definition comp_map w (m : nat -f> Wld) : Wld := comp_list w (cod m).

    Lemma comp_map_remove u (rs : nat -f> Wld) i w (HLu : rs i == Some w) :
      comp_map u rs == w · comp_map u (fdRemove i rs).
    Proof.
      destruct rs as [rs rsP]; unfold comp_map, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [contradiction |]; simpl comp_list; simpl in HLu.
      destruct (comp i j); [red in HLu; rewrite-> HLu; reflexivity | contradiction |].
      simpl comp_list; rewrite ->IHrs by eauto using SS_tail.
      rewrite-> !assoc, (comm s). reflexivity.
    Qed.

    Lemma comp_map_insert_new u (rs : nat -f> Wld) i w (HNLu : rs i == None) :
      w · comp_map u rs == comp_map u (fdUpdate i w rs).
    Proof.
      destruct rs as [rs rsP]; unfold comp_map, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [reflexivity | simpl comp_list; simpl in HNLu].
      destruct (comp i j); [contradiction | reflexivity |].
      simpl comp_list; rewrite <- IHrs by eauto using SS_tail.
      rewrite-> !assoc, (comm w); reflexivity.
    Qed.

    Lemma comp_map_insert_old u (rs : nat -f> Wld) i w1 w2 w
          (HLu : rs i == Some w1) (HEq : w1 · w2 == w):
      w2 · comp_map u rs == comp_map u (fdUpdate i w rs).
    Proof.
      destruct rs as [rs rsP]; unfold comp_map, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [contradiction |]; simpl comp_list; simpl in HLu.
      destruct (comp i j); [red in HLu; rewrite-> HLu; clear HLu | contradiction |].
      - simpl comp_list; rewrite ->assoc, (comm w2), <- HEq; reflexivity.
      - simpl comp_list; rewrite <- IHrs by eauto using SS_tail.
        rewrite-> !assoc, (comm w2); reflexivity.
    Qed.

    (* When is a resource okay with a state? *)
    Definition res_sat (r: res) σ: Prop := ↓r /\ fst r == ex_own σ.

    Global Instance res_sat_dist : Proper (equiv ==> equiv ==> iff) res_sat.
    Proof.
      intros [ [s1| |] r1] [ [s2| |] r2] [EQs EQr] σ1 σ2 EQσ; unfold res_sat; simpl in *; try tauto; try rewrite !EQs; try rewrite !EQr; try rewrite !EQσ; reflexivity.
    Qed.

    (* RJ: For the CMRA wsat, * think the folloiwing should work:
       Require the fully composed world to be (S n)-valid. Since this is under a ▹, that
       should not hinder non-expansiveness. Then use that proof and ra_ag_unInjApprox to
       extract an (S n)-approximation of the (halve Props) from the World. This
       will be an n-approximation of the Props, so things should fit. *)
    Program Definition wsat σ m : Props :=
      ▹ (m[(fun w => 
              mkSPred (
                  fun n => 
                    exists rs : nat -f> Wld,
                      let t := w · (comp_map w rs) in
                      exists pv : (cmra_valid t (S n)),
                        (fst (snd t) ⊑ ex_own σ)
                            /\ forall i (INt : i ∈ dom (fst t)),
                                 let op := Indom_lookup _ _ (proj2 (In_inlst _ _) INt) in
                                       exists INrs : i ∈ dom rs,
                                         let wp := Indom_lookup _ _ (proj2 (In_inlst _ _ ) INrs) in
                                               match op with
                                                 | ag_unit => True
                                                 | ag_inj v p ts => unhalved (ı (p n _)) wp n
                                               end
                ) _ 
        )] ).
    Next Obligation.
      symmetry in Heq_op.
      apply equivR in Heq_op.
      rewrite /cmra_valid /ra_prod_cmra_valid (surjective_pairing (w · _)) in pv.
      destruct pv as [Hf Hs].
      specialize (Hf i (ag_inj _ v p ts)).
      have/Hf : (fst (w · comp_map w rs) i == Some (ag_inj PreProp v p ts)).
      { rewrite -Heq_op. symmetry. apply/equivR. exact (Indom_lookup_find _ _ (proj2 (In_inlst _ _) INt)). }
      apply dpred; omega.
    Qed.
    Next Obligation.
      intros n1 n2 HLe (rs & pv & Hσ & H). 
      exists rs. exists (dpred (m := S n2) (le_n_S _ _ HLe) pv).
      split; [assumption|]. move => i INt. specialize (H i INt). destruct H as [INrs H].
      exists INrs. 
      pose (IL := 
Indom_lookup i (findom_t (fst (w · comp_map w rs)))
       (proj2
          (In_inlst i (List.map fst (findom_t (fst (w · comp_map w rs)))))
          INt)).
      fold IL in H. fold IL.
      clear H.
      generalize (@eq_refl _ IL) as EQ.
      pattern (IL) at 2 6.
      ddes (IL) at 4 5 6 as [v0 ts0 tsx0|] deqn:EQ1.
      generalize (eq_refl). pattern x.
      destruct (Indom_lookup i (findom_t (fst (w · comp_map w rs))) (proj2 (In_inlst i (List.map fst (findom_t (fst (w · comp_map w rs))))) INt)).
      
      setoid_rewrite HLe; eassumption.
    Qed.

    Global Instance wsat_equiv σ : Proper (equiv ==> equiv ==> equiv ==> equiv) (wsat σ).
    Proof.
      intros m1 m2 EQm r r' EQr w1 w2 EQw [| n]; [reflexivity |].
      split; intros [rs [HE HM] ]; exists rs.
      - split; [rewrite <-EQr; assumption | intros; apply EQm in Hm; split; [| setoid_rewrite <- EQw; apply HM, Hm] ].
        destruct (HM _ Hm) as [HD _]; rewrite HD; clear - EQw.
        rewrite fdLookup_in; setoid_rewrite EQw; rewrite <- fdLookup_in; reflexivity.
      - split; [rewrite EQr; assumption | intros; apply EQm in Hm; split; [| setoid_rewrite EQw; apply HM, Hm] ].
        destruct (HM _ Hm) as [HD _]; rewrite HD; clear - EQw.
        rewrite fdLookup_in; setoid_rewrite <- EQw; rewrite <- fdLookup_in; reflexivity.
    Qed.

    (* TODO: this duplicates some proof effort from above. unify these two. *)
    Global Instance wsat_dist n σ m u : Proper (dist n ==> dist n) (wsat σ m u).
    Proof.
      intros w1 w2 EQw [| n'] HLt; [reflexivity |]; destruct n as [| n]; [now inversion HLt |].
      split; intros [rs [HE HM] ]; exists rs.
      - split; [assumption | split; [rewrite <- (domeq EQw); apply HM, Hm |] ].
        intros; destruct (HM _ Hm) as [_ HR]; clear HE HM Hm.
        assert (EQπ := EQw i); rewrite-> HLw in EQπ; clear HLw.
        destruct (w1 i) as [π' |]; [| contradiction]; do 3 red in EQπ.
        apply ı in EQπ. apply halve_eq in EQπ.
        apply EQπ; [now auto with arith |].
        apply (met_morph_nonexp (unhalved (ı π'))) in EQw; apply EQw; [omega |].
        apply HR; [reflexivity | assumption].
      - split; [assumption | split; [rewrite (domeq EQw); apply HM, Hm |] ].
        intros; destruct (HM _ Hm) as [_ HR]; clear HE HM Hm.
        assert (EQπ := EQw i); rewrite-> HLw in EQπ; clear HLw.
        destruct (w2 i) as [π' |]; [| contradiction]. do 3 red in EQπ.
        apply ı in EQπ. apply halve_eq in EQπ. apply EQπ; [now auto with arith |].
        apply (met_morph_nonexp (unhalved (ı π'))) in EQw; apply EQw; [omega |].
        apply HR; [reflexivity | assumption].
    Qed.

    Lemma wsat_valid {σ m r w k} :
      wsat σ m r w (S k) -> ↓r.
    Proof.
      move=> [rs [[Hv _] _]]; exact: ra_op_valid Hv.
    Qed.

    Lemma wsat_state {σ m u w k} :
      wsat σ m u w (S k) -> fst u == ex_own σ \/ fst u == 1.
    Proof.
      move: u=>[ux ug]; move=>[rs [ [ Hv Heq] _] ] {m w k}; move: Hv Heq.
      move: (comp_map _)=> [rsx rsg] [Hv _] {rs}; move: Hv.
      rewrite ra_op_prod_fst 2![fst _]/=.
      by case: ux; case: rsx; auto.
    Qed.

  End WorldSatisfaction.

  (* Simple view lemma. *)
  Lemma wsatM {σ m} {r : res} {w n k} (HLe : k <= n) :
    wsat σ m r w n -> wsat σ m r w k.
  Proof. by exact: (dpred HLe). Qed.

  Section PrimitiveViewShifts.
    Local Obligation Tactic := intros.

    Program Definition preVS m1 m2 P w : UPred res :=
      mkUPred (fun n r => forall w1 (rf: res) mf σ k (HSub : w ⊑ w1) (HLe : k < n)
                                 (HD : mf # m1 ∪ m2)
                                 (HE : wsat σ (m1 ∪ mf) (r · rf) w1 (S k)),
                          exists w2 r',
                            w1 ⊑ w2 /\ P w2 (S k) r'
                            /\ wsat σ (m2 ∪ mf) (r' · rf) w2 (S k)) _.
    Next Obligation.
      intros n1 n2 r1 r2 HLe [rd HR] HP; intros.
      destruct (HP w1 (rd · rf) mf σ k) as [w2 [r1' [HW [HP' HE'] ] ] ];
        try assumption; [now eauto with arith | |].
      - eapply wsat_equiv, HE; try reflexivity.
        rewrite ->assoc, (comm r1), HR; reflexivity.
      - rewrite ->assoc, (comm r1') in HE'.
        exists w2 (rd · r1').
        split; [assumption | split; [| assumption] ].
        eapply uni_pred, HP'; [reflexivity|]. exists rd. reflexivity.
    Qed.

    Program Definition pvs m1 m2 : Props -n> Props :=
      n[(fun P => m[(preVS m1 m2 P)])].
    Next Obligation.
      intros w1 w2 EQw n' r HLt; destruct n as [| n]; [now inversion HLt |]; split; intros HP w2'; intros.
      - symmetry in EQw; assert (HDE := extend_dist EQw HSub).
        assert (HSE := extend_sub EQw HSub); specialize (HP (extend w2' w1)).
        edestruct HP as [w1'' [r' [HW HH] ] ]; try eassumption; clear HP; [ | ].
        + eapply wsat_dist, HE; [symmetry; eassumption | omega].
        + symmetry in HDE; assert (HDE' := extend_dist HDE HW).
          assert (HSE' := extend_sub HDE HW); destruct HH as [HP HE'];
          exists (extend w1'' w2') r'; split; [assumption | split].
          * eapply (met_morph_nonexp P), HP ; [symmetry; eassumption | omega].
          * eapply wsat_dist, HE'; [symmetry; eassumption | omega].
      - assert (HDE := extend_dist EQw HSub); assert (HSE := extend_sub EQw HSub); specialize (HP (extend w2' w2)).
        edestruct HP as [w1'' [r' [HW HH] ] ]; try eassumption; clear HP; [ | ].
        + eapply wsat_dist, HE; [symmetry; eassumption | omega].
        + symmetry in HDE; assert (HDE' := extend_dist HDE HW).
          assert (HSE' := extend_sub HDE HW); destruct HH as [HP HE'];
          exists (extend w1'' w2') r'; split; [assumption | split].
          * eapply (met_morph_nonexp P), HP ; [symmetry; eassumption | omega].
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

  End PrimitiveViewShifts.


  Section WeakestPre.

    (* RJ this should now be captured by the generic instance for discrete metrics.
    Instance LP_isval : LimitPreserving is_value.
    Proof.
      intros σ σc HC; apply HC.
    Qed. *)

    Local Obligation Tactic := intros; eauto with typeclass_instances.

    Definition safeExpr e σ :=
      is_value e \/
         (exists σ' ei ei' K, e = fill K ei /\ prim_step (ei, σ) (ei', σ')) \/
         (exists e' K, e = fill K (fork e')).

    (* Show that this definition makes some sense *)
    Lemma tp_safe e tp σ
          (SAFE  : safeExpr e σ)
          (INPOOL: e ∈ tp):
      is_value e \/ exists tp' σ', step (tp, σ) (tp', σ').
    Proof.
      apply List.in_split in INPOOL.
      destruct INPOOL as [tp1 [tp2 Htp]].
      destruct SAFE as [Hval|[ [σ' [ei [ei' [K [Hfill Hstep]]]]] | [e' [K Hfill]] ]].
      - left. assumption.
      - right; do 2 eexists. eapply step_atomic.
        + eassumption.
        + rewrite Htp Hfill. reflexivity.
        + reflexivity.
      - right; do 2 eexists. eapply step_fork.
        + rewrite Htp Hfill. reflexivity.
        + reflexivity.
    Qed.

    Definition wpFP safe m (WP : expr -n> vPred -n> Props) e φ w n r :=
      forall w' k rf mf σ (HSw : w ⊑ w') (HLt : k < n) (HD : mf # m)
             (HE : wsat σ (m ∪ mf) (r · rf) w' (S k)),
        (forall (HV : is_value e),
         exists w'' r', w' ⊑ w'' /\ φ (exist _ e HV) w'' (S k) r'
                           /\ wsat σ (m ∪ mf) (r' · rf) w'' (S k)) /\
        (forall σ' ei ei' K (HDec : e = fill K ei)
                (HStep : prim_step (ei, σ) (ei', σ')),
         exists w'' r', w' ⊑ w'' /\ WP (fill K ei') φ w'' k r'
                           /\ wsat σ' (m ∪ mf) (r' · rf) w'' k) /\
        (forall e' K (HDec : e = fill K (fork e')),
         exists w'' rfk rret, w' ⊑ w''
                                 /\ WP (fill K fork_ret) φ w'' k rret
                                 /\ WP e' (umconst ⊤) w'' k rfk
                                 /\ wsat σ (m ∪ mf) (rfk · rret · rf) w'' k) /\
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
        rewrite ->assoc, (comm r1') in HE'.
        exists w'' (rd · r1').
        split; [assumption | split; [| assumption] ].
        eapply uni_pred, Hφ; [| exists rd]; reflexivity.
      - specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r1' [HSw' [HWP HE']]]].
        rewrite ->assoc, (comm r1') in HE'. exists w''.
        destruct k as [| k]; [exists r1'; simpl wsat; tauto |].
        exists (rd · r1').
        split; [assumption | split; [| assumption] ].
        eapply uni_pred, HWP; [| exists rd]; reflexivity.
      - specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret1 [HSw' [HWR [HWF HE']]]]]].
        destruct k as [| k]; [exists w'' rfk rret1; simpl wsat; tauto |].
        rewrite ->assoc, <- (assoc rfk) in HE'.
        exists w''. exists rfk (rd · rret1).
        repeat (split; try assumption).
        + eapply uni_pred, HWR; [| exists rd]; reflexivity.
        + clear -HE'. rewrite ->(comm _ rd) in HE'. exact HE'.
      - auto.
    Qed.
    Next Obligation.
      intros w1 w2 EQw n' r HLt; simpl; destruct n as [| n]; [now inversion HLt |]; split; intros Hp w2'; intros.
      - symmetry in EQw; assert (EQw' := extend_dist EQw HSw); assert (HSw' := extend_sub EQw HSw); symmetry in EQw'.
        edestruct (Hp (extend w2' w1)) as [HV [HS [HF HS'] ] ]; try eassumption;
        [eapply wsat_dist, HE; [eassumption | omega] |].
        split; [clear HS HF | split; [clear HV HF | split; clear HV HS; [| clear HF ]]]; intros.
        + specialize (HV HV0); destruct HV as [w1'' [r' [HSw'' [Hφ HE'] ] ] ].
          assert (EQw'' := extend_dist EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub EQw' HSw'').
          exists (extend w1'' w2') r'; split; [assumption |].
          split; [| eapply wsat_dist, HE'; [eassumption | omega] ].
          eapply (met_morph_nonexp (φ _)), Hφ; [eassumption | omega].
        + specialize (HS _ _ _ _ HDec HStep); destruct HS as [w1'' [r' [HSw'' [HWP HE']]]].
          assert (EQw'' := extend_dist EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub EQw' HSw'').
          exists (extend w1'' w2') r'; split; [assumption |].
          split; [| eapply wsat_dist, HE'; [eassumption | omega] ].
          eapply (met_morph_nonexp (WP _ _)), HWP; [eassumption | omega].
        + specialize (HF _ _ HDec); destruct HF as [w1'' [rfk [rret [HSw'' [HWR [HWF HE']]]]]].
          assert (EQw'' := extend_dist EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub EQw' HSw'').
          exists (extend w1'' w2') rfk rret; split; [assumption |].
          split; [| split; [| eapply wsat_dist, HE'; [eassumption | omega] ] ];
          eapply (met_morph_nonexp (WP _ _)); try eassumption; omega.
        + auto.
      - assert (EQw' := extend_dist EQw HSw); assert (HSw' := extend_sub EQw HSw); symmetry in EQw'.
        edestruct (Hp (extend w2' w2)) as [HV [HS [HF HS'] ] ]; try eassumption;
        [eapply wsat_dist, HE; [eassumption | omega] |].
        split; [clear HS HF | split; [clear HV HF | split; clear HV HS; [| clear HF] ] ]; intros.
        + specialize (HV HV0); destruct HV as [w1'' [r' [HSw'' [Hφ HE'] ] ] ].
          assert (EQw'' := extend_dist EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub EQw' HSw'').
          exists (extend w1'' w2') r'; split; [assumption |].
          split; [| eapply wsat_dist, HE'; [eassumption | omega] ].
          eapply (met_morph_nonexp (φ _)), Hφ; [eassumption | omega].
        + specialize (HS _ _ _ _ HDec HStep); destruct HS as [w1'' [r' [HSw'' [HWP HE']]]].
          assert (EQw'' := extend_dist EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub EQw' HSw'').
          exists (extend w1'' w2') r'; split; [assumption |].
          split; [| eapply wsat_dist, HE'; [eassumption | omega] ].
          eapply (met_morph_nonexp (WP _ _)), HWP; [eassumption | omega].
        + specialize (HF _ _ HDec); destruct HF as [w1'' [rfk [rret [HSw'' [HWR [HWF HE']]]]]].
          assert (EQw'' := extend_dist EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub EQw' HSw'').
          exists (extend w1'' w2') rfk rret; split; [assumption |].
          split; [| split; [| eapply wsat_dist, HE'; [eassumption | omega] ] ];
          eapply (met_morph_nonexp (WP _ _)); try eassumption; omega.
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
          eapply (met_morph_nonexp (WP _)), Hφ; [symmetry; eassumption | omega].
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [HSw' [HWR [HWF HE'] ] ] ] ] ].
          exists w'' rfk rret ; repeat (split; try assumption); [].
          eapply (met_morph_nonexp (WP _)), HWR; [symmetry; eassumption | omega].
        + auto.
      - split; [| split; [| split] ]; intros.
        + clear HS HF; specialize (HV HV0); destruct HV as [w'' [r' [HSw' [Hφ HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          apply EQφ, Hφ; omega.
        + clear HV HF; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [HSw' [Hφ HE'] ] ] ].
          exists w'' r'; split; [assumption | split; [| assumption] ].
          eapply (met_morph_nonexp (WP _)), Hφ; [eassumption | omega].
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [HSw' [HWR [HWF HE'] ] ] ] ] ].
          exists w'' rfk rret; repeat (split; try assumption); [].
          eapply (met_morph_nonexp (WP _)), HWR; [eassumption | omega].
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

    Global Opaque wp.

    Lemma wpO {safe m e φ w r} : wp safe m e φ w O r.
    Proof.
      rewrite unfold_wp; intros w'; intros; now inversion HLt.
    Qed.

  End WeakestPre.

  Section DerivedForms.
    (* There will be no base rules concerning these derived forms - but there's a bunch of derived rules in iris_derived_rules.v *)

    Definition vs m1 m2 P Q : Props :=
      □(P → pvs m1 m2 Q).

    Global Instance vsProper m1 m2: Proper (equiv ==> equiv ==> equiv) (vs m1 m2).
    Proof.
      move=>P1 P2 EQP Q1 Q2 EQQ. unfold vs. rewrite EQP EQQ. reflexivity.
    Qed.

    Definition ht safe m P e Q := □(P → wp safe m e Q).

    Global Instance ht_proper safe m: Proper (equiv ==> equiv ==> equiv ==> equiv) (ht safe m).
    Proof.
      move=> P0 P1 HEQP e0 e1 HEQe Q0 Q1 HEQQ.
      (* TODO these rewrites are *slow* *)
      unfold ht. rewrite HEQe. rewrite HEQP. rewrite HEQQ.
      reflexivity.
    Qed.

  End DerivedForms.

End IRIS_PLOG.

Module IrisPlog (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) : IRIS_PLOG RL C R WP CORE.
  Include IRIS_PLOG RL C R WP CORE.
End IrisPlog.
