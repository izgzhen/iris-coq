Require Import ssreflect.
Require Import world_prop core_lang lang masks iris_core.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Bullet Behavior "Strict Subproofs".

(* This enriches the Iris core logic with program logic features:
   Invariants, View Shifts, and Hoare Triples. The last two make use
   of a notion of "world satisfaction" (which you can also think of
   as the erasure from logical states to physical ones). *)
Module Type IRIS_PLOG (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP).
  Export CORE.
  Module Export L  := Lang C.

  Local Open Scope lang_scope.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.
  
  Implicit Types (P : Props) (w : Wld) (n i k : nat) (m : mask) (r u v : res) (σ : state) (φ : vPred).

  Section Invariants.

    (** Invariants **)
    Definition invP i P w : UPred res :=
      intEqP (w i) (Some (ı' P)).
    Program Definition inv i : Props -n> Props :=
      n[(fun P => m[(invP i P)])].
    Next Obligation.
      intros w1 w2 EQw; unfold invP; simpl morph.
      destruct n; [apply dist_bound |].
      apply intEq_dist; [apply EQw | reflexivity].
    Qed.
    Next Obligation.
      intros w1 w2 Sw; unfold invP; simpl morph.
      intros n r HP; do 2 red; specialize (Sw i); do 2 red in HP.
      destruct (w1 i) as [μ1 |]; [| contradiction].
      destruct (w2 i) as [μ2 |]; [| contradiction]; simpl in Sw.
      rewrite <- Sw; assumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w; unfold invP; simpl morph.
      apply intEq_dist; [reflexivity |].
      apply dist_mono, (met_morph_nonexp _ _ ı'), EQp.
    Qed.

  End Invariants.

  Section WorldSatisfaction.

    (* First, we need to compose the resources of a finite map. This won't be pretty, for
       now, since the library does not provide enough
       constructs. Hopefully we can provide a fold that'd work for
       that at some point
     *)
    Fixpoint comp_list (xs : list res) : res :=
      match xs with
        | nil => 1
        | (x :: xs)%list => x · comp_list xs
      end.

    Lemma comp_list_app rs1 rs2 :
      comp_list (rs1 ++ rs2) == comp_list rs1 · comp_list rs2.
    Proof.
      induction rs1; simpl comp_list; [now rewrite ->ra_op_unit by apply _ |].
      now rewrite ->IHrs1, assoc.
    Qed.

    Definition cod (m : nat -f> res) : list res := List.map snd (findom_t m).
    Definition comp_map (m : nat -f> res) : res := comp_list (cod m).

    Lemma comp_map_remove (rs : nat -f> res) i r (HLu : rs i == Some r) :
      comp_map rs == r · comp_map (fdRemove i rs).
    Proof.
      destruct rs as [rs rsP]; unfold comp_map, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [contradiction |]; simpl comp_list; simpl in HLu.
      destruct (comp i j); [red in HLu; rewrite-> HLu; reflexivity | contradiction |].
      simpl comp_list; rewrite ->IHrs by eauto using SS_tail.
      rewrite-> !assoc, (comm s). reflexivity.
    Qed.

    Lemma comp_map_insert_new (rs : nat -f> res) i r (HNLu : rs i == None) :
      r · comp_map rs == comp_map (fdUpdate i r rs).
    Proof.
      destruct rs as [rs rsP]; unfold comp_map, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [reflexivity | simpl comp_list; simpl in HNLu].
      destruct (comp i j); [contradiction | reflexivity |].
      simpl comp_list; rewrite <- IHrs by eauto using SS_tail.
      rewrite-> !assoc, (comm r); reflexivity.
    Qed.

    Lemma comp_map_insert_old (rs : nat -f> res) i r1 r2 r
          (HLu : rs i == Some r1) (HEq : r1 · r2 == r):
      r2 · comp_map rs == comp_map (fdUpdate i r rs).
    Proof.
      destruct rs as [rs rsP]; unfold comp_map, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [contradiction |]; simpl comp_list; simpl in HLu.
      destruct (comp i j); [red in HLu; rewrite-> HLu; clear HLu | contradiction |].
      - simpl comp_list; rewrite ->assoc, (comm r2), <- HEq; reflexivity.
      - simpl comp_list; rewrite <- IHrs by eauto using SS_tail.
        rewrite-> !assoc, (comm r2); reflexivity.
    Qed.

    (* When is a resource okay with a state? *)
    Definition res_sat (r: res) σ: Prop := ↓r /\ fst r == ex_own state σ.

    Global Instance res_sat_dist : Proper (equiv ==> equiv ==> iff) res_sat.
    Proof.
      intros [ [s1| |] r1] [ [s2| |] r2] [EQs EQr] σ1 σ2 EQσ; unfold res_sat; simpl in *; try tauto; try rewrite !EQs; try rewrite !EQr; try rewrite !EQσ; reflexivity.
    Qed.

    Global Instance preo_unit : preoType () := disc_preo ().

    Program Definition wsat σ m (r : res) w : UPred () :=
      ▹ (mkUPred (fun n _ => exists rs : nat -f> res,
                    res_sat (r · (comp_map rs)) σ
                      /\ forall i (Hm : m i),
                           (i ∈ dom rs <-> i ∈ dom w) /\
                           forall π ri (HLw : w i == Some π) (HLrs : rs i == Some ri),
                             ı π w n ri) _).
    Next Obligation.
      intros n1 n2 _ _ HLe _ [rs [HLS HRS] ]. exists rs; split; [assumption|].
      setoid_rewrite HLe; eassumption.
    Qed.

    Global Instance wsat_equiv σ : Proper (meq ==> equiv ==> equiv ==> equiv) (wsat σ).
    Proof.
      intros m1 m2 EQm r r' EQr w1 w2 EQw [| n] []; [reflexivity |].
      split; intros [rs [HE HM] ]; exists rs.
      - split; [rewrite <-EQr; assumption | intros; apply EQm in Hm; split; [| setoid_rewrite <- EQw; apply HM, Hm] ].
        destruct (HM _ Hm) as [HD _]; rewrite HD; clear - EQw.
        rewrite fdLookup_in; setoid_rewrite EQw; rewrite <- fdLookup_in; reflexivity.
      - split; [rewrite EQr; assumption | intros; apply EQm in Hm; split; [| setoid_rewrite EQw; apply HM, Hm] ].
        destruct (HM _ Hm) as [HD _]; rewrite HD; clear - EQw.
        rewrite fdLookup_in; setoid_rewrite <- EQw; rewrite <- fdLookup_in; reflexivity.
    Qed.

    Global Instance wsat_dist n σ m u : Proper (dist n ==> dist n) (wsat σ m u).
    Proof.
      intros w1 w2 EQw [| n'] [] HLt; [reflexivity |]; destruct n as [| n]; [now inversion HLt |].
      split; intros [rs [HE HM] ]; exists rs.
      - split; [assumption | split; [rewrite <- (domeq _ _ _ EQw); apply HM, Hm |] ].
        intros; destruct (HM _ Hm) as [_ HR]; clear HE HM Hm.
        assert (EQπ := EQw i); rewrite-> HLw in EQπ; clear HLw.
        destruct (w1 i) as [π' |]; [| contradiction]; do 3 red in EQπ.
        apply ı in EQπ; apply EQπ; [now auto with arith |].
        apply (met_morph_nonexp _ _ (ı π')) in EQw; apply EQw; [omega |].
        apply HR; [reflexivity | assumption].
      - split; [assumption | split; [rewrite (domeq _ _ _ EQw); apply HM, Hm |] ].
        intros; destruct (HM _ Hm) as [_ HR]; clear HE HM Hm.
        assert (EQπ := EQw i); rewrite-> HLw in EQπ; clear HLw.
        destruct (w2 i) as [π' |]; [| contradiction]; do 3 red in EQπ.
        apply ı in EQπ; apply EQπ; [now auto with arith |].
        apply (met_morph_nonexp _ _ (ı π')) in EQw; apply EQw; [omega |].
        apply HR; [reflexivity | assumption].
    Qed.

    Lemma wsat_valid σ m (r: res) w k :
      wsat σ m r w (S k) tt -> ↓r.
    Proof.
      intros [rs [HD _] ]. destruct HD as [VAL _].
      eapply ra_op_valid; [now apply _|]. eassumption.
    Qed.

  End WorldSatisfaction.

  Notation " P @ k " := ((P : UPred ()) k tt) (at level 60, no associativity).

  (*
	Simple monotonicity tactics for props and wsat.

	The tactic propsM H proves P w' n' r' given H : P w n r when
		w ⊑ w', n' <= n, r ⊑ r'
	are immediate.

	The tactic wsatM is similar.
   *)

  Lemma propsM {P w n r w' n' r'}
      (HP : P w n r) (HSw : w ⊑ w') (HLe : n' <= n) (HSr : r ⊑ r') :
    P w' n' r'.
  Proof. by apply: (mu_mono _ _ P _ _ HSw); exact: (uni_pred _ _ _ _ _ HLe HSr). Qed.

  Ltac propsM H := solve [ done | apply (propsM H); solve [ done | reflexivity | omega ] ].

  Lemma wsatM {σ m} {r : res} {w n k}
      (HW : wsat σ m r w @ n) (HLe : k <= n) :
    wsat σ m r w @ k.
  Proof. by exact: (uni_pred _ _ _ _ _ HLe). Qed.

  Ltac wsatM H := solve [done | apply (wsatM H); solve [done | omega] ].

  Section ViewShifts.
    Local Obligation Tactic := intros.

    Program Definition preVS m1 m2 P w : UPred res :=
      mkUPred (fun n r => forall w1 (rf: res) mf σ k (HSub : w ⊑ w1) (HLe : k < n)
                                 (HD : mf # m1 ∪ m2)
                                 (HE : wsat σ (m1 ∪ mf) (r · rf) w1 @ S k),
                          exists w2 r',
                            w1 ⊑ w2 /\ P w2 (S k) r'
                            /\ wsat σ (m2 ∪ mf) (r' · rf) w2 @ S k) _.
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
      - symmetry in EQw; assert (HDE := extend_dist _ _ _ _ EQw HSub).
        assert (HSE := extend_sub _ _ _ _ EQw HSub); specialize (HP (extend w2' w1)).
        edestruct HP as [w1'' [r' [HW HH] ] ]; try eassumption; clear HP; [ | ].
        + eapply wsat_dist, HE; [symmetry; eassumption | omega].
        + symmetry in HDE; assert (HDE' := extend_dist _ _ _ _ HDE HW).
          assert (HSE' := extend_sub _ _ _ _ HDE HW); destruct HH as [HP HE'];
          exists (extend w1'' w2') r'; split; [assumption | split].
          * eapply (met_morph_nonexp _ _ P), HP ; [symmetry; eassumption | omega].
          * eapply wsat_dist, HE'; [symmetry; eassumption | omega].
      - assert (HDE := extend_dist _ _ _ _ EQw HSub); assert (HSE := extend_sub _ _ _ _ EQw HSub); specialize (HP (extend w2' w2)).
        edestruct HP as [w1'' [r' [HW HH] ] ]; try eassumption; clear HP; [ | ].
        + eapply wsat_dist, HE; [symmetry; eassumption | omega].
        + symmetry in HDE; assert (HDE' := extend_dist _ _ _ _ HDE HW).
          assert (HSE' := extend_sub _ _ _ _ HDE HW); destruct HH as [HP HE'];
          exists (extend w1'' w2') r'; split; [assumption | split].
          * eapply (met_morph_nonexp _ _ P), HP ; [symmetry; eassumption | omega].
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

    Definition vs m1 m2 P Q : Props :=
      □(P → pvs m1 m2 Q).

  End ViewShifts.


  Section HoareTriples.
  (* Quadruples, really *)

    Instance LP_isval : LimitPreserving is_value.
    Proof.
      intros σ σc HC; apply HC.
    Qed.

    Local Obligation Tactic := intros; eauto with typeclass_instances.

    Definition safeExpr e σ :=
      is_value e \/
         (exists σ' ei ei' K, e = K [[ ei ]] /\ prim_step (ei, σ) (ei', σ')) \/
         (exists e' K, e = K [[ fork e' ]]).

    Definition wpFP safe m (WP : expr -n> vPred -n> Props) e φ w n r :=
      forall w' k rf mf σ (HSw : w ⊑ w') (HLt : k < n) (HD : mf # m)
             (HE : wsat σ (m ∪ mf) (r · rf) w' @ S k),
        (forall (HV : is_value e),
         exists w'' r', w' ⊑ w'' /\ φ (exist _ e HV) w'' (S k) r'
                           /\ wsat σ (m ∪ mf) (r' · rf) w'' @ S k) /\
        (forall σ' ei ei' K (HDec : e = K [[ ei ]])
                (HStep : prim_step (ei, σ) (ei', σ')),
         exists w'' r', w' ⊑ w'' /\ WP (K [[ ei' ]]) φ w'' k r'
                           /\ wsat σ' (m ∪ mf) (r' · rf) w'' @ k) /\
        (forall e' K (HDec : e = K [[ fork e' ]]),
         exists w'' rfk rret, w' ⊑ w''
                                 /\ WP (K [[ fork_ret ]]) φ w'' k rret
                                 /\ WP e' (umconst ⊤) w'' k rfk
                                 /\ wsat σ (m ∪ mf) (rfk · rret · rf) w'' @ k) /\
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
      - specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r1' [HSw' [HWP HE'] ] ] ].
        rewrite ->assoc, (comm r1') in HE'. exists w''.
        destruct k as [| k]; [exists r1'; simpl wsat; tauto |].
        exists (rd · r1').
        split; [assumption | split; [| assumption] ].
        eapply uni_pred, HWP; [| exists rd]; reflexivity.
      - specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret1 [HSw' [HWR [HWF HE'] ] ] ] ] ].
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

    Lemma wpO {safe m e φ w r} : wp safe m e φ w O r.
    Proof.
      rewrite unfold_wp; intros w'; intros; now inversion HLt.
    Qed.

    Definition ht safe m P e Q := □(P → wp safe m e Q).

  End HoareTriples.

End IRIS_PLOG.

Module IrisPlog (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) : IRIS_PLOG RL C R WP CORE.
  Include IRIS_PLOG RL C R WP CORE.
End IrisPlog.
