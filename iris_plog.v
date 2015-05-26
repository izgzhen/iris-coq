Require Import Ssreflect.ssreflect Omega.
Require Import world_prop core_lang lang iris_core.
Require Import ModuRes.DecEnsemble ModuRes.RA ModuRes.CMRA ModuRes.SPred ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.RAConstr ModuRes.Agreement ModuRes.Lists.

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
  Local Open Scope de_scope.
  
  Implicit Types (P : Props) (u v w : Wld) (n i k : nat) (m : DecEnsemble nat) (r : res) (σ : state) (φ : vPred) (s : nat -f> Wld).

  Section WorldSatisfaction.

    (* First, we need to compose the resources of a finite map. *)
    Definition comp_finmap w0 m : (nat -f> Wld) -> Wld :=
      fdFold w0 (fun k w' wt => if k ∈ m then wt · w' else wt).

    Global Instance comp_finmap_nexp n: Proper (dist n ==> equiv ==> dist n ==> dist n) comp_finmap.
    Proof.
      move=>w01 w02 EQw0 m1 m2 EQm s1 s2 EQs. rewrite /comp_finmap.
      etransitivity.
      - eapply fdFoldExtP_dist; last eexact EQs.
        + move=>k1 k2 w1 w2 w. unfold compose. rewrite (EQm k1) (EQm k2)=>{EQm m1}.
          destruct (k2 ∈ m2), (k1 ∈ m2); try reflexivity; rewrite -assoc (comm w2) assoc; reflexivity.
        + move=>k k' EQk w1 w2 EQw wt1 wt2 EQwt. subst k'. destruct (k ∈ m1).
          * apply cmra_op_dist; assumption.
          * assumption.
      - eapply fdFoldExtT.
        + move=>k k' EQk w1 w2 EQw wt1 wt2 EQwt. subst k' w2. destruct (k ∈ m1).
          * apply cmra_op_dist; reflexivity || assumption.
          * assumption.
        + move=>k v t. apply dist_refl. rewrite (EQm k). reflexivity.
        + assumption.
    Qed.

    Lemma comp_finmap_chmask w0 m (f: nat -f> Wld) i b:
      ~List.In i (dom f) ->
      comp_finmap w0 m f = comp_finmap w0 (de_set m i b) f.
    Proof.
      move=>Hnin. rewrite /comp_finmap !fdFoldBehavior /fdFold'.
      eapply fold_ext_restr; try reflexivity; [].
      move=>k' w Hdom.
      rewrite /fdFold'Inner. destruct (f k'); last reflexivity.
      destruct (dec_eq i k') as [EQ|NEQ].
      { subst k'. contradiction. }
      erewrite de_set_neq by assumption. reflexivity.
    Qed.

    Global Instance comp_finmap_ext: Proper (equiv ==> equiv ==> equiv ==> equiv) comp_finmap.
    Proof.
      move=>w01 w02 EQw0 m1 m2 EQm s1 s2 EQs. apply dist_refl=>n.
      apply comp_finmap_nexp; assumption || apply dist_refl; assumption.
    Qed.

    Lemma comp_finmap_remove w0 m (s: nat -f> Wld) i w:
      i ∈ m = true -> s i == Some w ->
      comp_finmap w0 m s == comp_finmap w0 (de_set m i false) s · w.
    Proof.
      revert s i w. rewrite /comp_finmap. apply:fdRect.
      - move=>s1 s2 EQw EQd IH i w Hindom Hw.
        etransitivity; last (etransitivity; first eapply IH).
        + rewrite /comp_finmap. apply equivR.
          symmetry. apply fdFoldExtF; assumption.
        + eexact Hindom.
        + rewrite EQw. eassumption.
        + rewrite /comp_finmap. apply equivR. f_equal.
          apply fdFoldExtF; assumption.
      - move=>? ? _ [].
      - move=>k v f Hnew IH i w Hindom Hw.
        rewrite /comp_finmap. erewrite !fdFoldUpdate by assumption.
        destruct (dec_eq i k) as [EQ|NEQ].
        { subst i. rewrite Hindom. rewrite de_set_eq.
          rewrite fdStrongUpdate_eq in Hw.
          change (v == w) in Hw. rewrite Hw. clear v Hw.
          apply ra_op_proper; last reflexivity.
          apply equivR. exact:comp_finmap_chmask. }
        erewrite de_set_neq by assumption.
        destruct (k ∈ m) eqn:EQm.
        + rewrite -assoc (comm v) assoc. apply ra_op_proper; last reflexivity.
          eapply IH; first assumption.
          erewrite <-Hw. rewrite fdStrongUpdate_neq; first reflexivity.
          move=>EQ. subst k. now apply NEQ.
        + eapply IH; first assumption.
          erewrite <-Hw. rewrite fdStrongUpdate_neq; first reflexivity.
          move=>EQ. subst k. now apply NEQ.
    Qed.

    Lemma comp_finmap_move w0 w1 f m:
      comp_finmap (w0 · w1) m f == comp_finmap w0 m f · w1.
    Proof.
      rewrite /comp_finmap. revert f. apply:fdRect.
      - move=>f1 f2 EQk EQdom IH.
        etransitivity; last (etransitivity; first eapply IH).
        + apply equivR. symmetry. apply fdFoldExtF; assumption.
        + apply ra_op_proper; last reflexivity.
          apply equivR. apply fdFoldExtF; assumption.
      - rewrite !fdFoldEmpty. reflexivity.
      - move=>k v f Hnew IH. erewrite !fdFoldUpdate by assumption.
        destruct (k ∈ m).
        + rewrite -assoc (comm v) assoc. apply ra_op_proper; last reflexivity.
          eapply IH.
        + eapply IH.
    Qed.

    Lemma comp_finmap_add w0 s m i w:
      (i ∈ m <> true \/ s i == None) ->
      comp_finmap w0 m s · w == comp_finmap w0 (de_set m i true) (fdStrongUpdate i (Some w) s).
    Proof.
      revert s. apply:fdRect.
      - move=>f1 f2 EQk EQdom IH Hnew. rewrite /comp_finmap. 
        etransitivity; last (etransitivity; first eapply IH).
        + apply ra_op_proper; last reflexivity.
          apply equivR. symmetry. apply fdFoldExtF; assumption.
        + destruct Hnew; first (left; assumption). right.
          rewrite EQk. assumption.
        + apply equivR. apply fdFoldExtF.
          * move=>k. simpl. rewrite EQk. reflexivity.
          * rewrite /fdStrongUpdate /= /dom /=. rewrite /dom in EQdom.
            rewrite EQdom. reflexivity.
      - move=>Hnew. rewrite /comp_finmap fdFoldEmpty fdFoldUpdate.
        + rewrite de_set_eq !fdFoldEmpty. reflexivity.
        + move=>[].
      - move=>k v f Hnew IH Hfresh. destruct (dec_eq i k) as [EQ|NEQ].
        + subst k. rewrite fdStrongUpdateShadow /comp_finmap. erewrite fdFoldUpdate by assumption.
          destruct (i ∈ m) eqn:EQim.
          { exfalso. destruct Hfresh as [Hineq|Hl]; first now apply Hineq.
            rewrite fdStrongUpdate_eq in Hl. exact Hl. }
          clear Hfresh. erewrite fdFoldUpdate by assumption. rewrite de_set_eq.
          apply ra_op_proper; last reflexivity.
          apply equivR. exact:comp_finmap_chmask.
        + erewrite fdStrongUpdateCommute by assumption.
          erewrite fdStrongUpdate_neq in Hfresh by (now apply not_eq_sym).
          rewrite /comp_finmap fdFoldUpdate; last assumption. rewrite fdFoldUpdate; last first.
          { apply fdLookup_notin. erewrite fdStrongUpdate_neq by assumption.
            now apply fdLookup_notin. }
          unfold comp_finmap in IH.
          erewrite de_set_neq by assumption. destruct (k ∈ m).
          * rewrite -assoc (comm v) assoc. apply ra_op_proper; last reflexivity.
            apply IH. assumption.
          * apply IH. assumption.
    Qed.

    (* Go through some struggle to even write down world satisfaction... *)
    Local Open Scope finmap_scope.
    
    Lemma world_inv_val {w m} {s : nat -f> Wld} {n}:
      let wt := comp_finmap w m s in
      forall (pv: cmra_valid wt n) {i agP} (Heq: (Invs wt) i = Some agP), cmra_valid agP n.
    Proof.
      intros wt pv i agP Heq.
      destruct wt as [I O]. destruct pv as [HIval _]. specialize (HIval i).
      simpl Invs in Heq. destruct (I i).
      - eapply spredNE, HIval. apply cmra_valid_dist. inversion Heq. reflexivity.
      - discriminate.
    Qed.

    (* It may be possible to use "later_sp" here, but let's avoid indirections where possible. *)
    Definition wsatF σ m w n :=
      match n with
      | O => True
      | S n' => exists s : nat -f> Wld,
                  let wt := comp_finmap w m s in
                  exists pv : (cmra_valid wt n),
                    (State wt ⊑ ex_own σ) /\
                    forall i agP (Heq: (Invs wt) i = Some agP),
                      match s i with
                      | Some w => let P := ra_ag_unInj agP n (HVal:=world_inv_val pv Heq) in
                                  unhalved (ı P) w n'
                      | None => False
                      end
      end.

    Program Definition wsat σ m w : SPred :=
      mkSPred (wsatF σ m w) _ _.
    Next Obligation.
      intros n1 n2 HLe. destruct n2; first (intro; exact I).
      destruct n1; first (exfalso; omega).
      intros (s & pv & Hσ & H).
      exists s. exists (dpred (m := S n2) HLe pv).
      split; [assumption|]. move => {Hσ} i agP Heq.
      move:(H i agP Heq)=>{H}.
      destruct (s i) as [ws|]; last move=>[].
      move=>/= H.
      eapply spredNE; last first.
      - eapply dpred; last exact H. omega.
      - specialize (halve_eq (T:=Props) n2)=>Huneq. apply Huneq=>{Huneq H ws}.
        apply met_morph_nonexp. symmetry. apply ra_ag_unInj_move. omega.
    Qed.

    Global Instance wsat_dist n σ : Proper (equiv ==> dist n ==> dist n) (wsat σ).
    Proof.
      eapply dist_spred_simpl2; try apply _; [].
      intros m1 m2 w1 w2 m Hlt EQm EQw. destruct m; first reflexivity.
      destruct n as [| n]; [now inversion Hlt |].
      intros [s [pv [HS HI]]]; exists s; intro wt.
      assert (Hwt: comp_finmap w1 m1 s = S m = wt).
      { subst wt. rewrite EQm EQw. reflexivity. }
      assert (pv': cmra_valid wt (S m)).
      { eapply spredNE, pv. apply cmra_valid_dist. assumption. }
      exists pv'. split.
      { rewrite <-HS. apply pordR. destruct Hwt as [_ [HwtS _]].
        symmetry. exact HwtS. }
      move=>i agP Heq.
      edestruct (fdLookup_in_dist_strong (f2 := Invs (comp_finmap w1 m1 s)) (n:=m) Heq) as [agP' [Heq' HagPeq]].
      { rewrite -Hwt. reflexivity. }
      specialize (HI _ _ Heq'). destruct (s i); last exact HI.
      simpl. simpl in HI.
      eapply spredNE, HI.
      specialize (halve_eq (T:=Props) m)=>Huneq. apply Huneq=>{Huneq HS}.
      apply met_morph_nonexp. eapply ra_ag_unInj_dist.
      symmetry. assumption.
    Qed.

    Global Instance wsat_equiv σ : Proper (equiv ==> equiv ==> equiv) (wsat σ).
    Proof.
      move=> m1 m2 EQm w1 w2 EQw. apply dist_refl=>n.
      apply wsat_dist; (assumption || eapply dist_refl; eassumption).
    Qed.

    Lemma wsat_valid {σ m w k} :
      wsat σ m w k -> cmra_valid w k.
    Proof.
      destruct k; first (intro; exact:bpred).
      move=> [s [pv _]]. eapply cmra_op_valid2.
      eapply spredNE, pv.
      rewrite -{1}(ra_op_unit (t:=w)) comp_finmap_move.
      reflexivity.
    Qed.

(*    Lemma wsat_state {σ m u w k} :
      wsat σ m u w (S k) -> fst u == ex_own σ \/ fst u == 1.
    Proof.
      move: u=>[ux ug]; move=>[rs [ [ Hv Heq] _] ] {m w k}; move: Hv Heq.
      move: (comp_map _)=> [rsx rsg] [Hv _] {rs}; move: Hv.
      rewrite ra_op_prod_fst 2![fst _]/=.
      by case: ux; case: rsx; auto.
    Qed.*)

  End WorldSatisfaction.

  (* Simple view lemma. *)
  Lemma wsatM {σ m} {w n k} (HLe : k <= n) :
    wsat σ m w n -> wsat σ m w k.
  Proof. by exact: (dpred HLe). Qed.

  Section PrimitiveViewShifts.
    Local Obligation Tactic := intros.

    Program Definition preVS m1 m2 P w : SPred :=
      mkSPred (fun n => forall (wf: Wld) k mf σ (HLe : k < n)
                               (HD : mf # m1 ∪ m2)
                               (HE : wsat σ (m1 ∪ mf) (w · wf) (S k)),
                   exists w', P w' (S k)
                              /\ wsat σ (m2 ∪ mf) (w' · wf) (S k)) _ _.
    Next Obligation.
      inversion HLe.
    Qed.
    Next Obligation.
      intros n1 n2 HLe HP wf; intros.
      destruct (HP wf k mf σ) as [w2 [HP' HE'] ].
      - omega.
      - assumption.
      - assumption.
      - exists w2.
        split; assumption.
    Qed.

    Program Definition pvs m1 m2 : Props -n> Props :=
      n[(fun P => m[(preVS m1 m2 P)])].
    Next Obligation.
      apply dist_spred_simpl; try apply _; [].
      intros w1 w2 n' HLt EQw; destruct n as [| n]; [now inversion HLt |]. intros HV wf; intros.
      edestruct HV as [w1' [HP HE']]; try eassumption.
      - eapply wsat_dist, HE; first reflexivity.
        + eapply cmra_op_dist; last reflexivity. eexact EQw.
        + omega.
      - exists w1'. split; first assumption.
        eapply wsat_dist, HE'; try reflexivity; omega.
    Qed.
    Next Obligation.
      intros w1 w2 [wd EQw] n HV wf; intros.
      edestruct (HV (wd · wf) k mf) as [w1' [HP HE']]; try eassumption.
      - eapply wsat_dist, HE; try reflexivity.
        rewrite assoc (comm w1) EQw. reflexivity.
      - exists (w1' · wd). split.
        + eapply propsMW, HP. exists wd; now rewrite comm.
        + eapply wsat_dist, HE'; try reflexivity. now rewrite assoc.
    Qed.
    Next Obligation.
      apply dist_props_simpl; try apply _; [].
      intros p1 p2 w n' HLt EQp HV w1; intros.
      edestruct HV as [w2 [HP' HE']]; try eassumption; [].
      exists w2. split; last assumption.
      apply EQp; assumption || omega.
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
          (INPOOL: (e ∈ tp)%list):
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

    Definition wpFP safe m (WP : expr -n> vPred -n> Props) e φ w n :=
      forall wf k mf σ (HLt : k < n) (HD : mf # m)
             (HE : wsat σ (m ∪ mf) (w · wf) (S k)),
        (forall (HV : is_value e),
         exists w', φ (exist _ e HV) w' (S k)
                    /\ wsat σ (m ∪ mf) (w' · wf) (S k)) /\
        (forall σ' ei ei' K (HDec : e = fill K ei)
                (HStep : prim_step (ei, σ) (ei', σ')),
            exists w', WP (fill K ei') φ w' k
                       /\ wsat σ' (m ∪ mf) (w' · wf) k) /\
        (forall e' K (HDec : e = fill K (fork e')),
            exists wfk wret, WP (fill K fork_ret) φ wret k
                             /\ WP e' (umconst ⊤) wfk k
                             /\ wsat σ (m ∪ mf) (wfk · wret · wf) k) /\
        (forall HSafe : safe = true, safeExpr e σ).

    (* Define the function wp will be a fixed-point of *)
    Program Definition wpF safe m : (expr -n> vPred -n> Props) -> (expr -n> vPred -n> Props) :=
      fun WP => n[(fun e => n[(fun φ => m[(fun w => mkSPred (wpFP safe m WP e φ w) _ _)])])].
    Next Obligation.
      intro. intros. inversion HLt.
    Qed.
    Next Obligation.
      intros n1 n2 HLe Hwp wf k mf σ HLt HD HE.
      destruct (Hwp wf k mf σ) as [HV [HS [HF HS' ]]]; first omega; try assumption; [].
      split; [clear HS HF | split; [clear HV HF | split; clear HV HS; [| clear HF ] ] ]; intros.
      - specialize (HV HV0); destruct HV as [w'' [Hφ HE']].
        exists w''. split; assumption.
      - specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [HWP HE']].
        exists w''. split; assumption.
      - specialize (HF _ _ HDec); destruct HF as [wfk [wret [HWR [HWF HE']]]].
        exists wfk wret. split_conjs; assumption.
      - auto.
    Qed.
    Next Obligation.
      eapply dist_spred_simpl; first now apply _.
      intros w1 w2 n' HLt EQw; simpl; destruct n as [| n]; [now inversion HLt |]. intros Hwp wf; intros.
      edestruct (Hwp wf) as [HV [HS [HF HS'] ] ]; try eassumption;
      [eapply wsat_dist, HE; [reflexivity| eapply cmra_op_dist; eassumption || reflexivity |  omega] |].
      split; [clear HS HF | split; [clear HV HF | split; clear HV HS; [| clear HF ]]]; intros.
      - specialize (HV HV0); destruct HV as [w1'' [Hφ HE']]. exists w1''.
        split; assumption.
      - specialize (HS _ _ _ _ HDec HStep); destruct HS as [w1'' [HWP HE']]. exists w1''.
        split; assumption.
      - specialize (HF _ _ HDec); destruct HF as [wfk [wret [HWR [HWF HE']]]].
        exists wfk wret. split_conjs; assumption.
      - auto.
    Qed.
    Next Obligation.
      intros w1 w2 [wd EQw] n. simpl; intros Hwp wf; intros.
      edestruct (Hwp (wd · wf) k mf) as [HV [HS [HF HS'] ] ]; try assumption; [|].
      { eapply wsat_dist, HE; try reflexivity. now rewrite -EQw assoc (comm w1). }
      split; [clear HS HF | split; [clear HV HF | split; clear HV HS; [| clear HF ] ] ]; intros.
      - specialize (HV HV0); destruct HV as [w'' [Hφ HE']].
        exists (w'' · wd). split.
        + eapply propsMW, Hφ. exists wd; now rewrite comm.
        + eapply wsat_dist, HE'; try reflexivity. now rewrite assoc.
      - specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [HWP HE']].
        exists (w'' · wd). split.
        + eapply propsMW, HWP. exists wd; now rewrite comm.
        + eapply wsat_dist, HE'; try reflexivity. now rewrite assoc.
      - specialize (HF _ _ HDec); destruct HF as [wfk [wret [HWR [HWF HE']]]].
        exists wfk (wret · wd). split_conjs.
        + eapply propsMW, HWR. exists wd; now rewrite comm.
        + assumption.
        + eapply wsat_dist, HE'; try reflexivity. now rewrite !assoc.
      - auto.
    Qed.
    Next Obligation.
      eapply dist_props_simpl; first now apply _.
      intros φ1 φ2 w k HLt EQφ; simpl; destruct n as [| n]; [now inversion HLt |].
      intros Hp w'; intros; edestruct Hp as [HV [HS [HF HS'] ] ]; try eassumption; [].
      split; [clear HS HF | split; [clear HV HF | split; clear HV HS; [| clear HF ] ] ]; intros.
      - specialize (HV HV0); destruct HV as [w'' [Hφ HE']].
        exists w''. split; last assumption.
        apply EQφ, Hφ; omega.
      - specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [Hφ HE']].
        exists w''. split; last assumption.
        eapply (met_morph_nonexp (WP _)), Hφ; [symmetry; eassumption | omega].
      - specialize (HF _ _ HDec); destruct HF as [wfk [wret [HWR [HWF HE']]]].
        exists wfk wret. split; last tauto.
        eapply (met_morph_nonexp (WP _)), HWR; [symmetry; eassumption | omega].
      - auto.
    Qed.
    Next Obligation.
      intros e1 e2 EQe φ w. destruct n as [| n]; first exact:dist_bound.
      simpl in EQe; hnf in EQe; subst e2; reflexivity.
    Qed.

    Instance contr_wpF safe m : contractive (wpF safe m).
    Proof.
      intros n WP1 WP2 EQWP e φ w k HLt.
      split; intros Hp w'; intros; edestruct Hp as [HV [HS [HF HS'] ] ]; try eassumption; [|].
      - split; [assumption | split; [| split]; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [HWP HE']].
          exists w''; split; last assumption.
          eapply EQWP, HWP; omega.
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [wfk [wret [HWR [HWF HE']]]].
          exists wfk wret.
          split; [| split; [| assumption] ]; eapply EQWP; try eassumption; omega.
        + auto.
      - split; [assumption | split; [| split]; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [HWP HE']].
          exists w''; split; last assumption.
          eapply EQWP, HWP; omega.
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [wfk [wret [HWR [HWF HE']]]].
          exists wfk wret.
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

  End WeakestPre.

  Section DerivedForms.
    (* There will be no base rules concerning these derived forms - but there's a bunch of derived rules in iris_derived_rules.v *)

    Definition vs m1 m2 P Q : Props :=
      □(P → pvs m1 m2 Q).

    Global Instance vsProper m1 m2: Proper (equiv ==> equiv ==> equiv) (vs m1 m2).
    Proof.
      move=>P1 P2 EQP Q1 Q2 EQQ. unfold vs. apply morph_resp. apply impl_equiv; first assumption.
      now rewrite EQQ.
    Qed.

    Definition ht safe m P e Q := □(P → wp safe m e Q).

    Global Instance ht_proper safe m: Proper (equiv ==> equiv ==> equiv ==> equiv) (ht safe m).
    Proof.
      move=> P0 P1 HEQP e0 e1 HEQe Q0 Q1 HEQQ.
      (* TODO these rewrites are *slow* *)
      unfold ht. apply morph_resp. apply impl_equiv; first assumption.
      apply equiv_morph; last assumption.
      hnf in HEQe. subst e1. reflexivity.
    Qed.

  End DerivedForms.

  Global Opaque wp.

End IRIS_PLOG.

Module IrisPlog (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) : IRIS_PLOG RL C R WP CORE.
  Include IRIS_PLOG RL C R WP CORE.
End IrisPlog.
