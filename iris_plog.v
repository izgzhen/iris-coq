Require Import Ssreflect.ssreflect Ssreflect.ssrfun Omega.
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

  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.
  Local Open Scope de_scope.
  
  Implicit Types (P : Props) (u v w : Wld) (n i k : nat) (m : mask) (r : res) (σ : state) (φ : vPred) (s : nat -f> Wld).

  Section WorldSatisfaction.

    (* First, we need to compose the resources of a finite map. *)
    Definition comp_finmap w0 : (nat -f> Wld) -> Wld :=
      fdFold w0 (fun k w' wt => wt · w').

    Global Instance comp_finmap_dist n: Proper (dist n ==> dist n ==> dist n) comp_finmap.
    Proof.
      move=>w01 w02 EQw0 s1 s2 EQs. rewrite /comp_finmap.
      etransitivity.
      - eapply fdFoldExtP_dist; last eexact EQs.
        + move=>k1 k2 w1 w2 w. unfold compose.
          rewrite -assoc (comm w2) assoc; reflexivity.
        + move=>k k' EQk w1 w2 EQw wt1 wt2 EQwt.
          apply cmra_op_dist; assumption.
      - eapply fdFoldExtT.
        + move=>k k' EQk w1 w2 EQw wt1 wt2 EQwt. subst k' w2.
          apply cmra_op_dist; reflexivity || assumption.
        + move=>k v t. reflexivity.
        + assumption.
    Qed.

    Global Instance comp_finmap_ext: Proper (equiv ==> equiv ==> equiv) comp_finmap.
    Proof.
      move=>w01 w02 EQw0 s1 s2 EQs. apply dist_refl=>n.
      apply comp_finmap_dist; assumption || apply dist_refl; assumption.
    Qed.

    Lemma comp_finmap_remove w0 (s: nat -f> Wld) i w:
      s i == Some w ->
      comp_finmap w0 s == comp_finmap w0 (s \ i) · w.
    Proof.
      revert s i w. apply:fdRect.
      - move=>s1 s2 EQs IH i w Hindom.
        etransitivity; last (etransitivity; first eapply IH); first apply equivR; last apply equivR.
        + rewrite EQs. reflexivity.
        + destruct EQs as [EQw _]. rewrite (EQw i). eassumption.
        + f_equal. rewrite EQs. reflexivity.
      - move=>? ? [].
      - move=>k v f Hnew IH i w Hindom. destruct (dec_eq i k) as [EQ|NEQ].
        + subst i. clear IH. rewrite fdStrongUpdateShadow /comp_finmap.
          erewrite fdFoldAdd by assumption. rewrite fdStrongUpdate_eq in Hindom.
          simpl in Hindom. apply ra_op_proper; last assumption.
          symmetry. apply equivR. eapply fdFoldRedundantRemove. assumption.
        + erewrite fdStrongUpdateCommute by assumption.
          erewrite fdStrongUpdate_neq in Hindom by (now apply not_eq_sym). specialize (IH _ _ Hindom).
          rewrite /comp_finmap fdFoldAdd; last assumption. rewrite fdFoldAdd; last first.
          { apply fdLookup_notin. erewrite fdStrongUpdate_neq by assumption.
            apply fdLookup_notin. assumption. }
          rewrite -assoc (comm v) assoc. apply ra_op_proper; last reflexivity.
          rewrite /comp_finmap in IH. apply IH.
    Qed.

    Lemma comp_finmap_move w0 w1 f:
      comp_finmap (w0 · w1) f == w0 · comp_finmap w1 f.
    Proof.
      rewrite /comp_finmap. revert f. apply:fdRect.
      - move=>f1 f2 EQf IH.
        etransitivity; last (etransitivity; first eapply IH).
        + now rewrite EQf.
        + f_equiv. now rewrite EQf.
      - rewrite !fdFoldEmpty. reflexivity.
      - move=>k v f Hnew IH. erewrite !fdFoldAdd by assumption.
        rewrite assoc. apply ra_op_proper; last reflexivity.
        eapply IH.
    Qed.

    Lemma comp_finmap_add w0 s i w:
      s i == None ->
      comp_finmap w0 s · w == comp_finmap w0 (s + [fd  i  <- w] ).
    Proof.
      revert s. apply:fdRect.
      - move=>f1 f2 EQf IH Hnew. rewrite -{2}EQf. rewrite -IH=>{IH}; last first.
        { rewrite EQf. assumption. }
        f_equiv. rewrite /comp_finmap. rewrite EQf. reflexivity.
      - move=>Hnew. rewrite /comp_finmap fdFoldEmpty fdFoldAdd.
        + rewrite !fdFoldEmpty. reflexivity.
        + move=>[].
      - move=>k v f Hnew IH Hfresh. destruct (dec_eq i k) as [EQ|NEQ].
        + subst k. clear IH. rewrite fdStrongUpdateShadow /comp_finmap. erewrite fdFoldAdd by assumption.
          rewrite fdStrongUpdate_eq in Hfresh. destruct Hfresh.
        + erewrite fdStrongUpdateCommute by assumption.
          erewrite fdStrongUpdate_neq in Hfresh by (now apply not_eq_sym).
          rewrite /comp_finmap fdFoldAdd; last assumption. rewrite fdFoldAdd; last first.
          { apply fdLookup_notin. erewrite fdStrongUpdate_neq by assumption.
            now apply fdLookup_notin. }
          specialize (IH Hfresh). unfold comp_finmap in IH.
          rewrite -assoc (comm v) assoc. apply ra_op_proper; last reflexivity.
          apply IH.
    Qed.

    Lemma comp_finmap_le w0 s:
      w0 ⊑ comp_finmap w0 s.
    Proof.
      exists (comp_finmap (1 w0) s).
      rewrite comm -comp_finmap_move comm ra_op_unit. reflexivity.
    Qed.

    (** Now we define world satisfaction **)
    Lemma world_inv_val {wt n}:
      forall (pv: cmra_valid wt n) {i agP} (Heq: (Invs wt) i = n = Some agP), cmra_valid agP n.
    Proof.
      intros pv i agP Heq.
      destruct wt as [I O]. destruct pv as [HIval _]. specialize (HIval i).
      simpl Invs in Heq. destruct (I i).
      - eapply spredNE, HIval. apply cmra_valid_dist.
        destruct n; first exact:dist_bound.
        exact Heq.
      - destruct n; first exact:bpred. destruct Heq.
    Qed.

    (* RJ: Possible simplification: Could we match on (Invs wt i) instead of asking for
       a proof of an equality? The proofs end up having to reason about an equality
       anyway, so it may or may not end up actually simplifying anything. *)
    Definition wsatTotal n' σ (s: nat -f> Wld) m wt :=
      (cmra_valid wt (S n')) /\
      (State wt ⊑ ex_own σ) /\
      forall i agP (Heq: (Invs wt) i = S n' = Some agP),
        match (i ∈ m)%de, s i with
        | true , Some w => let P := ra_ag_unInj agP (S n') in unhalved (ı P) w n'
        | false, None   => True
        | _    , _      => False
        end.

    Global Instance wsatTotal_proper n' σ s:
      Proper (equiv ==> dist (S n') ==> equiv) (wsatTotal n' σ s).
    Proof.
      apply proper_sym_impl_iff_2; try apply _; [].
      move=>m1 m2 EQm wt1 wt2 EQwt. move=>[pv [HS HI]].
      split.
      { eapply spredNE, pv. apply cmra_valid_dist. assumption. }
      split.
      { rewrite <-HS. apply pordR. destruct EQwt as [_ [HwtS _]].
        symmetry. exact HwtS. }
      move=>i agP Heq.
      move:(HI i agP). case/(_ _)/Wrap; last move=>{HI} HI.
      { rewrite -Heq. rewrite EQwt. reflexivity. }
      rewrite -EQm. assumption.
    Qed.

    Lemma wsatTotal_dclosed n'1 n'2 σ s m wt:
      n'1 <= n'2 -> wsatTotal n'2 σ s m wt ->
      wsatTotal n'1 σ s m wt.
    Proof.
      intros HLe (pv & Hσ & H).
      assert (pv': cmra_valid wt (S n'1)).
      { eapply dpred, pv. omega. }
      split; first assumption.
      split; [assumption|]. move => {Hσ} i agP Heq.
      case HagP':(Invs wt i) => [agP'|]; last first.
      { exfalso. rewrite HagP' in Heq. exact Heq. }
      move:(H i agP'). case/(_ _)/Wrap; last move=>{H}.
      { now apply equivR. }
      destruct (s i) as [ws|], (i ∈ m)%de; simpl; tauto || (try contradiction); []=>H.
      eapply spredNE; last first.
      - eapply dpred; last exact H. omega.
      - specialize (halve_eq (T:=Props) n'1)=>Huneq. apply Huneq=>{Huneq H ws}.
        apply met_morph_nonexp. move:(Heq). rewrite HagP' in Heq=>Heq''.
        etransitivity.
        + symmetry. eapply ra_ag_unInj_move. omega.
          eapply world_inv_val; first eassumption. apply equivR. eassumption.
        + eapply ra_ag_unInj_dist; last assumption. 
          eapply world_invs_valid; first eexact pv'; first reflexivity.
          rewrite Heq. eassumption.
    Qed.  

    (* It may be possible to use "later_sp" here, but let's avoid indirections where possible. *)
    Program Definition wsat σ m w : SPred :=
      p[(fun n => match n return _ with
                  | S (S n') => exists s : nat -f> Wld,
                                           let wt := comp_finmap w s in
                                           wsatTotal (S n') σ s m wt
                  | _        => True
                  end)].
    Next Obligation.
      intros n1 n2 HLe. do 2 (destruct n2; first (intro; exact I)).
      do 2 (destruct n1; first (exfalso; omega)).
      intros (s & HWT). exists s.
      eapply wsatTotal_dclosed, HWT. omega.
    Qed.

    Global Instance wsat_dist n σ : Proper (equiv ==> dist n ==> dist n) (wsat σ).
    Proof.
      eapply dist_spred_simpl2; try apply _; [].
      intros m1 m2 w1 w2 m Hlt EQm EQw.
      do 2 (destruct m; first reflexivity).
      do 2 (destruct n as [| n]; [now inversion Hlt |]).
      intros [s HwsT]; exists s; intro wt.
      eapply wsatTotal_proper, HwsT; symmetry; first assumption.
      rewrite /wt. eapply comp_finmap_dist; last reflexivity.
      eapply mono_dist, EQw. omega.
    Qed.

    Global Instance wsat_equiv σ : Proper (equiv ==> equiv ==> equiv) (wsat σ).
    Proof.
      move=> m1 m2 EQm w1 w2 EQw. apply dist_refl=>n.
      apply wsat_dist; (assumption || eapply dist_refl; eassumption).
    Qed.

    Lemma wsat_valid {σ m w k} :
      wsat σ m w (S (S k)) -> cmra_valid w (S (S k)).
    Proof.
      move=> [s [pv _]]. eapply cmra_valid_ord, pv.
      exact:comp_finmap_le.
    Qed.

  End WorldSatisfaction.

  (* Simple view lemma. *)
  Lemma wsatM {σ m} {w n k} (HLe : k <= n) :
    wsat σ m w n -> wsat σ m w k.
  Proof. by exact: (dpred HLe). Qed.

  Section PrimitiveViewShifts.
    Local Obligation Tactic := intros.

    Program Definition preVS m1 m2 P w : SPred :=
      p[(fun n => forall (wf: Wld) k mf σ (HLe : S k < n)
                               (HD : mf # m1 ∪ m2)
                               (HE : wsat σ (m1 ∪ mf) (w · wf) (S (S k))),
                   exists w', P w' (S (S k))
                              /\ wsat σ (m2 ∪ mf) (w' · wf) (S (S k)))].
    Next Obligation.
      repeat intro.
      by inversion HLe.
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

    Global Instance pvs_mproper:
      Proper (equiv ==> equiv ==> equiv) pvs.
    Proof.
      move=>m11 m12 EQm1 m21 m22 EQm2 P w n. split=>Hvs.
      - move=>wf; intros.
        destruct (Hvs wf k mf σ) as [w' [HP HW]]; [assumption|de_auto_eq|now rewrite EQm1|].
        exists w'. split; first assumption. now rewrite <-EQm2.
      - move=>wf; intros.
        destruct (Hvs wf k mf σ) as [w' [HP HW]]; [assumption|de_auto_eq|now rewrite <-EQm1|].
        exists w'. split; first assumption. now rewrite EQm2.
    Qed.

    Lemma pvsEnt P m :
      P ⊑ pvs m m P.
    Proof.
      intros w0 n HP wf; intros.
      exists w0. split; last assumption.
      eapply propsMN, HP. omega.
    Qed.

  End PrimitiveViewShifts.


  Section WeakestPre.

    Local Obligation Tactic := intros; eauto with typeclass_instances.

    Definition safeExpr e σ :=
      is_value e \/
         (exists σ' e' ef, prim_step (e, σ) (e', σ') ef).

    Definition wpFP safe (WP : mask -n> expr -n> vPred -n> Props) m e φ w n :=
      (forall (HV : is_value e),
          φ (exist _ e HV) w n) /\
      forall wf k mf σ (HLt : S k < n) (HD : mf # m)
             (HE : wsat σ (m ∪ mf) (w · wf) (S (S k))),
        (forall e' σ' ef (HStep : prim_step (e, σ) (e', σ') ef),
            exists wret wfk, WP m e' φ wret (S k)
                             /\ match ef with None => True |
                                         Some ef' => WP de_full ef' (umconst ⊤) wfk (S k) end
                             /\ wsat σ' (m ∪ mf) (wfk · wret · wf) (S k)) /\
        (forall HSafe : safe = true, safeExpr e σ).

    (* Define the function wp will be a fixed-point of *)
    Program Definition wpF safe : (mask -n> expr -n> vPred -n> Props) -> (mask -n> expr -n> vPred -n> Props) :=
      fun WP => n[(fun m => n[(fun e => n[(fun φ => m[(fun w => p[(wpFP safe WP m e φ w)] )])])])].
    Next Obligation.
      split.
      - intros. exact: bpred.
      - intros. inversion HLt.
    Qed.
    Next Obligation.
      intros n1 n2 HLe Hwp. split.
      { intros. destruct Hwp as [Hwp _]. eapply dpred, Hwp. assumption. }
      intros  wf k mf σ HLt HD HE. destruct Hwp as [_ Hwp]. 
      destruct (Hwp wf k mf σ) as [HSt HSf]; first omega; try assumption; [].
      split; intros.
      - specialize (HSt _ _ _ HStep); destruct HSt as [w'' [HWP HE']].
        exists w''. eexists. eassumption.
      - now auto.
    Qed.
    Next Obligation.
      eapply dist_spred_simpl; first now apply _.
      intros w1 w2 n' HLt EQw [HV Hwp]; simpl. split.
      { intros. eapply spredNE, HV. rewrite EQw. reflexivity. }
      intros. edestruct (Hwp wf) as [HS HSf]; try eassumption;
      [eapply wsat_dist, HE; [reflexivity| eapply cmra_op_dist; eassumption || reflexivity |  omega] |].
      split; intros.
      - specialize (HS _ _ _ HStep); destruct HS as [w1'' [HWP HE']]. exists w1''.
        eexists; eassumption.
      - now auto.
    Qed.
    Next Obligation.
      intros w1 w2 [wd EQw] n. simpl; intros [HV Hwp]. split; intros.
      { eapply propsMW, HV. eexists. eassumption. }
      edestruct (Hwp (wd · wf) k mf) as [HS HSf]; try assumption; [|].
      { eapply wsat_dist, HE; try reflexivity. now rewrite -EQw assoc (comm w1). }
      split; intros.
      - specialize (HS _ _ _ HStep); destruct HS as [wret [wfk [HWR [HWF HE']]]].
        exists (wret · wd). exists wfk. split; [|split].
        + eapply propsMW, HWR. exists wd; now rewrite comm.
        + assumption.
        + eapply wsat_dist, HE'; try reflexivity. now rewrite !assoc.
      - now auto.
    Qed.
    Next Obligation.
      eapply dist_props_simpl; first now apply _.
      intros φ1 φ2 w k HLt EQφ [HV Hwp]; simpl; split; intros.
      { eapply spredNE, HV. eapply mmorph_proper; last reflexivity. eapply mono_dist, EQφ. assumption. }
      clear HV. edestruct Hwp as [HS HSf]; try eassumption; [].
      split; intros.
      - specialize (HS _ _ _ HStep); destruct HS as [wret [wfk [HWR [HWF HE']]]].
        exists wret wfk. split; last tauto.
        eapply (met_morph_nonexp (WP _ _)), HWR; [symmetry; eassumption | omega].
      - now auto.
    Qed.
    Next Obligation.
      intros e1 e2 EQe φ w. destruct n as [| n]; first exact:dist_bound.
      simpl in EQe; hnf in EQe; subst e2; reflexivity.
    Qed.
    Next Obligation.
      move=>m1 m2 EQm e φ w. destruct n; first exact:dist_bound.
      move:φ w e. split=>[] [HV Hwp]; split; intros.
      - eapply HV.
      - destruct (Hwp wf k mf σ) as (Hstep & Hsafe); [assumption|de_auto_eq|now rewrite EQm|].
        split; last assumption.
        move=>? ? ? Hprim. specialize (Hstep _ _ _ Hprim).
        destruct Hstep as (wfk & wret & Hwp' & Hwp'' & HW).
        exists wfk wret. split; last split.
        + eapply spredNE, Hwp'. eapply mmorph_proper; last reflexivity.
          eapply pcm_dist_inherit, mmorph_proper; last reflexivity.
          eapply mmorph_proper; last reflexivity. eapply met_morph_nonexp.
          eapply dist_mono, EQm.
        + assumption. 
        + now rewrite -EQm.
      - eapply HV.
      - destruct (Hwp wf k mf σ) as (Hstep & Hsafe); [assumption|de_auto_eq|now rewrite -EQm|].
        split; last assumption.
        move=>? ? ? Hprim. specialize (Hstep _ _ _ Hprim).
        destruct Hstep as (wret & wfk & Hwp' & Hwp'' & HW).
        exists wret wfk. split; last split.
        + eapply spredNE, Hwp'. eapply mmorph_proper; last reflexivity.
          eapply pcm_dist_inherit, mmorph_proper; last reflexivity.
          eapply mmorph_proper; last reflexivity. eapply met_morph_nonexp.
          symmetry. eapply dist_mono, EQm.
        + assumption.
        + now rewrite EQm.
    Qed.

    Instance contr_wpF safe : contractive (wpF safe).
    Proof.
      intros n WP1 WP2 EQWP m e φ w k HLt.
      split; intros [HV Hwp]; (split; first by auto); intros; edestruct Hwp as [HS HSf]; try eassumption; [|].
      - split; intros.
        + clear HV; specialize (HS _  _ _ HStep); destruct HS as [wret [wfk [HWR [HWF HE']]]].
          exists wret wfk.
          split; [| split; [| assumption] ].
          * eapply EQWP; try eassumption; omega.
          * intros. destruct ef; last done. eapply EQWP, HWF; try assumption; omega.
        + now auto.
      - split; intros.
        + clear HV; specialize (HS _ _ _ HStep); destruct HS as [wret [wfk [HWR [HWF HE']]]].
          exists wret wfk.
          split; [| split; [| assumption] ].
          * eapply EQWP; try eassumption; omega.
          * intros. destruct ef; last done. eapply EQWP, HWF; try assumption; omega.
        + now auto.
    Qed.

    Definition wp safe : mask -n> expr -n> vPred -n> Props :=
      fixp (wpF safe) (umconst (umconst (umconst ⊤))).

    Lemma unfold_wp safe :
      wp safe == (wpF safe) (wp safe).
    Proof.
      unfold wp; apply fixp_eq.
    Qed.
    
    Global Opaque wp.

    (* Some global properties are proven here directly. *)
    Lemma wpValue e (HV : is_value e) safe m φ :
      wp safe m e φ == φ (exist _ e HV).
    Proof.
      rewrite unfold_wp. split.
      - intros [HVl _]. apply HVl.
      - intros Hφ. split; last (intros; split; intros).
        + intros. eapply spredNE, Hφ. eapply mmorph_proper; last reflexivity.
          apply (met_morph_nonexp φ). destruct n; first done. reflexivity.
        + contradiction (values_stuck _ HV). repeat eexists. eassumption.
        + unfold safeExpr. auto.
    Qed.

    Lemma wpWeakenMask safe m1 m2 e φ (HD : m1 ⊑ m2) :
      wp safe m1 e φ ⊑ wp safe m2 e φ.
    Proof.
      intros w n; revert w e φ; induction n using wf_nat_ind; rename H into HInd; intros w e φ.
      rewrite unfold_wp. intros [HV HW]. split; intros; first done.
      edestruct HW with (mf := mf ∪ (m2 \ m1)) as [HS HSf]; try eassumption;
      [| eapply wsat_equiv, HE; try reflexivity; de_auto_eq |]; first de_auto_eq.
      clear HW HE; split; [intros; clear HV | intros; clear HV HS].
      - destruct (HS _ _ _ HStep) as [wret [wfk [HWR [HWF HE]]]]; clear HS.
        do 2 eexists. split; [eapply HInd; eassumption|].
        split; first eassumption.
        eapply wsat_equiv, HE; try reflexivity; clear; de_auto_eq.
      - now auto.
    Qed.

  End WeakestPre.

  Section DerivedForms.
    (* We define the derived forms here, so that iris_meta can also use them. *)

    (** View Shifts **)
    Definition vs m1 m2 P Q : Props :=
      □(P → pvs m1 m2 Q).

    Global Instance vsProper: Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) vs.
    Proof.
      move=>m11 m12 EQm1 m21 m22 EQm2 P1 P2 EQP Q1 Q2 EQQ. unfold vs.
      apply box_equiv. apply impl_equiv; first assumption.
      apply equiv_morph; last assumption.
      now rewrite EQm1 EQm2.
    Qed.

    Lemma vsIntro R m1 m2 P Q:
      □R ⊑ vs m1 m2 P Q <-> □R ∧ P ⊑ pvs m1 m2 Q.
    Proof.
      split=>H.
      - unfold vs in H.
        apply and_impl. etransitivity; last by eapply box_elim. assumption.
      - unfold vs; apply box_intro. rewrite <-and_impl. assumption.
    Qed.

    Lemma vsValid m1 m2 P Q:
      valid (vs m1 m2 P Q) <-> P ⊑ pvs m1 m2 Q.
    Proof.
      rewrite ->top_valid, <-box_top. split=>H.
      - etransitivity; last by erewrite <-vsIntro. apply and_R; split; last reflexivity.
        rewrite ->box_top. apply top_true.
      - etransitivity; first apply vsIntro; last reflexivity.
        rewrite <-H. apply and_projR.
    Qed.

    (** Hoare Triples **)
    Definition ht safe m P e Q := □(P → wp safe m e (pvs m m <M< Q)).

    Global Instance ht_proper safe: Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) (ht safe).
    Proof.
      move=>m0 m1 EQm P0 P1 HEQP e0 e1 HEQe Q0 Q1 HEQQ.
      unfold ht. apply box_equiv. apply impl_equiv; first assumption.
      apply equiv_morph.
      - hnf in HEQe. subst e1.
        eapply mmorph_inherit. eapply equiv_morph; last reflexivity.
        eapply mmorph_inherit, morph_resp. assumption.
      - eapply dist_refl=>n. eapply ndist_umcomp; eapply dist_refl; last assumption.
        rewrite EQm. reflexivity.
    Qed.

    Lemma htIntro R safe m e P Q:
      □R ⊑ ht safe m P e Q <-> □R ∧ P ⊑ wp safe m e (pvs m m <M< Q).
    Proof.
      split=>H.
      - unfold ht in H.
        apply and_impl. etransitivity; last by eapply box_elim. assumption.
      - unfold ht; apply box_intro. rewrite <-and_impl. assumption.
    Qed.

    Lemma htValid safe m e P Q:
      valid (ht safe m P e Q) <-> P ⊑ wp safe m e (pvs m m <M< Q).
    Proof.
      rewrite ->top_valid, <-box_top. split=>H.
      - etransitivity; last by erewrite <-htIntro. apply and_R; split; last reflexivity.
        rewrite ->box_top. apply top_true.
      - etransitivity; first apply htIntro; last reflexivity.
        rewrite <-H. apply and_projR.
    Qed.

  End DerivedForms.

End IRIS_PLOG.

Module IrisPlog (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) : IRIS_PLOG RL C R WP CORE.
  Include IRIS_PLOG RL C R WP CORE.
End IrisPlog.
