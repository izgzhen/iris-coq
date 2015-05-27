Require Import Ssreflect.ssreflect Ssreflect.ssrfun Omega.
Require Import world_prop core_lang iris_core iris_plog.
Require Import ModuRes.RA ModuRes.DecEnsemble ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.Agreement ModuRes.CMRA.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_VS_RULES (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE).
  Export PLOG.

  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.
  Local Open Scope de_scope.

  Implicit Types (P Q R : Props) (w : Wld) (n i k : nat) (m : DecEnsemble nat) (r : res) (σ : state) (g : RL.res).

  Section ViewShiftProps.

    Lemma pvsTimeless m P :
      timeless P ∧ ▹P ⊑ pvs m m P.
    Proof.
      intros w n [HTL Hp] ?; intros.
      exists w. split; last assumption.
      destruct n as [| n]; [exfalso;omega |]; simpl in Hp.
      destruct n as [| n]; first omega.
      eapply propsMN, HTL, Hp.
      - omega.
      - reflexivity.
      - omega.
    Qed.

    Lemma pvsOpen i P :
      (inv i P) ⊑ pvs (de_sing i) de_emp (▹P).
    Proof.
      intros w n HInv.
      destruct n; first exact:bpred. intros ?; intros.
      destruct HInv as [Pr HInv].
      destruct HE as [rs [pv [HS HM]]].
      case HLu:(Invs w i) => [μ |] ; simpl in HInv; last first.
      { exfalso. rewrite HLu in HInv. destruct HInv. }
      move:(HM i (ra_ag_inj (ı' (halved P)))). case/(_ _)/Wrap; last move=>Heq.
      { clear -HLu HInv pv HLe. eapply world_invs_extract; first assumption; last first.
        - eapply mono_dist, HInv. omega.
        - etransitivity; last eapply comp_finmap_le. exists wf. now rewrite comm. }
      rewrite /de_sing. erewrite de_in_true by de_tauto.
      destruct (rs i) as [wi |] eqn: HLr; last by move=>[]. move=>HP.
      exists (w · wi). split.
      { simpl. eapply propsMW; first (eexists; reflexivity). eapply spredNE, HP.
        simpl. rewrite isoR. reflexivity. }
      clear HLu HInv HP.
      exists (fdStrongUpdate i None rs). intros wt.
      assert (Heqwt:  comp_finmap (w · wf) rs == wt).
      { rewrite /wt -assoc (comm wi) assoc (comp_finmap_move wi).
        rewrite -comp_finmap_remove; last now rewrite HLr. reflexivity. }
      assert (pv': (cmra_valid wt) (S k)).
      { eapply spredNE, pv. rewrite -Heqwt. reflexivity. }
      exists pv'. split.
      - rewrite /State -Heqwt. assumption.
      - move=>j agP Hlu. rewrite (comm de_emp) de_emp_union. move:(HM j agP)=>{HM}.
        case/(_ _)/Wrap; last move=>Heq'.
        { rewrite /Invs Heqwt. exact Hlu. }
        destruct (j ∈ mf) eqn:Hm.
        + erewrite de_in_true by de_tauto.
          destruct (dec_eq i j) as [EQ|NEQ].
          { exfalso. subst j. move:(HD i) Hm. clear. de_tauto. }
          erewrite fdStrongUpdate_neq by assumption. destruct (rs j); last tauto.
          simpl=>H. erewrite ra_ag_unInj_pi. eassumption.
        + destruct (dec_eq i j) as [EQ|NEQ].
          { move=>_. subst j. rewrite fdStrongUpdate_eq. exact I. }
          erewrite de_in_false by de_tauto.
          erewrite fdStrongUpdate_neq by assumption. tauto.
    Qed.

    Lemma pvsClose i P :
      (inv i P ∧ ▹P) ⊑ pvs de_emp (de_sing i) ⊤.
    Proof.
      intros w n [HInv HP] wf; intros. destruct n; first by inversion HLe.
      destruct HInv as [Pr HInv].
      destruct HE as [rs [pv [HS HM]]].
      case HLu:(Invs w i) => [μ |] ; simpl in HInv; last first.
      { exfalso. rewrite HLu in HInv. destruct HInv. }
      exists (1 w). split; first exact I.
      exists (fdStrongUpdate i (Some w) rs). intros wt.
      assert (HeqP: (Invs (comp_finmap (w · wf) rs)) i = S k =
                    Some (ra_ag_inj (ı' (halved P)))).
      { eapply world_invs_extract; first assumption; last first.
        - etransitivity; first (eapply mono_dist, HInv; omega). reflexivity.
        - rewrite <-comp_finmap_le. exists wf. now rewrite comm. }
      assert (Heqwt: comp_finmap (w · wf) rs == wt).
      { rewrite /wt. erewrite <-comp_finmap_add; last first.
        { move:(HM i (ra_ag_inj (ı' (halved P))) HeqP).
          erewrite de_in_false; last first.
          { move:(HD i). clear. de_tauto. }
          destruct (rs i); first move=> [].
          move=>_. reflexivity. }
        rewrite -(comp_finmap_move w) -assoc (comm wf) assoc ra_op_unit.
        reflexivity. }
      assert (pv': (cmra_valid wt) (S k)).
      { eapply spredNE, pv. rewrite -Heqwt. reflexivity. }
      exists pv'. split.
      - rewrite /State -Heqwt. assumption.
      - move=>j agP Hlu. destruct (dec_eq i j) as [EQ|NEQ].
        + subst j. erewrite de_in_true by de_tauto.
          rewrite fdStrongUpdate_eq. clear HS HM. simpl in *.
          eapply spredNE, dpred, HP; last omega.
          rewrite ->Heqwt, ->Hlu in HeqP. simpl in HeqP.
          etransitivity; last first.
          * assert(Heq:=halve_eq (T:=Props) k). apply Heq=>{Heq}.
            eapply (met_morph_nonexp ı). eapply ra_ag_unInj_dist.
            symmetry. eexact HeqP.
          * simpl. rewrite isoR. reflexivity.
        + move:(HM j agP)=>{HM}. case/(_ _)/Wrap; last move=>Heq'.
          { rewrite Heqwt. assumption. }
          rewrite comm de_emp_union. destruct (j ∈ mf) eqn:Hjin.
          * erewrite de_in_true by de_tauto. erewrite fdStrongUpdate_neq by assumption.
            destruct (rs j); last tauto. simpl.
            move=>H. erewrite ra_ag_unInj_pi. eassumption.
          * erewrite de_in_false by de_tauto. erewrite fdStrongUpdate_neq by assumption.
            tauto.
    Grab Existential Variables.
    { eapply cmra_valid_ord.
      - exists Pr. reflexivity.
      - eapply world_invs_valid; first eassumption; last first.
        + eapply mono_dist, HInv. omega.
        + rewrite -Heqwt. etransitivity; last by eapply comp_finmap_le.
          exists wf. now rewrite comm. }
    Qed.

    Lemma pvsTrans P m1 m2 m3 (HMS : m2 ⊆ m1 ∪ m3) :
      pvs m1 m2 (pvs m2 m3 P) ⊑ pvs m1 m3 P.
    Proof.
      intros w0 n r0 HP w1 rf mf σ k HSub Hnk HD HSat.
      destruct (HP w1 rf mf σ _ HSub Hnk) as (w2 & r2 & HSub2 & HP2 & HSat2); [ | by auto | ].
      { clear - HD HMS; intros j [Hmf Hm12]; apply (HD j); split; [assumption |].
        destruct Hm12 as [Hm1 | Hm2]; [left; assumption | apply HMS, Hm2].
      }
      destruct (HP2 w2 rf mf σ k) as (w3 & r3 & HSub3 & HP3 & HSat3); 
        [ reflexivity | omega | | auto | ].
      { clear - HD HMS; intros j [Hmf Hm23]; apply (HD j); split; [assumption |].
        destruct Hm23 as [Hm2 | Hm3]; [apply HMS, Hm2 | right; assumption].
      }
      exists w3 r3; split; [ by rewrite -> HSub2 | by split ].
    Qed.
    
    Lemma pvsEnt P m :
      P ⊑ pvs m m P.
    Proof.
      intros w0 n r0 HP w1 rf mf σ k HSub Hnk HD HSat.
      exists w1 r0; repeat split; [ reflexivity | eapply propsMWN; eauto | assumption ].
    Qed.

    Lemma pvsImpl P Q m1 m2 :
      □ (P → Q) ∧ pvs m1 m2 P ⊑ pvs m1 m2 Q.
    Proof.
      move => w0 n r0 [HPQ HvsP].
      intros w1 rf mf σ k HSub1 Hlt HD HSat.
      move/HvsP: HSat => [|||w2 [r2 [HSub2 [/HPQ HQ HSat]]]]; try eassumption; []. 
      do 2!eexists; split; [exact HSub2|split; [|eassumption]].
      eapply HQ; [by rewrite -> HSub1 | omega | exact unit_min].
    Qed.
      
    Lemma pvsFrameMask P m1 m2 mf (HDisj : mf # m1 ∪ m2) :
      pvs m1 m2 P ⊑ pvs (m1 ∪ mf) (m2 ∪ mf) P.
    Proof.
      move => w0 n r0 HvsP.
      move => w1 rf mf1 σ k HSub1 Hlt HD HSat.
      edestruct (HvsP w1 rf (mf ∪ mf1)) as (w2 & r2 & HSub2 & HP & HSat2); eauto.
      - (* disjointness of masks: possible lemma *)
        clear - HD HDisj; intros i [ [Hmf | Hmf] [Hm1|Hm2]]; by firstorder.
      - eapply wsat_equiv; last eassumption; [|reflexivity|reflexivity].
        unfold mcup in *; split; intros i; tauto.
      - exists w2 r2; split; [eassumption|split; [assumption|]].
        eapply wsat_equiv; last eassumption; [|reflexivity|reflexivity].
        unfold mcup in *; split; intros i; tauto.
    Qed.

    Lemma pvsFrameRes P Q m1 m2:
      (pvs m1 m2 P) * Q ⊑ pvs m1 m2 (P * Q).
    Proof.
      move => w0 n r0 [rp [rq [HEr [HvsP HQ]]]].
      move => w1 rf mf σ k HSub1 Hlt HD HSat.
      edestruct (HvsP w1 (rq · rf) mf) as (w2 & r2 & HSub2 & HP & HSat2); eauto.
      - rewrite assoc HEr. eassumption. 
      - exists w2 (r2 · rq); split; [eassumption|split; [|]].
        + do 2!eexists; split; [reflexivity | split; [assumption|]].
          * eapply propsMWN; last eassumption; [by rewrite <- HSub2| omega].
        + setoid_rewrite <- ra_op_assoc. assumption.
    Qed.

    (* RJ this should now be captured by the generic instance for discrete metrics.
    Instance LP_res (P : RL.res -> Prop) : LimitPreserving P.
    Proof.
      intros σ σc HPc; simpl. unfold discreteCompl.
      now auto.
    Qed.*)

    Definition ownLP (P : RL.res -> Prop) : {s : RL.res | P s} -n> Props :=
      ownL <M< inclM.

    Lemma pvsGhostUpd m rl (P : RL.res -> Prop) (HU : rl ⇝∈ P) :
      ownL rl ⊑ pvs m m (xist (ownLP P)).
    Proof.
      unfold ownLP. intros w n [rp' rl'] HG w'; intros.
      destruct HE as [rs [ Hsat HE] ]. rewrite <-assoc in Hsat. destruct Hsat as [Hval Hst].
      destruct HG as [ [rdp rdl] [_ EQrl] ]. simpl in EQrl. clear rdp.
      destruct (HU (rdl · snd(rf · comp_map rs))) as [rsl [HPrsl HCrsl] ].
      - clear - Hval EQrl. eapply ra_prod_valid in Hval. destruct Hval as [_ Hsnd].
        rewrite ->assoc, (comm rl), EQrl.
        rewrite ra_op_prod_snd in Hsnd. exact Hsnd.
      - exists w' (rp', rsl).
        split; first reflexivity. split.
        + exists (exist _ rsl HPrsl). simpl.
          exists (rp', 1:RL.res). simpl.
          rewrite ra_op_unit ra_op_unit2. split; reflexivity.
        + exists rs. split; [| assumption]; clear HE. rewrite <-assoc. split; [eapply ra_prod_valid; split|].
          * clear - Hval. eapply ra_prod_valid in Hval. destruct Hval as [Hfst _].
            rewrite ra_op_prod_fst in Hfst.
            rewrite ra_op_prod_fst. exact Hfst.
          * clear -HCrsl. rewrite ->!assoc, (comm rsl), <-assoc in HCrsl.
            apply ra_op_valid2 in HCrsl. rewrite ra_op_prod_snd. exact HCrsl.
          * clear -Hst. rewrite ra_op_prod_fst. rewrite ra_op_prod_fst in Hst. exact Hst.
    Qed.

    Program Definition inv' m : Props -n> {n : nat | m n} -n> Props :=
      n[(fun P => n[(fun n : {n | m n} => inv n P)])].
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

    (* RJ this should now be captured by the generic instance for discrete metrics.
    Instance LP_mask m : LimitPreserving m.
    Proof.
      intros σ σc Hp; apply Hp.
    Qed. *)

    Lemma pvsNewInv P m (HInf : mask_infinite m) :
      ▹P ⊑ pvs m m (xist (inv' m P)).
    Proof.
      intros w n r HP w'; intros.
      destruct n as [| n]; [now inversion HLe | simpl in HP].
      rewrite ->HSub in HP; clear w HSub; rename w' into w.
      destruct (fresh_region w m HInf) as [i [Hm HLi] ].
      assert (HSub : w ⊑ fdUpdate i (ı' (halved P)) w).
      { intros j; destruct (Peano_dec.eq_nat_dec i j); [subst j; rewrite HLi; exact I|].
        now rewrite ->fdUpdate_neq by assumption.
      }
      exists (fdUpdate i (ı' (halved P)) w) 1; split; [assumption | split].
      - exists (exist _ i Hm).
        change (((fdUpdate i (ı' (halved P)) w) i) = S (S k) = (Some (ı' (halved P)))).
        rewrite fdUpdate_eq; reflexivity.
      - erewrite ra_op_unit by apply _.
        destruct HE as [rs [HE HM] ].
        exists (fdUpdate i r rs).
        assert (HRi : rs i = None).
        { destruct (HM i) as [HDom _]; unfold mcup; [tauto |].
          rewrite <- fdLookup_notin_strong, HDom, fdLookup_notin_strong; assumption.
        }
        split.
        {
          rewrite <-comp_map_insert_new by now eapply equivR.
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

    Lemma pvsNotOwnInvalid m1 m2 g
      (Hnval: ~↓r):
      ownL g ⊑ pvs m1 m2 ⊥.
    Proof.
      intros w0 n0 r0 [rs Heq] w' rf mf σ k _ _ _ [ ri [ [ Hval _ ] ] ].
      exfalso.
      apply Hnval. rewrite <-Heq in Hval.
      eapply ra_op_valid2, ra_op_valid, ra_op_valid; last eassumption; now apply _.
    Qed.

    (* TODO: can always get ownL of some unit *)
    (* TODO: ownS * ownS => ⊥ *)

  End ViewShiftProps.

End IRIS_VS_RULES.

Module IrisVSRules (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE): IRIS_VS_RULES RL C R WP CORE PLOG.
  Include IRIS_VS_RULES RL C R WP CORE PLOG.
End IrisVSRules.
