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
      - omega.
    Qed.

    Lemma pvsOpen i P :
      (inv i P) ⊑ pvs (de_sing i) de_emp (▹P).
    Proof.
      intros w n HInv.
      destruct n; first exact:bpred. repeat intro.
      destruct HInv as [Pr HInv].
      destruct HE as [rs [pv [HS HM]]]. simpl in HInv.
      move:(HM i (ra_ag_inj (ı' (halved P)))). case/(_ _)/Wrap.
      { clear -HInv pv HLe. eapply world_invs_extract; first assumption; last first.
        - eapply mono_dist, HInv. omega.
        - etransitivity; last eapply comp_finmap_le. exists wf. now rewrite comm. }
      erewrite de_in_true by de_tauto.
      destruct (rs i) as [wi |] eqn: HLr; last by move=>[]. move=>HP.
      exists (w · wi). split.
      { simpl. eapply propsMW; first (eexists; reflexivity). eapply spredNE, HP.
        simpl. rewrite isoR. reflexivity. }
      clear HInv HP.
      exists (fdStrongUpdate i None rs). intros wt.
      assert (Heqwt:  comp_finmap (w · wf) rs == wt).
      { rewrite /wt (comm _ wi) -assoc (comp_finmap_move wi).
        rewrite (comm wi) -comp_finmap_remove; last now rewrite HLr. reflexivity. }
      split.
      { eapply spredNE, pv. rewrite -Heqwt. reflexivity. }
      split.
      - rewrite /= -Heqwt. assumption.
      - move=>j agP Hlu. rewrite (comm de_emp) de_emp_union. move:(HM j agP)=>{HM}.
        case/(_ _)/Wrap.
        { rewrite Heqwt. exact Hlu. }
        destruct (j ∈ mf) eqn:Hm.
        + erewrite de_in_true by de_tauto.
          destruct (dec_eq i j) as [EQ|NEQ].
          { exfalso. subst j. move:(HD i) Hm. clear. de_tauto. }
          erewrite fdStrongUpdate_neq by assumption. done.
        + destruct (dec_eq i j) as [EQ|NEQ].
          { move=>_. subst j. rewrite fdStrongUpdate_eq. done. }
          erewrite de_in_false by de_tauto.
          erewrite fdStrongUpdate_neq by assumption. done.
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
      assert (HeqP: (Invs (comp_finmap (w · wf) rs)) i = S (S k) =
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
        rewrite -(comm w) -(comp_finmap_move w) assoc (comm _ (1w)) ra_op_unit.
        reflexivity. }
      split.
      { eapply spredNE, pv. rewrite -Heqwt. reflexivity. }
      split.
      - rewrite /State -Heqwt. assumption.
      - move=>j agP Hlu. destruct (dec_eq i j) as [EQ|NEQ].
        + subst j. erewrite de_in_true by de_tauto.
          rewrite fdStrongUpdate_eq. clear HS HM. simpl in HP.
          eapply spredNE, dpred, HP; last omega.
          rewrite ->Heqwt, ->Hlu in HeqP. simpl. simpl in HeqP.
          etransitivity; last first.
          * assert(Heq:=halve_eq (T:=Props) (S k)). apply Heq=>{Heq}.
            eapply (met_morph_nonexp ı). eapply ra_ag_unInj_dist; last (symmetry; eexact HeqP).
            exact I.
          * simpl. rewrite isoR. reflexivity.
        + move:(HM j agP)=>{HM}. case/(_ _)/Wrap.
          { rewrite Heqwt. assumption. }
          rewrite comm de_emp_union. destruct (j ∈ mf) eqn:Hjin.
          * erewrite de_in_true by de_tauto. by erewrite fdStrongUpdate_neq.
          * erewrite de_in_false by de_tauto. by erewrite fdStrongUpdate_neq.
    Qed.

    Lemma pvsTrans P m1 m2 m3 (HMS : m2 ⊑ m1 ∪ m3) :
      pvs m1 m2 (pvs m2 m3 P) ⊑ pvs m1 m3 P.
    Proof.
      intros w1 n HP wf; intros.
      destruct (HP wf _ mf σ HLe) as (w2 & HP2 & HSat2); [ de_auto_eq | by auto | ].
      destruct (HP2 wf k mf σ) as (w3 & HP3 & HSat3);
        [ omega | de_auto_eq | auto | ].
      exists w3; split; assumption.
    Qed.
    
    Lemma pvsEnt P m :
      P ⊑ pvs m m P.
    Proof.
      intros w0 n HP wf; intros.
      exists w0. split; last assumption.
      eapply propsMN, HP. omega.
    Qed.

    Lemma pvsMon P Q m1 m2 : 
      P ⊑ Q -> pvs m1 m2 P ⊑ pvs m1 m2 Q.
    Proof.
      move => HPQ w0 n HvsP.
      intros wf k mf σ Hlt HD HSat.
      destruct (HvsP wf _ mf σ Hlt) as (w1 & HP & HSat2); [de_auto_eq|assumption|].
      exists w1. split; last assumption.
      eapply HPQ, HP.
    Qed.
      
    Lemma pvsFrameMask P m1 m2 mf (HDisj : mf # m1 ∪ m2) :
      pvs m1 m2 P ⊑ pvs (m1 ∪ mf) (m2 ∪ mf) P.
    Proof.
      move => w0 n HvsP wf; intros.
      edestruct (HvsP wf k (mf ∪ mf0)) as (w2 & HP & HSat2); eauto.
      - de_auto_eq.
      - rewrite assoc. eassumption.
      - exists w2. split; first assumption.
        rewrite -assoc. assumption.
    Qed.

    Lemma pvsFrameRes P Q m1 m2:
      (pvs m1 m2 P) * Q ⊑ pvs m1 m2 (P * Q).
    Proof.
      move => w0 n. destruct n; first (intro; exact:bpred).
      intros [[wp wq] [HEr [HvsP HQ]]].
      move => wf mf σ k Hlt HD HSat.
      edestruct (HvsP (wq · wf) mf) as (w2 & HP & HSat2); eauto.
      { simpl morph. eapply wsat_dist, HSat;[reflexivity| |reflexivity].
        simpl in HEr. rewrite assoc. apply cmra_op_dist; last reflexivity.
        eapply mono_dist, HEr. omega. }
      exists (w2 · wq). split.
      - exists (w2, wq). split; last split.
        + rewrite [ra_op]lock. simpl. reflexivity.
        + assumption.
        + apply propsMN, HQ. omega.
      - now rewrite -assoc.
    Qed.

    Definition ownLP (P : RL.res -> Prop) : {s : RL.res | P s} -n> Props :=
      ownL <M< inclM.

    Lemma pvsGhostUpd m g (P : RL.res -> Prop) (HU : g ⇝∈ P) :
      ownL g ⊑ pvs m m (xist (ownLP P)).
    Proof.
      unfold ownLP. intros w n. destruct n; first (intros; exact:bpred).
      intros [g' Hg'] wf; intros.
      destruct HE as [rs HwsT ]. simpl in HwsT. rewrite ->comp_finmap_move in HwsT.
      destruct HwsT as [pv [HS HI]]. move:(pv). move/cmra_prod_valid=>[HIval]. move/cmra_prod_valid=>[HSval Hgval].
      destruct w as [I0 [S0 g0]]. simpl in Hg'.
      destruct (HU (g' · Res (comp_finmap wf rs))) as [g1 [HP HVal1] ].
      - clear - Hgval Hg'. simpl in Hgval. now rewrite assoc (comm g) Hg'.
      - exists (I0, (S0, g1 · g')). split.
        + simpl. exists (exist _ _ HP). simpl.
          eexists. now erewrite comm.
        + exists rs. simpl. rewrite comp_finmap_move. clear HP Hgval.
          split.
          { split; last split; try assumption; [].
            now rewrite ->assoc in HVal1. }
          done.
    Qed.

    Program Definition inv' m : Props -n> {n : nat | n ∈ m = true } -n> Props :=
      n[(fun P => n[(fun N => inv (proj1_sig N) P)])].
    Next Obligation.
      intros i i' EQi; destruct n as [| n]; [apply dist_bound |].
      simpl in EQi; rewrite EQi; reflexivity.
    Qed.
    Next Obligation.
      intros p1 p2 EQp i; simpl morph.
      apply (inv (` i)); assumption.
    Qed.

    Lemma fresh_region (w : Wld) (s: nat -f> Wld) m (HInf : de_infinite m) :
      exists i, i ∈ m = true /\ Invs w i = None /\ s i = None.
    Proof.
      pose (l := (dom (Invs w) ++ dom s)%list).
      pose (j := Lists.list_max l).
      destruct (HInf (S j)) as [i [HGe Hm] ].
      exists i; split; [assumption |]; clear - HGe.
      specialize (Lists.list_max_ge l i)=>Hin. subst l.
      split; apply fdLookup_notin_strong=>Hin'; move:Hin.
      - case/(_ _)/Wrap; first (apply List.in_app_iff; tauto).
        intros Hle. subst j. omega.
      - case/(_ _)/Wrap; first (apply List.in_app_iff; tauto).
        intros Hle. subst j. omega.
    Qed.

    Lemma pvsNewInv P m (HInf : de_infinite m) :
      ▹P ⊑ pvs m m (xist (inv' m P)).
    Proof.
      intros w n HP wf; intros.
      destruct n as [| n]; [now inversion HLe | simpl in HP].
      case:HE=>rs. cbv zeta. rewrite comp_finmap_move. move =>[pv [HS HI]].
      destruct (fresh_region (w · comp_finmap wf rs) rs m HInf) as [i [Hm [HLi Hrsi]]].
      pose (w' := (fdStrongUpdate i (Some (ra_ag_inj (ı' (halved P)))) fdEmpty, 1 (snd w))).
      exists w'. split.
      { eexists (exist _ i Hm). eexists. rewrite /w' /= DecEq_refl.
        apply dist_refl. symmetry. eapply ra_ag_dupl. }
      exists (fdStrongUpdate i (Some w) rs). simpl. simpl in HLi.
      rewrite comp_finmap_move. erewrite <-comp_finmap_add by (now apply equivR). rewrite (comm _ w).
      split.
      {  destruct pv as [pvI pvR]. split.
        -  rewrite /w' /= =>j /=. destruct (dec_eq i j).
           + subst j. rewrite HLi /=. done.
           + exact:(pvI j).
        - rewrite assoc /w' /= !ra_op_unit. exact pvR. }
      split.
      - rewrite /State assoc /w' /= ra_op_unit. assumption.
      - move=>j agP Heq. destruct (dec_eq i j) as [EQ|NEQ].
        + subst j. erewrite de_in_true by de_tauto. rewrite fdStrongUpdate_eq.
          move:(Heq)=>Heq'. move:Heq. rewrite /= DecEq_refl HLi /==>Heq.
          eapply spredNE, dpred, HP; last omega.
          eapply mmorph_proper; last reflexivity.
          etransitivity; last first.
          * assert(Hheq:=halve_eq (T:=Props) (S k)). apply Hheq=>{Hheq}.
            eapply (met_morph_nonexp ı). eapply ra_ag_unInj_dist; last eexact Heq.
            exact I.
          * simpl. rewrite isoR. reflexivity.
        + erewrite fdStrongUpdate_neq by assumption.
          move:(HI j agP)=>{HI Hrsi HLi Hm}. case/(_ _)/Wrap.
          { rewrite -Heq. simpl. destruct (dec_eq i j); last reflexivity.
            contradiction. }
          tauto.
    Qed.

    Lemma pvsOwnValid m w:
      own w ⊑ pvs m m (own w ∧ pcmconst (cmra_valid w)).
    Proof.
      intros w0 n. destruct n; first (intro; exact:bpred).
      move=>Hown wf; intros. exists w0.
      split; last done. split; first (eapply propsMN, Hown; omega).
      destruct HE as [rs [pv _]]. simpl. destruct Hown as [wr Heq]. simpl in Heq.
      eapply cmra_valid_ord, spredNE, pv; last first.
      - eapply cmra_valid_dist. erewrite comp_finmap_move. 
        eapply cmra_op_dist; last reflexivity. symmetry. eapply mono_dist, Heq. omega.
      - rewrite -assoc. eexists. now erewrite (comm _ w).
    Qed.

  End ViewShiftProps.

  Global Opaque pvs.
  Global Opaque wpF.

End IRIS_VS_RULES.

Module IrisVSRules (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE): IRIS_VS_RULES RL C R WP CORE PLOG.
  Include IRIS_VS_RULES RL C R WP CORE PLOG.
End IrisVSRules.
