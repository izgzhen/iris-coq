Require Import Ssreflect.ssreflect Ssreflect.ssrfun Omega List.
Require Import core_lang world_prop iris_core iris_plog iris_ht_rules.
Require Import ModuRes.RA ModuRes.CMRA ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.RAConstr ModuRes.DecEnsemble ModuRes.Agreement ModuRes.Lists ModuRes.Relations.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_META (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) (HT_RULES: IRIS_HT_RULES RL C R WP CORE PLOG).
  Export HT_RULES.

  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.

  Section Adequacy.

    Local Open Scope list_scope.

    Implicit Types (P : Props) (w : Wld) (i n : nat) (safe : bool) (m : DecEnsemble nat) (e : expr) (Q φ : vPred) (r : res) (σ : state) (g : RL.res) (t : tpool).


    (* weakest-pre for a threadpool *)
    Inductive wptp (safe : bool) n : tpool -> list Wld -> list vPred -> Prop :=
    | wp_emp : wptp safe n nil nil nil
    | wp_cons e φ tp w ws φs
              (WPE  : wp safe de_full e φ w n)
              (WPTP : wptp safe n tp ws φs) :
        wptp safe n (e :: tp) (w :: ws) (φ :: φs).

    (* Trivial lemmas about split over append *)
    Lemma wptp_app safe n tp1 tp2 ws1 ws2 φs1 φs2
          (HW1 : wptp safe n tp1 ws1 φs1)
          (HW2 : wptp safe n tp2 ws2 φs2) :
      wptp safe n (tp1 ++ tp2) (ws1 ++ ws2) (φs1 ++ φs2).
    Proof.
      induction HW1; [| constructor]; now trivial.
    Qed.

    Lemma wptp_app_tp safe n t1 t2 ws φs
          (HW : wptp safe n (t1 ++ t2) ws φs) :
      exists ws1 ws2 φs1 φs2, ws1 ++ ws2 = ws /\ φs1 ++ φs2 = φs /\ wptp safe n t1 ws1 φs1 /\ wptp safe n t2 ws2 φs2.
    Proof.
      revert ws φs HW; induction t1; intros; inversion HW; simpl in *; subst; clear HW.
      - do 4 eexists. split; [|split; [|split; now econstructor]]; reflexivity.
      - do 4 eexists. split; [|split; [|split; now eauto using wptp]]; reflexivity.
      - apply IHt1 in WPTP; destruct WPTP as [ws1 [ws2 [φs1 [φs2 [EQws [EQφs [WP1 WP2]]]]]]]; clear IHt1.
        exists (w :: ws1) ws2 (φ :: φs1) φs2; simpl; subst; now auto using wptp.
    Qed.

    (* Closure under smaller steps *)
    Lemma wptp_closure safe n1 n2 tp ws φs
          (HLe : n2 <= n1)
          (HW : wptp safe n1 tp ws φs) :
      wptp safe n2 tp ws φs.
    Proof.
      induction HW; constructor; [| assumption].
      eapply dpred, WPE. assumption.
    Qed.

    Definition comp_wlist := @fold_left Wld Wld ra_op.

    Global Instance comp_wlist_equiv ws:
      Proper (equiv ==> equiv) (comp_wlist ws).
    Proof.
      induction ws; intros w0 w1 EQw.
      - exact EQw.
      - rewrite /comp_wlist /=. eapply IHws. now rewrite EQw.
    Qed.

    Lemma comp_wlist_tofront w w0 ws:
      w · comp_wlist ws w0 == comp_wlist (w::ws) w0.
    Proof.
      revert w0. induction ws; intros; simpl comp_wlist.
      - simpl comp_wlist. now rewrite comm.
      - rewrite IHws /comp_wlist /=. rewrite -(assoc _ w) (comm w) assoc.
        reflexivity.
    Qed.

    Lemma preserve_wptp w0 safe n k tp tp' σ σ' ws φs
          (HSN  : stepn n (tp, σ) (tp', σ'))
          (HWTP : wptp safe (n + (S k)) tp ws φs)
          (HE   : wsat σ de_full (comp_wlist ws w0) (n + (S k))) :
      exists ws' φs',
        wptp safe (S k) tp' ws' (φs ++ φs') /\ wsat σ' de_full (comp_wlist ws' w0) (S k).
    Proof.
      revert tp σ w0 ws φs HSN HWTP HE. induction n; intros; inversion HSN; subst; clear HSN.
      (* no step is taken *)
      { inversion H; subst; clear H.
        exists ws (@nil vPred). split.
        - rewrite app_nil_r. assumption.
        - assumption.
      }
      rewrite -plus_n_Sm in HWTP, HE.
      inversion HS; subst; clear HS.
      (* a step is taken *)
      inversion H; subst; clear H.
      apply wptp_app_tp in HWTP. destruct HWTP as [ws1 [ws2 [φs1 [φs2 [EQws [EQφs [HWTP1 HWTP2]]]]]]].
      inversion HWTP2; subst; clear HWTP2; rewrite ->unfold_wp in WPE. destruct WPE as [_ WPE].
      edestruct (WPE (comp_wlist (ws1 ++ ws0) w0) (n + k) de_emp) as [HS _].
      - omega.
      - clear; de_auto_eq.
      - eapply spredNE, HE.
        apply dist_refl. eapply wsat_equiv.
        + clear; de_auto_eq.
        + rewrite /comp_wlist !fold_left_app /= comp_wlist_tofront /comp_wlist /=. reflexivity.  
      - edestruct HS as (w' & wfk' & HE' & HE'' & HWS); [eassumption | clear WPE HS]. destruct ef as [ef|].
        + edestruct IHn as [ws'' [φs'' [HSWTP'' HSE'']]]; first eassumption; first 2 last.
          * exists ws'' ([umconst ⊤] ++ φs''). split; last eassumption.
            rewrite List.app_assoc. eassumption.
          * rewrite -List.app_assoc. apply wptp_app.
            { eapply wptp_closure, HWTP1; omega. }
            rewrite -plus_n_Sm.
            constructor; [eassumption|].
            apply wptp_app; [eapply wptp_closure, WPTP; omega |].
            constructor; [|now constructor]. eassumption.
          * rewrite -plus_n_Sm. eapply spredNE, HWS.
            apply dist_refl. eapply wsat_equiv; first de_auto_eq.
            rewrite /comp_wlist !fold_left_app /= !fold_left_app. simpl fold_left.
            rewrite (comm _ wfk') -assoc. apply ra_op_proper; first reflexivity.
            rewrite comp_wlist_tofront /comp_wlist /=. reflexivity.
        + eapply IHn; clear IHn; first eassumption.
          * apply wptp_app.
            { eapply wptp_closure, HWTP1. omega. }
            rewrite -plus_n_Sm. simpl. rewrite app_nil_r.
            constructor; last (eapply wptp_closure, WPTP; omega).
            eapply propsMW, HE'. exists wfk'. reflexivity.
          * rewrite -plus_n_Sm. eapply spredNE, HWS.
            apply dist_refl. eapply wsat_equiv; first de_auto_eq.
            rewrite /comp_wlist !fold_left_app /= comp_wlist_tofront /comp_wlist /=. reflexivity.  
    Qed.

    Lemma adequacy_ht {safe m e P Q n k tp' σ σ' w}
            (HT  : valid (ht safe m P e Q))
            (HSN : stepn n ([e], σ) (tp', σ'))
            (HP  : P w (n + S k))
            (HE  : wsat σ de_full w (n + S k)) :
      exists ws' φs',
        wptp safe (S k) tp' ws' ((pvs m m <M< Q) :: φs') /\ wsat σ' de_full (comp_wlist ws' (1 w)) (S k).
    Proof.
      edestruct (preserve_wptp (1 w)) with (ws := [w]) as [ws' [φs' [HSWTP' HSWS']]]; first eassumption.
      - specialize (HT w (n + S k)). apply (applyImpl HT) in HP; try reflexivity; [|now apply unit_min].
        econstructor; [|now econstructor].
        eapply wpWeakenMask; last eassumption.
        de_auto_eq.
      - simpl comp_wlist. rewrite ra_op_unit. eassumption.
      - exists ws' φs'. now auto.
    Qed.

    (** This is a (relatively) generic adequacy statement for triples about an entire program: They always execute to a "good" threadpool. It does not expect the program to execute to termination.  *)
    Theorem adequacy_glob safe m e Q tp' σ σ' k'
            (HT  : valid (ht safe m (ownS σ) e Q))
            (HSN : steps ([e], σ) (tp', σ')):
      exists w0 ws' φs',
        wptp safe (S (S k')) tp' ws' ((pvs m m <M< Q) :: φs') /\ wsat σ' de_full (comp_wlist ws' w0) (S (S k')).
    Proof.
      destruct (refl_trans_n _ HSN) as [n HSN']. clear HSN.
      destruct (RL.res_vira) as [l Hval].
      pose (w := (fdEmpty, (ex_own σ, l)) : Wld).
      edestruct (adequacy_ht (w:=w) (k:=S k') HT HSN') as [ws' [φs' [HSWTP HWS]]]; clear HT HSN'.
      - rewrite -!plus_n_Sm. eexists ex_unit. reflexivity.
      - rewrite -!plus_n_Sm. hnf. eexists fdEmpty. intro.
        split.
        { rewrite /wt /=. split_conjs.
          - move=>i. exact I.
          - exact I.
          - assumption. }
        split.
        + rewrite /wt. reflexivity.
        + move=>i agP Heq. exfalso. rewrite /wt /= in Heq. exact Heq.
      - do 3 eexists. split; [eassumption|]. eassumption.
    Qed.

    Program Definition lift_vPred (Q : value -=> Prop): vPred :=
      n[(fun v => pcmconst (sp_const (Q v)))].
    Next Obligation.
      move=>v1 v2 EQv. destruct n; first exact:dist_bound.
      intros w m Hlt. rewrite /=. destruct m; first reflexivity.
      rewrite EQv. reflexivity.
    Qed.

    (* Adequacy as stated in the paper: for observations of the return value, after termination *)
    Theorem adequacy_obs safe m e (Q : value -=> Prop) e' tp' σ σ'
            (HT  : valid (ht safe m (ownS σ) e (lift_vPred Q)))
            (HSN : steps ([e], σ) (e' :: tp', σ'))
            (HV : is_value e') :
        Q (exist _ e' HV).
    Proof.
      edestruct adequacy_glob as [w0 [ws' [φs' [HSWTP HWS]]]]; try eassumption; [].
      inversion HSWTP; subst; clear HSWTP WPTP.
      rewrite ->unfold_wp in WPE. destruct WPE as [WPV _].
      edestruct (WPV HV (comp_wlist ws w0) O (de_minus de_full m)) as (w' & HQ & HWS').
      - unfold lt. reflexivity.
      - clear; de_auto_eq.
      - eapply spredNE, HWS. eapply dist_refl. eapply wsat_equiv.
        + clear; de_auto_eq.
        + rewrite comp_wlist_tofront. reflexivity.
      - clear- HQ HWS'. exact HQ.
    Qed.

    (* Adequacy for safe triples *)
    Lemma adequacy_safe_expr m e (Q : vPred) tp' σ σ' e'
            (HT  : valid (ht true m (ownS σ) e Q))
            (HSN : steps ([e], σ) (tp', σ'))
            (HE  : e' ∈ tp'):
      safeExpr e' σ'.
    Proof.
      edestruct adequacy_glob as [w' [rs' [φs' [HSWTP HWS]]]]; try eassumption.
      destruct (List.in_split _ _ HE) as [tp1 [tp2 HTP]]. clear HE. subst tp'.
      apply wptp_app_tp in HSWTP; destruct HSWTP as [ws1 [ws2 [_ [φs2 [EQrs [_ [_ HWTP2]]]]]]].
      inversion HWTP2; subst; clear HWTP2 WPTP.
      rewrite ->unfold_wp in WPE. destruct WPE as [_ WPE].
      edestruct (WPE (comp_wlist (ws1++ws) w') O de_emp) as [_ HSafe]; [unfold lt; reflexivity | de_auto_eq | |].
      - rewrite de_emp_union.
        eapply wsat_equiv, HWS; try reflexivity.
        rewrite /comp_wlist !fold_left_app. rewrite comp_wlist_tofront. reflexivity.
      - apply HSafe. reflexivity.
    Qed.

    Theorem adequacy_safe m e (Q : vPred) tp' σ σ'
            (HT  : valid (ht true m (ownS σ) e Q))
            (HSN : steps ([e], σ) (tp', σ')):
      (forall e', e' ∈ tp' -> is_value e') \/ exists tp'' σ'', step (tp', σ') (tp'', σ'').
    Proof. (* FIXME TODO use tp_safe *)
      assert (Hsafe: forall e', e' ∈ tp' -> safeExpr e' σ').
      { move=>e' HE. eapply adequacy_safe_expr; eassumption. }
      clear -Hsafe. induction tp' as [|e tp' IH].
      - left. move=>? [].
      - move:IH. case/(_ _)/Wrap.
        { move=>e' Hin. apply Hsafe. right. assumption. }
        case=>IH; last first.
        { destruct IH as [tp'' [σ'' Hstep]]. right.
          destruct Hstep.
          inversion H0=>{H0}; inversion H=>{H}; subst.
          do 2 eexists. eapply step_atomic; last eassumption; last reflexivity.
          rewrite app_comm_cons. reflexivity.
        }
        move:(Hsafe e)=>{Hsafe}. case/(_ _)/Wrap; first by left.
        case=>[Hsafe|[σ'' [e'' [ef Hstep]]]].
        + left. move=>e'. case.
          * by move =><-.
          * by auto.
        + right. do 2 eexists. eapply step_atomic with (t1:=[]); last eassumption; last reflexivity.
          reflexivity.
    Qed.

  End Adequacy.

  Section StatefulLifting.

    Implicit Types (P : Props) (n k : nat) (safe : bool) (m : DecEnsemble nat) (e : expr) (r : res) (σ : state) (w : Wld).

    Implicit Types (φ : expr * state * option expr -> Prop).
    Implicit Types (Q : vPred).

    (* Obligation common to lift_pred and lemma statement. *)
    Program Definition lift_esPred φ : expr * state * option expr -n> Props :=
      n[(fun c => pconst (φ c))].
    Next Obligation.
      move=>[[e1 σ1] ef1] [[e2 σ2] ef2] [[EQe EQσ] EQef].
      destruct n; first exact:dist_bound.
      destruct ef1, ef2; cbv in EQe, EQσ, EQef; subst; now destruct EQef || reflexivity.
    Qed.

    Program Definition lift_step_wp_quant safe m φ Q : expr * state * option expr -n> Props :=
      n[(fun c => let: (e',σ',ef) := c in
                  ((□lift_esPred φ c) ∧ ownS σ') -*
                    (wp safe m e' Q * match ef return _ with None => ⊤ | Some ef => wp safe de_full ef (umconst ⊤) end)  )].
    Next Obligation.
      move=>[[e1 σ1] ef1] [[e2 σ2] ef2] [[EQe EQσ] EQef].
      destruct n; first exact:dist_bound.
      destruct ef1, ef2; cbv in EQe, EQσ, EQef; subst; now destruct EQef || reflexivity.
    Qed.

    Lemma lift_step_wp {m safe e σ φ Q}
        (NVAL : ~is_value e)
        (STEP : forall e' σ' ef, prim_step (e,σ) (e',σ') ef -> φ(e',σ',ef))
        (SAFE : if safe then safeExpr e σ else True) :
      (ownS σ * ▹(all (lift_step_wp_quant safe m φ Q))) ⊑ wp safe m e Q.
    Proof.
      intros w n. destruct n; first (intro; exact:bpred).
      intros [[w1 w2] [Heqw [HoS Hwpe]]]. simpl in Heqw, Hwpe.
      rewrite ->unfold_wp. split; intros.
      { contradiction. }
      destruct HE as [rs HWT]. rename σ0 into σi.
      cbv zeta in HWT. rewrite ->comp_finmap_move in HWT.
      have Hσ: σ = σi /\ State (w2 · comp_finmap wf rs) = ex_unit.
      { clear - HoS Heqw HWT HLt. destruct HWT as [[_ [pv _]] [HS _]].
        destruct HoS as [t Heq]. destruct Heqw as [_ [HeqS _]]. simpl in *.
        destruct HS as [t' HS].
        unfold ra_op, ra_valid in *.
        destruct (fst (snd w1)), (fst (snd w2)), (fst (snd w)), t; simpl in *; try tauto; [].
        destruct (fst (snd (comp_finmap wf rs))), t'; simpl in *; try tauto; [].
        split; last reflexivity. rewrite -HS -HeqS -Heq. reflexivity. }
      destruct Hσ as [Hσ HStUnit]. clear HoS. subst σi.
      split; last first.
      { by move: SAFE {Hwpe} ; case: safe. }
      move=> e' σ' ef HStep {SAFE NVAL}.
      pose (w1' := (Invs w1, (ex_own σ', Res w1))).
      move: (Hwpe (e', σ', ef) w1' n (le_refl _))=>{Hwpe}. destruct n; first by (exfalso; omega).
      case; last move=>[w3e w3f] [Hw3 [Hwpe Hwpf]].
      { split; first by apply STEP. simpl. eexists ex_unit. reflexivity. }
      eexists w3e, w3f. split; last split.
      - eapply propsMN, Hwpe. omega.
      - destruct ef; last done. eapply propsMN, Hwpf. omega.
      - (* wsat σ' follows from wsat σ (by the construction of the new world). *)
        destruct k; first done. simpl.
        exists rs. rewrite comp_finmap_move.
        (* Rewrite Heqw in HWT - needs manual work *)
        assert(HWT': wsatTotal (S k) σ rs (m ∪ mf)%de (w1 · w2 · comp_finmap wf rs)).
        { eapply wsatTotal_proper, wsatTotal_dclosed, HWT; try reflexivity; last omega; [].
          apply cmra_op_dist; last reflexivity. eapply mono_dist, Heqw. omega. }
        clear HWT. destruct HWT' as [pv [HS HI]]. 
        (* Rewrite Hw3 in the goal - needs manual work *)
        rewrite /Mfst /Msnd in Hw3. simpl morph in Hw3. apply sp_eq_iff in Hw3.
        cut (wsatTotal (S k) σ' rs (m ∪ mf)%de (w1' · w2 · comp_finmap wf rs)).
        { eapply wsatTotal_proper; first reflexivity. apply cmra_op_dist; last reflexivity.
          rewrite (comm w1') (comm w3f). eapply mono_dist, Hw3. omega. }
        (* Get the projection to the physical state *)
        assert (HSt: State (w1' · w2 · comp_finmap wf rs) == ex_own σ').
        { clear -HStUnit. simpl in HStUnit. rewrite /State -assoc. simpl.
          rewrite HStUnit. reflexivity. }
        clear HStUnit.
        (* Now, finally, prove the actual thing *)
        split; last split.
        + clear- pv HSt Heqw HLt.
          destruct pv as [HIVal [HSVal HRVal]]. rewrite /w1'.
          split; last split; last 1 first.
          * assumption.
          * assumption.
          * simpl in HSt. by rewrite HSt.
        + rewrite HSt. reflexivity.
        + assumption.
    Qed.

    (* The "nicer looking" (ht-based) lemma is now a derived form. *)
    Program Definition plug_esPred φ safe m P P' Q: expr * state * option expr -n> Props :=
      n[(fun c => let: (e',σ',ef) := c in ht safe m (lift_esPred φ c ∧ (P * ownS σ')) e' Q ∧ match ef return _ with None => ⊤ | Some ef => ht safe de_full (lift_esPred φ c ∧ P') ef (umconst ⊤) end )].
    Next Obligation.
      move=>[[e1 σ1] ef1] [[e2 σ2] ef2] [[EQe EQσ] EQef].
      destruct n; first exact:dist_bound.
      destruct ef1, ef2; cbv in EQe, EQσ, EQef; subst; now destruct EQef || reflexivity.
    Qed.

    (* This is a temporary definition, used only in the proof of lift_step *)
    Program Definition plug_esPredWp φ safe m P P' Q: expr * state * option expr -n> Props :=
      n[(fun c => let: (e',σ',ef) := c in ((lift_esPred φ c ∧ (P * ownS σ')) → wp safe m e' (pvs m m <M< Q)) ∧ match ef return _ with None => ⊤ | Some ef => (lift_esPred φ c ∧ P') → wp safe de_full ef (pvs de_full de_full <M< (umconst ⊤)) end )].
    Next Obligation.
      move=>[[e1 σ1] ef1] [[e2 σ2] ef2] [[EQe EQσ] EQef].
      destruct n; first exact:dist_bound.
      destruct ef1, ef2; cbv in EQe, EQσ, EQef; subst; now destruct EQef || reflexivity.
    Qed.

    Lemma lift_step {m safe e σ φ P P' Q}
        (NVAL : ~is_value e)
        (STEP : forall e' σ' ef, prim_step (e,σ) (e',σ') ef -> φ(e',σ',ef))
        (SAFE : if safe then safeExpr e σ else True) :
      all (plug_esPred φ safe m P P' Q) ⊑ ht safe m (▹(P * P') * ownS σ) e Q.
    Proof.
      etransitivity; first (etransitivity; eapply pordR; last by (symmetry; eapply (box_all (plug_esPredWp φ safe m P P' Q)))).
      { apply all_equiv. move=>[[e' σ'] ef]. simpl morph. rewrite box_conj. destruct ef; first reflexivity.
        by rewrite box_top. }
      apply htIntro. etransitivity; last eapply (lift_step_wp (φ:=φ)); try eassumption; [].
      clear NVAL STEP SAFE.
      rewrite -box_conj_star assoc (comm _ (ownS _)). apply sc_pord; first by reflexivity.
      rewrite ->(later_mon (□_)). rewrite -later_star. apply later_pord.
      rewrite box_all. rewrite ->all_sc. apply all_pord.
      move=>[[e' σ'] ef]. simpl morph. rewrite -sc_si.
      rewrite ->(and_self (□_)), ->(and_self (□pconst _)).
      rewrite -!box_conj_star -(box_star (pcmconst _)) -box_conj_star box_star.
      rewrite !assoc (comm _ P) !assoc (comm _ (□pconst _)) comm.
      rewrite -!assoc. rewrite assoc assoc assoc. rewrite ->!box_elim. apply sc_pord.
      - eapply modus_ponens; last first.
        + rewrite ->sc_projR, and_projL. reflexivity.
        + rewrite ->sc_projL. apply and_R; split.
          { rewrite ->sc_projL. apply sc_projR. }
          rewrite (comm P). apply sc_pord; last reflexivity. apply sc_projL.
      - destruct ef; last exact:top_true. eapply modus_ponens; last first.
        + rewrite ->sc_projL, and_projR. eapply impl_pord; first reflexivity.
          eapply wpMon. move=>v. apply top_true.
        + rewrite ->sc_projR. rewrite comm. apply sc_and.
    Qed.

    Program Definition plug_atomic_esPred φ safe P': expr * state * option expr -n> Props :=
      n[(fun c => let: (e',σ',ef) := c in match ef return _ with None => ⊤ | Some ef => ht safe de_full (lift_esPred φ c ∧ P') ef (umconst ⊤) end )].
    Next Obligation.
      move=>[[e1 σ1] ef1] [[e2 σ2] ef2] [[EQe EQσ] EQef].
      destruct n; first exact:dist_bound.
      destruct ef1, ef2; cbv in EQe, EQσ, EQef; subst; now destruct EQef || reflexivity.
    Qed.

    Program Definition plug_atomic_esPost φ : value -n> Props :=
      n[(fun v:value => xist n[(fun c:state*option expr => ownS (Mfst c) ∧ lift_esPred φ (v, Mfst c, Msnd c))] )].
    Next Obligation.
      move=> [σ ef] [σ' ef'] [HEq1 HEq2]. destruct n; first exact:dist_bound.
      destruct ef, ef'; cbv in HEq1, HEq2; subst; now destruct HEq2 || reflexivity.
    Qed.
    Next Obligation.
      move=> v v' HEq. destruct n; first exact:dist_bound.
      hnf in HEq. eapply xist_dist=>σ' w. rewrite [dist]lock /= HEq -lock. reflexivity.
    Qed.

    Lemma lift_atomic_step {m safe e σ φ P Q}
        (AT   : atomic e)
        (STEP : forall e' σ' ef, prim_step (e,σ) (e',σ') ef -> φ(e',σ',ef))
        (SAFE : if safe then safeExpr e σ else True) :
      all (plug_atomic_esPred φ safe P) ⊑ ht safe m (▹P * ownS σ) e (plug_atomic_esPost φ).
    Proof.
      pose(φ' := fun (c : expr*state*option expr) => let: (e', σ', ef) := c in φ c /\ is_value e').
      rewrite -{2}(sc_top_unit P). etransitivity; last eapply (lift_step (φ := φ')); try (eassumption || exact: atomic_not_value); [|]; last first.
      { intros. split; first by exact:STEP. eapply atomic_step; eassumption. }
      apply all_pord. move=>[[e' σ' ef]]. simpl morph. apply and_R; split.
      - transitivity ⊤; first by exact:top_true. apply top_valid. apply htValid.
        apply pure_to_ctx=>[] [Hφ Hval]. rewrite sc_top_unit. erewrite (wpValue _ Hval).
        etransitivity; last by eapply pvsEnt. rewrite /plug_atomic_esPost. simpl morph.
        apply (xist_R (σ', ef)). simpl morph. apply and_R; split; first reflexivity.
        move: Hφ. apply ctx_to_pure. apply and_projL.
      - destruct ef; last reflexivity.
        rewrite {1}/ht. apply htIntro. rewrite ->box_elim. eapply modus_ponens; last first.
        + apply and_projL.
        + apply and_R; split.
          * rewrite ->and_projR. apply pure_to_ctx=>[] [Hφ _]. move:Hφ. apply ctx_to_pure.
            apply and_projL.
          * rewrite ->and_projR. apply and_projR.
    Qed.

  End StatefulLifting.

  Section StatelessLifting.

    Implicit Types (P : Props) (n k : nat) (safe : bool) (m : DecEnsemble nat) (e : expr) (r : res) (σ : state) (w : Wld).
    Implicit Types (Q R: vPred) (φ : expr -=> Prop).
    
    Program Definition lift_ePred (φ : expr -=> Prop) : expr -n> Props :=
      n[(fun v => pcmconst (sp_const (φ v)))].
    Next Obligation.
      move=>e1 e2 EQe.
      destruct n; first exact:dist_bound.
      cbv in EQe. subst. reflexivity.
    Qed.

    Program Definition plug_ePred safe m φ P Q: expr -n> Props :=
      n[(fun e' =>  (ht safe m (lift_ePred φ e' ∧ P) e' Q))].
    Next Obligation.
      intros e1 e2 EQe. destruct n; first exact:dist_bound.
      cbv in EQe. subst. reflexivity.
    Qed.

    Program Definition plug_ePredWp φ safe m P Q: expr -n> Props :=
      n[(fun e' => lift_ePred φ e' ∧ P → wp safe m e' Q)].
    Next Obligation.
      intros e1 e2 EQe. destruct n; first exact:dist_bound.
      cbv in EQe. subst. reflexivity.
    Qed.

    Lemma lift_pure_step_wp {safe m e} {φ : expr -=> Prop} P Q
            (RED  : reducible e)
            (STEP : forall σ e2 σ2, prim_step (e, σ) (e2, σ2) -> σ2 = σ /\ φ e2)
            (SAFE : forall σ, if safe then safeExpr e σ else True):
      (forall e', lift_ePred φ e' ∧ P ⊑ wp safe m e' Q) ->
      ▹P ⊑ wp safe m e Q.
    Proof.
      intros Hwpe' w n. destruct n; first (intro; exact:bpred).
      simpl. intros HP. rewrite ->unfold_wp. intros wf; intros.
      split; [| split; [| split ]]; first 2 last.
      { move=> e' K HDec; exfalso; exact: (reducible_not_fork RED HDec). }
      { by move: SAFE {Hwpe'} ; case: safe. }
      { move=> HV; exfalso. apply: reducible_not_value; eassumption. }
      (* The step-case of WP. *)
      move=>σ' ei ei' K Hfill Hstep.
      have HK: K = ε.
      { eapply step_same_ctx; first 2 last.
        - eassumption.
        - rewrite fill_empty. symmetry. eassumption.
        - do 2 eexists. eassumption. }
      subst K. rewrite fill_empty in Hfill. subst ei. rewrite fill_empty.
      specialize (STEP _ _ _ Hstep). destruct STEP as [Hσ Hφ]. subst σ'.
      exists w. split; last (eapply dpred, HE; omega).
      eapply Hwpe'. split.
      - exact Hφ.
      - eapply dpred, HP. omega.
    Qed.

    (* Again, the "ht-based" theorem is a derived form. *)
    Theorem lift_pure_step {safe m e} {φ : expr -=> Prop} P Q
            (RED  : reducible e)
            (STEP : forall σ e2 σ2, prim_step (e, σ) (e2, σ2) -> σ2 = σ /\ φ e2)
            (SAFE : forall σ, if safe then safeExpr e σ else True):
      (all (plug_ePred safe m φ P Q)) ⊑ ht safe m (▹P) e Q.
    Proof.
      etransitivity; first (etransitivity; eapply pordR; last by (symmetry; eapply (box_all (plug_ePredWp φ safe m P Q)))).
      { apply all_equiv. move=>e'. reflexivity. }
      apply htIntro. rewrite -box_conj_star. rewrite ->(later_mon (□_)).
      rewrite -later_star. apply (lift_pure_step_wp (φ:=φ)); try assumption; [].
      move=>e'. rewrite box_all. rewrite ->all_sc, ->all_and_r.
      apply (all_L e').
      change ((lift_ePred φ) e' ∧
              (□((lift_ePred φ) e' ∧ P → wp safe m e' Q) * P)
                ⊑ ((wp safe m) e') Q).
      rewrite ->box_elim.
      eapply modus_ponens; last first.
      - rewrite ->and_projR, sc_projL. reflexivity.
      - apply and_R; split.
        + apply and_projL.
        + rewrite ->and_projR. apply sc_projR.
    Qed.

    Lemma lift_pure_det_step safe m e e' P Q
          (RED  : reducible e)
          (STEP : forall σ e2 σ2, prim_step (e, σ) (e2, σ2) -> σ2 = σ /\ e2 = e')
          (SAFE : forall σ, if safe then safeExpr e σ else True):
      ht safe m P e' Q ⊑ ht safe m (▹P) e Q.
    Proof.
      pose(φ := s[(fun e => e = e')]).
      etransitivity; last first.
      - eapply (lift_pure_step (φ := φ)); assumption.
      - apply all_R=>e''.
        change (ht safe m P e' Q ⊑ (ht safe m (lift_ePred φ e'' ∧ P) e'' Q)).
        rewrite {1}/ht. apply htIntro.
        transitivity ((wp safe m e' Q) ∧ (lift_ePred φ) e'').
        { rewrite (comm _ P) assoc. apply and_pord; last reflexivity.
          rewrite ->box_elim. apply and_impl. reflexivity. }
        (* Now we fall back into the model. *)
        move=>w n [Hwp Heq]. destruct n; first exact:bpred.
        cbv in Heq. subst e''. assumption.
    Qed.

  End StatelessLifting.

End IRIS_META.

Module IrisMeta (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) : IRIS_META RL C R WP CORE PLOG.
  Include IRIS_META RL C R WP CORE PLOG.
End IrisMeta.
