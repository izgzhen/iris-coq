Require Import Ssreflect.ssreflect Ssreflect.ssrfun Omega List.
Require Import core_lang world_prop iris_core iris_plog.
Require Import ModuRes.RA ModuRes.CMRA ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.RAConstr ModuRes.DecEnsemble ModuRes.Agreement ModuRes.Lists ModuRes.Relations.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_META (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE).
  Export PLOG.

  Local Open Scope lang_scope.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.

  Section Adequacy.

    Local Open Scope list_scope.

    Implicit Types (P : Props) (w : Wld) (i n : nat) (safe : bool) (m : DecEnsemble nat) (e : expr) (Q φ : vPred) (r : res) (σ : state) (g : RL.res) (t : tpool).


    (* weakest-pre for a threadpool *)
    Inductive wptp (safe : bool) m n : tpool -> list Wld -> list vPred -> Prop :=
    | wp_emp : wptp safe m n nil nil nil
    | wp_cons e φ tp w ws φs
              (WPE  : wp safe m e φ w n)
              (WPTP : wptp safe m n tp ws φs) :
        wptp safe m n (e :: tp) (w :: ws) (φ :: φs).

    (* Trivial lemmas about split over append *)
    Lemma wptp_app safe m n tp1 tp2 ws1 ws2 φs1 φs2
          (HW1 : wptp safe m n tp1 ws1 φs1)
          (HW2 : wptp safe m n tp2 ws2 φs2) :
      wptp safe m n (tp1 ++ tp2) (ws1 ++ ws2) (φs1 ++ φs2).
    Proof.
      induction HW1; [| constructor]; now trivial.
    Qed.

    Lemma wptp_app_tp safe m n t1 t2 ws φs
          (HW : wptp safe m n (t1 ++ t2) ws φs) :
      exists ws1 ws2 φs1 φs2, ws1 ++ ws2 = ws /\ φs1 ++ φs2 = φs /\ wptp safe m n t1 ws1 φs1 /\ wptp safe m n t2 ws2 φs2.
    Proof.
      revert ws φs HW; induction t1; intros; inversion HW; simpl in *; subst; clear HW.
      - do 4 eexists. split; [|split; [|split; now econstructor]]; reflexivity.
      - do 4 eexists. split; [|split; [|split; now eauto using wptp]]; reflexivity.
      - apply IHt1 in WPTP; destruct WPTP as [ws1 [ws2 [φs1 [φs2 [EQws [EQφs [WP1 WP2]]]]]]]; clear IHt1.
        exists (w :: ws1) ws2 (φ :: φs1) φs2; simpl; subst; now auto using wptp.
    Qed.

    (* Closure under smaller steps *)
    Lemma wptp_closure safe m n1 n2 tp ws φs
          (HLe : n2 <= n1)
          (HW : wptp safe m n1 tp ws φs) :
      wptp safe m n2 tp ws φs.
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

    Lemma preserve_wptp w0 safe m n k tp tp' σ σ' ws φs
          (HSN  : stepn n (tp, σ) (tp', σ'))
          (HWTP : wptp safe m (n + (S k)) tp ws φs)
          (HE   : wsat σ m (comp_wlist ws w0) (n + (S k))) :
      exists ws' φs',
        wptp safe m (S k) tp' ws' (φs ++ φs') /\ wsat σ' m (comp_wlist ws' w0) (S k).
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
      (* atomic step *)
      { inversion H0; subst; clear H0.
        apply wptp_app_tp in HWTP. destruct HWTP as [ws1 [ws2 [φs1 [φs2 [EQws [EQφs [HWTP1 HWTP2]]]]]]].
        inversion HWTP2; subst; clear HWTP2; rewrite ->unfold_wp in WPE.
        edestruct (WPE (comp_wlist (ws1 ++ ws0) w0) (n + k) de_emp) as [_ [HS _]].
        + omega.
        + clear; de_auto_eq.
        + eapply spredNE, HE.
          apply dist_refl. eapply wsat_equiv.
          * clear; de_auto_eq.
          * rewrite /comp_wlist !fold_left_app /= comp_wlist_tofront /comp_wlist /=. reflexivity.  
        + edestruct HS as [w' [WPE' HE']];
          [reflexivity | eassumption | clear WPE HS].
          eapply IHn; clear IHn.
          * eassumption.
          * apply wptp_app.
            { eapply wptp_closure, HWTP1. omega. }
            rewrite -plus_n_Sm.
            constructor; [eassumption | eapply wptp_closure, WPTP; omega].
          * rewrite -plus_n_Sm. eapply spredNE, HE'.
            apply dist_refl. eapply wsat_equiv; first de_auto_eq.
            rewrite /comp_wlist !fold_left_app /= comp_wlist_tofront /comp_wlist /=. reflexivity.  
      }
      (* fork *)
      inversion H; subst; clear H.
      apply wptp_app_tp in HWTP; destruct HWTP as [ws1 [ws2 [φs1 [φs2 [EQws [EQφs [HWTP1 HWTP2]]]]]]].
      inversion HWTP2; subst; clear HWTP2; rewrite ->unfold_wp in WPE.
      edestruct (WPE (comp_wlist (ws1 ++ ws0) w0) (n + k) de_emp)  as [_ [_ [HF _]]].
      + omega.
      + clear; de_auto_eq.
      + eapply spredNE, HE. apply dist_refl. eapply wsat_equiv; first de_auto_eq.
        rewrite /comp_wlist !fold_left_app /= comp_wlist_tofront /comp_wlist /=. reflexivity.
      + specialize (HF _ _ eq_refl); destruct HF as [wfk [wret [WPE' [WPS HE']]]]; clear WPE.
        edestruct IHn as [ws'' [φs'' [HSWTP'' HSE'']]]; first eassumption; first 2 last.
        * exists ws'' ([umconst ⊤] ++ φs''). split; last eassumption.
          rewrite List.app_assoc. eassumption.
        * rewrite -List.app_assoc. apply wptp_app.
          { eapply wptp_closure, HWTP1; omega. }
          rewrite -plus_n_Sm.
          constructor; [eassumption|].
          apply wptp_app; [eapply wptp_closure, WPTP; omega |].
          constructor; [|now constructor]. eassumption.
        * rewrite -plus_n_Sm. eapply spredNE, HE'.
          apply dist_refl. eapply wsat_equiv; first de_auto_eq.
          rewrite /comp_wlist !fold_left_app /= !fold_left_app. simpl fold_left.
          rewrite (comm _ wfk) -assoc. apply ra_op_proper; first reflexivity.
          rewrite comp_wlist_tofront /comp_wlist /=. reflexivity.
    Qed.

    Lemma adequacy_ht {safe m e P Q n k tp' σ σ' w}
            (HT  : valid (ht safe m P e Q))
            (HSN : stepn n ([e], σ) (tp', σ'))
            (HP  : P w (n + S k))
            (HE  : wsat σ m w (n + S k)) :
      exists ws' φs',
        wptp safe m (S k) tp' ws' (Q :: φs') /\ wsat σ' m (comp_wlist ws' (1 w)) (S k).
    Proof.
      edestruct (preserve_wptp (1 w)) with (ws := [w]) as [ws' [φs' [HSWTP' HSWS']]]; first eassumption.
      - specialize (HT w (n + S k)). apply (applyImpl HT) in HP; try reflexivity; [|now apply unit_min].
        econstructor; [|now econstructor]. eassumption.
      - simpl comp_wlist. rewrite ra_op_unit. eassumption.
      - exists ws' φs'. now auto.
    Qed.

    (** This is a (relatively) generic adequacy statement for triples about an entire program: They always execute to a "good" threadpool. It does not expect the program to execute to termination.  *)
    Theorem adequacy_glob safe m e Q tp' σ σ' k'
            (HT  : valid (ht safe m (ownS σ) e Q))
            (HSN : steps ([e], σ) (tp', σ')):
      exists w0 ws' φs',
        wptp safe m (S (S k')) tp' ws' (Q :: φs') /\ wsat σ' m (comp_wlist ws' w0) (S (S k')).
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
      intros w m Hlt. rewrite /= /sp_constF. destruct m; first reflexivity.
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
      rewrite ->unfold_wp in WPE.
      edestruct (WPE (comp_wlist ws w0) O de_emp) as [HVal _].
      - unfold lt. reflexivity.
      - clear; de_auto_eq.
      - rewrite de_emp_union comp_wlist_tofront. eassumption.
      - destruct (HVal HV) as [w' [Hφ'' HE'']].
        exact Hφ''.
    Qed.

    (* Adequacy for safe triples *)
    Theorem adequacy_safe m e (Q : vPred) tp' σ σ' e'
            (HT  : valid (ht true m (ownS σ) e Q))
            (HSN : steps ([e], σ) (tp', σ'))
            (HE  : e' ∈ tp'):
      safeExpr e' σ'.
    Proof.
      edestruct adequacy_glob as [w' [rs' [φs' [HSWTP HWS]]]]; try eassumption.
      destruct (List.in_split _ _ HE) as [tp1 [tp2 HTP]]. clear HE. subst tp'.
      apply wptp_app_tp in HSWTP; destruct HSWTP as [ws1 [ws2 [_ [φs2 [EQrs [_ [_ HWTP2]]]]]]].
      inversion HWTP2; subst; clear HWTP2 WPTP.
      rewrite ->unfold_wp in WPE.
      edestruct (WPE (comp_wlist (ws1++ws) w') O de_emp) as [_ [_ [_ HSafe]]]; [unfold lt; reflexivity | de_auto_eq | |].
      - rewrite de_emp_union.
        eapply wsat_equiv, HWS; try reflexivity.
        rewrite /comp_wlist !fold_left_app. rewrite comp_wlist_tofront. reflexivity.
      - apply HSafe. reflexivity.
    Qed.

  End Adequacy.

  Section StatefulLifting.

    Implicit Types (P : Props) (n k : nat) (safe : bool) (m : DecEnsemble nat) (e : expr) (r : res) (σ : state) (w : Wld).

    Implicit Types (φ : expr * state -=> Prop).
    Implicit Types (Q : vPred).

    (* Obligation common to lift_pred and lemma statement. *)
    Program Definition lift_esPred φ : expr * state -n> Props :=
      n[(fun c => pcmconst(sp_const(φ c)))].
    Next Obligation.
      move=>[e1 σ1] [e2 σ2] [EQe EQσ].
      destruct n; first exact:dist_bound.
      cbv in EQe, EQσ. subst. reflexivity.
    Qed.

    Program Definition plug_esPred φ safe m P Q: expr * state -n> Props :=
      n[(fun c => let: (e',σ') := c in ht safe m (lift_esPred φ (e',σ') ∧ (P * ownS σ')) e' Q)].
    Next Obligation.
      move=>[e1 σ1] [e2 σ2] [EQe EQσ].
      destruct n; first exact:dist_bound.
      cbv in EQe, EQσ. subst. reflexivity.
    Qed.

    Program Definition plug_esPredWp φ safe m P Q: expr * state -n> Props :=
      n[(fun c => let: (e',σ') := c in (lift_esPred φ (e',σ') ∧ (P * ownS σ')) → wp safe m e' Q)].
    Next Obligation.
      move=>[e1 σ1] [e2 σ2] [EQe EQσ].
      destruct n; first exact:dist_bound.
      cbv in EQe, EQσ. subst. reflexivity.
    Qed.

    Lemma lift_step_wp {m safe e σ φ P Q}
        (RED : reducible e)
        (STEP : forall e' σ', prim_step (e,σ) (e',σ') -> φ(e',σ'))
        (SAFE : if safe then safeExpr e σ else True) :
      (forall e' σ', lift_esPred φ (e',σ') ∧ (P * ownS σ') ⊑ wp safe m e' Q) ->
      ▹P * ownS σ ⊑ wp safe m e Q.
    Proof.
      intros Hwpe' w n. destruct n; first (intro; exact:bpred).
      intros [[w1 w2] [Heqw [HP HoS]]]. simpl in Heqw, HP.
      rewrite ->unfold_wp; move=> wf k mf σi HLt HD [rs HWT].
      cbv zeta in HWT. rewrite ->comp_finmap_move in HWT.
      have Hσ: σ = σi /\ State (w1 · comp_finmap wf rs) = ex_unit.
      { clear - HoS Heqw HWT HLt. destruct HWT as [[_ [pv _]] [HS _]].
        destruct HoS as [t Heq]. destruct Heqw as [_ [HeqS _]]. simpl in *.
        destruct HS as [t' HS].
        unfold ra_op, ra_valid in *.
        destruct (fst (snd w1)), (fst (snd w2)), (fst (snd w)), t; simpl in *; try tauto; [].
        destruct (fst (snd (comp_finmap wf rs))), t'; simpl in *; try tauto; [].
        split; last reflexivity. rewrite -HS -HeqS -Heq. reflexivity. }
      destruct Hσ as [Hσ HStUnit]. clear HoS. subst σi.
      split; [| split; [| split ]]; first 2 last.
      { move=> e' K HDec; exfalso; exact: (reducible_not_fork RED HDec). }
      { by move: SAFE {Hwpe'} ; case: safe. }
      { move=> HV; exfalso. apply: reducible_not_value; eassumption. }
      move=> σ' ei e' K HDec HStep {SAFE}.
      have HK: K = ε.
      { move: HDec; rewrite -(fill_empty e) => HDec.
        have HRed1: reducible ei by exists σ (e',σ').
        eapply step_same_ctx; first (symmetry; eassumption); eassumption. }
      subst K. move: HDec HStep; rewrite 2!fill_empty. move=><- HStep {ei RED}.
      pose (w2' := (Invs w2, (ex_own σ', Res w2))).
      eexists (w1 · w2'). split.
      - (* We can now apply the wp we got. *)
        apply (Hwpe' e' σ'). split.
        { simpl. eapply STEP. assumption. }
        exists (w1, w2'). split; first (apply sp_eq_iff; reflexivity).
        split; simpl.
        * simpl. eapply propsMN, HP. omega.
        * eexists ex_unit. reflexivity.
      - (* wsat σ' follows from wsat σ (by the construction of the new world). *)
        destruct k; first exact I. simpl.
        assert(HWT': wsatTotal (S k) σ rs (m ∪ mf)%de (w1 · w2 · comp_finmap wf rs)).
        { eapply wsatTotal_proper, wsatTotal_dclosed, HWT; try reflexivity; last omega; [].
          apply cmra_op_dist; last reflexivity. eapply mono_dist, Heqw. omega. }
        clear HWT. destruct HWT' as [pv [HS HI]].
        exists rs. rewrite comp_finmap_move.
        assert (HSt: State (w1 · w2' · comp_finmap wf rs) == ex_own σ').
        { clear -HStUnit. rewrite /State (comm w1) -assoc. simpl. simpl in HStUnit.
          rewrite HStUnit. reflexivity. }
        clear HStUnit.
        split; last split.
        + clear- pv HSt Heqw HLt.
          destruct pv as [HIVal [HSVal HRVal]]. rewrite /w2'.
          split; last split; last 1 first.
          * assumption.
          * assumption.
          * simpl in HSt. by rewrite HSt.
        + rewrite HSt. reflexivity.
        + assumption.
    Qed.

    (* The "nicer looking" (ht-based) lemma is now a derived form. *)
    Lemma lift_step {m safe e σ φ P Q}
        (RED : reducible e)
        (STEP : forall e' σ', prim_step (e,σ) (e',σ') -> φ(e',σ'))
        (SAFE : if safe then safeExpr e σ else True) :
      all (plug_esPred φ safe m P Q) ⊑ ht safe m (▹P * ownS σ) e Q.
    Proof.
      etransitivity; first (etransitivity; eapply pordR; last by (symmetry; eapply (box_all (plug_esPredWp φ safe m P Q)))).
      { apply all_equiv. move=>[e' σ']. reflexivity. }
      apply htIntro. rewrite -box_conj_star assoc. rewrite ->(later_mon (□_)).
      rewrite -later_star. apply (lift_step_wp (φ:=φ)); try assumption; [].
      move=>e' σ'. rewrite box_all. rewrite <-assoc, ->all_sc, ->all_and_r.
      apply (all_L (e', σ')).
      change ((lift_esPred φ) (e', σ') ∧
              (□((lift_esPred φ) (e', σ') ∧ (P * ownS σ') → wp safe m e' Q) * (P * ownS σ'))
                ⊑ ((wp safe m) e') Q).
      rewrite ->box_elim.
      eapply modus_ponens; last first.
      - rewrite ->and_projR, sc_projL. reflexivity.
      - apply and_R; split.
        + apply and_projL.
        + rewrite ->and_projR. apply sc_projR.
    Qed.

    Program Definition lift_esPost φ : value -n> Props :=
      n[(fun v:value => ∃σ', ownS σ' ∧ lift_esPred φ (v, σ'))].
    Next Obligation.
      move=> σ σ' HEq. destruct n; first exact:dist_bound.
      hnf in HEq. subst. reflexivity.
    Qed.
    Next Obligation.
      move=> v v' HEq. destruct n; first exact:dist_bound.
      hnf in HEq. eapply xist_dist=>σ' w. rewrite [dist]lock /= HEq -lock. reflexivity.
    Qed.

    Lemma lift_atomic_det_step {m safe e σ φ P Q}
        (AT : atomic e)
        (STEP : forall e' σ', prim_step (e,σ) (e',σ') -> φ(e',σ'))
        (SAFE : if safe then safeExpr e σ else True) :
      valid(ht safe m (ownS σ) e (lift_esPost φ)).
    Proof.
      apply top_valid.
      assert (HEQ: ownS σ == ▹⊤ * ownS σ).
      { rewrite <-later_true. symmetry. by apply: sc_top_unit. }
      rewrite HEQ=>{HEQ}.
      pose(φ' := fun (c : expr*state) => let (e', σ') := c in φ c /\ is_value e').
      assert(Mφ': Proper (equiv ==> equiv) φ').
      { clear. move=>[e0 σ0] [e1 σ1] /= [HEQe HEQσ]. hnf in HEQe, HEQσ. subst. reflexivity. }
      etransitivity; last first.
      - eapply (lift_step (φ := mkMorph φ' Mφ')); last assumption.
        + by apply: atomic_reducible.
        + move=> e' σ' Hstep /=.
          split; first by apply: STEP.
          eapply atomic_step, Hstep. assumption.
      - clear STEP SAFE. apply all_R=>[] [e' σ'].
        change (⊤ ⊑ ht safe m (lift_esPred s[(φ')] (e',σ') ∧ (⊤ * ownS σ')) e' (lift_esPost φ)).
        apply top_valid. apply htValid. rewrite sc_top_unit.
        (* Now fall back to proving this in the model. *)
        move=>w n. destruct n; first (intro;exact:bpred).
        rewrite /= /sp_constF. move=>[[Hφ Hval] HownS].
        eapply wpValue; [].
        simpl. exists σ'. split; assumption.
    Grab Existential Variables.
    { assumption. }
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
