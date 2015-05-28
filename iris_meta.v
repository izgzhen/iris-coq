Require Import Ssreflect.ssreflect Omega List.
Require Import core_lang world_prop iris_core iris_plog.
Require Import ModuRes.RA ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.RAConstr ModuRes.DecEnsemble ModuRes.Agreement ModuRes.Lists ModuRes.Relations.

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
      revert w0. induction ws; intros; simpl.
      - now rewrite comm.
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
          rewrite /comp_wlist !fold_left_app /= !fold_left_app /=.
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
        wptp safe m (S k') tp' ws' (Q :: φs') /\ wsat σ' m (comp_wlist ws' w0) (S k').
    Proof.
      destruct (refl_trans_n _ HSN) as [n HSN']. clear HSN.
      destruct (RL.res_vira) as [l Hval].
      pose (w := (fdEmpty, (ex_own σ, l)) : Wld).
      edestruct (adequacy_ht (w:=w) (k:=k') HT HSN') as [ws' [φs' [HSWTP HWS]]]; clear HT HSN'.
      - rewrite -plus_n_Sm. eexists ex_unit. reflexivity.
      - rewrite -plus_n_Sm. hnf. eexists fdEmpty. intro.
        assert (pv: (CMRA.cmra_valid wt) (S (n + k'))).
        { rewrite /wt /=. split_conjs.
          - move=>i. exact I.
          - exact I.
          - assumption. }
        exists pv. split.
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
      apply wptp_app_tp in HSWTP; destruct HSWTP as [rs1 [rs2 [_ [φs2 [EQrs [_ [_ HWTP2]]]]]]].
      inversion HWTP2; subst; clear HWTP2 WPTP.
      rewrite ->unfold_wp in WPE.
      edestruct (WPE w' O) as [_ [_ [_ HSafe]]];
        [reflexivity | unfold lt; reflexivity | now apply mask_emp_disjoint | |].
      - rewrite mask_emp_union.
        eapply wsat_equiv, HWS; try reflexivity.
        rewrite comp_list_app. simpl comp_list.
        rewrite ->(assoc (comp_list rs1)), ->(comm (comp_list rs1) r), <-assoc. reflexivity.
      - apply HSafe. reflexivity.
    Qed.

  End Adequacy.

  Section RobustSafety.

    Implicit Types (P : Props) (i n k : nat) (safe : bool) (m : mask) (e : expr) (v : value) (Q : vPred) (r : res) (w : Wld) (σ : state).

    Implicit Types (E : expr -n> Props) (Θ : Props).

    Program Definition restrictV E : vPred :=
      n[(fun v => E (` v))].
    Next Obligation.
      move=> v v' Hv w k r; move: Hv.
      case: n=>[_ Hk | n]; first by exfalso; omega.
      by move=> /= ->.
    Qed.

    Definition pure e := ~ atomic e /\ forall σ e' σ',
      prim_step (e,σ) (e',σ') ->
      σ = σ'.
    
    Definition restrict_lang := forall e,
      reducible e ->
      atomic e \/ pure e.

    Definition fork_compat E Θ := forall e,
      Θ ⊑ (E (fork e) → E e).
    
    Definition fill_compat E Θ := forall K e,
      Θ ⊑ (E (fill K e) ↔ E e * E (fill K fork_ret)).

    Definition atomic_compat E Θ m := forall e,
      atomic e ->
      Θ ⊑ ht false m (E e) e (restrictV E).

    Definition pure_compat E Θ m := forall e σ e',
      prim_step (e,σ) (e',σ) ->
      Θ ⊑ vs m m (E e) (E e').

    Lemma robust_safety {E Θ e m}
        (LANG : restrict_lang)
        (FORK : fork_compat E Θ)
        (FILL : fill_compat E Θ)
        (HT : atomic_compat E Θ m)
        (VS : pure_compat E Θ m) :
      □Θ ⊑ ht false m (E e) e (restrictV E).
    Proof.
      move=> wz nz rz HΘ w HSw n r HLe _ He.
      have {HΘ wz nz rz HSw HLe} HΘ: Θ w n 1 by rewrite/= in HΘ; exact: propsMWN HΘ.
      (* generalize IH's post-condition for the fork case *)
      pose post Q := forall v w n r, (E (`v)) w n r -> (Q v) w n r.
      set Q := restrictV E; have HQ: post Q by done.
      move: HΘ He HQ; move: n e w r Q; elim/wf_nat_ind => n IH e w r Q HΘ He HQ.
      rewrite unfold_wp; move=> w' k rf mf σ HSw HLt HD HW.
      (* specialize a bit *)
      move/(_ _ _ _ _ HΘ): FORK => FORK.
      move/(_ _ _ _ _ _ HΘ): FILL => FILL.
      move/(_ _ _)/biimpL: (FILL) => SPLIT; move/(_ _ _)/biimpR: FILL => FILL.
      move/(_ _ _ _ _ _ HΘ): HT => HT.
      move/(_ _ _ _ _ _ _ _ HΘ): VS => VS.
      have {IH HΘ Θ} IH: forall e w' r Q,
        w ⊑ w' -> (E e) w' k r -> post Q -> ((wp false m e) Q) w' k r.
      { move=> ? ? ? ? HSw'; move/(propsMWN HSw' (lelt HLt)): HΘ => HΘ. exact: IH. }
      have HLe: S k <= n by omega.
      split.
      (* e value *)
      { move=> HV {FORK FILL LANG HT VS IH}.
        exists w' r. split; [by reflexivity | split; [| done]].
        apply: HQ. exact: propsMWN He. }
      split; [| split; [| done]]; first last.
      (* e forks *)
      { move=> e' K HDec {LANG FILL HT VS}; rewrite HDec {HDec} in He.
        move/(SPLIT _ _ _ (prefl w) _ _ (lerefl n) unit_min)
          /(propsMWN HSw (lelt HLt)): He => [re' [rK [Hr [He' HK]]]] {SPLIT}.
        move/(FORK _ _ HSw _ _ (lelt HLt) unit_min): He' => He' {FORK}.
        exists w' re' rK. split; [by reflexivity | split; [exact: IH | split; [exact: IH |]]].
        move: HW; rewrite -Hr. exact: wsatM. }
      (* e steps *)
      (* both forthcoming cases work at step-indices S k and (for the IH) k. *)
      have HLt': k < S k by done.
      move=> σ' ei ei' K HDec HStep; rewrite HDec {HDec} in He.
      move/(SPLIT _ _ _ (prefl w) _ _ (lerefl n) unit_min)
        /(propsMWN HSw HLe): He => [rei [rK [Hr [Hei HK]]]] {SPLIT}.
      move: HW; rewrite -Hr -assoc => HW {Hr r}.
      have HRed: reducible ei by exists σ (ei',σ').
      case: (LANG ei HRed)=>[HA {VS} | [_ HP] {HT}] {LANG HRed}; last first.
      (* pure step *)
      { move/(_ _ _ _ HStep): HP => HP; move: HStep HW. rewrite HP => HStep HW {HP σ}.
        move/(_ _ _ _ HStep _ HSw _ _ HLe unit_min Hei): VS => VS {HStep HLe Hei}.
        move: HD; rewrite -{1}(mask_union_idem m) => HD.
        move/(_ _ _ _ _ _ (prefl w') HLt' HD HW): VS => [w'' [r' [HSw' [Hei' HW']]]] {HLt' HD HW}.
        have HLe': k <= S k by omega.
        exists w'' (r' · rK). split; [done | split; [| by move/(wsatM HLe'): HW'; rewrite assoc]].
        set HwSw'' := ptrans HSw HSw'.
        apply: IH; [done | | done].
        apply: (FILL _ _ _ HwSw'' _ _ (lelt HLt) unit_min).
        exists r' rK. split; first by reflexivity.
        split; [ exact: propsMN Hei' | exact: propsMWN HK ]. }
      (* atomic step *)
      move/(_ _ HA _ HSw (S k) _ HLe unit_min Hei): HT => {Hei HLe} Hei.
      (* unroll wp(ei,E)—step case—to get wp(ei',E) *)
      move: Hei; rewrite {1}unfold_wp => Hei.
      move/(_ _ _ _ _ _ (prefl w') HLt' HD HW): Hei => [_ [HS _]] {HLt' HW}.
      have Hεei: ei = fill ε ei by rewrite fill_empty.
      move/(_ _ _ _ _ Hεei HStep): HS => [w'' [r' [HSw' [Hei' HW']]]] {Hεei}.
      (* unroll wp(ei',E)—value case—to get E ei' *)
      move: Hei'; rewrite (fill_empty ei') {1}unfold_wp => Hei'.
      move: IH HLt HK HW' Hei'; case: k => [| k'] IH HLt HK HW' Hei'.
      { exists w'' r'. by split; [done | split; [exact: wpO | done]]. }
      have HLt': k' < S k' by done.
      move/(_ _ _ _ _ _ (prefl w'') HLt' HD HW'): Hei' => [Hv _] {HLt' HD HW'}.
      move: (atomic_step HA HStep) => HV {HA HStep}.
      move/(_ HV): Hv => [w''' [rei' [HSw'' [Hei' HW]]]].
      move: HW; rewrite assoc => HW.
      set Hw'Sw''' := ptrans HSw' HSw''.
      set HwSw''' := ptrans HSw Hw'Sw'''.
      exists w''' (rei' · rK). split; [done | split; [| done]].
      apply: IH; [done | | done].
      apply: (FILL _ _ _ HwSw''' _ _ (lelt HLt) unit_min).
      exists rei' rK. split; [by reflexivity | split; [done |]].
      have HLe: S k' <= S (S k') by omega.
      exact: propsMWN HK.
    Qed.

  End RobustSafety.

  Section StatefulLifting.

    Implicit Types (P : Props) (n k : nat) (safe : bool) (m : mask) (e : expr) (r : res) (σ : state) (w : Wld).

    (* A bit too specific to hoist to iris_plog.v without cause. *)
    Lemma ownS_wsat {σ w n r σ' m u k}
        (Hr : (ownS σ) w n r)
        (HW : wsat σ' m u w (S k))
        (Hu : r ⊑ u) :
      σ == σ'.
    Proof.
      move: (ra_valid_ord Hu (wsat_valid HW)) => Hv.
      move/(ownS_state Hv): Hr; move=>{n}; move/wsat_state: HW; move=>{m w k Hv}.
      move: Hu=>[[r'x r'g] [Hx Hg]]; move: Hx Hg.
      move: u=> [ux ug]; move: r=> [rx rg].
      rewrite ra_op_prod_fst 3!/fst.
      move=> Hux _ HD Hrx; move: Hux; move: Hrx->; move=>{r'g ug rg}.
      case: HD=>->; last by case: r'x.
      case: r'x=>[σ''||]; [done | | done].
      by rewrite ra_op_unit; elim.
    Qed.

    Implicit Types (φ : expr * state -=> Prop).
    Implicit Types (Q : vPred).

    (* Obligation common to lift_pred and lemma statement. *)
    Program Instance lift_esPred_dist (φ : expr * state -> Props) n : Proper (dist n ==> dist n) φ.
    Next Obligation.
      move=> [e'1 σ'1] [e'2 σ'2] HEq w k r HLe.
      move: HEq HLe. case: n=>[|n] HEq HLt; first by (exfalso; omega).
      by move: HEq=>/=[-> ->].
    Qed.

    Program Definition lift_esPred φ : expr * state -n> Props :=
      n[(fun c => pcmconst(mkUPred(fun n r => φ c) _))].
    Next Obligation. done. Qed.

    Lemma lift_step {m safe e σ φ P Q}
        (RED : reducible e)
        (STEP : forall e' σ', prim_step (e,σ) (e',σ') -> φ(e',σ'))
        (SAFE : if safe then safeExpr e σ else True) :
      (∀c, let: (e',σ') := c in lift_esPred φ (e',σ') → ht safe m (P * ownS σ') e' Q)
        ⊑ ht safe m (▹P * ownS σ) e Q.
    Proof.
      move=> wz nz rz Hfrom w1 HSw1 n r HLe _ HPS.
      rewrite unfold_wp; move=> w2 k rf mf σi HSw2 HLt _ HW.
      have Hσ: σ = σi.
      { clear - HPS HW HSw2.
        move: HPS => [r1 [r2 [Hr [_ /(propsMW HSw2) HS]]]] {HSw2}.
        apply: (ownS_wsat HS HW); move=> {HS HW}.
        exists (r1 · rf). move: Hr=><-.
        by rewrite -{1}assoc  [rf · _]comm {1}assoc; reflexivity. }
      split; [| split; [| split ]]; first 2 last.
      { move=> e' K HDec; exfalso; exact: (reducible_not_fork RED HDec). }
      { by move: SAFE {Hfrom}; rewrite Hσ; case: safe. }
      { move=> HV; exfalso. apply: reducible_not_value; eassumption. }

      move=> σ' ei e' K HDec HStep {SAFE}.
      move: HW HStep; rewrite -Hσ => HW HStep {Hσ}.
      have HK: K = ε.
      { move: HDec; rewrite eq_sym_iff -(fill_empty e) => HDec.
        have HRed1: reducible ei by exists σ (e',σ').
        by apply: (step_same_ctx HDec HRed1 RED). }
      move: HDec HStep; rewrite HK 2!fill_empty; move=><- HStep {ei K HK RED}.

      (* have φ(e',σ'), so we can apply the triple… *)
      move/STEP: HStep => He' {STEP}.

      (* … after building P * ownS σ' *)
      move: HPS HLe HLt; case: n=>[| n'] HPS HLe HLt; first by exfalso; omega.
      move: HPS => [rP [rS [Hr [HP [rSg HrS]]]]]; rewrite/= in HP.
      pose (rS' := (ex_own σ', 1:RL.res)).
      pose (r' := rP · rS').
      have HPS: (P * ownS σ') w2 k r'.
      { have {HLt} HLt: k <= n' by omega.
        move/(propsMWN HSw2 HLt): HP => HP.
        have HS': (ownS σ') w2 k rS' by exists 1; rewrite ra_op_unit; split; reflexivity.
        exists rP rS'. split; [by reflexivity | done]. }
      move/(_ (e',σ') _ HSw1 _ rz (lerefl nz) (prefl rz) He'): {He'} Hfrom => He'.
      have {HLe HLt} HLe: k <= nz by omega.
      move/(_ _ HSw2 _ r' HLe unit_min HPS): He' => He' {HLe HPS}.

      (* wsat σ' r' follows from wsat σ r (by the construction of r'). *)
      exists w2 r'. split; [by reflexivity | split; [done |]].
      have HLe: k <= S k by omega.
      move/(wsatM HLe): HW; move=>{He' HLe}.
      case: k=>[| k]; first done; move=>[rs [Hstate HWld]].
      exists rs. split; last done.
      clear - Hr HrS Hstate; move: Hstate=>[Hv _]; move: Hv.
      rewrite -Hr -HrS /r'/= => {Hr HrS r' rS}.
      rewrite (* ((P(gσ))f)s *) [rP · _]comm -3!assoc =>/ra_op_valid2 Hv {rSg}.  (* ((σP)f)s *)
      rewrite (* ((Pσ')f)s *) [rP · _]comm -2!assoc. (* σ'(P(fs)) *)
      split; first by exact: state_fps Hv.
      rewrite/rS' ra_op_prod_fst.
      move/state_sep: Hv =>->.
      exact: ra_op_unit2.
    Qed.
    
    Program Definition lift_esPost φ : value -n> Props :=
      n[(fun v:value => ∃σ', ownS σ' ∧ lift_esPred φ (v, σ'))].
    Next Obligation.
      move=> σ σ' HEq w k r HLt.
      move: HEq HLt; case: n=>[|n] HEq HLt; first by exfalso; omega.
      by move: HEq=>/=->.
    Qed.
    Next Obligation.
      move=> v v' HEq w k r HLt.
      move: HEq HLt; case: n=>[|n] HEq HLt; first by exfalso; omega.
      by move: HEq=>/=->.
    Qed.

    Lemma lift_atomic_det_step {m safe e σ φ P Q}
        (AT : atomic e)
        (STEP : forall e' σ', prim_step (e,σ) (e',σ') -> φ(e',σ'))
        (SAFE : if safe then safeExpr e σ else True) :
      valid(ht safe m (ownS σ) e (lift_esPost φ)).
    Proof.
      move=>w0 n0 r0.
      assert (HEQ: ownS σ == ▹⊤ * ownS σ).
      { rewrite <-later_true. symmetry. by apply: sc_top_unit. }
      rewrite HEQ=>{HEQ}.
      pose(φ' := fun (c : expr*state) => let (e', σ') := c in φ c /\ is_value e').
      assert(Mφ': Proper (equiv ==> equiv) φ').
      { clear. move=>[e0 σ0] [e1 σ1] /= [HEQe HEQσ]. subst. reflexivity. }
      eapply (lift_step (φ := mkMorph φ' Mφ')).
      - by apply: atomic_reducible.
      - move=> e' σ' Hstep /=.
        split; first by apply: STEP.
        eapply atomic_step, Hstep. assumption.
      - assumption.
      - case =>{SAFE} e' σ' w1 Hw01 n1 r1 Hn01 Hr01 [Hφ Hval].
        move=>w2 Hw12 n2 r2 Hn12 Hr12 Hσ'.
        rewrite ->sc_top_unit in Hσ'. rewrite unfold_wp.
        move=>w3 n3 rf mf σ'' Hw23 Hn23 Hm Hsat.
        (* The four cases of WP *)
        split; last split; last split.
        + move=>Hval2. exists w3 r2.
          split; first by reflexivity.
          split; last by assumption.
          exists σ'. split.
          * eapply propsM, Hσ'; [assumption|omega|reflexivity].
          * exact Hφ.
        + move=>? ? ? ? Hfill Hstep. exfalso.
          eapply values_stuck; first by eassumption.
          * eassumption.
          * do 2 eexists. eassumption.
        + move=>e'' K Hfill. clear - Hval Hfill. subst.
          contradiction (fork_not_value (fill_value Hval)).
        + move=>_. left. assumption.
    Qed.

  End StatefulLifting.

  Section StatelessLifting.

    Implicit Types (P : Props) (n k : nat) (safe : bool) (m : mask) (e : expr) (r : res) (σ : state) (w : Wld).
    Implicit Types (Q R: vPred) (φ : expr -=> Prop).
    
    Program Definition lift_ePred (φ : expr -=> Prop) : expr -n> Props :=
      n[(fun v => pcmconst (mkUPred (fun n r => φ v) _))].
    Next Obligation.
      firstorder.
    Qed.
    Next Obligation.
      intros x y H_xy P m r. simpl in H_xy. destruct n.
      - intros LEZ. exfalso. omega.
      - intros _. simpl. assert(H_xy': x == y) by assumption. rewrite H_xy'. tauto.
    Qed.

    Program Definition plug_ePred safe m φ P Q: expr -n> Props :=
      n[(fun e' => (lift_ePred φ e') → (ht safe m P e' Q))].
    Next Obligation.
      intros e1 e2 Heq w n' r HLt.
      destruct n as [|n]; [now inversion HLt | simpl in *].
      subst e2; tauto.
    Qed.

    Theorem lift_pure_step safe m e (φ : expr -=> Prop) P Q
            (RED  : reducible e)
            (STEP : forall σ e2 σ2, prim_step (e, σ) (e2, σ2) -> σ2 = σ /\ φ e2)
            (SAFE : forall σ, if safe then safeExpr e σ else True):
      (all (plug_ePred safe m φ P Q)) ⊑ ht safe m (▹P) e Q.
    Proof.
      move=> w0 n0 r0 Hfrom w1 Hw01 n1 r1 Hn01 _ HlaterP.
      rewrite unfold_wp => w2 n2 rf mf σ Hw12 Hn12 Hmask Hsat.
      (* The four cases of WP *)
      split; last split; last split.
      - move=>HV. exfalso. eapply reducible_not_value; eauto.
      - move=>σ' ei ei' K Hfill Hstep.
        have HK: K = ε.
        { eapply step_same_ctx; first 2 last.
          - eassumption.
          - rewrite fill_empty. symmetry. eassumption.
          - do 2 eexists. eassumption. }
        subst K. rewrite fill_empty in Hfill. subst ei. rewrite fill_empty.
        specialize (STEP _ _ _ Hstep). destruct STEP as [Hσ Hφ]. subst σ'.
        exists w2 r1.
        split; first reflexivity.
        split; last by (eapply wsatM, Hsat; omega).
        (* Now we just want to apply Hfrom. TODO: Is there a less annoying way to do that? *)
        assert (Hht: ht safe m P ei' Q w1 n1 r1).
        { move: Hfrom.
          move/(_ ei' _ Hw01 _ _ Hn01 (prefl _)).
          apply. simpl. apply Hφ. }
        clear Hfrom Hφ RED SAFE.
        destruct n1 as [|n1']; first by (exfalso; omega).
        specialize (Hht _ Hw12 n2 r1).
        eapply Hht.
        + omega.
        + apply: unit_min.
        + change (P w1 n1' r1) in HlaterP.
          eapply propsMWN, HlaterP.
          * assumption.
          * omega.
      - move=>e' K Hfill. exfalso.
        eapply reducible_not_fork; first by eexact RED.
        eassumption.
      - move=>Heq. subst safe. by apply SAFE.
    Qed.

    Lemma lift_pure_det_step safe m e e' P Q
          (RED  : reducible e)
          (STEP : forall σ e2 σ2, prim_step (e, σ) (e2, σ2) -> σ2 = σ /\ e2 = e')
          (SAFE : forall σ, if safe then safeExpr e σ else True):
      ht safe m P e' Q ⊑ ht safe m (▹P) e Q.
    Proof.
      move=> w0 n0 r0 Hfrom.
      pose(φ := s[(fun e => e = e')]).
      eapply lift_pure_step with (φ := φ).
      - assumption.
      - move=>? ? ? Hstep. simpl. apply STEP. assumption.
      - assumption.
      - move=>e2 {RED STEP SAFE} w1 Hw01 n1 r1 Hn01 Hr01 Hφ.
        hnf in Hφ. subst e2. eapply propsM, Hfrom; eassumption.
    Qed.

  End StatelessLifting.

End IRIS_META.

Module IrisMeta (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) : IRIS_META RL C R WP CORE PLOG.
  Include IRIS_META RL C R WP CORE PLOG.
End IrisMeta.
