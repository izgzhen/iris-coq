Require Import ssreflect.
Require Import core_lang masks world_prop iris_core iris_plog.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Bullet Behavior "Strict Subproofs".

Module Type IRIS_META (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE).
  Export PLOG.

  Local Open Scope lang_scope.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.

  Section Adequacy.

    Local Open Scope list_scope.

    (* weakest-pre for a threadpool *)
    Inductive wptp (safe : bool) (m : mask) (w : Wld) (n : nat) : tpool -> list res -> list vPred -> Prop :=
    | wp_emp : wptp safe m w n nil nil nil
    | wp_cons e φ r tp rs φs
              (WPE  : wp safe m e φ w n r)
              (WPTP : wptp safe m w n tp rs φs) :
        wptp safe m w n (e :: tp) (r :: rs) (φ :: φs).

    (* Trivial lemmas about split over append *)
    Lemma wptp_app safe m w n tp1 tp2 rs1 rs2 φs1 φs2
          (HW1 : wptp safe m w n tp1 rs1 φs1)
          (HW2 : wptp safe m w n tp2 rs2 φs2) :
      wptp safe m w n (tp1 ++ tp2) (rs1 ++ rs2) (φs1 ++ φs2).
    Proof.
      induction HW1; [| constructor]; now trivial.
    Qed.

    Lemma wptp_app_tp safe m w n t1 t2 rs φs
          (HW : wptp safe m w n (t1 ++ t2) rs φs) :
      exists rs1 rs2 φs1 φs2, rs1 ++ rs2 = rs /\ φs1 ++ φs2 = φs /\ wptp safe m w n t1 rs1 φs1 /\ wptp safe m w n t2 rs2 φs2.
    Proof.
      revert rs φs HW; induction t1; intros; inversion HW; simpl in *; subst; clear HW.
      - do 4 eexists. split; [|split; [|split; now econstructor]]; reflexivity.
      - do 4 eexists. split; [|split; [|split; now eauto using wptp]]; reflexivity.
      - apply IHt1 in WPTP; destruct WPTP as [rs1 [rs2 [φs1 [φs2 [EQrs [EQφs [WP1 WP2]]]]]]]; clear IHt1.
        exists (r :: rs1) rs2 (φ :: φs1) φs2; simpl; subst; now auto using wptp.
    Qed.

    (* Closure under future worlds and smaller steps *)
    Lemma wptp_closure safe m (w1 w2 : Wld) n1 n2 tp rs φs
          (HSW : w1 ⊑ w2) (HLe : n2 <= n1)
          (HW : wptp safe m w1 n1 tp rs φs) :
      wptp safe m w2 n2 tp rs φs.
    Proof.
      induction HW; constructor; [| assumption].
      eapply uni_pred; [eassumption | reflexivity |].
      rewrite <- HSW; assumption.
    Qed.

    Lemma preserve_wptp safe m n k tp tp' σ σ' w rs φs
          (HSN  : stepn n (tp, σ) (tp', σ'))
          (HWTP : wptp safe m w (n + S k) tp rs φs)
          (HE   : wsat σ m (comp_list rs) w @ n + S k) :
      exists w' rs' φs',
        w ⊑ w' /\ wptp safe m w' (S k) tp' rs' (φs ++ φs') /\ wsat σ' m (comp_list rs') w' @ S k.
    Proof.
      revert tp σ w rs  φs HSN HWTP HE. induction n; intros; inversion HSN; subst; clear HSN.
      (* no step is taken *)
      { exists w rs (@nil vPred). split; [reflexivity|]. split.
        - rewrite List.app_nil_r. assumption.
        - assumption.
      }
      inversion HS; subst; clear HS.
      (* atomic step *)
      { inversion H0; subst; clear H0.
        apply wptp_app_tp in HWTP; destruct HWTP as [rs1 [rs2 [φs1 [φs2 [EQrs [EQφs [HWTP1 HWTP2]]]]]]].
        inversion HWTP2; subst; clear HWTP2; rewrite ->unfold_wp in WPE.
        edestruct (WPE w (n + S k) (comp_list (rs1 ++ rs0))) as [_ [HS _]];
          [reflexivity | now apply le_n | now apply mask_emp_disjoint | |].
        + eapply wsat_equiv, HE; try reflexivity; [apply mask_emp_union |].
          rewrite !comp_list_app; simpl comp_list; unfold equiv.
          rewrite ->assoc, (comm r), <- assoc. reflexivity.
        + edestruct HS as [w' [r' [HSW [WPE' HE']]]];
          [reflexivity | eassumption | clear WPE HS].
          setoid_rewrite HSW. eapply IHn; clear IHn.
          * eassumption.
          * apply wptp_app; [eapply wptp_closure, HWTP1; [assumption | now auto with arith] |].
            constructor; [eassumption | eapply wptp_closure, WPTP; [assumption | now auto with arith]].
          * eapply wsat_equiv, HE'; [now erewrite mask_emp_union| |reflexivity].
            rewrite !comp_list_app; simpl comp_list; unfold equiv.
            rewrite ->2!assoc, (comm r'). reflexivity.
      }
      (* fork *)
      inversion H; subst; clear H.
      apply wptp_app_tp in HWTP; destruct HWTP as [rs1 [rs2 [φs1 [φs2 [EQrs [EQφs [HWTP1 HWTP2]]]]]]].
      inversion HWTP2; subst; clear HWTP2; rewrite ->unfold_wp in WPE.
      edestruct (WPE w (n + S k) (comp_list (rs1 ++ rs0))) as [_ [_ [HF _]]];
        [reflexivity | now apply le_n | now apply mask_emp_disjoint | |].
      + eapply wsat_equiv, HE; try reflexivity; [apply mask_emp_union |].
        rewrite !comp_list_app; simpl comp_list; unfold equiv.
        rewrite ->assoc, (comm r), <- assoc. reflexivity.
      + specialize (HF _ _ eq_refl); destruct HF as [w' [rfk [rret [HSW [WPE' [WPS HE']]]]]]; clear WPE.
        setoid_rewrite HSW. edestruct IHn as [w'' [rs'' [φs'' [HSW'' [HSWTP'' HSE'']]]]]; first eassumption; first 2 last.
        * exists w'' rs'' ([umconst ⊤] ++ φs''). split; [eassumption|].
          rewrite List.app_assoc. split; eassumption.
        * rewrite -List.app_assoc. apply wptp_app; [eapply wptp_closure, HWTP1; [assumption | now auto with arith] |].
          constructor; [eassumption|].
          apply wptp_app; [eapply wptp_closure, WPTP; [assumption | now auto with arith] |].
          constructor; [|now constructor]. eassumption.
        * eapply wsat_equiv, HE'; try reflexivity; [symmetry; apply mask_emp_union |].
          rewrite comp_list_app. simpl comp_list. rewrite !comp_list_app. simpl comp_list.
          rewrite (comm rfk). rewrite ra_op_unit.
          rewrite (comm _ rfk). rewrite ->!assoc. apply: ra_op_proper; last by reflexivity.
          rewrite -assoc comm (comm rret). reflexivity.
    Qed.

    Lemma adequacy_ht {safe m e P Q n k tp' σ σ' w r}
            (HT  : valid (ht safe m P e Q))
            (HSN : stepn n ([e], σ) (tp', σ'))
            (HP  : P w (n + S k) r)
            (HE  : wsat σ m r w @ n + S k) :
      exists w' rs' φs',
        w ⊑ w' /\ wptp safe m w' (S k) tp' rs' (Q :: φs') /\ wsat σ' m (comp_list rs') w' @ S k.
    Proof.
      edestruct preserve_wptp with (rs:=[r]) as [w' [rs' [φs' [HSW' [HSWTP' HSWS']]]]]; [eassumption | | simpl comp_list; erewrite comm, ra_op_unit by apply _; eassumption | clear HT HSN HP HE].
      - specialize (HT w (n + S k) r). apply HT in HP; try reflexivity; [|now apply unit_min].
        econstructor; [|now econstructor]. eassumption.
      - exists w' rs' φs'. now auto.
    Qed.

    (** This is a (relatively) generic adequacy statement for triples about an entire program: They always execute to a "good" threadpool. It does not expect the program to execute to termination.  *)
    Theorem adequacy_glob safe m e Q tp' σ σ' k'
            (HT  : valid (ht safe m (ownS σ) e Q))
            (HSN : steps ([e], σ) (tp', σ')):
      exists w' rs' φs',
        wptp safe m w' (S k') tp' rs' (Q :: φs') /\ wsat σ' m (comp_list rs') w' @ S k'.
    Proof.
      destruct (steps_stepn _ _ HSN) as [n HSN']. clear HSN.
      pose (r := (ex_own σ, 1) : res).
      edestruct (adequacy_ht (w:=fdEmpty) (k:=k') (r:=r) HT HSN') as [w' [rs' [φs' [HW [HSWTP HWS]]]]]; clear HT HSN'.
      - exists 1; now rewrite ->ra_op_unit by apply _.
      - hnf. rewrite Plus.plus_comm. exists (fdEmpty (V:=res)). split.
        + unfold r, comp_map. simpl. rewrite ra_op_unit2. split; last reflexivity.
          unfold ra_valid. simpl. split; [|eapply ra_valid_unit; now apply _]. exact I.
        + intros i _; split; [reflexivity |].
          intros _ _ [].
      - do 3 eexists. split; [eassumption|]. assumption.
    Qed.

    Program Definition lift_vPred (Q : value -=> Prop): vPred :=
      n[(fun v => pcmconst (mkUPred (fun n r => Q v) _))].
    Next Obligation.
      firstorder.
    Qed.
    Next Obligation.
      intros x y H_xy P m r. simpl in H_xy. destruct n.
      - intros LEZ. exfalso. omega.
      - intros _. simpl. assert(H_xy': x == y) by assumption. rewrite H_xy'. tauto.
    Qed.


    (* Adequacy as stated in the paper: for observations of the return value, after termination *)
    Theorem adequacy_obs safe m e (Q : value -=> Prop) e' tp' σ σ'
            (HT  : valid (ht safe m (ownS σ) e (lift_vPred Q)))
            (HSN : steps ([e], σ) (e' :: tp', σ'))
            (HV : is_value e') :
        Q (exist _ e' HV).
    Proof.
      edestruct adequacy_glob as [w' [rs' [φs' [HSWTP HWS]]]]; try eassumption.
      inversion HSWTP; subst; clear HSWTP WPTP.
      rewrite ->unfold_wp in WPE.
      edestruct (WPE w' O) as [HVal _];
        [reflexivity | unfold lt; reflexivity | now apply mask_emp_disjoint | rewrite mask_emp_union; eassumption |].
      fold comp_list in HVal.
      specialize (HVal HV); destruct HVal as [w'' [r'' [HSW'' [Hφ'' HE'']]]].
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

  Notation "P ↔ Q" := ((P → Q) ∧ (Q → P)) (at level 95, no associativity) : iris_scope.	(* PDS *)
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
      σ == σ'.
    
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
      { move/(_ _ _ _ HStep): HP => HP; move: HStep HW; rewrite HP => HStep HW {HP σ}.
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
      move: (atomic_step _ _ _ _ HA HStep) => HV {HA HStep}.
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
        (HW : wsat σ' m u w @ S k)
        (Hu : r ⊑ u) :
      σ == σ'.
    Proof.
      move: (ra_valid_ord _ _ Hu (wsat_valid HW)) => Hv.
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
    Program Instance lift_pred_dist (φ : expr * state -> Props) n : Proper (dist n ==> dist n) φ.
    Next Obligation.
      move=> [e'1 σ'1] [e'2 σ'2] HEq w k r HLe.
      move: HEq HLe; case: n=>[|n] HEq HLt; first by exfalso; exact: lt0.
      by move: HEq=>/=[-> ->].
    Qed.

    Program Definition lift_pred φ : expr * state -n> Props :=
      n[(fun c => pcmconst(mkUPred(fun n r => φ c) _))].
    Next Obligation. done. Qed.

    Lemma lift_step {m safe e σ φ P Q}
        (RED : reducible e)
        (STEP : forall e' σ', prim_step (e,σ) (e',σ') -> φ(e',σ'))
        (SAFE : if safe then safeExpr e σ else True) :
      (∀c, let: (e',σ') := c in lift_pred φ (e',σ') → ht safe m (P * ownS σ') e' Q)
        ⊑ ht safe m (▹P * ownS σ) e Q.
    Proof.
      move=> wz nz rz Hfrom w1 HSw1 n r HLe _ HPS.
      rewrite unfold_wp; move=> w2 k rf mf σi HSw2 HLt _ HW.
      have Hσ: σ == σi.
      { clear - HPS HW HSw2.
        move: HPS => [r1 [r2 [Hr [_ /(propsMW HSw2) HS]]]] {HSw2}.
        apply: (ownS_wsat HS HW); move=> {HS HW}.
        exists (r1 · rf). move: Hr=><-.
        by rewrite -{1}assoc  [rf · _]comm {1}assoc; reflexivity. }
      split; [| split; [| split ]]; first 2 last.
      { move=> e' K HDec; exfalso; exact: (reducible_not_fork RED HDec). }
      { by move: SAFE {Hfrom}; rewrite Hσ; case: safe. }
      { move=> HV; exfalso; exact: reducible_not_value. }

      move=> σ' ei e' K HDec HStep {SAFE}.
      move: HW HStep; rewrite -Hσ => HW HStep {Hσ}.
      have HK: K = ε.
      { move: HDec; rewrite eq_sym_iff -(fill_empty e) => HDec.
        have HRed1: reducible ei by exists σ (e',σ').
        by apply: (step_same_ctx _ _ _ _ HDec HRed1 RED). }
      move: HDec HStep; rewrite HK 2!fill_empty; move=><- HStep {ei K HK RED}.

      (* have φ(e',σ'), so we can apply the triple… *)
      move/STEP: HStep => He' {STEP}.

      (* … after building P * ownS σ' *)
      move: HPS HLe HLt; case: n=>[| n'] HPS HLe HLt; first by exfalso; exact: lt0.
      move: HPS => [rP [rS [Hr [HP [rSg HrS]]]]]; rewrite/= in HP.
      pose (rS' := (ex_own σ', 1) : res).
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
      split; first by exact: (ex_fpu Hv).
      rewrite/rS' ra_op_prod_fst.
      move/ex_frame: Hv =>->.
      exact: ra_op_unit2.
    Qed.
    
    Program Definition lift_post φ : value -n> Props :=
      n[(fun v => ∃σ', ownS σ' ∧ lift_pred φ (`v, σ'))].
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

    Lemma lift_atomic_det {m safe e σ φ P Q}
        (AT : atomic e)
        (STEP : forall e' σ', prim_step (e,σ) (e',σ') -> φ(e',σ'))
        (SAFE : if safe then safeExpr e σ else True) :
      valid(ht safe m (ownS σ) e (lift_post φ)).
    Abort.
    
  End StatefulLifting.

  Section Lifting.

    Implicit Types (P : Props) (i : nat) (safe : bool) (m : mask) (e : expr) (Q R : vPred) (r : res).

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

    Program Definition plugExpr safe m φ P Q: expr -n> Props :=
      n[(fun e' => (lift_ePred φ e') → (ht safe m P e' Q))].
    Next Obligation.
      intros e1 e2 Heq w n' r HLt.
      destruct n as [|n]; [now inversion HLt | simpl in *].
      subst e2; tauto.
    Qed.

    Theorem lift_pure_step safe m e (φ : expr -=> Prop) P Q
            (RED  : reducible e)
            (STEP : forall σ e2 σ2, prim_step (e, σ) (e2, σ2) -> σ2 = σ /\ φ e2):
      (all (plugExpr safe m φ P Q)) ⊑ ht safe m (▹P) e Q.
    Abort.

    Lemma lift_pure_deterministic_step safe m e e' P Q
          (RED  : reducible e)
          (STEP : forall σ e2 σ2, prim_step (e, σ) (e2, σ2) -> σ2 = σ /\ e2 = e):
      ht safe m P e' Q ⊑ ht safe m (▹P) e Q.
    Abort.

  End Lifting.

End IRIS_META.

Module IrisMeta (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP) (PLOG: IRIS_PLOG RL C R WP CORE) : IRIS_META RL C R WP CORE PLOG.
  Include IRIS_META RL C R WP CORE PLOG.
End IrisMeta.
