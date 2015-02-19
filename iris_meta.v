Require Import ssreflect.
Require Import core_lang masks iris_wp.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Bullet Behavior "Strict Subproofs".

Module IrisMeta (RL : RA_T) (C : CORE_LANG).
  Module Export WP := IrisWP RL C.

  Delimit Scope iris_scope with iris.
  Local Open Scope iris_scope.

  Section Adequacy.
    Local Open Scope mask_scope.
    Local Open Scope ra_scope.
    Local Open Scope bi_scope.
    Local Open Scope lang_scope.
    Local Open Scope list_scope.

    (* weakest-pre for a threadpool *)
    Inductive wptp (safe : bool) (m : mask) (w : Wld) (n : nat) : tpool -> list pres -> list vPred -> Prop :=
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
      - do 4 eexists. split; [|split; [|split; now econstructor] ]; reflexivity.
      - do 4 eexists. split; [|split; [|split; now eauto using wptp] ]; reflexivity.
      - apply IHt1 in WPTP; destruct WPTP as [rs1 [rs2 [φs1 [φs2 [EQrs [EQφs [WP1 WP2] ] ] ] ] ] ]; clear IHt1.
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
        apply wptp_app_tp in HWTP; destruct HWTP as [rs1 [rs2 [φs1 [φs2 [EQrs [EQφs [HWTP1 HWTP2] ] ] ] ] ] ].
        inversion HWTP2; subst; clear HWTP2; rewrite ->unfold_wp in WPE.
        edestruct (WPE w (n + S k) (comp_list (rs1 ++ rs0))) as [_ [HS _] ];
          [reflexivity | now apply le_n | now apply mask_emp_disjoint | |].
        + eapply wsat_equiv, HE; try reflexivity; [apply mask_emp_union |].
          rewrite !comp_list_app; simpl comp_list; unfold equiv.
          rewrite ->assoc, (comm (_ r)), <- assoc. reflexivity.       
        + edestruct HS as [w' [r' [HSW [WPE' HE'] ] ] ];
          [reflexivity | eassumption | clear WPE HS].
          setoid_rewrite HSW. eapply IHn; clear IHn.
          * eassumption.
          * apply wptp_app; [eapply wptp_closure, HWTP1; [assumption | now auto with arith] |].
            constructor; [eassumption | eapply wptp_closure, WPTP; [assumption | now auto with arith] ].
          * eapply wsat_equiv, HE'; [now erewrite mask_emp_union| |reflexivity].
            rewrite !comp_list_app; simpl comp_list; unfold equiv.
            rewrite ->2!assoc, (comm (_ r')). reflexivity.
      }
      (* fork *)
      inversion H; subst; clear H.
      apply wptp_app_tp in HWTP; destruct HWTP as [rs1 [rs2 [φs1 [φs2 [EQrs [EQφs [HWTP1 HWTP2] ] ] ] ] ] ].
      inversion HWTP2; subst; clear HWTP2; rewrite ->unfold_wp in WPE.
      edestruct (WPE w (n + S k) (comp_list (rs1 ++ rs0))) as [_ [_ [HF _] ] ];
        [reflexivity | now apply le_n | now apply mask_emp_disjoint | |].
      + eapply wsat_equiv, HE; try reflexivity; [apply mask_emp_union |].
        rewrite !comp_list_app; simpl comp_list; unfold equiv.
        rewrite ->assoc, (comm (_ r)), <- assoc. reflexivity.
      + specialize (HF _ _ eq_refl); destruct HF as [w' [rfk [rret [HSW [WPE' [WPS HE'] ] ] ] ] ]; clear WPE.
        setoid_rewrite HSW. edestruct IHn as [w'' [rs'' [φs'' [HSW'' [HSWTP'' HSE''] ] ] ] ]; first eassumption; first 2 last.
        * exists w'' rs'' ([umconst ⊤] ++ φs''). split; [eassumption|].
          rewrite List.app_assoc. split; eassumption.
        * rewrite -List.app_assoc. apply wptp_app; [eapply wptp_closure, HWTP1; [assumption | now auto with arith] |].
          constructor; [eassumption|].
          apply wptp_app; [eapply wptp_closure, WPTP; [assumption | now auto with arith] |].
          constructor; [|now constructor]. eassumption.
        * eapply wsat_equiv, HE'; try reflexivity; [symmetry; apply mask_emp_union |].
          rewrite comp_list_app. simpl comp_list. rewrite !comp_list_app. simpl comp_list.
          rewrite (comm (_ rfk)). erewrite ra_op_unit by apply _.
          rewrite (comm _ (_ rfk)). rewrite ->!assoc. eapply ra_op_proper;[now apply _ | |reflexivity]. unfold equiv.
          rewrite <-assoc, (comm (_ rret)). rewrite (comm (_ rret)). reflexivity.
    Qed.

    Lemma adequacy_ht {safe m e P Q n k tp' σ σ' w r}
            (HT  : valid (ht safe m P e Q))
            (HSN : stepn n ([e], σ) (tp', σ'))
            (HP  : P w (n + S k) r)
            (HE  : wsat σ m (ra_proj r) w @ n + S k) :
      exists w' rs' φs',
        w ⊑ w' /\ wptp safe m w' (S k) tp' rs' (Q :: φs') /\ wsat σ' m (comp_list rs') w' @ S k.
    Proof.
      edestruct preserve_wptp with (rs:=[r]) as [w' [rs' [φs' [HSW' [HSWTP' HSWS'] ] ] ] ]; [eassumption | | simpl comp_list; erewrite comm, ra_op_unit by apply _; eassumption | clear HT HSN HP HE].
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
      pose↓ r := (ex_own _ σ, 1:RL.res).
      { unfold ra_valid. simpl. eapply ra_valid_unit. now apply _. }
      edestruct (adequacy_ht (w:=fdEmpty) (k:=k') (r:=r) HT HSN') as [w' [rs' [φs' [HW [HSWTP HWS] ] ] ] ]; clear HT HSN'.
      - exists (ra_unit _); now rewrite ->ra_op_unit by apply _.
      - hnf. rewrite Plus.plus_comm. exists (fdEmpty (V:=pres)). split.
        + unfold r, comp_map. simpl. rewrite ra_op_unit2. split; first assumption.
          reflexivity.
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
      edestruct adequacy_glob as [w' [rs' [φs' [HSWTP HWS] ] ] ]; try eassumption.
      inversion HSWTP; subst; clear HSWTP WPTP.
      rewrite ->unfold_wp in WPE.
      edestruct (WPE w' O) as [HVal _];
        [reflexivity | unfold lt; reflexivity | now apply mask_emp_disjoint | rewrite mask_emp_union; eassumption |].
      fold comp_list in HVal.
      specialize (HVal HV); destruct HVal as [w'' [r'' [HSW'' [Hφ'' HE''] ] ] ].
      exact Hφ''.
    Qed.

    (* Adequacy for safe triples *)
    Theorem adequacy_safe m e (Q : vPred) tp' σ σ' e'
            (HT  : valid (ht true m (ownS σ) e Q))
            (HSN : steps ([e], σ) (tp', σ'))
            (HE  : e' ∈ tp'):
      safeExpr e' σ'.
    Proof.
      edestruct adequacy_glob as [w' [rs' [φs' [HSWTP HWS] ] ] ]; try eassumption.
      destruct (List.in_split _ _ HE) as [tp1 [tp2 HTP] ]. clear HE. subst tp'.
      apply wptp_app_tp in HSWTP; destruct HSWTP as [rs1 [rs2 [_ [φs2 [EQrs [_ [_ HWTP2] ] ] ] ] ] ].
      inversion HWTP2; subst; clear HWTP2 WPTP.
      rewrite ->unfold_wp in WPE.
      edestruct (WPE w' O) as [_ [_ [_ HSafe] ] ];
        [reflexivity | unfold lt; reflexivity | now apply mask_emp_disjoint | |].
      - rewrite mask_emp_union.
        eapply wsat_equiv, HWS; try reflexivity.
        rewrite comp_list_app. simpl comp_list.
        rewrite ->(assoc (comp_list rs1)), ->(comm (comp_list rs1) (ra_proj r)), <-assoc. reflexivity.
      - apply HSafe. reflexivity.
    Qed.

  End Adequacy.

  Section Lifting.

    Local Open Scope mask_scope.
    Local Open Scope ra_scope.
    Local Open Scope bi_scope.
    Local Open Scope lang_scope.

    Implicit Types (P : Props) (i : nat) (safe : bool) (m : mask) (e : expr) (Q R : vPred) (r : pres).


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
      n[(fun e => (lift_ePred φ e) ∨ (ht safe m P e Q))].
    Next Obligation.
      intros e1 e2 Heq w n' r HLt.
      destruct n as [|n]; [now inversion HLt | simpl in *].
      subst e2; tauto.
    Qed.

    Theorem lift_pure_step safe m e (φ : expr -=> Prop) P Q
            (RED  : reducible e)
            (STEP : forall σ e2 σ2, prim_step (e, σ) (e2, σ2) -> σ2 = σ /\ φ e2):
      (all (plugExpr safe m φ P Q)) ⊑ ht safe m (▹P) e Q.
    Proof.
    Admitted.

    Lemma lift_pure_deterministic_step safe m e e' P Q
          (RED  : reducible e)
          (STEP : forall σ e2 σ2, prim_step (e, σ) (e2, σ2) -> σ2 = σ /\ e2 = e):
      ht safe m P e' Q ⊑ ht safe m (▹P) e Q.
    Proof.
    Admitted.

  End Lifting. 

End IrisMeta.
