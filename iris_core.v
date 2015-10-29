Require Import Ssreflect.ssreflect Omega.
Require Import world_prop core_lang.
Require Import ModuRes.RA ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.RAConstr ModuRes.Agreement.
Require Import ModuRes.CMRA ModuRes.DecEnsemble.

Set Bullet Behavior "Strict Subproofs".

(* We hack a bit here to avoid spelling out module types for functor results.
   The hack that involves least work is to duplicate the definition of our final
   resource type as a module type (which is how we can use it, circumventing the
   Coq restrictions) and as a module (to show the type can be instantiated). *)
Module Type IRIS_RES (RL : VIRA_T) (C : CORE_LANG) <: CMRA_EXT_T.
  Instance state_type : Setoid C.state := discreteType.
  Instance state_metr : metric (ex C.state) := discreteMetric.
  Instance state_cmetr : cmetric (ex C.state) := discreteCMetric.
  Instance state_cmra_valid : CMRA_valid (ex C.state) := discreteCMRA_valid. 
  Instance state_cmra : CMRA (ex C.state) := discreteCMRA.
  Instance state_cmra_ext : CMRAExt (ex C.state) := discreteCMRAExt. 

  Instance logR_metr : metric RL.res := discreteMetric.
  Instance logR_cmetr : cmetric RL.res := discreteCMetric.
  Instance logR_cmra_valid : CMRA_valid RL.res := discreteCMRA_valid. 
  Instance logR_cmra : CMRA RL.res := discreteCMRA.
  Instance logR_cmra_ext : CMRAExt RL.res := discreteCMRAExt.

  Definition res := (ex C.state * RL.res)%type.
  Instance res_type : Setoid res := _.
  Instance res_op   : RA_op res := _.
  Instance res_unit : RA_unit res := _.
  Instance res_valid: RA_valid res := _.
  Instance res_ra   : RA res := _.
  
  Instance res_metric : metric res := _.
  Instance res_cmetric : cmetric res := _.
  Instance res_pord: preoType res := pord_ra.
  Instance res_pcmetric : pcmType res := _.

  Instance res_cmra_valid : CMRA_valid res := _.
  Instance res_cmra : CMRA res := _.
  Instance res_cmra_ext : CMRAExt res := _.
  Instance res_vira : VIRA res := _.

End IRIS_RES.

Module IrisRes (RL : VIRA_T) (C : CORE_LANG) <: IRIS_RES RL C.
  Include IRIS_RES RL C. (* I cannot believe Coq lets me do this... *)
End IrisRes.

(* This instantiates the framework(s) provided by ModuRes to obtain a higher-order
   separation logic with ownership, later, necessitation and equality.
   The logic has "worlds" in its model, but nothing here uses them yet. *)
Module Type IRIS_CORE (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R).
  Export C.
  Export R.
  Export WP.

  Delimit Scope iris_scope with iris.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.

  (** Instances for a bunch of types (some don't even have Setoids) *)
  Instance state_type : Setoid C.state := _.
  Instance state_metr : metric C.state := discreteMetric.
  Instance state_cmetr : cmetric C.state := discreteCMetric.
  
  Instance nat_type : Setoid nat := discreteType.
  Instance nat_metr : metric nat := discreteMetric.
  Instance nat_cmetr : cmetric nat := discreteCMetric.

  Definition mask := DecEnsemble nat.
  Instance mask_type : Setoid mask := _.
  Instance mask_metr : metric mask := discreteMetric.
  Instance mask_cmetr : cmetric mask := discreteCMetric.

  Instance expr_type : Setoid expr := discreteType.
  Instance expr_metr : metric expr := discreteMetric.
  Instance expr_cmetr : cmetric expr := discreteCMetric.

  (* We use this type quite a bit, so give it and its instances names *)
  Definition vPred := value -n> Props.
  Instance vPred_type  : Setoid vPred  := _.
  Instance vPred_metr  : metric vPred  := _.
  Instance vPred_cmetr : cmetric vPred := _.

  (** The final thing we'd like to check is that the space of
      propositions does indeed form a complete BI algebra.

      The following instance declaration checks that an instance of
      the complete BI class can be found for Props (and binds it with
      a low priority to potentially speed up the proof search).
   *)
  (* RJ: For some reason, these terms do not (all) use the Wld_op, Wld_RA, ... instances.
     I have no idea, why. *)
  Instance Props_valid : validBI Props | 0 := _.
  Instance Props_top : topBI Props | 0 := _.
  Instance Props_bot : botBI Props | 0 := _.
  Instance Props_and : andBI Props | 0 := _.
  Instance Props_or : orBI Props | 0 := _.
  Instance Props_impl : implBI Props | 0 := _.
  Instance Props_sc : scBI Props | 0 := _.
  Instance Props_si : siBI Props | 0 := _.
  Instance Props_eq : eqBI Props | 0 := _.
  Instance Props_all : allBI Props | 0 := _.
  Instance Props_xist : xistBI Props | 0 := _.
  Instance Props_Lattice : Lattice Props | 0 := _.
  Instance Props_CBI : ComplBI Props | 0 := _.
  Instance Props_Eq : EqBI Props | 0 := _.

  Implicit Types (P Q : Props) (w : Wld) (n i k : nat) (r : res) (g : RL.res) (σ : state).

  (* Helpful when dealing with Iris propositions *)
  Definition Invs (w: Wld) := Mfst w.
  Arguments Invs w /.
  Definition State (w: Wld) := Mfst (Msnd w).
  Arguments State w /.
  Definition Res (w: Wld) := Msnd (Msnd w).
  Arguments Res w /.

  (* This probably doesn't reduce in helpful ways. But re-defining the entire thing here is too annoying. *)
  Definition pconst (p: Prop): Props := pcmconst(sp_const p).

  (* Simple view lemmas. *)

  Section Views.
    Lemma lelt {n k} (H : k < n) : k <= n.
    Proof. by omega. Qed.

    Lemma lt0 (n : nat) :  ~ n < 0. Proof. by omega. Qed.

    Lemma propsMW {P w n w'} (HSw : w ⊑ w') : P w n -> P w' n.
    Proof. exact: (mu_mono P HSw). Qed.

    Lemma propsMN {P w n n'} (HLe : n' <= n) : P w n -> P w n'.
    Proof. apply: dpred HLe. Qed.

    Lemma propsM {P w n w' n' } (HSw : w ⊑ w') (HLe : n' <= n) :
      P w n -> P w' n'.
    Proof.
      move=> HP. eapply propsMW, propsMN, HP; assumption.
    Qed.

    Lemma biimpL {P Q : Props} {w n} : (P ↔ Q) w n -> (P → Q) w n.
    Proof. by move=>[L _]. Qed.

    Lemma biimpR {P Q : Props} {w n} : (P ↔ Q) w n -> (Q → P) w n.
    Proof. by move=>[_ R]. Qed.

    Lemma applyImpl {P Q: Props} {w n w' n'} (HImpl: (P → Q) w n) (HSw : w ⊑ w') (HLe : n' <= n):
      P w' n' -> Q w' n'.
    Proof.
      move=>HP. destruct HSw as [wF EQw]. rewrite <-EQw. rewrite comm. eapply HImpl; first assumption.
      simpl morph. by rewrite comm EQw.
    Qed.
    
    Lemma propsNE {P : Props} {w1 w2 n} (EQw : w1 = n = w2) :
      P w1 n -> P w2 n.
    Proof.
      apply spredNE. by rewrite EQw.
    Qed.

    Lemma pure_to_ctx (P: Prop) (Q R: Props):
      (P -> Q ⊑ R) -> pconst P ∧ Q ⊑ R.
    Proof.
      intros H.
      intros w n [p q]. destruct n; first exact:bpred.
      apply H; assumption.
    Qed.

    Lemma ctx_to_pure (P: Prop) (Q R: Props):
      pconst P ∧ Q ⊑ R -> (P -> Q ⊑ R).
    Proof.
      intros H.
      intros p w n q. destruct n; first exact:bpred.
      apply H. split; assumption.
    Qed.

      
  End Views.

  Section SimplProper.
    
    Lemma dist_props_simpl U (R : relation U) (f : U -> Props) n {RS : Symmetric R}
          (HP : forall u1 u2 w m, m <= n -> R u1 u2 -> f u1 w m -> f u2 w m) :
      Proper (R ==> dist n) f.
    Proof.
      intros u1 u2 HRu m; split; intros HF;
      eapply HP; eassumption || symmetry; eassumption.
    Qed.

    Lemma dist_props_simpl2 U V (RU : relation U) (RV : relation V)
          (f : U -> V -> Props) n {RS : Symmetric RU} {VS : Symmetric RV}
          (HP : forall u1 u2 v1 v2 w m, m <= n -> RU u1 u2 -> RV v1 v2 -> f u1 v1 w m -> f u2 v2 w m) :
      Proper (RU ==> RV ==> dist n) f.
    Proof.
      intros u1 u2 HRu v1 v2 HRv m; split; intros HF;
      eapply HP; eassumption || symmetry; eassumption.
    Qed.

  End SimplProper.

  Section Resources.

    Lemma state_sep {σ g rf} (Hv : ↓(ex_own σ, g) · rf) : fst rf == 1 (ex_own σ)
.
    Proof. move: (ra_sep_prod Hv) => [Hs _]; exact: ra_sep_ex Hs. Qed.

    Lemma state_fps {σ g σ' rf} (Hv : ↓(ex_own σ, g) · rf) : ↓(ex_own σ', g) · rf.
    Proof. exact: (ra_fps_fst (ra_fps_ex σ σ') rf). Qed.

  End Resources.

  Section FinmapInvs.
    Lemma finmap_invs_unit (I: nat -f> ra_agree PreProp):
      1 I == I.
    Proof.
      move=>i. rewrite /= /fdMap_pre. destruct (I i); last reflexivity.
      reflexivity.
    Qed.

    Lemma world_invs_valid w1 w2 μ i n:
      cmra_valid w1 n -> w2 ⊑ w1 -> Invs w2 i = n = Some μ -> cmra_valid μ n.
    Proof.
      move=>Hval Hle Heq. destruct w1 as [I1 [S1 g1]], w2 as [I2 [S2 g2]]. destruct Hval as [Hval _]. simpl in Heq. apply ra_pord_iff_prod_pord in Hle.
      destruct Hle as [Hle _]. simpl in Hle.
      apply ra_pord_iff_ext_pord in Hle.
      clear S1 g1 S2 g2. specialize (Hval i). specialize (Hle i).
      destruct n; first exact:bpred.
      destruct (I2 i); last contradiction Heq.
      destruct (I1 i); last contradiction Hle. simpl in Hle.
      simpl in Heq. eapply spredNE.
      - rewrite -Heq. reflexivity.
      - eapply cmra_valid_ord; eassumption.
    Qed.

    Lemma world_invs_extract w1 w2 μ μ' i n:
      cmra_valid w1 n -> w2 ⊑ w1 -> Invs w2 i = n = Some (μ' · μ) ->
      Invs w1 i = n = Some μ.
    Proof.
      move=> Hval [w' Hleq] Hlu. unfold Invs. rewrite -Hleq.
      simpl morph. rewrite {1}/ra_op /ra_op_finprod fdComposeRed.
      destruct n; first exact:dist_bound.
      rewrite /Invs /= in Hlu.  destruct (fst w2 i) as [μ2|] eqn:Hw2; last contradiction Hlu.
      destruct (fst w' i) as [μ1|] eqn:Hw1; simpl in *.
      - rewrite Hlu assoc (comm _ μ). apply ra_ag_prod_dist. eapply world_invs_valid; first eexact Hval; first reflexivity.
        rewrite -Hleq. rewrite /Invs. simpl morph. instantiate (1:=i).
        rewrite {1}/ra_op /ra_op_finprod fdComposeRed. rewrite Hw2 Hw1. rewrite /finprod_op.
        apply option_dist_Some.
        now rewrite Hlu (comm μ) assoc.
      - rewrite Hlu comm. apply ra_ag_prod_dist. eapply world_invs_valid; first eexact Hval; first reflexivity.
        rewrite -Hleq. rewrite /Invs. simpl morph. instantiate (1:=i).
        rewrite {1}/ra_op /ra_op_finprod fdComposeRed. rewrite Hw2 Hw1. simpl.
        now rewrite comm.
    Qed.
  End FinmapInvs.

  (** And now we're ready to build the IRIS-specific connectives! *)

  Section Later.
    (** Note: this could be moved to BI, since it's possible to define
        more generally. However, we should first figure out a concise
        set of axioms. **)
    Program Definition later: Props -> Props :=
      fun P => m[(fun w => later_sp (P w))].
    Next Obligation.
      move=>w1 w2 EQw. simpl. eapply later_sp_dist. rewrite EQw. reflexivity.
    Qed.
    Next Obligation.
      move=>w1 w2 Hw n H. destruct n as [|n]; first exact I.
      simpl. rewrite <-Hw. exact H.
    Qed.

    Global Instance later_contractive: contractive later.
    Proof.
      move=>n P Q EQ w. rewrite/later. simpl morph. eapply contr.
      rewrite EQ. reflexivity.
    Qed.

    Global Instance later_dist n : Proper (dist n ==> dist n) later.
    Proof.
      pose (lf := contractive_nonexp later _).
      move=> ? ? ?.
        by apply: (met_morph_nonexp lf).
    Qed.

    Global Instance later_equiv : Proper (equiv ==> equiv) later.
    Proof.
      eapply dist_equiv; now apply _.
    Qed.

    Global Instance later_pord: Proper (pord ++> pord) later.
    Proof.
      move=>P Q HPQ w n HP. destruct n; first done. simpl in *. by apply HPQ.
    Qed.
  End Later.
  Notation " ▹ p " := (later p) (at level 35) : iris_scope.


  Section LaterProps.
    Lemma later_mon P: P ⊑ ▹P.
    Proof.
      move=>w n H. simpl morph.
      destruct n as [|n]; first exact I.
      simpl. eapply dpred; last eassumption. omega.
    Qed.

    Lemma loeb P (HL: later P ⊑ P): valid P.
      intros w n. induction n.
      - eapply HL. exact I.
      - eapply HL. exact IHn.
    Qed.

    Lemma later_impl P Q:
      ▹(P → Q) == ▹P → ▹Q.
    Proof.
      intros w n. split; (destruct n; first (intro; exact:bpred)); intro H.
      - simpl in H. move=>wf /= m Hle HP.
        destruct m; first exact I. apply H; assumption || omega.
      - move=>wf /= m Hle HP. apply (H wf (S m)); assumption || omega.
    Qed.

    Lemma later_wand P Q:
      ▹(P -* Q) == ▹P -* ▹Q.
    Proof.
      intros w n. split; (destruct n; first (intro; exact:bpred)); intro H.
      - simpl in H. move=>wf /= m Hle HP.
        destruct m; first exact I. apply H; assumption || omega.
      - move=>wf /= m Hle HP. apply (H wf (S m)); assumption || omega.
    Qed.

    Lemma later_top P:
      ▹⊤ == ⊤.
    Proof.
      intros w [|n]; split; simpl; tauto.
    Qed.

     Lemma later_disj P Q :
      ▹(P ∨ Q) == ▹P ∨ ▹Q.
    Proof.
      intros w [|n]; split; simpl; tauto.
    Qed.
    
    Lemma later_conj P Q :
      ▹(P ∧ Q) == ▹P ∧ ▹Q.
    Proof.
      intros w [|n]; split; simpl; tauto.
    Qed.
    
    Lemma later_star P Q:
      ▹(P * Q) == ▹P * ▹Q.
    Proof.
      intros w n; split; (destruct n; first tauto).
      - destruct n.
        { move=>_. exists (1 w, w). simpl.
          split; last (split; exact:bpred).
          now rewrite ra_op_unit. }
        move=>[[w1 w2] [/= Heq [HP HQ]]].
        edestruct Wld_CMRAExt as [w'1 [w'2 [Heq' [Hdist1 Hdist2]]]]; first eexact Heq; first reflexivity.
        exists (w'1, w'2). split; first now rewrite Heq'. simpl in *.
        split; (eapply propsNE; last eassumption); assumption.
      - move=>[[w1 w2] [Heq [HP HQ]]]. destruct n; first exact I.
        exists (w1, w2). simpl in *. split; last tauto.
        now apply dist_mono.
    Qed.

    Lemma strong_loeb P: (▹P → P) ⊑ P.
    Proof.
      transitivity (⊤ ∧ (▹P → P)).
      { apply and_R; split; last reflexivity. apply top_true. }
      apply and_impl. apply top_valid. apply loeb. apply and_impl.
      eapply modus_ponens; last by apply and_projR.
      rewrite later_impl. eapply modus_ponens; last by eapply and_projL.
      rewrite->and_projR. apply later_mon.
    Qed.

    Section LaterQuant.
      Context {T} `{cT : cmetric T}.
      Context (φ : T -n> Props).

      Lemma later_all : ▹all φ == all (n[(later)] <M< φ).
      Proof.
        intros w n; split; intros H; (destruct n; first exact:bpred); intros t; simpl in *; apply H.
      Qed.

      Lemma xist_later : xist (n[(later)] <M< φ) ⊑ ▹xist φ. (* The other direction does not hold for empty T. *)
      Proof.
        intros w n H. do 2 (destruct n; first done). exact H.
      Qed.

      Lemma later_xist (HI: inhabited T):
        ▹xist φ ⊑ xist (n[(later)] <M< φ).
      Proof.
        move=>w n /= H. destruct n; first done.
        destruct n.
        - destruct HI as [t]. exists t. simpl. exact:bpred.
        - destruct H as [t H]. by exists t.
      Qed.

    End LaterQuant.
    
    
  End LaterProps.

  Section Necessitation.
    (** Note: this could be moved to BI, since it's possible to define
        more generally. However, we should first figure out a concise
        set of axioms. **)

(*    Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances. *)

    Program Definition box : Props -> Props :=
      fun P => m[(fun w => p[(fun n => P (1 w) n)] )].
    Next Obligation.
      exact: bpred.
    Qed.
    Next Obligation.
      intros n m HLe. by apply propsMN.
    Qed.
    Next Obligation.
      intros w1 w2 EQw m HLt. 
      have/(met_morph_nonexp P) H : 1 w1 = n = 1 w2 by apply cmra_unit_dist. 
      by apply H.
    Qed.
    Next Obligation.
      intros w1 w2 HSub. 
      have/(propsMW (P := P)) : 1 w1 ⊑ 1 w2. 
      { destruct HSub as [wr HSub].
        rewrite -HSub.
        rewrite comm.
        destruct (ra_unit_mono w1 wr) as [wm Hm].
        rewrite Hm. exists wm. rewrite comm. reflexivity.
      }
      tauto.
    Qed.

    Global Instance box_dist n: Proper (dist n ==> dist n) box.
    Proof.
      intros p1 p2 EQp w m HLt.
      by apply EQp.
    Qed.

    Global Instance box_equiv : Proper (equiv ==> equiv) box.
    Proof.
      eapply dist_equiv; now apply _.
    Qed.

  End Necessitation.

  Notation "□ P" := (box P) (at level 35, right associativity) : iris_scope.

  (** Lemmas about box **)
  Section NecessitationProps.
    Lemma box_intro P Q (Hpr : □P ⊑ Q) :
      □P ⊑ □Q.
    Proof.
      intros w n HP. apply Hpr.
      by rewrite /box/= ra_unit_idem.
    Qed.

    Lemma box_elim P :
      □P ⊑ P.
    Proof.
      move=>w n. rewrite /box/=. apply propsMW. 
      exists w. now rewrite comm ra_op_unit.
    Qed.

    Lemma box_top : □⊤ == ⊤.
    Proof.
      now auto.
    Qed.

    Lemma box_disj P Q :
      □(P ∨ Q) == □P ∨ □Q.
    Proof.
      intros w n.
      split; intros [|]; by [left|right].
    Qed.
    
    Lemma box_conj P Q :
      □(P ∧ Q) == □P ∧ □Q.
    Proof.
      intros w n. 
      split; tauto.
    Qed.

    Lemma box_star P Q :
      □(P * Q) == □P * □Q.
    Proof.
      intros w n. split; (destruct n; first (intro; exact:bpred)); intros [[wP wQ] [Heq [HP HQ]]]. 
      - rewrite (lock (1 w)) /= -lock in Heq.
        exists (1 w, w). simpl; split_conjs; simpl.
        + now rewrite ra_op_unit.
        + rewrite ra_unit_idem. eapply propsNE; first eexact Heq.
          eapply propsMW, HP. eexists; now erewrite comm.
        + eapply propsNE; first eexact Heq.
          eapply propsMW, HQ. simpl. eexists; now erewrite comm.
      - simpl in Heq. exists (1 w, 1 w). rewrite (lock (1w)) /= -lock; split_conjs.
        + rewrite /fst /snd. rewrite -{1}(ra_unit_idem w). rewrite ra_op_unit. reflexivity.
        + simpl. eapply propsNE; first (eapply cmra_unit_dist; eexact Heq).
          eapply propsMW, HP. apply ra_unit_proper_pord. exists wQ; now rewrite comm.
        + simpl. eapply propsNE; first (eapply cmra_unit_dist; eexact Heq).
          eapply propsMW, HQ. apply ra_unit_proper_pord. exists wP; now rewrite comm.
    Qed.

    Lemma box_conj_star P Q :
      □P * Q == □P ∧ Q.
    Proof.
      apply pord_antisym; first by eapply sc_and.
      intros w n [HP HQ]. destruct n; first exact I. exists (1w, w).
      split; last split; simpl.
      - now rewrite ra_op_unit.
      - rewrite ra_unit_idem. assumption.
      - assumption.
    Qed.

    Lemma box_impl P Q:
      □(P → Q) ⊑ □P → □Q.
    (* The backwards direction does NOT hold: We can have □⊤ → own m
       without having □(⊤ → own m).  *)
    Proof.
      apply and_impl. rewrite -box_conj. apply box_intro.
      rewrite ->box_elim. apply and_impl. reflexivity.
    Qed.

    Lemma box_wand P Q:
      □(P -* Q) ⊑ □P -* □Q.
    (* The backwards direction does NOT hold: We can have □⊤ -* own m
       without having □(⊤ -* own m).  *)
    Proof.
      apply sc_si. rewrite -box_star. apply box_intro.
      rewrite ->box_elim. apply sc_si. reflexivity.
    Qed.

    Lemma box_impl_si P Q:
      □(P → Q) == □(P -* Q).
    Proof.
      apply pord_antisym.
      { apply box_intro. rewrite ->box_elim. apply impl_si. }
      apply box_intro. apply and_impl. rewrite <-box_conj_star.
      rewrite ->box_elim. apply sc_si. reflexivity.
    Qed.
    
    Lemma box_dup P :
      □P == □P * □P.
    Proof.
      apply pord_antisym.
      - intros w n.
        intros HP. destruct n; first exact:bpred.
        exists (w, 1 w). 
        split; last by simpl; rewrite !ra_unit_idem. simpl morph.
        do 3 red.
        now rewrite (ra_op_unit2).
      - by apply sc_projL.
    Qed.
    
    Lemma box_box P :
      □ □ P == □ P.
    Proof.
      apply pord_antisym.
      - exact: box_elim.
      - apply box_intro. reflexivity.
    Qed.

    Lemma box_later P:
      (▹□P) == □▹P.
    Proof.
      move=>w n; split; intros H; exact H.
    Qed.

    Section BoxQuant.
      Context {T} `{cT : cmetric T}.

      Lemma box_eq (t1 t2: T):
        t1 === t2 == □(t1 === t2).
      Proof.
        apply pord_antisym; last exact:box_elim.
        move=>w n H. exact H.
      Qed.
      
      Context (φ : T -n> Props).

      Lemma box_all : □all φ == all (n[(box)] <M< φ).
      Proof. done. Qed.

      Lemma box_xist : □xist φ == xist (n[(box)] <M< φ).
      Proof. done. Qed.

    End BoxQuant.
  End NecessitationProps.

  Section IntEqProps.

    (* On Props, valid biimplication, valid internal equality, and external equality coincide. *)


    Remark valid_biimp_intEq {P Q} : valid(P ↔ Q) -> valid(P === Q).
    Proof.
      move=> H _ nz wz n HLt.
      move/(_ wz n): H => [Hpq Hqp]. split.
      - move/(_ (1 wz) n _) : Hpq => Hpq. by rewrite -(ra_op_unit2 (t:=wz)).
      - move/(_ (1 wz) n _) : Hqp => Hqp. by rewrite -(ra_op_unit2 (t:=wz)).
    Qed.

    Remark valid_intEq_equiv {P Q} : valid(P === Q) -> P == Q.
    Proof. move=> H w n; exact: H. Qed.

    Remark valid_equiv_biimp {P Q} : P == Q -> valid(P ↔ Q).
    Proof.
      move=> H wz nz; split; move=> w HSw n HLe. 
      - by rewrite -(H (wz · w)).
      - by rewrite  (H (wz · w)).
    Qed.

    (* Internal equality implies biimplication, but not vice versa. *)

    Remark biimp_equiv {P Q}: P === Q ⊑ (P ↔ Q).
    Proof.
      have HLt n n' : n' <= n -> n' < S n by omega.
      move=> w n H. destruct n; first exact:bpred.
      split;
      move=> w' n' HLt' HP;
      move/(_ (w · w') n' _): H => [Hpq Hqp];
      [exact: Hpq | exact: Hqp].
    Qed.

    (* Note that (P ↔ Q) ⊑ (P === Q) does NOT hold: The first says
       that the equivalence holds in all future worlds, the second says
       it holds in *all* worlds. *)

  End IntEqProps.

  Section Timeless.

    Definition timelessP P w n :=
      forall w' k (HLt : (S k) < n) (Hp : P w' (S k)), P w' (S (S k)).

    Program Definition timeless P : Props :=
      m[(fun w => p[(fun n => timelessP P w n)] )].
    Next Obligation.
      move=>? ? ? ?. exfalso. omega.
    Qed.
    Next Obligation.
      intros n1 n2 HLe HP w' k HLt. eapply HP.
      omega.
    Qed.
    Next Obligation.
      intros w1 w2 EQw k; simpl. intros HLt.
      split; intros HT w' m HLt' Hp.
      - eapply HT; done.
      - eapply HT; done.
    Qed.
    Next Obligation.
      intros w1 w2 Hsub n; simpl; intros HT w' m HLt Hp.
      eapply HT, Hp; done.
    Qed.

    Global Instance timeless_dist n:
      Proper (dist n ==> dist n) timeless.
    Proof.
      apply dist_props_simpl; first apply _.
      move=>P1 P2 w m Hle Heq HT; repeat intro.
      eapply spredNE, HT; try eassumption; [|].
      - eapply mmorph_proper; last reflexivity. eapply mono_dist, Heq. omega.
      - eapply spredNE, Hp. eapply mmorph_proper; last reflexivity.
        symmetry. eapply mono_dist, Heq. omega.
    Qed.

    Lemma timeless_boxed P:
      timeless P == □timeless P.
    Proof.
      apply pord_antisym; last exact:box_elim.
      move=>w n H. exact H.
    Qed.

    Lemma timeless_conj P Q:
      timeless P ∧ timeless Q ⊑ timeless (P ∧ Q).
    Proof.
      move=>w n [HTP HTQ] /=. repeat intro. split.
      - eapply HTP, Hp; done.
      - eapply HTQ, Hp; done.
    Qed.

    Lemma timeless_disj P Q:
      timeless P ∧ timeless Q ⊑ timeless (P ∨ Q).
    Proof.
      move=>w n [HTP HTQ] /=. repeat intro. destruct Hp.
      - left. eapply HTP; done.
      - right. eapply HTQ; done.
    Qed.

    Lemma timeless_star P Q:
      timeless P ∧ timeless Q ⊑ timeless (P * Q).
    Proof.
      move=>w n [HTP HTQ] /=. repeat intro. destruct Hp as [[w1 w2] [Heq [HP HQ]]]. simpl in *.
      edestruct Wld_CMRAExt as [w'1 [w'2 [Heq' [Hdist1 Hdist2]]]]; first eexact Heq; first reflexivity.
      exists (w'1, w'2). simpl in *. split_conjs.
      - now rewrite Heq'.
      - eapply HTP; first done. eapply spredNE, HP.
        eapply met_morph_nonexp, Hdist1.
      - eapply HTQ; first done. eapply spredNE, HQ.
        eapply met_morph_nonexp, Hdist2.
    Qed.

    Lemma timeless_box P:
      timeless P ⊑ timeless(□P).
    Proof.
      intros w n HTP. repeat intro.
      simpl. eapply HTP; done.
    Qed.

    Lemma timeless_impl P Q:
      timeless Q ⊑ timeless (P → Q).
    Proof.
      move=>w n HTQ /= w' k Ltk HPQ w'' [|[|m]] Lem HP; first exact: bpred.
      { apply HPQ, HP. omega. }
      eapply HTQ, HPQ; [omega|omega|].
      eapply dpred, HP. omega.
    Qed.
    
    Lemma timeless_si P Q:
      timeless Q ⊑ timeless (P -* Q).
    Proof.
      move=>w n HTQ /= w' k Ltk HPQ w'' [|[|m]] Lem HP; first exact: bpred.
      { apply HPQ, HP. omega. }
      eapply HTQ, HPQ; [omega|omega|].
      eapply dpred, HP. omega.
    Qed.

    Section TimelessQuant.
      Context {T} `{cT : cmetric T}.
      Context (φ : T -n> Props).

      Lemma all_timeless :
        all (n[(timeless)] <M< φ) ⊑ timeless (all φ).
      Proof.
        move => w n HAT. simpl in *. repeat intro. simpl.
        eapply HAT; first done. apply Hp.
      Qed.

      Lemma xist_timeless :
        all (n[(timeless)] <M< φ) ⊑ timeless (xist φ).
      Proof.
        move => w n HAT. simpl in *. repeat intro. simpl.
        destruct Hp as [t Hφ]. exists t. eapply HAT; first done.
        exact Hφ.
      Qed.
    End TimelessQuant.

  End Timeless.

  Section IntEqTimeless.
    Context {T} `{cmT: Setoid T}.
    (* This only works for types with the discrete metric! *)
    Existing Instance discreteMetric.
    Existing Instance discreteCMetric.

    Lemma intEqTimeless (t1 t2: T):
      valid(timeless(intEq t1 t2)).
    Proof.
      intros w n. intros w' k HLt Hsq. simpl.
      tauto.
    Qed.
  End IntEqTimeless.

  Section Ownership.

    Local Obligation Tactic := idtac.

    (** General Ownership - used to show that the other assertions make sense **)
    Program Definition own: Wld -> Props :=
      fun w0 => m[(fun w => ∃ wr, (w0 · wr) === w )].
    Next Obligation.
      intros. move=>wr0 wr1 EQwr. apply intEq_dist; last reflexivity.
      apply cmra_op_dist; first reflexivity. assumption.
    Qed.
    Next Obligation.
      intros w0 n w1 w2 EQw k HLt.
      destruct k; first reflexivity.
      split; move => [wr Hwr];
        exists wr. 
      - eapply spredNE, Hwr. simpl morph. eapply intEq_dist; first reflexivity. (* RJ: another instance of simpl going too far *)
        eapply mono_dist, EQw. assumption.
      - eapply spredNE, Hwr. simpl morph. eapply intEq_dist; first reflexivity.
        symmetry. eapply mono_dist, EQw. assumption.
    Qed.
    Next Obligation.
      intros w w1 w2 [wd Hequ] k. destruct k; first reflexivity.
      case=>wr. move/sp_eq_iff=>Heq. exists (wd · wr).
      apply sp_eq_iff. rewrite -Hequ. rewrite assoc (comm w) -assoc.
      apply cmra_op_dist; first reflexivity. assumption.
    Qed.
    Arguments own _ : simpl never.

    Global Instance own_dist n:
      Proper (dist n ==> dist n) own.
    Proof.
      move=>w0 w1 Heq w m HLt. destruct m; first reflexivity.
      split; case=>wd; move/sp_eq_iff=>Heqd; exists wd; apply sp_eq_iff; rewrite -Heqd;
        (apply cmra_op_dist; last reflexivity); eapply mono_dist; first eassumption; eassumption || symmetry; eassumption.
    Qed.

    Global Instance own_equiv : Proper (equiv ==> equiv) own.
    Proof.
      eapply dist_equiv; now apply _.
    Qed.

    Lemma own_sc (u v : Wld):
      own (u · v) == own u * own v.
    Proof.
      move => w n; destruct n; first (split; intro; exact:bpred). split; simpl.
      - move => [wr Hwr].
        exists (u, v · wr); split; last split.
        + split; now rewrite -Hwr -assoc.
        + exists (1u). now rewrite ra_op_unit2.
        + exists wr; reflexivity.
      - move : w => [wu wr] [[w1 w2] [Hw] [[w1r Hw1r] [w2r Hw2r]]].
        exists (w1r · w2r). rewrite -assoc (assoc v) (comm v) -assoc. rewrite -Hw. split.
        (* RJ: Simplification here is not nice... *)
        + rewrite [ra_op]lock /= -lock. simpl in Hw1r, Hw2r. rewrite -Hw1r -Hw2r.
          rewrite !assoc. reflexivity.
        + rewrite [ra_op]lock /=. simpl in Hw1r, Hw2r. rewrite -Hw1r -Hw2r.
          rewrite !assoc. split; reflexivity.
    Qed.
   
    Program Definition inv i : Props -n> Props := 
      n[(fun P => m[(fun w => ∃Pr, Invs w i === Some (Pr · (ra_ag_inj (ı' (halved P)))) )] )].
    Next Obligation.
      intros. move=>Pr1 Pr2 EQPr. apply intEq_dist; first reflexivity.
      apply option_dist_Some. apply ra_ag_op_dist; last reflexivity. assumption.
    Qed.
    Next Obligation.
      move=>i P n w1 w2 EQw. apply xist_dist=>Pr. simpl morph. apply intEq_dist; last reflexivity.
      now rewrite EQw.
    Qed.
    Next Obligation.
      move => i P w1 w2 [wd Hw] n. simpl morph. destruct n; first reflexivity.
      move=>[Pr HPr]. simpl morph in HPr. destruct w1 as [I1 R1], w2 as [I2 R2], wd as [Id Rd].
      destruct Hw as [EQI _]. simpl in *. clear R1 R2 Rd. specialize (EQI i).
      simpl in EQI. destruct (Id i) as [Pd|].
      - exists (Pd · Pr). change (I2 i = S n = (Some (Pd · Pr · ra_ag_inj (ı' (halved P))))).
        etransitivity; first (eapply dist_refl; symmetry; exact:EQI).
        destruct (I1 i) as [P1|]; last contradiction HPr.
        unfold finprod_op. do 3 red. rewrite -assoc. apply cmra_op_dist; first reflexivity.
        exact HPr.
      - exists Pr. change (I2 i = S n = (Some (Pr · ra_ag_inj (ı' (halved P))))).
        etransitivity; last eexact HPr. symmetry. apply dist_refl.
        destruct (I1 i) as [P1|]; last contradiction HPr.
        exact EQI.
    Qed.
    Next Obligation.
      move => i n P1 P2 EQP. destruct n; first exact: dist_bound.
      intros w. apply xist_dist=>Pr. simpl morph. apply intEq_dist; first reflexivity.
      do 3 red. apply cmra_op_dist; first reflexivity.
      apply ra_ag_inj_dist. apply met_morph_nonexp.
      simpl. apply dist_mono. assumption.
    Qed.

    Lemma inv_contractive i : contractive (inv i).
    Proof.
      move => n P1 P2 EQP w [|k /le_S_n Hk] //; split; move => [p /= EQwi]; simpl;
      exists p; rewrite EQwi {EQwi} /dist /option_metric /option_dist;
      rewrite (_ : ra_ag_inj _ = S k = ra_ag_inj _); [reflexivity| |reflexivity|]; 
      split; try reflexivity; move => [|m] Hm _; apply met_morph_nonexp => //;
      eapply (mono_dist _ _ _ (S _)); [|exact: EQP| |symmetry; exact EQP]; omega.
    Qed.

    Lemma inv_box i P:
      inv i P == □inv i P.
    Proof.
      apply pord_antisym; last by apply:box_elim.
      intros [u r] n. destruct n; first (intro; exact:bpred).
      case=>Pr. move/sp_eq_iff=>Heq. exists Pr. apply sp_eq_iff.
      rewrite -Heq. unfold ra_unit, Wld_unit, ra_unit_prod, Invs, fst. now rewrite finmap_invs_unit.
    Qed.

    Program Definition inv_own i P: Props :=
      ∃ r, own (fdStrongUpdate i (Some (ra_ag_inj (ı' (halved P)))) fdEmpty, r).
    Next Obligation.
      intros. move=>r1 r2 EQr. apply (own_dist). split; first reflexivity.
      exact EQr.
    Qed.

    Lemma inv_iff i P:
      inv i P == inv_own i P.
    Proof.
      move=>w n. destruct n; first reflexivity. split.
      - case=>Pr /= Heq. exists (1 (snd w)). exists w.
        destruct w as [I R]. unfold ra_op, ra_op_prod. split; last first.
        { rewrite /= ra_op_unit. reflexivity. }
        simpl. move=>j. rewrite /ra_op /ra_op_finprod fdComposeRed.
        destruct (dec_eq i j).
        + subst j. rewrite fdStrongUpdate_eq. simpl in Heq.
          destruct (I i) as [Ii|]; last contradiction Heq.
          simpl in *.
          rewrite Heq=>{Heq}. apply dist_refl. rewrite assoc (comm _ Pr) -assoc.
          rewrite ra_ag_dupl. reflexivity.
        + erewrite fdStrongUpdate_neq by assumption. destruct (I j); reflexivity.
      - case=>r. case=>wf /= Heq. destruct w as [I R], wf as [If Rf].
        destruct Heq as [HeqI _]. simpl in HeqI. specialize (HeqI i).
        rewrite /ra_op /ra_op_finprod fdComposeRed fdStrongUpdate_eq in HeqI.
        destruct (If i) as [Ifi|].
        + exists Ifi. unfold Invs, fst. rewrite -HeqI /finprod_op.
          rewrite comm. reflexivity.
        + exists (1 (ra_ag_inj (ı' (halved P)))). unfold Invs, fst.
          rewrite -HeqI /finprod_op. rewrite ra_op_unit. reflexivity.
    Qed.
    
    (** Proper physical state: ownership of the machine state **)
    Program Definition ownS : state -n> Props :=
      n[(fun σ => m[(fun w => sp_const (ex_own σ ⊑ State w) )] )].
    Next Obligation.
      intros σ n w1 w2 EQw; destruct n as [| n]; [exact:dist_bound |].
      move=>m HLt. destruct m; first reflexivity. simpl.
      destruct w1 as [I1 [σ1 g1]], w2 as [I2 [σ2 g2]], EQw as [_ [EQσ _]]. simpl in EQσ.
      unfold State. simpl. rewrite EQσ. reflexivity.
    Qed.
    Next Obligation.
      move=>σ [I1 [σ1 g1]] [I2 [σ2 g2]] [[I3 [σ3 g3]] /= [_ [EQσ _]]] n.
      simpl. destruct n; first reflexivity. simpl=>Hle. rewrite <-EQσ, Hle.
      exists σ3. reflexivity.
    Qed.
    Next Obligation.
      move=>n σ1 σ2 EQσ w. simpl morph. destruct n; first exact:dist_bound.
      hnf in EQσ. subst. reflexivity.
    Qed.
    
    Lemma ownS_timeless {σ} : valid(timeless(ownS σ)).
    Proof.
      unfold ownS. move=>w n w' k Hwle Hle. simpl. tauto.
    Qed.

    Program Definition own_state σ: Props :=
      ∃ I, ∃ g, own (I, (ex_own σ, g)).
    Next Obligation.
      intros. move=>g1 g2 EQg. cbv beta. apply own_dist.
      split; first reflexivity. split; first reflexivity.
      simpl. assumption.
    Qed.
    Next Obligation.
      intros. move=>I1 I2 EQI. cbv beta. apply xist_dist=>r.
      apply own_dist.
      split; last reflexivity. simpl. assumption.
    Qed.

    Lemma ownS_iff σ:
      ownS σ == own_state σ.
    Proof.
      move=>w n. destruct n; first reflexivity. split; simpl.
      - move=>[Sr Heq]. destruct w as [I [S g]]. exists (1 I) (1 g) (I, (Sr, g)).
        simpl. split; last split.
        + apply dist_refl. rewrite ra_op_unit. reflexivity.
        + rewrite comm. exact Heq.
        + apply dist_refl. rewrite ra_op_unit. reflexivity.
      - move=>[Id [rd [w' Heq]]]. destruct w as [I [S g]], w' as [I' [S' g']].
        simpl in *. exists S'. destruct Heq as [_ [Heq _]]. rewrite comm. exact Heq.
    Qed.

    (** Proper ghost state: ownership of logical **)
    Program Definition ownL : RL.res -n> Props :=
      n[(fun g => m[(fun w => sp_const (g ⊑ Res w) )] )].
    Next Obligation.
      intros r n w1 w2 EQw; destruct n as [| n]; [exact:dist_bound |].
      move=>m HLt. destruct m; first reflexivity. simpl.
      destruct w1 as [I1 [σ1 g1]], w2 as [I2 [σ2 g2]], EQw as [_ [_ EQg]]. simpl in EQg. simpl.
      rewrite EQg. reflexivity.
    Qed.
    Next Obligation.
      move=>r [I1 [σ1 g1]] [I2 [σ2 g2]] [[I3 [σ3 g3]] /= [_ [_ EQg]]] n.
      simpl. destruct n; first reflexivity. simpl=>Hle. rewrite <-EQg, Hle.
      exists g3. reflexivity.
    Qed.
    Next Obligation.
      move=>n g1 g2 EQg w. simpl morph. destruct n; first exact:dist_bound.
      move=>m Hle. simpl. destruct m; first reflexivity. simpl.
      rewrite EQg. reflexivity.
    Qed.
    
    Lemma ownL_timeless {g} : valid(timeless(ownL g)).
    Proof.
      unfold ownL. move=>w n w' k Hwle Hle. simpl. tauto.
    Qed.

    Program Definition own_ghost g: Props :=
      ∃ I, ∃ S, own (I, (S, g)).
    Next Obligation.
      intros. move=>g1 g2 EQr. apply own_dist.
      split; first reflexivity. split; last reflexivity.
      simpl. assumption.
    Qed.
    Next Obligation.
      intros. move=>I1 I2 EQI. cbv beta. apply xist_dist=>S.
      apply own_dist.
      split; last reflexivity. simpl. assumption.
    Qed.

    Lemma ownL_iff g:
      ownL g == own_ghost g.
    Proof.
      move=>w n. destruct n; first reflexivity. split; simpl.
      - move=>[gr Heq]. destruct w as [I [S r]]. exists (1 I) (1 S) (I, (S, gr)).
        simpl. split; last split.
        + apply dist_refl. rewrite ra_op_unit. reflexivity.
        + apply dist_refl. rewrite ra_op_unit. reflexivity.
        + rewrite comm. exact Heq.
      - move=>[Id [rd [w' Heq]]]. destruct w as [I [S g0]], w' as [I' [S' g']].
        simpl in *. exists g'. destruct Heq as [_ [_ Heq]]. rewrite comm. exact Heq.
    Qed.

    Lemma ownL_sc (g1 g2 : RL.res) :
      ownL (g1 · g2) == ownL g1 * ownL g2.
    Proof.
      intros [I [S g]] n. destruct n; first (split; intro; exact:bpred). split; simpl.
      - move => [gd Heq]. exists ((I, (S, gd · g1)), (1 I, (1 S, g2))). simpl. split_conjs.
        + rewrite ra_op_unit2. reflexivity.
        + rewrite ra_op_unit2. reflexivity.
        + rewrite -assoc. apply dist_refl. assumption.
        + exists gd. reflexivity.
        + reflexivity.
      - move=>[[[I1 [S1 g'1]] [I2 [S2 g'2]]] /= [[_ [_ Heq]] [Hg1 Hg2]]].
        rewrite ->Hg1, Hg2. apply pordR. exact Heq.
    Qed.

    Lemma ownL_box (g: RL.res) :
      ownL (1 g) == □ownL (1 g).
    Proof.
      apply pord_antisym; last exact:box_elim.
      move=>w n. destruct n; first (intro; exact:bpred).
      case=>[gr Heq]. simpl. destruct (ra_unit_mono (1 g) gr) as [g' Heq'].
      simpl in Heq. rewrite -Heq. exists g'.
      rewrite (comm gr) Heq' ra_unit_idem comm. reflexivity.
    Qed.

    Lemma ownL_something:
      valid(xist ownL).
    Proof.
      move=>w n. destruct n; first exact:bpred. exists (Res w).
      simpl. reflexivity.
    Qed.

  End Ownership.

End IRIS_CORE.

Module IrisCore (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) : IRIS_CORE RL C R WP.
  Include IRIS_CORE RL C R WP.
End IrisCore.
