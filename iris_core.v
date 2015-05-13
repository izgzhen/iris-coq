Require Import Ssreflect.ssreflect Omega.
Require Import world_prop core_lang.
Require Import ModuRes.RA ModuRes.SPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap ModuRes.RAConstr ModuRes.Agreement.
Require Import ModuRes.CMRA.

Set Bullet Behavior "Strict Subproofs".

(* We hack a bit here to avoid spelling out module types for functor results.
   The hack that involves least work is to duplicate the definition of our final
   resource type as a module type (which is how we can use it, circumventing the
   Coq restrictions) and as a module (to show the type can be instantiated). *)
Module Type IRIS_RES (RL : VIRA_T) (C : CORE_LANG) <: CMRA_T.
  Instance state_type : Setoid C.state := discreteType.
  Instance state_metr : metric (ex C.state) := discreteMetric.
  Instance state_cmetr : cmetric (ex C.state) := discreteCMetric.
  Instance state_cmra_valid : CMRA_valid (ex C.state) := discreteCMRA_valid. 
  Instance state_cmra : CMRA (ex C.state) := discreteCMRA. 

  Instance logR_metr : metric RL.res := discreteMetric.
  Instance logR_cmetr : cmetric RL.res := discreteCMetric.
  Instance logR_cmra_valid : CMRA_valid RL.res := discreteCMRA_valid. 
  Instance logR_cmra : CMRA RL.res := discreteCMRA. 

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
  Instance state_metr : metric C.state := discreteMetric.
  Instance state_cmetr : cmetric C.state := discreteCMetric.
  
  Instance nat_type : Setoid nat := discreteType.
  Instance nat_metr : metric nat := discreteMetric.
  Instance nat_cmetr : cmetric nat := discreteCMetric.

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
  Instance Props_Lattice : Lattice Props | 0 := _.
  Instance Props_CBI : ComplBI Props | 0 := _.
  Instance Props_Eq : EqBI Props | 0 := _.

  Implicit Types (P Q : Props) (w : Wld) (n i k : nat) (r u v : res) (σ : state).

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
    
    Lemma propsNE {P : Props} {w1 w2 n} (EQw : w1 = S n = w2) :
      P w1 n -> P w2 n.
    Proof.
      apply spredNE. by rewrite EQw.
    Qed.
      
  End Views.

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
  End Later.
  Notation " ▹ p " := (later p) (at level 35) : iris_scope.


  Section LaterProps.
    Lemma later_mon P: P ⊑ ▹P.
    Proof.
      move=>w n H. simpl morph.
      destruct n as [|n]; first exact I.
      simpl. eapply dpred; last eassumption. omega.
    Qed.

    Lemma loeb t (HL: later t ⊑ t): valid t.
      intros w n. induction n.
      - eapply HL. exact I.
      - eapply HL. exact IHn.
    Qed.

    Lemma later_true: (⊤:Props) == ▹⊤.
    Proof.
      move=> w n.
      case:n=>[|n].
      - reflexivity.
      - reflexivity.
    Qed.

    Lemma laterM {P Q: Props}:
      (P → Q) ∧ ▹P ⊑ ▹Q.
    Proof.
      move=>w0 n0 [HPQ HLP].
      destruct n0 as [|n0]; first by auto.
      simpl. simpl in HLP. eapply (applyImpl HPQ);[reflexivity|now eauto|assumption].
    Qed.

  End LaterProps.

  Section Necessitation.
    (** Note: this could be moved to BI, since it's possible to define
        more generally. However, we should first figure out a concise
        set of axioms. **)

    Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

    Program Definition box : Props -n> Props :=
      n[(fun P => m[(fun w => mkSPred (fun n => P (1 w) n) _)])].
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
    Next Obligation.
      intros p1 p2 EQp w m HLt.
      by apply EQp.
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

    Lemma box_top : ⊤ == □⊤.
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

    Lemma box_dup P :
      □P == □P * □P.
    Proof.
      apply pord_antisym.
      - intros w n.
        intros HP. exists (w, 1 w). 
        split; last by simpl; rewrite !ra_unit_idem.
        rewrite (ra_op_unit2).
        split; reflexivity.
      - by apply sc_projL.
    Qed.
    
    Lemma box_box P :
      □ □ P == □ P.
    Proof.
      apply pord_antisym.
      - exact: box_elim.
      - apply box_intro. reflexivity.
    Qed.

    Section BoxAll.
      Context {T} `{cT : cmetric T}.
      Context (φ : T -n> Props).

      Program Definition box_all_lhs : Props := ∀t, □φ t.
      Next Obligation.
        move=> t t' HEq w k HLt.
        simpl morph; simpl spred.
        split.
        - apply spredNE. eapply mono_dist; last by rewrite HEq. omega.
        - apply spredNE. eapply mono_dist; last by rewrite HEq. omega.
      Qed.

      Lemma box_all : □all φ == box_all_lhs.
      Proof. done. Qed.
    End BoxAll.
  End NecessitationProps.

  Section IntEqProps.

    (* On Props, valid biimplication, valid internal equality, and external equality coincide. *)


    Remark valid_biimp_intEq {P Q} : valid(P ↔ Q) -> valid(P === Q).
    Proof.
      move=> H nz wz n HLt.
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
      move=> w n H; split;
      move=> w' n' HLt' HP;
      move/(_ (w · w') n' (le_lt_n_Sm _ _ HLt')): H => [Hpq Hqp];
      [exact: Hpq | exact: Hqp].
    Qed.

    (* Note that (P ↔ Q) ⊑ (P === Q) does NOT hold: The first says
       that the equivalence holds in all future worlds, the second says
       it holds in *all* worlds. *)

  End IntEqProps.

  Section Timeless.

    Definition timelessP P w n :=
      forall w' k (HSw : w ⊑ w') (HLt : k < n) (Hp : P w' k), P w' (S k).

    Program Definition timeless P : Props :=
      m[(fun w => mkSPred (fun n => timelessP P w n) _)].
    Next Obligation.
      intros n1 n2 HLe HP w' k HSub HLt. eapply HP; [eassumption |].
      omega.
    Qed.
    Next Obligation.
      intros w1 w2 EQw k; simpl. intros HLt; destruct n as [| n]; [now inversion HLt |].
      split; intros HT w' m HSw HLt' Hp.
      - destruct HSw as [wr HSw].
        have Hwr : wr · w1 = S n = w'. 
        { rewrite -HSw. apply cmra_op_dist; [reflexivity|assumption]. }
        apply: propsNE; [|eapply mono_dist; last eassumption; omega|].
        apply: HT; [exists wr; reflexivity|omega|].
        apply: propsNE; [|symmetry; eapply mono_dist; last eassumption; omega|].
        assumption.
      - destruct HSw as [wr HSw].
        have Hwr : wr · w2 = S n = w'. 
        { rewrite -HSw. apply cmra_op_dist; [reflexivity|symmetry; assumption]. }
        apply: propsNE; [|eapply mono_dist; last eassumption; omega|].
        apply: HT; [exists wr; reflexivity|omega|].
        apply: propsNE; [|symmetry; eapply mono_dist; last eassumption; omega|].
        assumption.
    Qed.
    Next Obligation.
      intros w1 w2 HSw n; simpl; intros HT w' m HSw' HLt Hp.
      eapply HT, Hp; [etransitivity |]; eassumption.
    Qed.

  End Timeless.

  Section IntEqTimeless.
    Context {T} `{cmT: Setoid T}.
    (* This only works for types with the discrete metric! *)
    Existing Instance discreteMetric.
    Existing Instance discreteCMetric.

    Lemma intEqTimeless (t1 t2: T):
      valid(timeless(intEq t1 t2)).
    Proof.
      intros w n. intros w' k HLt Hsq H.
      tauto.
    Qed.
  End IntEqTimeless.

  Section Ownership.

    (* Make sure equiv is not simplified too soon. Unfortunately, settings this globally breaks
       other things. *)
    Local Arguments equiv {_ _} _ _ /.
    
    Local Obligation Tactic := idtac.

    (** Ownership **)
    Program Definition own: Wld -n> Props :=
      n[(fun w0 => m[(fun w => mkSPred (fun n => exists wr, w0 · wr = S n = w) _)] )].
    Next Obligation.
      intros w w' n m HLe [wr Hwr].
      exists wr. eapply mono_dist; last eassumption. omega.
    Qed.
    Next Obligation.
      intros w0 n w1 w2 EQw k HLt; unfold spred; split; move => [wr Hwr];
        exists wr. 
      - etransitivity; first eassumption. eapply mono_dist; last eassumption. omega.
      - etransitivity; first eassumption. eapply mono_dist; last (symmetry; eassumption). omega.
    Qed.
    Next Obligation.
      intros w w1 w2 Hequ. intros k [wr Hwr]. 
      destruct Hequ as [wr' Hequ].
      exists (wr · wr').
      rewrite assoc -Hequ.
      rewrite (comm wr' w1).
      apply: cmra_op_dist; last reflexivity. assumption.
    Qed.
    Next Obligation.
      intros n w1 w2 Hw w k HLt.
      split; move => [wr Hwr]; exists wr; rewrite -Hwr;
      (apply cmra_op_dist; last reflexivity); [symmetry|];
      (eapply mono_dist; last eassumption; omega).
    Qed.
    
    Lemma own_sc (u v : Wld):
      own (u · v) == own u * own v.
    Proof.
      move => w n; split.
      - move => [wr Hwr].
        exists (u, v · wr); split; last split.
        + split; now rewrite -Hwr -assoc.
        + exists (1u). now rewrite ra_op_unit2.
        + now exists wr. 
      - move : w => [wu wr] [[w1 w2] [Hw] [[w1r Hw1r] [w2r Hw2r]]].
        exists (w1r · w2r).
        assert ((Mfst (w1, w2) · Msnd (w1, w2)) = S n = (wu, wr)) by assumption.
        assert ((u · w1r) · (v · w2r) = S n = w1 · w2) by (apply: cmra_op_dist; assumption).
        etransitivity; last eassumption.
        transitivity (u · w1r · (v · w2r)); last (split).
        + rewrite -!(assoc u) (assoc v) (assoc w1r) (comm v w1r).
          reflexivity.
        + by apply: (met_morph_nonexp Mfst). 
        + by apply: (met_morph_nonexp Msnd).
    Qed.
    
    Program Definition inv i : Props -n> Props := 
      n[(fun P =>  ∃ r, own (fdStrongUpdate i (Some (ra_ag_inj (ı' (halved P)))) fdEmpty, r) )].
    Next Obligation.
      move => i P n w1 w2 Hw.
      apply met_morph_nonexp. split; first reflexivity.
      exact Hw.
    Qed.
    Next Obligation.
      move => i n P1 P2 EQP.
      apply xist_dist=>w. apply (met_morph_nonexp own). split; last reflexivity.
      simpl. destruct n; first now auto.
      move=>j. destruct (beq_nat i j) eqn:EQ.
      - apply beq_nat_true in EQ. subst j. erewrite !fdStrongUpdate_eq.
        apply ra_ag_inj_dist. apply met_morph_nonexp. simpl. apply dist_mono. assumption.
      - apply beq_nat_false in EQ. erewrite !fdStrongUpdate_neq; try (exact EQ); [].
        reflexivity.
    Qed.

    Lemma inv_box i P:
      inv i P == □inv i P.
    Proof.
      apply pord_antisym; last by apply:box_elim.
      intros [u r] n. intros [r' [[u'' r''] H]]. exists (1 r').
      destruct (ra_unit_mono r' r'') as [r1 Heq]. exists (u'', r1).
      etransitivity; last first.
      { eapply cmra_unit_dist, H. }
      rewrite /ra_unit /ra_unit_prod /ra_op /ra_op_prod /fst /snd. split; rewrite /fst /snd.
      - apply dist_refl. rewrite finmap_invs_unit. reflexivity.
      - rewrite Heq. reflexivity.
    Qed.

    (* TODO RJ: complete if useful...
    Lemma inv_iff i P w n:
      cmra_valid w (S n) ->
      (inv i P w n <-> Mfst w i = S n = Some (ra_ag_inj (ı' (halved P)))).
    Proof.
      intro Hval. split.
      - move=>[r' [w' Hinv]]. destruct w as [I r]. destruct w' as [I' r''].
        destruct Hval as [Hval _]. destruct Hinv as [Hinv _]. rewrite ra_op_prod_fst /fst in Hinv.
        specialize (Hval i). specialize (Hinv i). simpl morph. move:Hinv.
        rewrite /ra_op /ra_op_finprod fdComposeRed fdStrongUpdate_eq /finprod_op.
        destruct (I' i) as [v'|] eqn:EQI'; last first.
        { move=>Heq. symmetry. assumption. }
        destruct (I i) as [v|] eqn:EQI; last first.
        { move=>[]. }
        move=>Heq. symmetry. eapply ra_ag_inj_prod; first assumption.
        instantiate (1:=v'). exact Heq.
      - move=>EQ. destruct w as [I r]. simpl morph in EQ. exists r. exists (I, r).
        unfold ra_op, ra_op_prod. split; unfold fst, snd; last first.
        { apply dist_refl. apply ra_op_unit. }
        move=>j. destruct (beq_nat i j) eqn:EQi.
        + apply beq_nat_true in EQi. subst j. rewrite EQ=>{EQ}. apply invs_comp. erewrite !fdUpdate_eq.
          reflexivity.
        + apply beq_nat_false in EQi. destruct (I j) as [v|] eqn:Ij.
          * apply dist_refl. apply fdComposeP'. right. right. split; last now rewrite Ij.
            erewrite fdUpdate_neq by assumption. reflexivity.
          * apply dist_refl. apply fdComposePN'. split; last now rewrite Ij.
            erewrite fdUpdate_neq by assumption. reflexivity.
    Qed.*)
    
    Program Definition ownR : res -n> Props :=
      n[(fun r => ∃ u, own (u, r) )].
    Next Obligation.
      move => r n u1 u2 EQu.
      apply met_morph_nonexp. split; last reflexivity.
      exact EQu.
    Qed.
    Next Obligation.
      move => n r1 r2 EQr w k HLt. split; move => [u Hown].
      - have EQw : (u, r1) = n = (u, r2) by now apply prod_proper_n. 
        change ((own (u, r1) w k)) in Hown.
        exists u.
        change ((own (u, r2) w k)).
        eapply (met_morph_nonexp own); last eassumption.
        + symmetry. destruct EQw.
          split; eassumption.
        + omega.
      - have EQw : (u, r1) = n = (u, r2) by now apply prod_proper_n. 
        change ((own (u, r2) w k)) in Hown.
        exists u.
        change ((own (u, r1) w k)).
        eapply (met_morph_nonexp own); last eassumption.
        + destruct EQw.
          split; eassumption. 
        + omega.
    Qed.
    
    Lemma ownR_timeless {r} :
      valid(timeless(ownR r)).
    Proof. 
      move => w n [u' r'] k HSub HLt [u1 [[ur rr] Hwr]].
      exists (u').
      exists ((u', 1 r · rr)). 
      split.
      - unfold ra_op, ra_op_prod.
        rewrite /fst. rewrite -{1}(finmap_invs_unit u').
        now rewrite ra_op_unit.
      - unfold ra_op, ra_op_prod.
        unfold snd.
        rewrite assoc ra_op_unit2.
        by destruct Hwr.
    Qed.

    Lemma ownR_sc r1 r2:
      ownR (r1 · r2) == ownR r1 * ownR r2.
    Proof.
      intros [u r] n; split.
      - move => [u' H].
        change ((own (u', r1 · r2)) (u, r) n) in H.
        have {H} : (own (u', r1) * own (u', r2)) (u, r) n.
        { rewrite -own_sc. rewrite /ra_op /ra_op_prod.
          eapply spredNE, H. f_equiv.
          apply (met_morph_nonexp own). split; last reflexivity.
          symmetry. apply dist_refl.
          rewrite /fst. rewrite -{1}(finmap_invs_unit u').
          now rewrite ra_op_unit. }
        move => [w [Hw [H1 H2]]].
        exists w; split; first assumption.
        split; exists u'; assumption.
      - move => [w [Hw [[u1 H1] [u2 H2]]]].
        have {H1 H2} : own ((u1, r1) · (u2, r2)) (u, r) n. 
        { rewrite own_sc. exists w; split; first assumption.
          split; assumption. }
        move => H. exists (u1 · u2). exact H.
    Qed.

    (** Proper physical state: ownership of the machine state **)
    Program Definition ownS : state -n> Props :=
      n[(fun σ => ∃ l, ownR (ex_own σ, l))].
    Next Obligation.
      intros σ n r1 r2 EQr; destruct n as [| n]; [apply dist_bound |].
      apply met_morph_nonexp. split; first reflexivity.
      rewrite EQr. reflexivity.
    Qed.
    Next Obligation.
      intros n r1 r2 EQr; destruct n as [| n]; [apply dist_bound |].
      rewrite EQr. reflexivity.
    Qed.
    
    Lemma xist_timeless {T:Type} `{cmetric T} (P : T -n> Props) :
      (forall t, valid(timeless(P t))) -> valid (timeless (xist P)).
    Proof.
      intros.
      move => w n w' k HSub HLt [t /H0 Ht].
      exists t. apply: Ht; [| |eassumption|eassumption].
    Qed.

    Lemma ownS_timeless {σ} : valid(timeless(ownS σ)).
    Proof. apply: (xist_timeless (T := RL.res)). intros. apply ownR_timeless. Qed.

    Lemma ownS_state {σ w n} (Hv : ↓w) :
      (ownS σ) w n -> fst (snd w) == ex_own σ.
    Proof.
      move: Hv; move: w => [w r] [_ Hv] [l [u Hlu]]. 
      change (own (u , (ex_own σ, l)) (w, r) n) in Hlu.
      destruct Hlu as [[ur rr] [Hur Hrr]].
      unfold snd at 2 in Hrr.
      rewrite <- Hrr in Hv.
      simpl in Hv.
      destruct rr as [[] lr], Hv as [Hv _] => //.
      by rewrite -Hrr /=.
    Qed.

    (** Proper ghost state: ownership of logical **)
    Program Definition ownL : RL.res -n> Props :=
      n[(fun r : RL.res => ∃ σ, ownR (σ, r))].
    Next Obligation.
      intros r n σ1 σ2 EQr. destruct n as [| n]; [apply dist_bound |eapply dist_refl].
      intros w m. eapply (met_morph_nonexp ownR (n := S m)); last omega. 
      split; [rewrite EQr|]; reflexivity.
    Qed.
    Next Obligation.
      intros n r1 r2 EQr; destruct n as [| n]; [apply dist_bound |].
      move => w m HLt.
      split; move => [σ [u [[ur [pr lr]] [Hwr1 Hwr2]]]].
      - exists σ u (ur, (pr, lr)). hnf. 
        rewrite -Hwr1 -Hwr2.
        split; rewrite /ra_op /ra_op_prod /fst /snd; [reflexivity|]. 
        split; [reflexivity|]. rewrite /ra_op /res_op /=.
        now rewrite EQr.
      - exists σ u (ur, (pr, lr)). hnf. 
        rewrite -Hwr1 -Hwr2.
        split; rewrite /ra_op /ra_op_prod /fst /snd; [reflexivity|]. 
        split; [reflexivity|]. rewrite /ra_op /res_op /=.
        now rewrite EQr.
    Qed.
    
    Lemma ownL_timeless {r : RL.res} : valid(timeless(ownL r)).
    Proof. apply: (xist_timeless (T := (ex state))). intros. apply ownR_timeless. Qed.

    (** Ghost state ownership **)
    Lemma ownL_sc (g1 g2 : RL.res) :
      ownL (g1 · g2) == ownL g1 * ownL g2.
    Proof.
      intros [u r] n; split.
      - move => [s H]. 
        have {H} : (ownR (s, g1) * ownR (ex_unit, g2)) (u,r) n by (rewrite -ownR_sc; destruct s). 
        move => [w [Hw [H1 H2]]].
        exists w; split; first assumption; last split; by [exists s|exists (1s) ].
      - move => [w [Hw [[s1 H1] [s2 H2]]]].
        have {H1 H2} : ownR ((s1, g1) · (s2, g2)) (u, r) n. 
        { rewrite ownR_sc. exists w; split; first assumption.
          split; assumption. }
        move => H. by exists (s1 · s2). 
    Qed.

  End Ownership.

End IRIS_CORE.

Module IrisCore (RL : VIRA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) : IRIS_CORE RL C R WP.
  Include IRIS_CORE RL C R WP.
End IrisCore.
