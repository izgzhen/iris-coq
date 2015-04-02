Require Import Ssreflect.ssreflect.
Require Import RA MetricCore PreoMet BI SPred.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope ra_scope.

(* CMRA ("camera"): RAs with a complete metric. *)
Section CMRA.
  Context {T: Type} {eqT: Setoid T} `{raT: RA (eqT:=eqT) T}.

  Class CMRA_valid:= cmra_valid : T -> SPred.


  Class CMRA `{pcmT: pcmType (eqT:=eqT) (pTA:=pord_ra) T} {TCV: CMRA_valid}: Prop := (* force this to become an actual argument *)
    { cmra_op_dist n :> Proper (dist n ==> dist n ==> dist n) ra_op ;
      cmra_valid_dist n :> Proper (dist n ==> dist n) cmra_valid ;
      cmra_ra_valid t: (sp_full (cmra_valid t)) <-> ra_valid t
    }.
End CMRA.
Arguments CMRA_valid : clear implicits.
Arguments CMRA T {_ _ _ _ _ _ _ _ _}: clear implicits.

Section CMRAProps.
  Context {T: Type} `{cmraT: CMRA T}.

  Program Definition ra_op_n : T -n> T -n> T :=
    n[(fun t1:T => n[(fun t2:T => t1 · t2)])].
  Next Obligation.
    move=>t2 t2' EQt2. simpl. rewrite EQt2. reflexivity.
  Qed.
  Next Obligation.
    move=>t1 t1' EQt1 t2. simpl. rewrite EQt1. reflexivity.
  Qed.

  Global Instance cmra_valid_equiv:
    Proper (equiv ==> equiv) cmra_valid.
  Proof.
    move=>t1 t2 EQt. apply dist_refl=>n.
    eapply cmra_valid_dist. by apply dist_refl.
  Qed.
  
End CMRAProps.

Section DiscreteCMRA.
  Context {T: Type} `{raT: RA T}.
  Existing Instance discreteMetric.
  Existing Instance discreteCMetric.

  Local Instance discreteCMRA_valid : CMRA_valid T := (* can't make this global, it does not depend on the discrete metric... *)
    fun t => sp_c (↓t).

  Global Instance discreteCMRA : CMRA T.
  Proof.
    split.
    - move=>n a1 a2 EQa b1 b2 EQb.
      destruct n as [|n]; first by exact I.
      simpl in *. rewrite EQa EQb. reflexivity.
    - move=>n t1 t2 EQt. destruct n as [|n]; first exact: dist_bound.
      simpl in EQt. move=>m Hle. simpl. rewrite ->EQt. reflexivity.
    - move=>t. split.
      + move=>H. specialize (H 1%nat). exact H.
      + move=>H n. simpl. exact H.
  Qed.
End DiscreteCMRA.

(* Pairs work as CMRA *)
Section PairsCMRA.
  Context {S T: Type} `{cmraS: CMRA S} `{cmraT: CMRA T}.

  Global Instance ra_prod_pcm: pcmType (pTA:=pord_ra) (S * T).
  Proof.
    split. intros σ ρ σc ρc HC.
    apply ra_pord_iff_prod_pord.
    eapply pcm_respC; first by apply _.
    move=>i. apply ra_pord_iff_prod_pord. by apply: HC.
  Qed.

  Global Instance ra_prod_cmra_valid : CMRA_valid (S * T) :=
    fun st => let (s, t) := st in and (cmra_valid s) (cmra_valid t).

  Global Instance ra_prod_cmra: CMRA (S * T).
  Proof.
    split.
    - move=>n [s11 t11] [s12 t12] /= [EQs1 EQt1] [s21 t21] [s22 t22] /= [EQs2 EQt2].
      split.
      + rewrite EQs1 EQs2. reflexivity.
      + rewrite EQt1 EQt2. reflexivity.
    - move=>n [t1 s1] [t2 s2] /= [EQt EQs]. eapply and_sp_dist; eapply cmra_valid_dist; assumption.
    - move=>[t s]. split=>H.
      + split; eapply cmra_ra_valid; intro n; eapply H.
      + move=>n. split; eapply cmra_ra_valid; eapply H.
  Qed.
End PairsCMRA.

Section PairsMap.
  Context {S T U V: Type} `{cmraS: CMRA S} `{cmraT: CMRA T} `{cmraU: CMRA U} `{cmraV: CMRA V}.

  Local Instance ra_force_pord_TS: preoType (T * S) := pord_ra.
  Local Instance ra_force_pord_UV: preoType (U * V) := pord_ra.
  
  Program Definition RAprod_map (f: T -m> U) (g: S -m> V): (T * S) -m> (U * V) :=
    mkMUMorph (pcmprod_map f g) _.
  Next Obligation. (* If one day, this obligation disappears, then probably the instances are not working out anymore *)
    move=>x y EQxy. change (pcmprod_map f g x ⊑ pcmprod_map f g y).
    apply ra_pord_iff_prod_pord. apply ra_pord_iff_prod_pord in EQxy.
    by eapply mu_mono.
  Qed.

  Global Instance RAprod_map_resp: Proper (equiv ==> equiv ==> equiv) RAprod_map.
  Proof.
    move=>f1 f2 EQf g1 g2 EQg. change (pcmprod_map f1 g1 == pcmprod_map f2 g2).
    rewrite EQf EQg. reflexivity.
  Qed.
  Global Instance RAprod_map_nonexp n : Proper (dist n ==> dist n ==> dist n) RAprod_map.
  Proof.
    move=>f1 f2 EQf g1 g2 EQg. change (pcmprod_map f1 g1 = n = pcmprod_map f2 g2).
    rewrite EQf EQg. reflexivity.
  Qed.
  Global Instance RAprod_map_monic : Proper (pord ++> pord ++> pord) RAprod_map.
  Proof.
    move=>f1 f2 EQf g1 g2 EQg x. apply ra_pord_iff_prod_pord. 
    revert x. change (pcmprod_map f1 g1 ⊑ pcmprod_map f2 g2).
    by eapply pcmprod_map_monic.
  Qed.
End PairsMap.
Section PairsMapComp.
  Context {S T: Type} `{cmraS: CMRA S} `{cmraT: CMRA T}.

  Lemma RAprod_map_id:
    RAprod_map (pid T) (pid S) == pid (T*S).
  Proof. (* doing the proof again here is actually easier than using the ones from PreoMet... *)
    intros x. simpl. split; reflexivity.
  Qed.

  Context {U V W X: Type} `{cmraU: CMRA U} `{cmraV: CMRA V} `{cmraW: CMRA W} `{cmraX: CMRA X}.

  Lemma RAprod_map_comp (f: T -m> U) (g: U -m> V) (h: S -m> W) (i: W -m> X):
    RAprod_map g i ∘ RAprod_map f h == RAprod_map (g ∘ f) (i ∘ h).
  Proof.
    intros x. simpl. split; reflexivity.
  Qed.
End PairsMapComp.
Lemma RAprod_map_comp_fst {S T U V W: Type}
      `{cmraS: CMRA S} `{cmraT: CMRA T} `{cmraU: CMRA U} `{cmraV: CMRA V} `{cmraW: CMRA W}
      (f: T -m> U) (g: U -m> V) (h: S -m> W):
  RAprod_map g h ∘ RAprod_map f (pid _) == RAprod_map (g ∘ f) h.
Proof.
  intros x. simpl. split; reflexivity.
Qed.


(* Show that any BI can close over "future Us", for U being a CMRA. *)
Section MComplBI.
  Context {B} `{ComplBI B}.
  Context {T} `{CMRA T}.
  Local Obligation Tactic := intros; try resp_set.

  Program Definition mclose : (T -n> B) -n> T -m> B :=
    n[(fun f: T -n> B => m[(fun t => (all (U:=T) (f <M< n[(ra_op t)])))])].
  Next Obligation.
    move=>t1 t2 EQt. eapply all_dist. eapply ndist_umcomp; first reflexivity.
    move=>u. now eapply cmra_op_dist.
  Qed.
  Next Obligation.
    intros t1 t2 [t3 EQt]. simpl. eapply all_R=>u.
    simpl. rewrite <-EQt. rewrite-> (comm t3), <-assoc.
    transitivity ((f <M< n[(ra_op t1)]) (t3 · u)%ra); last first.
    - eapply pordR. simpl. reflexivity.
    - eapply all_R. eapply pordR, all_equiv. move=>?. reflexivity.
  Qed.
  Next Obligation.
    intros f1 f2 EQf t. simpl. eapply all_dist. move=>u. simpl. rewrite EQf. reflexivity.
  Qed.

  Lemma mclose_cl f : (mclose f: T -n> B) ⊑ f.
  Proof.
    unfold mclose=>u. simpl.
    transitivity ((f <M< n[(ra_op u)]) 1%ra).
    - eapply all_R. eapply all_pord=>t. reflexivity.
    - simpl. rewrite ra_op_unit2. reflexivity.
  Qed.
  Lemma  mclose_fw (f : T -n> B) u t (HFW : forall u' (HS : u ⊑ u'), t ⊑ f u'):
    t ⊑ mclose f u.
  Proof.
    unfold mclose. simpl. eapply all_R=>u'.
    eapply HFW. exists u'. rewrite comm. reflexivity.
  Qed.

End MComplBI.

(* Monotone functions from a CMRA to a BI form a BI. *)
Section MonotoneExt.
  Context B {eqB: Setoid B} {preoB: preoType B} {BIVB: validBI B} {BIBB: botBI B} {BITB: topBI B} {BB: Bounded B}.
  Context {mB: metric B} {cmB: cmetric B} {pcmB: pcmType B}.
  Context T `{cmraT: CMRA T}.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  
  Local Obligation Tactic := intros; resp_set || mono_resp || eauto with typeclass_instances.

  Global Instance top_mm : topBI (T -m> B) := pcmconst top.
  Global Instance bot_mm : botBI (T -m> B) := pcmconst bot.
  Global Instance valid_mm : validBI (T -m> B) := fun P => forall t, valid (P t).

  Global Instance bounded_mm : Bounded (T -m> B).
  Proof.
    split.
    - intros P Q HPQ HQP t. apply pord_antisym; [apply HPQ | apply HQP].
    - intros P t. apply top_true.
    - intros P t. apply bot_false.
    - intros P. split; intros HV.
      + intros t. simpl morph. unfold const. rewrite <-top_valid. eapply HV.
      + intros t. rewrite ->top_valid. eapply HV.
  Qed.

  Context {BIAB : andBI B} {BIOB: orBI B} {BIIB: implBI B} {BISCB: scBI B} {BISIB: siBI B} {BBI: BI B}.
  Context {BIAllB: allBI B} {BIXistB: xistBI B} {CBBI: ComplBI B}. (* We need this already for upclosing and equality *)
  Context {EQBT: eqBI B} {EQB: EqBI B}.

  Global Program Instance and_mm : andBI (T -m> B) :=
    fun P Q => m[(lift_bin and P Q)].
  Global Program Instance or_mm  : orBI  (T -m> B) :=
    fun P Q => m[(lift_bin or P Q)].

  Global Program Instance impl_mm : implBI (T -m> B) :=
    fun P Q => mclose (lift_bin impl P Q).

  Global Program Instance sc_mm  : scBI (T -m> B) :=
    fun P Q => m[(fun t:T => xist n[(fun ts:T*T => ((Mfst ts · Msnd ts) === t) ∧ (P (Mfst ts) * Q (Msnd ts)))])].
  Next Obligation.
    move=>t1 t2 EQt. rewrite /= -/dist. eapply xist_dist. move=>[ts1 ts2] /=. rewrite -/dist.
    rewrite EQt. reflexivity.
  Qed.
  Next Obligation.
    move=>t1 t2 [tx EQt]. simpl. eapply xist_L. intros [ts1 ts2]. eapply xist_R with (u:=(ts1·tx, ts2)).
    simpl. eapply and_pord; last eapply sc_pord.
    - rewrite !intEq_leibnitz /bi_leibnitz. eapply all_R=>φ/=.
      eapply all_L with (u:= φ <M< ra_op_n tx). simpl. apply pordR.
      eapply impl_equiv; f_equiv.
      + rewrite (comm ts1 tx) (assoc _ ts1). reflexivity.
      + assumption.
    - eapply mu_mono. exists tx. rewrite comm. reflexivity.
    - reflexivity.
  Qed.

  Global Program Instance si_mm : siBI (T -m> B) :=
    fun P Q => m[(fun t1 => all n[(fun t2 => (P t2) -* (Q (t1 · t2)))])].
  Next Obligation.
    move=>u1 u2 EQu. simpl. eapply si_dist.
    - rewrite EQu. reflexivity.
    - rewrite EQu. reflexivity.
  Qed.
  Next Obligation.
    move=>u1 u2 EQu. eapply all_dist. move=>t. simpl. eapply si_dist; first reflexivity.
    rewrite EQu. reflexivity.
  Qed.
  Next Obligation.
    intros t1 t2 [t3 EQt]. simpl. eapply all_R=>u.
    simpl. transitivity (P (t3 · u) -* Q (t3 · t1 · u)); last first.
    - rewrite -sc_si. assert (HP: P u ⊑ P (t3 · u)).
      { eapply mu_mono. exists t3. reflexivity. }
      setoid_rewrite HP. rewrite sc_si. eapply si_pord; first reflexivity. eapply mu_mono, pordR.
      rewrite EQt. reflexivity.
    - eapply (all_L (t3 · u)). simpl. eapply si_pord; first reflexivity. eapply mu_mono, pordR.
      rewrite assoc (comm t1). reflexivity.
  Qed.

  (* All of the above preserve all the props it should. *)
  Global Instance and_mm_equiv : Proper (equiv ==> equiv ==> equiv) and_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply and_equiv; [apply EQP | apply EQQ].
  Qed.
  Global Instance and_mm_dist n : Proper (dist n ==> dist n ==> dist n) and_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply and_dist; [apply EQP | apply EQQ].
  Qed.
  Global Instance and_mm_ord : Proper (pord ==> pord ==> pord) and_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply and_pord; [apply EQP | apply EQQ].
  Qed.

  Global Instance or_mm_equiv : Proper (equiv ==> equiv ==> equiv) or_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply or_equiv; [apply EQP | apply EQQ].
  Qed.
  Global Instance or_mm_dist n : Proper (dist n ==> dist n ==> dist n) or_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply or_dist; [apply EQP | apply EQQ].
  Qed.
  Global Instance or_mm_ord : Proper (pord ==> pord ==> pord) or_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply or_pord; [apply EQP | apply EQQ].
  Qed.

  Global Instance impl_mm_dist n : Proper (dist n ==> dist n ==> dist n) impl_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ; apply met_morph_nonexp; intros t; simpl morph.
    apply impl_dist; [apply EQP | apply EQQ].
  Qed.

  Global Instance sc_mm_equiv : Proper (equiv ==> equiv ==> equiv) sc_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply xist_equiv; move=>[t1 t2]. simpl. apply and_equiv; first reflexivity.
    apply sc_equiv; [apply EQP | apply EQQ].
  Qed.
  Global Instance sc_mm_dist n : Proper (dist n ==> dist n ==> dist n) sc_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply xist_dist; move=>[t1 t2]. simpl morph. apply and_dist; first reflexivity.
    apply sc_dist; [apply EQP | apply EQQ].
  Qed.
  Global Instance sc_mm_ord : Proper (pord ++> pord ++> pord) sc_mm.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ t; simpl morph.
    apply xist_pord. intros [t1 t2]. simpl morph. eapply and_pord; first reflexivity.
    apply sc_pord; [apply EQP | apply EQQ].
  Qed.

  Global Instance sc_mm_comm : Commutative sc_mm.
  Proof.
    intros f1 f2 t; simpl morph. apply pord_antisym.
    - apply xist_L; move=>[u1 u2]. simpl morph. apply (xist_R (u2, u1)). simpl morph. apply and_pord.
      + apply pordR. apply intEq_equiv; last reflexivity. rewrite comm. reflexivity.
      + rewrite comm. reflexivity.
    - apply xist_L; move=>[u1 u2]. simpl morph. apply (xist_R (u2, u1)). simpl morph. apply and_pord.
      + apply pordR. apply intEq_equiv; last reflexivity. rewrite comm. reflexivity.
      + rewrite comm. reflexivity.
  Qed.

  Program Definition sc_mm_assoc_f1 u1 u2 t (f1 f2 f3: T -n> B) :=
    lift_bin and (umconst ((u1 · u2) === t)) (lift_bin sc (umconst (f1 u1)) n[(fun ts => ((fst ts · snd ts) === u2) ∧ (f2 (fst ts) * f3 (snd ts)))]).

  Program Definition sc_mm_assoc_f2 u1 u2 t (f1 f2 f3: T -n> B) :=
    lift_bin and (umconst ((u1 · u2) === t)) (lift_bin sc n[(fun ts => ((fst ts · snd ts) === u1) ∧ (f1 (fst ts) * f2 (snd ts)))] (umconst (f3 u2))).

  Existing Instance sc_equiv.

  Global Instance sc_mm_assoc : Associative sc_mm.
  Proof.
    intros f1 f2 f3 t; simpl morph. apply pord_antisym.
    - apply xist_L; move=>[u1 u2]. simpl morph.
      transitivity (xist (sc_mm_assoc_f1 u1 u2 t f1 f2 f3)); unfold sc_mm_assoc_f1.
      + etransitivity; last eapply xist_and_r. apply and_pord; first reflexivity.
        etransitivity; last eapply xist_sc_r. apply sc_pord; first reflexivity.
        reflexivity.
      + apply xist_L; move=>[u3 u4]. simpl morph. unfold const.
        apply (xist_R (u1 · u3, u4)). simpl morph. apply and_R; split.
        * transitivity ((u1 · u2) === t ∧ (u3 · u4) === u2).
          { apply and_pord; first reflexivity. setoid_rewrite and_projL.
            apply sc_projR. }
          eapply intEq_rewrite_goal with (φ := intEq_l (u1 · u3 · u4)).
          { rewrite ->and_projL. reflexivity. }
          setoid_rewrite and_projR. eapply intEq_rewrite_goal with (t2:=u2) (φ := intEq_l (u1 · u3 · u4) <M< ra_op_n u1).
          { reflexivity. }
          simpl morph. eapply intEqR. now rewrite assoc.
        * transitivity ((f1 u1 * f2 u3) * f3 u4).
          { rewrite ->and_projR, and_projR. rewrite assoc. reflexivity. }
          apply sc_pord; last reflexivity.
          apply (xist_R (u1, u3)). simpl morph.
          apply and_R; split; last reflexivity.
          setoid_rewrite <-intEq_refl. apply top_true.
    - apply xist_L; move=>[u1 u2]. simpl morph.
      transitivity (xist (sc_mm_assoc_f2 u1 u2 t f1 f2 f3)); unfold sc_mm_assoc_f2.
      + etransitivity; last eapply xist_and_r. apply and_pord; first reflexivity.
        eapply xist_sc.
      + apply xist_L; move=>[u3 u4]. simpl morph. unfold const.
        apply (xist_R (u3, u4·u2)). simpl morph. apply and_R; split.
        * transitivity ((u1 · u2) === t ∧ (u3 · u4) === u1).
          { apply and_pord; first reflexivity. rewrite ->and_projL, sc_projL. reflexivity. }
          eapply intEq_rewrite_goal with (φ := intEq_l (u3 · (u4 · u2))).
          { rewrite ->and_projL. reflexivity. }
          rewrite ->and_projR. simpl morph. eapply intEq_rewrite_goal with (t2:=u1) (φ := intEq_l (u3 · (u4 · u2)) <M< Mswap ra_op_n u2).
          { reflexivity. }
          simpl morph. eapply intEqR. now rewrite assoc.
        * transitivity (f1 u3 * (f2 u4 * f3 u2)).
          { rewrite ->and_projR, and_projR. rewrite assoc. reflexivity. }
          apply sc_pord; first reflexivity.
          apply (xist_R (u4, u2)). simpl morph. apply and_R; split; last reflexivity.
          setoid_rewrite <-intEq_refl. apply top_true.
  Qed.

  Global Instance si_mm_dist n : Proper (dist n ==> dist n ==> dist n) si_mm.
  Proof.    
    intros P1 P2 EQP Q1 Q2 EQQ t. simpl morph.
    apply all_dist; move=>u. simpl morph.
    apply si_dist; [apply EQP | apply EQQ].
  Qed.

  Global Program Instance bi_mm : BI (T -m> B).
  Next Obligation.
    intros t; simpl morph; apply and_self.
  Qed.
  Next Obligation.
    intros t; simpl morph; apply and_projL.
  Qed.
  Next Obligation.
    intros t; simpl morph; apply and_projR.
  Qed.
  Next Obligation.
    split; intros HH t; simpl morph.
    - apply mclose_fw; intros t' Subt; specialize (HH t'); simpl morph in *.
      rewrite ->Subt, <- and_impl; assumption.
    - rewrite ->and_impl, (HH t); apply mclose_cl.
  Qed.
  Next Obligation.
    intros t; simpl morph; apply or_injL.
  Qed.
  Next Obligation.
    intros t; simpl morph; apply or_injR.
  Qed.
  Next Obligation.
    intros t; simpl morph; apply or_self.
  Qed.
  Next Obligation.
    intros t; simpl morph. apply pord_antisym.
    - apply xist_L;move=>[ts1 ts2]. simpl morph.
      eapply intEq_rewrite_goal with (φ := P).
      { rewrite ->and_projL. reflexivity. }
      rewrite ->and_projR, ->sc_projR. apply mu_mono. exists ts1. reflexivity.
    - apply (xist_R (1, t)). simpl morph. apply and_R; split.
      + eapply intEqR. now rewrite ra_op_unit.
      + unfold const. rewrite sc_top_unit. reflexivity.
  Qed.
  Next Obligation.
    split; move=>HLE t.
    - simpl. apply all_R=>u. simpl morph.
      eapply sc_si. rewrite <-(HLE _). simpl morph. apply (xist_R (t, u)). simpl morph.
      apply and_R; split; last reflexivity.
      eapply intEqR. reflexivity.
    - simpl. apply xist_L;move=>[u1 u2]. simpl morph.
      eapply intEq_rewrite_goal with (φ := R).
      { rewrite ->and_projL. reflexivity. }
      rewrite ->and_projR=>{t}. apply sc_si. rewrite ->HLE=>{HLE}. simpl.
      apply (all_L u2). reflexivity.
  Qed.

  Global Program Instance all_mm : allBI (T -m> B) :=
    fun U eqU mU cmU R =>
      m[(fun t => all n[(fun u => R u t)])].
  Next Obligation.
    intros t1 t2 EQt; apply all_dist; intros u; simpl morph.
    rewrite EQt; reflexivity.
  Qed.
  Next Obligation.
    intros t1 t2 Subt; apply all_pord; intros u; simpl morph.
    rewrite ->Subt; reflexivity.
  Qed.

  Global Program Instance xist_mm : xistBI (T -m> B) :=
    fun U eqU mU cmU R =>
      m[(fun t => xist n[(fun u => R u t)])].
  Next Obligation.
    intros t1 t2 EQt; apply xist_dist; intros u; simpl morph.
    rewrite EQt; reflexivity.
  Qed.
  Next Obligation.
    intros t1 t2 Subt; apply xist_pord; intros u; simpl morph.
    rewrite ->Subt; reflexivity.
  Qed.

  Section Quantifiers.
    Context V `{cmV : cmetric V}.

    Global Instance all_mm_dist n : Proper (dist (T := V -n> T -m> B) n ==> dist n) all.
    Proof.
      intros R1 R2 EQR t; simpl morph.
      apply all_dist; intros u; simpl morph; apply EQR.
    Qed.

    Global Instance xist_mm_dist n : Proper (dist (T := V -n> T -m> B)n ==> dist n) xist.
    Proof.
      intros R1 R2 EQR t; simpl morph.
      apply xist_dist; intros u; simpl morph; apply EQR.
    Qed.

  End Quantifiers.

  Global Program Instance cbi_mm : ComplBI (T -m> B).
  Next Obligation.
    split.
    - intros HH t; simpl morph; rewrite <- all_R; intros u; simpl morph; apply HH.
    - intros HH u t; specialize (HH t); simpl morph in *; rewrite <- all_R in HH.
      simpl morph in HH; apply HH.
  Qed.
  Next Obligation.
    split.
    - intros HH t; simpl morph; rewrite <- xist_L; intros u; simpl morph; apply HH.
    - intros HH u t; specialize (HH t); simpl morph in *.
      rewrite <- xist_L in HH; simpl morph in HH; apply HH.
  Qed.

End MonotoneExt.

Section MonotoneEQ.
  Context B `{LB: EqBI B}
          T `{cmraT : CMRA T}.
  Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.

  Global Instance eq_mm : eqBI (T -m> B) :=
    fun U {eqU mU cmU u1 u2} => pcmconst (u1 === u2).

  Global Instance eqbi_mm : EqBI (T -m> B).
  Proof.
    split; intros.
    - move=>t1 t2 EQt u1 u2 EQu x. simpl morph. unfold const. apply intEq_equiv; assumption.
    - move=>t1 t2 EQt u1 u2 EQu x. simpl morph. unfold const. apply intEq_dist; assumption.
    - move=>x. simpl morph. unfold const. rewrite intEq_leibnitz /bi_leibnitz. apply pord_antisym.
      + apply all_R=>f. simpl morph. apply all_R=>t. simpl morph.
        pose (φ := fun u => f u (x·t)%ra).
        assert (φ_dist: forall n, Proper (dist n ==> dist n) φ).
        { clear. move=>n u1 u2 EQu. unfold φ. rewrite EQu. reflexivity. } 
        apply (all_L n[(φ)]). simpl morph. unfold φ. reflexivity.
      + apply all_R=>f. simpl morph.
        pose (φ := fun u => (pcmconst (T:=T) (U:=B) (f u))).
        assert (φ_dist: forall n, Proper (dist n ==> dist n) φ).
        { clear. move=>n u1 u2 EQu r. unfold φ, pcmconst. simpl morph. unfold const. rewrite EQu. reflexivity. }
        apply (all_L n[(φ)]). simpl morph. apply (all_L x)%ra. simpl morph. unfold const. apply impl_pord.
        * reflexivity.
        * reflexivity.
    - move=>t. simpl morph. unfold const. apply (xist_R (1%ra, t)). simpl morph.
      apply and_R; split; last now eapply intEq_sc.
      apply intEqR. now rewrite ra_op_unit.
  Qed.

End MonotoneEQ.
