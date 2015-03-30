Require Import Ssreflect.ssreflect Omega.
Require Export PreoMet BI.

Section Definitions.
  Program Definition dclosed (p : nat -> Prop) :=
    forall n m (HLe : m <= n), p n -> p m.

  Record SPred :=
    mkSPred {spred    :> nat -> Prop;
             dpred    :  dclosed spred }.

  Program Definition sp_c (p : Prop) :=
    mkSPred (fun n => p) _.
  Next Obligation. intros m n _ HP. tauto. Qed.

  Definition sp_top: SPred := sp_c True.

  Definition sp_full (p: SPred) := forall n, p n.

  Lemma sp_top_full:
    sp_full sp_top.
  Proof.
    intro. exact I.
  Qed.

  Definition sp_equiv (p q : SPred) := forall n, p n == q n.

  Global Instance sp_equiv_e: Equivalence sp_equiv.
  Proof.
    split.
    - intros p n; reflexivity.
    - intros p q Hpq n; symmetry; apply Hpq.
    - intros p q r Hpq Hqr n; etransitivity; [apply Hpq | apply Hqr].
  Qed.

  Global Program Instance sp_type : Setoid SPred := mkType sp_equiv.

  Global Instance sp_full_resp: Proper (equiv ==> equiv) sp_full.
  Proof.
    move=>s1 s2 EQs.
    split; intros H n; now firstorder.
  Qed.

  Definition sp_dist n (p q : SPred) :=
    forall m, m < n -> (p m <-> q m).

  Global Program Instance sp_metric : metric SPred := mkMetr sp_dist.
  Next Obligation.
    intros p q Hpq r s Hrs; split; intros HD m HLt; [symmetry in Hpq, Hrs |];
    rewrite -> (Hpq m), (Hrs m); apply HD; assumption.
  Qed.
  Next Obligation.
    split; intros HEq.
    - intros n; apply (HEq (S n)); auto with arith.
    - intros _ m _; apply HEq.
  Qed.
  Next Obligation.
    intros p q Hpq m HLt; symmetry; apply Hpq, HLt.    
  Qed.
  Next Obligation.
    intros p q r Hpq Hqr m HLt; etransitivity; [apply Hpq, HLt | apply Hqr, HLt].
  Qed.
  Next Obligation.
    intros m HLt; apply H; auto with arith.    
  Qed.
  Next Obligation.
    intros m HLt; inversion HLt.    
  Qed.

  Program Definition sp_compl (σ : chain SPred) (σc : cchain σ) :=
    mkSPred (fun n => σ (S n) n) _.
  Next Obligation.
    intros n m HLt HSub.
    eapply (chain_cauchy σ σc (S m) (S n)); auto with arith; [].
    eapply dpred; eassumption.
  Qed.

  Global Program Instance sp_cmetric : cmetric SPred := mkCMetr sp_compl.
  Next Obligation.
    intros n; intros i HLe k HLt; simpl.
    eapply (chain_cauchy σ σc (S k)); eauto with arith.
  Qed.

  Definition sp_ord (p q : SPred) := forall n, p n -> q n.

  Global Program Instance sp_preotype : preoType SPred := mkPOType sp_ord _.
  Next Obligation.
    split.
    + intros p n; tauto.
    + intros p q r Hpq Hqr n Hp; apply Hqr, Hpq, Hp.
  Qed.
  Next Obligation.
    move=> p1 p2 Rp q1 q2 Rq HLe n.
    rewrite -(Rp n) -(Rq n).
    exact: HLe.
  Qed.

  Global Instance sp_pcmetric : pcmType SPred.
  Proof.
    split.
    + intros σ ρ σc ρc HSub n Hpc; simpl in *; apply HSub, Hpc.
  Qed.

  Global Instance spred_equiv : Proper (equiv ==> eq ==> iff) spred.
  Proof.
    add_morphism_tactic; intros R1 R2 EQR n; split; intros HH; apply EQR; assumption.
  Qed.

  Global Instance spred_pord : Proper (pord ++> le --> Basics.impl) spred.
  Proof.
    intros R1 R2 SubR n1 n2 Len HR1; eapply SubR, dpred; eassumption.
  Qed.

  Definition laterF (p : nat -> Prop) n :=
    match n with
      | O => True
      | S n => p n
    end.
  Program Definition later_sp (p : SPred) :=
    mkSPred (laterF p) _.
  Next Obligation.
    intros [| m] [| n] HLe; simpl; try tauto; [now inversion HLe |].
    intros HP; eapply dpred; [| eassumption]; auto with arith.
  Qed.

  Global Instance later_sp_equiv : Proper (equiv ==> equiv) later_sp.
  Proof.
    intros P Q EQPQ [| n]; simpl; [reflexivity | apply EQPQ].
  Qed.

  Global Instance later_sp_contractive: contractive later_sp.
  Proof.
    move=>n P Q EQ m Hle. split=>H; (destruct m as [|m]; first exact I); simpl in *; (eapply EQ; [omega|assumption]).
  Qed.

  Global Instance later_sp_dist n : Proper (dist n ==> dist n) later_sp.
  Proof.
    pose (lf := contractive_nonexp later_sp _).
    move=> ? ? ?.
    by apply: (met_morph_nonexp lf).
  Qed.

  Lemma equiv_spred_simpl U (R : relation U) (f : U -> SPred) {RS : Symmetric R}
        (HP : forall u1 u2 n, R u1 u2 -> f u1 n -> f u2 n) :
    Proper (R ==> equiv) f.
  Proof.
    intros u1 u2 HRu; split; intros HF; (eapply HP; [| eassumption]);
    [| symmetry]; assumption.
  Qed.
  Lemma dist_spred_simpl U (R : relation U) (f : U -> SPred) n {RS : Symmetric R}
        (HP : forall u1 u2 m (HLt : m < n), R u1 u2 -> f u1 m -> f u2 m) :
    Proper (R ==> dist n) f.
  Proof.
    intros u1 u2 HRu m; split; intros HF;
    (eapply HP; [eassumption | | eassumption]); [| symmetry]; assumption.
  Qed.

End Definitions.

Arguments dpred {s} {n m} _ _.

Section SPredBI.
  Local Obligation Tactic := intros; eauto with typeclass_instances.

  (* Standard interpretations of propositional connectives. *)
  Global Program Instance top_sp : topBI SPred := sp_top.
  Global Program Instance bot_sp : botBI SPred := sp_c False.
  Global Program Instance valid_sp : validBI SPred := sp_full.

  Global Instance bounded_sp : Bounded SPred.
  Proof.
    split.
    - intros P Q HPQ HQP n. split; [apply HPQ| apply HQP].
    - intros P n _; exact I.
    - intros P n HC; contradiction HC.
    - intros P; split.
      + intros HV n _. apply HV.
      + intros HV n. now apply HV.
  Qed.

  Global Program Instance and_sp : andBI SPred :=
    fun P Q =>
      mkSPred (fun n => P n /\ Q n) _.
  Next Obligation.
    intros n m HLe; rewrite-> HLe; tauto.
  Qed.
  Global Program Instance or_sp : orBI SPred :=
    fun P Q =>
      mkSPred (fun n => P n \/ Q n) _.
  Next Obligation.
    intros n m HLe; rewrite-> HLe; tauto.
  Qed.

  Global Program Instance impl_sp : implBI SPred :=
    fun P Q =>
      mkSPred (fun n => forall m, m <= n -> P m -> Q m) _.
  Next Obligation.
    intros n m HLe HImp k HLe' HP.
    apply HImp; try (etransitivity; eassumption); assumption.
  Qed.
  
  (* BI connectives: Boring. We'd actually want just a Heyting Algebra for SPred, but whatever. *)
  Global Instance sc_sp : scBI SPred := and_sp.
  Global Instance si_sp : siBI SPred := impl_sp.

  (* For some reason tc inference gets confused otherwise *)
  Existing Instance sp_type.

  (* All of the above preserve all the props it should. *)
  Global Instance and_sp_equiv : Proper (equiv ==> equiv ==> equiv) and_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n; simpl.
    rewrite-> EQP, EQQ; tauto.
  Qed.
  Global Instance and_sp_dist n : Proper (dist n ==> dist n ==> dist n) and_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ m HLt; simpl.
    split; intros; (split; [apply EQP | apply EQQ]; now auto with arith).
  Qed.
  Global Instance and_sp_ord : Proper (pord ==> pord ==> pord) and_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n; simpl.
    rewrite-> EQP, EQQ; tauto.
  Qed.

  Global Instance or_sp_equiv : Proper (equiv ==> equiv ==> equiv) or_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n; simpl.
    rewrite ->EQP, EQQ; tauto.
  Qed.
  Global Instance or_sp_dist n : Proper (dist n ==> dist n ==> dist n) or_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ m HLt; simpl.
    split; (intros [HP | HQ]; [left; apply EQP | right; apply EQQ]; now auto with arith).
  Qed.
  Global Instance or_sp_ord : Proper (pord ==> pord ==> pord) or_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n; simpl.
    rewrite ->EQP, EQQ; tauto.
  Qed.

  Global Instance impl_sp_dist n : Proper (dist n ==> dist n ==> dist n) impl_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ m HLt; simpl.
    split; intros; apply EQQ, H, EQP; now eauto with arith.
  Qed.

  Global Instance sc_sp_equiv : Proper (equiv ==> equiv ==> equiv) sc_sp := and_sp_equiv.
  Global Instance sc_sp_dist n : Proper (dist n ==> dist n ==> dist n) sc_sp := and_sp_dist n.
  Global Instance sc_sp_ord : Proper (pord ==> pord ==> pord) sc_sp := and_sp_ord.

  Global Instance si_sp_dist n : Proper (dist n ==> dist n ==> dist n) si_sp := impl_sp_dist n.

  Global Program Instance bi_sp : BI SPred.
  Next Obligation.
    intros n; simpl; tauto.
  Qed.
  Next Obligation.
    intros n [HP HQ]; assumption.
  Qed.
  Next Obligation.
    intros n [HP HQ]; assumption.
  Qed.
  Next Obligation.
    split; intros HH n.
    - intros HP m HLe HQ; apply HH; split; [rewrite-> HLe |]; assumption.
    - intros [HP HQ]; eapply HH; eassumption || reflexivity.
  Qed.
  Next Obligation.
    intros n HP; left; assumption.
  Qed.
  Next Obligation.
    intros n HQ; right; assumption.
  Qed.
  Next Obligation.
    intros n; simpl; tauto.
  Qed.
  Next Obligation.
    intros P Q n; simpl. tauto.
  Qed.
  Next Obligation.
    intros P Q R n; split; simpl; tauto.
  Qed.
  Next Obligation.
    intros n; split; simpl; tauto.
  Qed.
  Next Obligation.
    split; intros HH n; simpl in *.
    - intros HP m HLe HQ. apply HH. split; last assumption. rewrite-> HLe. assumption.
    - intros [HP HQ]. eapply HH; try eassumption; omega.
  Qed.

  (* Quantifiers. *)
  Global Program Instance all_sp : allBI SPred :=
    fun T eqT mT cmT R =>
      mkSPred (fun n => forall t, R t n) _.
  Next Obligation.
    intros n m HLe HR t. rewrite-> HLe; apply HR.
  Qed.

  Global Program Instance xist_sp : xistBI SPred :=
    fun T eqT mT cmT R =>
      mkSPred (fun n => exists t, R t n) _.
  Next Obligation.
    intros n m HLe [t HR]; exists t; rewrite-> HLe; apply HR.
  Qed.

  Section Quantifiers.
    Context V `{cmV : cmetric V}.

    Existing Instance nonexp_type.

    Global Instance all_sp_dist n : Proper (dist (T := V -n> SPred) n ==> dist n) all.
    Proof.
      intros R1 R2 EQR m HLt; simpl.
      split; intros; apply EQR; now auto.
    Qed.

    Global Instance xist_sp_dist n : Proper (dist (T := V -n> SPred)n ==> dist n) xist.
    Proof.
      intros R1 R2 EQR m HLt; simpl.
      split; intros [t HR]; exists t; apply EQR; now auto.
    Qed.

  End Quantifiers.

  Global Program Instance cbi_sp : ComplBI SPred.
  Next Obligation.
    split.
    - intros HH v n HP. apply HH; assumption.
    - intros HH v n HP. apply HH. assumption.
  Qed.
  Next Obligation.
    split.
    - intros HH n [u HP]; eapply HH; eassumption.
    - intros HH u n HP; apply HH; exists u; assumption.
  Qed.

End SPredBI.

Section SPredEq.
  Global Program Instance sp_eq : eqBI SPred :=
    fun U {eqU mU cmU u1 u2} => mkSPred (fun n => u1 = S n = u2) _.
  Next Obligation.
    move=>n m Hle. simpl. eapply mono_dist. omega.
  Qed.

  Global Instance sp_eq_dist {U} `{pU : cmetric U} n: Proper (dist n ==> dist n ==> dist n) (@sp_eq U _ _ _).
  Proof.
    move=>u1 u2 EQu t1 t2 EQt m Hle. simpl. split=>EQ.
    - transitivity u1.
      { symmetry. eapply mono_dist; last eassumption. omega. }
      transitivity t1; first assumption.
      eapply mono_dist; last eassumption. omega.
    - transitivity u2.
      { eapply mono_dist; last eassumption. omega. }
      transitivity t2; first assumption.
      symmetry. eapply mono_dist; last eassumption. omega.
  Qed.

  Global Program Instance eqbi_sp : EqBI SPred.
  Next Obligation.
    move=>u1 u2 EQu t1 t2 EQt n. simpl. rewrite ->EQu, EQt. reflexivity.
  Qed.
  Next Obligation.
    move=>n. rewrite /= -/dist. split.
    - move=>EQ P m HLe HP.
      assert (P u1 = S n = P u2) by now rewrite EQ. apply H; first omega. assumption.
    - move=>HP. pose(φ := n[(sp_eq _ _ _ _ u1)]). specialize (HP φ n (le_refl _)). eapply HP.
      simpl. reflexivity.
  Qed.
  Next Obligation.
    move=>?. simpl. tauto.
  Qed.
End SPredEq.
