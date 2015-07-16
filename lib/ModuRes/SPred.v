Require Import Ssreflect.ssreflect Omega.
Require Export PreoMet BI.

Section Definitions.
  Program Definition dclosed (p : nat -> Prop) :=
    forall n m (HLe : m <= n), p n -> p m.

  Record SPred :=
    mkSPred {spred    :> nat -> Prop;
             bpred    :  spred 0;
             dpred    :  dclosed spred }.

End Definitions.
Arguments dpred {s} {n m} _ _.
Arguments mkSPred _ _ _.
Notation "'p[(' f ')]'" := (mkSPred f _ _).

Section Props.
  Program Definition sp_const P :=
    p[(fun n => match n return _ with
                | O => True
                | S _ => P end)].
  Next Obligation.
    move=>n m Hle. destruct m, n; simpl; tauto || inversion Hle.
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

  Definition sp_dist n (p q : SPred) :=
    forall m, m <= n -> (p m <-> q m).

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
    intros m Hle. destruct m; last omega.
    split; intro; apply bpred.
  Qed.

  Lemma spredNE {P1 P2 : SPred} {n} (EQP : P1 = n = P2) : P1 n -> P2 n.
  Proof. by apply EQP. Qed.

  Program Definition sp_compl (σ : chain SPred) (σc : cchain σ) :=
    p[(fun n => σ n n)].
  Next Obligation.
    apply bpred.
  Qed.
  Next Obligation.
    intros n m HLt HSub.
    eapply (chain_cauchy σ σc m n); auto with arith; [].
    eapply dpred; eassumption.
  Qed.

  Global Program Instance sp_cmetric : cmetric SPred := mkCMetr sp_compl.
  Next Obligation.
    intros n; intros i HLe k HLt; simpl.
    eapply (chain_cauchy σ σc k); eauto with arith.
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
    p[(laterF p)].
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
    split; intros HF;
    eapply HP; eassumption || symmetry; eassumption.
  Qed.
  Lemma dist_spred_simpl U (R : relation U) (f : U -> SPred) n {RS : Symmetric R}
        (HP : forall u1 u2 m (HLt : m <= n), R u1 u2 -> f u1 m -> f u2 m) :
    Proper (R ==> dist n) f.
  Proof.
    split; intros HF;
    eapply HP; eassumption || symmetry; eassumption.
  Qed.

  Lemma equiv_spred_simpl2 U V (RU : relation U) (RV : relation V) (f : U -> V -> SPred) {US : Symmetric RU} {VS : Symmetric RV}
        (HP : forall u1 u2 v1 v2 n, RU u1 u2 -> RV v1 v2 -> f u1 v1 n -> f u2 v2 n) :
    Proper (RU ==> RV ==> equiv) f.
  Proof.
    split; intros HF;
    eapply HP; eassumption || symmetry; eassumption.
  Qed.
  Lemma dist_spred_simpl2 U V (RU : relation U) (RV : relation V) (f : U -> V -> SPred) n {US : Symmetric RU} {VS : Symmetric RV}
        (HP : forall u1 u2 v1 v2 m (HLt : m <= n), RU u1 u2 -> RV v1 v2 -> f u1 v1 m -> f u2 v2 m) :
    Proper (RU ==> RV ==> dist n) f.
  Proof.
    split; intros HF;
    eapply HP; eassumption || symmetry; eassumption.
  Qed.
  
End Props.

Section SPredBI.
  Local Obligation Tactic := intros; eauto with typeclass_instances.

  (* Standard interpretations of propositional connectives. *)
  Global Program Instance top_sp : topBI SPred :=
    p[(fun _ => True)]. (* this behaves nicer than sp_c *)
  Next Obligation.
    repeat intro. exact I.
  Qed.
  
  Global Program Instance bot_sp : botBI SPred := sp_const False.
    
  Global Program Instance valid_sp : validBI SPred :=
    fun s => forall n, s n.

  Global Program Instance and_sp : andBI SPred :=
    fun P Q =>
      p[(fun n => P n /\ Q n)].
  Next Obligation.
    split; now apply bpred.
  Qed.
  Next Obligation.
    intros n m HLe; rewrite-> HLe; tauto.
  Qed.
  Global Program Instance or_sp : orBI SPred :=
    fun P Q =>
      p[(fun n => P n \/ Q n)].
  Next Obligation.
    left. now apply bpred.
  Qed.
  Next Obligation.
    intros n m HLe; rewrite-> HLe; tauto.
  Qed.

  Global Instance and_sp_equiv : Proper (equiv ==> equiv ==> equiv) and_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ n; simpl.
    rewrite-> EQP, EQQ; split; tauto.
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
    rewrite ->EQP, EQQ; hnf; tauto.
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

  Global Program Instance lattice_sp : Lattice SPred.
  Next Obligation.
    split; auto.
  Qed.
  Next Obligation.
    intros n _; exact I.
  Qed.
  Next Obligation.
    intros n HC; destruct n; last contradiction HC.
    apply bpred.
  Qed.
  Next Obligation.
    split.
    - intros HV n _. apply HV.
    - intros HV n. now apply HV.
  Qed.
  Next Obligation.
    move=>H. exact:(H 1).
  Qed.
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
    intros n HP; left; assumption.
  Qed.
  Next Obligation.
    intros n HQ; right; assumption.
  Qed.
  Next Obligation.
    intros n; simpl; tauto.
  Qed.
  
  Global Program Instance impl_sp : implBI SPred :=
    fun P Q =>
      p[(fun n => forall m, m <= n -> P m -> Q m)].
  Next Obligation.
    destruct m; last omega.
    apply bpred.
  Qed.
  Next Obligation.
    intros n m HLe HImp k HLe' HP.
    apply HImp; try (etransitivity; eassumption); assumption.
  Qed.
  
  (* BI connectives: Boring. We'd actually want just a Heyting Algebra for SPred, but whatever. *)
  Global Instance sc_sp : scBI SPred := and_sp.
  Global Instance si_sp : siBI SPred := impl_sp.

  (* For some reason tc inference gets confused otherwise *)
  Existing Instance sp_type.

  Global Instance impl_sp_dist n : Proper (dist n ==> dist n ==> dist n) impl_sp.
  Proof.
    intros P1 P2 EQP Q1 Q2 EQQ m HLt; simpl.
    split; intros; apply EQQ, H, EQP; now eauto with arith.
  Qed.

  Global Instance sc_sp_equiv : Proper (equiv ==> equiv ==> equiv) sc_sp := and_sp_equiv.
  Global Instance sc_sp_dist n : Proper (dist n ==> dist n ==> dist n) sc_sp := and_sp_dist n.
  Global Instance sc_sp_ord : Proper (pord ==> pord ==> pord) sc_sp := and_sp_ord.

  Global Instance si_sp_dist n : Proper (dist n ==> dist n ==> dist n) si_sp := impl_sp_dist n.

  (* Quantifiers. *)
  Global Program Instance all_sp : allBI SPred :=
    fun T eqT mT cmT R =>
      p[(fun n => forall t, R t n)].
  Next Obligation.
    apply bpred.
  Qed.
  Next Obligation.
    intros n m HLe HR t. rewrite-> HLe; apply HR.
  Qed.

  Definition xist_spF {T: Type} (R: T -> SPred) n :=
    match n with
    | O => True
    | S _ => exists t, R t n
    end.
  Global Program Instance xist_sp : xistBI SPred :=
    fun T eqT mT cmT R =>
      p[(xist_spF R)].
  Next Obligation.
    exact I.
  Qed.
  Next Obligation.
    intros n m HLe. destruct n.
    { destruct m; last omega. intro; exact I. }
    intros [t HR]. destruct m; first exact I.
    exists t; rewrite-> HLe; apply HR.
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
      destruct m; first reflexivity.
      split; intros [t HR]; exists t; apply EQR; now auto.
    Qed.

  End Quantifiers.

  Global Program Instance cbi_sp : ComplBI SPred.
  Next Obligation.
    split; intros HH n.
    - intros HP m HLe HQ; apply HH; split; [rewrite-> HLe |]; assumption.
    - intros [HP HQ]; eapply HH; eassumption || reflexivity.
  Qed.
  Next Obligation.
    intros n; split; simpl; tauto.
  Qed.
  Next Obligation.
    split; intros HH n; simpl in *.
    - intros HP m HLe HQ. apply HH. split; last assumption. rewrite-> HLe. assumption.
    - intros [HP HQ]. eapply HH; try eassumption; omega.
  Qed.
  Next Obligation.
    split.
    - intros HH v n HP. apply HH; assumption.
    - intros HH v n HP. apply HH. assumption.
  Qed.
  Next Obligation.
    split.
    - intros HH n. destruct n; first (intro; exact: bpred).
      intros [u HP]; eapply HH; eassumption.
    - intros HH u n. destruct n; first (intro; exact: bpred).
      intros HP; apply HH; exists u; assumption.
  Qed.

End SPredBI.

Section SPredEq.
  Global Program Instance sp_eq : eqBI SPred :=
    fun U {eqU mU cmU u1 u2} => p[(fun n => u1 = n = u2)].
  Next Obligation.
    exact:dist_bound.
  Qed.
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

  Global Instance eqbi_sp : EqBI SPred.
  Proof.
    split; intros.
    - move=>u1 u2 EQu t1 t2 EQt n. simpl. rewrite ->EQu, EQt. reflexivity.
    - apply _.
    - move=>n. rewrite /= -/dist. split.
      + move=>EQ P m HLe HP.
        assert (P u1 = n = P u2) by now rewrite EQ. apply H; first omega. assumption.
      + move=>HP. pose(φ := n[(sp_eq _ _ _ _ u1)]). specialize (HP φ n (le_refl _)). eapply HP.
        simpl. reflexivity.
  Qed.

  Lemma sp_eq_iff U `{cmU: cmetric U} {u1 u2: U} n:
    ((intEq u1 u2):SPred) n <-> u1 = n = u2.
  Proof.
    reflexivity.
  Qed.
End SPredEq.
