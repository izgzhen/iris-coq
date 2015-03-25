Require Import Ssreflect.ssreflect.
Require Export PreoMet.

Section Definitions.
  Program Definition dclosed (p : nat -> Prop) :=
    forall n m (HLe : m <= n), p n -> p m.

  Record SPred :=
    mkSPred {spred    :> nat -> Prop;
             dpred    :  dclosed spred }.

  Program Definition sp_c (p : Prop) :=
    mkSPred (fun n => p) _.
  Next Obligation. intros m n _ HP. tauto. Qed.

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

  Global Instance spred_pord : Proper (pord ++> le --> impl) spred.
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

  Global Instance later_sp_dist n : Proper (dist n ==> dist n) later_sp.
  Proof.
    intros P Q EQPQ [| k]; simpl; first reflexivity. auto with arith.
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

Notation "▹ p" := (later_sp p) (at level 20) : spred_scope.
(*
Section Products.
  Context {R S} `{pR : preoType R} `{pS : preoType S}.

  Program Definition prod_up (p : UPred R) (q : UPred S) : UPred (R * S) :=
    mkUPred (fun n rs => p n (fst rs) /\ q n (snd rs)) _.
  Next Obligation.
    intros n m [r1 s1] [r2 s2] HLe [Subr Subs] [HP HQ]; simpl in HP, HQ.
    simpl; split; [rewrite <- Subr | rewrite <- Subs]; rewrite -> HLe; assumption.
  Qed.

  Global Instance prod_up_equiv : Proper (equiv ==> equiv ==> equiv) prod_up.
  Proof.
    intros p1 p2 EQp q1 q2 EQq n [r s]; simpl.
    rewrite -> EQp, EQq; tauto.
  Qed.
  Global Instance prod_up_dist n : Proper (dist n ==> dist n ==> dist n) prod_up.
  Proof.
    intros p1 p2 EQp q1 q2 EQq m [r s] HLt; simpl.
    split; intros [HP HQ]; (split; [apply EQp | apply EQq]); assumption.
  Qed.
  Global Instance prod_up_pord : Proper (pord ==> pord ==> pord) prod_up.
  Proof.
    intros p1 p2 Subp q1 q2 Subq n [r s]; simpl; intros [HP HQ].
    split; [apply Subp | apply Subq]; assumption.
  Qed.

End Products.
Notation "p × q" := (prod_up p q) (at level 40, left associativity) : spred_scope.
*)
Delimit Scope spred_scope with sp.
(*
Section Closures.
  Context {T} `{pcmT : pcmType T} {R} `{poT : preoType R} (P : T -> Prop) (Q : T -> UPred R).
  Local Obligation Tactic := intros.

  Program Definition all_cl : UPred R :=
    mkUPred (fun n r => forall t (HP : P t), Q t n r) _.
  Next Obligation.
    intros n m r1 r2 HLe HSubr HQ t' HP.
    rewrite <- HSubr, HLe; apply HQ, HP.
  Qed.

  Program Definition xist_cl : UPred R :=
    mkUPred (fun n r => exists t, P t /\ Q t n r) _.
  Next Obligation.
    intros n m r1 r2 HLe HSubr [t' [HP HQ]].
    exists t'; split; [assumption |].
    rewrite -> HLe, <- HSubr; apply HQ.
  Qed.

End Closures.

Notation "∀ w ∈ P , Q" := (all_cl P (fun w => Q)) (at level 60, w at level 30, P, Q at next level) : upred_scope.
Notation "∃ w ∈ P , Q" := (xist_cl P (fun w => Q)) (at level 60, w at level 30, P, Q at next level) : upred_scope.
*)