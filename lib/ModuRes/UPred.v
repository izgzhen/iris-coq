Require Export PreoMet.

Section Definitions.
  Context {T} {pT : preoType T}.

  Program Definition uniform (p : nat -> T -> Prop) :=
    forall n m (t1 t2 : T) (HLe : m <= n) (HSub : t1 ⊑ t2), p n t1 -> p m t2.

  Record UPred :=
    mkUPred {pred     :> nat -> T -> Prop;
             uni_pred :  uniform pred }.

  Program Definition up_cr (p : T -> Prop) {HP : Proper (pord ==> impl) p}:=
    mkUPred (fun n t => p t) _.
  Next Obligation. intros m n t1 t2 _ HT; simpl; rewrite HT; tauto. Qed.

  Definition up_equiv (p q : UPred) := forall n t, p n t == q n t.

  Global Instance up_equiv_e: Equivalence up_equiv.
  Proof.
    split.
    - intros p n t; reflexivity.
    - intros p q Hpq n t; symmetry; apply Hpq.
    - intros p q r Hpq Hqr n t; etransitivity; [apply Hpq | apply Hqr].
  Qed.

  Global Program Instance up_type : Setoid UPred := mkType up_equiv.

  Definition up_dist n (p q : UPred) :=
    forall m t, m < n -> (p m t <-> q m t).

  Global Program Instance up_metric : metric UPred := mkMetr up_dist.
  Next Obligation.
    intros p q Hpq r s Hrs; split; intros HD m t HLt; [symmetry in Hpq, Hrs |];
    rewrite (Hpq m t), (Hrs m t); apply HD; assumption.
  Qed.
  Next Obligation.
    split; intros HEq.
    - intros n t; apply (HEq (S n)); auto with arith.
    - intros _ m t _; apply HEq.
  Qed.
  Next Obligation.
    intros p q Hpq m t HLt; symmetry; apply Hpq, HLt.    
  Qed.
  Next Obligation.
    intros p q r Hpq Hqr m t HLt; etransitivity; [apply Hpq, HLt | apply Hqr, HLt].
  Qed.
  Next Obligation.
    intros m t HLt; apply H; auto with arith.    
  Qed.
  Next Obligation.
    intros m t HLt; inversion HLt.    
  Qed.

  Program Definition up_compl (σ : chain UPred) (σc : cchain σ) :=
    mkUPred (fun n t => σ (S n) n t) _.
  Next Obligation.
    intros n m t1 t2 HLt HSub HCn.
    eapply (chain_cauchy σ σc (S m) (S n)); auto with arith; [].
    eapply uni_pred; eassumption.
  Qed.

  Global Program Instance up_cmetric : cmetric UPred := mkCMetr up_compl.
  Next Obligation.
    intros n; exists n; intros i HLe k t HLt; simpl.
    eapply (chain_cauchy σ σc (S k)); eauto with arith.
  Qed.

  Definition up_ord (p q : UPred) := forall n t, p n t -> q n t.

  Global Program Instance up_preotype : preoType UPred := mkPOType up_ord.
  Next Obligation.
    split.
    + intros p n t; tauto.
    + intros p q r Hpq Hqr n t Hp; apply Hqr, Hpq, Hp.
  Qed.

  Global Instance up_pcmetric : pcmType UPred.
  Proof.
    split.
    + intros p q Hpq r s Hrs; split; intros Hpr n t Hq;
      apply Hrs, Hpr, Hpq, Hq.
    + intros σ ρ σc ρc HSub n t Hpc; simpl in *; apply HSub, Hpc.
  Qed.

  Global Instance upred_equiv : Proper (equiv ==> eq ==> eq ==> iff) pred.
  Proof.
    add_morphism_tactic; intros R1 R2 EQR n t; split; intros HH; apply EQR; assumption.
  Qed.

  Global Instance upred_pord : Proper (pord ==> le --> pord ==> impl) pred.
  Proof.
    intros R1 R2 SubR n1 n2 Len t1 t2 Subt HR1; eapply SubR, uni_pred; eassumption.
  Qed.

  Definition laterF (p : nat -> T -> Prop) n t :=
    match n with
      | O => True
      | S n => p n t
    end.
  Program Definition later_up (p : UPred) :=
    mkUPred (laterF p) _.
  Next Obligation.
    intros [| m] [| n] t1 t2 HLe HSubt; simpl; try tauto; [now inversion HLe |].
    intros HP; eapply uni_pred; [| eassumption | eassumption]; auto with arith.
  Qed.

  Global Instance later_up_equiv : Proper (equiv ==> equiv) later_up.
  Proof.
    intros P Q EQPQ [| n] t; simpl; [reflexivity | apply EQPQ].
  Qed.

  Global Instance later_up_dist n : Proper (dist n ==> dist n) later_up.
  Proof.
    intros P Q EQPQ [| k] t HLt; simpl; [reflexivity | apply EQPQ; auto with arith].
  Qed.

  Lemma equiv_upred_simpl U (R : relation U) (f : U -> UPred) {RS : Symmetric R}
        (HP : forall u1 u2 n t, R u1 u2 -> f u1 n t -> f u2 n t) :
    Proper (R ==> equiv) f.
  Proof.
    intros u1 u2 HRu; split; intros HF; (eapply HP; [| eassumption]);
    [| symmetry]; assumption.
  Qed.
  Lemma dist_upred_simpl U (R : relation U) (f : U -> UPred) n {RS : Symmetric R}
        (HP : forall u1 u2 m t (HLt : m < n), R u1 u2 -> f u1 m t -> f u2 m t) :
    Proper (R ==> dist n) f.
  Proof.
    intros u1 u2 HRu m t HLt; split; intros HF;
    (eapply HP; [eassumption | | eassumption]); [| symmetry]; assumption.
  Qed.

  Global Instance const_resp P : Proper (pord (T := T) ==> impl) (const P).
  Proof. add_morphism_tactic; unfold impl; unfold const; tauto. Qed.

End Definitions.

Global Arguments UPred T {pT}.
Arguments uni_pred {T pT u} {n m t1 t2} _ _ _.

Notation "▹ p" := (later_up p) (at level 20) : upred_scope.

Section Products.
  Context {R S} {pR : preoType R} {pS : preoType S}.

  Program Definition prod_up (p : UPred R) (q : UPred S) : UPred (R * S) :=
    mkUPred (fun n rs => p n (fst rs) /\ q n (snd rs)) _.
  Next Obligation.
    intros n m [r1 s1] [r2 s2] HLe [Subr Subs] [HP HQ]; simpl in HP, HQ.
    simpl; split; [rewrite <- Subr | rewrite <- Subs]; rewrite HLe; assumption.
  Qed.

  Global Instance prod_up_equiv : Proper (equiv ==> equiv ==> equiv) prod_up.
  Proof.
    intros p1 p2 EQp q1 q2 EQq n [r s]; simpl.
    rewrite EQp, EQq; tauto.
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

Notation "p × q" := (prod_up p q) (at level 40, left associativity) : upred_scope.
Delimit Scope upred_scope with up.

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
    rewrite HLe, <- HSubr; apply HQ.
  Qed.

End Closures.

Notation "∀ w ∈ P , Q" := (all_cl P (fun w => Q)) (at level 60, w at level 30, P, Q at next level) : upred_scope.
Notation "∃ w ∈ P , Q" := (xist_cl P (fun w => Q)) (at level 60, w at level 30, P, Q at next level) : upred_scope.
