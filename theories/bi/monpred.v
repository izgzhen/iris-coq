From iris.bi Require Import derived_laws.

Structure bi_index :=
  BiIndex
    { bi_index_type :> Type;
      bi_index_rel : SqSubsetEq bi_index_type;
      bi_index_rel_preorder : PreOrder (⊑) }.

Local Notation mono R P := (Proper (R ==> bi_entails) P).
Existing Instances bi_index_rel bi_index_rel_preorder.

Record monPred (I : bi_index) (B : bi) :=
  FUN
    { monPred_car :> I -c> B;
      monPred_mono :> mono (⊑) monPred_car }.

Arguments monPred _ _ : clear implicits.
Arguments FUN [_ _] _ _.
Arguments monPred_car [_ _] _ _.
Arguments monPred_mono [_ _] _ _ _ _ .

Notation monPred_upclose I B :=
  (λ (P : bi_index_type I → B) i, (∀ j (_ : i ⊑ j), (P j))%I).

Instance monPred_upclose_mono I (B : bi) (P : bi_index_type I → B) :
  mono (⊑) (monPred_upclose I B (P)).
Proof.
  repeat intro. do !apply bi.forall_intro => ?.
  rewrite !bi.forall_elim; [reflexivity|by etransitivity].
Qed.

Notation monPred_upclosed I B P :=
  (@FUN I B%type (monPred_upclose I B P%function) (monPred_upclose_mono I B%type P%function)).

Instance monPred_dist {I B} : Dist (monPred I B) := λ n P1 P2, dist n (monPred_car P1) (monPred_car P2).
Instance monPred_equiv {I B} : Equiv (monPred I B) := λ P1 P2, (monPred_car P1) ≡ (monPred_car P2).

Global Instance monPred_car_ne I B : NonExpansive (@monPred_car I B).
Proof.
  rewrite /monPred_car. move => n [f /= fm] [g gm].
  by rewrite {1}/dist /= /monPred_dist /=.
Qed.

Section Ofe_Cofe.
  Context {I : bi_index} {B : bi}.
  Implicit Types i : I.
  Implicit Types P : monPred I B.

  Definition monPred_sig P:
    sig (fun f : I -c> B => mono (⊑) f) :=
    exist _ (monPred_car P) (monPred_mono P).

  Definition sig_monPred
             (P' : sig (fun f : I -c> B => mono (⊑) f)):
    monPred I B :=
    FUN (proj1_sig P') (proj2_sig P').

  Lemma monPred_sig_equiv:
    ∀ P Q, P ≡ Q ↔ monPred_sig P ≡ monPred_sig Q.
  Proof. done. Qed.

  Lemma monPred_sig_dist:
    ∀ n, ∀ P Q : monPred I B, P ≡{n}≡ Q ↔ monPred_sig P ≡{n}≡ monPred_sig Q.
  Proof. done. Qed.

  Definition monPred_ofe_mixin : OfeMixin (monPred I B).
  Proof. by apply (iso_ofe_mixin monPred_sig monPred_sig_equiv monPred_sig_dist). Qed.

  Canonical Structure monPred_ofe := OfeT (monPred I B) (monPred_ofe_mixin).

  Instance monPred_cofe
  {C : Cofe B}
  {limit_preserving_entails :
     ∀ cP cQ : chain B, (∀ n, cP n ⊢ cQ n) → compl cP ⊢ compl cQ}
    : Cofe (monPred_ofe).
  Proof.
    unshelve refine (iso_cofe_subtype (A:=I-c>B)
                                      (fun f => mono (⊑) f)
                                      (@FUN _ _)
                                      (@monPred_car _ _) _ _ _);
    [done|done|].
    intros c i j Hij.
    apply limit_preserving_entails.
    intros. by apply monPred_mono.
  Qed.
End Ofe_Cofe.


Inductive monPred_entails {I B} (P1 P2 : monPred I B) : Prop := monPred_in_entails : (∀ i, bi_entails (monPred_car P1 i) (monPred_car P2 i)) → monPred_entails P1 P2.
Lemma monPred_entails_eq {I B} P1 P2 : @monPred_entails I B P1 P2 ↔ (∀ i, bi_entails (monPred_car P1 i) (monPred_car P2 i)).
Proof. split=>[[]//|//]. Qed.

Hint Immediate monPred_in_entails.

Program Definition monPred_pure_def {I B} : Prop → monPred I B := λ P, FUN (λ _, bi_pure P) _.
Definition monPred_pure_aux : seal (@monPred_pure_def). by eexists. Qed.
Definition monPred_pure {I B} := unseal (@monPred_pure_aux) I B.
Definition monPred_pure_eq : @monPred_pure = _ := seal_eq _.

Program Definition monPred_emp {I B} := @FUN I B (λ _, emp)%I _.

  
Program Definition monPred_and_def {I B} := λ (P Q : monPred I B), @FUN I B (λ i, monPred_car P i ∧ monPred_car Q i)%I _.
Next Obligation.
  intros I B P Q V1 V2 HV.
  by apply bi.and_mono; apply monPred_mono.
Qed.
Definition monPred_and_aux : seal (@monPred_and_def). by eexists. Qed.
Definition monPred_and {I B} := unseal (@monPred_and_aux) I B.
Definition monPred_and_eq : @monPred_and = _ := seal_eq _.

Program Definition monPred_or_def {I B} := λ (P Q : monPred I B), @FUN I B (λ i, monPred_car P i ∨ monPred_car Q i)%I _.
Next Obligation.
  intros I B P Q V1 V2 HV.
  by apply bi.or_mono; apply monPred_mono.
Qed.
Definition monPred_or_aux : seal (@monPred_or_def). by eexists. Qed.
Definition monPred_or {I B} := unseal (@monPred_or_aux) I B.
Definition monPred_or_eq : @monPred_or = _ := seal_eq _.

Program Definition monPred_impl_def {I B} := λ (P Q : monPred I B), monPred_upclosed I B (λ i, monPred_car P i → monPred_car Q i)%I.
Definition monPred_impl_aux : seal (@monPred_impl_def). by eexists. Qed.
Definition monPred_impl {I B} := unseal (@monPred_impl_aux) I B.
Definition monPred_impl_eq : @monPred_impl = _ := seal_eq _.

Program Definition monPred_forall_def {I B} A := λ (Φ : A -> monPred I B), @FUN I B (λ i, ∀ x : A, monPred_car (Φ x) i)%I _.
Next Obligation.
  intros I B P Q V1 V2 HV.
  by apply bi.forall_mono; intros; apply monPred_mono.
Qed.
Definition monPred_forall_aux : seal (@monPred_forall_def). by eexists. Qed.
Definition monPred_forall {I B} := unseal (@monPred_forall_aux) I B.
Definition monPred_forall_eq : @monPred_forall = _ := seal_eq _.

Program Definition monPred_exist_def {I B} A := λ (Φ : A -> monPred I B), FUN (λ i, ∃ x : A, monPred_car (Φ x) i)%I _.
Next Obligation.
  intros I B P Q V1 V2 HV.
  by apply bi.exist_mono; intros; apply monPred_mono.
Qed.
Definition monPred_exist_aux : seal (@monPred_exist_def). by eexists. Qed.
Definition monPred_exist {I B} := unseal (@monPred_exist_aux) I B.
Definition monPred_exist_eq : @monPred_exist = _ := seal_eq _.

Definition monPred_internal_eq_def {I B} A := λ a b, @FUN I B (λ _, @bi_internal_eq B A a b) _.
Definition monPred_internal_eq_aux : seal (@monPred_internal_eq_def). by eexists. Qed.
Definition monPred_internal_eq {I B} := unseal (@monPred_internal_eq_aux) I B.
Definition monPred_internal_eq_eq : @monPred_internal_eq = _ := seal_eq _.

Program Definition monPred_sep_def {I B} := λ (P Q : monPred I B), FUN (λ i, monPred_car P i ∗ monPred_car Q i)%I _.
Next Obligation.
  intros I B P Q V1 V2 HV.
  by apply bi.sep_mono; intros; apply monPred_mono.
Qed.
Definition monPred_sep_aux : seal (@monPred_sep_def). by eexists. Qed.
Definition monPred_sep {I B} := unseal monPred_sep_aux I B.
Definition monPred_sep_eq : @monPred_sep = _ := seal_eq _.

Program Definition monPred_wand_def {I B} := λ (P Q : monPred I B), monPred_upclosed I B (λ i, monPred_car P i -∗ monPred_car Q i)%I.
Definition monPred_wand_aux : seal (@monPred_wand_def). by eexists. Qed.
Definition monPred_wand {I B} := unseal monPred_wand_aux I B.
Definition monPred_wand_eq : @monPred_wand = _ := seal_eq _.

Program Definition monPred_persistently_def {I B} : monPred I B → monPred I B := λ P, FUN (λ i, bi_persistently (monPred_car P i)) _.
Next Obligation.
  intros I B P V1 V2 HV.
  by apply bi.persistently_mono; intros; apply monPred_mono.
Qed.
Definition monPred_persistently_aux : seal (@monPred_persistently_def). by eexists. Qed.
Definition monPred_persistently {I B} := unseal monPred_persistently_aux I B.
Definition monPred_persistently_eq : @monPred_persistently = _ := seal_eq _.

Program Definition monPred_plainly_def {I B} : monPred I B → monPred I B := λ P, FUN (λ i, bi_plainly (monPred_car P i)) _.
Next Obligation.
  intros I B P V1 V2 HV.
  by apply bi.plainly_mono; intros; apply monPred_mono.
Qed.
Definition monPred_plainly_aux : seal (@monPred_plainly_def). by eexists. Qed.
Definition monPred_plainly {I B} := unseal monPred_plainly_aux I B.
Definition monPred_plainly_eq : @monPred_plainly = _ := seal_eq _.

Program Definition monPred_later_def {I} {B : sbi} (P : monPred I B) : monPred I B := FUN (λ i, ▷ (monPred_car P i))%I _.
Next Obligation.
  intros I B P V1 V2 HV.
  by apply bi.later_mono; intros; apply monPred_mono.
Qed.
Definition monPred_later_aux : seal (@monPred_later_def). by eexists. Qed.
Definition monPred_later {I B} := unseal monPred_later_aux I B.
Definition monPred_later_eq : @monPred_later = _ := seal_eq _.


Program Definition monPred_in_def {I B} (i_0 : bi_index_type I) : monPred I B := FUN (λ i : I, ⌜i_0 ⊑ i⌝%I) _.
Next Obligation.
  intros I B V V1 V2 HV.
  by apply bi.pure_mono; intros; etrans.
Qed.
Definition monPred_in_aux : seal (@monPred_in_def). by eexists. Qed.
Definition monPred_in {I B} := unseal (@monPred_in_aux) I B.
Definition monPred_in_eq : @monPred_in = _ := seal_eq _.

Lemma monPred_all_def_mono {I B} (P : monPred I B) : mono (⊑) (λ _ : I, ∀ i, monPred_car P i)%I.
Proof. apply _. Qed.
Program Definition monPred_all_def {I B} := λ (P : monPred I B), FUN (λ _ : I, ∀ i, monPred_car P i)%I (monPred_all_def_mono P).
Definition monPred_all_aux : seal (@monPred_all_def). by eexists. Qed.
Definition monPred_all {I B} := unseal (@monPred_all_aux) I B.
Definition monPred_all_eq : @monPred_all = _ := seal_eq _.


Program Definition monPred_ipure_def {I B} P : monPred I B := FUN (λ _, P) _.
Definition monPred_ipure_aux : seal (@monPred_ipure_def). by eexists. Qed.
Definition monPred_ipure {I B} := unseal monPred_ipure_aux I B.
Definition monPred_ipure_eq : @monPred_ipure = _ := seal_eq _.

Local Definition unseal_eqs :=
  (@monPred_pure_eq, @monPred_and_eq, @monPred_or_eq, @monPred_impl_eq, @monPred_forall_eq,
   @monPred_exist_eq, @monPred_internal_eq_eq, @monPred_sep_eq, @monPred_wand_eq, @monPred_persistently_eq,
   @monPred_plainly_eq,
   @monPred_entails_eq, @monPred_later_eq, @monPred_in_eq, @monPred_all_eq, @monPred_ipure_eq 
  ).

Lemma monPred_bi_mixin I B :
  BiMixin  (@monPred_ofe_mixin I B) monPred_entails monPred_emp monPred_pure monPred_and monPred_or monPred_impl monPred_forall monPred_exist monPred_internal_eq monPred_sep monPred_wand monPred_plainly monPred_persistently.
Proof.
  rewrite !unseal_eqs.
  split;
  (* repeat setoid_rewrite monPred_entails_eq; repeat intro. *)
  repeat (match goal with | [|- monPred_entails _ _ -> _] => intros [] end
          || intro
         );
  try match goal with | [ |- monPred_entails _ _] => split => ? end.
  - split.
    + intros ?. by econstructor.
    + intros ? ? ? [e1] [e2]. constructor => ?. by rewrite e1 e2.
  - split.
    + intros. split; split => i; move: (H i); by apply bi.equiv_spec.
    + intros [[] []] ?. by apply bi.equiv_spec.
  - by apply: bi.pure_ne.
  - by apply: bi.and_ne.
  - by apply: bi.or_ne.
  - do 2!apply bi.forall_ne => ?. by repeat apply: bi.impl_ne.
  - apply bi.forall_ne => ?. by firstorder.
  - apply bi.exist_ne => ?. by firstorder.
  - by apply bi.sep_ne.
  - do 2!apply bi.forall_ne => ?. by apply bi.wand_ne.
  - by apply bi.plainly_ne.
  - by apply bi.persistently_ne.
  - by apply bi.internal_eq_ne.
  - by apply bi.pure_intro.
  - apply bi.pure_elim'. by move/H => [] /(_ _) /=.
  - by apply bi.pure_forall_2.
  - by apply bi.and_elim_l.
  - by apply bi.and_elim_r.
  - by apply bi.and_intro.
  - by apply bi.or_intro_l.
  - by apply bi.or_intro_r.
  - by apply bi.or_elim.
  - do 2!apply bi.forall_intro => ?.
    rewrite -H monPred_mono //.
    apply: bi.impl_intro_l.
      by rewrite (comm (∧)%I).
  - do !setoid_rewrite bi.forall_elim in H; last reflexivity.
    rewrite /= H. by rewrite bi.impl_elim_l.
  - apply bi.forall_intro => ?. by apply H.
  - by apply: bi.forall_elim.
  - by rewrite /= -bi.exist_intro.
  - apply bi.exist_elim => ?. by apply H.
  - by apply bi.internal_eq_refl.
  - do 2!apply bi.forall_intro => ? /=.
    erewrite (bi.internal_eq_rewrite _ _ (λ c, monPred_car (Ψ c) _)) => //.
    intros ? ? ? ?. by apply H.
  - by apply bi.fun_ext.
  - by apply bi.sig_eq.
  - by apply bi.discrete_eq_1.
  - by apply bi.sep_mono.
  - by apply bi.emp_sep_1.
  - by apply bi.emp_sep_2.
  - by apply bi.sep_comm'.
  - by apply bi.sep_assoc'.
  - apply bi.forall_intro => ?.
    apply bi.forall_intro => M.
    apply bi.wand_intro_r.
    rewrite (monPred_mono _ _ _ M). by apply H.
  - apply bi.wand_elim_l'.
      by do !setoid_rewrite bi.forall_elim in H; last reflexivity.
  - by apply bi.plainly_mono.
  - by apply bi.plainly_elim_persistently.
  - by apply bi.plainly_idemp_2.
  - by apply bi.plainly_forall_2.
  - rewrite /=. admit.
  (* apply bi.prop_ext *)
  - rewrite /=.
    do 2!(rewrite -bi.persistently_forall_2; apply bi.forall_intro => ?).
    rewrite !bi.forall_elim //.
    by apply bi.persistently_impl_plainly.
  - rewrite /=.
    do 2!(rewrite -bi.plainly_forall_2; apply bi.forall_intro => ?).
    rewrite !bi.forall_elim //.
    by apply bi.plainly_impl_plainly.
  - by apply bi.plainly_emp_intro.
  - rewrite /=.
    apply: (bi_mixin_plainly_absorbing (PROP:=B) _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bi_bi_mixin B)).
    (* XXX: FIXME *)
  - by apply bi.persistently_mono.
  - by apply bi.persistently_idemp_2.
  - by apply bi.plainly_persistently_1.
  - by apply bi.persistently_forall_2.
  - by apply bi.persistently_exist_1.
  - rewrite /=.
    refine (bi_mixin_persistently_absorbing _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    exact (bi_bi_mixin B). (* WTF? *)
  - by apply bi.persistently_and_sep_elim.
Admitted.


Canonical Structure monPredI I B : bi :=
  Bi (monPred I B) monPred_dist monPred_equiv monPred_entails monPred_emp monPred_pure monPred_and monPred_or monPred_impl monPred_forall monPred_exist monPred_internal_eq monPred_sep monPred_wand monPred_plainly monPred_persistently monPred_ofe_mixin (monPred_bi_mixin _ _).

Instance monPred_affine I B : BiAffine B → BiAffine (monPredI I B).
Proof. split => ?. by apply affine. Qed.

Arguments monPred_ofe _ _ : clear implicits.
Arguments monPred _ _ : clear implicits.

Module Prelim.
  Ltac unseal := rewrite 
                   /sbi_except_0
                   (* TODO: the next line used to contain uPred.emp and that was necessary *)
                   /bi_emp /= /bi_pure /bi_and /bi_or /bi_impl
                   /bi_forall /bi_exist /bi_internal_eq /bi_sep /bi_wand /bi_persistently /bi_plainly /bi_affinely /sbi_later /=
                   /sbi_emp /sbi_pure /sbi_and /sbi_or /sbi_impl
                   /sbi_forall /sbi_exist /sbi_internal_eq /sbi_sep /sbi_wand /sbi_persistently /sbi_plainly
                   /=
                   !unseal_eqs /=.
End Prelim.

Lemma monPred_wand_force I B (P Q : monPred I B) i:
  monPred_car (P -∗ Q) i -∗ (monPred_car P i -∗ monPred_car Q i).
Proof. Prelim.unseal. by rewrite !bi.forall_elim. Qed.

Lemma monPred_impl_force I B (P Q : monPred I B) i:
  monPred_car (P → Q) i -∗ (monPred_car P i → monPred_car Q i).
Proof. Prelim.unseal. by rewrite !bi.forall_elim. Qed.

Lemma monPred_persistently_if_eq I B p (P : monPred I B) i:
  monPred_car (bi_persistently_if p P) i = bi_persistently_if p (monPred_car P i).
Proof. rewrite /bi_persistently_if. Prelim.unseal. by destruct p. Qed.

Lemma monPred_plainly_if_eq I B p (P : monPred I B) i:
  monPred_car (bi_plainly_if p P) i = bi_plainly_if p (monPred_car P i).
Proof. rewrite /bi_plainly_if. Prelim.unseal. by destruct p. Qed.

Lemma monPred_affinely_if_eq I B p (P : monPred I B) i:
  monPred_car (bi_affinely_if p P) i = bi_affinely_if p (monPred_car P i).
Proof. rewrite /bi_affinely_if. destruct p => //. rewrite /bi_affinely. by Prelim.unseal. Qed.

Lemma monPred_sbi_mixin I (B : sbi) :
    SbiMixin (PROP:=monPred I B) monPred_entails monPred_pure monPred_or monPred_impl monPred_forall monPred_exist monPred_internal_eq monPred_sep monPred_plainly monPred_persistently monPred_later.
Proof.
  intros.
  Prelim.unseal.
  split; repeat setoid_rewrite monPred_entails_eq; repeat intro.
  - apply bi.later_contractive. rewrite /dist_later in H. destruct n => //. by apply H.
  - by apply bi.later_eq_1.
  - by apply bi.later_eq_2.
  - by apply bi.later_mono.
  - rewrite /= !bi.forall_elim; last reflexivity. by apply bi.löb.
  - by apply bi.later_forall_2.
  - by apply bi.later_exist_false.
  - by apply bi.later_sep_1.
  - by apply bi.later_sep_2.
  - by apply bi.later_plainly_1.
  - by apply bi.later_plainly_2.
  - by apply bi.later_persistently_1.
  - by apply bi.later_persistently_2.
  - rewrite /= -bi.forall_intro. apply bi.later_false_em.
    intros. rewrite <-bi.forall_intro. reflexivity.
    intros. by rewrite monPred_mono.
Qed.
Canonical Structure monPredSI I (B : sbi) : sbi :=
    Sbi (monPred I B) monPred_dist monPred_equiv monPred_entails monPred_emp monPred_pure monPred_and monPred_or monPred_impl monPred_forall monPred_exist monPred_internal_eq monPred_sep monPred_wand monPred_plainly monPred_persistently monPred_later monPred_ofe_mixin (bi_bi_mixin _) (monPred_sbi_mixin _ _).

Ltac unseal := rewrite
                 /(@sbi_except_0 (monPredSI _ _))
                 /(@bi_emp (monPredI _ _)) /=
                 /(@bi_pure (monPredI _ _))
                 /(@bi_and (monPredI _ _))
                 /(@bi_or (monPredI _ _))
                 /(@bi_impl (monPredI _ _))
                 /(@bi_forall (monPredI _ _))
                 /(@bi_exist (monPredI _ _))
                 /(@bi_internal_eq (monPredI _ _))
                 /(@bi_sep (monPredI _ _))
                 /(@bi_wand (monPredI _ _))
                 /(@bi_persistently (monPredI _ _))
                 /(@sbi_later (monPredSI _ _)) /=
                 /(@sbi_emp (monPredSI _ _))
                 /(@sbi_pure (monPredSI _ _))
                 /(@sbi_and (monPredSI _ _))
                 /(@sbi_or (monPredSI _ _))
                 /(@sbi_impl (monPredSI _ _))
                 /(@sbi_forall (monPredSI _ _))
                 /(@sbi_exist (monPredSI _ _))
                 /(@sbi_internal_eq (monPredSI _ _))
                 /(@sbi_sep (monPredSI _ _))
                 /(@sbi_wand (monPredSI _ _))
                 /(@sbi_persistently (monPredSI _ _))
                 /=
                 !unseal_eqs /=.


Section ProofmodeInstances.
  Global Instance monPred_car_persistent B I P i : Persistent P → Persistent (@monPred_car B I P i).
  Proof. move => [] /(_ i). by unseal. Qed.

  Global Instance monPred_in_persistent {I B} V : Persistent (@monPred_in I B V).
  Proof.
    unfold Persistent.
    unseal; split => ?.
      by apply bi.pure_persistent.
  Qed. (* TODO: why is this so long and why can I not rewrite monPred_persistently after move? *)
End ProofmodeInstances.

(* Notation "☐ P" := (monPred_ipure P%I) *)
(*   (at level 20, right associativity) : bi_scope. *)

Global Instance monPred_ipure_timeless {I B} (P : sbi_car B) :
  Timeless (P) → Timeless (@monPred_ipure I B P).
Proof.
  intros. split => ? /=.
  unseal. rewrite /monPred_ipure_def. exact: H.
Qed.

Global Instance monPred_ipure_persistent {I B} (P : sbi_car B) :
  Persistent (P) → Persistent (@monPred_ipure I B P).
Proof.
  intros. split => ? /=.
  unseal. rewrite /monPred_ipure_def. exact: H.
Qed.
