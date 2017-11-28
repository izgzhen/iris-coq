From iris.bi Require Import derived_laws.

Structure bi_index :=
  BiIndex
    { bi_index_type :> Type;
      bi_index_rel : SqSubsetEq bi_index_type;
      bi_index_rel_preorder : PreOrder (⊑) }.

Local Notation mono R P := (Proper (R ==> (⊢)) P).
Local Existing Instances bi_index_rel bi_index_rel_preorder.

Structure funbi_ty (I : bi_index) (B : bi) :=
  FUN
    { funbi_car :> I -c> B;
      funbi_mono :> mono (⊑) funbi_car }.

Arguments funbi_ty _ _ : clear implicits.
Arguments FUN [_ _] _ _.
Arguments funbi_car [_ _] _ _.
Arguments funbi_mono [_ _] _ _ _ _ .

Notation funbi_upclose I B := (λ (P : bi_index_type I → B), (λ i, (∀ j (_ : i ⊑ j), (P j)))%I).

Instance funbi_upclose_mono I (B : bi) (P : bi_index_type I → B) : mono (⊑) (funbi_upclose I B (P)).
Proof.
  repeat intro. do !apply bi.forall_intro => ?.
  rewrite !bi.forall_elim; [reflexivity|by etransitivity].
Qed.

Notation funbi_upclosed I B P := (@FUN I B%type (funbi_upclose I B P%function) (funbi_upclose_mono I B%type P%function)).

Instance funbi_dist {I B} : Dist (funbi_ty I B) := λ n P1 P2, dist n (funbi_car P1) (funbi_car P2).
Instance funbi_equiv {I B} : Equiv (funbi_ty I B) := λ P1 P2, (funbi_car P1) ≡ (funbi_car P2).

Global Instance funbi_car_ne I B : NonExpansive (@funbi_car I B).
Proof.
  rewrite /funbi_car. move => n [f /= fm] [g gm].
  by rewrite {1}/dist /= /funbi_dist /=.
Qed.

Section Ofe_Cofe.
  Context {I : bi_index} {B : bi}.
  Implicit Types i : I.
  Implicit Types P : funbi_ty I B.

  Definition funbi_sig P:
    sig (fun f : I -c> B => mono (bi_index_rel I) f) :=
    exist _ (funbi_car P) (funbi_mono P).

  Definition sig_funbi
             (P' : sig (fun f : I -c> B => mono (bi_index_rel I) f)):
    funbi_ty I B :=
    FUN (proj1_sig P') (proj2_sig P').

  Lemma funbi_sig_equiv:
    ∀ P Q, P ≡ Q ↔ funbi_sig P ≡ funbi_sig Q.
  Proof. done. Qed.

  Lemma funbi_sig_dist:
    ∀ n, ∀ P Q : funbi_ty I B, P ≡{n}≡ Q ↔ funbi_sig P ≡{n}≡ funbi_sig Q.
  Proof. done. Qed.

  Definition funbi_ofe_mixin : OfeMixin (funbi_ty I B).
  Proof. by apply (iso_ofe_mixin funbi_sig funbi_sig_equiv funbi_sig_dist). Qed.

  Canonical Structure funbi_ofe := OfeT (funbi_ty I B) (funbi_ofe_mixin).

  Instance funbi_cofe
  {C : Cofe B}
  {limit_preserving_entails :
     ∀ cP cQ : chain B, (∀ n, cP n ⊢ cQ n) → compl cP ⊢ compl cQ}
    : Cofe (funbi_ofe).
  Proof.
    unshelve refine (iso_cofe_subtype (A:=I-c>B)
                                      (fun f => mono (bi_index_rel I) f)
                                      (@FUN _ _)
                                      (@funbi_car _ _) _ _ _);
    [done|done|].
    intros c i j Hij.
    apply limit_preserving_entails.
    intros. by apply funbi_mono.
  Qed.
End Ofe_Cofe.


Inductive funbi_entails {I B} (P1 P2 : funbi_ty I B) : Prop := funbi_in_entails : (∀ i, bi_entails (funbi_car P1 i) (funbi_car P2 i)) → funbi_entails P1 P2.
Lemma funbi_entails_eq {I B} P1 P2 : @funbi_entails I B P1 P2 ↔ (∀ i, bi_entails (funbi_car P1 i) (funbi_car P2 i)).
Proof. split=>[[]//|//]. Qed.

Hint Immediate funbi_in_entails.

Program Definition funbi_pure_def {I B} : Prop → funbi_ty I B := λ P, FUN (λ _, bi_pure P) _.
Definition funbi_pure_aux : seal (@funbi_pure_def). by eexists. Qed.
Definition funbi_pure {I B} := unseal (@funbi_pure_aux) I B.
Definition funbi_pure_eq : @funbi_pure = _ := seal_eq _.

Program Definition funbi_emp {I B} := @FUN I B (λ _, emp)%I _.


Program Definition funbi_and_def {I B} := λ (P Q : funbi_ty I B), @FUN I B (λ i, funbi_car P i ∧ funbi_car Q i)%I _.
Next Obligation.
  intros I B P Q V1 V2 HV.
  by apply bi.and_mono; apply funbi_mono.
Qed.
Definition funbi_and_aux : seal (@funbi_and_def). by eexists. Qed.
Definition funbi_and {I B} := unseal (@funbi_and_aux) I B.
Definition funbi_and_eq : @funbi_and = _ := seal_eq _.

Program Definition funbi_or_def {I B} := λ (P Q : funbi_ty I B), @FUN I B (λ i, funbi_car P i ∨ funbi_car Q i)%I _.
Next Obligation.
  intros I B P Q V1 V2 HV.
  by apply bi.or_mono; apply funbi_mono.
Qed.
Definition funbi_or_aux : seal (@funbi_or_def). by eexists. Qed.
Definition funbi_or {I B} := unseal (@funbi_or_aux) I B.
Definition funbi_or_eq : @funbi_or = _ := seal_eq _.

Program Definition funbi_impl_def {I B} := λ (P Q : funbi_ty I B), funbi_upclosed I B (λ i, funbi_car P i → funbi_car Q i)%I.
Definition funbi_impl_aux : seal (@funbi_impl_def). by eexists. Qed.
Definition funbi_impl {I B} := unseal (@funbi_impl_aux) I B.
Definition funbi_impl_eq : @funbi_impl = _ := seal_eq _.

Program Definition funbi_forall_def {I B} A := λ (Φ : A -> funbi_ty I B), @FUN I B (λ i, ∀ x : A, funbi_car (Φ x) i)%I _.
Next Obligation.
  intros I B P Q V1 V2 HV.
  by apply bi.forall_mono; intros; apply funbi_mono.
Qed.
Definition funbi_forall_aux : seal (@funbi_forall_def). by eexists. Qed.
Definition funbi_forall {I B} := unseal (@funbi_forall_aux) I B.
Definition funbi_forall_eq : @funbi_forall = _ := seal_eq _.

Program Definition funbi_exist_def {I B} A := λ (Φ : A -> funbi_ty I B), FUN (λ i, ∃ x : A, funbi_car (Φ x) i)%I _.
Next Obligation.
  intros I B P Q V1 V2 HV.
  by apply bi.exist_mono; intros; apply funbi_mono.
Qed.
Definition funbi_exist_aux : seal (@funbi_exist_def). by eexists. Qed.
Definition funbi_exist {I B} := unseal (@funbi_exist_aux) I B.
Definition funbi_exist_eq : @funbi_exist = _ := seal_eq _.

Definition funbi_internal_eq_def {I B} A := λ a b, @FUN I B (λ _, @bi_internal_eq B A a b) _.
Definition funbi_internal_eq_aux : seal (@funbi_internal_eq_def). by eexists. Qed.
Definition funbi_internal_eq {I B} := unseal (@funbi_internal_eq_aux) I B.
Definition funbi_internal_eq_eq : @funbi_internal_eq = _ := seal_eq _.

Program Definition funbi_sep_def {I B} := λ (P Q : funbi_ty I B), FUN (λ i, funbi_car P i ∗ funbi_car Q i)%I _.
Next Obligation.
  intros I B P Q V1 V2 HV.
  by apply bi.sep_mono; intros; apply funbi_mono.
Qed.
Definition funbi_sep_aux : seal (@funbi_sep_def). by eexists. Qed.
Definition funbi_sep {I B} := unseal funbi_sep_aux I B.
Definition funbi_sep_eq : @funbi_sep = _ := seal_eq _.

Program Definition funbi_wand_def {I B} := λ (P Q : funbi_ty I B), funbi_upclosed I B (λ i, funbi_car P i -∗ funbi_car Q i)%I.
Definition funbi_wand_aux : seal (@funbi_wand_def). by eexists. Qed.
Definition funbi_wand {I B} := unseal funbi_wand_aux I B.
Definition funbi_wand_eq : @funbi_wand = _ := seal_eq _.

Program Definition funbi_persistently_def {I B} : funbi_ty I B → funbi_ty I B := λ P, FUN (λ i, bi_persistently (funbi_car P i)) _.
Next Obligation.
  intros I B P V1 V2 HV.
  by apply bi.persistently_mono; intros; apply funbi_mono.
Qed.
Definition funbi_persistently_aux : seal (@funbi_persistently_def). by eexists. Qed.
Definition funbi_persistently {I B} := unseal funbi_persistently_aux I B.
Definition funbi_persistently_eq : @funbi_persistently = _ := seal_eq _.

Program Definition funbi_plainly_def {I B} : funbi_ty I B → funbi_ty I B := λ P, FUN (λ i, bi_plainly (funbi_car P i)) _.
Next Obligation.
  intros I B P V1 V2 HV.
  by apply bi.plainly_mono; intros; apply funbi_mono.
Qed.
Definition funbi_plainly_aux : seal (@funbi_plainly_def). by eexists. Qed.
Definition funbi_plainly {I B} := unseal funbi_plainly_aux I B.
Definition funbi_plainly_eq : @funbi_plainly = _ := seal_eq _.

Program Definition funbi_later_def {I} {B : sbi} (P : funbi_ty I B) : funbi_ty I B := FUN (λ i, ▷ (funbi_car P i))%I _.
Next Obligation.
  intros I B P V1 V2 HV.
  by apply bi.later_mono; intros; apply funbi_mono.
Qed.
Definition funbi_later_aux : seal (@funbi_later_def). by eexists. Qed.
Definition funbi_later {I B} := unseal funbi_later_aux I B.
Definition funbi_later_eq : @funbi_later = _ := seal_eq _.


Program Definition funbi_in_def {I B} (i_0 : bi_index_type I) : funbi_ty I B := FUN (λ i : I, ⌜i_0 ⊑ i⌝%I) _.
Next Obligation.
  intros I B V V1 V2 HV.
  by apply bi.pure_mono; intros; etrans.
Qed.
Definition funbi_in_aux : seal (@funbi_in_def). by eexists. Qed.
Definition funbi_in {I B} := unseal (@funbi_in_aux) I B.
Definition funbi_in_eq : @funbi_in = _ := seal_eq _.

Lemma funbi_all_def_mono {I B} (P : funbi_ty I B) : mono (⊑) (λ _ : I, ∀ i, funbi_car P i)%I.
Proof. apply _. Qed.
Program Definition funbi_all_def {I B} := λ (P : funbi_ty I B), FUN (λ _ : I, ∀ i, funbi_car P i)%I (funbi_all_def_mono P).
Definition funbi_all_aux : seal (@funbi_all_def). by eexists. Qed.
Definition funbi_all {I B} := unseal (@funbi_all_aux) I B.
Definition funbi_all_eq : @funbi_all = _ := seal_eq _.


Program Definition funbi_ipure_def {I B} P : funbi_ty I B := FUN (λ _, P) _.
Definition funbi_ipure_aux : seal (@funbi_ipure_def). by eexists. Qed.
Definition funbi_ipure {I B} := unseal funbi_ipure_aux I B.
Definition funbi_ipure_eq : @funbi_ipure = _ := seal_eq _.

Local Definition unseal_eqs :=
  (@funbi_pure_eq, @funbi_and_eq, @funbi_or_eq, @funbi_impl_eq, @funbi_forall_eq,
   @funbi_exist_eq, @funbi_internal_eq_eq, @funbi_sep_eq, @funbi_wand_eq, @funbi_persistently_eq,
   @funbi_plainly_eq,
   @funbi_entails_eq, @funbi_later_eq, @funbi_in_eq, @funbi_all_eq, @funbi_ipure_eq 
  ).

Lemma funbi_mixin I B :
  BiMixin  (@funbi_ofe_mixin I B) funbi_entails funbi_emp funbi_pure funbi_and funbi_or funbi_impl funbi_forall funbi_exist funbi_internal_eq funbi_sep funbi_wand funbi_plainly funbi_persistently.
Proof.
  rewrite !unseal_eqs.
  split;
  (* repeat setoid_rewrite funbi_entails_eq; repeat intro. *)
  repeat (match goal with | [|- funbi_entails _ _ -> _] => intros [] end
          || intro
         );
  try match goal with | [ |- funbi_entails _ _] => split => ? end.
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
    rewrite -H funbi_mono //.
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
    erewrite (bi.internal_eq_rewrite _ _ (λ c, funbi_car (Ψ c) _)) => //.
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
    rewrite (funbi_mono _ _ _ M). by apply H.
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


Canonical Structure funbi I B : bi :=
  Bi (funbi_ty I B) funbi_dist funbi_equiv funbi_entails funbi_emp funbi_pure funbi_and funbi_or funbi_impl funbi_forall funbi_exist funbi_internal_eq funbi_sep funbi_wand funbi_plainly funbi_persistently funbi_ofe_mixin (funbi_mixin _ _).

Instance funbi_affine I B : BiAffine B → BiAffine (funbi I B).
Proof. split => ?. by apply affine. Qed.

Arguments funbi_ofe _ _ : clear implicits.
Arguments funbi _ _ : clear implicits.

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

Lemma funbi_wand_force I B (P Q : funbi I B) i:
  funbi_car (P -∗ Q) i -∗ (funbi_car P i -∗ funbi_car Q i).
Proof. Prelim.unseal. by rewrite !bi.forall_elim. Qed.

Lemma funbi_impl_force I B (P Q : funbi I B) i:
  funbi_car (P → Q) i -∗ (funbi_car P i → funbi_car Q i).
Proof. Prelim.unseal. by rewrite !bi.forall_elim. Qed.

Lemma funbi_persistently_if_eq I B p (P : funbi I B) i:
  funbi_car (bi_persistently_if p P) i = bi_persistently_if p (funbi_car P i).
Proof. rewrite /bi_persistently_if. Prelim.unseal. by destruct p. Qed.

Lemma funbi_plainly_if_eq I B p (P : funbi I B) i:
  funbi_car (bi_plainly_if p P) i = bi_plainly_if p (funbi_car P i).
Proof. rewrite /bi_plainly_if. Prelim.unseal. by destruct p. Qed.

Lemma funbi_affinely_if_eq I B p (P : funbi I B) i:
  funbi_car (bi_affinely_if p P) i = bi_affinely_if p (funbi_car P i).
Proof. rewrite /bi_affinely_if. destruct p => //. rewrite /bi_affinely. by Prelim.unseal. Qed.

Lemma funsbi_mixin I (B : sbi) :
    SbiMixin (PROP:=funbi I B) funbi_entails funbi_pure funbi_or funbi_impl funbi_forall funbi_exist funbi_internal_eq funbi_sep funbi_plainly funbi_persistently funbi_later.
Proof.
  intros.
  Prelim.unseal.
  split; repeat setoid_rewrite funbi_entails_eq; repeat intro.
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
    intros. by rewrite funbi_mono.
Qed.
Canonical Structure funsbi I (B : sbi) : sbi :=
    Sbi (funbi_ty I B) funbi_dist funbi_equiv funbi_entails funbi_emp funbi_pure funbi_and funbi_or funbi_impl funbi_forall funbi_exist funbi_internal_eq funbi_sep funbi_wand funbi_plainly funbi_persistently funbi_later funbi_ofe_mixin (bi_bi_mixin _) (funsbi_mixin _ _).

Ltac unseal := rewrite 
                 /(@sbi_except_0 (funsbi _ _))
                 /(@bi_emp (funbi _ _)) /=
                 /(@bi_pure (funbi _ _))
                 /(@bi_and (funbi _ _))
                 /(@bi_or (funbi _ _))
                 /(@bi_impl (funbi _ _))
                 /(@bi_forall (funbi _ _))
                 /(@bi_exist (funbi _ _))
                 /(@bi_internal_eq (funbi _ _))
                 /(@bi_sep (funbi _ _))
                 /(@bi_wand (funbi _ _))
                 /(@bi_persistently (funbi _ _))
                 /(@sbi_later (funsbi _ _)) /=
                 /(@sbi_emp (funsbi _ _))
                 /(@sbi_pure (funsbi _ _))
                 /(@sbi_and (funsbi _ _))
                 /(@sbi_or (funsbi _ _))
                 /(@sbi_impl (funsbi _ _))
                 /(@sbi_forall (funsbi _ _))
                 /(@sbi_exist (funsbi _ _))
                 /(@sbi_internal_eq (funsbi _ _))
                 /(@sbi_sep (funsbi _ _))
                 /(@sbi_wand (funsbi _ _))
                 /(@sbi_persistently (funsbi _ _))
                 /=
                 !unseal_eqs /=.


Section ProofmodeInstances.
  Global Instance funbi_car_persistent B I P i : Persistent P → Persistent (@funbi_car B I P i).
  Proof. move => [] /(_ i). by unseal. Qed.

  Global Instance funbi_in_persistent {I B} V : Persistent (@funbi_in I B V).
  Proof.
    unfold Persistent.
    unseal; split => ?.
      by apply bi.pure_persistent.
  Qed. (* TODO: why is this so long and why can I not rewrite funbi_persistently after move? *)
End ProofmodeInstances.

Global Instance funbi_ipure_timeless {I B} (P : sbi_car B) :
  Timeless (P) → Timeless (@funbi_ipure I B P).
Proof.
  intros. split => ? /=.
  unseal. rewrite /funbi_ipure_def. exact: H.
Qed.

Global Instance funbi_ipure_persistent {I B} (P : sbi_car B) :
  Persistent (P) → Persistent (@funbi_ipure I B P).
Proof.
  intros. split => ? /=.
  unseal. rewrite /funbi_ipure_def. exact: H.
Qed.
