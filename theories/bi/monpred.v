From iris.bi Require Import derived_laws.

(** Definitions. *)

Structure bi_index :=
  BiIndex
    { bi_index_type :> Type;
      bi_index_rel : SqSubsetEq bi_index_type;
      bi_index_rel_preorder : PreOrder (⊑) }.

Existing Instances bi_index_rel bi_index_rel_preorder.

Record monPred (I : bi_index) (B : bi) :=
  FUN
    { monPred_car :> I -> B;
      monPred_mono :> Proper ((⊑) ==> (⊢)) monPred_car }.
Local Existing Instance monPred_mono.

Arguments FUN {_ _} _ _.
Arguments monPred_car {_ _} _ _.
Arguments monPred_mono {_ _} _ _ _ _ .

(** Ofe + Cofe instances  *)

Section Ofe_Cofe.
  Context {I : bi_index} {B : bi}.
  Implicit Types i : I.
  Implicit Types P Q : monPred I B.

  Inductive monPred_equiv' (P Q : monPred I B) : Prop :=
    { monPred_in_equiv i : P i ≡ Q i } .
  Instance monPred_equiv : Equiv (monPred I B) := monPred_equiv'.
  Inductive monPred_dist' (n : nat) (P Q : monPred I B) : Prop :=
    { monPred_in_dist i : P i ≡{n}≡ Q i }.
  Instance monPred_dist : Dist (monPred I B) := monPred_dist'.

  Definition monPred_sig P : { f : I -c> B | Proper ((⊑) ==> (⊢)) f } :=
    exist _ (monPred_car P) (monPred_mono P).

  Definition sig_monPred (P' : { f : I -c> B | Proper ((⊑) ==> (⊢)) f })
    : monPred I B :=
    FUN (proj1_sig P') (proj2_sig P').

  (* These two lemma use the wrong Equiv and Dist instance for
    monPred. so we make sure they are not accessible outside of the
    section by using Let. *)
  Let monPred_sig_equiv:
    ∀ P Q, P ≡ Q ↔ monPred_sig P ≡ monPred_sig Q.
  Proof. by split; [intros []|]. Qed.
  Let monPred_sig_dist:
    ∀ n, ∀ P Q : monPred I B, P ≡{n}≡ Q ↔ monPred_sig P ≡{n}≡ monPred_sig Q.
  Proof. by split; [intros []|]. Qed.

  Definition monPred_ofe_mixin : OfeMixin (monPred I B).
  Proof. by apply (iso_ofe_mixin monPred_sig monPred_sig_equiv monPred_sig_dist). Qed.

  Canonical Structure monPred_ofe := OfeT (monPred I B) (monPred_ofe_mixin).

  Global Instance monPred_cofe {C : Cofe B} : Cofe (monPred_ofe).
  Proof.
    unshelve refine (iso_cofe_subtype (A:=I-c>B) _ (@FUN _ _) (@monPred_car _ _) _ _ _);
    [apply _|by apply monPred_sig_dist|done|].
    intros c i j Hij. apply @limit_preserving;
      [by apply bi.limit_preserving_entails; intros ??|]=>n. by rewrite Hij.
  Qed.
End Ofe_Cofe.

Arguments monPred_ofe _ _ : clear implicits.

Section Iso.
  Context {I : bi_index} {B : bi}.
  Implicit Types i : I.
  Implicit Types P Q : monPred I B.

  Lemma monPred_sig_monPred (P' : { f : I -c> B | Proper ((⊑) ==> (⊢)) f }) :
    monPred_sig (sig_monPred P') ≡ P'.
  Proof. by change (P' ≡ P'). Qed.
  Lemma sig_monPred_sig P : sig_monPred (monPred_sig P) ≡ P.
  Proof. done. Qed.

  Global Instance monPred_sig_ne : NonExpansive (@monPred_sig I B).
  Proof. move=> ??? [?] ? //=. Qed.
  Global Instance monPred_sig_proper : Proper ((≡) ==> (≡)) (@monPred_sig I B).
  Proof. eapply (ne_proper _). Qed.
  Global Instance sig_monPred_ne : NonExpansive (@sig_monPred I B).
  Proof. split=>? //=. Qed.
  Global Instance sig_monPred_proper : Proper ((≡) ==> (≡)) (@sig_monPred I B).
  Proof. eapply (ne_proper _). Qed.
End Iso.

(* We generalize over the relation R which is morally the equivalence
   relation over B. That way, the BI index can use equality as an
   equivalence relation (and Coq is able to infer the Proper and
   Reflexive instances properly), or any other equivalence relation,
   provided it is compatible with (⊑). *)
Instance monPred_car_ne {I : bi_index} {B} (R : relation I) :
  Proper (R ==> R ==> iff) (⊑) → Reflexive R →
  ∀ n, Proper (dist n ==> R ==> dist n) (@monPred_car I B).
Proof.
  intros ????? [Hd] ?? HR. rewrite Hd.
  apply equiv_dist, bi.equiv_spec; split; f_equiv; rewrite ->HR; done.
Qed.
Instance monPred_car_proper {I : bi_index} {B} (R : relation I) :
  Proper (R ==> R ==> iff) (⊑) → Reflexive R →
  Proper ((≡) ==> R ==> (≡)) (@monPred_car I B).
Proof. repeat intro. apply equiv_dist=>?. f_equiv=>//. by apply equiv_dist. Qed.

(** BI and SBI structures. *)

Inductive monPred_entails {I B} (P1 P2 : monPred I B) : Prop :=
  { monPred_in_entails i : P1 i ⊢ P2 i }.
Hint Immediate monPred_in_entails.

Instance monPred_upclose_mono I (B : bi) (P : bi_index_type I → B) :
  Proper ((⊑) ==> (⊢)) (λ i, (∀ j, ⌜i ⊑ j⌝ → P j)%I).
Proof. solve_proper. Qed.

Definition monPred_upclosed {I B} P :=
  FUN _ (monPred_upclose_mono I B P%function).

Definition monPred_ipure_def {I} {B : bi} (P : B) : monPred I B := FUN (λ _, P) _.
Definition monPred_ipure_aux : seal (@monPred_ipure_def). by eexists. Qed.
Definition monPred_ipure {I B} := unseal monPred_ipure_aux I B.
Definition monPred_ipure_eq : @monPred_ipure = _ := seal_eq _.

Definition monPred_pure {I B} (P : Prop) : monPred I B :=
  monPred_ipure (bi_pure P).
Definition monPred_emp {I B} : monPred I B :=
  monPred_ipure emp%I.

Program Definition monPred_and_def {I B} (P Q : monPred I B) : monPred I B :=
  FUN (λ i, P i ∧ Q i)%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_and_aux : seal (@monPred_and_def). by eexists. Qed.
Definition monPred_and {I B} := unseal (@monPred_and_aux) I B.
Definition monPred_and_eq : @monPred_and = _ := seal_eq _.

Program Definition monPred_or_def {I B} (P Q : monPred I B) : monPred I B :=
  FUN (λ i, P i ∨ Q i)%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_or_aux : seal (@monPred_or_def). by eexists. Qed.
Definition monPred_or {I B} := unseal (@monPred_or_aux) I B.
Definition monPred_or_eq : @monPred_or = _ := seal_eq _.

Definition monPred_impl_def {I B} (P Q : monPred I B) : monPred I B :=
  monPred_upclosed (λ i, P i → Q i)%I.
Definition monPred_impl_aux : seal (@monPred_impl_def). by eexists. Qed.
Definition monPred_impl {I B} := unseal (@monPred_impl_aux) I B.
Definition monPred_impl_eq : @monPred_impl = _ := seal_eq _.

Program Definition monPred_forall_def {I B} A (Φ : A → monPred I B) : monPred I B :=
  FUN (λ i, ∀ x : A, Φ x i)%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_forall_aux : seal (@monPred_forall_def). by eexists. Qed.
Definition monPred_forall {I B} := unseal (@monPred_forall_aux) I B.
Definition monPred_forall_eq : @monPred_forall = _ := seal_eq _.

Program Definition monPred_exist_def {I B} A (Φ : A → monPred I B) : monPred I B :=
  FUN (λ i, ∃ x : A, Φ x i)%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_exist_aux : seal (@monPred_exist_def). by eexists. Qed.
Definition monPred_exist {I B} := unseal (@monPred_exist_aux) I B.
Definition monPred_exist_eq : @monPred_exist = _ := seal_eq _.

Definition monPred_internal_eq_def {I B} (A : ofeT) (a b : A) : monPred I B :=
  FUN (λ _, bi_internal_eq a b) _.
Definition monPred_internal_eq_aux : seal (@monPred_internal_eq_def). by eexists. Qed.
Definition monPred_internal_eq {I B} := unseal (@monPred_internal_eq_aux) I B.
Definition monPred_internal_eq_eq : @monPred_internal_eq = _ := seal_eq _.

Program Definition monPred_sep_def {I B} (P Q : monPred I B) : monPred I B :=
  FUN (λ i, P i ∗ Q i)%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_sep_aux : seal (@monPred_sep_def). by eexists. Qed.
Definition monPred_sep {I B} := unseal monPred_sep_aux I B.
Definition monPred_sep_eq : @monPred_sep = _ := seal_eq _.

Definition monPred_wand_def {I B} (P Q : monPred I B) : monPred I B :=
  monPred_upclosed (λ i, P i -∗ Q i)%I.
Definition monPred_wand_aux : seal (@monPred_wand_def). by eexists. Qed.
Definition monPred_wand {I B} := unseal monPred_wand_aux I B.
Definition monPred_wand_eq : @monPred_wand = _ := seal_eq _.

Program Definition monPred_persistently_def {I B} (P : monPred I B) : monPred I B := 
  FUN (λ i, bi_persistently (P i)) _.
Next Obligation. solve_proper. Qed.
Definition monPred_persistently_aux : seal (@monPred_persistently_def). by eexists. Qed.
Definition monPred_persistently {I B} := unseal monPred_persistently_aux I B.
Definition monPred_persistently_eq : @monPred_persistently = _ := seal_eq _.

Definition monPred_plainly {I B} (P : monPred I B) : monPred I B :=
  monPred_ipure (∀ i, bi_plainly (P i))%I.

Program Definition monPred_later_def {I} {B : sbi} (P : monPred I B) : monPred I B :=
  FUN (λ i, ▷ (P i))%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_later_aux : seal (@monPred_later_def). by eexists. Qed.
Definition monPred_later {I B} := unseal monPred_later_aux I B.
Definition monPred_later_eq : @monPred_later = _ := seal_eq _.

Program Definition monPred_in_def {I : bi_index} {B} (i_0 : I) : monPred I B :=
  FUN (λ i : I, ⌜i_0 ⊑ i⌝%I) _.
Next Obligation. solve_proper. Qed.
Definition monPred_in_aux : seal (@monPred_in_def). by eexists. Qed.
Definition monPred_in {I B} := unseal (@monPred_in_aux) I B.
Definition monPred_in_eq : @monPred_in = _ := seal_eq _.

Definition monPred_all_def {I B} (P : monPred I B) : monPred I B :=
  FUN (λ _ : I, ∀ i, P i)%I _.
Definition monPred_all_aux : seal (@monPred_all_def). by eexists. Qed.
Definition monPred_all {I B} := unseal (@monPred_all_aux) I B.
Definition monPred_all_eq : @monPred_all = _ := seal_eq _.

Definition unseal_eqs :=
  (@monPred_and_eq, @monPred_or_eq, @monPred_impl_eq,
   @monPred_forall_eq, @monPred_exist_eq, @monPred_internal_eq_eq,
   @monPred_sep_eq, @monPred_wand_eq,
   @monPred_persistently_eq, @monPred_later_eq,
   @monPred_in_eq, @monPred_all_eq, @monPred_ipure_eq).
Ltac unseal :=
  unfold bi_affinely, bi_absorbingly, sbi_except_0, bi_pure, bi_emp,
         monPred_upclosed, bi_and, bi_or, bi_impl, bi_forall, bi_exist,
         bi_internal_eq, bi_sep, bi_wand, bi_persistently, bi_affinely,
         sbi_later; simpl;
  unfold sbi_emp, sbi_pure, sbi_and, sbi_or, sbi_impl, sbi_forall, sbi_exist,
         sbi_internal_eq, sbi_sep, sbi_wand, sbi_persistently, sbi_plainly,
         bi_plainly; simpl;
  unfold monPred_pure, monPred_emp, monPred_plainly; simpl;
  rewrite !unseal_eqs /=.

Lemma monPred_bi_mixin I B : BiMixin (@monPred_ofe_mixin I B)
  monPred_entails monPred_emp monPred_pure monPred_and monPred_or
  monPred_impl monPred_forall monPred_exist monPred_internal_eq
  monPred_sep monPred_wand monPred_plainly monPred_persistently.
Proof.
  split; try unseal;
    repeat match goal with
        | _ => intro || done
        | [ H : monPred_entails _ _ |- _] => destruct H as [H]
        | [ |- monPred_entails _ _ ] => split => ? /=
        | [ |- @dist _ monPred_dist _ _ _ ] => split => ? /=
        | [ |- ?f _ ≡{_}≡ ?f _ ] => f_equiv
        | [ |- ?f _ _ ≡{_}≡ ?f _ _ ] => f_equiv
        end.
  - split.
    + intros ?. by split.
    + intros ? ? ? [e1] [e2]. split => ?. by rewrite e1 e2.
  - split.
    + intros [HPQ]. split; split => i; move: (HPQ i); by apply bi.equiv_spec.
    + intros [[] []]. split=>i. by apply bi.equiv_spec.
  - by apply bi.pure_intro.
  - apply bi.pure_elim'. move/H => [] //=.
  - by apply bi.pure_forall_2.
  - by apply bi.and_elim_l.
  - by apply bi.and_elim_r.
  - by apply bi.and_intro.
  - by apply bi.or_intro_l.
  - by apply bi.or_intro_r.
  - by apply bi.or_elim.
  - setoid_rewrite bi.pure_impl_forall. do 2 apply bi.forall_intro => ?.
    apply bi.impl_intro_r. rewrite -H /=. by do 2 f_equiv.
  - rewrite H /=. rewrite bi.forall_elim bi.pure_impl_forall bi.forall_elim //.
    apply bi.impl_elim_l.
  - apply bi.forall_intro => ?. by apply H.
  - by apply: bi.forall_elim.
  - by rewrite /= -bi.exist_intro.
  - apply bi.exist_elim => ?. by apply H.
  - by apply bi.internal_eq_refl.
  - setoid_rewrite bi.pure_impl_forall. do 2 apply bi.forall_intro => ?.
    erewrite (bi.internal_eq_rewrite _ _ (flip Ψ _)) => //=. solve_proper.
  - by apply bi.fun_ext.
  - by apply bi.sig_eq.
  - by apply bi.discrete_eq_1.
  - by apply bi.sep_mono.
  - by apply bi.emp_sep_1.
  - by apply bi.emp_sep_2.
  - by apply bi.sep_comm'.
  - by apply bi.sep_assoc'.
  - setoid_rewrite bi.pure_impl_forall. do 2 apply bi.forall_intro => ?.
    apply bi.wand_intro_r. rewrite -H /=. by do 2 f_equiv.
  - apply bi.wand_elim_l'.
    rewrite H /= bi.forall_elim bi.pure_impl_forall bi.forall_elim //.
  - by do 3 f_equiv.
  - by rewrite bi.forall_elim bi.plainly_elim_persistently.
  - repeat setoid_rewrite <-bi.plainly_forall.
    rewrite -bi.plainly_idemp_2. f_equiv. by apply bi.forall_intro=>_.
  - apply bi.forall_intro=>?. rewrite bi.plainly_forall. apply bi.forall_intro=>?.
    by rewrite !bi.forall_elim.
  - rewrite <-(sig_monPred_sig P), <-(sig_monPred_sig Q), <-(bi.f_equiv _).
    rewrite -bi.sig_equivI /= -bi.fun_ext. f_equiv=>i.
    rewrite -bi.prop_ext !(bi.forall_elim i) !bi.pure_impl_forall
            !bi.forall_elim //.
  - repeat setoid_rewrite bi.pure_impl_forall.
    repeat setoid_rewrite <-bi.plainly_forall.
    repeat setoid_rewrite bi.persistently_forall. do 4 f_equiv.
    apply bi.persistently_impl_plainly.
  - repeat setoid_rewrite bi.pure_impl_forall. rewrite 2!bi.forall_elim //.
    repeat setoid_rewrite <-bi.plainly_forall.
    setoid_rewrite bi.plainly_impl_plainly. f_equiv.
    do 3 apply bi.forall_intro => ?. f_equiv. rewrite bi.forall_elim //.
  - apply bi.forall_intro=>_. by apply bi.plainly_emp_intro.
  - apply bi.sep_elim_l, _.
  - by f_equiv.
  - by apply bi.persistently_idemp_2.
  - by setoid_rewrite bi.plainly_persistently_1.
  - by apply bi.persistently_forall_2.
  - by apply bi.persistently_exist_1.
  - apply bi.sep_elim_l, _.
  - by apply bi.persistently_and_sep_elim.
Qed.

Canonical Structure monPredI I B : bi :=
  Bi (monPred I B) monPred_dist monPred_equiv monPred_entails monPred_emp
     monPred_pure monPred_and monPred_or monPred_impl monPred_forall
     monPred_exist monPred_internal_eq monPred_sep monPred_wand monPred_plainly
     monPred_persistently monPred_ofe_mixin (monPred_bi_mixin _ _).

Lemma monPred_sbi_mixin I (B : sbi) :
  SbiMixin (PROP:=monPred I B) monPred_entails monPred_pure monPred_or
           monPred_impl monPred_forall monPred_exist monPred_internal_eq
           monPred_sep monPred_plainly monPred_persistently monPred_later.
Proof.
  intros. split; try unseal;
    repeat match goal with
           | _ => intro || done
           | [ H : monPred_entails _ _ |- _] => destruct H as [H]
           | [ |- monPred_entails _ _ ] => split => ? /=
           | [ |- @dist _ _ _ _ _ ] => split => ? /=
           end.
  - apply bi.later_contractive. rewrite /dist_later in H. destruct n => //. by apply H.
  - by apply bi.later_eq_1.
  - by apply bi.later_eq_2.
  - by apply bi.later_mono.
  - setoid_rewrite bi.pure_impl_forall. rewrite /= !bi.forall_elim //. by apply bi.löb.
  - by apply bi.later_forall_2.
  - by apply bi.later_exist_false.
  - by apply bi.later_sep_1.
  - by apply bi.later_sep_2.
  - rewrite bi.later_forall. f_equiv=>?. by rewrite -bi.later_plainly_1.
  - rewrite bi.later_forall. f_equiv=>?. by rewrite -bi.later_plainly_2.
  - by apply bi.later_persistently_1.
  - by apply bi.later_persistently_2.
  - rewrite /= -bi.forall_intro. apply bi.later_false_em.
    intros. rewrite bi.pure_impl_forall. apply bi.forall_intro=>?. by repeat f_equiv.
Qed.

Canonical Structure monPredSI I (B : sbi) : sbi :=
  Sbi (monPred I B) monPred_dist monPred_equiv monPred_entails monPred_emp
      monPred_pure monPred_and monPred_or monPred_impl monPred_forall
      monPred_exist monPred_internal_eq monPred_sep monPred_wand monPred_plainly
      monPred_persistently monPred_later monPred_ofe_mixin
      (bi_bi_mixin _) (monPred_sbi_mixin _ _).

(** Primitive facts that cannot be deduced from the BI structure. *)

Instance monPred_car_mono {I B} : Proper ((⊢) ==> (⊑) ==> (⊢)) (@monPred_car I B).
Proof. by move=> ?? [?] ?? ->. Qed.
Instance monPred_car_mono_flip {I B} :
  Proper (flip (⊢) ==> flip (⊑) ==> flip (⊢)) (@monPred_car I B).
Proof. solve_proper. Qed.

Instance monPred_ipure_ne {I B} : NonExpansive (@monPred_ipure I B).
Proof. unseal. by split. Qed.
Instance monPred_ipure_proper {I B} : Proper ((≡) ==> (≡)) (@monPred_ipure I B).
Proof. apply (ne_proper _). Qed.
Instance monPred_ipure_mono {I B} : Proper ((⊢) ==> (⊢)) (@monPred_ipure I B).
Proof. unseal. by split. Qed.
Instance monPred_ipure_mono_flip {I B} :
  Proper (flip (⊢) ==> flip (⊢)) (@monPred_ipure I B).
Proof. solve_proper. Qed.

Instance monPred_in_proper {I : bi_index} {B} (R : relation I) :
  Proper (R ==> R ==> iff) (⊑) → Reflexive R →
  Proper (R ==> (≡)) (@monPred_in I B).
Proof. unseal. split. solve_proper. Qed.
Instance monPred_in_mono {I : bi_index} {B} :
  Proper (flip (⊑) ==> (⊢)) (@monPred_in I B).
Proof. unseal. split. solve_proper. Qed.
Instance monPred_in_mono_flip {I : bi_index} {B} :
  Proper ((⊑) ==> flip (⊢)) (@monPred_in I B).
Proof. solve_proper. Qed.

Instance monPred_all_ne {I B} : NonExpansive (@monPred_all I B).
Proof. unseal. split. solve_proper. Qed.
Instance monPred_all_proper {I B} : Proper ((≡) ==> (≡)) (@monPred_all I B).
Proof. apply (ne_proper _). Qed.
Instance monPred_all_mono {I B} : Proper ((⊢) ==> (⊢)) (@monPred_all I B).
Proof. unseal. split. solve_proper. Qed.
Instance monPred_all_mono_flip {I B} :
  Proper (flip (⊢) ==> flip (⊢)) (@monPred_all I B).
Proof. solve_proper. Qed.

Instance monPred_affine I B : BiAffine B → BiAffine (monPredI I B).
Proof. split => ?. unseal. by apply affine. Qed.

Lemma monPred_wand_force I B (P Q : monPred I B) i:
  (P -∗ Q) i -∗ (P i -∗ Q i).
Proof. unseal. rewrite bi.forall_elim bi.pure_impl_forall bi.forall_elim //. Qed.

Lemma monPred_impl_force I B (P Q : monPred I B) i:
  (P → Q) i -∗ (P i → Q i).
Proof. unseal. rewrite bi.forall_elim bi.pure_impl_forall bi.forall_elim //. Qed.

Lemma monPred_persistently_if_eq I B p (P : monPred I B) i:
  (bi_persistently_if p P) i = bi_persistently_if p (P i).
Proof. rewrite /bi_persistently_if. unseal. by destruct p. Qed.

Lemma monPred_affinely_if_eq I B p (P : monPred I B) i:
  (bi_affinely_if p P) i = bi_affinely_if p (P i).
Proof. rewrite /bi_affinely_if. destruct p => //. rewrite /bi_affinely. by unseal. Qed.

(* TODO : if we use this for linear BIs, we should additionally define
   Absorbing and Affine instances. *)

Global Instance monPred_car_timeless {I B} (P : monPred I (sbi_bi B)) i :
  Timeless P → Timeless (P i).
Proof. move => [] /(_ i). unfold Timeless. by unseal. Qed.
Global Instance monPred_car_persistent {I B} (P : monPred I B) i :
  Persistent P → Persistent (P i).
Proof. move => [] /(_ i). by unseal. Qed.
Global Instance monPred_car_plain I B (P : monPred I B) i :
  Plain P → Plain (P i).
Proof. move => [] /(_ i). unfold Plain. unseal. rewrite bi.forall_elim //. Qed.

(* Notation "☐ P" := (monPred_ipure P%I) *)
(*   (at level 20, right associativity) : bi_scope. *)

Global Instance monPred_ipure_timeless {I B} (P : sbi_car B) :
  Timeless P → Timeless (@monPred_ipure I B P).
Proof. intros. split => ? /=. unseal. exact: H. Qed.
Global Instance monPred_ipure_plain {I B} P :
  Plain P → Plain (@monPred_ipure I B P).
Proof. intros. split => ? /=. unseal. apply bi.forall_intro=>?. apply (plain _). Qed.
Global Instance monPred_ipure_persistent {I B} P :
  Persistent P → Persistent (@monPred_ipure I B P).
Proof. intros. split => ? /=. unseal. exact: H. Qed.

Global Instance monPred_in_timeless {I} {B : sbi} V :
  Timeless (@monPred_in I B V).
Proof. split => ? /=. unseal. apply timeless, _. Qed.
(* Note that monPred_in is *not* Plain, because it does depend on the
   index. *)
Global Instance monPred_in_persistent {I B} V :
  Persistent (@monPred_in I B V).
Proof. unfold Persistent. unseal; split => ?. by apply bi.pure_persistent. Qed.

Global Instance monPred_all_timeless {I} {B : sbi} P :
  Timeless P → Timeless (@monPred_all I B P).
Proof.
  move=>[]. unfold Timeless. unseal=>Hti. split=> ? /=.
  by apply timeless, bi.forall_timeless.
Qed.
Global Instance monPred_all_plain {I B} P :
  Plain P → Plain (@monPred_all I B P).
Proof.
  move=>[]. unfold Plain. unseal=>Hp. split=>? /=.
  apply bi.forall_intro=>i. rewrite {1}(bi.forall_elim i) Hp.
  by rewrite bi.plainly_forall.
Qed.
Global Instance monPred_all_persistent {I B} P :
  Persistent P → Persistent (@monPred_all I B P).
Proof.
  move=>[]. unfold Persistent. unseal=>Hp. split => ?.
  by apply persistent, bi.forall_persistent.
Qed.
