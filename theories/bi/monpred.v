From iris.bi Require Import derived_laws.

(** Definitions. *)

Structure bi_index :=
  BiIndex
    { bi_index_type :> Type;
      bi_index_inhabited : Inhabited bi_index_type;
      bi_index_rel : SqSubsetEq bi_index_type;
      bi_index_rel_preorder : PreOrder (⊑) }.

Existing Instances bi_index_inhabited bi_index_rel bi_index_rel_preorder.

Section Ofe_Cofe.
Context {I : bi_index} {PROP : bi}.
Implicit Types i : I.

Record monPred :=
  MonPred { monPred_car :> I → PROP;
            monPred_mono : Proper ((⊑) ==> (⊢)) monPred_car }.
Local Existing Instance monPred_mono.

Implicit Types P Q : monPred.

(** Ofe + Cofe instances  *)

Section Ofe_Cofe_def.
  Inductive monPred_equiv' P Q : Prop :=
    { monPred_in_equiv i : P i ≡ Q i } .
  Instance monPred_equiv : Equiv monPred := monPred_equiv'.
  Inductive monPred_dist' (n : nat) (P Q : monPred) : Prop :=
    { monPred_in_dist i : P i ≡{n}≡ Q i }.
  Instance monPred_dist : Dist monPred := monPred_dist'.

  Definition monPred_sig P : { f : I -c> PROP | Proper ((⊑) ==> (⊢)) f } :=
    exist _ (monPred_car P) (monPred_mono P).

  Definition sig_monPred (P' : { f : I -c> PROP | Proper ((⊑) ==> (⊢)) f })
    : monPred :=
    MonPred (proj1_sig P') (proj2_sig P').

  (* These two lemma use the wrong Equiv and Dist instance for
    monPred. so we make sure they are not accessible outside of the
    section by using Let. *)
  Let monPred_sig_equiv:
    ∀ P Q, P ≡ Q ↔ monPred_sig P ≡ monPred_sig Q.
  Proof. by split; [intros []|]. Qed.
  Let monPred_sig_dist:
    ∀ n, ∀ P Q : monPred, P ≡{n}≡ Q ↔ monPred_sig P ≡{n}≡ monPred_sig Q.
  Proof. by split; [intros []|]. Qed.

  Definition monPred_ofe_mixin : OfeMixin monPred.
  Proof. by apply (iso_ofe_mixin monPred_sig monPred_sig_equiv monPred_sig_dist). Qed.

  Canonical Structure monPredC := OfeT monPred monPred_ofe_mixin.

  Global Instance monPred_cofe `{Cofe PROP} : Cofe monPredC.
  Proof.
    unshelve refine (iso_cofe_subtype (A:=I-c>PROP) _ MonPred monPred_car _ _ _);
      [apply _|by apply monPred_sig_dist|done|].
    intros c i j Hij. apply @limit_preserving;
      [by apply bi.limit_preserving_entails; intros ??|]=>n. by rewrite Hij.
  Qed.
End Ofe_Cofe_def.

Lemma monPred_sig_monPred (P' : { f : I -c> PROP | Proper ((⊑) ==> (⊢)) f }) :
  monPred_sig (sig_monPred P') ≡ P'.
Proof. by change (P' ≡ P'). Qed.
Lemma sig_monPred_sig P : sig_monPred (monPred_sig P) ≡ P.
Proof. done. Qed.

Global Instance monPred_sig_ne : NonExpansive monPred_sig.
Proof. move=> ??? [?] ? //=. Qed.
Global Instance monPred_sig_proper : Proper ((≡) ==> (≡)) monPred_sig.
Proof. eapply (ne_proper _). Qed.
Global Instance sig_monPred_ne : NonExpansive (@sig_monPred).
Proof. split=>? //=. Qed.
Global Instance sig_monPred_proper : Proper ((≡) ==> (≡)) sig_monPred.
Proof. eapply (ne_proper _). Qed.

(* We generalize over the relation R which is morally the equivalence
   relation over B. That way, the BI index can use equality as an
   equivalence relation (and Coq is able to infer the Proper and
   Reflexive instances properly), or any other equivalence relation,
   provided it is compatible with (⊑). *)
Global Instance monPred_car_ne (R : relation I) :
  Proper (R ==> R ==> iff) (⊑) → Reflexive R →
  ∀ n, Proper (dist n ==> R ==> dist n) monPred_car.
Proof.
  intros ????? [Hd] ?? HR. rewrite Hd.
  apply equiv_dist, bi.equiv_spec; split; f_equiv; rewrite ->HR; done.
Qed.
Global Instance monPred_car_proper (R : relation I) :
  Proper (R ==> R ==> iff) (⊑) → Reflexive R →
  Proper ((≡) ==> R ==> (≡)) monPred_car.
Proof. repeat intro. apply equiv_dist=>?. f_equiv=>//. by apply equiv_dist. Qed.
End Ofe_Cofe.

Arguments monPred _ _ : clear implicits.
Local Existing Instance monPred_mono.
Arguments monPredC _ _ : clear implicits.

(** BI and SBI structures. *)

Section Bi.
Context {I : bi_index} {PROP : bi}.
Implicit Types i : I.
Notation monPred := (monPred I PROP).
Implicit Types P Q : monPred.

Inductive monPred_entails (P1 P2 : monPred) : Prop :=
  { monPred_in_entails i : P1 i ⊢ P2 i }.
Hint Immediate monPred_in_entails.

Program Definition monPred_upclosed (Φ : I → PROP) : monPred :=
  MonPred (λ i, (∀ j, ⌜i ⊑ j⌝ → Φ j)%I) _.
Next Obligation. solve_proper. Qed.

Definition monPred_ipure_def (P : PROP) : monPred := MonPred (λ _, P) _.
Definition monPred_ipure_aux : seal (@monPred_ipure_def). by eexists. Qed.
Global Instance monPred_ipure : BiEmbedding PROP monPred := unseal monPred_ipure_aux.
Definition monPred_ipure_eq : bi_embedding = _ := seal_eq _.

Definition monPred_pure (φ : Prop) : monPred := ⎡⌜φ⌝⎤%I.
Definition monPred_emp : monPred := ⎡emp⎤%I.

Program Definition monPred_and_def P Q : monPred :=
  MonPred (λ i, P i ∧ Q i)%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_and_aux : seal (@monPred_and_def). by eexists. Qed.
Definition monPred_and := unseal (@monPred_and_aux).
Definition monPred_and_eq : @monPred_and = _ := seal_eq _.

Program Definition monPred_or_def P Q : monPred :=
  MonPred (λ i, P i ∨ Q i)%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_or_aux : seal (@monPred_or_def). by eexists. Qed.
Definition monPred_or := unseal (@monPred_or_aux).
Definition monPred_or_eq : @monPred_or = _ := seal_eq _.

Definition monPred_impl_def P Q : monPred :=
  monPred_upclosed (λ i, P i → Q i)%I.
Definition monPred_impl_aux : seal (@monPred_impl_def). by eexists. Qed.
Definition monPred_impl := unseal (@monPred_impl_aux).
Definition monPred_impl_eq : @monPred_impl = _ := seal_eq _.

Program Definition monPred_forall_def A (Φ : A → monPred) : monPred :=
  MonPred (λ i, ∀ x : A, Φ x i)%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_forall_aux : seal (@monPred_forall_def). by eexists. Qed.
Definition monPred_forall := unseal (@monPred_forall_aux).
Definition monPred_forall_eq : @monPred_forall = _ := seal_eq _.

Program Definition monPred_exist_def A (Φ : A → monPred) : monPred :=
  MonPred (λ i, ∃ x : A, Φ x i)%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_exist_aux : seal (@monPred_exist_def). by eexists. Qed.
Definition monPred_exist := unseal (@monPred_exist_aux).
Definition monPred_exist_eq : @monPred_exist = _ := seal_eq _.

Definition monPred_internal_eq_def (A : ofeT) (a b : A) : monPred :=
  MonPred (λ _, bi_internal_eq a b) _.
Definition monPred_internal_eq_aux : seal (@monPred_internal_eq_def). by eexists. Qed.
Definition monPred_internal_eq := unseal (@monPred_internal_eq_aux).
Definition monPred_internal_eq_eq : @monPred_internal_eq = _ := seal_eq _.

Program Definition monPred_sep_def P Q : monPred :=
  MonPred (λ i, P i ∗ Q i)%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_sep_aux : seal (@monPred_sep_def). by eexists. Qed.
Definition monPred_sep := unseal monPred_sep_aux.
Definition monPred_sep_eq : @monPred_sep = _ := seal_eq _.

Definition monPred_wand_def P Q : monPred :=
  monPred_upclosed (λ i, P i -∗ Q i)%I.
Definition monPred_wand_aux : seal (@monPred_wand_def). by eexists. Qed.
Definition monPred_wand := unseal monPred_wand_aux.
Definition monPred_wand_eq : @monPred_wand = _ := seal_eq _.

Program Definition monPred_persistently_def P : monPred :=
  MonPred (λ i, bi_persistently (P i)) _.
Next Obligation. solve_proper. Qed.
Definition monPred_persistently_aux : seal (@monPred_persistently_def). by eexists. Qed.
Definition monPred_persistently := unseal monPred_persistently_aux.
Definition monPred_persistently_eq : @monPred_persistently = _ := seal_eq _.

Definition monPred_plainly P : monPred := ⎡∀ i, bi_plainly (P i)⎤%I.

Program Definition monPred_in_def (i0 : I) : monPred :=
  MonPred (λ i : I, ⌜i0 ⊑ i⌝%I) _.
Next Obligation. solve_proper. Qed.
Definition monPred_in_aux : seal (@monPred_in_def). by eexists. Qed.
Definition monPred_in := unseal (@monPred_in_aux).
Definition monPred_in_eq : @monPred_in = _ := seal_eq _.

Definition monPred_all_def (P : monPred) : monPred :=
  MonPred (λ _ : I, ∀ i, P i)%I _.
Definition monPred_all_aux : seal (@monPred_all_def). by eexists. Qed.
Definition monPred_all := unseal (@monPred_all_aux).
Definition monPred_all_eq : @monPred_all = _ := seal_eq _.
End Bi.

Typeclasses Opaque monPred_pure monPred_emp monPred_plainly.

Program Definition monPred_later_def {I : bi_index} {PROP : sbi}
        (P : monPred I PROP) : monPred I PROP := MonPred (λ i, ▷ (P i))%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_later_aux {I PROP} : seal (@monPred_later_def I PROP). by eexists. Qed.
Definition monPred_later {I PROP} := unseal (@monPred_later_aux I PROP).
Definition monPred_later_eq {I PROP} : @monPred_later I PROP = _ := seal_eq _.

Module MonPred.
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
End MonPred.
Import MonPred.

Section canonical_bi.
Context (I : bi_index) (PROP : bi).

Lemma monPred_bi_mixin : BiMixin (@monPred_ofe_mixin I PROP)
  monPred_entails monPred_emp monPred_pure monPred_and monPred_or
  monPred_impl monPred_forall monPred_exist monPred_internal_eq
  monPred_sep monPred_wand monPred_plainly monPred_persistently.
Proof.
  split; try unseal;
    try by (repeat intro; split=> ? /=; repeat f_equiv).
  - split.
    + intros P. by split.
    + intros P Q R [H1] [H2]. split => ?. by rewrite H1 H2.
  - split.
    + intros [HPQ]. split; split => i; move: (HPQ i); by apply bi.equiv_spec.
    + intros [[] []]. split=>i. by apply bi.equiv_spec.
  - intros P φ ?. split=> i. by apply bi.pure_intro.
  - intros φ P HP. split=> i. apply bi.pure_elim'=> ?. by apply HP.
  - intros A φ. split=> i. by apply bi.pure_forall_2.
  - intros P Q. split=> i. by apply bi.and_elim_l.
  - intros P Q. split=> i. by apply bi.and_elim_r.
  - intros P Q R [?] [?]. split=> i. by apply bi.and_intro.
  - intros P Q. split=> i. by apply bi.or_intro_l.
  - intros P Q. split=> i. by apply bi.or_intro_r.
  - intros P Q R [?] [?]. split=> i. by apply bi.or_elim.
  - intros P Q R [HR]. split=> i /=. setoid_rewrite bi.pure_impl_forall.
    apply bi.forall_intro=> j. apply bi.forall_intro=> Hij.
    apply bi.impl_intro_r. by rewrite -HR /= !Hij.
  - intros P Q R [HR]. split=> i /=.
     rewrite HR /= bi.forall_elim bi.pure_impl_forall bi.forall_elim //.
    apply bi.impl_elim_l.
  - intros A P Ψ HΨ. split=> i. apply bi.forall_intro => ?. by apply HΨ.
  - intros A Ψ. split=> i. by apply: bi.forall_elim.
  - intros A Ψ a. split=> i. by rewrite /= -bi.exist_intro.
  - intros A Ψ Q HΨ. split=> i. apply bi.exist_elim => a. by apply HΨ.
  - intros A P a. split=> i. by apply bi.internal_eq_refl.
  - intros A a b Ψ ?. split=> i /=.
    setoid_rewrite bi.pure_impl_forall. do 2 apply bi.forall_intro => ?.
    erewrite (bi.internal_eq_rewrite _ _ (flip Ψ _)) => //=. solve_proper.
  - intros A1 A2 f g. split=> i. by apply bi.fun_ext.
  - intros A P x y. split=> i. by apply bi.sig_eq.
  - intros A a b ?. split=> i. by apply bi.discrete_eq_1.
  - intros P P' Q Q' [?] [?]. split=> i. by apply bi.sep_mono.
  - intros P. split=> i. by apply bi.emp_sep_1.
  - intros P. split=> i. by apply bi.emp_sep_2.
  - intros P Q. split=> i. by apply bi.sep_comm'.
  - intros P Q R. split=> i. by apply bi.sep_assoc'.
  - intros P Q R [HR]. split=> i /=. setoid_rewrite bi.pure_impl_forall.
    apply bi.forall_intro=> j. apply bi.forall_intro=> Hij.
    apply bi.wand_intro_r. by rewrite -HR /= !Hij.
  - intros P Q R [HP]. split=> i. apply bi.wand_elim_l'.
    rewrite HP /= bi.forall_elim bi.pure_impl_forall bi.forall_elim //.
  - intros P Q [?]. split=> i /=. by do 3 f_equiv.
  - intros P. split=> i /=. by rewrite bi.forall_elim bi.plainly_elim_persistently.
  - intros P. split=> i /=. repeat setoid_rewrite <-bi.plainly_forall.
    rewrite -bi.plainly_idemp_2. f_equiv. by apply bi.forall_intro=>_.
  - intros A Ψ. split=> i /=. apply bi.forall_intro=> j.
    rewrite bi.plainly_forall. apply bi.forall_intro=> a.
    by rewrite !bi.forall_elim.
  - intros P Q. split=> i /=.
    rewrite <-(sig_monPred_sig P), <-(sig_monPred_sig Q), <-(bi.f_equiv _).
    rewrite -bi.sig_equivI /= -bi.fun_ext. f_equiv=> j.
    rewrite -bi.prop_ext !(bi.forall_elim j) !bi.pure_impl_forall
            !bi.forall_elim //.
  - intros P Q. split=> i /=. repeat setoid_rewrite bi.pure_impl_forall.
    repeat setoid_rewrite <-bi.plainly_forall.
    repeat setoid_rewrite bi.persistently_forall. do 4 f_equiv.
    apply bi.persistently_impl_plainly.
  - intros P Q. split=> i /=.
    repeat setoid_rewrite bi.pure_impl_forall. rewrite 2!bi.forall_elim //.
    repeat setoid_rewrite <-bi.plainly_forall.
    setoid_rewrite bi.plainly_impl_plainly. f_equiv.
    do 3 apply bi.forall_intro => ?. f_equiv. rewrite bi.forall_elim //.
  - intros P. split=> i. apply bi.forall_intro=>_. by apply bi.plainly_emp_intro.
  - intros P Q. split=> i. apply bi.sep_elim_l, _.
  - intros P Q [?]. split=> i /=. by f_equiv.
  - intros P. split=> i. by apply bi.persistently_idemp_2.
  - intros P. split=> i /=. by setoid_rewrite bi.plainly_persistently_1.
  - intros A Ψ. split=> i. by apply bi.persistently_forall_2.
  - intros A Ψ. split=> i. by apply bi.persistently_exist_1.
  - intros P Q. split=> i. apply bi.sep_elim_l, _.
  - intros P Q. split=> i. by apply bi.persistently_and_sep_elim.
Qed.

Canonical Structure monPredI : bi :=
  Bi (monPred I PROP) monPred_dist monPred_equiv monPred_entails monPred_emp
     monPred_pure monPred_and monPred_or monPred_impl monPred_forall
     monPred_exist monPred_internal_eq monPred_sep monPred_wand monPred_plainly
     monPred_persistently monPred_ofe_mixin monPred_bi_mixin.
End canonical_bi.

Section canonical_sbi.
Context (I : bi_index) (PROP : sbi).

Lemma monPred_sbi_mixin :
  SbiMixin (PROP:=monPred I PROP) monPred_entails monPred_pure monPred_or
           monPred_impl monPred_forall monPred_exist monPred_internal_eq
           monPred_sep monPred_plainly monPred_persistently monPred_later.
Proof.
  split; unseal.
  - intros n P Q HPQ. split=> i /=.
    apply bi.later_contractive. destruct n as [|n]=> //. by apply HPQ.
  - intros A x y. split=> i. by apply bi.later_eq_1.
  - intros A x y. split=> i. by apply bi.later_eq_2.
  - intros P Q [?]. split=> i. by apply bi.later_mono.
  - intros P. split=> i /=.
    setoid_rewrite bi.pure_impl_forall. rewrite /= !bi.forall_elim //. by apply bi.löb.
  - intros A Ψ. split=> i. by apply bi.later_forall_2.
  - intros A Ψ. split=> i. by apply bi.later_exist_false.
  - intros P Q. split=> i. by apply bi.later_sep_1.
  - intros P Q. split=> i. by apply bi.later_sep_2.
  - intros P. split=> i /=.
    rewrite bi.later_forall. f_equiv=> j. by rewrite -bi.later_plainly_1.
  - intros P. split=> i /=.
    rewrite bi.later_forall. f_equiv=> j. by rewrite -bi.later_plainly_2.
  - intros P. split=> i. by apply bi.later_persistently_1.
  - intros P. split=> i. by apply bi.later_persistently_2.
  - intros P. split=> i /=. rewrite -bi.forall_intro. apply bi.later_false_em.
    intros j. rewrite bi.pure_impl_forall. apply bi.forall_intro=> Hij. by rewrite Hij.
Qed.

Canonical Structure monPredSI : sbi :=
  Sbi (monPred I PROP) monPred_dist monPred_equiv monPred_entails monPred_emp
      monPred_pure monPred_and monPred_or monPred_impl monPred_forall
      monPred_exist monPred_internal_eq monPred_sep monPred_wand monPred_plainly
      monPred_persistently monPred_later monPred_ofe_mixin
      (bi_bi_mixin _) monPred_sbi_mixin.
End canonical_sbi.

(** Primitive facts that cannot be deduced from the BI structure. *)

Section bi_facts.
Context {I : bi_index} {PROP : bi}.
Implicit Types i : I.
Implicit Types P Q : monPred I PROP.

Global Instance monPred_car_mono :
  Proper ((⊢) ==> (⊑) ==> (⊢)) (@monPred_car I PROP).
Proof. by move=> ?? [?] ?? ->. Qed.
Global Instance monPred_car_mono_flip :
  Proper (flip (⊢) ==> flip (⊑) ==> flip (⊢)) (@monPred_car I PROP).
Proof. solve_proper. Qed.

Global Instance monPred_ipure_ne :
  NonExpansive (@bi_embedding PROP (monPred I PROP) _).
Proof. unseal. by split. Qed.
Global Instance monPred_ipure_proper :
  Proper ((≡) ==> (≡)) (@bi_embedding PROP (monPred I PROP) _).
Proof. apply (ne_proper _). Qed.
Global Instance monPred_ipure_mono :
  Proper ((⊢) ==> (⊢)) (@bi_embedding PROP (monPred I PROP) _).
Proof. unseal. by split. Qed.
Global Instance monPred_ipure_mono_flip :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_embedding PROP (monPred I PROP) _).
Proof. solve_proper. Qed.

Global Instance monPred_in_proper (R : relation I) :
  Proper (R ==> R ==> iff) (⊑) → Reflexive R →
  Proper (R ==> (≡)) (@monPred_in I PROP).
Proof. unseal. split. solve_proper. Qed.
Global Instance monPred_in_mono : Proper (flip (⊑) ==> (⊢)) (@monPred_in I PROP).
Proof. unseal. split. solve_proper. Qed.
Global Instance monPred_in_mono_flip : Proper ((⊑) ==> flip (⊢)) (@monPred_in I PROP).
Proof. solve_proper. Qed.

Global Instance monPred_all_ne : NonExpansive (@monPred_all I PROP).
Proof. unseal. split. solve_proper. Qed.
Global Instance monPred_all_proper : Proper ((≡) ==> (≡)) (@monPred_all I PROP).
Proof. apply (ne_proper _). Qed.
Global Instance monPred_all_mono : Proper ((⊢) ==> (⊢)) (@monPred_all I PROP).
Proof. unseal. split. solve_proper. Qed.
Global Instance monPred_all_mono_flip :
  Proper (flip (⊢) ==> flip (⊢)) (@monPred_all I PROP).
Proof. solve_proper. Qed.

Global Instance monPred_positive : BiPositive PROP → BiPositive (monPredI I PROP).
Proof. split => ?. unseal. apply bi_positive. Qed.
Global Instance monPred_affine : BiAffine PROP → BiAffine (monPredI I PROP).
Proof. split => ?. unseal. by apply affine. Qed.

(* (∀ x, bottom ⊑ x) cannot be infered using typeclasses. So this is
  not an instance. One should explicitely make an instance from this
  lemma for each instantiation of monPred. *)
Lemma monPred_plainly_exist (bottom : I) :
  (∀ x, bottom ⊑ x) → BiPlainlyExist PROP → BiPlainlyExist (monPredI I PROP).
Proof.
  intros ????. unseal. split=>? /=.
  rewrite (bi.forall_elim bottom) plainly_exist_1. do 2 f_equiv.
  apply bi.forall_intro=>?. by do 2 f_equiv.
Qed.

Lemma monPred_wand_force P Q i : (P -∗ Q) i -∗ (P i -∗ Q i).
Proof. unseal. rewrite bi.forall_elim bi.pure_impl_forall bi.forall_elim //. Qed.

Lemma monPred_impl_force P Q i : (P → Q) i -∗ (P i → Q i).
Proof. unseal. rewrite bi.forall_elim bi.pure_impl_forall bi.forall_elim //. Qed.

Lemma monPred_persistently_if_eq p P i:
  (bi_persistently_if p P) i = bi_persistently_if p (P i).
Proof. rewrite /bi_persistently_if. unseal. by destruct p. Qed.

Lemma monPred_affinely_if_eq p P i:
  (bi_affinely_if p P) i = bi_affinely_if p (P i).
Proof. rewrite /bi_affinely_if. destruct p => //. rewrite /bi_affinely. by unseal. Qed.

Global Instance monPred_car_persistent P i : Persistent P → Persistent (P i).
Proof. move => [] /(_ i). by unseal. Qed.
Global Instance monPred_car_plain P i : Plain P → Plain (P i).
Proof. move => [] /(_ i). unfold Plain. unseal. rewrite bi.forall_elim //. Qed.
Global Instance monPred_car_absorbing P i : Absorbing P → Absorbing (P i).
Proof. move => [] /(_ i). unfold Absorbing. by unseal. Qed.
Global Instance monPred_car_affine P i : Affine P → Affine (P i).
Proof. move => [] /(_ i). unfold Affine. by unseal. Qed.

Global Instance monPred_ipure_plain (P : PROP) :
  Plain P → @Plain (monPredI I PROP) ⎡P⎤%I.
Proof. split => ? /=. unseal. apply bi.forall_intro=>?. apply (plain _). Qed.
Global Instance monPred_ipure_persistent (P : PROP) :
  Persistent P → @Persistent (monPredI I PROP) ⎡P⎤%I.
Proof. split => ? /=. unseal. exact: H. Qed.
Global Instance monPred_ipure_absorbing (P : PROP) :
  Absorbing P → @Absorbing (monPredI I PROP) ⎡P⎤%I.
Proof. unfold Absorbing. split => ? /=. by unseal. Qed.
Global Instance monPred_ipure_affine (P : PROP) :
  Affine P → @Affine (monPredI I PROP) ⎡P⎤%I.
Proof. unfold Affine. split => ? /=. by unseal. Qed.

(* Note that monPred_in is *not* Plain, because it does depend on the
   index. *)
Global Instance monPred_in_persistent V :
  Persistent (@monPred_in I PROP V).
Proof. unfold Persistent. unseal; split => ?. by apply bi.pure_persistent. Qed.
Global Instance monPred_in_absorbing V :
  Absorbing (@monPred_in I PROP V).
Proof. unfold Absorbing. unseal. split=> ? /=. apply absorbing, _. Qed.

Global Instance monPred_all_plain P : Plain P → Plain (@monPred_all I PROP P).
Proof.
  move=>[]. unfold Plain. unseal=>Hp. split=>? /=.
  apply bi.forall_intro=>i. rewrite {1}(bi.forall_elim i) Hp.
  by rewrite bi.plainly_forall.
Qed.
Global Instance monPred_all_persistent P :
  Persistent P → Persistent (@monPred_all I PROP P).
Proof.
  move=>[]. unfold Persistent. unseal=>Hp. split => ?.
  by apply persistent, bi.forall_persistent.
Qed.
Global Instance monPred_all_absorbing P :
  Absorbing P → Absorbing (@monPred_all I PROP P).
Proof.
  move=>[]. unfold Absorbing. unseal=>Hp. split => ?.
  by apply absorbing, bi.forall_absorbing.
Qed.
Global Instance monPred_all_affine P :
  Affine P → Affine (@monPred_all I PROP P).
Proof.
  move=> []. unfold Affine. unseal=>Hp. split => ?.
  by apply affine, bi.forall_affine.
Qed.
End bi_facts.

Section sbi_facts.
Context {I : bi_index} {PROP : sbi}.
Implicit Types i : I.
Implicit Types P Q : monPred I PROP.

Global Instance monPred_car_timeless P i : Timeless P → Timeless (P i).
Proof. move => [] /(_ i). unfold Timeless. by unseal. Qed.
Global Instance monPred_ipure_timeless (P : PROP) :
  Timeless P → @Timeless (monPredSI I PROP) ⎡P⎤%I.
Proof. intros. split => ? /=. unseal. exact: H. Qed.
Global Instance monPred_in_timeless i0 : Timeless (@monPred_in I PROP i0).
Proof. split => ? /=. unseal. apply timeless, _. Qed.
Global Instance monPred_all_timeless P :
  Timeless P → Timeless (@monPred_all I PROP P).
Proof.
  move=>[]. unfold Timeless. unseal=>Hti. split=> ? /=.
  by apply timeless, bi.forall_timeless.
Qed.
End sbi_facts.
