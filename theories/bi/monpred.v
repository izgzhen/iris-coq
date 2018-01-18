From stdpp Require Import coPset.
From iris.bi Require Import bi.

(** Definitions. *)

Structure biIndex :=
  BiIndex
    { bi_index_type :> Type;
      bi_index_inhabited : Inhabited bi_index_type;
      bi_index_rel : SqSubsetEq bi_index_type;
      bi_index_rel_preorder : PreOrder (⊑) }.
Existing Instances bi_index_inhabited bi_index_rel bi_index_rel_preorder.

(* TODO : all the use cases of this have a bi_index with a bottom
   element. Should we add this to the structure? *)
Class BiIndexBottom {I : biIndex} (bot : I) :=
  bi_index_bot i : bot ⊑ i.

Section Ofe_Cofe.
Context {I : biIndex} {PROP : bi}.
Implicit Types i : I.

Record monPred :=
  MonPred { monPred_at :> I → PROP;
            monPred_mono : Proper ((⊑) ==> (⊢)) monPred_at }.
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
    exist _ (monPred_at P) (monPred_mono P).

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
    unshelve refine (iso_cofe_subtype (A:=I-c>PROP) _ MonPred monPred_at _ _ _);
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
Global Instance monPred_at_ne (R : relation I) :
  Proper (R ==> R ==> iff) (⊑) → Reflexive R →
  ∀ n, Proper (dist n ==> R ==> dist n) monPred_at.
Proof.
  intros ????? [Hd] ?? HR. rewrite Hd.
  apply equiv_dist, bi.equiv_spec; split; f_equiv; rewrite ->HR; done.
Qed.
Global Instance monPred_at_proper (R : relation I) :
  Proper (R ==> R ==> iff) (⊑) → Reflexive R →
  Proper ((≡) ==> R ==> (≡)) monPred_at.
Proof. repeat intro. apply equiv_dist=>?. f_equiv=>//. by apply equiv_dist. Qed.
End Ofe_Cofe.

Arguments monPred _ _ : clear implicits.
Arguments monPred_at {_ _} _%I _.
Local Existing Instance monPred_mono.
Arguments monPredC _ _ : clear implicits.

(** BI and SBI structures. *)

Section Bi.
Context {I : biIndex} {PROP : bi}.
Implicit Types i : I.
Notation monPred := (monPred I PROP).
Implicit Types P Q : monPred.

Inductive monPred_entails (P1 P2 : monPred) : Prop :=
  { monPred_in_entails i : P1 i ⊢ P2 i }.
Hint Immediate monPred_in_entails.

Program Definition monPred_upclosed (Φ : I → PROP) : monPred :=
  MonPred (λ i, (∀ j, ⌜i ⊑ j⌝ → Φ j)%I) _.
Next Obligation. solve_proper. Qed.

Definition monPred_embed_def (P : PROP) : monPred := MonPred (λ _, P) _.
Definition monPred_embed_aux : seal (@monPred_embed_def). by eexists. Qed.
Global Instance monPred_embed : BiEmbed PROP monPred := unseal monPred_embed_aux.
Definition monPred_embed_eq : bi_embed (A:=PROP) = _ := seal_eq _.

Definition monPred_pure (φ : Prop) : monPred := tc_opaque ⎡⌜φ⌝⎤%I.
Definition monPred_emp : monPred := tc_opaque ⎡emp⎤%I.
Definition monPred_internal_eq (A : ofeT) (a b : A) : monPred := tc_opaque ⎡a ≡ b⎤%I.
Definition monPred_plainly P : monPred := tc_opaque ⎡∀ i, bi_plainly (P i)⎤%I.

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

Definition monPred_ex_def (P : monPred) : monPred :=
  MonPred (λ _ : I, ∃ i, P i)%I _.
Definition monPred_ex_aux : seal (@monPred_ex_def). by eexists. Qed.
Definition monPred_ex := unseal (@monPred_ex_aux).
Definition monPred_ex_eq : @monPred_ex = _ := seal_eq _.

Definition monPred_bupd_def `{BUpd PROP} (P : monPred) : monPred :=
  (* monPred_upclosed is not actually needed, since bupd is always
     monotone. However, this depends on BUpdFacts, and we do not want
     this definition to depend on BUpdFacts to avoid having proofs
     terms in logical terms. *)
  monPred_upclosed (λ i, |==> P i)%I.
Definition monPred_bupd_aux `{BUpd PROP} : seal monPred_bupd_def. by eexists. Qed.
Global Instance monPred_bupd `{BUpd PROP} : BUpd _ := unseal monPred_bupd_aux.
Definition monPred_bupd_eq `{BUpd PROP} : @bupd monPred _ = _ := seal_eq _.
End Bi.

Typeclasses Opaque monPred_pure monPred_emp monPred_plainly.

Section Sbi.
Context {I : biIndex} {PROP : sbi}.
Implicit Types i : I.
Notation monPred := (monPred I PROP).
Implicit Types P Q : monPred.

Program Definition monPred_later_def P : monPred := MonPred (λ i, ▷ (P i))%I _.
Next Obligation. solve_proper. Qed.
Definition monPred_later_aux : seal monPred_later_def. by eexists. Qed.
Definition monPred_later := unseal monPred_later_aux.
Definition monPred_later_eq : monPred_later = _ := seal_eq _.

Definition monPred_fupd_def `{FUpd PROP} (E1 E2 : coPset) (P : monPred) : monPred :=
  (* monPred_upclosed is not actually needed, since fupd is always
     monotone. However, this depends on FUpdFacts, and we do not want
     this definition to depend on FUpdFacts to avoid having proofs
     terms in logical terms. *)
  monPred_upclosed (λ i, |={E1,E2}=> P i)%I.
Definition monPred_fupd_aux `{FUpd PROP} : seal monPred_fupd_def. by eexists. Qed.
Global Instance monPred_fupd `{FUpd PROP} : FUpd _ := unseal monPred_fupd_aux.
Definition monPred_fupd_eq `{FUpd PROP} : @fupd monPred _ = _ := seal_eq _.
End Sbi.

Module MonPred.
Definition unseal_eqs :=
  (@monPred_and_eq, @monPred_or_eq, @monPred_impl_eq,
   @monPred_forall_eq, @monPred_exist_eq,
   @monPred_sep_eq, @monPred_wand_eq,
   @monPred_persistently_eq, @monPred_later_eq,
   @monPred_in_eq, @monPred_all_eq, @monPred_ex_eq, @monPred_embed_eq,
   @monPred_bupd_eq, @monPred_fupd_eq).
Ltac unseal :=
  unfold bi_affinely, bi_absorbingly, sbi_except_0, bi_pure, bi_emp,
         monPred_upclosed, bi_and, bi_or, bi_impl, bi_forall, bi_exist,
         bi_internal_eq, bi_sep, bi_wand, bi_persistently, bi_affinely,
         sbi_later; simpl;
  unfold sbi_emp, sbi_pure, sbi_and, sbi_or, sbi_impl, sbi_forall, sbi_exist,
         sbi_internal_eq, sbi_sep, sbi_wand, sbi_persistently, sbi_plainly,
         bi_plainly; simpl;
  unfold monPred_pure, monPred_emp, monPred_internal_eq, monPred_plainly; simpl;
  rewrite !unseal_eqs /=.
End MonPred.
Import MonPred.

Section canonical_bi.
Context (I : biIndex) (PROP : bi).

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
Context (I : biIndex) (PROP : sbi).

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
Context {I : biIndex} {PROP : bi}.
Local Notation monPred := (monPred I PROP).
Local Notation monPredI := (monPredI I PROP).
Local Notation monPred_at := (@monPred_at I PROP).
Local Notation BiIndexBottom := (@BiIndexBottom I).
Implicit Types i : I.
Implicit Types P Q : monPred.

(** Instances *)

Global Instance monPred_at_mono :
  Proper ((⊢) ==> (⊑) ==> (⊢)) monPred_at.
Proof. by move=> ?? [?] ?? ->. Qed.
Global Instance monPred_at_mono_flip :
  Proper (flip (⊢) ==> flip (⊑) ==> flip (⊢)) monPred_at.
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

Global Instance monPred_ex_ne : NonExpansive (@monPred_ex I PROP).
Proof. unseal. split. solve_proper. Qed.
Global Instance monPred_ex_proper : Proper ((≡) ==> (≡)) (@monPred_ex I PROP).
Proof. apply (ne_proper _). Qed.
Global Instance monPred_ex_mono : Proper ((⊢) ==> (⊢)) (@monPred_ex I PROP).
Proof. unseal. split. solve_proper. Qed.
Global Instance monPred_ex_mono_flip :
  Proper (flip (⊢) ==> flip (⊢)) (@monPred_ex I PROP).
Proof. solve_proper. Qed.

Global Instance monPred_positive : BiPositive PROP → BiPositive monPredI.
Proof. split => ?. unseal. apply bi_positive. Qed.
Global Instance monPred_affine : BiAffine PROP → BiAffine monPredI.
Proof. split => ?. unseal. by apply affine. Qed.

Global Instance monPred_plainly_exist `{BiIndexBottom bot} :
  BiPlainlyExist PROP → BiPlainlyExist monPredI.
Proof.
  split=>?/=. unseal. rewrite (bi.forall_elim bot) plainly_exist_1. do 2 f_equiv.
  apply bi.forall_intro=>?. by do 2 f_equiv.
Qed.

Global Instance monPred_at_persistent P i : Persistent P → Persistent (P i).
Proof. move => [] /(_ i). by unseal. Qed.
Global Instance monPred_at_plain P i : Plain P → Plain (P i).
Proof. move => [] /(_ i). unfold Plain. unseal. rewrite bi.forall_elim //. Qed.
Global Instance monPred_at_absorbing P i : Absorbing P → Absorbing (P i).
Proof. move => [] /(_ i). unfold Absorbing. by unseal. Qed.
Global Instance monPred_at_affine P i : Affine P → Affine (P i).
Proof. move => [] /(_ i). unfold Affine. by unseal. Qed.

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

Global Instance monPred_ex_plain P :
  Plain P → Plain (@monPred_ex I PROP P).
Proof.
  move=>[]. unfold Plain. unseal=>Hp. split=>? /=.
  apply bi.exist_elim=>i. apply bi.forall_intro=>_. rewrite Hp.
  rewrite (bi.forall_elim i) -bi.exist_intro //.
Qed.
Global Instance monPred_ex_persistent P :
  Persistent P → Persistent (@monPred_ex I PROP P).
Proof.
  move=>[]. unfold Persistent. unseal=>Hp. split => ?.
  by apply persistent, bi.exist_persistent.
Qed.
Global Instance monPred_ex_absorbing P :
  Absorbing P → Absorbing (@monPred_ex I PROP P).
Proof.
  move=>[]. unfold Absorbing. unseal=>Hp. split => ?.
  by apply absorbing, bi.exist_absorbing.
Qed.
Global Instance monPred_ex_affine P :
  Affine P → Affine (@monPred_ex I PROP P).
Proof.
  move=> []. unfold Affine. unseal=>Hp. split => ?.
  by apply affine, bi.exist_affine.
Qed.

Global Instance monPred_bi_embedding : BiEmbedding PROP monPredI.
Proof.
  split; try apply _; unseal; try done.
  - move =>?? /= [/(_ inhabitant) ?] //.
  - split=>? /=.
    by rewrite bi.forall_elim bi.pure_impl_forall bi.forall_elim.
  - split=>? /=.
    by rewrite bi.forall_elim bi.pure_impl_forall bi.forall_elim.
  - intros ?. split => ? /=. apply bi.equiv_spec; split.
    by apply bi.forall_intro. by rewrite bi.forall_elim.
Qed.

Global Instance monPred_bupd_facts `{BUpdFacts PROP} : BUpdFacts monPredI.
Proof.
  split; unseal; unfold monPred_bupd_def, monPred_upclosed.
  - intros n P Q HPQ. split=>/= i. by repeat f_equiv.
  - intros P. split=>/= i. apply bi.forall_intro=>?. rewrite bi.pure_impl_forall.
    apply bi.forall_intro=><-. apply bupd_intro.
  - intros P Q HPQ. split=>/= i. by repeat f_equiv.
  - intros P. split=>/= i. do 3 f_equiv. rewrite -(bupd_trans (P _))
      bi.forall_elim bi.pure_impl_forall bi.forall_elim //.
  - intros P Q. split=> /= i. apply bi.forall_intro=>?.
    rewrite bi.pure_impl_forall. apply bi.forall_intro=><-.
    rewrite -bupd_frame_r bi.forall_elim bi.pure_impl_forall bi.forall_elim //.
  - intros P. split=> /= i. rewrite bi.forall_elim bi.pure_impl_forall
      bi.forall_elim // -bi.plainly_forall bupd_plainly bi.forall_elim //.
Qed.

(** monPred_at unfolding laws *)
Lemma monPred_at_embed i (P : PROP) : monPred_at ⎡P⎤ i ⊣⊢ P.
Proof. by unseal. Qed.
Lemma monPred_at_pure i (φ : Prop) : monPred_at ⌜φ⌝ i ⊣⊢ ⌜φ⌝.
Proof. by apply monPred_at_embed. Qed.
Lemma monPred_at_emp i : monPred_at emp i ⊣⊢ emp.
Proof. by apply monPred_at_embed. Qed.
Lemma monPred_at_internal_eq {A : ofeT} i (a b : A) : monPred_at (a ≡ b) i ⊣⊢ a ≡ b.
Proof. by apply monPred_at_embed. Qed.
Lemma monPred_at_plainly i P : bi_plainly P i ⊣⊢ ∀ j, bi_plainly (P j).
Proof. by apply monPred_at_embed. Qed.
Lemma monPred_at_and i P Q : (P ∧ Q) i ⊣⊢ P i ∧ Q i.
Proof. by unseal. Qed.
Lemma monPred_at_or i P Q : (P ∨ Q) i ⊣⊢ P i ∨ Q i.
Proof. by unseal. Qed.
Lemma monPred_at_impl i P Q : (P → Q) i ⊣⊢ ∀ j, ⌜i ⊑ j⌝ → P j → Q j.
Proof. by unseal. Qed.
Lemma monPred_at_forall {A} i (Φ : A → monPred) : (∀ x, Φ x) i ⊣⊢ ∀ x, Φ x i.
Proof. by unseal. Qed.
Lemma monPred_at_exist {A} i (Φ : A → monPred) : (∃ x, Φ x) i ⊣⊢ ∃ x, Φ x i.
Proof. by unseal. Qed.
Lemma monPred_at_sep i P Q : (P ∗ Q) i ⊣⊢ P i ∗ Q i.
Proof. by unseal. Qed.
Lemma monPred_at_wand i P Q : (P -∗ Q) i ⊣⊢ ∀ j, ⌜i ⊑ j⌝ → P j -∗ Q j.
Proof. by unseal. Qed.
Lemma monPred_at_persistently i P : bi_persistently P i ⊣⊢ bi_persistently (P i).
Proof. by unseal. Qed.
Lemma monPred_at_in i j : monPred_at (monPred_in j) i ⊣⊢ ⌜j ⊑ i⌝.
Proof. by unseal. Qed.
Lemma monPred_at_all i P : monPred_all P i ⊣⊢ ∀ j, P j.
Proof. by unseal. Qed.
Lemma monPred_at_ex i P : monPred_ex P i ⊣⊢ ∃ j, P j.
Proof. by unseal. Qed.
Lemma monPred_at_bupd `{BUpdFacts PROP} i P : (|==> P) i ⊣⊢ |==> P i.
Proof.
  unseal. setoid_rewrite bi.pure_impl_forall. apply bi.equiv_spec; split.
  - rewrite !bi.forall_elim //.
  - do 2 apply bi.forall_intro=>?. by do 2 f_equiv.
Qed.
Lemma monPred_at_persistently_if i p P :
  bi_persistently_if p P i ⊣⊢ bi_persistently_if p (P i).
Proof. destruct p=>//=. apply monPred_at_persistently. Qed.
Lemma monPred_at_affinely i P : bi_affinely P i ⊣⊢ bi_affinely (P i).
Proof. by rewrite /bi_affinely monPred_at_and monPred_at_emp. Qed.
Lemma monPred_at_affinely_if i p P :
  bi_affinely_if p P i ⊣⊢ bi_affinely_if p (P i).
Proof. destruct p=>//=. apply monPred_at_affinely. Qed.
Lemma monPred_at_absorbingly i P : bi_absorbingly P i ⊣⊢ bi_absorbingly (P i).
Proof. by rewrite /bi_absorbingly monPred_at_sep monPred_at_pure. Qed.

Lemma monPred_wand_force i P Q : (P -∗ Q) i -∗ (P i -∗ Q i).
Proof. unseal. rewrite bi.forall_elim bi.pure_impl_forall bi.forall_elim //. Qed.
Lemma monPred_impl_force i P Q : (P → Q) i -∗ (P i → Q i).
Proof. unseal. rewrite bi.forall_elim bi.pure_impl_forall bi.forall_elim //. Qed.

(* Laws for monPred_all. *)
Local Notation monPred_all := (@monPred_all I PROP).
Lemma monPred_all_elim P : monPred_all P ⊢ P.
Proof. unseal. split=>?. apply bi.forall_elim. Qed.
Lemma monPred_all_idemp P : monPred_all (monPred_all P) ⊣⊢ monPred_all P.
Proof.
  apply bi.equiv_spec; split; [by apply monPred_all_elim|].
  unseal. split=>i /=. by apply bi.forall_intro=>_.
Qed.

Lemma monPred_all_and P Q : monPred_all (P ∧ Q) ⊣⊢ monPred_all P ∧ monPred_all Q.
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=.
  - apply bi.and_intro; do 2 f_equiv. apply bi.and_elim_l. apply bi.and_elim_r.
  - apply bi.forall_intro=>?. by rewrite !bi.forall_elim.
Qed.
Lemma monPred_all_sep_2 P Q : monPred_all P ∗ monPred_all Q ⊢ monPred_all (P ∗ Q).
Proof. unseal. split=>i /=. apply bi.forall_intro=>?. by rewrite !bi.forall_elim. Qed.
Lemma monPred_all_sep `{BiIndexBottom bot} P Q :
  monPred_all (P ∗ Q) ⊣⊢ monPred_all P ∗ monPred_all Q.
Proof.
  apply bi.equiv_spec, conj, monPred_all_sep_2. unseal. split=>i /=.
  rewrite (bi.forall_elim bot). by f_equiv; apply bi.forall_intro=>j; f_equiv.
Qed.
Lemma monPred_all_embed (P : PROP) : monPred_all ⎡P⎤ ⊣⊢ ⎡P⎤.
Proof.
  apply bi.equiv_spec; split; unseal; split=>i /=.
  by rewrite (bi.forall_elim inhabitant). by apply bi.forall_intro.
Qed.

Lemma monPred_ex_intro P : P ⊢ monPred_ex P.
Proof. unseal. split=>?. apply bi.exist_intro. Qed.
Lemma monPred_ex_idemp P : monPred_ex (monPred_ex P) ⊣⊢ monPred_ex P.
Proof.
  apply bi.equiv_spec; split; [|by apply monPred_ex_intro].
  unseal. split=>i /=. by apply bi.exist_elim=>_.
Qed.

Lemma monPred_in_intro P : P ⊢ ∃ i, monPred_in i ∧ ⎡P i⎤.
Proof.
  unseal. split=>i /=.
  rewrite /= -(bi.exist_intro i). apply bi.and_intro=>//. by apply bi.pure_intro.
Qed.
Lemma monPred_in_elim P i : monPred_in i ∧ ⎡P i⎤ ⊢ P .
Proof.
  unseal. split=>i' /=.
  eapply bi.pure_elim; [apply bi.and_elim_l|]=>?. rewrite bi.and_elim_r. by f_equiv.
Qed.

Lemma monPred_equivI {PROP' : bi} P Q :
  bi_internal_eq (PROP:=PROP') P Q ⊣⊢ ∀ i, P i ≡ Q i.
Proof.
  apply bi.equiv_spec. split.
  - apply bi.forall_intro=>?. apply (bi.f_equiv (flip monPred_at _)).
  - by rewrite -{2}(sig_monPred_sig P) -{2}(sig_monPred_sig Q)
               -bi.f_equiv -bi.sig_equivI !bi.ofe_fun_equivI.
Qed.

Lemma monPred_bupd_embed `{BUpdFacts PROP} (P : PROP) :
  ⎡|==> P⎤ ⊣⊢ bupd (PROP:=monPredI) ⎡P⎤.
Proof.
  unseal. split=>i /=. setoid_rewrite bi.pure_impl_forall. apply bi.equiv_spec; split.
  - by do 2 apply bi.forall_intro=>?.
  - rewrite !bi.forall_elim //.
Qed.

(** Big op *)

Global Instance monPred_at_monoid_and_homomorphism i :
  MonoidHomomorphism bi_and bi_and (≡) (flip monPred_at i).
Proof. split; [split|]; try apply _. apply monPred_at_and. apply monPred_at_pure. Qed.
Global Instance monPred_at_monoid_or_homomorphism :
  MonoidHomomorphism bi_or bi_or (≡) (flip monPred_at i).
Proof. split; [split|]; try apply _. apply monPred_at_or. apply monPred_at_pure. Qed.
Global Instance monPred_at_monoid_sep_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (≡) (flip monPred_at i).
Proof. split; [split|]; try apply _. apply monPred_at_sep. apply monPred_at_emp. Qed.

Lemma monPred_at_big_sepL {A} i (Φ : nat → A → monPredI) l :
  ([∗ list] k↦x ∈ l, Φ k x) i ⊣⊢ [∗ list] k↦x ∈ l, Φ k x i.
Proof. apply (big_opL_commute (flip monPred_at i)). Qed.
Lemma monPred_at_big_sepM `{Countable K} {A} i (Φ : K → A → monPredI) (m : gmap K A) :
  ([∗ map] k↦x ∈ m, Φ k x) i ⊣⊢ [∗ map] k↦x ∈ m, Φ k x i.
Proof. apply (big_opM_commute (flip monPred_at i)). Qed.
Lemma monPred_at_big_sepS `{Countable A} i (Φ : A → monPredI) (X : gset A) :
  ([∗ set] y ∈ X, Φ y) i ⊣⊢ [∗ set] y ∈ X, Φ y i.
Proof. apply (big_opS_commute (flip monPred_at i)). Qed.
Lemma monPred_at_big_sepMS `{Countable A} i (Φ : A → monPredI) (X : gmultiset A) :
  ([∗ mset] y ∈ X, Φ y) i ⊣⊢ ([∗ mset] y ∈ X, Φ y i).
Proof. apply (big_opMS_commute (flip monPred_at i)). Qed.

Global Instance monPred_all_monoid_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) monPred_all.
Proof.
  split; [split|]; try apply _. apply monPred_all_and. apply monPred_all_embed.
Qed.
Global Instance monPred_all_monoid_sep_entails_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) monPred_all.
Proof.
  split; [split|]; try apply _. apply monPred_all_sep_2. by rewrite monPred_all_embed.
Qed.
Global Instance monPred_all_monoid_sep_homomorphism `{BiIndexBottom bot} :
  MonoidHomomorphism bi_sep bi_sep (≡) monPred_all.
Proof.
  split; [split|]; try apply _. apply monPred_all_sep. by rewrite monPred_all_embed.
Qed.

Lemma monPred_all_big_sepL_entails {A} (Φ : nat → A → monPredI) l :
  ([∗ list] k↦x ∈ l, monPred_all (Φ k x)) ⊢ monPred_all ([∗ list] k↦x ∈ l, Φ k x).
Proof. apply (big_opL_commute monPred_all (R:=flip (⊢))). Qed.
Lemma monPred_all_big_sepM_entails
      `{Countable K} {A} (Φ : K → A → monPredI) (m : gmap K A) :
  ([∗ map] k↦x ∈ m, monPred_all (Φ k x)) ⊢ monPred_all ([∗ map] k↦x ∈ m, Φ k x).
Proof. apply (big_opM_commute monPred_all (R:=flip (⊢))). Qed.
Lemma monPred_all_big_sepS_entails `{Countable A} (Φ : A → monPredI) (X : gset A) :
  ([∗ set] y ∈ X, monPred_all (Φ y)) ⊢ monPred_all ([∗ set] y ∈ X, Φ y).
Proof. apply (big_opS_commute monPred_all (R:=flip (⊢))). Qed.
Lemma monPred_all_big_sepMS_entails `{Countable A} (Φ : A → monPredI) (X : gmultiset A) :
  ([∗ mset] y ∈ X, monPred_all (Φ y)) ⊢ monPred_all ([∗ mset] y ∈ X, Φ y).
Proof. apply (big_opMS_commute monPred_all (R:=flip (⊢))). Qed.

Lemma monPred_all_big_sepL `{BiIndexBottom bot} {A} (Φ : nat → A → monPredI) l :
  monPred_all ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, monPred_all (Φ k x)).
Proof. apply (big_opL_commute _). Qed.
Lemma monPred_all_big_sepM `{BiIndexBottom bot} `{Countable K} {A}
      (Φ : K → A → monPredI) (m : gmap K A) :
  monPred_all ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, monPred_all (Φ k x)).
Proof. apply (big_opM_commute _). Qed.
Lemma monPred_all_big_sepS `{BiIndexBottom bot} `{Countable A}
      (Φ : A → monPredI) (X : gset A) :
  monPred_all ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, monPred_all (Φ y)).
Proof. apply (big_opS_commute _). Qed.
Lemma monPred_all_big_sepMS `{BiIndexBottom bot} `{Countable A}
      (Φ : A → monPredI) (X : gmultiset A) :
  monPred_all ([∗ mset] y ∈ X, Φ y) ⊣⊢  ([∗ mset] y ∈ X, monPred_all (Φ y)).
Proof. apply (big_opMS_commute _). Qed.
End bi_facts.

Section sbi_facts.
Context {I : biIndex} {PROP : sbi}.
Local Notation monPred := (monPred I PROP).
Local Notation monPredSI := (monPredSI I PROP).
Implicit Types i : I.
Implicit Types P Q : monPred.

Global Instance monPred_at_timeless P i : Timeless P → Timeless (P i).
Proof. move => [] /(_ i). unfold Timeless. by unseal. Qed.
Global Instance monPred_in_timeless i0 : Timeless (@monPred_in I PROP i0).
Proof. split => ? /=. unseal. apply timeless, _. Qed.
Global Instance monPred_all_timeless P :
  Timeless P → Timeless (@monPred_all I PROP P).
Proof.
  move=>[]. unfold Timeless. unseal=>Hti. split=> ? /=.
  by apply timeless, bi.forall_timeless.
Qed.
Global Instance monPred_ex_timeless P :
  Timeless P → Timeless (@monPred_ex I PROP P).
Proof.
  move=>[]. unfold Timeless. unseal=>Hti. split=> ? /=.
  by apply timeless, bi.exist_timeless.
Qed.

Global Instance monPred_sbi_embedding : SbiEmbedding PROP monPredSI.
Proof. split; try apply _. by unseal. Qed.

Global Instance monPred_fupd_facts `{FUpdFacts PROP} : FUpdFacts monPredSI.
Proof.
  split; first apply _; unseal; unfold monPred_fupd_def, monPred_upclosed.
  - intros E1 E2 n P Q HPQ. split=>/= i. by repeat f_equiv.
  - intros E1 E2 P HE12. split=>/= i.
    do 2 setoid_rewrite bi.pure_impl_forall. do 2 apply bi.forall_intro=>?.
    rewrite (fupd_intro_mask E1 E2 (P i)) //. f_equiv.
    do 2 apply bi.forall_intro=>?. do 2 f_equiv. by etrans.
  - intros E P. split=>/= i. by setoid_rewrite bupd_fupd.
  - intros E1 E2 P. split=>/= i. etrans; [apply bi.equiv_entails, bi.except_0_forall|].
    do 2 f_equiv. rewrite bi.pure_impl_forall bi.except_0_forall. do 2 f_equiv.
    by apply except_0_fupd.
  - intros E1 E2 P Q HPQ. split=>/= i. by repeat f_equiv.
  - intros E1 E2 E3 P. split=>/= i. do 3 f_equiv. rewrite -(fupd_trans _ _ _ (P _))
      bi.forall_elim bi.pure_impl_forall bi.forall_elim //.
  - intros E1 E2 Ef P HE1f. split=>/= i. do 3 f_equiv. rewrite -fupd_mask_frame_r' //
      bi.forall_elim bi.pure_impl_forall bi.forall_elim //.
  - intros E1 E2 P Q. split=>/= i. setoid_rewrite bi.pure_impl_forall.
    do 2 setoid_rewrite bi.sep_forall_r. setoid_rewrite fupd_frame_r.
    by repeat f_equiv.
  - intros E1 E2 E2' P Q ? HE12. split=>/= i. repeat setoid_rewrite bi.pure_impl_forall.
    do 4 f_equiv. rewrite 4?bi.forall_elim // fupd_plain' //.
    apply bi.wand_intro_r. rewrite bi.wand_elim_l. do 2 apply bi.forall_intro=>?.
    repeat f_equiv=>//. do 2 apply bi.forall_intro=>?. repeat f_equiv. by etrans.
  - intros E P ?. split=>/= i. setoid_rewrite bi.pure_impl_forall.
    do 2 setoid_rewrite bi.later_forall. do 4 f_equiv. apply later_fupd_plain, _.
Qed.

(** Unfolding lemmas *)

Lemma monPred_at_later i P : (▷ P) i ⊣⊢ ▷ P i.
Proof. by unseal. Qed.
Lemma monPred_at_fupd `{FUpdFacts PROP} i E1 E2 P :
  (|={E1,E2}=> P) i ⊣⊢ |={E1,E2}=> P i.
Proof.
  unseal. setoid_rewrite bi.pure_impl_forall. apply bi.equiv_spec; split.
  - rewrite !bi.forall_elim //.
  - do 2 apply bi.forall_intro=>?. by do 2 f_equiv.
Qed.
Lemma monPred_at_except_0 i P : (◇ P) i ⊣⊢ ◇ P i.
Proof. by unseal. Qed.

Lemma monPred_fupd_embed `{FUpdFacts PROP} E1 E2 (P : PROP) :
  ⎡|={E1,E2}=> P⎤ ⊣⊢ fupd E1 E2 (PROP:=monPred) ⎡P⎤.
Proof.
  unseal. split=>i /=. setoid_rewrite bi.pure_impl_forall. apply bi.equiv_spec; split.
  - by do 2 apply bi.forall_intro=>?.
  - rewrite !bi.forall_elim //.
Qed.
End sbi_facts.
