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

(* We may want to instantiate monPred with the reflexivity relation in
   the case where there is no relevent order. In that case, there is
   no bottom element, so that we do not want to force any BI index to
   have one. *)
Class BiIndexBottom {I : biIndex} (bot : I) :=
  bi_index_bot i : bot ⊑ i.

Section Ofe_Cofe.
Context {I : biIndex} {PROP : bi}.
Implicit Types i : I.

Record monPred :=
  MonPred { monPred_at :> I → PROP;
            monPred_mono : Proper ((⊑) ==> (⊢)) monPred_at }.
Local Existing Instance monPred_mono.

Bind Scope monPred with bi.

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
Definition monPred_embed : Embed PROP monPred := unseal monPred_embed_aux.
Definition monPred_embed_eq : @embed _ _ monPred_embed = _ := seal_eq _.

Definition monPred_emp_def : monPred := MonPred (λ _, emp)%I _.
Definition monPred_emp_aux : seal (@monPred_emp_def). by eexists. Qed.
Definition monPred_emp := unseal monPred_emp_aux.
Definition monPred_emp_eq : @monPred_emp = _ := seal_eq _.

Definition monPred_pure_def (φ : Prop) : monPred := MonPred (λ _, ⌜φ⌝)%I _.
Definition monPred_pure_aux : seal (@monPred_pure_def). by eexists. Qed.
Definition monPred_pure := unseal monPred_pure_aux.
Definition monPred_pure_eq : @monPred_pure = _ := seal_eq _.

Definition monPred_objectively_def P : monPred := MonPred (λ _, ∀ i, P i)%I _.
Definition monPred_objectively_aux : seal (@monPred_objectively_def). by eexists. Qed.
Definition monPred_objectively := unseal monPred_objectively_aux.
Definition monPred_objectively_eq : @monPred_objectively = _ := seal_eq _.

Definition monPred_subjectively_def P : monPred := MonPred (λ _, ∃ i, P i)%I _.
Definition monPred_subjectively_aux : seal (@monPred_subjectively_def). by eexists. Qed.
Definition monPred_subjectively := unseal monPred_subjectively_aux.
Definition monPred_subjectively_eq : @monPred_subjectively = _ := seal_eq _.

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

Definition monPred_bupd_def `{BUpd PROP} (P : monPred) : monPred :=
  (* monPred_upclosed is not actually needed, since bupd is always
     monotone. However, this depends on BUpdFacts, and we do not want
     this definition to depend on BUpdFacts to avoid having proofs
     terms in logical terms. *)
  monPred_upclosed (λ i, |==> P i)%I.
Definition monPred_bupd_aux `{BUpd PROP} : seal monPred_bupd_def. by eexists. Qed.
Definition monPred_bupd `{BUpd PROP} : BUpd _ := unseal monPred_bupd_aux.
Definition monPred_bupd_eq `{BUpd PROP} : @bupd _ monPred_bupd = _ := seal_eq _.
End Bi.

Arguments monPred_objectively {_ _} _%I.
Arguments monPred_subjectively {_ _} _%I.
Notation "'<obj>' P" := (monPred_objectively P) (at level 20, right associativity) : bi_scope.
Notation "'<subj>' P" := (monPred_subjectively P) (at level 20, right associativity) : bi_scope.

Section Sbi.
Context {I : biIndex} {PROP : sbi}.
Implicit Types i : I.
Notation monPred := (monPred I PROP).
Implicit Types P Q : monPred.

Definition monPred_plainly_def `{BiPlainly PROP} P : monPred := MonPred (λ _, ∀ i, ■ (P i))%I _.
Definition monPred_plainly_aux `{BiPlainly PROP} : seal monPred_plainly_def. by eexists. Qed.
Definition monPred_plainly `{BiPlainly PROP} : Plainly _ := unseal monPred_plainly_aux.
Definition monPred_plainly_eq `{BiPlainly PROP} : @plainly _ monPred_plainly = _ := seal_eq _.

Definition monPred_internal_eq_def (A : ofeT) (a b : A) : monPred := MonPred (λ _, a ≡ b)%I _.
Definition monPred_internal_eq_aux : seal (@monPred_internal_eq_def). by eexists. Qed.
Definition monPred_internal_eq := unseal monPred_internal_eq_aux.
Definition monPred_internal_eq_eq : @monPred_internal_eq = _ := seal_eq _.

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
Definition monPred_fupd `{FUpd PROP} : FUpd _ := unseal monPred_fupd_aux.
Definition monPred_fupd_eq `{FUpd PROP} : @fupd _ monPred_fupd = _ := seal_eq _.
End Sbi.

Module MonPred.
Definition unseal_eqs :=
  (@monPred_and_eq, @monPred_or_eq, @monPred_impl_eq,
   @monPred_forall_eq, @monPred_exist_eq,
   @monPred_sep_eq, @monPred_wand_eq,
   @monPred_persistently_eq, @monPred_later_eq, @monPred_internal_eq_eq, @monPred_in_eq,
   @monPred_embed_eq, @monPred_emp_eq, @monPred_pure_eq, @monPred_plainly_eq,
   @monPred_objectively_eq, @monPred_subjectively_eq, @monPred_bupd_eq, @monPred_fupd_eq).
Ltac unseal :=
  unfold bi_affinely, bi_absorbingly, sbi_except_0, bi_pure, bi_emp,
         monPred_upclosed, bi_and, bi_or,
         bi_impl, bi_forall, bi_exist, sbi_internal_eq, bi_sep, bi_wand,
         bi_persistently, bi_affinely, sbi_later;
  simpl;
  unfold sbi_emp, sbi_pure, sbi_and, sbi_or, sbi_impl, sbi_forall, sbi_exist,
         sbi_internal_eq, sbi_sep, sbi_wand, sbi_persistently;
  simpl;
  rewrite !unseal_eqs /=.
End MonPred.
Import MonPred.

Section canonical_bi.
Context (I : biIndex) (PROP : bi).

Lemma monPred_bi_mixin : BiMixin (PROP:=monPred I PROP)
  monPred_entails monPred_emp monPred_pure monPred_and monPred_or
  monPred_impl monPred_forall monPred_exist monPred_sep monPred_wand
  monPred_persistently.
Proof.
  split; try unseal; try by (split=> ? /=; repeat f_equiv).
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
  - intros P Q [?]. split=> i /=. by f_equiv.
  - intros P. split=> i. by apply bi.persistently_idemp_2.
  - intros P. split=> i. by apply bi.persistently_emp_intro.
  - intros A Ψ. split=> i. by apply bi.persistently_forall_2.
  - intros A Ψ. split=> i. by apply bi.persistently_exist_1.
  - intros P Q. split=> i. apply bi.sep_elim_l, _.
  - intros P Q. split=> i. by apply bi.persistently_and_sep_elim.
Qed.

Canonical Structure monPredI : bi :=
  {| bi_ofe_mixin := monPred_ofe_mixin; bi_bi_mixin := monPred_bi_mixin |}.
End canonical_bi.

Section canonical_sbi.
Context (I : biIndex) (PROP : sbi).

Lemma monPred_sbi_mixin :
  SbiMixin (PROP:=monPred I PROP) monPred_entails monPred_pure
           monPred_or monPred_impl monPred_forall monPred_exist
           monPred_sep monPred_persistently monPred_internal_eq monPred_later.
Proof.
  split; unseal.
  - intros n P Q HPQ. split=> i /=.
    apply bi.later_contractive. destruct n as [|n]=> //. by apply HPQ.
  - by split=> ? /=; repeat f_equiv.
  - intros A P a. split=> i. by apply bi.internal_eq_refl.
  - intros A a b Ψ ?. split=> i /=.
    setoid_rewrite bi.pure_impl_forall. do 2 apply bi.forall_intro => ?.
    erewrite (bi.internal_eq_rewrite _ _ (flip Ψ _)) => //=. solve_proper.
  - intros A1 A2 f g. split=> i. by apply bi.fun_ext.
  - intros A P x y. split=> i. by apply bi.sig_eq.
  - intros A a b ?. split=> i. by apply bi.discrete_eq_1.
  - intros A x y. split=> i. by apply bi.later_eq_1.
  - intros A x y. split=> i. by apply bi.later_eq_2.
  - intros P Q [?]. split=> i. by apply bi.later_mono.
  - intros P. split=> i /=.
    setoid_rewrite bi.pure_impl_forall. rewrite /= !bi.forall_elim //. by apply bi.löb.
  - intros A Ψ. split=> i. by apply bi.later_forall_2.
  - intros A Ψ. split=> i. by apply bi.later_exist_false.
  - intros P Q. split=> i. by apply bi.later_sep_1.
  - intros P Q. split=> i. by apply bi.later_sep_2.
  - intros P. split=> i. by apply bi.later_persistently_1.
  - intros P. split=> i. by apply bi.later_persistently_2.
  - intros P. split=> i /=. rewrite -bi.forall_intro. apply bi.later_false_em.
    intros j. rewrite bi.pure_impl_forall. apply bi.forall_intro=> Hij. by rewrite Hij.
Qed.

Canonical Structure monPredSI : sbi :=
  {| sbi_ofe_mixin := monPred_ofe_mixin; sbi_bi_mixin := monPred_bi_mixin I PROP;
     sbi_sbi_mixin := monPred_sbi_mixin |}.

Lemma monPred_plainly_mixin `{BiPlainly PROP} : BiPlainlyMixin monPredSI monPred_plainly.
Proof.
  split; unseal.
  - by (split=> ? /=; repeat f_equiv).
  - intros P Q [?]. split=> i /=. by do 3 f_equiv.
  - intros P. split=> i /=. by rewrite bi.forall_elim plainly_elim_persistently.
  - intros P. split=> i /=. repeat setoid_rewrite <-plainly_forall.
    rewrite -plainly_idemp_2. f_equiv. by apply bi.forall_intro=>_.
  - intros A Ψ. split=> i /=. apply bi.forall_intro=> j.
    rewrite plainly_forall. apply bi.forall_intro=> a.
    by rewrite !bi.forall_elim.
  - intros P Q. split=> i /=. repeat setoid_rewrite bi.pure_impl_forall.
    repeat setoid_rewrite <-plainly_forall.
    repeat setoid_rewrite bi.persistently_forall. do 4 f_equiv.
    apply persistently_impl_plainly.
  - intros P Q. split=> i /=.
    repeat setoid_rewrite bi.pure_impl_forall. rewrite 2!bi.forall_elim //.
    repeat setoid_rewrite <-plainly_forall.
    setoid_rewrite plainly_impl_plainly. f_equiv.
    do 3 apply bi.forall_intro => ?. f_equiv. rewrite bi.forall_elim //.
  - intros P. split=> i /=. apply bi.forall_intro=>_. by apply plainly_emp_intro.
  - intros P Q. split=> i. apply bi.sep_elim_l, _.
  - intros P Q. split=> i /=.
    rewrite <-(sig_monPred_sig P), <-(sig_monPred_sig Q), <-(bi.f_equiv _).
    rewrite -bi.sig_equivI /= -bi.fun_ext. f_equiv=> j.
    rewrite -prop_ext !(bi.forall_elim j) !bi.pure_impl_forall
            !bi.forall_elim //.
  - intros P. split=> i /=.
    rewrite bi.later_forall. f_equiv=> j. by rewrite -later_plainly_1.
  - intros P. split=> i /=.
    rewrite bi.later_forall. f_equiv=> j. by rewrite -later_plainly_2.
Qed.
Global Instance monPred_plainlyC `{BiPlainly PROP} : BiPlainly monPredSI :=
  {| bi_plainly_mixin := monPred_plainly_mixin |}.

Global Instance monPred_plainly_exist `{BiPlainly PROP} `{@BiIndexBottom I bot} :
  BiPlainlyExist PROP → BiPlainlyExist monPredSI.
Proof.
  split=>?/=. unseal. rewrite (bi.forall_elim bot) plainly_exist_1. do 2 f_equiv.
  apply bi.forall_intro=>?. by do 2 f_equiv.
Qed.
End canonical_sbi.

Class Objective {I : biIndex} {PROP : bi} (P : monPred I PROP) :=
  objective_at i j : P i -∗ P j.
Arguments Objective {_ _} _%I.
Arguments objective_at {_ _} _%I {_}.
Hint Mode Objective + + ! : typeclass_instances.
Instance: Params (@Objective) 2.

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
Global Instance monPred_at_flip_mono :
  Proper (flip (⊢) ==> flip (⊑) ==> flip (⊢)) monPred_at.
Proof. solve_proper. Qed.

Global Instance monPred_in_proper (R : relation I) :
  Proper (R ==> R ==> iff) (⊑) → Reflexive R →
  Proper (R ==> (≡)) (@monPred_in I PROP).
Proof. unseal. split. solve_proper. Qed.
Global Instance monPred_in_mono : Proper (flip (⊑) ==> (⊢)) (@monPred_in I PROP).
Proof. unseal. split. solve_proper. Qed.
Global Instance monPred_in_flip_mono : Proper ((⊑) ==> flip (⊢)) (@monPred_in I PROP).
Proof. solve_proper. Qed.

Global Instance monPred_positive : BiPositive PROP → BiPositive monPredI.
Proof. split => ?. unseal. apply bi_positive. Qed.
Global Instance monPred_affine : BiAffine PROP → BiAffine monPredI.
Proof. split => ?. unseal. by apply affine. Qed.

Global Instance monPred_at_persistent P i : Persistent P → Persistent (P i).
Proof. move => [] /(_ i). by unseal. Qed.
Global Instance monPred_at_absorbing P i : Absorbing P → Absorbing (P i).
Proof. move => [] /(_ i). unfold Absorbing. by unseal. Qed.
Global Instance monPred_at_affine P i : Affine P → Affine (P i).
Proof. move => [] /(_ i). unfold Affine. by unseal. Qed.

(* Note that monPred_in is *not* Plain, because it does depend on the
   index. *)
Global Instance monPred_in_persistent i :
  Persistent (@monPred_in I PROP i).
Proof. unfold Persistent. unseal; split => ?. by apply bi.pure_persistent. Qed.
Global Instance monPred_in_absorbing i :
  Absorbing (@monPred_in I PROP i).
Proof. unfold Absorbing. unseal. split=> ? /=. apply absorbing, _. Qed.

Definition monPred_embedding_mixin : BiEmbedMixin PROP monPredI monPred_embed.
Proof.
  split; try apply _; unseal; try done.
  - move =>?? /= [/(_ inhabitant) ?] //.
  - split=>? /=.
    by rewrite bi.forall_elim bi.pure_impl_forall bi.forall_elim.
  - split=>? /=.
    by rewrite bi.forall_elim bi.pure_impl_forall bi.forall_elim.
Qed.
Global Instance monPred_bi_embed : BiEmbed PROP monPredI :=
  {| bi_embed_mixin := monPred_embedding_mixin |}.

Lemma monPred_emp_unfold : emp%I = ⎡emp : PROP⎤%I.
Proof. by unseal. Qed.
Lemma monPred_pure_unfold : bi_pure = λ φ, ⎡ ⌜ φ ⌝ : PROP⎤%I.
Proof. by unseal. Qed.
Lemma monPred_objectively_unfold : monPred_objectively = λ P, ⎡∀ i, P i⎤%I.
Proof. by unseal. Qed.
Lemma monPred_subjectively_unfold : monPred_subjectively = λ P, ⎡∃ i, P i⎤%I.
Proof. by unseal. Qed.

Global Instance monPred_objectively_ne : NonExpansive (@monPred_objectively I PROP).
Proof. rewrite monPred_objectively_unfold. solve_proper. Qed.
Global Instance monPred_objectively_proper : Proper ((≡) ==> (≡)) (@monPred_objectively I PROP).
Proof. apply (ne_proper _). Qed.
Lemma monPred_objectively_mono P Q : (P ⊢ Q) → (<obj> P ⊢ <obj> Q).
Proof. rewrite monPred_objectively_unfold. solve_proper. Qed.
Global Instance monPred_objectively_mono' : Proper ((⊢) ==> (⊢)) (@monPred_objectively I PROP).
Proof. intros ???. by apply monPred_objectively_mono. Qed.
Global Instance monPred_objectively_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@monPred_objectively I PROP).
Proof. intros ???. by apply monPred_objectively_mono. Qed.

Global Instance monPred_objectively_persistent P : Persistent P → Persistent (<obj> P).
Proof. rewrite monPred_objectively_unfold. apply _. Qed.
Global Instance monPred_objectively_absorbing P : Absorbing P → Absorbing (<obj> P).
Proof. rewrite monPred_objectively_unfold. apply _. Qed.
Global Instance monPred_objectively_affine P : Affine P → Affine (<obj> P).
Proof. rewrite monPred_objectively_unfold. apply _. Qed.

Global Instance monPred_subjectively_ne : NonExpansive (@monPred_subjectively I PROP).
Proof. rewrite monPred_subjectively_unfold. solve_proper. Qed.
Global Instance monPred_subjectively_proper : Proper ((≡) ==> (≡)) (@monPred_subjectively I PROP).
Proof. apply (ne_proper _). Qed.
Lemma monPred_subjectively_mono P Q : (P ⊢ Q) → <subj> P ⊢ <subj> Q.
Proof. rewrite monPred_subjectively_unfold. solve_proper. Qed.
Global Instance monPred_subjectively_mono' : Proper ((⊢) ==> (⊢)) (@monPred_subjectively I PROP).
Proof. intros ???. by apply monPred_subjectively_mono. Qed.
Global Instance monPred_subjectively_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@monPred_subjectively I PROP).
Proof. intros ???. by apply monPred_subjectively_mono. Qed.

Global Instance monPred_subjectively_persistent P : Persistent P → Persistent (<subj> P).
Proof. rewrite monPred_subjectively_unfold. apply _. Qed.
Global Instance monPred_subjectively_absorbing P : Absorbing P → Absorbing (<subj> P).
Proof. rewrite monPred_subjectively_unfold. apply _. Qed.
Global Instance monPred_subjectively_affine P : Affine P → Affine (<subj> P).
Proof. rewrite monPred_subjectively_unfold. apply _. Qed.

(** monPred_at unfolding laws *)
Lemma monPred_at_embed i (P : PROP) : monPred_at ⎡P⎤ i ⊣⊢ P.
Proof. by unseal. Qed.
Lemma monPred_at_pure i (φ : Prop) : monPred_at ⌜φ⌝ i ⊣⊢ ⌜φ⌝.
Proof. by unseal. Qed.
Lemma monPred_at_emp i : monPred_at emp i ⊣⊢ emp.
Proof. by unseal. Qed.
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
Lemma monPred_at_objectively i P : (<obj> P) i ⊣⊢ ∀ j, P j.
Proof. by unseal. Qed.
Lemma monPred_at_subjectively i P : (<subj> P) i ⊣⊢ ∃ j, P j.
Proof. by unseal. Qed.
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

(* Laws for monPred_objectively and of Objective. *)
Lemma monPred_objectively_elim P : <obj> P ⊢ P.
Proof. rewrite monPred_objectively_unfold. unseal. split=>?. apply bi.forall_elim. Qed.
Lemma monPred_objectively_idemp P : <obj> <obj> P ⊣⊢ <obj> P.
Proof.
  apply bi.equiv_spec; split; [by apply monPred_objectively_elim|].
  unseal. split=>i /=. by apply bi.forall_intro=>_.
Qed.

Lemma monPred_objectively_forall {A} (Φ : A → monPred) : <obj> (∀ x, Φ x) ⊣⊢ ∀ x, <obj> (Φ x).
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=;
    do 2 apply bi.forall_intro=>?; by do 2 rewrite bi.forall_elim.
Qed.
Lemma monPred_objectively_and P Q : <obj> (P ∧ Q) ⊣⊢ <obj> P ∧ <obj> Q.
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=.
  - apply bi.and_intro; do 2 f_equiv. apply bi.and_elim_l. apply bi.and_elim_r.
  - apply bi.forall_intro=>?. by rewrite !bi.forall_elim.
Qed.
Lemma monPred_objectively_exist {A} (Φ : A → monPred) :
  (∃ x, <obj> (Φ x)) ⊢ <obj> (∃ x, (Φ x)).
Proof. apply bi.exist_elim=>?. f_equiv. apply bi.exist_intro. Qed.
Lemma monPred_objectively_or P Q : <obj> P ∨ <obj> Q ⊢ <obj> (P ∨ Q).
Proof. apply bi.or_elim; f_equiv. apply bi.or_intro_l. apply bi.or_intro_r. Qed.

Lemma monPred_objectively_sep_2 P Q : <obj> P ∗ <obj> Q ⊢ <obj> (P ∗ Q).
Proof. unseal. split=>i /=. apply bi.forall_intro=>?. by rewrite !bi.forall_elim. Qed.
Lemma monPred_objectively_sep `{BiIndexBottom bot} P Q : <obj> (P ∗ Q) ⊣⊢ <obj> P ∗ <obj> Q.
Proof.
  apply bi.equiv_spec, conj, monPred_objectively_sep_2. unseal. split=>i /=.
  rewrite (bi.forall_elim bot). by f_equiv; apply bi.forall_intro=>j; f_equiv.
Qed.
Lemma monPred_objectively_embed (P : PROP) : <obj> ⎡P⎤ ⊣⊢ ⎡P⎤.
Proof.
  apply bi.equiv_spec; split; unseal; split=>i /=.
  by rewrite (bi.forall_elim inhabitant). by apply bi.forall_intro.
Qed.
Lemma monPred_objectively_emp : <obj> (emp : monPred) ⊣⊢ emp.
Proof. rewrite monPred_emp_unfold. apply monPred_objectively_embed. Qed.
Lemma monPred_objectively_pure φ : <obj> (⌜ φ ⌝ : monPred) ⊣⊢ ⌜ φ ⌝.
Proof. rewrite monPred_pure_unfold. apply monPred_objectively_embed. Qed.

Lemma monPred_subjectively_intro P : P ⊢ <subj> P.
Proof. unseal. split=>?. apply bi.exist_intro. Qed.

Lemma monPred_subjectively_forall {A} (Φ : A → monPred) :
  (<subj> (∀ x, Φ x)) ⊢ ∀ x, <subj> (Φ x).
Proof. apply bi.forall_intro=>?. f_equiv. apply bi.forall_elim. Qed.
Lemma monPred_subjectively_and P Q : <subj> (P ∧ Q) ⊢ <subj> P ∧ <subj> Q.
Proof. apply bi.and_intro; f_equiv. apply bi.and_elim_l. apply bi.and_elim_r. Qed.
Lemma monPred_subjectively_exist {A} (Φ : A → monPred) : <subj> (∃ x, Φ x) ⊣⊢ ∃ x, <subj> (Φ x).
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=;
    do 2 apply bi.exist_elim=>?; by do 2 rewrite -bi.exist_intro.
Qed.
Lemma monPred_subjectively_or P Q : <subj> (P ∨ Q) ⊣⊢ <subj> P ∨ <subj> Q.
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=.
  - apply bi.exist_elim=>?. by rewrite -!bi.exist_intro.
  - apply bi.or_elim; do 2 f_equiv. apply bi.or_intro_l. apply bi.or_intro_r.
Qed.

Lemma monPred_subjectively_sep P Q : <subj> (P ∗ Q) ⊢ <subj> P ∗ <subj> Q.
Proof. unseal. split=>i /=. apply bi.exist_elim=>?. by rewrite -!bi.exist_intro. Qed.

Lemma monPred_subjectively_idemp P : <subj> <subj> P ⊣⊢ <subj> P.
Proof.
  apply bi.equiv_spec; split; [|by apply monPred_subjectively_intro].
  unseal. split=>i /=. by apply bi.exist_elim=>_.
Qed.

Lemma objective_objectively P `{!Objective P} : P ⊢ <obj> P.
Proof.
  rewrite monPred_objectively_unfold /= embed_forall. apply bi.forall_intro=>?.
  split=>?. unseal. apply objective_at, _.
Qed.
Lemma objective_subjectively P `{!Objective P} : <subj> P ⊢ P.
Proof.
  rewrite monPred_subjectively_unfold /= embed_exist. apply bi.exist_elim=>?.
  split=>?. unseal. apply objective_at, _.
Qed.

Global Instance embed_objective (P : PROP) : @Objective I PROP ⎡P⎤.
Proof. intros ??. by unseal. Qed.
Global Instance pure_objective φ : @Objective I PROP ⌜φ⌝.
Proof. intros ??. by unseal. Qed.
Global Instance emp_objective : @Objective I PROP emp.
Proof. intros ??. by unseal. Qed.
Global Instance objectively_objective P : Objective (<obj> P).
Proof. intros ??. by unseal. Qed.
Global Instance subjectively_objective P : Objective (<subj> P).
Proof. intros ??. by unseal. Qed.

Global Instance and_objective P Q `{!Objective P, !Objective Q} : Objective (P ∧ Q).
Proof. intros i j. unseal. by rewrite !(objective_at _ i j). Qed.
Global Instance or_objective P Q `{!Objective P, !Objective Q} : Objective (P ∨ Q).
Proof. intros i j. by rewrite !monPred_at_or !(objective_at _ i j). Qed.
Global Instance impl_objective P Q `{!Objective P, !Objective Q} : Objective (P → Q).
Proof.
  intros i j. unseal. rewrite (bi.forall_elim i) bi.pure_impl_forall.
  rewrite bi.forall_elim //. apply bi.forall_intro=> k.
  rewrite bi.pure_impl_forall. apply bi.forall_intro=>_.
  rewrite (objective_at Q i). by rewrite (objective_at P k).
Qed.
Global Instance forall_objective {A} Φ {H : ∀ x : A, Objective (Φ x)} :
  @Objective I PROP (∀ x, Φ x)%I.
Proof. intros i j. unseal. do 2 f_equiv. by apply objective_at. Qed.
Global Instance exists_objective {A} Φ {H : ∀ x : A, Objective (Φ x)} :
  @Objective I PROP (∃ x, Φ x)%I.
Proof. intros i j. unseal. do 2 f_equiv. by apply objective_at. Qed.

Global Instance sep_objective P Q `{!Objective P, !Objective Q} : Objective (P ∗ Q).
Proof. intros i j. unseal. by rewrite !(objective_at _ i j). Qed.
Global Instance wand_objective P Q `{!Objective P, !Objective Q} : Objective (P -∗ Q).
Proof.
  intros i j. unseal. rewrite (bi.forall_elim i) bi.pure_impl_forall.
  rewrite bi.forall_elim //. apply bi.forall_intro=> k.
  rewrite bi.pure_impl_forall. apply bi.forall_intro=>_.
  rewrite (objective_at Q i). by rewrite (objective_at P k).
Qed.
Global Instance persistently_objective P `{!Objective P} :
  Objective (bi_persistently P).
Proof. intros i j. unseal. by rewrite objective_at. Qed.

Global Instance affinely_objective P `{!Objective P} : Objective (bi_affinely P).
Proof. rewrite /bi_affinely. apply _. Qed.
Global Instance absorbingly_objective P `{!Objective P} :
  Objective (bi_absorbingly P).
Proof. rewrite /bi_absorbingly. apply _. Qed.
Global Instance persistently_if_objective P p `{!Objective P} :
  Objective (bi_persistently_if p P).
Proof. rewrite /bi_persistently_if. destruct p; apply _. Qed.
Global Instance affinely_if_objective P p `{!Objective P} :
  Objective (bi_affinely_if p P).
Proof. rewrite /bi_affinely_if. destruct p; apply _. Qed.

(** monPred_in *)
Lemma monPred_in_intro P : P ⊢ ∃ i, monPred_in i ∧ ⎡P i⎤.
Proof.
  unseal. split=>i /=.
  rewrite /= -(bi.exist_intro i). apply bi.and_intro=>//. by apply bi.pure_intro.
Qed.
Lemma monPred_in_elim P i : monPred_in i -∗ ⎡P i⎤ → P .
Proof.
  apply bi.impl_intro_r. unseal. split=>i' /=.
  eapply bi.pure_elim; [apply bi.and_elim_l|]=>?. rewrite bi.and_elim_r. by f_equiv.
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

Lemma monPred_at_big_sepL {A} i (Φ : nat → A → monPred) l :
  ([∗ list] k↦x ∈ l, Φ k x) i ⊣⊢ [∗ list] k↦x ∈ l, Φ k x i.
Proof. apply (big_opL_commute (flip monPred_at i)). Qed.
Lemma monPred_at_big_sepM `{Countable K} {A} i (Φ : K → A → monPred) (m : gmap K A) :
  ([∗ map] k↦x ∈ m, Φ k x) i ⊣⊢ [∗ map] k↦x ∈ m, Φ k x i.
Proof. apply (big_opM_commute (flip monPred_at i)). Qed.
Lemma monPred_at_big_sepS `{Countable A} i (Φ : A → monPred) (X : gset A) :
  ([∗ set] y ∈ X, Φ y) i ⊣⊢ [∗ set] y ∈ X, Φ y i.
Proof. apply (big_opS_commute (flip monPred_at i)). Qed.
Lemma monPred_at_big_sepMS `{Countable A} i (Φ : A → monPred) (X : gmultiset A) :
  ([∗ mset] y ∈ X, Φ y) i ⊣⊢ ([∗ mset] y ∈ X, Φ y i).
Proof. apply (big_opMS_commute (flip monPred_at i)). Qed.

Global Instance monPred_objectively_monoid_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) (@monPred_objectively I PROP).
Proof.
  split; [split|]; try apply _. apply monPred_objectively_and.
  apply monPred_objectively_pure.
Qed.
Global Instance monPred_objectively_monoid_sep_entails_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@monPred_objectively I PROP).
Proof.
  split; [split|]; try apply _. apply monPred_objectively_sep_2.
  by rewrite monPred_objectively_emp.
Qed.
Global Instance monPred_objectively_monoid_sep_homomorphism `{BiIndexBottom bot} :
  MonoidHomomorphism bi_sep bi_sep (≡) (@monPred_objectively I PROP).
Proof.
  split; [split|]; try apply _. apply monPred_objectively_sep.
  by rewrite monPred_objectively_emp.
Qed.

Lemma monPred_objectively_big_sepL_entails {A} (Φ : nat → A → monPred) l :
  ([∗ list] k↦x ∈ l, <obj> (Φ k x)) ⊢ <obj> ([∗ list] k↦x ∈ l, Φ k x).
Proof. apply (big_opL_commute monPred_objectively (R:=flip (⊢))). Qed.
Lemma monPred_objectively_big_sepM_entails
      `{Countable K} {A} (Φ : K → A → monPred) (m : gmap K A) :
  ([∗ map] k↦x ∈ m, <obj> (Φ k x)) ⊢ <obj> ([∗ map] k↦x ∈ m, Φ k x).
Proof. apply (big_opM_commute monPred_objectively (R:=flip (⊢))). Qed.
Lemma monPred_objectively_big_sepS_entails `{Countable A} (Φ : A → monPred) (X : gset A) :
  ([∗ set] y ∈ X, <obj> (Φ y)) ⊢ <obj> ([∗ set] y ∈ X, Φ y).
Proof. apply (big_opS_commute monPred_objectively (R:=flip (⊢))). Qed.
Lemma monPred_objectively_big_sepMS_entails `{Countable A} (Φ : A → monPred) (X : gmultiset A) :
  ([∗ mset] y ∈ X, <obj> (Φ y)) ⊢ <obj> ([∗ mset] y ∈ X, Φ y).
Proof. apply (big_opMS_commute monPred_objectively (R:=flip (⊢))). Qed.

Lemma monPred_objectively_big_sepL `{BiIndexBottom bot} {A} (Φ : nat → A → monPred) l :
  <obj> ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, <obj> (Φ k x)).
Proof. apply (big_opL_commute _). Qed.
Lemma monPred_objectively_big_sepM `{BiIndexBottom bot} `{Countable K} {A}
      (Φ : K → A → monPred) (m : gmap K A) :
  <obj> ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, <obj> (Φ k x)).
Proof. apply (big_opM_commute _). Qed.
Lemma monPred_objectively_big_sepS `{BiIndexBottom bot} `{Countable A}
      (Φ : A → monPred) (X : gset A) :
  <obj> ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, <obj> (Φ y)).
Proof. apply (big_opS_commute _). Qed.
Lemma monPred_objectively_big_sepMS `{BiIndexBottom bot} `{Countable A}
      (Φ : A → monPred) (X : gmultiset A) :
  <obj> ([∗ mset] y ∈ X, Φ y) ⊣⊢  ([∗ mset] y ∈ X, <obj> (Φ y)).
Proof. apply (big_opMS_commute _). Qed.

Global Instance big_sepL_objective {A} (l : list A) Φ `{∀ n x, Objective (Φ n x)} :
  @Objective I PROP ([∗ list] n↦x ∈ l, Φ n x)%I.
Proof. generalize dependent Φ. induction l=>/=; apply _. Qed.
Global Instance big_sepM_objective `{Countable K} {A}
       (Φ : K → A → monPred) (m : gmap K A) `{∀ k x, Objective (Φ k x)} :
  Objective ([∗ map] k↦x ∈ m, Φ k x)%I.
Proof. intros ??. rewrite !monPred_at_big_sepM. do 3 f_equiv. by apply objective_at. Qed.
Global Instance big_sepS_objective `{Countable A} (Φ : A → monPred)
       (X : gset A) `{∀ y, Objective (Φ y)} :
  Objective ([∗ set] y ∈ X, Φ y)%I.
Proof. intros ??. rewrite !monPred_at_big_sepS. do 2 f_equiv. by apply objective_at. Qed.
Global Instance big_sepMS_objective `{Countable A} (Φ : A → monPred)
       (X : gmultiset A) `{∀ y, Objective (Φ y)} :
  Objective ([∗ mset] y ∈ X, Φ y)%I.
Proof. intros ??. rewrite !monPred_at_big_sepMS. do 2 f_equiv. by apply objective_at. Qed.

(** bupd *)
Lemma monPred_bupd_mixin `{BiBUpd PROP} : BiBUpdMixin monPredI monPred_bupd.
Proof.
  split; unseal; unfold monPred_bupd_def, monPred_upclosed.
  (* Note: Notation is somewhat broken here. *)
  - intros n P Q HPQ. split=>/= i. by repeat f_equiv.
  - intros P. split=>/= i. apply bi.forall_intro=>?. rewrite bi.pure_impl_forall.
    apply bi.forall_intro=><-. apply bupd_intro.
  - intros P Q HPQ. split=>/= i. by repeat f_equiv.
  - intros P. split=>/= i. do 3 f_equiv. rewrite -(bupd_trans (P _))
      bi.forall_elim bi.pure_impl_forall bi.forall_elim //.
  - intros P Q. split=> /= i. apply bi.forall_intro=>?.
    rewrite bi.pure_impl_forall. apply bi.forall_intro=><-.
    rewrite -bupd_frame_r bi.forall_elim bi.pure_impl_forall bi.forall_elim //.
Qed.
Global Instance monPred_bi_bupd `{BiBUpd PROP} : BiBUpd monPredI :=
  {| bi_bupd_mixin := monPred_bupd_mixin |}.

Lemma monPred_at_bupd `{BiBUpd PROP} i P : (|==> P) i ⊣⊢ |==> P i.
Proof.
  unseal. setoid_rewrite bi.pure_impl_forall. apply bi.equiv_spec; split.
  - rewrite !bi.forall_elim //.
  - do 2 apply bi.forall_intro=>?. by do 2 f_equiv.
Qed.
Global Instance bupd_objective `{BiBUpd PROP} P `{!Objective P} :
  Objective (|==> P)%I.
Proof. intros ??. by rewrite !monPred_at_bupd objective_at. Qed.

Global Instance monPred_bi_embed_bupd `{BiBUpd PROP} :
  BiEmbedBUpd PROP monPredI.
Proof.
  split. unseal. split=>i /=. setoid_rewrite bi.pure_impl_forall.
  apply bi.equiv_spec; split.
  - by do 2 apply bi.forall_intro=>?.
  - rewrite !bi.forall_elim //.
Qed.
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
Global Instance monPred_objectively_timeless P : Timeless P → Timeless (<obj> P).
Proof.
  move=>[]. unfold Timeless. unseal=>Hti. split=> ? /=.
  by apply timeless, bi.forall_timeless.
Qed.
Global Instance monPred_subjectively_timeless P : Timeless P → Timeless (<subj> P).
Proof.
  move=>[]. unfold Timeless. unseal=>Hti. split=> ? /=.
  by apply timeless, bi.exist_timeless.
Qed.

Global Instance monPred_sbi_embed : SbiEmbed PROP monPredSI.
Proof.
  split; unseal=> //. intros ? P Q.
  apply (@bi.f_equiv _ _ _ (λ P, monPred_at P inhabitant)); solve_proper.
Qed.

Lemma monPred_plainly_unfold `{BiPlainly PROP} : plainly = λ P, ⎡ ∀ i, ■ (P i) ⎤%I.
Proof. by unseal. Qed.
Lemma monPred_internal_eq_unfold : @sbi_internal_eq monPredSI = λ A x y, ⎡ x ≡ y ⎤%I.
Proof. by unseal. Qed.

Lemma monPred_fupd_mixin `{BiFUpd PROP} : BiFUpdMixin monPredSI monPred_fupd.
Proof.
  split; unseal; unfold monPred_fupd_def, monPred_upclosed.
  (* Note: Notation is somewhat broken here. *)
  - intros E1 E2 n P Q HPQ. split=>/= i. by repeat f_equiv.
  - intros E1 E2 P HE12. split=>/= i.
    do 2 setoid_rewrite bi.pure_impl_forall. do 2 apply bi.forall_intro=>?.
    rewrite (fupd_intro_mask E1 E2 (P i)) //. f_equiv.
    do 2 apply bi.forall_intro=>?. do 2 f_equiv. by etrans.
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
Qed.
Global Instance monPred_bi_fupd `{BiFUpd PROP} : BiFUpd monPredSI :=
  {| bi_fupd_mixin := monPred_fupd_mixin |}.
Global Instance monPred_bi_bupd_fupd `{BiBUpdFUpd PROP} : BiBUpdFUpd monPredSI.
Proof.
  rewrite /BiBUpdFUpd; unseal; unfold monPred_fupd_def, monPred_upclosed.
  intros E P. split=>/= i. by setoid_rewrite bupd_fupd.
Qed.

Global Instance monPred_bi_bupd_plainly `{BiBUpdPlainly PROP} : BiBUpdPlainly monPredSI.
Proof.
  rewrite /BiBUpdPlainly=> P; unseal.
  split=> /= i. rewrite bi.forall_elim bi.pure_impl_forall.
  by rewrite bi.forall_elim // -plainly_forall bupd_plainly bi.forall_elim.
Qed.

Global Instance monPred_at_plain `{BiPlainly PROP} P i : Plain P → Plain (P i).
Proof. move => [] /(_ i). unfold Plain. unseal. rewrite bi.forall_elim //. Qed.

Global Instance monPred_bi_fupd_plainly `{BiFUpdPlainly PROP} : BiFUpdPlainly monPredSI.
Proof.
  split; unseal.
  - intros E1 E2 E2' P Q ? HE12. split=>/= i. repeat setoid_rewrite bi.pure_impl_forall.
    do 4 f_equiv. rewrite 4?bi.forall_elim // fupd_plain' //.
    apply bi.wand_intro_r. rewrite bi.wand_elim_l. do 2 apply bi.forall_intro=>?.
    repeat f_equiv=>//. do 2 apply bi.forall_intro=>?. repeat f_equiv. by etrans.
  - intros E P ?. split=>/= i. setoid_rewrite bi.pure_impl_forall.
    do 2 setoid_rewrite bi.later_forall. do 4 f_equiv. apply later_fupd_plain, _.
Qed.

Global Instance monPred_bi_embed_fupd `{BiFUpd PROP} : BiEmbedFUpd PROP monPredSI.
Proof.
  split. unseal. split=>i /=. setoid_rewrite bi.pure_impl_forall.
  apply bi.equiv_spec; split.
  - by do 2 apply bi.forall_intro=>?.
  - rewrite !bi.forall_elim //.
Qed.

(** Unfolding lemmas *)
Lemma monPred_at_plainly `{BiPlainly PROP} i P : (■ P) i ⊣⊢ ∀ j, ■ (P j).
Proof. by unseal. Qed.
Lemma monPred_at_internal_eq {A : ofeT} i (a b : A) :
  @monPred_at I PROP (a ≡ b) i ⊣⊢ a ≡ b.
Proof. rewrite monPred_internal_eq_unfold. by apply monPred_at_embed. Qed.
Lemma monPred_at_later i P : (▷ P) i ⊣⊢ ▷ P i.
Proof. by unseal. Qed.
Lemma monPred_at_fupd `{BiFUpd PROP} i E1 E2 P :
  (|={E1,E2}=> P) i ⊣⊢ |={E1,E2}=> P i.
Proof.
  unseal. setoid_rewrite bi.pure_impl_forall. apply bi.equiv_spec; split.
  - rewrite !bi.forall_elim //.
  - do 2 apply bi.forall_intro=>?. by do 2 f_equiv.
Qed.
Lemma monPred_at_except_0 i P : (◇ P) i ⊣⊢ ◇ P i.
Proof. by unseal. Qed.

Lemma monPred_equivI {PROP' : sbi} P Q :
  sbi_internal_eq (PROP:=PROP') P Q ⊣⊢ ∀ i, P i ≡ Q i.
Proof.
  apply bi.equiv_spec. split.
  - apply bi.forall_intro=>?. apply (bi.f_equiv (flip monPred_at _)).
  - by rewrite -{2}(sig_monPred_sig P) -{2}(sig_monPred_sig Q)
               -bi.f_equiv -bi.sig_equivI !bi.ofe_fun_equivI.
Qed.

Global Instance monPred_objectively_plain `{BiPlainly PROP} P : Plain P → Plain (<obj> P).
Proof. rewrite monPred_objectively_unfold. apply _. Qed.
Global Instance monPred_subjectively_plain `{BiPlainly PROP} P : Plain P → Plain (<subj> P).
Proof. rewrite monPred_subjectively_unfold. apply _. Qed.

(** Objective  *)
Global Instance plainly_objective `{BiPlainly PROP} P : Objective (■ P).
Proof. intros ??. by unseal. Qed.
Global Instance plainly_if_objective `{BiPlainly PROP} P p `{!Objective P} :
  Objective (■?p P).
Proof. rewrite /plainly_if. destruct p; apply _. Qed.

Global Instance internal_eq_objective {A : ofeT} (x y : A) :
  @Objective I PROP (x ≡ y)%I.
Proof. intros ??. by unseal. Qed.

Global Instance later_objective P `{!Objective P} : Objective (▷ P)%I.
Proof. intros ??. unseal. by rewrite objective_at. Qed.
Global Instance laterN_objective P `{!Objective P} n : Objective (▷^n P)%I.
Proof. induction n; apply _. Qed.
Global Instance except0_objective P `{!Objective P} : Objective (◇ P)%I.
Proof. rewrite /sbi_except_0. apply _. Qed.

Global Instance fupd_objective E1 E2 P `{!Objective P} `{BiFUpd PROP} :
  Objective (|={E1,E2}=> P)%I.
Proof. intros ??. by rewrite !monPred_at_fupd objective_at. Qed.
End sbi_facts.
