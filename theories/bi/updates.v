From stdpp Require Import coPset.
From iris.bi Require Import interface derived_laws_sbi big_op plainly.
Import interface.bi derived_laws_bi.bi derived_laws_sbi.bi.

(* We first define operational type classes for the notations, and then later
bundle these operational type classes with the laws. *)
Class BUpd (PROP : Type) : Type := bupd : PROP → PROP.
Instance : Params (@bupd) 2.
Hint Mode BUpd ! : typeclass_instances.

Notation "|==> Q" := (bupd Q) : bi_scope.
Notation "P ==∗ Q" := (P ⊢ |==> Q) (only parsing) : stdpp_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q)%I : bi_scope.

Class FUpd (PROP : Type) : Type := fupd : coPset → coPset → PROP → PROP.
Instance: Params (@fupd) 4.
Hint Mode FUpd ! : typeclass_instances.

Notation "|={ E1 , E2 }=> Q" := (fupd E1 E2 Q) : bi_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q)%I : bi_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q) : stdpp_scope.

Notation "|={ E }=> Q" := (fupd E E Q) : bi_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q)%I : bi_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q) : stdpp_scope.

(** Fancy updates that take a step. *)
Notation "|={ E1 , E2 , E3 }▷=> Q" := (|={E1,E2}=> (▷ |={E2,E3}=> Q))%I : bi_scope.
Notation "P ={ E1 , E2 , E3 }▷=∗ Q" := (P -∗ |={ E1,E2,E3 }▷=> Q)%I : bi_scope.
Notation "|={ E1 , E2 }▷=> Q" := (|={E1,E2,E1}▷=> Q)%I : bi_scope.
Notation "P ={ E1 , E2 }▷=∗ Q" := (P ⊢ |={ E1 , E2, E1 }▷=> Q) (only parsing) : stdpp_scope.
Notation "P ={ E1 , E2 }▷=∗ Q" := (P -∗ |={ E1 , E2, E1 }▷=> Q)%I : bi_scope.
Notation "|={ E }▷=> Q" := (|={E,E}▷=> Q)%I : bi_scope.
Notation "P ={ E }▷=∗ Q" := (P ={E,E}▷=∗ Q)%I : bi_scope.
Notation "|={ E1 , E2 }▷=>^ n Q" := (Nat.iter n (λ P, |={E1,E2}▷=> P) Q)%I : bi_scope.
Notation "P ={ E1 , E2 }▷=∗^ n Q" := (P ⊢ |={E1,E2}▷=>^n Q)%I (only parsing) : stdpp_scope.
Notation "P ={ E1 , E2 }▷=∗^ n Q" := (P -∗ |={E1,E2}▷=>^n Q)%I : bi_scope.

(** Bundled versions  *)
(* Mixins allow us to create instances easily without having to use Program *)
Record BiBUpdMixin (PROP : bi) `(BUpd PROP) := {
  bi_bupd_mixin_bupd_ne : NonExpansive bupd;
  bi_bupd_mixin_bupd_intro (P : PROP) : P ==∗ P;
  bi_bupd_mixin_bupd_mono (P Q : PROP) : (P ⊢ Q) → (|==> P) ==∗ Q;
  bi_bupd_mixin_bupd_trans (P : PROP) : (|==> |==> P) ==∗ P;
  bi_bupd_mixin_bupd_frame_r (P R : PROP) : (|==> P) ∗ R ==∗ P ∗ R;
}.

Record BiFUpdMixin (PROP : sbi) `(FUpd PROP) := {
  bi_fupd_mixin_fupd_ne E1 E2 : NonExpansive (fupd E1 E2);
  bi_fupd_mixin_fupd_intro_mask E1 E2 (P : PROP) : E2 ⊆ E1 → P ⊢ |={E1,E2}=> |={E2,E1}=> P;
  bi_fupd_mixin_except_0_fupd E1 E2 (P : PROP) : ◇ (|={E1,E2}=> P) ={E1,E2}=∗ P;
  bi_fupd_mixin_fupd_mono E1 E2 (P Q : PROP) : (P ⊢ Q) → (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q;
  bi_fupd_mixin_fupd_trans E1 E2 E3 (P : PROP) : (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P;
  bi_fupd_mixin_fupd_mask_frame_r' E1 E2 Ef (P : PROP) :
    E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ={E1 ∪ Ef,E2 ∪ Ef}=∗ P;
  bi_fupd_mixin_fupd_frame_r E1 E2 (P R : PROP) : (|={E1,E2}=> P) ∗ R ={E1,E2}=∗ P ∗ R;
}.

Class BiBUpd (PROP : bi) := {
  bi_bupd_bupd :> BUpd PROP;
  bi_bupd_mixin : BiBUpdMixin PROP bi_bupd_bupd;
}.
Hint Mode BiBUpd ! : typeclass_instances.
Arguments bi_bupd_bupd : simpl never.

Class BiFUpd (PROP : sbi) := {
  bi_fupd_fupd :> FUpd PROP;
  bi_fupd_mixin : BiFUpdMixin PROP bi_fupd_fupd;
}.
Hint Mode BiFUpd ! : typeclass_instances.
Arguments bi_fupd_fupd : simpl never.

Class BiBUpdFUpd (PROP : sbi) `{BiBUpd PROP, BiFUpd PROP} :=
  bupd_fupd E (P : PROP) : (|==> P) ={E}=∗ P.
Hint Mode BiBUpdFUpd ! - - : typeclass_instances.

Class BiBUpdPlainly (PROP : sbi) `{!BiBUpd PROP, !BiPlainly PROP} :=
  bupd_plainly (P : PROP) : (|==> ■ P) -∗ P.
Hint Mode BiBUpdPlainly ! - - : typeclass_instances.

(** These rules for the interaction between the [■] and [|={E1,E2=>] modalities
only make sense for affine logics. From the axioms below, one could derive
[■ P ={E}=∗ P] (see the lemma [fupd_plainly_elim]), which in turn gives
[True ={E}=∗ emp]. *)
Class BiFUpdPlainly (PROP : sbi) `{!BiFUpd PROP, !BiPlainly PROP} := {
  (** When proving a fancy update of a plain proposition, you can also prove it
  while being allowed to open all invariants. *)
  fupd_plainly_mask_empty E (P : PROP) :
    (|={E,∅}=> ■ P) ⊢ |={E}=> P;
  (** A strong eliminator (a la modus ponens) for the wand-fancy-update with a
  plain conclusion: We eliminate [R ={E}=∗ ■ P] by supplying an [R], but we get
  to keep the [R]. *)
  fupd_plainly_keep_l E (P R : PROP) :
    (R ={E}=∗ ■ P) ∗ R ⊢ |={E}=> P ∗ R;
  (** Later "almost" commutes with fancy updates over plain propositions. It
  commutes "almost" because of the ◇ modality, which is needed in the definition
  of fancy updates so one can remove laters of timeless propositions. *)
  fupd_plainly_later E (P : PROP) :
    (▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P;
  (** Forall quantifiers commute with fancy updates over plain propositions. *)
  fupd_plainly_forall_2 E {A} (Φ : A → PROP) :
    (∀ x, |={E}=> ■ Φ x) ⊢ |={E}=> ∀ x, Φ x
}.
Hint Mode BiBUpdFUpd ! - - : typeclass_instances.

Section bupd_laws.
  Context `{BiBUpd PROP}.
  Implicit Types P : PROP.

  Global Instance bupd_ne : NonExpansive (@bupd PROP _).
  Proof. eapply bi_bupd_mixin_bupd_ne, bi_bupd_mixin. Qed.
  Lemma bupd_intro P : P ==∗ P.
  Proof. eapply bi_bupd_mixin_bupd_intro, bi_bupd_mixin. Qed.
  Lemma bupd_mono (P Q : PROP) : (P ⊢ Q) → (|==> P) ==∗ Q.
  Proof. eapply bi_bupd_mixin_bupd_mono, bi_bupd_mixin. Qed.
  Lemma bupd_trans (P : PROP) : (|==> |==> P) ==∗ P.
  Proof. eapply bi_bupd_mixin_bupd_trans, bi_bupd_mixin. Qed.
  Lemma bupd_frame_r (P R : PROP) : (|==> P) ∗ R ==∗ P ∗ R.
  Proof. eapply bi_bupd_mixin_bupd_frame_r, bi_bupd_mixin. Qed.
End bupd_laws.

Section fupd_laws.
  Context `{BiFUpd PROP}.
  Implicit Types P : PROP.

  Global Instance fupd_ne E1 E2 : NonExpansive (@fupd PROP _ E1 E2).
  Proof. eapply bi_fupd_mixin_fupd_ne, bi_fupd_mixin. Qed.
  Lemma fupd_intro_mask E1 E2 (P : PROP) : E2 ⊆ E1 → P ⊢ |={E1,E2}=> |={E2,E1}=> P.
  Proof. eapply bi_fupd_mixin_fupd_intro_mask, bi_fupd_mixin. Qed.
  Lemma except_0_fupd E1 E2 (P : PROP) : ◇ (|={E1,E2}=> P) ={E1,E2}=∗ P.
  Proof. eapply bi_fupd_mixin_except_0_fupd, bi_fupd_mixin. Qed.
  Lemma fupd_mono E1 E2 (P Q : PROP) : (P ⊢ Q) → (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q.
  Proof. eapply bi_fupd_mixin_fupd_mono, bi_fupd_mixin. Qed.
  Lemma fupd_trans E1 E2 E3 (P : PROP) : (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P.
  Proof. eapply bi_fupd_mixin_fupd_trans, bi_fupd_mixin. Qed.
  Lemma fupd_mask_frame_r' E1 E2 Ef (P : PROP) :
    E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ={E1 ∪ Ef,E2 ∪ Ef}=∗ P.
  Proof. eapply bi_fupd_mixin_fupd_mask_frame_r', bi_fupd_mixin. Qed.
  Lemma fupd_frame_r E1 E2 (P R : PROP) : (|={E1,E2}=> P) ∗ R ={E1,E2}=∗ P ∗ R.
  Proof. eapply bi_fupd_mixin_fupd_frame_r, bi_fupd_mixin. Qed.
End fupd_laws.

Section bupd_derived.
  Context `{BiBUpd PROP}.
  Implicit Types P Q R : PROP.

  (* FIXME: Removing the `PROP:=` diverges. *)
  Global Instance bupd_proper :
    Proper ((≡) ==> (≡)) (bupd (PROP:=PROP)) := ne_proper _.

  (** BUpd derived rules *)
  Global Instance bupd_mono' : Proper ((⊢) ==> (⊢)) (bupd (PROP:=PROP)).
  Proof. intros P Q; apply bupd_mono. Qed.
  Global Instance bupd_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) (bupd (PROP:=PROP)).
  Proof. intros P Q; apply bupd_mono. Qed.

  Lemma bupd_frame_l R Q : (R ∗ |==> Q) ==∗ R ∗ Q.
  Proof. rewrite !(comm _ R); apply bupd_frame_r. Qed.
  Lemma bupd_wand_l P Q : (P -∗ Q) ∗ (|==> P) ==∗ Q.
  Proof. by rewrite bupd_frame_l wand_elim_l. Qed.
  Lemma bupd_wand_r P Q : (|==> P) ∗ (P -∗ Q) ==∗ Q.
  Proof. by rewrite bupd_frame_r wand_elim_r. Qed.
  Lemma bupd_sep P Q : (|==> P) ∗ (|==> Q) ==∗ P ∗ Q.
  Proof. by rewrite bupd_frame_r bupd_frame_l bupd_trans. Qed.
End bupd_derived.

Section bupd_derived_sbi.
  Context {PROP : sbi} `{BiBUpd PROP}.
  Implicit Types P Q R : PROP.

  Lemma except_0_bupd P : ◇ (|==> P) ⊢ (|==> ◇ P).
  Proof.
    rewrite /sbi_except_0. apply or_elim; eauto using bupd_mono, or_intro_r.
    by rewrite -bupd_intro -or_intro_l.
  Qed.

  Section bupd_plainly.
    Context `{BiBUpdPlainly PROP}.

    Lemma bupd_plain P `{!Plain P} : (|==> P) ⊢ P.
    Proof. by rewrite {1}(plain P) bupd_plainly. Qed.

    Lemma bupd_forall {A} (Φ : A → PROP) `{∀ x, Plain (Φ x)} :
      (|==> ∀ x, Φ x) ⊣⊢ (∀ x, |==> Φ x).
    Proof.
      apply (anti_symm _).
      - apply forall_intro=> x. by rewrite (forall_elim x).
      - rewrite -bupd_intro. apply forall_intro=> x.
        by rewrite (forall_elim x) bupd_plain.
    Qed.
  End bupd_plainly.
End bupd_derived_sbi.

Section fupd_derived.
  Context `{BiFUpd PROP}.
  Implicit Types P Q R : PROP.

  Global Instance fupd_proper E1 E2 :
    Proper ((≡) ==> (≡)) (fupd (PROP:=PROP) E1 E2) := ne_proper _.

  (** FUpd derived rules *)
  Global Instance fupd_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (fupd (PROP:=PROP) E1 E2).
  Proof. intros P Q; apply fupd_mono. Qed.
  Global Instance fupd_flip_mono' E1 E2 :
    Proper (flip (⊢) ==> flip (⊢)) (fupd (PROP:=PROP) E1 E2).
  Proof. intros P Q; apply fupd_mono. Qed.

  Lemma fupd_intro E P : P ={E}=∗ P.
  Proof. by rewrite {1}(fupd_intro_mask E E P) // fupd_trans. Qed.
  Lemma fupd_intro_mask' E1 E2 : E2 ⊆ E1 → (|={E1,E2}=> |={E2,E1}=> bi_emp (PROP:=PROP))%I.
  Proof. exact: fupd_intro_mask. Qed.
  Lemma fupd_except_0 E1 E2 P : (|={E1,E2}=> ◇ P) ={E1,E2}=∗ P.
  Proof. by rewrite {1}(fupd_intro E2 P) except_0_fupd fupd_trans. Qed.

  Lemma fupd_frame_l E1 E2 R Q : (R ∗ |={E1,E2}=> Q) ={E1,E2}=∗ R ∗ Q.
  Proof. rewrite !(comm _ R); apply fupd_frame_r. Qed.
  Lemma fupd_wand_l E1 E2 P Q : (P -∗ Q) ∗ (|={E1,E2}=> P) ={E1,E2}=∗ Q.
  Proof. by rewrite fupd_frame_l wand_elim_l. Qed.
  Lemma fupd_wand_r E1 E2 P Q : (|={E1,E2}=> P) ∗ (P -∗ Q) ={E1,E2}=∗ Q.
  Proof. by rewrite fupd_frame_r wand_elim_r. Qed.

  Lemma fupd_mask_weaken E1 E2 P `{!Absorbing P} : E2 ⊆ E1 → P ={E1,E2}=∗ P.
  Proof.
    intros ?. rewrite -{1}(right_id emp%I bi_sep P%I).
    rewrite (fupd_intro_mask E1 E2 emp%I) //.
    by rewrite fupd_frame_l sep_elim_l.
  Qed.

  Lemma fupd_trans_frame E1 E2 E3 P Q :
    ((Q ={E2,E3}=∗ emp) ∗ |={E1,E2}=> (Q ∗ P)) ={E1,E3}=∗ P.
  Proof.
    rewrite fupd_frame_l assoc -(comm _ Q) wand_elim_r.
    by rewrite fupd_frame_r left_id fupd_trans.
  Qed.

  Lemma fupd_elim E1 E2 E3 P Q :
    (Q -∗ (|={E2,E3}=> P)) → (|={E1,E2}=> Q) -∗ (|={E1,E3}=> P).
  Proof. intros ->. rewrite fupd_trans //. Qed.

  Lemma fupd_mask_frame_r E1 E2 Ef P :
    E1 ## Ef → (|={E1,E2}=> P) ={E1 ∪ Ef,E2 ∪ Ef}=∗ P.
  Proof.
    intros ?. rewrite -fupd_mask_frame_r' //. f_equiv.
    apply impl_intro_l, and_elim_r.
  Qed.
  Lemma fupd_mask_mono E1 E2 P : E1 ⊆ E2 → (|={E1}=> P) ={E2}=∗ P.
  Proof.
    intros (Ef&->&?)%subseteq_disjoint_union_L. by apply fupd_mask_frame_r.
  Qed.
  (** How to apply an arbitrary mask-changing view shift when having
      an arbitrary mask. *)
  Lemma fupd_mask_frame E E' E1 E2 P :
    E1 ⊆ E →
    (|={E1,E2}=> |={E2 ∪ (E ∖ E1),E'}=> P) -∗ (|={E,E'}=> P).
  Proof.
    intros ?. rewrite (fupd_mask_frame_r _ _ (E ∖ E1)); last set_solver.
    rewrite fupd_trans.
    by replace (E1 ∪ E ∖ E1) with E by (by apply union_difference_L).
  Qed.
  (* A variant of [fupd_mask_frame] that works well for accessors: Tailored to
     elliminate updates of the form [|={E1,E1∖E2}=> Q] and provides a way to
     transform the closing view shift instead of letting you prove the same
     side-conditions twice. *)
  Lemma fupd_mask_frame_acc E E' E1(*Eo*) E2(*Em*) P Q :
    E1 ⊆ E →
    (|={E1,E1∖E2}=> Q) -∗
    (Q -∗ |={E∖E2,E'}=> (∀ R, (|={E1∖E2,E1}=> R) -∗ |={E∖E2,E}=> R) -∗  P) -∗
    (|={E,E'}=> P).
  Proof.
    intros HE. apply wand_intro_r. rewrite fupd_frame_r.
    rewrite wand_elim_r. clear Q.
    rewrite -(fupd_mask_frame E E'); first apply fupd_mono; last done.
    (* The most horrible way to apply fupd_intro_mask *)
    rewrite -[X in (X -∗ _)](right_id emp%I).
    rewrite (fupd_intro_mask (E1 ∖ E2 ∪ E ∖ E1) (E ∖ E2) emp%I); last first.
    { rewrite {1}(union_difference_L _ _ HE). set_solver. }
    rewrite fupd_frame_l fupd_frame_r. apply fupd_elim.
    apply fupd_mono.
    eapply wand_apply;
      last (apply sep_mono; first reflexivity); first reflexivity.
    apply forall_intro=>R. apply wand_intro_r.
    rewrite fupd_frame_r. apply fupd_elim. rewrite left_id.
    rewrite (fupd_mask_frame_r _ _ (E ∖ E1)); last set_solver+.
    rewrite {4}(union_difference_L _ _ HE). done.
  Qed.

  Lemma fupd_mask_same E E1 P :
    E = E1 → (|={E}=> P) -∗ (|={E,E1}=> P).
  Proof. intros <-. done. Qed.

  Lemma fupd_sep E P Q : (|={E}=> P) ∗ (|={E}=> Q) ={E}=∗ P ∗ Q.
  Proof. by rewrite fupd_frame_r fupd_frame_l fupd_trans. Qed.
  Lemma fupd_big_sepL {A} E (Φ : nat → A → PROP) (l : list A) :
    ([∗ list] k↦x ∈ l, |={E}=> Φ k x) ={E}=∗ [∗ list] k↦x ∈ l, Φ k x.
  Proof.
    apply (big_opL_forall (λ P Q, P ={E}=∗ Q)); auto using fupd_intro.
    intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ -fupd_sep.
  Qed.
  Lemma fupd_big_sepM `{Countable K} {A} E (Φ : K → A → PROP) (m : gmap K A) :
    ([∗ map] k↦x ∈ m, |={E}=> Φ k x) ={E}=∗ [∗ map] k↦x ∈ m, Φ k x.
  Proof.
    apply (big_opM_forall (λ P Q, P ={E}=∗ Q)); auto using fupd_intro.
    intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ -fupd_sep.
  Qed.
  Lemma fupd_big_sepS `{Countable A} E (Φ : A → PROP) X :
    ([∗ set] x ∈ X, |={E}=> Φ x) ={E}=∗ [∗ set] x ∈ X, Φ x.
  Proof.
    apply (big_opS_forall (λ P Q, P ={E}=∗ Q)); auto using fupd_intro.
    intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ -fupd_sep.
  Qed.

  (** Fancy updates that take a step derived rules. *)
  Lemma step_fupd_wand E1 E2 E3 P Q : (|={E1,E2,E3}▷=> P) -∗ (P -∗ Q) -∗ |={E1,E2,E3}▷=> Q.
  Proof.
    apply wand_intro_l.
    by rewrite (later_intro (P -∗ Q)%I) fupd_frame_l -later_sep fupd_frame_l
               wand_elim_l.
  Qed.

  Lemma step_fupd_mask_frame_r E1 E2 E3 Ef P :
    E1 ## Ef → E2 ## Ef → (|={E1,E2,E3}▷=> P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef,E3 ∪ Ef}▷=> P.
  Proof.
    intros. rewrite -fupd_mask_frame_r //. do 2 f_equiv. by apply fupd_mask_frame_r.
  Qed.

  Lemma step_fupd_mask_mono E1 E2 F1 F2 P :
    F1 ⊆ F2 → E1 ⊆ E2 → (|={E1,F2}▷=> P) ⊢ |={E2,F1}▷=> P.
  Proof.
    intros ??. rewrite -(emp_sep (|={E1,F2}▷=> P)%I).
    rewrite (fupd_intro_mask E2 E1 emp%I) //.
    rewrite fupd_frame_r -(fupd_trans E2 E1 F1). f_equiv.
    rewrite fupd_frame_l -(fupd_trans E1 F2 F1). f_equiv.
    rewrite (fupd_intro_mask F2 F1 (|={_,_}=> emp)%I) //.
    rewrite fupd_frame_r. f_equiv.
    rewrite [X in (X ∗ _)%I]later_intro -later_sep. f_equiv.
    rewrite fupd_frame_r -(fupd_trans F1 F2 E2). f_equiv.
    rewrite fupd_frame_l -(fupd_trans F2 E1 E2). f_equiv.
    by rewrite fupd_frame_r left_id.
  Qed.

  Lemma step_fupd_intro E1 E2 P : E2 ⊆ E1 → ▷ P -∗ |={E1,E2}▷=> P.
  Proof. intros. by rewrite -(step_fupd_mask_mono E2 _ _ E2) // -!fupd_intro. Qed.

  Lemma step_fupd_frame_l E1 E2 R Q :
    (R ∗ |={E1, E2}▷=> Q) -∗ |={E1, E2}▷=> (R ∗ Q).
  Proof.
    rewrite fupd_frame_l.
    apply fupd_mono.
    rewrite [P in P ∗ _ ⊢ _](later_intro R) -later_sep fupd_frame_l.
    by apply later_mono, fupd_mono.
  Qed.

  Lemma step_fupd_fupd E E' P : (|={E,E'}▷=> P) ⊣⊢ (|={E,E'}▷=> |={E}=> P).
  Proof.
    apply (anti_symm (⊢)).
    - by rewrite -fupd_intro.
    - by rewrite fupd_trans.
  Qed.

  Lemma step_fupdN_mono E1 E2 n P Q :
    (P ⊢ Q) → (|={E1,E2}▷=>^n P) ⊢ (|={E1,E2}▷=>^n Q).
  Proof.
    intros HPQ. induction n as [|n IH]=> //=. rewrite IH //.
  Qed.

  Lemma step_fupdN_wand E1 E2 n P Q :
    (|={E1,E2}▷=>^n P) -∗ (P -∗ Q) -∗ (|={E1,E2}▷=>^n Q).
  Proof.
    apply wand_intro_l. induction n as [|n IH]=> /=.
    { by rewrite wand_elim_l. }
    rewrite -IH -fupd_frame_l later_sep -fupd_frame_l.
    by apply sep_mono; first apply later_intro.
  Qed.

  Lemma step_fupdN_S_fupd n E P:
    (|={E, ∅}▷=>^(S n) P) ⊣⊢ (|={E, ∅}▷=>^(S n) |={E}=> P).
  Proof.
    apply (anti_symm (⊢)); rewrite !Nat_iter_S_r; apply step_fupdN_mono;
      rewrite -step_fupd_fupd //.
  Qed.

  Lemma step_fupdN_frame_l E1 E2 n R Q :
    (R ∗ |={E1, E2}▷=>^n Q) -∗ |={E1, E2}▷=>^n (R ∗ Q).
  Proof.
    induction n as [|n IH]; simpl; [done|].
    rewrite step_fupd_frame_l IH //=.
  Qed.

  Section fupd_plainly_derived.
    Context `{BiPlainly PROP, !BiFUpdPlainly PROP}.

    Lemma fupd_plainly_mask E E' P : (|={E,E'}=> ■ P) ⊢ |={E}=> P.
    Proof.
      rewrite -(fupd_plainly_mask_empty).
      apply fupd_elim, (fupd_mask_weaken _ _ _). set_solver.
    Qed.

    Lemma fupd_plainly_elim E P : ■ P ={E}=∗ P.
    Proof. by rewrite (fupd_intro E (■ P)%I) fupd_plainly_mask. Qed.

    Lemma fupd_plainly_keep_r E P R : R ∗ (R ={E}=∗ ■ P) ⊢ |={E}=> R ∗ P.
    Proof. by rewrite !(comm _ R) fupd_plainly_keep_l. Qed.

    Lemma fupd_plain_mask_empty E P `{!Plain P} : (|={E,∅}=> P) ⊢ |={E}=> P.
    Proof. by rewrite {1}(plain P) fupd_plainly_mask_empty. Qed.
    Lemma fupd_plain_mask E E' P `{!Plain P} : (|={E,E'}=> P) ⊢ |={E}=> P.
    Proof. by rewrite {1}(plain P) fupd_plainly_mask. Qed.

    Lemma fupd_plain_keep_l E P R `{!Plain P} : (R ={E}=∗ P) ∗ R ⊢ |={E}=> P ∗ R.
    Proof. by rewrite {1}(plain P) fupd_plainly_keep_l. Qed.
    Lemma fupd_plain_keep_r E P R `{!Plain P} : R ∗ (R ={E}=∗ P) ⊢ |={E}=> R ∗ P.
    Proof. by rewrite {1}(plain P) fupd_plainly_keep_r. Qed.

    Lemma fupd_plain_later E P `{!Plain P} : (▷ |={E}=> P) ⊢ |={E}=> ▷ ◇ P.
    Proof. by rewrite {1}(plain P) fupd_plainly_later. Qed.
    Lemma fupd_plain_forall_2 E {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} :
      (∀ x, |={E}=> Φ x) ⊢ |={E}=> ∀ x, Φ x.
    Proof.
      rewrite -fupd_plainly_forall_2. apply forall_mono=> x.
      by rewrite {1}(plain (Φ _)).
    Qed.

    Lemma fupd_plainly_laterN E n P `{HP : !Plain P} :
      (▷^n |={E}=> P) ⊢ |={E}=> ▷^n ◇ P.
    Proof.
      revert P HP. induction n as [|n IH]=> P ? /=.
      - by rewrite -except_0_intro.
      - rewrite -!later_laterN !laterN_later.
        rewrite fupd_plain_later. by rewrite IH except_0_later.
    Qed.

    Lemma fupd_plain_forall E1 E2 {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} :
      E2 ⊆ E1 →
      (|={E1,E2}=> ∀ x, Φ x) ⊣⊢ (∀ x, |={E1,E2}=> Φ x).
    Proof.
      intros. apply (anti_symm _).
      { apply forall_intro=> x. by rewrite (forall_elim x). }
      trans (∀ x, |={E1}=> Φ x)%I.
      { apply forall_mono=> x. by rewrite fupd_plain_mask. }
      rewrite fupd_plain_forall_2. apply fupd_elim.
      rewrite {1}(plain (∀ x, Φ x)) (fupd_mask_weaken E1 E2 (■ _)%I) //.
      apply fupd_elim. by rewrite fupd_plainly_elim.
    Qed.
    Lemma fupd_plain_forall' E {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} :
      (|={E}=> ∀ x, Φ x) ⊣⊢ (∀ x, |={E}=> Φ x).
    Proof. by apply fupd_plain_forall. Qed.

    Lemma step_fupd_plain E E' P `{!Plain P} : (|={E,E'}▷=> P) ={E}=∗ ▷ ◇ P.
    Proof.
      rewrite -(fupd_plain_mask _ E' (▷ ◇ P)%I).
      apply fupd_elim. by rewrite fupd_plain_mask -fupd_plain_later.
    Qed.

    Lemma step_fupdN_plain E E' n P `{!Plain P} : (|={E,E'}▷=>^n P) ={E}=∗ ▷^n ◇ P.
    Proof.
      induction n as [|n IH].
      - by rewrite -fupd_intro -except_0_intro.
      - rewrite Nat_iter_S step_fupd_fupd IH !fupd_trans step_fupd_plain.
        apply fupd_mono. destruct n as [|n]; simpl.
        * by rewrite except_0_idemp.
        * by rewrite except_0_later.
    Qed.

    Lemma step_fupd_plain_forall E1 E2 {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} :
      E2 ⊆ E1 →
      (|={E1,E2}▷=> ∀ x, Φ x) ⊣⊢ (∀ x, |={E1,E2}▷=> Φ x).
    Proof.
      intros. apply (anti_symm _).
      { apply forall_intro=> x. by rewrite (forall_elim x). }
      trans (∀ x, |={E1}=> ▷ ◇ Φ x)%I.
      { apply forall_mono=> x. by rewrite step_fupd_plain. }
      rewrite -fupd_plain_forall'. apply fupd_elim.
      rewrite -(fupd_except_0 E2 E1) -step_fupd_intro //.
      by rewrite -later_forall -except_0_forall.
    Qed.
  End fupd_plainly_derived.
End fupd_derived.
