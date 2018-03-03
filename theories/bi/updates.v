From stdpp Require Import coPset.
From iris.bi Require Import interface derived_laws big_op plainly.

(* We first define operational type classes for the notations, and then later
bundle these operational type classes with the laws. *)
Class BUpd (PROP : Type) : Type := bupd : PROP → PROP.
Instance : Params (@bupd) 2.
Hint Mode BUpd ! : typeclass_instances.

Notation "|==> Q" := (bupd Q)
  (at level 99, Q at level 200, format "|==>  Q") : bi_scope.
Notation "P ==∗ Q" := (P ⊢ |==> Q)
  (at level 99, Q at level 200, only parsing) : stdpp_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q)%I
  (at level 99, Q at level 200, format "P  ==∗  Q") : bi_scope.

Class FUpd (PROP : Type) : Type := fupd : coPset → coPset → PROP → PROP.
Instance: Params (@fupd) 4.
Hint Mode FUpd ! : typeclass_instances.

Notation "|={ E1 , E2 }=> Q" := (fupd E1 E2 Q)
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }=>  Q") : bi_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q)%I
  (at level 99, E1,E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }=∗  Q") : bi_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q)
  (at level 99, E1, E2 at level 50, Q at level 200, only parsing) : stdpp_scope.

Notation "|={ E }=> Q" := (fupd E E Q)
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }=>  Q") : bi_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }=∗  Q") : bi_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q)
  (at level 99, E at level 50, Q at level 200, only parsing) : stdpp_scope.

(** Fancy updates that take a step. *)
Notation "|={ E1 , E2 }▷=> Q" := (|={E1,E2}=> (▷ |={E2,E1}=> Q))%I
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }▷=>  Q") : bi_scope.
Notation "P ={ E1 , E2 }▷=∗ Q" := (P -∗ |={ E1 , E2 }▷=> Q)%I
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }▷=∗  Q") : bi_scope.
Notation "|={ E }▷=> Q" := (|={E,E}▷=> Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }▷=>  Q") : bi_scope.
Notation "P ={ E }▷=∗ Q" := (P ={E,E}▷=∗ Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }▷=∗  Q") : bi_scope.

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
  bi_fupd_mixin_fupd_frame_r E1 E2 (P Q : PROP) : (|={E1,E2}=> P) ∗ Q ={E1,E2}=∗ P ∗ Q;
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
Hint Mode BiBUpdFUpd + ! ! : typeclass_instances.

Class BiBUpdPlainly (PROP : sbi) `{!BiBUpd PROP, !BiPlainly PROP} :=
  bupd_plainly (P : PROP) : (|==> ■ P) -∗ P.
Hint Mode BiBUpdPlainly + ! ! : typeclass_instances.

Class BiFUpdPlainly (PROP : sbi) `{!BiFUpd PROP, !BiPlainly PROP} := {
  fupd_plain' E1 E2 E2' (P Q : PROP) `{!Plain P} :
    E1 ⊆ E2 →
    (Q ={E1, E2'}=∗ P) -∗ (|={E1, E2}=> Q) ={E1}=∗ (|={E1, E2}=> Q) ∗ P;
  later_fupd_plain E (P : PROP) `{!Plain P} :
    (▷ |={E}=> P) ={E}=∗ ▷ ◇ P;
}.
Hint Mode BiBUpdFUpd + ! ! : typeclass_instances.

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
  Lemma fupd_frame_r E1 E2 (P Q : PROP) : (|={E1,E2}=> P) ∗ Q ={E1,E2}=∗ P ∗ Q.
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
  Proof. by rewrite bupd_frame_l bi.wand_elim_l. Qed.
  Lemma bupd_wand_r P Q : (|==> P) ∗ (P -∗ Q) ==∗ Q.
  Proof. by rewrite bupd_frame_r bi.wand_elim_r. Qed.
  Lemma bupd_sep P Q : (|==> P) ∗ (|==> Q) ==∗ P ∗ Q.
  Proof. by rewrite bupd_frame_r bupd_frame_l bupd_trans. Qed.
End bupd_derived.

Section bupd_derived_sbi.
  Context {PROP : sbi} `{BiBUpd PROP}.
  Implicit Types P Q R : PROP.

  Lemma except_0_bupd P : ◇ (|==> P) ⊢ (|==> ◇ P).
  Proof.
    rewrite /sbi_except_0. apply bi.or_elim; eauto using bupd_mono, bi.or_intro_r.
    by rewrite -bupd_intro -bi.or_intro_l.
  Qed.

  Lemma bupd_plain P `{BiBUpdPlainly PROP, !Plain P} : (|==> P) ⊢ P.
  Proof. by rewrite {1}(plain P) bupd_plainly. Qed.
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

  Lemma fupd_frame_l E1 E2 P Q : (P ∗ |={E1,E2}=> Q) ={E1,E2}=∗ P ∗ Q.
  Proof. rewrite !(comm _ P); apply fupd_frame_r. Qed.
  Lemma fupd_wand_l E1 E2 P Q : (P -∗ Q) ∗ (|={E1,E2}=> P) ={E1,E2}=∗ Q.
  Proof. by rewrite fupd_frame_l bi.wand_elim_l. Qed.
  Lemma fupd_wand_r E1 E2 P Q : (|={E1,E2}=> P) ∗ (P -∗ Q) ={E1,E2}=∗ Q.
  Proof. by rewrite fupd_frame_r bi.wand_elim_r. Qed.

  Lemma fupd_trans_frame E1 E2 E3 P Q :
    ((Q ={E2,E3}=∗ emp) ∗ |={E1,E2}=> (Q ∗ P)) ={E1,E3}=∗ P.
  Proof.
    rewrite fupd_frame_l assoc -(comm _ Q) bi.wand_elim_r.
    by rewrite fupd_frame_r left_id fupd_trans.
  Qed.

  Lemma fupd_mask_frame_r E1 E2 Ef P :
    E1 ## Ef → (|={E1,E2}=> P) ={E1 ∪ Ef,E2 ∪ Ef}=∗ P.
  Proof.
    intros ?. rewrite -fupd_mask_frame_r' //. f_equiv.
    apply bi.impl_intro_l, bi.and_elim_r.
  Qed.
  Lemma fupd_mask_mono E1 E2 P : E1 ⊆ E2 → (|={E1}=> P) ={E2}=∗ P.
  Proof.
    intros (Ef&->&?)%subseteq_disjoint_union_L. by apply fupd_mask_frame_r.
  Qed.

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

  Lemma fupd_plain `{BiPlainly PROP, !BiFUpdPlainly PROP} E1 E2 P Q `{!Plain P} :
    E1 ⊆ E2 → (Q -∗ P) -∗ (|={E1, E2}=> Q) ={E1}=∗ (|={E1, E2}=> Q) ∗ P.
  Proof.
    intros HE. rewrite -(fupd_plain' _ _ E1) //. apply bi.wand_intro_l.
    by rewrite bi.wand_elim_r -fupd_intro.
  Qed.

  (** Fancy updates that take a step derived rules. *)
  Lemma step_fupd_wand E1 E2 P Q : (|={E1,E2}▷=> P) -∗ (P -∗ Q) -∗ |={E1,E2}▷=> Q.
  Proof.
    apply bi.wand_intro_l.
    by rewrite (bi.later_intro (P -∗ Q)%I) fupd_frame_l -bi.later_sep fupd_frame_l
               bi.wand_elim_l.
  Qed.

  Lemma step_fupd_mask_frame_r E1 E2 Ef P :
    E1 ## Ef → E2 ## Ef → (|={E1,E2}▷=> P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}▷=> P.
  Proof.
    intros. rewrite -fupd_mask_frame_r //. do 2 f_equiv. by apply fupd_mask_frame_r.
  Qed.

  Lemma step_fupd_mask_mono E1 E2 F1 F2 P :
    F1 ⊆ F2 → E1 ⊆ E2 → (|={E1,F2}▷=> P) ⊢ |={E2,F1}▷=> P.
  Proof.
    intros ??. rewrite -(left_id emp%I _ (|={E1,F2}▷=> P)%I).
    rewrite (fupd_intro_mask E2 E1 emp%I) //.
    rewrite fupd_frame_r -(fupd_trans E2 E1 F1). f_equiv.
    rewrite fupd_frame_l -(fupd_trans E1 F2 F1). f_equiv.
    rewrite (fupd_intro_mask F2 F1 (|={_,_}=> emp)%I) //.
    rewrite fupd_frame_r. f_equiv.
    rewrite [X in (X ∗ _)%I]bi.later_intro -bi.later_sep. f_equiv.
    rewrite fupd_frame_r -(fupd_trans F1 F2 E2). f_equiv.
    rewrite fupd_frame_l -(fupd_trans F2 E1 E2). f_equiv.
    by rewrite fupd_frame_r left_id.
  Qed.

  Lemma step_fupd_intro E1 E2 P : E2 ⊆ E1 → ▷ P -∗ |={E1,E2}▷=> P.
  Proof. intros. by rewrite -(step_fupd_mask_mono E2 _ _ E2) // -!fupd_intro. Qed.
End fupd_derived.
