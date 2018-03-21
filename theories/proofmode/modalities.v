From iris.bi Require Export bi.
From stdpp Require Import namespaces.
Set Default Proof Using "Type".
Import bi.

(** The `iModIntro` tactic is not tied the Iris modalities, but can be
instantiated with a variety of modalities.

In order to plug in a modality, one has to decide for both the intuitionistic and
spatial context what action should be performed upon introducing the modality:

- Introduction is only allowed when the context is empty.
- Introduction is only allowed when all hypotheses satisfy some predicate
  `C : PROP → Prop` (where `C` should be a type class).
- Introduction will transform each hypotheses using a type class
  `C : PROP → PROP → Prop`, where the first parameter is the input and the
  second parameter is the output. Hypotheses that cannot be transformed (i.e.
  for which no instance of `C` can be found) will be cleared.
- Introduction will clear the context.
- Introduction will keep the context as-if.

Formally, these actions correspond to the following inductive type: *)

Inductive modality_intro_spec (PROP1 : bi) : bi → Type :=
  | MIEnvIsEmpty {PROP2 : bi} : modality_intro_spec PROP1 PROP2
  | MIEnvForall (C : PROP1 → Prop) : modality_intro_spec PROP1 PROP1
  | MIEnvTransform {PROP2 : bi} (C : PROP2 → PROP1 → Prop) : modality_intro_spec PROP1 PROP2
  | MIEnvClear {PROP2} : modality_intro_spec PROP1 PROP2
  | MIEnvId : modality_intro_spec PROP1 PROP1.
Arguments MIEnvIsEmpty {_ _}.
Arguments MIEnvForall {_} _.
Arguments MIEnvTransform {_ _} _.
Arguments MIEnvClear {_ _}.
Arguments MIEnvId {_}.

Notation MIEnvFilter C := (MIEnvTransform (TCDiag C)).

Definition modality_intro_spec_intuitionistic {PROP1 PROP2}
    (s : modality_intro_spec PROP1 PROP2) : (PROP1 → PROP2) → Prop :=
  match s with
  | MIEnvIsEmpty => λ M, True
  | MIEnvForall C => λ M,
     (∀ P, C P → □ P ⊢ M (□ P)) ∧
     (∀ P Q, M P ∧ M Q ⊢ M (P ∧ Q))
  | MIEnvTransform C => λ M,
     (∀ P Q, C P Q → □ P ⊢ M (□ Q)) ∧
     (∀ P Q, M P ∧ M Q ⊢ M (P ∧ Q))
  | MIEnvClear => λ M, True
  | MIEnvId => λ M, ∀ P, □ P ⊢ M (□ P)
  end.

Definition modality_intro_spec_spatial {PROP1 PROP2}
    (s : modality_intro_spec PROP1 PROP2) : (PROP1 → PROP2) → Prop :=
  match s with
  | MIEnvIsEmpty => λ M, True
  | MIEnvForall C => λ M, ∀ P, C P → P ⊢ M P
  | MIEnvTransform C => λ M, ∀ P Q, C P Q → P ⊢ M Q
  | MIEnvClear => λ M, ∀ P, Absorbing (M P)
  | MIEnvId => λ M, ∀ P, P ⊢ M P
  end.

(* A modality is then a record packing together the modality with the laws it
should satisfy to justify the given actions for both contexts: *)
Record modality_mixin {PROP1 PROP2 : bi} (M : PROP1 → PROP2)
    (pspec sspec : modality_intro_spec PROP1 PROP2) := {
  modality_mixin_intuitionistic : modality_intro_spec_intuitionistic pspec M;
  modality_mixin_spatial : modality_intro_spec_spatial sspec M;
  modality_mixin_emp : emp ⊢ M emp;
  modality_mixin_mono P Q : (P ⊢ Q) → M P ⊢ M Q;
  modality_mixin_sep P Q : M P ∗ M Q ⊢ M (P ∗ Q)
}.

Record modality (PROP1 PROP2 : bi) := Modality {
  modality_car :> PROP1 → PROP2;
  modality_intuitionistic_spec : modality_intro_spec PROP1 PROP2;
  modality_spatial_spec : modality_intro_spec PROP1 PROP2;
  modality_mixin_of :
    modality_mixin modality_car modality_intuitionistic_spec modality_spatial_spec
}.
Arguments Modality {_ _} _ {_ _} _.
Arguments modality_intuitionistic_spec {_ _} _.
Arguments modality_spatial_spec {_ _} _.

Section modality.
  Context {PROP1 PROP2} (M : modality PROP1 PROP2).

  Lemma modality_intuitionistic_transform C P Q :
    modality_intuitionistic_spec M = MIEnvTransform C → C P Q → □ P ⊢ M (□ Q).
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma modality_and_transform C P Q :
    modality_intuitionistic_spec M = MIEnvTransform C → M P ∧ M Q ⊢ M (P ∧ Q).
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma modality_spatial_transform C P Q :
    modality_spatial_spec M = MIEnvTransform C → C P Q → P ⊢ M Q.
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma modality_spatial_clear P :
    modality_spatial_spec M = MIEnvClear → Absorbing (M P).
  Proof. destruct M as [??? []]; naive_solver. Qed.

  Lemma modality_emp : emp ⊢ M emp.
  Proof. eapply modality_mixin_emp, modality_mixin_of. Qed.
  Lemma modality_mono P Q : (P ⊢ Q) → M P ⊢ M Q.
  Proof. eapply modality_mixin_mono, modality_mixin_of. Qed.
  Lemma modality_sep P Q : M P ∗ M Q ⊢ M (P ∗ Q).
  Proof. eapply modality_mixin_sep, modality_mixin_of. Qed.
  Global Instance modality_mono' : Proper ((⊢) ==> (⊢)) M.
  Proof. intros P Q. apply modality_mono. Qed.
  Global Instance modality_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) M.
  Proof. intros P Q. apply modality_mono. Qed.
  Global Instance modality_proper : Proper ((≡) ==> (≡)) M.
  Proof. intros P Q. rewrite !equiv_spec=> -[??]; eauto using modality_mono. Qed.
End modality.

Section modality1.
  Context {PROP} (M : modality PROP PROP).

  Lemma modality_intuitionistic_forall C P :
    modality_intuitionistic_spec M = MIEnvForall C → C P → □ P ⊢ M (□ P).
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma modality_and_forall C P Q :
    modality_intuitionistic_spec M = MIEnvForall C → M P ∧ M Q ⊢ M (P ∧ Q).
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma modality_intuitionistic_id P :
    modality_intuitionistic_spec M = MIEnvId → □ P ⊢ M (□ P).
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma modality_spatial_forall C P :
    modality_spatial_spec M = MIEnvForall C → C P → P ⊢ M P.
  Proof. destruct M as [??? []]; naive_solver. Qed.
  Lemma modality_spatial_id P :
    modality_spatial_spec M = MIEnvId → P ⊢ M P.
  Proof. destruct M as [??? []]; naive_solver. Qed.

  Lemma modality_intuitionistic_forall_big_and C Ps :
    modality_intuitionistic_spec M = MIEnvForall C →
    Forall C Ps → □ [∧] Ps ⊢ M (□ [∧] Ps).
  Proof.
    induction 2 as [|P Ps ? _ IH]; simpl.
    - by rewrite intuitionistically_True_emp -modality_emp.
    - rewrite intuitionistically_and -modality_and_forall // -IH.
      by rewrite {1}(modality_intuitionistic_forall _ P).
  Qed.
  Lemma modality_spatial_forall_big_sep C Ps :
    modality_spatial_spec M = MIEnvForall C →
    Forall C Ps → [∗] Ps ⊢ M ([∗] Ps).
  Proof.
    induction 2 as [|P Ps ? _ IH]; simpl.
    - by rewrite -modality_emp.
    - by rewrite -modality_sep -IH {1}(modality_spatial_forall _ P).
  Qed.
End modality1.

(** The identity modality [modality_id] can be used in combination with
[FromModal modality_id] to support introduction for modalities that enjoy
[P ⊢ M P]. This is done by defining an instance [FromModal modality_id (M P) P],
which will instruct [iModIntro] to introduce the modality without modifying the
proof mode context. Examples of such modalities are [bupd], [fupd], [except_0],
[monPred_subjectively] and [bi_absorbingly]. *)
Lemma modality_id_mixin {PROP : bi} : modality_mixin (@id PROP) MIEnvId MIEnvId.
Proof. split; simpl; eauto. Qed.
Definition modality_id {PROP : bi} := Modality (@id PROP) modality_id_mixin.
