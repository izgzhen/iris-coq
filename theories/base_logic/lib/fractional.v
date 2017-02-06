From stdpp Require Import gmap gmultiset.
From iris.base_logic Require Export derived.
From iris.base_logic Require Import big_op.
From iris.proofmode Require Import classes class_instances.
Set Default Proof Using "Type".

Class Fractional {M} (Φ : Qp → uPred M) :=
  fractional p q : Φ (p + q)%Qp ⊣⊢ Φ p ∗ Φ q.
Class AsFractional {M} (P : uPred M) (Φ : Qp → uPred M) (q : Qp) := {
  as_fractional : P ⊣⊢ Φ q;
  as_fractional_fractional :> Fractional Φ
}.

Arguments fractional {_ _ _} _ _.

Hint Mode AsFractional - + - - : typeclass_instances.
Hint Mode AsFractional - - + + : typeclass_instances.

Section fractional.
  Context {M : ucmraT}.
  Implicit Types P Q : uPred M.
  Implicit Types Φ : Qp → uPred M.
  Implicit Types p q : Qp.

  Lemma fractional_split `{!Fractional Φ} p q :
    Φ (p + q)%Qp ⊢ Φ p ∗ Φ q.
  Proof. by rewrite fractional. Qed.
  Lemma fractional_combine `{!Fractional Φ} p q :
    Φ p ∗ Φ q ⊢ Φ (p + q)%Qp.
  Proof. by rewrite fractional. Qed.
  Lemma fractional_half_equiv `{!Fractional Φ} p :
    Φ p ⊣⊢ Φ (p/2)%Qp ∗ Φ (p/2)%Qp.
  Proof. by rewrite -(fractional (p/2) (p/2)) Qp_div_2. Qed.
  Lemma fractional_half `{!Fractional Φ} p :
    Φ p ⊢ Φ (p/2)%Qp ∗ Φ (p/2)%Qp.
  Proof. by rewrite fractional_half_equiv. Qed.
  Lemma half_fractional `{!Fractional Φ} p q :
    Φ (p/2)%Qp ∗ Φ (p/2)%Qp ⊢ Φ p.
  Proof. by rewrite -fractional_half_equiv. Qed.

  (** Fractional and logical connectives *)
  Global Instance persistent_fractional P :
    PersistentP P → Fractional (λ _, P).
  Proof. intros HP q q'. by apply uPred.always_sep_dup. Qed.

  Global Instance fractional_sep Φ Ψ :
    Fractional Φ → Fractional Ψ → Fractional (λ q, Φ q ∗ Ψ q)%I.
  Proof.
    intros ?? q q'. rewrite !fractional -!assoc. f_equiv.
    rewrite !assoc. f_equiv. by rewrite comm.
  Qed.

  Global Instance fractional_big_sepL {A} l Ψ :
    (∀ k (x : A), Fractional (Ψ k x)) →
    Fractional (M:=M) (λ q, [∗ list] k↦x ∈ l, Ψ k x q)%I.
  Proof.
    intros ? q q'. rewrite -big_sepL_sepL. by setoid_rewrite fractional.
  Qed.

  Global Instance fractional_big_sepM `{Countable K} {A} (m : gmap K A) Ψ :
    (∀ k (x : A), Fractional (Ψ k x)) →
    Fractional (M:=M) (λ q, [∗ map] k↦x ∈ m, Ψ k x q)%I.
  Proof.
    intros ? q q'. rewrite -big_sepM_sepM. by setoid_rewrite fractional.
  Qed.

  Global Instance fractional_big_sepS `{Countable A} (X : gset A) Ψ :
    (∀ x, Fractional (Ψ x)) →
    Fractional (M:=M) (λ q, [∗ set] x ∈ X, Ψ x q)%I.
  Proof.
    intros ? q q'. rewrite -big_sepS_sepS. by setoid_rewrite fractional.
  Qed.

  Global Instance fractional_big_sepMS `{Countable A} (X : gmultiset A) Ψ :
    (∀ x, Fractional (Ψ x)) →
    Fractional (M:=M) (λ q, [∗ mset] x ∈ X, Ψ x q)%I.
  Proof.
    intros ? q q'. rewrite -big_sepMS_sepMS. by setoid_rewrite fractional.
  Qed.

  (** Mult instances *)

  Global Instance mult_fractional_l Φ Ψ p :
    (∀ q, AsFractional (Φ q) Ψ (q * p)) → Fractional Φ.
  Proof.
    intros H q q'. rewrite ->!as_fractional, Qp_mult_plus_distr_l. by apply H.
  Qed.
  Global Instance mult_fractional_r Φ Ψ p :
    (∀ q, AsFractional (Φ q) Ψ (p * q)) → Fractional Φ.
  Proof.
    intros H q q'. rewrite ->!as_fractional, Qp_mult_plus_distr_r. by apply H.
  Qed.

  (* REMARK: These two instances do not work in either direction of the
     search:
       - In the forward direction, they make the search not terminate
       - In the backward direction, the higher order unification of Φ
         with the goal does not work. *)
  Instance mult_as_fractional_l P Φ p q :
    AsFractional P Φ (q * p) → AsFractional P (λ q, Φ (q * p)%Qp) q.
  Proof.
    intros H. split. apply H. eapply (mult_fractional_l _ Φ p).
    split. done. apply H.
  Qed.
  Instance mult_as_fractional_r P Φ p q :
    AsFractional P Φ (p * q) → AsFractional P (λ q, Φ (p * q)%Qp) q.
  Proof.
    intros H. split. apply H. eapply (mult_fractional_r _ Φ p).
    split. done. apply H.
  Qed.

  (** Proof mode instances *)
  Global Instance from_sep_fractional_fwd P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    FromSep P P1 P2.
  Proof. by rewrite /FromSep=>-[-> ->] [-> _] [-> _]. Qed.
  Global Instance from_sep_fractional_bwd P P1 P2 Φ q1 q2 :
    AsFractional P1 Φ q1 → AsFractional P2 Φ q2 → AsFractional P Φ (q1 + q2) →
    FromSep P P1 P2 | 10.
  Proof. by rewrite /FromSep=>-[-> _] [-> <-] [-> _]. Qed.

  Global Instance from_sep_fractional_half_fwd P Q Φ q :
    AsFractional P Φ q → AsFractional Q Φ (q/2) →
    FromSep P Q Q | 10.
  Proof. by rewrite /FromSep -{1}(Qp_div_2 q)=>-[-> ->] [-> _]. Qed.
  Global Instance from_sep_fractional_half_bwd P Q Φ q :
    AsFractional P Φ (q/2) → AsFractional Q Φ q →
    FromSep Q P P.
  Proof. rewrite /FromSep=>-[-> <-] [-> _]. by rewrite Qp_div_2. Qed.

  Global Instance into_and_fractional P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    IntoAnd false P P1 P2.
  Proof. by rewrite /IntoAnd=>-[-> ->] [-> _] [-> _]. Qed.
  Global Instance into_and_fractional_half P Q Φ q :
    AsFractional P Φ q → AsFractional Q Φ (q/2) →
    IntoAnd false P Q Q | 100.
  Proof. by rewrite /IntoAnd -{1}(Qp_div_2 q)=>-[->->][-> _]. Qed.

  (* The instance [frame_fractional] can be tried at all the nodes of
     the proof search. The proof search then fails almost always on
     [AsFractional R Φ r], but the slowdown is still noticeable.  For
     that reason, we factorize the three instances that could ave been
     defined for that purpose into one. *)
  Inductive FrameFractionalHyps R Φ RES : Qp → Qp → Prop :=
  | frame_fractional_hyps_l Q p p' r:
      Frame R (Φ p) Q → MakeSep Q (Φ p') RES →
      FrameFractionalHyps R Φ RES r (p + p')
  | frame_fractional_hyps_r Q p p' r:
      Frame R (Φ p') Q → MakeSep Q (Φ p) RES →
      FrameFractionalHyps R Φ RES r (p + p')
  | frame_fractional_hyps_half p:
      AsFractional RES Φ (p/2)%Qp → FrameFractionalHyps R Φ RES (p/2)%Qp p.
  Existing Class FrameFractionalHyps.
  Global Existing Instances frame_fractional_hyps_l frame_fractional_hyps_r
         frame_fractional_hyps_half.
  Global Instance frame_fractional R r Φ P p RES:
    AsFractional R Φ r → AsFractional P Φ p → FrameFractionalHyps R Φ RES r p →
    Frame R P RES.
  Proof.
    rewrite /Frame=>-[HR _][->?]H.
    revert H HR=>-[Q p0 p0' r0|Q p0 p0' r0|p0].
    - rewrite fractional=><-<-. by rewrite assoc.
    - rewrite fractional=><-<-=>_.
      rewrite (comm _ Q (Φ p0)) !assoc. f_equiv. by rewrite comm.
    - move=>-[-> _]->. by rewrite -fractional Qp_div_2.
  Qed.
End fractional.
