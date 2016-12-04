From iris.base_logic Require Export derived.
From iris.proofmode Require Import classes class_instances.

Class Fractional {M} (Φ : Qp → uPred M) :=
  fractional p q : Φ (p + q)%Qp ⊣⊢ Φ p ∗ Φ q.
Class AsFractional {M} (P : uPred M) (Φ : Qp → uPred M) (q : Qp) :=
  as_fractional : P ⊣⊢ Φ q.

Arguments fractional {_ _ _} _ _.

Hint Mode AsFractional - + - - : typeclass_instances.
Hint Mode AsFractional - - + + : typeclass_instances.

Section fractional.
  Context {M : ucmraT}.
  Implicit Types P Q : uPred M.
  Implicit Types Φ : Qp → uPred M.
  Implicit Types p q : Qp.

  Lemma fractional_sep `{Fractional _ Φ} p q :
    Φ (p + q)%Qp ⊢ Φ p ∗ Φ q.
  Proof. by rewrite fractional. Qed.
  Lemma sep_fractional `{Fractional _ Φ} p q :
    Φ p ∗ Φ q ⊢ Φ (p + q)%Qp.
  Proof. by rewrite fractional. Qed.
  Lemma fractional_half_equiv `{Fractional _ Φ} p :
    Φ p ⊣⊢ Φ (p/2)%Qp ∗ Φ (p/2)%Qp.
  Proof. by rewrite -(fractional (p/2) (p/2)) Qp_div_2. Qed.
  Lemma fractional_half `{Fractional _ Φ} p :
    Φ p ⊢ Φ (p/2)%Qp ∗ Φ (p/2)%Qp.
  Proof. by rewrite fractional_half_equiv. Qed.
  Lemma half_fractional `{Fractional _ Φ} p q :
    Φ (p/2)%Qp ∗ Φ (p/2)%Qp ⊢ Φ p.
  Proof. by rewrite -fractional_half_equiv. Qed.

  (** Mult instances *)

  Global Instance mult_fractional_l Φ Ψ p :
    (∀ q, AsFractional (Φ q) Ψ (q * p)) → Fractional Ψ → Fractional Φ.
  Proof. intros AF F q q'. by rewrite !AF Qp_mult_plus_distr_l F. Qed.
  Global Instance mult_fractional_r Φ Ψ p :
    (∀ q, AsFractional (Φ q) Ψ (p * q)) → Fractional Ψ → Fractional Φ.
  Proof. intros AF F q q'. by rewrite !AF Qp_mult_plus_distr_r F. Qed.

  (* REMARK: These two instances do not work in either direction of the
     search:
       - In the forward direction, they make the search not terminate
       - In the backward direction, the higher order unification of Φ
         with the goal does not work. *)
  Instance mult_as_fractional_l P Φ p q :
    AsFractional P Φ (q * p) → AsFractional P (λ q, Φ (q * p)%Qp) q.
  Proof. done. Qed.
  Instance mult_as_fractional_r P Φ p q :
    AsFractional P Φ (p * q) → AsFractional P (λ q, Φ (p * q)%Qp) q.
  Proof. done. Qed.

  (** Proof mode instances *)
  Global Instance from_sep_fractional_fwd P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → Fractional Φ →
    AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    FromSep P P1 P2.
  Proof. by rewrite /FromSep=> -> -> -> ->. Qed.
  Global Instance from_sep_fractional_bwd P P1 P2 Φ q1 q2 :
    AsFractional P1 Φ q1 → AsFractional P2 Φ q2 → Fractional Φ →
    AsFractional P Φ (q1 + q2) →
    FromSep P P1 P2 | 10.
  Proof. by rewrite /FromSep=> -> -> <- ->. Qed.

  Global Instance from_sep_fractional_half_fwd P Q Φ q :
    AsFractional P Φ q → Fractional Φ →
    AsFractional Q Φ (q/2) →
    FromSep P Q Q | 10.
  Proof. by rewrite /FromSep -{1}(Qp_div_2 q)=> -> -> ->. Qed.
  Global Instance from_sep_fractional_half_bwd P Q Φ q :
    AsFractional P Φ (q/2) → Fractional Φ →
    AsFractional Q Φ q →
    FromSep Q P P.
  Proof. rewrite /FromSep=> -> <- ->. by rewrite Qp_div_2. Qed.

  Global Instance into_and_fractional P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → Fractional Φ →
    AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    IntoAnd false P P1 P2.
  Proof. by rewrite /AsFractional /IntoAnd=>->->->->. Qed.
  Global Instance into_and_fractional_half P Q Φ q :
    AsFractional P Φ q → Fractional Φ →
    AsFractional Q Φ (q/2) →
    IntoAnd false P Q Q | 100.
  Proof. by rewrite /AsFractional /IntoAnd -{1}(Qp_div_2 q)=>->->->. Qed.

  Global Instance frame_fractional_l R Q PP' QP' Φ r p p' :
    AsFractional R Φ r → AsFractional PP' Φ (p + p') → Fractional Φ →
    Frame R (Φ p) Q → MakeSep Q (Φ p') QP' → Frame R PP' QP'.
  Proof. rewrite /Frame=>->->-><-<-. by rewrite assoc. Qed.
  Global Instance frame_fractional_r R Q PP' PQ Φ r p p' :
    AsFractional R Φ r → AsFractional PP' Φ (p + p') → Fractional Φ →
    Frame R (Φ p') Q → MakeSep (Φ p) Q PQ → Frame R PP' PQ.
  Proof.
    rewrite /Frame=>->->-><-<-. rewrite !assoc. f_equiv. by rewrite comm.
  Qed.
  Global Instance frame_fractional_half P Q R Φ p:
    AsFractional R Φ (p/2) → AsFractional P Φ p → Fractional Φ →
    AsFractional Q Φ (p/2)%Qp →
    Frame R P Q.
  Proof. by rewrite /Frame -{2}(Qp_div_2 p)=>->->->->. Qed.
End fractional.
