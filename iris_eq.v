Require Import ssreflect.
Require Import world_prop core_lang lang masks iris_core.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Set Bullet Behavior "Strict Subproofs".

(* PDS: This file is temporary. *)

Module Type IRIS_EQ (RL : RA_T) (C : CORE_LANG) (R: IRIS_RES RL C) (WP: WORLD_PROP R) (CORE: IRIS_CORE RL C R WP).
  Export CORE.

  Local Open Scope lang_scope.
  Local Open Scope ra_scope.
  Local Open Scope bi_scope.
  Local Open Scope iris_scope.
  
  Implicit Types (P Q : Props) (w : Wld) (n i k : nat) (r u v : res) (σ : state).

  (*
   * Valid biimplication, valid internal equality, and external
   * equality coincide.
   *)

  Notation "P ↔ Q" := ((P → Q) ∧ (Q → P)) (at level 90, no associativity) : iris_scope.

  Remark valid_biimp_intEq {P Q} : valid(P ↔ Q) -> valid(P === Q).
  Proof.
    move=> H wz nz rz w n r HLt. move/(_ w n r): H => [Hpq Hqp]. split.
    - by move/(_ _ (prefl w) _ _ (lerefl n) (prefl r)): Hpq.
    - by move/(_ _ (prefl w) _ _ (lerefl n) (prefl r)): Hqp.
  Qed.
  
  Remark valid_intEq_equiv {P Q} : valid(P === Q) -> P == Q.
  Proof. move=> H w n r; exact: H. Qed.

  Remark valid_equiv_biimp {P Q} : P == Q -> valid(P ↔ Q).
  Proof.
    by move=> H wz nz rz; split; move=> w HSw n r HLe HSr; move: H->.
  Qed.
  
  (*
   * Validity matters: Internal equality implies biimplication, but
   * not vice versa.
   *)

  Remark biimp_equiv {P Q}: P === Q ⊑ (P ↔ Q).
  Proof.
    have HLt n n' : n' <= n -> n' < S n by omega.
    move=> w n r H; split;
    move=> w' HSw' n' r' HLe' HSr' HP;
    move/(_ w' n' r' (HLt _ _ HLe')): H => [Hpq Hqp];
    [exact: Hpq | exact: Hqp].
  Qed.

  Goal forall P Q, (P ↔ Q) ⊑ (P === Q).
  Proof.
    move=> P Q w n r [Hpq Hqp] w' n' r' HLt; split.
    move=> HP.
    (*
     * Lacking w ⊑ w', we cannot apply Hpq.
     *)
  Abort.

End IRIS_EQ.
