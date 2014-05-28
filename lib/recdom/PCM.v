(** Partial commutative monoids. *)

Require Export Predom.
Require Import MetricCore.
Require Import PreoMet.

Class Associative {T} `{eqT : Setoid T} (op : T -> T -> T) :=
  assoc : forall t1 t2 t3, op t1 (op t2 t3) == op (op t1 t2) t3.
Class Commutative {T} `{eqT : Setoid T} (op : T -> T -> T) :=
  comm  : forall t1 t2, op t1 t2 == op t2 t1.

Section Definitions.
  Context (T : Type).
  Local Instance eqT : Setoid T | 20000 := discreteType.

  Class PCM_unit := pcm_unit : T.
  Class PCM_op   := pcm_op : option T -> option T -> option T.
  Class PCM {TU : PCM_unit} {TOP : PCM_op} :=
    mkPCM {
        pcm_op_assoc :> Associative (eqT := discreteType) pcm_op;
        pcm_op_comm  :> Commutative (eqT := discreteType) pcm_op;
        pcm_op_unit  :  forall t, pcm_op (Some pcm_unit) t = t;
        pcm_op_zero  :  forall t, pcm_op None t = None
      }.

End Definitions.

Notation "1" := (Some (pcm_unit _)) : pcm_scope.
Notation "0" := None : pcm_scope.
Notation "p · q" := (pcm_op _ p q) (at level 40, left associativity) : pcm_scope.

Delimit Scope pcm_scope with pcm.

(* PCMs with cartesian products of carriers. *)
Section Products.
  Context S T `{pcmS : PCM S, pcmT : PCM T}.
  Local Open Scope pcm_scope.
  Local Existing Instance eqT.

  Global Instance pcm_unit_prod : PCM_unit (S * T) := (pcm_unit S, pcm_unit T).
  Global Instance pcm_op_prod : PCM_op (S * T) :=
    fun ost1 ost2 =>
      match ost1, ost2 with
        | Some (s1, t1), Some (s2, t2) =>
          match Some s1 · Some s2, Some t1 · Some t2 with
            | Some sr, Some tr => Some (sr, tr)
            | _, _ => None
          end
        | _, _ => None
      end.
  Global Instance pcm_prod : PCM (S * T).
  Proof.
    split.
    - intros [[s1 t1] |]; [| reflexivity].
      intros [[s2 t2] |]; [| reflexivity].
      intros [[s3 t3] |];
        [unfold pcm_op, pcm_op_prod |
         unfold pcm_op at 1 2, pcm_op_prod;
           destruct (Some (s1, t1) · Some (s2, t2)) as [[s t] |]; simpl; tauto].
      assert (HS := assoc (Some s1) (Some s2) (Some s3));
        assert (HT := assoc (Some t1) (Some t2) (Some t3)).
      destruct (Some s1 · Some s2) as [s12 |];
        destruct (Some s2 · Some s3) as [s23 |]; [.. | reflexivity].
      + destruct (Some t1 · Some t2) as [t12 |];
        destruct (Some t2 · Some t3) as [t23 |]; [.. | reflexivity].
        * simpl in HS, HT; rewrite HS, HT; reflexivity.
        * erewrite comm, pcm_op_zero in HT by eassumption; simpl in HT.
          rewrite <- HT; destruct (Some s12 · Some s3); reflexivity.
        * erewrite pcm_op_zero in HT by eassumption; simpl in HT.
          rewrite HT; destruct (Some s1 · Some s23); reflexivity.
      + erewrite comm, pcm_op_zero in HS by eassumption; simpl in HS.
        destruct (Some t1 · Some t2) as [t12 |]; [| reflexivity].
        rewrite <- HS; reflexivity.
      + erewrite pcm_op_zero in HS by eassumption; simpl in HS.
        destruct (Some t2 · Some t3) as [t23 |]; [| reflexivity].
        rewrite HS; reflexivity.
    - intros [[s1 t1] |] [[s2 t2] |]; try reflexivity; []; simpl; unfold pcm_op, pcm_op_prod.
      rewrite (comm (Some s1)); assert (HT := comm (Some t1) (Some t2)).
      simpl in HT; rewrite HT; reflexivity.
    - intros [[s t] |]; [| reflexivity]; unfold pcm_op, pcm_op_prod; simpl.
      erewrite !pcm_op_unit by eassumption; reflexivity.
    - intros st; reflexivity.
  Qed.

End Products.

Section Order.
  Context T `{pcmT : PCM T}.
  Local Open Scope pcm_scope.
  Local Existing Instance eqT.

  Definition pcm_ord (t1 t2 : T) :=
    exists ot, ot · Some t1 = Some t2.

  Global Program Instance PCM_preo : preoType T | 0 := mkPOType pcm_ord.
  Next Obligation.
    split.
    - intros x; exists 1; eapply pcm_op_unit; assumption.
    - intros z yz xyz [y Hyz] [x Hxyz]; exists (x · y).
      rewrite <- assoc; congruence.
  Qed.

  Local Existing Instance option_preo_top.

  Global Instance prod_ord : Proper (pord ==> pord ==> pord) (pcm_op _).
  Proof.
    intros x1 x2 EQx y1 y2 EQy.
    destruct x2 as [x2 |]; [| erewrite pcm_op_zero by eassumption; exact I].
    destruct x1 as [x1 |]; [| contradiction]; destruct EQx as [x EQx].
    destruct y2 as [y2 |]; [| erewrite (comm (Some x2)), pcm_op_zero by eassumption; exact I].
    destruct y1 as [y1 |]; [| contradiction]; destruct EQy as [y EQy].
    destruct (Some x2 · Some y2) as [xy2 |] eqn: EQxy2; [| exact I].
    destruct (Some x1 · Some y1) as [xy1 |] eqn: EQxy1.
    - exists (x · y); rewrite <- EQxy1.
      rewrite <- assoc, (comm y), <- assoc, assoc, (comm (Some y1)); congruence.
    - rewrite <- EQx, <- EQy in EQxy2.
      rewrite <- assoc, (assoc (Some x1)), (comm (Some x1)), <- assoc in EQxy2.
      erewrite EQxy1, (comm y), comm, !pcm_op_zero in EQxy2 by eassumption.
      discriminate.
  Qed.

End Order.

(* Package of a monoid as a module type (for use with other modules). *)
Module Type PCM_T.

  Parameter res : Type.
  Declare Instance res_op : PCM_op res.
  Declare Instance res_unit : PCM_unit res.
  Declare Instance res_pcm : PCM res.

End PCM_T.
