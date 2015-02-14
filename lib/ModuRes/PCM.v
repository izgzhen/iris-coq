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
  Class PCM {TU : PCM_unit} {TOP : PCM_op}: Prop :=
    mkPCM {
        pcm_op_assoc  :> Associative pcm_op;
        pcm_op_comm   :> Commutative pcm_op;
        pcm_op_unit t : pcm_op (Some pcm_unit) t = t;
        pcm_op_zero t : pcm_op None t = None
      }.

End Definitions.

Notation "1" := (Some (pcm_unit _)) : pcm_scope.
Notation "0" := None : pcm_scope.
Notation "p · q" := (pcm_op _ p q) (at level 40, left associativity) : pcm_scope.

Delimit Scope pcm_scope with pcm.

(* FIXME having this with highest priority is really not a good idea. but necessary. *)
Instance pcm_eq T `{pcmT : PCM T} : Setoid T | 0 := eqT _.

(* PCMs with cartesian products of carriers. *)
Section Products.
  Context S T `{pcmS : PCM S, pcmT : PCM T}.
  Local Open Scope pcm_scope.

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
        [| unfold pcm_op at 1 2, pcm_op_prod;
           destruct (Some (s1, t1) · Some (s2, t2)) as [[s t] |]; simpl; tauto].
      assert (HS := assoc (Some s1) (Some s2) (Some s3));
        assert (HT := assoc (Some t1) (Some t2) (Some t3)).
      unfold pcm_op, pcm_op_prod.
      destruct (Some s1 · Some s2) as [s12 |];
        destruct (Some s2 · Some s3) as [s23 |]; [.. | reflexivity].
      + destruct (Some t1 · Some t2) as [t12 |];
        destruct (Some t2 · Some t3) as [t23 |]; [.. | reflexivity].
        * destruct (Some s1 · Some s23) as [s |]; destruct (Some s12 · Some s3) as [s' |];
          try (reflexivity || contradiction); simpl in HS; subst s'; [].
          destruct (Some t1 · Some t23) as [t |]; destruct (Some t12 · Some t3) as [t' |];
          try (reflexivity || contradiction); simpl in HT; subst t'; reflexivity.
        * erewrite comm, pcm_op_zero in HT by apply _.
          destruct (Some t12 · Some t3); [contradiction |].
          destruct (Some s12 · Some s3); reflexivity.
        * erewrite pcm_op_zero in HT by apply _.
          destruct (Some t1 · Some t23); [contradiction |].
          destruct (Some s1 · Some s23); reflexivity.
      + erewrite comm, pcm_op_zero in HS by apply _.
        destruct (Some t1 · Some t2) as [t12 |]; [| reflexivity].
        destruct (Some s12 · Some s3) as [s |]; [contradiction | reflexivity].
      + erewrite pcm_op_zero in HS by apply _.
        destruct (Some t2 · Some t3) as [t23 |]; [| reflexivity].
        destruct (Some s1 · Some s23); [contradiction | reflexivity].
    - intros [[s1 t1] |] [[s2 t2] |]; try reflexivity; []; simpl morph; unfold pcm_op, pcm_op_prod.
      assert (HS := comm (Some s1) (Some s2)); assert (HT := comm (Some t1) (Some t2)).
      destruct (Some s1 · Some s2); destruct (Some s2 · Some s1); try (contradiction || exact I); [].
      destruct (Some t1 · Some t2); destruct (Some t2 · Some t1); try (contradiction || exact I); [].
      simpl in HS, HT; subst s0 t0; reflexivity.
    - intros [[s t] |]; [| reflexivity]; unfold pcm_op, pcm_op_prod; simpl.
      erewrite !pcm_op_unit by eassumption; reflexivity.
    - intros st; reflexivity.
  Qed.

End Products.

Section Order.
  Context T `{pcmT : PCM T}.
  Local Open Scope pcm_scope.

  Global Instance pcm_op_equiv : Proper (equiv ==> equiv ==> equiv) (pcm_op T).
  Proof.
    intros [s1 |] [s2 |] EQs; try contradiction; [|];
    [intros [t1 |] [t2 |] EQt; try contradiction; [| rewrite (comm (Some s1)), (comm (Some s2)) ] | intros t1 t2 _];
    try (erewrite !pcm_op_zero by apply _; reflexivity); [].
    simpl in EQs, EQt; subst t2 s2; reflexivity.
  Qed.

  Definition pcm_ord (t1 t2 : T) :=
    exists td, Some td · Some t1 == Some t2.

  Global Program Instance PCM_preo : preoType T | 0 := mkPOType pcm_ord.
  Next Obligation.
    split.
    - intros x; eexists; erewrite pcm_op_unit by apply _; reflexivity.
    - intros z yz xyz [y Hyz] [x Hxyz]; unfold pcm_ord.
      rewrite <- Hyz, assoc in Hxyz; setoid_rewrite <- Hxyz.
      destruct (Some x · Some y) as [xy |] eqn: Hxy; [eexists; reflexivity |].
      erewrite pcm_op_zero in Hxyz by apply _; contradiction.
  Qed.

  Definition opcm_ord (t1 t2 : option T) :=
    exists otd, otd · t1 == t2.
  Global Program Instance opcm_preo : preoType (option T) :=
    mkPOType opcm_ord.
  Next Obligation.
    split.
    - intros r; exists 1; erewrite pcm_op_unit by apply _; reflexivity.
    - intros z yz xyz [y Hyz] [x Hxyz]; exists (x · y).
      rewrite <- Hxyz, <- Hyz; symmetry; apply assoc.
  Qed.

  Global Instance equiv_pord_pcm : Proper (equiv ==> equiv ==> equiv) (pord (T := option T)).
  Proof.
    intros s1 s2 EQs t1 t2 EQt; split; intros [s HS].
    - exists s; rewrite <- EQs, <- EQt; assumption.
    - exists s; rewrite EQs, EQt; assumption.
  Qed.

  Global Instance pcm_op_monic : Proper (pord ==> pord ==> pord) (pcm_op _).
  Proof.
    intros x1 x2 [x EQx] y1 y2 [y EQy]; exists (x · y).
    rewrite <- assoc, (comm y), <- assoc, assoc, (comm y1), EQx, EQy; reflexivity.
  Qed.

  Lemma ord_res_optRes r s :
    (r ⊑ s) <-> (Some r ⊑ Some s).
  Proof.
    split; intros HR.
     - destruct HR as [d EQ]; exists (Some d); assumption.
     - destruct HR as [[d |] EQ]; [exists d; assumption |].
       erewrite pcm_op_zero in EQ by apply _; contradiction.
  Qed.

  Lemma unit_min r : pcm_unit _ ⊑ r.
  Proof.
    exists r; now erewrite comm, pcm_op_unit by apply _.
  Qed.

End Order.

Section Exclusive.
  Context (T: Type).
  Local Open Scope pcm_scope.

  Inductive pcm_res_ex: Type :=
  | ex_own: T -> pcm_res_ex
  | ex_unit: pcm_res_ex.

  Global Instance pcm_unit_ex : PCM_unit pcm_res_ex := ex_unit.
  Global Instance pcm_op_ex : PCM_op pcm_res_ex :=
    fun ost1 ost2 =>
      match ost1, ost2 with
        | Some (ex_own s1), Some ex_unit => Some (ex_own s1)
        | Some ex_unit, Some (ex_own s2) => Some (ex_own s2)
        | Some ex_unit, Some ex_unit     => Some ex_unit
        | _, _                           => None
      end.
  Global Instance pcm_ex : PCM pcm_res_ex.
  Proof.
    split.
    - intros [[s1|]|] [[s2|]|] [[s3|]|]; reflexivity.
    - intros [[s1|]|] [[s2|]|]; reflexivity.
    - intros [[s1|]|]; reflexivity.
    - intros [[s1|]|]; reflexivity.
  Qed.

End Exclusive.


(* Package of a monoid as a module type (for use with other modules). *)
Module Type PCM_T.

  Parameter res : Type.
  Declare Instance res_op : PCM_op res.
  Declare Instance res_unit : PCM_unit res.
  Declare Instance res_pcm : PCM res.

End PCM_T.
