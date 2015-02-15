(** Resource algebras: Commutative monoids with a decidable validity predicate. *)

Require Import Bool.
Require Export Predom.
Require Import MetricCore.
Require Import PreoMet.

Class Associative {T} `{eqT : Setoid T} (op : T -> T -> T) :=
  assoc : forall t1 t2 t3, op t1 (op t2 t3) == op (op t1 t2) t3.
Class Commutative {T} `{eqT : Setoid T} (op : T -> T -> T) :=
  comm  : forall t1 t2, op t1 t2 == op t2 t1.

Section Definitions.
  Context (T : Type) `{Setoid T}.

  Class RA_unit := ra_unit : T.
  Class RA_op   := ra_op : T -> T -> T.
  Class RA_valid:= ra_valid : T -> bool.
  Class RA {TU : RA_unit} {TOP : RA_op} {TV : RA_valid}: Prop :=
    mkRA {
        ra_op_proper       :> Proper (equiv ==> equiv ==> equiv) ra_op;
        ra_op_assoc        :> Associative ra_op;
        ra_op_comm         :> Commutative ra_op;
        ra_op_unit t       : ra_op ra_unit t == t;
        ra_valid_proper    :> Proper (equiv ==> eq) ra_valid;
        ra_valid_unit      : ra_valid ra_unit = true;
        ra_op_invalid t1 t2: ra_valid t1 = false -> ra_valid (ra_op t1 t2) = false
      }.
End Definitions.

Notation "1" := (ra_unit _) : ra_scope.
Notation "p · q" := (ra_op _ p q) (at level 40, left associativity) : ra_scope.
Notation "'valid' p" := (ra_valid _ p) (at level 35) : ra_scope.

Delimit Scope ra_scope with ra.

(* General RA lemmas *)
Section RAs.
  Context {T} `{RA T}.
  Local Open Scope ra_scope.

  Lemma ra_op_unit2 t: t · 1 == t.
  Proof.
    rewrite comm. now eapply ra_op_unit.
  Qed.

  Lemma ra_op_invalid2 t1 t2: valid t2 = false -> valid (t1 · t2) = false.
  Proof.
    rewrite comm. now eapply ra_op_invalid.
  Qed.

  Lemma ra_op_valid t1 t2: valid (t1 · t2) = true -> valid t1 = true.
  Proof.
    intros Hval.
    destruct (valid t1) eqn:Heq; [reflexivity|].
    rewrite <-Hval. symmetry. now eapply ra_op_invalid.
  Qed.

  Lemma ra_op_valid2 t1 t2: valid (t1 · t2) = true -> valid t2 = true.
  Proof.
    rewrite comm. now eapply ra_op_valid.
  Qed.
End RAs.

(* RAs with cartesian products of carriers. *)
Section Products.
  Context S T `{raS : RA S, raT : RA T}.
  Local Open Scope ra_scope.

  Global Instance ra_unit_prod : RA_unit (S * T) := (ra_unit S, ra_unit T).
  Global Instance ra_op_prod : RA_op (S * T) :=
    fun st1 st2 =>
      match st1, st2 with
        | (s1, t1), (s2, t2) => (s1 · s2, t1 · t2)
      end.
  Global Instance ra_valid_prod : RA_valid (S * T) :=
    fun st => match st with (s, t) =>
                            valid s && valid t
              end.
  Global Instance ra_prod : RA (S * T).
  Proof.
    split.
    - intros [s1 t1] [s2 t2] [Heqs Heqt]. intros [s'1 t'1] [s'2 t'2] [Heqs' Heqt']. simpl in *.
      split; [rewrite Heqs, Heqs'|rewrite Heqt, Heqt']; reflexivity.
    - intros [s1 t1] [s2 t2] [s3 t3]. simpl; split; now rewrite ra_op_assoc.
    - intros [s1 t1] [s2 t2]. simpl; split; now rewrite ra_op_comm.
    - intros [s t]. simpl; split; now rewrite ra_op_unit.
    - intros [s1 t1] [s2 t2] [Heqs Heqt]. unfold ra_valid; simpl in *.
      rewrite Heqs, Heqt. reflexivity.
    - unfold ra_unit, ra_valid; simpl. erewrite !ra_valid_unit by apply _. reflexivity.
    - intros [s1 t1] [s2 t2]. unfold ra_valid; simpl. rewrite !andb_false_iff. intros [Hv|Hv].
      + left. now eapply ra_op_invalid.
      + right. now eapply ra_op_invalid.
  Qed.

End Products.

Section PositiveCarrier.
  Context {T} `{raT : RA T}.
  Local Open Scope ra_scope.

  Definition ra_pos: Type := { r | valid r = true }.
  Coercion ra_proj (t:ra_pos): T := proj1_sig t.

  Definition ra_mk_pos t (VAL: valid t = true): ra_pos := exist _ t VAL.

  Program Definition ra_pos_unit: ra_pos := exist _ 1 _.
  Next Obligation.
    now erewrite ra_valid_unit by apply _.
  Qed.

  Lemma ra_pos_mult_valid t1 t2 t:
    t1 · t2 == ra_proj t -> valid t1 = true.
  Proof.
    destruct t as [t Hval]; simpl. intros Heq. rewrite <-Heq in Hval.
    eapply ra_op_valid. eassumption.
  Qed.

  Lemma ra_pos_mult_valid2 t1 t2 t:
    t1 · t2 == ra_proj t -> valid t2 = true.
  Proof.
    rewrite comm. now eapply ra_pos_mult_valid.
  Qed.

End PositiveCarrier.
Global Arguments ra_pos T {_}.


Section Order.
  Context T `{raT : RA T}.
  Local Open Scope ra_scope.

  Definition ra_ord (t1 t2 : ra_pos T) :=
    exists td, (ra_proj td) · (ra_proj t1) == (ra_proj t2).

  Global Program Instance RA_preo : preoType (ra_pos T) | 0 := mkPOType ra_ord.
  Next Obligation.
    split.
    - intros x; exists ra_pos_unit. simpl. erewrite ra_op_unit by apply _; reflexivity.
    - intros z yz xyz [y Hyz] [x Hxyz]; unfold ra_ord.
      rewrite <- Hyz, assoc in Hxyz; setoid_rewrite <- Hxyz.
      assert (VAL:valid (ra_proj x · ra_proj y) = true).
      { now eapply ra_pos_mult_valid in Hxyz. }
      exists (ra_mk_pos (ra_proj x · ra_proj y) VAL). reflexivity.
  Qed.

(*  Definition opcm_ord (t1 t2 : option T) :=
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
  Qed.*)

End Order.

Section Exclusive.
  Context (T: Type) `{Setoid T}.
  Local Open Scope ra_scope.

  Inductive ra_res_ex: Type :=
  | ex_own: T -> ra_res_ex
  | ex_unit: ra_res_ex
  | ex_bot: ra_res_ex.

  Definition ra_res_ex_eq e1 e2: Prop :=
    match e1, e2 with
      | ex_own s1, ex_own s2 => s1 == s2
      | ex_unit, ex_unit => True
      | ex_bot, ex_bot => True
      | _, _ => False
    end.

  Global Program Instance ra_type_ex : Setoid ra_res_ex :=
    mkType ra_res_ex_eq.
  Next Obligation.
    split.
    - intros [t| |]; simpl; now auto.
    - intros [t1| |] [t2| |]; simpl; now auto.
    - intros [t1| |] [t2| |] [t3| |]; simpl; try now auto.
      + intros ? ?. etransitivity; eassumption.
  Qed.
      
  Global Instance ra_unit_ex : RA_unit ra_res_ex := ex_unit.
  Global Instance ra_op_ex : RA_op ra_res_ex :=
    fun e1 e2 =>
      match e1, e2 with
        | ex_own s1, ex_unit => ex_own s1
        | ex_unit, ex_own s2 => ex_own s2
        | ex_unit, ex_unit   => ex_unit
        | _, _               => ex_bot
      end.
  Global Instance ra_valid_ex : RA_valid ra_res_ex :=
    fun e => match e with
               | ex_bot => false
               | _      => true
             end.
  
  Global Instance ra_ex : RA ra_res_ex.
  Proof.
    split.
    - intros [t1| |] [t2| |] Heqt [t'1| |] [t'2| |] Heqt'; simpl; now auto.  
    - intros [s1| |] [s2| |] [s3| |]; reflexivity.
    - intros [s1| |] [s2| |]; reflexivity.
    - intros [s1| |]; reflexivity.
    - intros [t1| |] [t2| |] Heqt; unfold ra_valid; simpl in *; now auto.
    - reflexivity.
    - intros [t1| |] [t2| |]; unfold ra_valid; simpl; now auto.
  Qed.

End Exclusive.


(* Package of a monoid as a module type (for use with other modules). *)
Module Type RA_T.

  Parameter res : Type.
  Declare Instance res_type : Setoid res.
  Declare Instance res_op : RA_op res.
  Declare Instance res_unit : RA_unit res.
  Declare Instance res_valid : RA_valid res.
  Declare Instance res_ra : RA res.

End RA_T.
