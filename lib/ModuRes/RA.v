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
        ra_op_valid t1 t2  : ra_valid (ra_op t1 t2) = true -> ra_valid t1 = true
      }.
End Definitions.
Arguments ra_valid {T} {_} t.

Notation "1" := (ra_unit _) : ra_scope.
Notation "p · q" := (ra_op _ p q) (at level 40, left associativity) : ra_scope.
Notation "'✓' p" := (ra_valid p = true) (at level 35) : ra_scope.
Notation "'~' '✓' p" := (ra_valid p <> true) (at level 35) : ra_scope.
Delimit Scope ra_scope with ra.

Tactic Notation "decide✓" ident(t1) "eqn:" ident(H) := destruct (ra_valid t1) eqn:H; [|apply not_true_iff_false in H].


(* General RA lemmas *)
Section RAs.
  Context {T} `{RA T}.
  Local Open Scope ra_scope.

  Lemma ra_op_unit2 t: t · 1 == t.
  Proof.
    rewrite comm. now eapply ra_op_unit.
  Qed.
  
  Lemma ra_op_valid2 t1 t2: ✓ (t1 · t2) -> ✓ t2.
  Proof.
    rewrite comm. now eapply ra_op_valid.
  Qed.

  Lemma ra_op_invalid t1 t2: ~✓t1 -> ~✓(t1 · t2).
  Proof.
    intros Hinval Hval.
    apply Hinval.
    eapply ra_op_valid; now eauto.
  Qed.

  Lemma ra_op_invalid2 t1 t2: ~✓t2 -> ~✓(t1 · t2).
  Proof.
    rewrite comm. now eapply ra_op_invalid.
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
    fun st => match st with (s, t) => ra_valid s && ra_valid t
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
    - intros [s1 t1] [s2 t2]. unfold ra_valid; simpl. rewrite !andb_true_iff. intros [H1 H2]. split.
      + eapply ra_op_valid; now eauto.
      + eapply ra_op_valid; now eauto.
  Qed.

End Products.

Section PositiveCarrier.
  Context {T} `{raT : RA T}.
  Local Open Scope ra_scope.

  Definition ra_pos: Type := { r | ✓ r }.
  Coercion ra_proj (t:ra_pos): T := proj1_sig t.

  Definition ra_mk_pos t {VAL: ✓ t}: ra_pos := exist _ t VAL.

  Program Definition ra_pos_unit: ra_pos := exist _ 1 _.
  Next Obligation.
    now erewrite ra_valid_unit by apply _.
  Qed.

  Lemma ra_op_pos_valid t1 t2 t:
    t1 · t2 == ra_proj t -> ✓ t1.
  Proof.
    destruct t as [t Hval]; simpl. intros Heq. rewrite <-Heq in Hval.
    eapply ra_op_valid; eassumption.
  Qed.

  Lemma ra_op_pos_valid2 t1 t2 t:
    t1 · t2 == ra_proj t -> ✓ t2.
  Proof.
    rewrite comm. now eapply ra_op_pos_valid.
  Qed.

End PositiveCarrier.
Global Arguments ra_pos T {_}.

(** Validity automation tactics *)
Ltac auto_valid_inner :=
  solve [ eapply ra_op_pos_valid; (eassumption || rewrite comm; eassumption)
        | eapply ra_op_pos_valid2; (eassumption || rewrite comm; eassumption)
        | eapply ra_op_valid; (eassumption || rewrite comm; eassumption) ].
Ltac auto_valid := match goal with
                     | |- @ra_valid ?T _ _ = true =>
                       let H := fresh in assert (H : RA T) by apply _; auto_valid_inner
                   end.

(* FIXME put the common parts into a helper tactic, and allow arbitrary tactics after "by" *)
Tactic Notation "exists✓" constr(t) := let H := fresh "Hval" in assert(H:(✓t)%ra); [|exists (ra_mk_pos t (VAL:=H) ) ].
Tactic Notation "exists✓" constr(t) "by" "auto_valid" := let H := fresh "Hval" in assert(H:(✓t)%ra); [auto_valid|exists (ra_mk_pos t (VAL:=H) ) ].
Tactic Notation "pose✓" ident(name) ":=" constr(t) := let H := fresh "Hval" in assert(H:(✓t)%ra); [|pose (name := ra_mk_pos t (VAL:=H) ) ].
Tactic Notation "pose✓" ident(name) ":=" constr(t) "by" "auto_valid" := let H := fresh "Hval" in assert(H:(✓t)%ra); [auto_valid|pose (name := ra_mk_pos t (VAL:=H) ) ].


Section Order.
  Context T `{raT : RA T}.
  Local Open Scope ra_scope.

  Definition pra_ord (t1 t2 : ra_pos T) :=
    exists td, td · (ra_proj t1) == (ra_proj t2).

  Global Program Instance pRA_preo : preoType (ra_pos T) | 0 := mkPOType pra_ord.
  Next Obligation.
    split.
    - intros x; exists 1. simpl. erewrite ra_op_unit by apply _; reflexivity.
    - intros z yz xyz [y Hyz] [x Hxyz]; unfold pra_ord.
      rewrite <- Hyz, assoc in Hxyz; setoid_rewrite <- Hxyz.
      exists (x · y). reflexivity.
  Qed.

  Global Instance equiv_pord_pra : Proper (equiv ==> equiv ==> equiv) (pord (T := ra_pos T)).
  Proof.
    intros s1 s2 EQs t1 t2 EQt; split; intros [s HS].
    - exists s; rewrite <- EQs, <- EQt; assumption.
    - exists s; rewrite EQs, EQt; assumption.
  Qed.

  Lemma unit_min r : ra_pos_unit ⊑ r.
  Proof.
    exists (ra_proj r). simpl.
    now erewrite ra_op_unit2 by apply _.
  Qed.

  Definition ra_ord (t1 t2 : T) :=
    exists t, t · t1 == t2.
  Global Program Instance ra_preo : preoType T := mkPOType ra_ord.
  Next Obligation.
    split.
    - intros r; exists 1; erewrite ra_op_unit by apply _; reflexivity.
    - intros z yz xyz [y Hyz] [x Hxyz]; exists (x · y).
      rewrite <- Hxyz, <- Hyz; symmetry; apply assoc.
  Qed.

  Global Instance equiv_pord_ra : Proper (equiv ==> equiv ==> equiv) (pord (T := T)).
  Proof.
    intros s1 s2 EQs t1 t2 EQt; split; intros [s HS].
    - exists s; rewrite <- EQs, <- EQt; assumption.
    - exists s; rewrite EQs, EQt; assumption.
  Qed.

  Global Instance ra_op_monic : Proper (pord ++> pord ++> pord) (ra_op _).
  Proof.
    intros x1 x2 [x EQx] y1 y2 [y EQy]. exists (x · y).
    rewrite <- assoc, (comm y), <- assoc, assoc, (comm y1), EQx, EQy; reflexivity.
  Qed.

  Lemma ord_res_optRes r s :
    (r ⊑ s) <-> (ra_proj r ⊑ ra_proj s).
  Proof.
    split; intros HR.
    - destruct HR as [d EQ]. exists d. assumption.
    - destruct HR as [d EQ]. exists d. assumption.
  Qed.

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
