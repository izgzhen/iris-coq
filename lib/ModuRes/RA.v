(** Resource algebras: Commutative monoids with a decidable validity predicate. *)

Require Import Bool.
Require Import Predom.
Require Import CSetoid.
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
  Class RA_valid:= ra_valid : T -> Prop.
  Class RA {TU : RA_unit} {TOP : RA_op} {TV : RA_valid}: Prop :=
    mkRA {
        ra_op_proper       :> Proper (equiv ==> equiv ==> equiv) ra_op;
        ra_op_assoc        :> Associative ra_op;
        ra_op_comm         :> Commutative ra_op;
        ra_op_unit t       : ra_op ra_unit t == t;
        ra_valid_proper    :> Proper (equiv ==> iff) ra_valid;
        ra_valid_unit      : ra_valid ra_unit;
        ra_op_valid t1 t2  : ra_valid (ra_op t1 t2) -> ra_valid t1
      }.
End Definitions.
Arguments ra_valid {T} {_} t.

Delimit Scope ra_scope with ra.
Local Open Scope ra_scope.

Notation "1" := (ra_unit _) : ra_scope.
Notation "p · q" := (ra_op _ p q) (at level 40, left associativity) : ra_scope.
Notation "'↓' p" := (ra_valid p) (at level 35) : ra_scope.

(* General RA lemmas *)
Section RAs.
  Context {T} `{RA T}.

  Implicit Types (t : T).

  Lemma ra_op_unit2 t: t · 1 == t.
  Proof.
    rewrite comm. now eapply ra_op_unit.
  Qed.
  
  Lemma ra_op_valid2 t1 t2: ↓ (t1 · t2) -> ↓ t2.
  Proof.
    rewrite comm. now eapply ra_op_valid.
  Qed.

  Lemma ra_op_invalid t1 t2: ~↓t1 -> ~↓(t1 · t2).
  Proof.
    intros Hinval Hval.
    apply Hinval.
    eapply ra_op_valid; now eauto.
  Qed.

  Lemma ra_op_invalid2 t1 t2: ~↓t2 -> ~↓(t1 · t2).
  Proof.
    rewrite comm. now eapply ra_op_invalid.
  Qed.
End RAs.

(* RAs with cartesian products of carriers. *)
Section Products.
  Context S T `{raS : RA S, raT : RA T}.

  Global Instance ra_unit_prod : RA_unit (S * T) := (ra_unit S, ra_unit T).
  Global Instance ra_op_prod : RA_op (S * T) :=
    fun st1 st2 =>
      match st1, st2 with
        | (s1, t1), (s2, t2) => (s1 · s2, t1 · t2)
      end.
  Global Instance ra_valid_prod : RA_valid (S * T) :=
    fun st => match st with (s, t) => ra_valid s /\ ra_valid t
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
    - unfold ra_unit, ra_valid; simpl. split; eapply ra_valid_unit; now apply _.
    - intros [s1 t1] [s2 t2]. unfold ra_valid; simpl. intros [H1 H2]. split.
      + eapply ra_op_valid; now eauto.
      + eapply ra_op_valid; now eauto.
  Qed.
End Products.

Section ProductLemmas.
  Context {S T} `{raS : RA S, raT : RA T}.
    
  Lemma ra_op_prod_fst (st1 st2: S*T):
    fst (st1 · st2) = fst st1 · fst st2.
  Proof.
    destruct st1 as [s1 t1]. destruct st2 as [s2 t2]. reflexivity.
  Qed.
  
  Lemma ra_op_prod_snd (st1 st2: S*T):
    snd (st1 · st2) = snd st1 · snd st2.
  Proof.
    destruct st1 as [s1 t1]. destruct st2 as [s2 t2]. reflexivity.
  Qed.

  Lemma ra_prod_valid (st: S*T):
    ↓st <-> ↓(fst st) /\ ↓(snd st).
  Proof.
    destruct st as [s t]. unfold ra_valid, ra_valid_prod.
    tauto.
  Qed.

End ProductLemmas.

Section PositiveCarrier.
  Context {T} `{raT : RA T}.

  Definition ra_pos: Type := { t : T | ↓ t }.
  Coercion ra_proj (r:ra_pos): T := proj1_sig r.

  Implicit Types (t u : T) (r : ra_pos).

  Global Instance ra_pos_type : Setoid ra_pos := _.

  Definition ra_mk_pos t {VAL: ↓ t}: ra_pos := exist _ t VAL.

  Program Definition ra_pos_unit: ra_pos := exist _ 1 _.
  Next Obligation.
    now eapply ra_valid_unit; apply _.
  Qed.

  Lemma ra_proj_cancel t (VAL: ↓t):
    ra_proj (ra_mk_pos t (VAL:=VAL)) = t.
  Proof.
    reflexivity.
  Qed.

  Lemma ra_op_pos_valid t1 t2 r:
    t1 · t2 == ra_proj r -> ↓ t1.
  Proof.
    destruct r as [t Hval]; simpl. intros Heq. rewrite <-Heq in Hval.
    eapply ra_op_valid; eassumption.
  Qed.

  Lemma ra_op_pos_valid2 t1 t2 r:
    t1 · t2 == ra_proj r -> ↓ t2.
  Proof.
    rewrite comm. now eapply ra_op_pos_valid.
  Qed.

  Lemma ra_pos_valid r:
    ↓(ra_proj r).
  Proof.
    destruct r as [r VAL].
    exact VAL.
  Qed.

End PositiveCarrier.
Global Arguments ra_pos T {_}.
Notation "'⁺' T" := (ra_pos T) (at level 75) : type_scope.

(** Validity automation tactics *)
Ltac auto_valid_inner :=
  solve [ eapply ra_op_pos_valid; (eassumption || rewrite comm; eassumption)
        | eapply ra_op_pos_valid2; (eassumption || rewrite comm; eassumption)
        | eapply ra_op_valid; (eassumption || rewrite comm; eassumption) ].
Ltac auto_valid := idtac; match goal with
                     | |- @ra_valid ?T _ _ =>
                       let H := fresh in assert (H : RA T) by apply _; auto_valid_inner
                   end.

(* FIXME put the common parts into a helper tactic, and allow arbitrary tactics after "by" *)
Ltac exists_valid t tac := let H := fresh "Hval" in assert(H:(↓t)%ra); [tac|exists (ra_mk_pos t (VAL:=H) ) ].
Tactic Notation "exists↓" constr(t) := exists_valid t idtac.
Tactic Notation "exists↓" constr(t) "by" tactic(tac) := exists_valid t ltac:(now tac).

Ltac pose_valid name t tac := let H := fresh "Hval" in assert(H:(↓t)%ra); [tac|pose (name := ra_mk_pos t (VAL:=H) ) ].
Tactic Notation "pose↓" ident(name) ":=" constr(t) := pose_valid name t idtac.
Tactic Notation "pose↓" ident(name) ":=" constr(t) "by" tactic(tac) := pose_valid name t ltac:(now tac).


Section Order.
  Context T `{raT : RA T}.

  Implicit Types (t : T) (r s : ra_pos T).

  Definition pra_ord r1 r2 :=
    exists t, t · (ra_proj r1) == (ra_proj r2).

  Global Instance pra_ord_preo: PreOrder pra_ord.
  Proof.
    split.
    - intros x; exists 1. simpl. erewrite ra_op_unit by apply _; reflexivity.
    - intros z yz xyz [y Hyz] [x Hxyz]; unfold pra_ord.
      rewrite <- Hyz, assoc in Hxyz; setoid_rewrite <- Hxyz.
      exists (x · y). reflexivity.
  Qed.

  Global Program Instance pRA_preo : preoType (ra_pos T) | 0 := mkPOType pra_ord.

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

  Definition ra_ord t1 t2 :=
    exists t, t · t1 == t2.

  Global Instance ra_ord_preo: PreOrder ra_ord.
  Proof.
    split.
    - intros r; exists 1; erewrite ra_op_unit by apply _; reflexivity.
    - intros z yz xyz [y Hyz] [x Hxyz]; exists (x · y).
      rewrite <- Hxyz, <- Hyz; symmetry; apply assoc.
  Qed.
  
  Global Program Instance ra_preo : preoType T := mkPOType ra_ord.

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

  Lemma ord_res_pres r s :
    (r ⊑ s) <-> (ra_proj r ⊑ ra_proj s).
  Proof.
    split; intros HR.
    - destruct HR as [d EQ]. exists d. assumption.
    - destruct HR as [d EQ]. exists d. assumption.
  Qed.

End Order.

Section Exclusive.
  Context (T: Type) `{Setoid T}.
  
  Inductive ra_res_ex: Type :=
  | ex_own: T -> ra_res_ex
  | ex_unit: ra_res_ex
  | ex_bot: ra_res_ex.

  Implicit Types (r s : ra_res_ex).

  Definition ra_res_ex_eq r s: Prop :=
    match r, s with
      | ex_own t1, ex_own t2 => t1 == t2
      | ex_unit, ex_unit => True
      | ex_bot, ex_bot => True
      | _, _ => False
    end.

  Global Instance ra_eq_equiv : Equivalence ra_res_ex_eq.
  Proof.
    split.
    - intros [t| |]; simpl; now auto.
    - intros [t1| |] [t2| |]; simpl; now auto.
    - intros [t1| |] [t2| |] [t3| |]; simpl; try now auto.
      + intros ? ?. etransitivity; eassumption.
  Qed.

  Global Program Instance ra_type_ex : Setoid ra_res_ex :=
    mkType ra_res_ex_eq.
      
  Global Instance ra_unit_ex : RA_unit ra_res_ex := ex_unit.
  Global Instance ra_op_ex : RA_op ra_res_ex :=
    fun r s =>
      match r, s with
        | ex_own _, ex_unit => r
        | ex_unit, ex_own _ => s
        | ex_unit, ex_unit   => ex_unit
        | _, _               => ex_bot
      end.
  Global Instance ra_valid_ex : RA_valid ra_res_ex :=
    fun r => match r with
               | ex_bot => False
               | _      => True
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


(* Package a RA as a module type (for use with other modules). *)
Module Type RA_T.

  Parameter res : Type.
  Declare Instance res_type : Setoid res.
  Declare Instance res_op : RA_op res.
  Declare Instance res_unit : RA_unit res.
  Declare Instance res_valid : RA_valid res.
  Declare Instance res_ra : RA res.

End RA_T.
