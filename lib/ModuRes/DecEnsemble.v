(* Like Ensembles in Coq, but decidable. *)
Require Import Ssreflect.ssreflect.
Require Import CSetoid Predom.

Delimit Scope de_scope with de.
Local Open Scope general_if_scope.
Local Open Scope type.
Local Open Scope bool_scope.
Local Open Scope de_scope.

Section DecEnsemble.
  Context {T: Type}.

  CoInductive DecEnsemble := DE: (T -> bool) -> DecEnsemble.

  Implicit Types (de: DecEnsemble).

  Definition de_in t de: bool :=
    let (de):=de in de t.

End DecEnsemble.

Arguments DecEnsemble T: clear implicits.
Notation "t '∈' de" := (de_in t de) (at level 31, no associativity) : de_scope.

Section DecEnsembleOps.
  Context {T: Type}.
  Implicit Types (de: DecEnsemble T).

  Definition de_emp  : DecEnsemble T := DE (const false).
  Definition de_full : DecEnsemble T := DE (const true).

  Definition dele de1 de2 :=
    forall t, implb (t ∈ de1) (t ∈ de2) = true.

  Global Instance deeq_PreOrder: PreOrder dele.
  Proof.
    split.
    - intros ? ?. destruct (_ ∈ _); reflexivity.
    - intros x y z. unfold dele. intros IMxy IMyz t. move:(IMxy t) (IMyz t).
      destruct (t ∈ x), (t ∈ y), (t ∈ z); simpl; tauto.
  Qed.

  Definition deeq de1 de2 :=
    forall t, t ∈ de1 = t ∈ de2.

  Global Instance deeq_Equivalence: Equivalence deeq.
  Proof.
    split.
    - intros ?. unfold deeq. tauto.
    - intros ? ?. unfold deeq. now auto.
    - intros ? ? ? EQxy EQyz t. rewrite EQxy EQyz. reflexivity. 
  Qed.
  Global Instance deeq_type : Setoid (DecEnsemble T) := mkType deeq.

  Global Program Instance deeq_preo: preoType (DecEnsemble T) := mkPOType dele _.
  Next Obligation.
    move=>t1 t2 EQt s1 s2 EQs Hle t.
    rewrite -EQs. rewrite -EQt. exact:Hle.
  Qed.

  Definition de_cap de1 de2 :=
    DE (fun t => t ∈ de1 && t ∈ de2).
  Definition de_cup de1 de2 :=
    DE (fun t => t ∈ de1 || t ∈ de2).
  Definition de_minus de1 de2 :=
    DE (fun t => t ∈ de1 && negb (t ∈ de2)).
  Definition de_compl de :=
    DE (fun t => negb (t ∈ de)).
End DecEnsembleOps.

Notation "de1 ∩ de2" := (de_cap de1 de2) (at level 40) : de_scope.
Notation "de1 ∪ de2" := (de_cup de1 de2) (at level 50) : de_scope.
Notation "de1 \ de2"  := (de_minus de1 de2) (at level 35) : de_scope.
Notation "de1 # de2" := (de1 ∩ de2 == de_emp) (at level 70) : de_scope.

(* Some automation *)
Ltac de_destr := repeat (match goal with [ x : DecEnsemble _ |- _ ] => destruct x as [x] end).
Ltac de_in_destr := repeat (match goal with [ |- context[?t ∈ ?de] ] => destruct (t ∈ de) end).
Ltac de_auto_destr := repeat progress (simpl; unfold const; de_in_destr).
Ltac de_tauto := de_auto_destr; rewrite ?de_ft_eq ?de_tf_eq ?de_tt_eq ?de_ff_eq; repeat (split || intro); (reflexivity || discriminate || tauto).
Ltac de_auto_eq := destruct_conjs;
      let t := fresh "t" in move=>t;
      repeat (match goal with
              | [ H : _ |- _ ] => try move:(H t); clear H
              end);
      de_tauto.


Section DecEnsembleProps.
  Context {T: Type}.
  Implicit Types (de: DecEnsemble T).

  Lemma de_union_idem de :
    (de ∪ de) == de.
  Proof. repeat intro. de_tauto. Qed.

  Lemma de_isect_idem de :
    (de ∩ de) == de.
  Proof. repeat intro. de_tauto. Qed.

  Lemma de_emp_union de :
    (de ∪ de_emp) == de.
  Proof. repeat intro. de_tauto. Qed.

  Lemma de_full_union de :
    (de_full ∪ de) == de_full.
  Proof. repeat intro. de_tauto. Qed.

  Lemma de_emp_isect de :
    (de ∩ de_emp) == de_emp.
  Proof. repeat intro. de_tauto. Qed.

  Lemma de_full_isect de :
    (de_full ∩ de) == de.
  Proof. repeat intro. de_tauto. Qed.

  Lemma de_union_isect de1 de2 de3 :
    (de1 ∩ de2) ∪ (de1 ∩ de3) == de1 ∩ (de2 ∪ de3).
  Proof. repeat intro. de_tauto. Qed.

  Lemma de_isect_union de1 de2 de3 :
    (de1 ∪ de2) ∩ (de1 ∪ de3) == de1 ∪ (de2 ∩ de3).
  Proof. repeat intro. de_tauto. Qed.

  Global Instance de_union_com: Commutative (@de_cup T).
  Proof. repeat intro. de_tauto. Qed.

  Global Instance de_union_ass: Associative (@de_cup T).
  Proof. repeat intro. de_tauto. Qed.

  Global Instance de_isec_com: Commutative (@de_cap T).
  Proof. repeat intro. de_tauto. Qed.

  Global Instance de_isec_ass: Associative (@de_cap T).
  Proof. repeat intro. de_tauto. Qed.

  Global Instance de_union_equiv: Proper (equiv ==> equiv ==> equiv) (@de_cup T).
  Proof. do 6 intro. de_auto_eq. Qed.

  Global Instance de_isect_equiv: Proper (equiv ==> equiv ==> equiv) (@de_cap T).
  Proof. do 6 intro. de_auto_eq. Qed.

  Global Instance de_minus_equiv: Proper (equiv ==> equiv ==> equiv) (@de_minus T).
  Proof. do 6 intro. de_auto_eq. Qed.
  
  Global Instance de_compl_equiv: Proper (equiv ==> equiv) (@de_compl T).
  Proof. do 3 intro. de_auto_eq. Qed.

End DecEnsembleProps.

Section DecEqEnsemble.
  Context {T: Type} {eqT: DecEq T}.

  Definition de_set de t b :=
    DE (fun t' => if dec_eq t t' then b else t' ∈ de).

  Lemma de_set_eq de t b:
    t ∈ de_set de t b = b.
  Proof.
    simpl. rewrite DecEq_refl. reflexivity.
  Qed.

  Lemma de_set_neq de t b t':
    t <> t' -> t' ∈ de_set de t b = t' ∈ de.
  Proof.
    move=>Hneq. simpl.
    destruct (dec_eq t t') as [EQ|NEQ]; first contradiction.
    reflexivity.
  Qed.

End DecEqEnsemble.
  

Section DecNatEnsemble.
  Definition de_infinite (m : DecEnsemble nat) :=
    forall i, exists j, j >= i /\ j ∈ m = true.

  Lemma de_full_infinite : de_infinite de_full.
  Proof.
    intros i; exists i; split; [now auto with arith | reflexivity].
  Qed.

End DecNatEnsemble.

