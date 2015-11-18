(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files implements an efficient implementation of finite/cofinite sets
of positive binary naturals [positive]. *)
Require Export prelude.collections.
Require Import prelude.pmap prelude.mapset.
Local Open Scope positive_scope.

(** * The tree data structure *)
Inductive coPset_raw :=
  | coPLeaf : bool → coPset_raw
  | coPNode : bool → coPset_raw → coPset_raw → coPset_raw.

Instance coPset_raw_eq_dec (t1 t2 : coPset_raw) : Decision (t1 = t2).
Proof. solve_decision. Defined.

Fixpoint coPset_wf (t : coPset_raw) : bool :=
  match t with
  | coPLeaf _ => true
  | coPNode true (coPLeaf true) (coPLeaf true) => false
  | coPNode false (coPLeaf false) (coPLeaf false) => false
  | coPNode b l r => coPset_wf l && coPset_wf r
  end.
Arguments coPset_wf !_ / : simpl nomatch.

Lemma coPNode_wf_l b l r : coPset_wf (coPNode b l r) → coPset_wf l.
Proof. destruct b, l as [[]|],r as [[]|]; simpl; rewrite ?andb_True; tauto. Qed.
Lemma coPNode_wf_r b l r : coPset_wf (coPNode b l r) → coPset_wf r.
Proof. destruct b, l as [[]|],r as [[]|]; simpl; rewrite ?andb_True; tauto. Qed.
Local Hint Immediate coPNode_wf_l coPNode_wf_r.

Definition coPNode' (b : bool) (l r : coPset_raw) : coPset_raw :=
  match b, l, r with
  | true, coPLeaf true, coPLeaf true => coPLeaf true
  | false, coPLeaf false, coPLeaf false => coPLeaf false
  | _, _, _ => coPNode b l r
  end.
Arguments coPNode' _ _ _ : simpl never.
Lemma coPNode_wf b l r : coPset_wf l → coPset_wf r → coPset_wf (coPNode' b l r).
Proof. destruct b, l as [[]|], r as [[]|]; simpl; auto. Qed.
Hint Resolve coPNode_wf.

Fixpoint coPset_elem_of_raw (p : positive) (t : coPset_raw) {struct t} : bool :=
  match t, p with
  | coPLeaf b, _ => b
  | coPNode b l r, 1 => b
  | coPNode _ l _, p~0 => coPset_elem_of_raw p l
  | coPNode _ _ r, p~1 => coPset_elem_of_raw p r
  end.
Local Notation e_of := coPset_elem_of_raw.
Arguments coPset_elem_of_raw _ !_ / : simpl nomatch.
Lemma coPset_elem_of_coPNode' b l r p :
  e_of p (coPNode' b l r) = e_of p (coPNode b l r).
Proof. by destruct p, b, l as [[]|], r as [[]|]. Qed.

Lemma coPLeaf_wf t b : (∀ p, e_of p t = b) → coPset_wf t → t = coPLeaf b.
Proof.
  induction t as [b'|b' l IHl r IHr]; intros Ht ?; [f_equal; apply (Ht 1)|].
  assert (b' = b) by (apply (Ht 1)); subst.
  assert (l = coPLeaf b) as -> by (apply IHl; try apply (λ p, Ht (p~0)); eauto).
  assert (r = coPLeaf b) as -> by (apply IHr; try apply (λ p, Ht (p~1)); eauto).
  by destruct b.
Qed.
Lemma coPset_eq t1 t2 :
  (∀ p, e_of p t1 = e_of p t2) → coPset_wf t1 → coPset_wf t2 → t1 = t2.
Proof.
  revert t2.
  induction t1 as [b1|b1 l1 IHl r1 IHr]; intros [b2|b2 l2 r2] Ht ??; simpl in *.
  * f_equal; apply (Ht 1).
  * by discriminate (coPLeaf_wf (coPNode b2 l2 r2) b1).
  * by discriminate (coPLeaf_wf (coPNode b1 l1 r1) b2).
  * f_equal; [apply (Ht 1)| |].
    + apply IHl; try apply (λ x, Ht (x~0)); eauto.
    + apply IHr; try apply (λ x, Ht (x~1)); eauto.
Qed.

Fixpoint coPset_singleton_raw (p : positive) : coPset_raw :=
  match p with
  | 1 => coPNode true (coPLeaf false) (coPLeaf false)
  | p~0 => coPNode' false (coPset_singleton_raw p) (coPLeaf false)
  | p~1 => coPNode' false (coPLeaf false) (coPset_singleton_raw p)
  end.
Instance coPset_union_raw : Union coPset_raw :=
  fix go t1 t2 := let _ : Union _ := @go in
  match t1, t2 with
  | coPLeaf false, coPLeaf false => coPLeaf false
  | _, coPLeaf true => coPLeaf true
  | coPLeaf true, _ => coPLeaf true
  | coPNode b l r, coPLeaf false => coPNode' b l r
  | coPLeaf false, coPNode b l r => coPNode' b l r
  | coPNode b1 l1 r1, coPNode b2 l2 r2 => coPNode' (b1 || b2) (l1 ∪ l2) (r1 ∪ r2)
  end.
Local Arguments union _ _!_ !_ /.
Instance coPset_intersection_raw : Intersection coPset_raw :=
  fix go t1 t2 := let _ : Intersection _ := @go in
  match t1, t2 with
  | coPLeaf true, coPLeaf true => coPLeaf true
  | _, coPLeaf false => coPLeaf false
  | coPLeaf false, _ => coPLeaf false
  | coPNode b l r, coPLeaf true => coPNode' b l r
  | coPLeaf true, coPNode b l r => coPNode' b l r
  | coPNode b1 l1 r1, coPNode b2 l2 r2 => coPNode' (b1 && b2) (l1 ∩ l2) (r1 ∩ r2)
  end.
Local Arguments intersection _ _!_ !_ /.
Fixpoint coPset_opp_raw (t : coPset_raw) : coPset_raw :=
  match t with
  | coPLeaf b => coPLeaf (negb b)
  | coPNode b l r => coPNode' (negb b) (coPset_opp_raw l) (coPset_opp_raw r)
  end.

Lemma coPset_singleton_wf p : coPset_wf (coPset_singleton_raw p).
Proof. induction p; simpl; eauto. Qed.
Lemma coPset_union_wf t1 t2 : coPset_wf t1 → coPset_wf t2 → coPset_wf (t1 ∪ t2).
Proof. revert t2; induction t1 as [[]|[]]; intros [[]|[] ??]; simpl; eauto. Qed.
Lemma coPset_intersection_wf t1 t2 :
  coPset_wf t1 → coPset_wf t2 → coPset_wf (t1 ∩ t2).
Proof. revert t2; induction t1 as [[]|[]]; intros [[]|[] ??]; simpl; eauto. Qed.
Lemma coPset_opp_wf t : coPset_wf (coPset_opp_raw t).
Proof. induction t as [[]|[]]; simpl; eauto. Qed.
Lemma elem_of_coPset_singleton p q : e_of p (coPset_singleton_raw q) ↔ p = q.
Proof.
  split; [|by intros <-; induction p; simpl; rewrite ?coPset_elem_of_coPNode'].
  by revert q; induction p; intros [?|?|]; simpl;
    rewrite ?coPset_elem_of_coPNode'; intros; f_equal'; auto.
Qed.
Lemma elem_of_coPset_union t1 t2 p : e_of p (t1 ∪ t2) = e_of p t1 || e_of p t2.
Proof.
  by revert t2 p; induction t1 as [[]|[]]; intros [[]|[] ??] [?|?|]; simpl;
    rewrite ?coPset_elem_of_coPNode'; simpl;
    rewrite ?orb_true_l, ?orb_false_l, ?orb_true_r, ?orb_false_r.
Qed.
Lemma elem_of_coPset_intersection t1 t2 p :
  e_of p (t1 ∩ t2) = e_of p t1 && e_of p t2.
Proof.
  by revert t2 p; induction t1 as [[]|[]]; intros [[]|[] ??] [?|?|]; simpl;
    rewrite ?coPset_elem_of_coPNode'; simpl;
    rewrite ?andb_true_l, ?andb_false_l, ?andb_true_r, ?andb_false_r.
Qed.
Lemma elem_of_coPset_opp t p : e_of p (coPset_opp_raw t) = negb (e_of p t).
Proof.
  by revert p; induction t as [[]|[]]; intros [?|?|]; simpl;
    rewrite ?coPset_elem_of_coPNode'; simpl.
Qed.

(** * Packed together + set operations *)
Definition coPset := { t | coPset_wf t }.

Instance coPset_singleton : Singleton positive coPset := λ p,
  coPset_singleton_raw p ↾ coPset_singleton_wf _.
Instance coPset_elem_of : ElemOf positive coPset := λ p X, e_of p (`X).
Instance coPset_empty : Empty coPset := coPLeaf false ↾ I.
Definition coPset_all : coPset := coPLeaf true ↾ I.
Instance coPset_union : Union coPset := λ X Y,
  (`X ∪ `Y) ↾ coPset_union_wf _ _ (proj2_sig X) (proj2_sig Y).
Instance coPset_intersection : Intersection coPset := λ X Y,
  (`X ∩ `Y) ↾ coPset_intersection_wf _ _ (proj2_sig X) (proj2_sig Y).
Instance coPset_difference : Difference coPset := λ X Y,
  (`X ∩ coPset_opp_raw (`Y)) ↾
    coPset_intersection_wf _ _ (proj2_sig X) (coPset_opp_wf _).

Instance coPset_elem_of_dec (p : positive) (X : coPset) : Decision (p ∈ X) := _.
Instance coPset_collection : Collection positive coPset.
Proof.
  split; [split| |].
  * by intros ??.
  * intros p q. apply elem_of_coPset_singleton.
  * intros X Y p; unfold elem_of, coPset_elem_of, coPset_union; simpl.
    by rewrite elem_of_coPset_union, orb_True.
  * intros X Y p; unfold elem_of, coPset_elem_of, coPset_intersection; simpl.
    by rewrite elem_of_coPset_intersection, andb_True.
  * intros X Y p; unfold elem_of, coPset_elem_of, coPset_difference; simpl.
    by rewrite elem_of_coPset_intersection,
      elem_of_coPset_opp, andb_True, negb_True.
Qed.
Instance coPset_leibniz : LeibnizEquiv coPset.
Proof.
  intros X Y; split; [rewrite elem_of_equiv; intros HXY|by intros ->].
  apply (sig_eq_pi _), coPset_eq; try apply proj2_sig.
  intros p; apply eq_bool_prop_intro, (HXY p).
Qed.

(** Infinite sets *)
Fixpoint coPset_infinite_raw (t : coPset_raw) : bool :=
  match t with
  | coPLeaf b => b
  | coPNode b l r => coPset_infinite_raw l || coPset_infinite_raw r
  end.
Definition coPset_infinite (t : coPset) : bool := coPset_infinite_raw (`t).
Lemma coPset_infinite_coPNode b l r :
  coPset_infinite_raw (coPNode' b l r) = coPset_infinite_raw (coPNode b l r).
Proof. by destruct b, l as [[]|], r as [[]|]. Qed.

(** Splitting of infinite sets *)
Fixpoint coPset_l_raw (t : coPset_raw) : coPset_raw :=
  match t with
  | coPLeaf false => coPLeaf false
  | coPLeaf true => coPNode true (coPLeaf true) (coPLeaf false)
  | coPNode b l r => coPNode' b (coPset_l_raw l) (coPset_l_raw r)
  end.
Fixpoint coPset_r_raw (t : coPset_raw) : coPset_raw :=
  match t with
  | coPLeaf false => coPLeaf false
  | coPLeaf true => coPNode false (coPLeaf false) (coPLeaf true)
  | coPNode b l r => coPNode' false (coPset_r_raw l) (coPset_r_raw r)
  end.

Lemma coPset_l_wf t : coPset_wf (coPset_l_raw t).
Proof. induction t as [[]|]; simpl; auto. Qed.
Lemma coPset_r_wf t : coPset_wf (coPset_r_raw t).
Proof. induction t as [[]|]; simpl; auto. Qed.
Definition coPset_l (X : coPset) : coPset := coPset_l_raw (`X) ↾ coPset_l_wf _.
Definition coPset_r (X : coPset) : coPset := coPset_r_raw (`X) ↾ coPset_r_wf _.

Lemma coPset_lr_disjoint X : coPset_l X ∩ coPset_r X = ∅.
Proof.
  apply elem_of_equiv_empty_L; intros p; apply Is_true_false.
  destruct X as [t Ht]; simpl; clear Ht; rewrite elem_of_coPset_intersection.
  revert p; induction t as [[]|[]]; intros [?|?|]; simpl;
    rewrite ?coPset_elem_of_coPNode'; simpl;
    rewrite ?orb_true_l, ?orb_false_l, ?orb_true_r, ?orb_false_r; auto.
Qed.
Lemma coPset_lr_union X : coPset_l X ∪ coPset_r X = X.
Proof.
  apply elem_of_equiv_L; intros p; apply eq_bool_prop_elim.
  destruct X as [t Ht]; simpl; clear Ht; rewrite elem_of_coPset_union.
  revert p; induction t as [[]|[]]; intros [?|?|]; simpl;
    rewrite ?coPset_elem_of_coPNode'; simpl;
    rewrite ?orb_true_l, ?orb_false_l, ?orb_true_r, ?orb_false_r; auto.
Qed.
Lemma coPset_l_infinite X : coPset_infinite X → coPset_infinite (coPset_l X).
Proof.
  destruct X as [t Ht]; unfold coPset_infinite; simpl; clear Ht.
  induction t as [[]|]; simpl;
    rewrite ?coPset_infinite_coPNode; simpl; rewrite ?orb_True; tauto.
Qed.
Lemma coPset_r_infinite X : coPset_infinite X → coPset_infinite (coPset_r X).
Proof.
  destruct X as [t Ht]; unfold coPset_infinite; simpl; clear Ht.
  induction t as [[]|]; simpl;
    rewrite ?coPset_infinite_coPNode; simpl; rewrite ?orb_True; tauto.
Qed.

(** Conversion from psets *)
Fixpoint to_coPset_raw (t : Pmap_raw ()) : coPset_raw :=
  match t with
  | PLeaf => coPLeaf false
  | PNode None l r => coPNode false (to_coPset_raw l) (to_coPset_raw r)
  | PNode (Some _) l r => coPNode true (to_coPset_raw l) (to_coPset_raw r)
  end.
Lemma to_coPset_raw_wf t : Pmap_wf t → coPset_wf (to_coPset_raw t).
Proof.
  induction t as [|[] l IHl r IHr]; simpl; rewrite ?andb_True; auto.
  * intros [??]; destruct l as [|[]], r as [|[]]; simpl in *; auto.
  * destruct l as [|[]], r as [|[]]; simpl in *; rewrite ?andb_true_r;
      rewrite ?andb_True; rewrite ?andb_True in IHl, IHr; intuition.
Qed.
Definition to_coPset (X : Pset) : coPset :=
  to_coPset_raw (pmap_car (mapset_car X)) ↾ to_coPset_raw_wf _ (pmap_prf _).
Lemma elem_of_to_coPset X i : i ∈ to_coPset X ↔ i ∈ X.
Proof.
  destruct X as [[t Ht]]; change (e_of i (to_coPset_raw t) ↔ t !! i = Some ()).
  clear Ht; revert i.
  induction t as [|[[]|] l IHl r IHr]; intros [i|i|]; simpl; auto; by split.
Qed.
Instance Pmap_dom_Pset {A} : Dom (Pmap A) coPset := λ m, to_coPset (dom _ m).
Instance Pmap_dom_coPset: FinMapDom positive Pmap coPset.
Proof.
  split; try apply _; intros A m i; unfold dom, Pmap_dom_Pset.
  by rewrite elem_of_to_coPset, elem_of_dom.
Qed.
