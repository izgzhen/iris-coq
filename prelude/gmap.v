(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements finite maps and finite sets with keys of any countable
type. The implementation is based on [Pmap]s, radix-2 search trees. *)
Require Export prelude.countable prelude.fin_maps prelude.fin_map_dom.
Require Import prelude.pmap prelude.mapset.

(** * The data structure *)
(** We pack a [Pmap] together with a proof that ensures that all keys correspond
to codes of actual elements of the countable type. *)
Definition gmap_wf `{Countable K} {A} : Pmap A → Prop :=
  map_Forall (λ p _, encode <$> decode p = Some p).
Record gmap K `{Countable K} A := GMap {
  gmap_car : Pmap A;
  gmap_prf : bool_decide (gmap_wf gmap_car)
}.
Arguments GMap {_ _ _ _} _ _.
Arguments gmap_car {_ _ _ _} _.
Lemma gmap_eq `{Countable K} {A} (m1 m2 : gmap K A) :
  m1 = m2 ↔ gmap_car m1 = gmap_car m2.
Proof.
  split; [by intros ->|intros]. destruct m1, m2; simplify_equality'.
  f_equal; apply proof_irrel.
Qed.
Instance gmap_eq_eq `{Countable K} `{∀ x y : A, Decision (x = y)}
  (m1 m2 : gmap K A) : Decision (m1 = m2).
Proof.
 refine (cast_if (decide (gmap_car m1 = gmap_car m2)));
  abstract (by rewrite gmap_eq).
Defined.

(** * Operations on the data structure *)
Instance gmap_lookup `{Countable K} {A} : Lookup K A (gmap K A) := λ i m,
  let (m,_) := m in m !! encode i.
Instance gmap_empty `{Countable K} {A} : Empty (gmap K A) := GMap ∅ I.
Lemma gmap_partial_alter_wf `{Countable K} {A} (f : option A → option A) m i :
  gmap_wf m → gmap_wf (partial_alter f (encode i) m).
Proof.
  intros Hm p x. destruct (decide (encode i = p)) as [<-|?].
  * rewrite decode_encode; eauto.
  * rewrite lookup_partial_alter_ne by done. by apply Hm.
Qed.
Instance gmap_partial_alter `{Countable K} {A} :
    PartialAlter K A (gmap K A) := λ f i m,
  let (m,Hm) := m in GMap (partial_alter f (encode i) m)
    (bool_decide_pack _ (gmap_partial_alter_wf f m i
    (bool_decide_unpack _ Hm))).
Lemma gmap_fmap_wf `{Countable K} {A B} (f : A → B) m :
  gmap_wf m → gmap_wf (f <$> m).
Proof. intros ? p x. rewrite lookup_fmap, fmap_Some; intros (?&?&?); eauto. Qed.
Instance gmap_fmap `{Countable K} : FMap (gmap K) := λ A B f m,
  let (m,Hm) := m in GMap (f <$> m)
    (bool_decide_pack _ (gmap_fmap_wf f m (bool_decide_unpack _ Hm))).
Lemma gmap_omap_wf `{Countable K} {A B} (f : A → option B) m :
  gmap_wf m → gmap_wf (omap f m).
Proof. intros ? p x; rewrite lookup_omap, bind_Some; intros (?&?&?); eauto. Qed.
Instance gmap_omap `{Countable K} : OMap (gmap K) := λ A B f m,
  let (m,Hm) := m in GMap (omap f m)
    (bool_decide_pack _ (gmap_omap_wf f m (bool_decide_unpack _ Hm))).
Lemma gmap_merge_wf `{Countable K} {A B C}
    (f : option A → option B → option C) m1 m2 :
  let f' o1 o2 := match o1, o2 with None, None => None | _, _ => f o1 o2 end in
  gmap_wf m1 → gmap_wf m2 → gmap_wf (merge f' m1 m2).
Proof.
  intros f' Hm1 Hm2 p z; rewrite lookup_merge by done; intros.
  destruct (m1 !! _) eqn:?, (m2 !! _) eqn:?; naive_solver.
Qed.
Instance gmap_merge `{Countable K} : Merge (gmap K) := λ A B C f m1 m2,
  let (m1,Hm1) := m1 in let (m2,Hm2) := m2 in
  let f' o1 o2 := match o1, o2 with None, None => None | _, _ => f o1 o2 end in
  GMap (merge f' m1 m2) (bool_decide_pack _ (gmap_merge_wf f _ _
    (bool_decide_unpack _ Hm1) (bool_decide_unpack _ Hm2))).
Instance gmap_to_list `{Countable K} {A} : FinMapToList K A (gmap K A) := λ m,
  let (m,_) := m in omap (λ ix : positive * A,
    let (i,x) := ix in (,x) <$> decode i) (map_to_list m).

(** * Instantiation of the finite map interface *)
Instance gmap_finmap `{Countable K} : FinMap K (gmap K).
Proof.
  split.
  * unfold lookup; intros A [m1 Hm1] [m2 Hm2] Hm.
    apply gmap_eq, map_eq; intros i; simpl in *.
    apply bool_decide_unpack in Hm1; apply bool_decide_unpack in Hm2.
    apply option_eq; intros x; split; intros Hi.
    + pose proof (Hm1 i x Hi); simpl in *.
      by destruct (decode i); simplify_equality'; rewrite <-Hm.
    + pose proof (Hm2 i x Hi); simpl in *.
      by destruct (decode i); simplify_equality'; rewrite Hm.
  * done.
  * intros A f [m Hm] i; apply (lookup_partial_alter f m).
  * intros A f [m Hm] i j Hs; apply (lookup_partial_alter_ne f m).
    by contradict Hs; apply (injective encode).
  * intros A B f [m Hm] i; apply (lookup_fmap f m).
  * intros A [m Hm]; unfold map_to_list; simpl.
    apply bool_decide_unpack, map_Forall_to_list in Hm; revert Hm.
    induction (NoDup_map_to_list m) as [|[p x] l Hpx];
      inversion 1 as [|??? Hm']; simplify_equality'; [by constructor|].
    destruct (decode p) as [i|] eqn:?; simplify_equality'; constructor; eauto.
    rewrite elem_of_list_omap; intros ([p' x']&?&?); simplify_equality'.
    feed pose proof (proj1 (Forall_forall _ _) Hm' (p',x')); simpl in *; auto.
    by destruct (decode p') as [i'|]; simplify_equality'.
  * intros A [m Hm] i x; unfold map_to_list, lookup; simpl.
    apply bool_decide_unpack in Hm; rewrite elem_of_list_omap; split.
    + intros ([p' x']&Hp'&?); apply elem_of_map_to_list in Hp'.
      feed pose proof (Hm p' x'); simpl in *; auto.
      by destruct (decode p') as [i'|] eqn:?; simplify_equality'.
    + intros; exists (encode i,x); simpl.
      by rewrite elem_of_map_to_list, decode_encode.
  * intros A B f [m Hm] i; apply (lookup_omap f m).
  * intros A B C f ? [m1 Hm1] [m2 Hm2] i; unfold merge, lookup; simpl.
    set (f' o1 o2 := match o1, o2 with None,None => None | _, _ => f o1 o2 end).
    by rewrite lookup_merge by done; destruct (m1 !! _), (m2 !! _).
Qed.

(** * Finite sets *)
Notation gset K := (mapset (gmap K)).
Instance gset_dom `{Countable K} {A} : Dom (gmap K A) (gset K) := mapset_dom.
Instance gset_dom_spec `{Countable K} :
  FinMapDom K (gmap K) (gset K) := mapset_dom_spec.

(** * Fresh elements *)
(* This is pretty ad-hoc and just for the case of [gset positive]. We need a
notion of countable non-finite types to generalize this. *)
Instance gset_positive_fresh : Fresh positive (gset positive) := λ X,
  let 'Mapset (GMap m _) := X in fresh (dom _ m).
Instance gset_positive_fresh_spec : FreshSpec positive (gset positive).
Proof.
  split.
  * apply _.
  * by intros X Y; rewrite <-elem_of_equiv_L; intros ->.
  * intros [[m Hm]]; unfold fresh; simpl.
    by intros ?; apply (is_fresh (dom Pset m)), elem_of_dom_2 with ().
Qed.
