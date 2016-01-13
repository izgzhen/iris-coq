Require Export modures.cmra prelude.gmap.
Require Import modures.option.

Section map.
Context `{Countable K}.

(* COFE *)
Global Instance map_dist `{Dist A} : Dist (gmap K A) := λ n m1 m2,
  ∀ i, m1 !! i ={n}= m2 !! i.
Program Definition map_chain `{Dist A} (c : chain (gmap K A))
  (k : K) : chain (option A) := {| chain_car n := c n !! k |}.
Next Obligation. by intros A ? c k n i ?; apply (chain_cauchy c). Qed.
Global Instance map_compl `{Cofe A} : Compl (gmap K A) := λ c,
  map_imap (λ i _, compl (map_chain c i)) (c 1).
Global Instance map_cofe `{Cofe A} : Cofe (gmap K A).
Proof.
  split.
  * intros m1 m2; split.
    + by intros Hm n k; apply equiv_dist.
    + intros Hm k; apply equiv_dist; intros n; apply Hm.
  * intros n; split.
    + by intros m k.
    + by intros m1 m2 ? k.
    + by intros m1 m2 m3 ?? k; transitivity (m2 !! k).
  * by intros n m1 m2 ? k; apply dist_S.
  * by intros m1 m2 k.
  * intros c n k; unfold compl, map_compl; rewrite lookup_imap.
    destruct (decide (n = 0)) as [->|]; [constructor|].
    feed inversion (λ H, chain_cauchy c 1 n H k); simpl; auto with lia.
    by rewrite conv_compl; simpl; apply reflexive_eq.
Qed.
Global Instance lookup_ne `{Dist A} n k :
  Proper (dist n ==> dist n) (lookup k : gmap K A → option A).
Proof. by intros m1 m2. Qed.
Global Instance insert_ne `{Dist A} (i : K) n :
  Proper (dist n ==> dist n ==> dist n) (insert (M:=gmap K A) i).
Proof.
  intros x y ? m m' ? j; destruct (decide (i = j)); simplify_map_equality;
    [by constructor|by apply lookup_ne].
Qed.
Global Instance singleton_ne `{Cofe A} (i : K) n :
  Proper (dist n ==> dist n) (singletonM i : A → gmap K A).
Proof. by intros ???; apply insert_ne. Qed.
Global Instance delete_ne `{Dist A} (i : K) n :
  Proper (dist n ==> dist n) (delete (M:=gmap K A) i).
Proof.
  intros m m' ? j; destruct (decide (i = j)); simplify_map_equality;
    [by constructor|by apply lookup_ne].
Qed.
Global Instance map_empty_timeless `{Dist A, Equiv A} : Timeless (∅ : gmap K A).
Proof.
  intros m Hm i; specialize (Hm i); rewrite lookup_empty in Hm |- *.
  inversion_clear Hm; constructor.
Qed.
Global Instance map_lookup_timeless `{Cofe A} (m : gmap K A) i :
  Timeless m → Timeless (m !! i).
Proof.
  intros ? [x|] Hx; [|by symmetry; apply (timeless _)].
  assert (m ={1}= <[i:=x]> m)
    by (by symmetry in Hx; inversion Hx; cofe_subst; rewrite insert_id).
  by rewrite (timeless m (<[i:=x]>m)) // lookup_insert.
Qed.
Global Instance map_ra_insert_timeless `{Cofe A} (m : gmap K A) i x :
  Timeless x → Timeless m → Timeless (<[i:=x]>m).
Proof.
  intros ?? m' Hm j; destruct (decide (i = j)); simplify_map_equality.
  { by apply (timeless _); rewrite -Hm lookup_insert. }
  by apply (timeless _); rewrite -Hm lookup_insert_ne.
Qed.
Global Instance map_ra_singleton_timeless `{Cofe A} (i : K) (x : A) :
  Timeless x → Timeless ({[ i ↦ x ]} : gmap K A) := _.
Global Instance map_fmap_ne `{Dist A, Dist B} (f : A → B) n :
  Proper (dist n ==> dist n) f →
  Proper (dist n ==> dist n) (fmap (M:=gmap K) f).
Proof. by intros ? m m' Hm k; rewrite !lookup_fmap; apply option_fmap_ne. Qed.
Canonical Structure mapC (A : cofeT) : cofeT := CofeT (gmap K A).
Definition mapC_map {A B} (f: A -n> B) : mapC A -n> mapC B :=
  CofeMor (fmap f : mapC A → mapC B).
Global Instance mapC_map_ne {A B} n :
  Proper (dist n ==> dist n) (@mapC_map A B).
Proof.
  intros f g Hf m k; rewrite /= !lookup_fmap.
  destruct (_ !! k) eqn:?; simpl; constructor; apply Hf.
Qed.

(* CMRA *)
Global Instance map_op `{Op A} : Op (gmap K A) := merge op.
Global Instance map_unit `{Unit A} : Unit (gmap K A) := fmap unit.
Global Instance map_valid `{Valid A} : Valid (gmap K A) := λ m, ∀ i, ✓ (m !! i).
Global Instance map_validN `{ValidN A} : ValidN (gmap K A) := λ n m,
  ∀ i, ✓{n} (m!!i).
Global Instance map_minus `{Minus A} : Minus (gmap K A) := merge minus.
Lemma lookup_op `{Op A} m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
Proof. by apply lookup_merge. Qed.
Lemma lookup_minus `{Minus A} m1 m2 i : (m1 ⩪ m2) !! i = m1 !! i ⩪ m2 !! i.
Proof. by apply lookup_merge. Qed.
Lemma lookup_unit `{Unit A} m i : unit m !! i = unit (m !! i).
Proof. by apply lookup_fmap. Qed.
Lemma map_included_spec `{CMRA A} (m1 m2 : gmap K A) :
  m1 ≼ m2 ↔ ∀ i, m1 !! i ≼ m2 !! i.
Proof.
  split.
  * by intros [m Hm]; intros i; exists (m !! i); rewrite -lookup_op Hm.
  * intros Hm; exists (m2 ⩪ m1); intros i.
    by rewrite lookup_op lookup_minus ra_op_minus.
Qed.
Lemma map_includedN_spec `{CMRA A} (m1 m2 : gmap K A) n :
  m1 ≼{n} m2 ↔ ∀ i, m1 !! i ≼{n} m2 !! i.
Proof.
  split.
  * by intros [m Hm]; intros i; exists (m !! i); rewrite -lookup_op Hm.
  * intros Hm; exists (m2 ⩪ m1); intros i.
    by rewrite lookup_op lookup_minus cmra_op_minus.
Qed.
Global Instance map_cmra `{CMRA A} : CMRA (gmap K A).
Proof.
  split.
  * apply _.
  * by intros n m1 m2 m3 Hm i; rewrite !lookup_op (Hm i).
  * by intros n m1 m2 Hm i; rewrite !lookup_unit (Hm i).
  * by intros n m1 m2 Hm ? i; rewrite -(Hm i).
  * by intros n m1 m1' Hm1 m2 m2' Hm2 i; rewrite !lookup_minus (Hm1 i) (Hm2 i).
  * by intros m i.
  * intros n m Hm i; apply cmra_valid_S, Hm.
  * intros m; split; [by intros Hm n i; apply cmra_valid_validN|].
    intros Hm i; apply cmra_valid_validN; intros n; apply Hm.
  * by intros m1 m2 m3 i; rewrite !lookup_op (associative _).
  * by intros m1 m2 i; rewrite !lookup_op (commutative _).
  * by intros m i; rewrite lookup_op !lookup_unit ra_unit_l.
  * by intros m i; rewrite !lookup_unit ra_unit_idempotent.
  * intros n x y; rewrite !map_includedN_spec; intros Hm i.
    by rewrite !lookup_unit; apply cmra_unit_preserving.
  * intros n m1 m2 Hm i; apply cmra_valid_op_l with (m2 !! i).
    by rewrite -lookup_op.
  * intros x y n; rewrite map_includedN_spec; intros ? i.
    by rewrite lookup_op lookup_minus cmra_op_minus.
Qed.
Global Instance map_ra_empty `{RA A} : RAIdentity (gmap K A).
Proof.
  split.
  * by intros ?; rewrite lookup_empty.
  * by intros m i; rewrite /= lookup_op lookup_empty; destruct (m !! i).
Qed.
Global Instance map_cmra_extend `{CMRA A, !CMRAExtend A} : CMRAExtend (gmap K A).
Proof.
  intros n m m1 m2 Hm Hm12.
  assert (∀ i, m !! i ={n}= m1 !! i ⋅ m2 !! i) as Hm12'
    by (by intros i; rewrite -lookup_op).
  set (f i := cmra_extend_op n (m !! i) (m1 !! i) (m2 !! i) (Hm i) (Hm12' i)).
  set (f_proj i := proj1_sig (f i)).
  exists (map_imap (λ i _, (f_proj i).1) m, map_imap (λ i _, (f_proj i).2) m);
    repeat split; intros i; rewrite /= ?lookup_op !lookup_imap.
  * destruct (m !! i) as [x|] eqn:Hx; simpl; [|constructor].
    rewrite -Hx; apply (proj2_sig (f i)).
  * destruct (m !! i) as [x|] eqn:Hx; simpl; [apply (proj2_sig (f i))|].
    pose proof (Hm12' i) as Hm12''; rewrite Hx in Hm12''.
    by destruct (m1 !! i), (m2 !! i); inversion_clear Hm12''.
  * destruct (m !! i) as [x|] eqn:Hx; simpl; [apply (proj2_sig (f i))|].
    pose proof (Hm12' i) as Hm12''; rewrite Hx in Hm12''.
    by destruct (m1 !! i), (m2 !! i); inversion_clear Hm12''.
Qed.
Global Instance map_empty_valid_timeless `{Valid A, ValidN A} :
  ValidTimeless (∅ : gmap K A).
Proof. by intros ??; rewrite lookup_empty. Qed.
Global Instance map_ra_insert_valid_timeless `{Valid A, ValidN A}
    (m : gmap K A) i x:
  ValidTimeless x → ValidTimeless m → m !! i = None →
  ValidTimeless (<[i:=x]>m).
Proof.
  intros ?? Hi Hm j; destruct (decide (i = j)); simplify_map_equality.
  { specialize (Hm j); simplify_map_equality. by apply (valid_timeless _). }
  generalize j; clear dependent j; rapply (valid_timeless m).
  intros j; destruct (decide (i = j)); simplify_map_equality;[by rewrite Hi|].
  by specialize (Hm j); simplify_map_equality.
Qed.
Global Instance map_ra_singleton_valid_timeless `{Valid A, ValidN A} (i : K) x :
  ValidTimeless x → ValidTimeless ({[ i ↦ x ]} : gmap K A).
Proof.
  intros ?; apply (map_ra_insert_valid_timeless _ _ _ _ _).
  by rewrite lookup_empty.
Qed.
Lemma map_insert_valid `{ValidN A} (m : gmap K A) n i x :
  ✓{n} x → ✓{n} m → ✓{n} (<[i:=x]>m).
Proof. by intros ?? j; destruct (decide (i = j)); simplify_map_equality. Qed.
Lemma map_insert_op `{Op A} (m1 m2 : gmap K A) i x :
  m2 !! i = None →  <[i:=x]>(m1 ⋅ m2) = <[i:=x]>m1 ⋅ m2.
Proof. by intros Hi; apply (insert_merge_l _); rewrite Hi. Qed.
Lemma map_singleton_op `{Op A} (i : K) (x y : A) :
  ({[ i ↦ x ⋅ y ]} : gmap K A) = {[ i ↦ x ]} ⋅ {[ i ↦ y ]}.
Proof. by apply symmetry, merge_singleton. Qed.

Canonical Structure mapRA (A : cmraT) : cmraT := CMRAT (gmap K A).
Global Instance map_fmap_cmra_monotone `{CMRA A, CMRA B} (f : A → B)
  `{!CMRAMonotone f} : CMRAMonotone (fmap f : gmap K A → gmap K B).
Proof.
  split.
  * intros m1 m2 n; rewrite !map_includedN_spec; intros Hm i.
    by rewrite !lookup_fmap; apply includedN_preserving.
  * by intros n m ? i; rewrite lookup_fmap; apply validN_preserving.
Qed.
Definition mapRA_map {A B : cmraT} (f : A -n> B) : mapRA A -n> mapRA B :=
  CofeMor (fmap f : mapRA A → mapRA B).
Global Instance mapRA_map_ne {A B} n :
  Proper (dist n ==> dist n) (@mapRA_map A B) := mapC_map_ne n.
Global Instance mapRA_map_monotone {A B : cmraT} (f : A -n> B)
  `{!CMRAMonotone f} : CMRAMonotone (mapRA_map f) := _.

Context `{Fresh K (gset K), !FreshSpec K (gset K)}.

Lemma map_dom_op `{Op A} (m1 m2 : gmap K A) :
  dom (gset K) (m1 ⋅ m2) ≡ dom _ m1 ∪ dom _ m2.
Proof.
  apply elem_of_equiv; intros i; rewrite elem_of_union !elem_of_dom.
  unfold is_Some; setoid_rewrite lookup_op.
  destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma map_update_alloc `{CMRA A} (m : gmap K A) x :
  ✓ x → m ⇝: λ m', ∃ i, m' = <[i:=x]>m ∧ m !! i = None.
Proof.
  intros ? mf n Hm. set (i := fresh (dom (gset K) (m ⋅ mf))).
  assert (i ∉ dom (gset K) m ∧ i ∉ dom (gset K) mf) as [??].
  { rewrite -not_elem_of_union -map_dom_op; apply is_fresh. }
  exists (<[i:=x]>m); split; [exists i; split; [done|]|].
  * by apply not_elem_of_dom.
  * rewrite -map_insert_op; last by apply not_elem_of_dom.
    by apply map_insert_valid; [apply cmra_valid_validN|].
Qed.
End map.
Arguments mapC _ {_ _} _.
Arguments mapRA _ {_ _} _.
