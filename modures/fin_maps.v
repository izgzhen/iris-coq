Require Export modures.cmra prelude.gmap modures.option.

Section cofe.
Context `{Countable K} {A : cofeT}.

(* COFE *)
Instance map_dist : Dist (gmap K A) := λ n m1 m2,
  ∀ i, m1 !! i ={n}= m2 !! i.
Program Definition map_chain (c : chain (gmap K A))
  (k : K) : chain (option A) := {| chain_car n := c n !! k |}.
Next Obligation. by intros c k n i ?; apply (chain_cauchy c). Qed.
Instance map_compl : Compl (gmap K A) := λ c,
  map_imap (λ i _, compl (map_chain c i)) (c 1).
Definition map_cofe_mixin : CofeMixin (gmap K A).
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
Canonical Structure mapC : cofeT := CofeT map_cofe_mixin.

Global Instance lookup_ne n k :
  Proper (dist n ==> dist n) (lookup k : gmap K A → option A).
Proof. by intros m1 m2. Qed.
Global Instance insert_ne (i : K) n :
  Proper (dist n ==> dist n ==> dist n) (insert (M:=gmap K A) i).
Proof.
  intros x y ? m m' ? j; destruct (decide (i = j)); simplify_map_equality;
    [by constructor|by apply lookup_ne].
Qed.
Global Instance singleton_ne (i : K) n :
  Proper (dist n ==> dist n) (singletonM i : A → gmap K A).
Proof. by intros ???; apply insert_ne. Qed.
Global Instance delete_ne (i : K) n :
  Proper (dist n ==> dist n) (delete (M:=gmap K A) i).
Proof.
  intros m m' ? j; destruct (decide (i = j)); simplify_map_equality;
    [by constructor|by apply lookup_ne].
Qed.
Global Instance map_empty_timeless : Timeless (∅ : gmap K A).
Proof.
  intros m Hm i; specialize (Hm i); rewrite lookup_empty in Hm |- *.
  inversion_clear Hm; constructor.
Qed.
Global Instance map_lookup_timeless (m : gmap K A) i :
  Timeless m → Timeless (m !! i).
Proof.
  intros ? [x|] Hx; [|by symmetry; apply (timeless _)].
  assert (m ={1}= <[i:=x]> m)
    by (by symmetry in Hx; inversion Hx; cofe_subst; rewrite insert_id).
  by rewrite (timeless m (<[i:=x]>m)) // lookup_insert.
Qed.
Global Instance map_ra_insert_timeless (m : gmap K A) i x :
  Timeless x → Timeless m → Timeless (<[i:=x]>m).
Proof.
  intros ?? m' Hm j; destruct (decide (i = j)); simplify_map_equality.
  { by apply (timeless _); rewrite -Hm lookup_insert. }
  by apply (timeless _); rewrite -Hm lookup_insert_ne.
Qed.
Global Instance map_ra_singleton_timeless (i : K) (x : A) :
  Timeless x → Timeless ({[ i ↦ x ]} : gmap K A) := _.
End cofe.
Arguments mapC _ {_ _} _.

(* CMRA *)
Section cmra.
Context `{Countable K} {A : cmraT}.

Instance map_op : Op (gmap K A) := merge op.
Instance map_unit : Unit (gmap K A) := fmap unit.
Instance map_valid : Valid (gmap K A) := λ m, ∀ i, ✓ (m !! i).
Instance map_validN : ValidN (gmap K A) := λ n m, ∀ i, ✓{n} (m!!i).
Instance map_minus : Minus (gmap K A) := merge minus.
Lemma lookup_op m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
Proof. by apply lookup_merge. Qed.
Lemma lookup_minus m1 m2 i : (m1 ⩪ m2) !! i = m1 !! i ⩪ m2 !! i.
Proof. by apply lookup_merge. Qed.
Lemma lookup_unit m i : unit m !! i = unit (m !! i).
Proof. by apply lookup_fmap. Qed.
Lemma map_included_spec (m1 m2 : gmap K A) : m1 ≼ m2 ↔ ∀ i, m1 !! i ≼ m2 !! i.
Proof.
  split.
  * by intros [m Hm]; intros i; exists (m !! i); rewrite -lookup_op Hm.
  * intros Hm; exists (m2 ⩪ m1); intros i.
    by rewrite lookup_op lookup_minus ra_op_minus.
Qed.
Lemma map_includedN_spec (m1 m2 : gmap K A) n :
  m1 ≼{n} m2 ↔ ∀ i, m1 !! i ≼{n} m2 !! i.
Proof.
  split.
  * by intros [m Hm]; intros i; exists (m !! i); rewrite -lookup_op Hm.
  * intros Hm; exists (m2 ⩪ m1); intros i.
    by rewrite lookup_op lookup_minus cmra_op_minus.
Qed.
Definition map_cmra_mixin : CMRAMixin (gmap K A).
Proof.
  split.
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
Global Instance map_ra_empty : RAIdentity (gmap K A).
Proof.
  split.
  * by intros ?; rewrite lookup_empty.
  * by intros m i; rewrite /= lookup_op lookup_empty (left_id_L None _).
Qed.
Definition map_cmra_extend_mixin : CMRAExtendMixin (gmap K A).
Proof.
  intros n m m1 m2 Hm Hm12.
  assert (∀ i, m !! i ={n}= m1 !! i ⋅ m2 !! i) as Hm12'
    by (by intros i; rewrite -lookup_op).
  set (f i := cmra_extend_op n (m !! i) (m1 !! i) (m2 !! i) (Hm i) (Hm12' i)).
  set (f_proj i := proj1_sig (f i)).
  exists (map_imap (λ i _, (f_proj i).1) m, map_imap (λ i _, (f_proj i).2) m);
    repeat split; intros i; rewrite /= ?lookup_op !lookup_imap.
  * destruct (m !! i) as [x|] eqn:Hx; rewrite !Hx /=; [|constructor].
    rewrite -Hx; apply (proj2_sig (f i)).
  * destruct (m !! i) as [x|] eqn:Hx; rewrite /=; [apply (proj2_sig (f i))|].
    pose proof (Hm12' i) as Hm12''; rewrite Hx in Hm12''.
    by symmetry; apply option_op_positive_dist_l with (m2 !! i).
  * destruct (m !! i) as [x|] eqn:Hx; simpl; [apply (proj2_sig (f i))|].
    pose proof (Hm12' i) as Hm12''; rewrite Hx in Hm12''.
    by symmetry; apply option_op_positive_dist_r with (m1 !! i).
Qed.
Canonical Structure mapRA : cmraT :=
  CMRAT map_cofe_mixin map_cmra_mixin map_cmra_extend_mixin.

Global Instance map_empty_valid_timeless : ValidTimeless (∅ : gmap K A).
Proof. by intros ??; rewrite lookup_empty. Qed.
Global Instance map_ra_insert_valid_timeless (m : gmap K A) i x:
  ValidTimeless x → ValidTimeless m → m !! i = None →
  ValidTimeless (<[i:=x]>m).
Proof.
  intros ?? Hi Hm j; destruct (decide (i = j)); simplify_map_equality.
  { specialize (Hm j); simplify_map_equality. by apply (valid_timeless _). }
  generalize j; clear dependent j; rapply (valid_timeless m).
  intros j; destruct (decide (i = j)); simplify_map_equality;[by rewrite Hi|].
  by specialize (Hm j); simplify_map_equality.
Qed.
Global Instance map_ra_singleton_valid_timeless (i : K) x :
  ValidTimeless x → ValidTimeless {[ i ↦ x ]}.
Proof.
  intros ?; apply (map_ra_insert_valid_timeless _ _ _ _ _).
  by rewrite lookup_empty.
Qed.
End cmra.
Arguments mapRA _ {_ _} _.

Section properties.
Context `{Countable K} {A: cmraT}.

Lemma map_insert_valid (m :gmap K A) n i x : ✓{n} x → ✓{n} m → ✓{n} (<[i:=x]>m).
Proof. by intros ?? j; destruct (decide (i = j)); simplify_map_equality. Qed.
Lemma map_insert_op (m1 m2 : gmap K A) i x :
  m2 !! i = None →  <[i:=x]>(m1 ⋅ m2) = <[i:=x]>m1 ⋅ m2.
Proof. by intros Hi; apply (insert_merge_l _ m1 m2); rewrite Hi. Qed.
Lemma map_unit_singleton (i : K) (x : A) :
  unit ({[ i ↦ x ]} : gmap K A) = {[ i ↦ unit x ]}.
Proof. apply map_fmap_singleton. Qed.
Lemma map_op_singleton (i : K) (x y : A) :
  {[ i ↦ x ]} ⋅ {[ i ↦ y ]} = ({[ i ↦ x ⋅ y ]} : gmap K A).
Proof. by apply (merge_singleton _ _ _ x y). Qed.

Context `{Fresh K (gset K), !FreshSpec K (gset K)}.

Lemma map_dom_op (m1 m2 : gmap K A) :
  dom (gset K) (m1 ⋅ m2) ≡ dom _ m1 ∪ dom _ m2.
Proof.
  apply elem_of_equiv; intros i; rewrite elem_of_union !elem_of_dom.
  unfold is_Some; setoid_rewrite lookup_op.
  destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma map_update_alloc (m : gmap K A) x :
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
End properties.

Instance map_fmap_ne `{Countable K} {A B : cofeT} (f : A → B) n :
  Proper (dist n ==> dist n) f → Proper (dist n ==>dist n) (fmap (M:=gmap K) f).
Proof. by intros ? m m' Hm k; rewrite !lookup_fmap; apply option_fmap_ne. Qed.
Definition mapC_map `{Countable K} {A B} (f: A -n> B) : mapC K A -n> mapC K B :=
  CofeMor (fmap f : mapC K A → mapC K B).
Instance mapC_map_ne `{Countable K} {A B} n :
  Proper (dist n ==> dist n) (@mapC_map K _ _ A B).
Proof.
  intros f g Hf m k; rewrite /= !lookup_fmap.
  destruct (_ !! k) eqn:?; simpl; constructor; apply Hf.
Qed.

Instance map_fmap_cmra_monotone `{Countable K} {A B : cmraT} (f : A → B)
  `{!CMRAMonotone f} : CMRAMonotone (fmap f : gmap K A → gmap K B).
Proof.
  split.
  * intros m1 m2 n; rewrite !map_includedN_spec; intros Hm i.
    by rewrite !lookup_fmap; apply: includedN_preserving.
  * by intros n m ? i; rewrite lookup_fmap; apply validN_preserving.
Qed.
Definition mapRA_map `{Countable K} {A B : cmraT} (f : A -n> B) :
  mapRA K A -n> mapRA K B := CofeMor (fmap f : mapRA K A → mapRA K B).
Instance mapRA_map_ne `{Countable K} {A B} n :
  Proper (dist n ==> dist n) (@mapRA_map K _ _ A B) := mapC_map_ne n.
Instance mapRA_map_monotone `{Countable K} {A B : cmraT} (f : A -n> B)
  `{!CMRAMonotone f} : CMRAMonotone (mapRA_map f) := _.
