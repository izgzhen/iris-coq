From algebra Require Export cmra option.
From prelude Require Export gmap.
From algebra Require Import upred.

Section cofe.
Context `{Countable K} {A : cofeT}.
Implicit Types m : gmap K A.

Instance map_dist : Dist (gmap K A) := λ n m1 m2,
  ∀ i, m1 !! i ≡{n}≡ m2 !! i.
Program Definition map_chain (c : chain (gmap K A))
  (k : K) : chain (option A) := {| chain_car n := c n !! k |}.
Next Obligation. by intros c k n i ?; apply (chain_cauchy c). Qed.
Instance map_compl : Compl (gmap K A) := λ c,
  map_imap (λ i _, compl (map_chain c i)) (c 0).
Definition map_cofe_mixin : CofeMixin (gmap K A).
Proof.
  split.
  - intros m1 m2; split.
    + by intros Hm n k; apply equiv_dist.
    + intros Hm k; apply equiv_dist; intros n; apply Hm.
  - intros n; split.
    + by intros m k.
    + by intros m1 m2 ? k.
    + by intros m1 m2 m3 ?? k; trans (m2 !! k).
  - by intros n m1 m2 ? k; apply dist_S.
  - intros n c k; rewrite /compl /map_compl lookup_imap.
    feed inversion (λ H, chain_cauchy c 0 n H k); simpl; auto with lia.
    by rewrite conv_compl /=; apply reflexive_eq.
Qed.
Canonical Structure mapC : cofeT := CofeT map_cofe_mixin.
Global Instance map_discrete : Discrete A → Discrete mapC.
Proof. intros ? m m' ? i. by apply (timeless _). Qed.
(* why doesn't this go automatic? *)
Global Instance mapC_leibniz: LeibnizEquiv A → LeibnizEquiv mapC.
Proof. intros; change (LeibnizEquiv (gmap K A)); apply _. Qed.

Global Instance lookup_ne n k :
  Proper (dist n ==> dist n) (lookup k : gmap K A → option A).
Proof. by intros m1 m2. Qed.
Global Instance lookup_proper k :
  Proper ((≡) ==> (≡)) (lookup k : gmap K A → option A) := _.
Global Instance alter_ne f k n :
  Proper (dist n ==> dist n) f → Proper (dist n ==> dist n) (alter f k).
Proof.
  intros ? m m' Hm k'.
  by destruct (decide (k = k')); simplify_map_eq; rewrite (Hm k').
Qed.
Global Instance insert_ne i n :
  Proper (dist n ==> dist n ==> dist n) (insert (M:=gmap K A) i).
Proof.
  intros x y ? m m' ? j; destruct (decide (i = j)); simplify_map_eq;
    [by constructor|by apply lookup_ne].
Qed.
Global Instance singleton_ne i n :
  Proper (dist n ==> dist n) (singletonM i : A → gmap K A).
Proof. by intros ???; apply insert_ne. Qed.
Global Instance delete_ne i n :
  Proper (dist n ==> dist n) (delete (M:=gmap K A) i).
Proof.
  intros m m' ? j; destruct (decide (i = j)); simplify_map_eq;
    [by constructor|by apply lookup_ne].
Qed.

Instance map_empty_timeless : Timeless (∅ : gmap K A).
Proof.
  intros m Hm i; specialize (Hm i); rewrite lookup_empty in Hm |- *.
  inversion_clear Hm; constructor.
Qed.
Global Instance map_lookup_timeless m i : Timeless m → Timeless (m !! i).
Proof.
  intros ? [x|] Hx; [|by symmetry; apply: timeless].
  assert (m ≡{0}≡ <[i:=x]> m)
    by (by symmetry in Hx; inversion Hx; cofe_subst; rewrite insert_id).
  by rewrite (timeless m (<[i:=x]>m)) // lookup_insert.
Qed.
Global Instance map_insert_timeless m i x :
  Timeless x → Timeless m → Timeless (<[i:=x]>m).
Proof.
  intros ?? m' Hm j; destruct (decide (i = j)); simplify_map_eq.
  { by apply: timeless; rewrite -Hm lookup_insert. }
  by apply: timeless; rewrite -Hm lookup_insert_ne.
Qed.
Global Instance map_singleton_timeless i x :
  Timeless x → Timeless ({[ i := x ]} : gmap K A) := _.
End cofe.

Arguments mapC _ {_ _} _.

(* CMRA *)
Section cmra.
Context `{Countable K} {A : cmraT}.
Implicit Types m : gmap K A.

Instance map_op : Op (gmap K A) := merge op.
Instance map_core : Core (gmap K A) := fmap core.
Instance map_valid : Valid (gmap K A) := λ m, ∀ i, ✓ (m !! i).
Instance map_validN : ValidN (gmap K A) := λ n m, ∀ i, ✓{n} (m !! i).
Instance map_div : Div (gmap K A) := merge div.

Lemma lookup_op m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
Proof. by apply lookup_merge. Qed.
Lemma lookup_div m1 m2 i : (m1 ÷ m2) !! i = m1 !! i ÷ m2 !! i.
Proof. by apply lookup_merge. Qed.
Lemma lookup_core m i : core m !! i = core (m !! i).
Proof. by apply lookup_fmap. Qed.

Lemma map_included_spec (m1 m2 : gmap K A) : m1 ≼ m2 ↔ ∀ i, m1 !! i ≼ m2 !! i.
Proof.
  split.
  - by intros [m Hm]; intros i; exists (m !! i); rewrite -lookup_op Hm.
  - intros Hm; exists (m2 ÷ m1); intros i.
    by rewrite lookup_op lookup_div cmra_op_div.
Qed.
Lemma map_includedN_spec (m1 m2 : gmap K A) n :
  m1 ≼{n} m2 ↔ ∀ i, m1 !! i ≼{n} m2 !! i.
Proof.
  split.
  - by intros [m Hm]; intros i; exists (m !! i); rewrite -lookup_op Hm.
  - intros Hm; exists (m2 ÷ m1); intros i.
    by rewrite lookup_op lookup_div cmra_op_div'.
Qed.

Definition map_cmra_mixin : CMRAMixin (gmap K A).
Proof.
  split.
  - by intros n m1 m2 m3 Hm i; rewrite !lookup_op (Hm i).
  - by intros n m1 m2 Hm i; rewrite !lookup_core (Hm i).
  - by intros n m1 m2 Hm ? i; rewrite -(Hm i).
  - by intros n m1 m1' Hm1 m2 m2' Hm2 i; rewrite !lookup_div (Hm1 i) (Hm2 i).
  - intros m; split.
    + by intros ? n i; apply cmra_valid_validN.
    + intros Hm i; apply cmra_valid_validN=> n; apply Hm.
  - intros n m Hm i; apply cmra_validN_S, Hm.
  - by intros m1 m2 m3 i; rewrite !lookup_op assoc.
  - by intros m1 m2 i; rewrite !lookup_op comm.
  - by intros m i; rewrite lookup_op !lookup_core cmra_core_l.
  - by intros m i; rewrite !lookup_core cmra_core_idemp.
  - intros x y; rewrite !map_included_spec; intros Hm i.
    by rewrite !lookup_core; apply cmra_core_preserving.
  - intros n m1 m2 Hm i; apply cmra_validN_op_l with (m2 !! i).
    by rewrite -lookup_op.
  - intros x y; rewrite map_included_spec=> ? i.
    by rewrite lookup_op lookup_div cmra_op_div.
  - intros n m m1 m2 Hm Hm12.
    assert (∀ i, m !! i ≡{n}≡ m1 !! i ⋅ m2 !! i) as Hm12'
      by (by intros i; rewrite -lookup_op).
    set (f i := cmra_extend n (m !! i) (m1 !! i) (m2 !! i) (Hm i) (Hm12' i)).
    set (f_proj i := proj1_sig (f i)).
    exists (map_imap (λ i _, (f_proj i).1) m, map_imap (λ i _, (f_proj i).2) m);
      repeat split; intros i; rewrite /= ?lookup_op !lookup_imap.
    + destruct (m !! i) as [x|] eqn:Hx; rewrite !Hx /=; [|constructor].
      rewrite -Hx; apply (proj2_sig (f i)).
    + destruct (m !! i) as [x|] eqn:Hx; rewrite /=; [apply (proj2_sig (f i))|].
      pose proof (Hm12' i) as Hm12''; rewrite Hx in Hm12''.
      by symmetry; apply option_op_positive_dist_l with (m2 !! i).
    + destruct (m !! i) as [x|] eqn:Hx; simpl; [apply (proj2_sig (f i))|].
      pose proof (Hm12' i) as Hm12''; rewrite Hx in Hm12''.
      by symmetry; apply option_op_positive_dist_r with (m1 !! i).
Qed.
Canonical Structure mapR : cmraT := CMRAT map_cofe_mixin map_cmra_mixin.
Global Instance map_cmra_unit : CMRAUnit mapR.
Proof.
  split.
  - by intros i; rewrite lookup_empty.
  - by intros m i; rewrite /= lookup_op lookup_empty (left_id_L None _).
  - apply map_empty_timeless.
Qed.
Global Instance map_cmra_discrete : CMRADiscrete A → CMRADiscrete mapR.
Proof. split; [apply _|]. intros m ? i. by apply: cmra_discrete_valid. Qed.

(** Internalized properties *)
Lemma map_equivI {M} m1 m2 : (m1 ≡ m2)%I ≡ (∀ i, m1 !! i ≡ m2 !! i : uPred M)%I.
Proof. by uPred.unseal. Qed.
Lemma map_validI {M} m : (✓ m)%I ≡ (∀ i, ✓ (m !! i) : uPred M)%I.
Proof. by uPred.unseal. Qed.
End cmra.

Arguments mapR _ {_ _} _.

Section properties.
Context `{Countable K} {A : cmraT}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types a : A.

Lemma map_lookup_validN n m i x : ✓{n} m → m !! i ≡{n}≡ Some x → ✓{n} x.
Proof. by move=> /(_ i) Hm Hi; move:Hm; rewrite Hi. Qed.
Lemma map_lookup_valid m i x : ✓ m → m !! i ≡ Some x → ✓ x.
Proof. move=> Hm Hi. move:(Hm i). by rewrite Hi. Qed.
Lemma map_insert_validN n m i x : ✓{n} x → ✓{n} m → ✓{n} <[i:=x]>m.
Proof. by intros ?? j; destruct (decide (i = j)); simplify_map_eq. Qed.
Lemma map_insert_valid m i x : ✓ x → ✓ m → ✓ <[i:=x]>m.
Proof. by intros ?? j; destruct (decide (i = j)); simplify_map_eq. Qed.
Lemma map_singleton_validN n i x : ✓{n} ({[ i := x ]} : gmap K A) ↔ ✓{n} x.
Proof.
  split; [|by intros; apply map_insert_validN, cmra_unit_validN].
  by move=>/(_ i); simplify_map_eq.
Qed.
Lemma map_singleton_valid i x : ✓ ({[ i := x ]} : gmap K A) ↔ ✓ x.
Proof. rewrite !cmra_valid_validN. by setoid_rewrite map_singleton_validN. Qed.

Lemma map_insert_singleton_opN n m i x :
  m !! i = None ∨ m !! i ≡{n}≡ Some (core x) → <[i:=x]> m ≡{n}≡ {[ i := x ]} ⋅ m.
Proof.
  intros Hi j; destruct (decide (i = j)) as [->|];
    [|by rewrite lookup_op lookup_insert_ne // lookup_singleton_ne // left_id].
  rewrite lookup_op lookup_insert lookup_singleton.
  by destruct Hi as [->| ->]; constructor; rewrite ?cmra_core_r.
Qed.
Lemma map_insert_singleton_op m i x :
  m !! i = None ∨ m !! i ≡ Some (core x) → <[i:=x]> m ≡ {[ i := x ]} ⋅ m.
Proof.
  rewrite !equiv_dist; naive_solver eauto using map_insert_singleton_opN.
Qed.

Lemma map_core_singleton (i : K) (x : A) :
  core ({[ i := x ]} : gmap K A) = {[ i := core x ]}.
Proof. apply map_fmap_singleton. Qed.
Lemma map_op_singleton (i : K) (x y : A) :
  {[ i := x ]} ⋅ {[ i := y ]} = ({[ i := x ⋅ y ]} : gmap K A).
Proof. by apply (merge_singleton _ _ _ x y). Qed.

Lemma singleton_includedN n m i x :
  {[ i := x ]} ≼{n} m ↔ ∃ y, m !! i ≡{n}≡ Some y ∧ x ≼ y.
  (* not m !! i = Some y ∧ x ≼{n} y to deal with n = 0 *)
Proof.
  split.
  - move=> [m' /(_ i)]; rewrite lookup_op lookup_singleton=> Hm.
    destruct (m' !! i) as [y|];
      [exists (x ⋅ y)|exists x]; eauto using cmra_included_l.
  - intros (y&Hi&?); rewrite map_includedN_spec=>j.
    destruct (decide (i = j)); simplify_map_eq.
    + rewrite Hi. by apply (includedN_preserving _), cmra_included_includedN.
    + apply: cmra_unit_leastN.
Qed.
Lemma map_dom_op m1 m2 : dom (gset K) (m1 ⋅ m2) ≡ dom _ m1 ∪ dom _ m2.
Proof.
  apply elem_of_equiv; intros i; rewrite elem_of_union !elem_of_dom.
  unfold is_Some; setoid_rewrite lookup_op.
  destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.

Lemma map_insert_updateP (P : A → Prop) (Q : gmap K A → Prop) m i x :
  x ~~>: P → (∀ y, P y → Q (<[i:=y]>m)) → <[i:=x]>m ~~>: Q.
Proof.
  intros Hx%option_updateP' HP n mf Hm.
  destruct (Hx n (mf !! i)) as ([y|]&?&?); try done.
  { by generalize (Hm i); rewrite lookup_op; simplify_map_eq. }
  exists (<[i:=y]> m); split; first by auto.
  intros j; move: (Hm j)=>{Hm}; rewrite !lookup_op=>Hm.
  destruct (decide (i = j)); simplify_map_eq/=; auto.
Qed.
Lemma map_insert_updateP' (P : A → Prop) m i x :
  x ~~>: P → <[i:=x]>m ~~>: λ m', ∃ y, m' = <[i:=y]>m ∧ P y.
Proof. eauto using map_insert_updateP. Qed.
Lemma map_insert_update m i x y : x ~~> y → <[i:=x]>m ~~> <[i:=y]>m.
Proof.
  rewrite !cmra_update_updateP; eauto using map_insert_updateP with subst.
Qed.

Lemma map_singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) i x :
  x ~~>: P → (∀ y, P y → Q {[ i := y ]}) → {[ i := x ]} ~~>: Q.
Proof. apply map_insert_updateP. Qed.
Lemma map_singleton_updateP' (P : A → Prop) i x :
  x ~~>: P → {[ i := x ]} ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
Proof. apply map_insert_updateP'. Qed.
Lemma map_singleton_update i (x y : A) : x ~~> y → {[ i := x ]} ~~> {[ i := y ]}.
Proof. apply map_insert_update. Qed.

Lemma map_singleton_updateP_empty `{Empty A, !CMRAUnit A}
    (P : A → Prop) (Q : gmap K A → Prop) i :
  ∅ ~~>: P → (∀ y, P y → Q {[ i := y ]}) → ∅ ~~>: Q.
Proof.
  intros Hx HQ n gf Hg.
  destruct (Hx n (from_option ∅ (gf !! i))) as (y&?&Hy).
  { move:(Hg i). rewrite !left_id.
    case _: (gf !! i); simpl; auto using cmra_unit_validN. }
  exists {[ i := y ]}; split; first by auto.
  intros i'; destruct (decide (i' = i)) as [->|].
  - rewrite lookup_op lookup_singleton.
    move:Hy; case _: (gf !! i); first done.
    by rewrite right_id.
  - move:(Hg i'). by rewrite !lookup_op lookup_singleton_ne // !left_id.
Qed.
Lemma map_singleton_updateP_empty' `{Empty A, !CMRAUnit A} (P: A → Prop) i :
  ∅ ~~>: P → ∅ ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
Proof. eauto using map_singleton_updateP_empty. Qed.

Section freshness.
Context `{Fresh K (gset K), !FreshSpec K (gset K)}.
Lemma map_updateP_alloc_strong (Q : gmap K A → Prop) (I : gset K) m x :
  ✓ x → (∀ i, m !! i = None → i ∉ I → Q (<[i:=x]>m)) → m ~~>: Q.
Proof.
  intros ? HQ n mf Hm. set (i := fresh (I ∪ dom (gset K) (m ⋅ mf))).
  assert (i ∉ I ∧ i ∉ dom (gset K) m ∧ i ∉ dom (gset K) mf) as [?[??]].
  { rewrite -not_elem_of_union -map_dom_op -not_elem_of_union; apply is_fresh. }
  exists (<[i:=x]>m); split.
  { by apply HQ; last done; apply not_elem_of_dom. }
  rewrite map_insert_singleton_opN; last by left; apply not_elem_of_dom.
  rewrite -assoc -map_insert_singleton_opN;
    last by left; apply not_elem_of_dom; rewrite map_dom_op not_elem_of_union.
  by apply map_insert_validN; [apply cmra_valid_validN|].
Qed.
Lemma map_updateP_alloc (Q : gmap K A → Prop) m x :
  ✓ x → (∀ i, m !! i = None → Q (<[i:=x]>m)) → m ~~>: Q.
Proof. move=>??. eapply map_updateP_alloc_strong with (I:=∅); by eauto. Qed.
Lemma map_updateP_alloc_strong' m x (I : gset K) :
  ✓ x → m ~~>: λ m', ∃ i, i ∉ I ∧ m' = <[i:=x]>m ∧ m !! i = None.
Proof. eauto using map_updateP_alloc_strong. Qed.
Lemma map_updateP_alloc' m x :
  ✓ x → m ~~>: λ m', ∃ i, m' = <[i:=x]>m ∧ m !! i = None.
Proof. eauto using map_updateP_alloc. Qed.
End freshness.

(* Allocation is a local update: Just use composition with a singleton map. *)
(* Deallocation is *not* a local update. The trouble is that if we
   own {[ i ↦ x ]}, then the frame could always own "core x", and prevent
   deallocation. *)

(* Applying a local update at a position we own is a local update. *)
Global Instance map_alter_update `{!LocalUpdate Lv L} i :
  LocalUpdate (λ m, ∃ x, m !! i = Some x ∧ Lv x) (alter L i).
Proof.
  split; first apply _.
  intros n m1 m2 (x&Hix&?) Hm j; destruct (decide (i = j)) as [->|].
  - rewrite lookup_alter !lookup_op lookup_alter Hix /=.
    move: (Hm j); rewrite lookup_op Hix.
    case: (m2 !! j)=>[y|] //=; constructor. by apply (local_updateN L).
  - by rewrite lookup_op !lookup_alter_ne // lookup_op.
Qed.
End properties.

(** Functor *)
Instance map_fmap_ne `{Countable K} {A B : cofeT} (f : A → B) n :
  Proper (dist n ==> dist n) f → Proper (dist n ==>dist n) (fmap (M:=gmap K) f).
Proof. by intros ? m m' Hm k; rewrite !lookup_fmap; apply option_fmap_ne. Qed.
Instance map_fmap_cmra_monotone `{Countable K} {A B : cmraT} (f : A → B)
  `{!CMRAMonotone f} : CMRAMonotone (fmap f : gmap K A → gmap K B).
Proof.
  split; try apply _.
  - by intros n m ? i; rewrite lookup_fmap; apply (validN_preserving _).
  - intros m1 m2; rewrite !map_included_spec=> Hm i.
    by rewrite !lookup_fmap; apply: included_preserving.
Qed.
Definition mapC_map `{Countable K} {A B} (f: A -n> B) : mapC K A -n> mapC K B :=
  CofeMor (fmap f : mapC K A → mapC K B).
Instance mapC_map_ne `{Countable K} {A B} n :
  Proper (dist n ==> dist n) (@mapC_map K _ _ A B).
Proof.
  intros f g Hf m k; rewrite /= !lookup_fmap.
  destruct (_ !! k) eqn:?; simpl; constructor; apply Hf.
Qed.

Program Definition mapCF K `{Countable K} (F : cFunctor) : cFunctor := {|
  cFunctor_car A B := mapC K (cFunctor_car F A B);
  cFunctor_map A1 A2 B1 B2 fg := mapC_map (cFunctor_map F fg)
|}.
Next Obligation.
  by intros K ?? F A1 A2 B1 B2 n f g Hfg; apply mapC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros K ?? F A B x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_setoid_ext=>y ??; apply cFunctor_id.
Qed.
Next Obligation.
  intros K ?? F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_setoid_ext=>y ??; apply cFunctor_compose.
Qed.
Instance mapCF_contractive K `{Countable K} F :
  cFunctorContractive F → cFunctorContractive (mapCF K F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply mapC_map_ne, cFunctor_contractive.
Qed.

Program Definition mapRF K `{Countable K} (F : rFunctor) : rFunctor := {|
  rFunctor_car A B := mapR K (rFunctor_car F A B);
  rFunctor_map A1 A2 B1 B2 fg := mapC_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros K ?? F A1 A2 B1 B2 n f g Hfg; apply mapC_map_ne, rFunctor_ne.
Qed.
Next Obligation.
  intros K ?? F A B x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_setoid_ext=>y ??; apply rFunctor_id.
Qed.
Next Obligation.
  intros K ?? F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_setoid_ext=>y ??; apply rFunctor_compose.
Qed.
Instance mapRF_contractive K `{Countable K} F :
  rFunctorContractive F → rFunctorContractive (mapRF K F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply mapC_map_ne, rFunctor_contractive.
Qed.
