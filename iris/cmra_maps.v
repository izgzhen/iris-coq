Require Export iris.cmra iris.cofe_maps.
Require Import prelude.pmap prelude.natmap prelude.gmap.

(** option *)
Instance option_valid `{Valid A} : Valid (option A) := λ mx,
  match mx with Some x => ✓ x | None => True end.
Instance option_validN `{ValidN A} : ValidN (option A) := λ n mx,
  match mx with Some x => ✓{n} x | None => True end.
Instance option_unit `{Unit A} : Unit (option A) := fmap unit.
Instance option_op `{Op A} : Op (option A) := union_with (λ x y, Some (x ⋅ y)).
Instance option_minus `{Minus A} : Minus (option A) :=
  difference_with (λ x y, Some (x ⩪ y)).
Lemma option_included `{CMRA A} mx my :
  mx ≼ my ↔ mx = None ∨ ∃ x y, mx = Some x ∧ my = Some y ∧ x ≼ y.
Proof.
  split.
  * intros [mz Hmz]; destruct mx as [x|]; [right|by left].
    destruct my as [y|]; [exists x, y|destruct mz; inversion_clear Hmz].
    destruct mz as [z|]; inversion_clear Hmz; split_ands; auto;
      setoid_subst; eauto using ra_included_l.
  * intros [->|(x&y&->&->&z&Hz)]; try (by exists my; destruct my; constructor).
    by exists (Some z); constructor.
Qed.
Lemma option_includedN `{CMRA A} n mx my :
  mx ≼{n} my ↔ n = 0 ∨ mx = None ∨ ∃ x y, mx = Some x ∧ my = Some y ∧ x ≼{n} y.
Proof.
  split.
  * intros [mz Hmz]; destruct n as [|n]; [by left|right].
    destruct mx as [x|]; [right|by left].
    destruct my as [y|]; [exists x, y|destruct mz; inversion_clear Hmz].
    destruct mz as [z|]; inversion_clear Hmz; split_ands; auto;
      cofe_subst; auto using cmra_included_l.
  * intros [->|[->|(x&y&->&->&z&Hz)]];
      try (by exists my; destruct my; constructor).
    by exists (Some z); constructor.
Qed.
Instance option_cmra `{CMRA A} : CMRA (option A).
Proof.
  split.
  * apply _.
  * by intros n [x|]; destruct 1; constructor;
      repeat apply (_ : Proper (dist _ ==> _ ==> _) _).
  * by destruct 1; constructor; apply (_ : Proper (dist n ==> _) _).
  * destruct 1 as [[?|] [?|]| |]; unfold validN, option_validN; simpl;
     intros ?; auto using cmra_valid_0;
     eapply (_ : Proper (dist _ ==> impl) (✓{_})); eauto.
  * by destruct 1; inversion_clear 1; constructor;
      repeat apply (_ : Proper (dist _ ==> _ ==> _) _).
  * intros [x|]; unfold validN, option_validN; auto using cmra_valid_0.
  * intros n [x|]; unfold validN, option_validN; auto using cmra_valid_S.
  * by intros [x|]; unfold valid, validN, option_validN, option_valid;
      auto using cmra_valid_validN.
  * intros [x|] [y|] [z|]; constructor; rewrite ?(associative _); auto.
  * intros [x|] [y|]; constructor; rewrite 1?(commutative _); auto.
  * by intros [x|]; constructor; rewrite cmra_unit_l.
  * by intros [x|]; constructor; rewrite cmra_unit_idempotent.
  * intros n mx my; rewrite !option_includedN;intros [|[->|(x&y&->&->&?)]];auto.
    do 2 right; exists (unit x), (unit y); eauto using cmra_unit_preserving.
  * intros n [x|] [y|]; unfold validN, option_validN; simpl;
      eauto using cmra_valid_op_l.
  * intros n mx my; rewrite option_includedN.
    intros [->|[->|(x&y&->&->&?)]]; [done|by destruct my|].
    by constructor; apply cmra_op_minus.
Qed.
Instance option_cmra_extend `{CMRA A, !CMRAExtend A} : CMRAExtend (option A).
Proof.
  intros n mx my1 my2; destruct (decide (n = 0)) as [->|].
  { by exists (mx, None); repeat constructor; destruct mx; constructor. }
  destruct mx as [x|], my1 as [y1|], my2 as [y2|]; intros Hx Hx';
    try (by exfalso; inversion Hx'; auto).
  * destruct (cmra_extend_op n x y1 y2) as ([z1 z2]&?&?&?); auto.
    { by inversion_clear Hx'. }
    by exists (Some z1, Some z2); repeat constructor.
  * by exists (Some x,None); inversion Hx'; repeat constructor.
  * by exists (None,Some x); inversion Hx'; repeat constructor.
  * exists (None,None); repeat constructor.
Qed.
Instance None_valid_timeless `{Valid A, ValidN A} : ValidTimeless (@None A).
Proof. done. Qed.
Instance Some_valid_timeless `{Valid A, ValidN A} x :
  ValidTimeless x → ValidTimeless (Some x).
Proof. by intros ? y; apply (valid_timeless x). Qed.
Instance option_fmap_cmra_monotone `{CMRA A, CMRA B} (f : A → B)
  `{!CMRAMonotone f} : CMRAMonotone (fmap f : option A → option B).
Proof.
  split.
  * intros n mx my; rewrite !option_includedN.
    intros [->|[->|(x&y&->&->&?)]]; simpl; eauto 10 using @includedN_preserving.
  * by intros n [x|] ?;
      unfold validN, option_validN; simpl; try apply validN_preserving.
Qed.

(** fin maps *)
Section map.
  Context `{FinMap K M}.
  Existing Instances map_dist map_compl map_cofe.
  Instance map_op `{Op A} : Op (M A) := merge op.
  Instance map_unit `{Unit A} : Unit (M A) := fmap unit.
  Instance map_valid `{Valid A} : Valid (M A) := λ m, ∀ i, ✓ (m !! i).
  Instance map_validN `{ValidN A} : ValidN (M A) := λ n m, ∀ i, ✓{n} (m!!i).
  Instance map_minus `{Minus A} : Minus (M A) := merge minus.
  Lemma lookup_op `{Op A} m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
  Proof. by apply lookup_merge. Qed.
  Lemma lookup_minus `{Minus A} m1 m2 i : (m1 ⩪ m2) !! i = m1 !! i ⩪ m2 !! i.
  Proof. by apply lookup_merge. Qed.
  Lemma lookup_unit `{Unit A} m i : unit m !! i = unit (m !! i).
  Proof. by apply lookup_fmap. Qed.
  Lemma map_included_spec `{CMRA A} (m1 m2 : M A) :
    m1 ≼ m2 ↔ ∀ i, m1 !! i ≼ m2 !! i.
  Proof.
    split.
    * intros [m Hm]; intros i; exists (m !! i). by rewrite <-lookup_op, Hm.
    * intros Hm; exists (m2 ⩪ m1); intros i.
      by rewrite lookup_op, lookup_minus, ra_op_minus.
  Qed.
  Lemma map_includedN_spec `{CMRA A} (m1 m2 : M A) n :
    m1 ≼{n} m2 ↔ ∀ i, m1 !! i ≼{n} m2 !! i.
  Proof.
    split.
    * intros [m Hm]; intros i; exists (m !! i). by rewrite <-lookup_op, Hm.
    * intros Hm; exists (m2 ⩪ m1); intros i.
      by rewrite lookup_op, lookup_minus, cmra_op_minus.
  Qed.
  Instance map_cmra `{CMRA A} : CMRA (M A).
  Proof.
    split.
    * apply _.
    * by intros n m1 m2 m3 Hm i; rewrite !lookup_op, (Hm i).
    * by intros n m1 m2 Hm i; rewrite !lookup_unit, (Hm i).
    * by intros n m1 m2 Hm ? i; rewrite <-(Hm i).
    * intros n m1 m1' Hm1 m2 m2' Hm2 i.
      by rewrite !lookup_minus, (Hm1 i), (Hm2 i).
    * by intros m i.
    * intros n m Hm i; apply cmra_valid_S, Hm.
    * intros m; split; [by intros Hm n i; apply cmra_valid_validN|].
      intros Hm i; apply cmra_valid_validN; intros n; apply Hm.
    * by intros m1 m2 m3 i; rewrite !lookup_op, (associative _).
    * by intros m1 m2 i; rewrite !lookup_op, (commutative _).
    * by intros m i; rewrite lookup_op, !lookup_unit, ra_unit_l.
    * by intros m i; rewrite !lookup_unit, ra_unit_idempotent.
    * intros n x y; rewrite !map_includedN_spec; intros Hm i.
      by rewrite !lookup_unit; apply cmra_unit_preserving.
    * intros n m1 m2 Hm i; apply cmra_valid_op_l with (m2 !! i).
      by rewrite <-lookup_op.
    * intros x y n; rewrite map_includedN_spec; intros ? i.
      by rewrite lookup_op, lookup_minus, cmra_op_minus by done.
  Qed.
  Instance map_ra_empty `{RA A} : RAEmpty (M A).
  Proof.
    split.
    * by intros ?; rewrite lookup_empty.
    * by intros m i; simpl; rewrite lookup_op, lookup_empty; destruct (m !! i).
  Qed.
  Instance map_cmra_extend `{CMRA A, !CMRAExtend A} : CMRAExtend (M A).
  Proof.
    intros n m m1 m2 Hm Hm12.
    assert (∀ i, m !! i ={n}= m1 !! i ⋅ m2 !! i) as Hm12'
      by (by intros i; rewrite <-lookup_op).
    set (f i := cmra_extend_op n (m !! i) (m1 !! i) (m2 !! i) (Hm i) (Hm12' i)).
    set (f_proj i := proj1_sig (f i)).
    exists (map_imap (λ i _, (f_proj i).1) m, map_imap (λ i _, (f_proj i).2) m);
      repeat split; simpl; intros i; rewrite ?lookup_op, !lookup_imap.
    * destruct (m !! i) as [x|] eqn:Hx; simpl; [|constructor].
      rewrite <-Hx; apply (proj2_sig (f i)).
    * destruct (m !! i) as [x|] eqn:Hx; simpl; [apply (proj2_sig (f i))|].
      pose proof (Hm12' i) as Hm12''; rewrite Hx in Hm12''.
      by destruct (m1 !! i), (m2 !! i); inversion_clear Hm12''.
    * destruct (m !! i) as [x|] eqn:Hx; simpl; [apply (proj2_sig (f i))|].
      pose proof (Hm12' i) as Hm12''; rewrite Hx in Hm12''.
      by destruct (m1 !! i), (m2 !! i); inversion_clear Hm12''.
  Qed.
  Global Instance map_empty_valid_timeless `{Valid A, ValidN A} :
    ValidTimeless (∅ : M A).
  Proof. by intros ??; rewrite lookup_empty. Qed.
  Global Instance map_ra_insert_valid_timeless `{Valid A,ValidN A} (m: M A) i x:
    ValidTimeless x → ValidTimeless m → m !! i = None →
    ValidTimeless (<[i:=x]>m).
  Proof.
    intros ?? Hi Hm j; destruct (decide (i = j)); simplify_map_equality.
    { specialize (Hm j); simplify_map_equality. by apply (valid_timeless _). }
    generalize j; clear dependent j; rapply (valid_timeless m).
    intros j; destruct (decide (i = j)); simplify_map_equality;[by rewrite Hi|].
    by specialize (Hm j); simplify_map_equality.
  Qed.
  Global Instance map_ra_singleton_timeless `{Valid A, ValidN A} (i : K) x :
    ValidTimeless x → ValidTimeless ({[ i, x ]} : M A).
  Proof.
    intros ?; apply (map_ra_insert_valid_timeless _ _ _ _ _); simpl.
    by rewrite lookup_empty.
  Qed.
  Definition mapRA (A : cmraT) : cmraT := CMRAT (M A).
  Global Instance map_fmap_cmra_monotone `{CMRA A, CMRA B} (f : A → B)
    `{!CMRAMonotone f} : CMRAMonotone (fmap f : M A → M B).
  Proof.
    split.
    * intros m1 m2 n; rewrite !map_includedN_spec; intros Hm i.
      by rewrite !lookup_fmap; apply includedN_preserving.
    * by intros n m ? i; rewrite lookup_fmap; apply validN_preserving.
  Qed.
  Hint Resolve (map_fmap_ne (M:=M)) : typeclass_instances.
  Definition mapRA_map {A B : cmraT} (f : A -n> B) : mapRA A -n> mapRA B :=
    CofeMor (fmap f : mapRA A → mapRA B).
  Global Instance mapRA_map_ne {A B} n :
    Proper (dist n ==> dist n) (@mapRA_map A B) := mapC_map_ne n.
  Global Instance mapRA_map_monotone {A B : cmraT} (f : A -n> B)
    `{!CMRAMonotone f} : CMRAMonotone (mapRA_map f) := _.
End map.

Arguments mapRA {_} _ {_ _ _ _ _ _ _ _ _} _.

Canonical Structure natmapRA := mapRA natmap.
Definition natmapRA_map {A B : cmraT}
  (f : A -n> B) : natmapRA A -n> natmapRA B := mapRA_map f.
Canonical Structure PmapRA := mapRA Pmap.
Definition PmapRA_map {A B : cmraT}
  (f : A -n> B) : PmapRA A -n> PmapRA B := mapRA_map f.
Canonical Structure gmapRA K `{Countable K} := mapRA (gmap K).
Definition gmapRA_map `{Countable K} {A B : cmraT}
  (f : A -n> B) : gmapRA K A -n> gmapRA K B := mapRA_map f.
