From algebra Require Export cmra.
From algebra Require Import functor upred.

(** * Indexed product *)
(** Need to put this in a definition to make canonical structures to work. *)
Definition iprod {A} (B : A → cofeT) := ∀ x, B x.
Definition iprod_insert {A} {B : A → cofeT} `{∀ x x' : A, Decision (x = x')}
    (x : A) (y : B x) (f : iprod B) : iprod B := λ x',
  match decide (x = x') with left H => eq_rect _ B y _ H | right _ => f x' end.
Global Instance iprod_empty {A} {B : A → cofeT}
  `{∀ x, Empty (B x)} : Empty (iprod B) := λ x, ∅.
Definition iprod_singleton {A} {B : A → cofeT} 
    `{∀ x x' : A, Decision (x = x'), ∀ x : A, Empty (B x)}
  (x : A) (y : B x) : iprod B := iprod_insert x y ∅.
Instance: Params (@iprod_insert) 4.
Instance: Params (@iprod_singleton) 5.

Section iprod_cofe.
  Context {A} {B : A → cofeT}.
  Implicit Types x : A.
  Implicit Types f g : iprod B.

  Instance iprod_equiv : Equiv (iprod B) := λ f g, ∀ x, f x ≡ g x.
  Instance iprod_dist : Dist (iprod B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Program Definition iprod_chain (c : chain (iprod B)) (x : A) : chain (B x) :=
    {| chain_car n := c n x |}.
  Next Obligation. by intros c x n i ?; apply (chain_cauchy c). Qed.
  Program Instance iprod_compl : Compl (iprod B) := λ c x,
    compl (iprod_chain c x).
  Definition iprod_cofe_mixin : CofeMixin (iprod B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist; intros n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - intros n f g Hfg x; apply dist_S, Hfg.
    - intros n c x.
      rewrite /compl /iprod_compl (conv_compl n (iprod_chain c x)).
      apply (chain_cauchy c); lia.
  Qed.
  Canonical Structure iprodC : cofeT := CofeT iprod_cofe_mixin.

  (** Properties of empty *)
  Section empty.
    Context `{∀ x, Empty (B x)}.
    Definition iprod_lookup_empty  x : ∅ x = ∅ := eq_refl.
    Global Instance iprod_empty_timeless :
      (∀ x : A, Timeless (∅ : B x)) → Timeless (∅ : iprod B).
    Proof. intros ? f Hf x. by apply: timeless. Qed.
  End empty.

  (** Properties of iprod_insert. *)
  Context `{∀ x x' : A, Decision (x = x')}.

  Global Instance iprod_insert_ne n x :
    Proper (dist n ==> dist n ==> dist n) (iprod_insert x).
  Proof.
    intros y1 y2 ? f1 f2 ? x'; rewrite /iprod_insert.
    by destruct (decide _) as [[]|].
  Qed.
  Global Instance iprod_insert_proper x :
    Proper ((≡) ==> (≡) ==> (≡)) (iprod_insert x) := ne_proper_2 _.

  Lemma iprod_lookup_insert f x y : (iprod_insert x y f) x = y.
  Proof.
    rewrite /iprod_insert; destruct (decide _) as [Hx|]; last done.
    by rewrite (proof_irrel Hx eq_refl).
  Qed.
  Lemma iprod_lookup_insert_ne f x x' y :
    x ≠ x' → (iprod_insert x y f) x' = f x'.
  Proof. by rewrite /iprod_insert; destruct (decide _). Qed.

  Global Instance iprod_lookup_timeless f x : Timeless f → Timeless (f x).
  Proof.
    intros ? y ?.
    cut (f ≡ iprod_insert x y f).
    { by move=> /(_ x)->; rewrite iprod_lookup_insert. }
    by apply: timeless=>x'; destruct (decide (x = x')) as [->|];
      rewrite ?iprod_lookup_insert ?iprod_lookup_insert_ne.
  Qed.
  Global Instance iprod_insert_timeless f x y :
    Timeless f → Timeless y → Timeless (iprod_insert x y f).
  Proof.
    intros ?? g Heq x'; destruct (decide (x = x')) as [->|].
    - rewrite iprod_lookup_insert.
      apply: timeless. by rewrite -(Heq x') iprod_lookup_insert.
    - rewrite iprod_lookup_insert_ne //.
      apply: timeless. by rewrite -(Heq x') iprod_lookup_insert_ne.
  Qed.

  (** Properties of iprod_singletom. *)
  Context `{∀ x : A, Empty (B x)}.

  Global Instance iprod_singleton_ne n x :
    Proper (dist n ==> dist n) (iprod_singleton x).
  Proof. by intros y1 y2 Hy; rewrite /iprod_singleton Hy. Qed.
  Global Instance iprod_singleton_proper x :
    Proper ((≡) ==> (≡)) (iprod_singleton x) := ne_proper _.

  Lemma iprod_lookup_singleton x y : (iprod_singleton x y) x = y.
  Proof. by rewrite /iprod_singleton iprod_lookup_insert. Qed.
  Lemma iprod_lookup_singleton_ne x x' y: x ≠ x' → (iprod_singleton x y) x' = ∅.
  Proof. intros; by rewrite /iprod_singleton iprod_lookup_insert_ne. Qed.

  Global Instance iprod_singleton_timeless x (y : B x) :
    (∀ x : A, Timeless (∅ : B x)) → Timeless y → Timeless (iprod_singleton x y).
  Proof. eauto using iprod_insert_timeless, iprod_empty_timeless. Qed.
End iprod_cofe.

Arguments iprodC {_} _.

Section iprod_cmra.
  Context {A} {B : A → cmraT}.
  Implicit Types f g : iprod B.

  Instance iprod_op : Op (iprod B) := λ f g x, f x ⋅ g x.
  Instance iprod_unit : Unit (iprod B) := λ f x, unit (f x).
  Instance iprod_validN : ValidN (iprod B) := λ n f, ∀ x, ✓{n} f x.
  Instance iprod_minus : Minus (iprod B) := λ f g x, f x ⩪ g x.

  Definition iprod_lookup_op f g x : (f ⋅ g) x = f x ⋅ g x := eq_refl.
  Definition iprod_lookup_unit f x : (unit f) x = unit (f x) := eq_refl.
  Definition iprod_lookup_minus f g x : (f ⩪ g) x = f x ⩪ g x := eq_refl.

  Lemma iprod_includedN_spec (f g : iprod B) n : f ≼{n} g ↔ ∀ x, f x ≼{n} g x.
  Proof.
    split.
    - by intros [h Hh] x; exists (h x); rewrite /op /iprod_op (Hh x).
    - intros Hh; exists (g ⩪ f)=> x; specialize (Hh x).
      by rewrite /op /iprod_op /minus /iprod_minus cmra_op_minus.
  Qed.

  Definition iprod_cmra_mixin : CMRAMixin (iprod B).
  Proof.
    split.
    - by intros n f1 f2 f3 Hf x; rewrite iprod_lookup_op (Hf x).
    - by intros n f1 f2 Hf x; rewrite iprod_lookup_unit (Hf x).
    - by intros n f1 f2 Hf ? x; rewrite -(Hf x).
    - by intros n f f' Hf g g' Hg i; rewrite iprod_lookup_minus (Hf i) (Hg i).
    - intros n f Hf x; apply cmra_validN_S, Hf.
    - by intros f1 f2 f3 x; rewrite iprod_lookup_op assoc.
    - by intros f1 f2 x; rewrite iprod_lookup_op comm.
    - by intros f x; rewrite iprod_lookup_op iprod_lookup_unit cmra_unit_l.
    - by intros f x; rewrite iprod_lookup_unit cmra_unit_idemp.
    - intros n f1 f2; rewrite !iprod_includedN_spec=> Hf x.
      by rewrite iprod_lookup_unit; apply cmra_unit_preservingN, Hf.
    - intros n f1 f2 Hf x; apply cmra_validN_op_l with (f2 x), Hf.
    - intros n f1 f2; rewrite iprod_includedN_spec=> Hf x.
      by rewrite iprod_lookup_op iprod_lookup_minus cmra_op_minus; try apply Hf.
  Qed.
  Definition iprod_cmra_extend_mixin : CMRAExtendMixin (iprod B).
  Proof.
    intros n f f1 f2 Hf Hf12.
    set (g x := cmra_extend_op n (f x) (f1 x) (f2 x) (Hf x) (Hf12 x)).
    exists ((λ x, (proj1_sig (g x)).1), (λ x, (proj1_sig (g x)).2)).
    split_and?; intros x; apply (proj2_sig (g x)).
  Qed.
  Canonical Structure iprodRA : cmraT :=
    CMRAT iprod_cofe_mixin iprod_cmra_mixin iprod_cmra_extend_mixin.
  Global Instance iprod_cmra_identity `{∀ x, Empty (B x)} :
    (∀ x, CMRAIdentity (B x)) → CMRAIdentity iprodRA.
  Proof.
    intros ?; split.
    - intros n x; apply cmra_empty_valid.
    - by intros f x; rewrite iprod_lookup_op left_id.
    - by apply _.
  Qed.

  (** Internalized properties *)
  Lemma iprod_equivI {M} g1 g2 : (g1 ≡ g2)%I ≡ (∀ i, g1 i ≡ g2 i : uPred M)%I.
  Proof. done. Qed.
  Lemma iprod_validI {M} g : (✓ g)%I ≡ (∀ i, ✓ g i : uPred M)%I.
  Proof. done. Qed.

  (** Properties of iprod_insert. *)
  Context `{∀ x x' : A, Decision (x = x')}.

  Lemma iprod_insert_updateP x (P : B x → Prop) (Q : iprod B → Prop) g y1 :
    y1 ~~>: P → (∀ y2, P y2 → Q (iprod_insert x y2 g)) →
    iprod_insert x y1 g ~~>: Q.
  Proof.
    intros Hy1 HP n gf Hg. destruct (Hy1 n (gf x)) as (y2&?&?).
    { move: (Hg x). by rewrite iprod_lookup_op iprod_lookup_insert. }
    exists (iprod_insert x y2 g); split; [auto|].
    intros x'; destruct (decide (x' = x)) as [->|];
      rewrite iprod_lookup_op ?iprod_lookup_insert //; [].
    move: (Hg x'). by rewrite iprod_lookup_op !iprod_lookup_insert_ne.
  Qed.

  Lemma iprod_insert_updateP' x (P : B x → Prop) g y1 :
    y1 ~~>: P →
    iprod_insert x y1 g ~~>: λ g', ∃ y2, g' = iprod_insert x y2 g ∧ P y2.
  Proof. eauto using iprod_insert_updateP. Qed.
  Lemma iprod_insert_update g x y1 y2 :
    y1 ~~> y2 → iprod_insert x y1 g ~~> iprod_insert x y2 g.
  Proof.
    rewrite !cmra_update_updateP; eauto using iprod_insert_updateP with subst.
  Qed.

  (** Properties of iprod_singleton. *)
  Context `{∀ x, Empty (B x), ∀ x, CMRAIdentity (B x)}.

  Lemma iprod_singleton_validN n x (y: B x) : ✓{n} iprod_singleton x y ↔ ✓{n} y.
  Proof.
    split; [by move=>/(_ x); rewrite iprod_lookup_singleton|].
    move=>Hx x'; destruct (decide (x = x')) as [->|];
      rewrite ?iprod_lookup_singleton ?iprod_lookup_singleton_ne //.
    by apply cmra_empty_valid.
  Qed.

  Lemma iprod_unit_singleton x (y : B x) :
    unit (iprod_singleton x y) ≡ iprod_singleton x (unit y).
  Proof.
    by move=>x'; destruct (decide (x = x')) as [->|];
      rewrite iprod_lookup_unit ?iprod_lookup_singleton
      ?iprod_lookup_singleton_ne // cmra_unit_empty.
  Qed.

  Lemma iprod_op_singleton (x : A) (y1 y2 : B x) :
    iprod_singleton x y1 ⋅ iprod_singleton x y2 ≡ iprod_singleton x (y1 ⋅ y2).
  Proof.
    intros x'; destruct (decide (x' = x)) as [->|].
    - by rewrite iprod_lookup_op !iprod_lookup_singleton.
    - by rewrite iprod_lookup_op !iprod_lookup_singleton_ne // left_id.
  Qed.

  Lemma iprod_singleton_updateP x (P : B x → Prop) (Q : iprod B → Prop) y1 :
    y1 ~~>: P → (∀ y2, P y2 → Q (iprod_singleton x y2)) →
    iprod_singleton x y1 ~~>: Q.
  Proof. rewrite /iprod_singleton; eauto using iprod_insert_updateP. Qed.
  Lemma iprod_singleton_updateP' x (P : B x → Prop) y1 :
    y1 ~~>: P →
    iprod_singleton x y1 ~~>: λ g, ∃ y2, g = iprod_singleton x y2 ∧ P y2.
  Proof. eauto using iprod_singleton_updateP. Qed.
  Lemma iprod_singleton_update x y1 y2 :
    y1 ~~> y2 → iprod_singleton x y1 ~~> iprod_singleton x y2.
  Proof. eauto using iprod_insert_update. Qed.

  Lemma iprod_singleton_updateP_empty x (P : B x → Prop) (Q : iprod B → Prop) :
    ∅ ~~>: P → (∀ y2, P y2 → Q (iprod_singleton x y2)) → ∅ ~~>: Q.
  Proof.
    intros Hx HQ n gf Hg. destruct (Hx n (gf x)) as (y2&?&?); first apply Hg.
    exists (iprod_singleton x y2); split; [by apply HQ|].
    intros x'; destruct (decide (x' = x)) as [->|].
    - by rewrite iprod_lookup_op iprod_lookup_singleton.
    - rewrite iprod_lookup_op iprod_lookup_singleton_ne //. apply Hg.
  Qed.
  Lemma iprod_singleton_updateP_empty' x (P : B x → Prop) :
    ∅ ~~>: P → ∅ ~~>: λ g, ∃ y2, g = iprod_singleton x y2 ∧ P y2.
  Proof. eauto using iprod_singleton_updateP_empty. Qed.
End iprod_cmra.

Arguments iprodRA {_} _.

(** * Functor *)
Definition iprod_map {A} {B1 B2 : A → cofeT} (f : ∀ x, B1 x → B2 x)
  (g : iprod B1) : iprod B2 := λ x, f _ (g x).

Lemma iprod_map_ext {A} {B1 B2 : A → cofeT} (f1 f2 : ∀ x, B1 x → B2 x) g :
  (∀ x, f1 x (g x) ≡ f2 x (g x)) → iprod_map f1 g ≡ iprod_map f2 g.
Proof. done. Qed.
Lemma iprod_map_id {A} {B: A → cofeT} (g : iprod B) : iprod_map (λ _, id) g = g.
Proof. done. Qed.
Lemma iprod_map_compose {A} {B1 B2 B3 : A → cofeT}
    (f1 : ∀ x, B1 x → B2 x) (f2 : ∀ x, B2 x → B3 x) (g : iprod B1) :
  iprod_map (λ x, f2 x ∘ f1 x) g = iprod_map f2 (iprod_map f1 g).
Proof. done. Qed.

Instance iprod_map_ne {A} {B1 B2 : A → cofeT} (f : ∀ x, B1 x → B2 x) n :
  (∀ x, Proper (dist n ==> dist n) (f x)) →
  Proper (dist n ==> dist n) (iprod_map f).
Proof. by intros ? y1 y2 Hy x; rewrite /iprod_map (Hy x). Qed.
Instance iprod_map_cmra_monotone {A} {B1 B2: A → cmraT} (f : ∀ x, B1 x → B2 x) :
  (∀ x, CMRAMonotone (f x)) → CMRAMonotone (iprod_map f).
Proof.
  split.
  - intros n g1 g2; rewrite !iprod_includedN_spec=> Hf x.
    rewrite /iprod_map; apply includedN_preserving, Hf.
  - intros n g Hg x; rewrite /iprod_map; apply validN_preserving, Hg.
Qed.

Definition iprodC_map {A} {B1 B2 : A → cofeT} (f : iprod (λ x, B1 x -n> B2 x)) :
  iprodC B1 -n> iprodC B2 := CofeMor (iprod_map f).
Instance iprodC_map_ne {A} {B1 B2 : A → cofeT} n :
  Proper (dist n ==> dist n) (@iprodC_map A B1 B2).
Proof. intros f1 f2 Hf g x; apply Hf. Qed.

Program Definition iprodF {A} (Σ : A → iFunctor) : iFunctor := {|
  ifunctor_car B := iprodRA (λ x, Σ x B);
  ifunctor_map B1 B2 f := iprodC_map (λ x, ifunctor_map (Σ x) f);
|}.
Next Obligation.
  by intros A Σ B1 B2 n f f' ? g; apply iprodC_map_ne=>x; apply ifunctor_map_ne.
Qed.
Next Obligation.
  intros A Σ B g. rewrite /= -{2}(iprod_map_id g).
  apply iprod_map_ext=> x; apply ifunctor_map_id.
Qed.
Next Obligation.
  intros A Σ B1 B2 B3 f1 f2 g. rewrite /= -iprod_map_compose.
  apply iprod_map_ext=> y; apply ifunctor_map_compose.
Qed.
