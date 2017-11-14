From iris.algebra Require Export cmra.
From iris.base_logic Require Import base_logic.
From stdpp Require Import finite.
Set Default Proof Using "Type".

(** * Indexed product *)
(** Need to put this in a definition to make canonical structures to work. *)
Definition iprod `{Finite A} (B : A → ofeT) := ∀ x, B x.
Definition iprod_insert `{Finite A} {B : A → ofeT}
    (x : A) (y : B x) (f : iprod B) : iprod B := λ x',
  match decide (x = x') with left H => eq_rect _ B y _ H | right _ => f x' end.
Instance: Params (@iprod_insert) 5.

Section iprod_cofe.
  Context `{Finite A} {B : A → ofeT}.
  Implicit Types x : A.
  Implicit Types f g : iprod B.

  Instance iprod_equiv : Equiv (iprod B) := λ f g, ∀ x, f x ≡ g x.
  Instance iprod_dist : Dist (iprod B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition iprod_ofe_mixin : OfeMixin (iprod B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist; intros n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - intros n f g Hfg x; apply dist_S, Hfg.
  Qed.
  Canonical Structure iprodC : ofeT := OfeT (iprod B) iprod_ofe_mixin.

  Program Definition iprod_chain (c : chain iprodC) (x : A) : chain (B x) :=
    {| chain_car n := c n x |}.
  Next Obligation. by intros c x n i ?; apply (chain_cauchy c). Qed.
  Global Program Instance iprod_cofe `{∀ a, Cofe (B a)} : Cofe iprodC :=
    {| compl c x := compl (iprod_chain c x) |}.
  Next Obligation.
    intros ? n c x.
    rewrite (conv_compl n (iprod_chain c x)).
    apply (chain_cauchy c); lia.
  Qed.

  (** Properties of iprod_insert. *)
  Global Instance iprod_insert_ne x :
    NonExpansive2 (iprod_insert x).
  Proof.
    intros n y1 y2 ? f1 f2 ? x'; rewrite /iprod_insert.
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

  Global Instance iprod_lookup_discrete f x : Discrete f → Discrete (f x).
  Proof.
    intros ? y ?.
    cut (f ≡ iprod_insert x y f).
    { by move=> /(_ x)->; rewrite iprod_lookup_insert. }
    apply (discrete _)=> x'; destruct (decide (x = x')) as [->|];
      by rewrite ?iprod_lookup_insert ?iprod_lookup_insert_ne.
  Qed.
  Global Instance iprod_insert_discrete f x y :
    Discrete f → Discrete y → Discrete (iprod_insert x y f).
  Proof.
    intros ?? g Heq x'; destruct (decide (x = x')) as [->|].
    - rewrite iprod_lookup_insert.
      apply: discrete. by rewrite -(Heq x') iprod_lookup_insert.
    - rewrite iprod_lookup_insert_ne //.
      apply: discrete. by rewrite -(Heq x') iprod_lookup_insert_ne.
  Qed.
End iprod_cofe.

Arguments iprodC {_ _ _} _.

Section iprod_cmra.
  Context `{Finite A} {B : A → ucmraT}.
  Implicit Types f g : iprod B.

  Instance iprod_op : Op (iprod B) := λ f g x, f x ⋅ g x.
  Instance iprod_pcore : PCore (iprod B) := λ f, Some (λ x, core (f x)).
  Instance iprod_valid : Valid (iprod B) := λ f, ∀ x, ✓ f x.
  Instance iprod_validN : ValidN (iprod B) := λ n f, ∀ x, ✓{n} f x.

  Definition iprod_lookup_op f g x : (f ⋅ g) x = f x ⋅ g x := eq_refl.
  Definition iprod_lookup_core f x : (core f) x = core (f x) := eq_refl.

  Lemma iprod_included_spec (f g : iprod B) : f ≼ g ↔ ∀ x, f x ≼ g x.
  Proof.
    split; [by intros [h Hh] x; exists (h x); rewrite /op /iprod_op (Hh x)|].
    intros [h ?]%finite_choice. by exists h.
  Qed.

  Lemma iprod_cmra_mixin : CmraMixin (iprod B).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - by intros n f1 f2 f3 Hf x; rewrite iprod_lookup_op (Hf x).
    - by intros n f1 f2 Hf x; rewrite iprod_lookup_core (Hf x).
    - by intros n f1 f2 Hf ? x; rewrite -(Hf x).
    - intros g; split.
      + intros Hg n i; apply cmra_valid_validN, Hg.
      + intros Hg i; apply cmra_valid_validN=> n; apply Hg.
    - intros n f Hf x; apply cmra_validN_S, Hf.
    - by intros f1 f2 f3 x; rewrite iprod_lookup_op assoc.
    - by intros f1 f2 x; rewrite iprod_lookup_op comm.
    - by intros f x; rewrite iprod_lookup_op iprod_lookup_core cmra_core_l.
    - by intros f x; rewrite iprod_lookup_core cmra_core_idemp.
    - intros f1 f2; rewrite !iprod_included_spec=> Hf x.
      by rewrite iprod_lookup_core; apply cmra_core_mono, Hf.
    - intros n f1 f2 Hf x; apply cmra_validN_op_l with (f2 x), Hf.
    - intros n f f1 f2 Hf Hf12.
      destruct (finite_choice (λ x (yy : B x * B x),
        f x ≡ yy.1 ⋅ yy.2 ∧ yy.1 ≡{n}≡ f1 x ∧ yy.2 ≡{n}≡ f2 x)) as [gg Hgg].
      { intros x. specialize (Hf12 x).
        destruct (cmra_extend n (f x) (f1 x) (f2 x)) as (y1&y2&?&?&?); eauto.
        exists (y1,y2); eauto. }
      exists (λ x, gg x.1), (λ x, gg x.2). split_and!=> -?; naive_solver.
  Qed.
  Canonical Structure iprodR := CmraT (iprod B) iprod_cmra_mixin.

  Instance iprod_unit : Unit (iprod B) := λ x, ε.
  Definition iprod_lookup_empty x : ε x = ε := eq_refl.

  Lemma iprod_ucmra_mixin : UcmraMixin (iprod B).
  Proof.
    split.
    - intros x; apply ucmra_unit_valid.
    - by intros f x; rewrite iprod_lookup_op left_id.
    - constructor=> x. apply core_id_core, _.
  Qed.
  Canonical Structure iprodUR := UcmraT (iprod B) iprod_ucmra_mixin.

  Global Instance iprod_unit_discrete :
    (∀ i, Discrete (ε : B i)) → Discrete (ε : iprod B).
  Proof. intros ? f Hf x. by apply: discrete. Qed.

  (** Internalized properties *)
  Lemma iprod_equivI {M} g1 g2 : g1 ≡ g2 ⊣⊢ (∀ i, g1 i ≡ g2 i : uPred M).
  Proof. by uPred.unseal. Qed.
  Lemma iprod_validI {M} g : ✓ g ⊣⊢ (∀ i, ✓ g i : uPred M).
  Proof. by uPred.unseal. Qed.

  (** Properties of iprod_insert. *)
  Lemma iprod_insert_updateP x (P : B x → Prop) (Q : iprod B → Prop) g y1 :
    y1 ~~>: P → (∀ y2, P y2 → Q (iprod_insert x y2 g)) →
    iprod_insert x y1 g ~~>: Q.
  Proof.
    intros Hy1 HP; apply cmra_total_updateP.
    intros n gf Hg. destruct (Hy1 n (Some (gf x))) as (y2&?&?).
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
End iprod_cmra.

Arguments iprodR {_ _ _} _.
Arguments iprodUR {_ _ _} _.

Definition iprod_singleton `{Finite A} {B : A → ucmraT} 
  (x : A) (y : B x) : iprod B := iprod_insert x y ε.
Instance: Params (@iprod_singleton) 5.

Section iprod_singleton.
  Context `{Finite A} {B : A → ucmraT}.
  Implicit Types x : A.

  Global Instance iprod_singleton_ne x :
    NonExpansive (iprod_singleton x : B x → _).
  Proof. intros n y1 y2 ?; apply iprod_insert_ne. done. by apply equiv_dist. Qed.
  Global Instance iprod_singleton_proper x :
    Proper ((≡) ==> (≡)) (iprod_singleton x) := ne_proper _.

  Lemma iprod_lookup_singleton x (y : B x) : (iprod_singleton x y) x = y.
  Proof. by rewrite /iprod_singleton iprod_lookup_insert. Qed.
  Lemma iprod_lookup_singleton_ne x x' (y : B x) :
    x ≠ x' → (iprod_singleton x y) x' = ε.
  Proof. intros; by rewrite /iprod_singleton iprod_lookup_insert_ne. Qed.

  Global Instance iprod_singleton_discrete x (y : B x) :
    (∀ i, Discrete (ε : B i)) →  Discrete y → Discrete (iprod_singleton x y).
  Proof. apply _. Qed.

  Lemma iprod_singleton_validN n x (y : B x) : ✓{n} iprod_singleton x y ↔ ✓{n} y.
  Proof.
    split; [by move=>/(_ x); rewrite iprod_lookup_singleton|].
    move=>Hx x'; destruct (decide (x = x')) as [->|];
      rewrite ?iprod_lookup_singleton ?iprod_lookup_singleton_ne //.
    by apply ucmra_unit_validN.
  Qed.

  Lemma iprod_core_singleton x (y : B x) :
    core (iprod_singleton x y) ≡ iprod_singleton x (core y).
  Proof.
    move=>x'; destruct (decide (x = x')) as [->|];
      by rewrite iprod_lookup_core ?iprod_lookup_singleton
      ?iprod_lookup_singleton_ne // (core_id_core ∅).
  Qed.

  Global Instance iprod_singleton_core_id x (y : B x) :
    CoreId y → CoreId (iprod_singleton x y).
  Proof. by rewrite !core_id_total iprod_core_singleton=> ->. Qed.

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
  Lemma iprod_singleton_update x (y1 y2 : B x) :
    y1 ~~> y2 → iprod_singleton x y1 ~~> iprod_singleton x y2.
  Proof. eauto using iprod_insert_update. Qed.

  Lemma iprod_singleton_updateP_empty x (P : B x → Prop) (Q : iprod B → Prop) :
    ε ~~>: P → (∀ y2, P y2 → Q (iprod_singleton x y2)) → ε ~~>: Q.
  Proof.
    intros Hx HQ; apply cmra_total_updateP.
    intros n gf Hg. destruct (Hx n (Some (gf x))) as (y2&?&?); first apply Hg.
    exists (iprod_singleton x y2); split; [by apply HQ|].
    intros x'; destruct (decide (x' = x)) as [->|].
    - by rewrite iprod_lookup_op iprod_lookup_singleton.
    - rewrite iprod_lookup_op iprod_lookup_singleton_ne //. apply Hg.
  Qed.
  Lemma iprod_singleton_updateP_empty' x (P : B x → Prop) :
    ε ~~>: P → ε ~~>: λ g, ∃ y2, g = iprod_singleton x y2 ∧ P y2.
  Proof. eauto using iprod_singleton_updateP_empty. Qed.
  Lemma iprod_singleton_update_empty x (y : B x) :
    ε ~~> y → ε ~~> iprod_singleton x y.
  Proof.
    rewrite !cmra_update_updateP;
      eauto using iprod_singleton_updateP_empty with subst.
  Qed.
End iprod_singleton.

(** * Functor *)
Definition iprod_map `{Finite A} {B1 B2 : A → ofeT} (f : ∀ x, B1 x → B2 x)
  (g : iprod B1) : iprod B2 := λ x, f _ (g x).

Lemma iprod_map_ext `{Finite A} {B1 B2 : A → ofeT} (f1 f2 : ∀ x, B1 x → B2 x) (g : iprod B1) :
  (∀ x, f1 x (g x) ≡ f2 x (g x)) → iprod_map f1 g ≡ iprod_map f2 g.
Proof. done. Qed.
Lemma iprod_map_id `{Finite A} {B : A → ofeT} (g : iprod B) :
  iprod_map (λ _, id) g = g.
Proof. done. Qed.
Lemma iprod_map_compose `{Finite A} {B1 B2 B3 : A → ofeT}
    (f1 : ∀ x, B1 x → B2 x) (f2 : ∀ x, B2 x → B3 x) (g : iprod B1) :
  iprod_map (λ x, f2 x ∘ f1 x) g = iprod_map f2 (iprod_map f1 g).
Proof. done. Qed.

Instance iprod_map_ne `{Finite A} {B1 B2 : A → ofeT} (f : ∀ x, B1 x → B2 x) n :
  (∀ x, Proper (dist n ==> dist n) (f x)) →
  Proper (dist n ==> dist n) (iprod_map f).
Proof. by intros ? y1 y2 Hy x; rewrite /iprod_map (Hy x). Qed.
Instance iprod_map_cmra_morphism
    `{Finite A} {B1 B2 : A → ucmraT} (f : ∀ x, B1 x → B2 x) :
  (∀ x, CmraMorphism (f x)) → CmraMorphism (iprod_map f).
Proof.
  split; first apply _.
  - intros n g Hg x; rewrite /iprod_map; apply (cmra_morphism_validN (f _)), Hg.
  - intros. apply Some_proper=>i. apply (cmra_morphism_core (f i)).
  - intros g1 g2 i. by rewrite /iprod_map iprod_lookup_op cmra_morphism_op.
Qed.

Definition iprodC_map `{Finite A} {B1 B2 : A → ofeT}
    (f : iprod (λ x, B1 x -n> B2 x)) :
  iprodC B1 -n> iprodC B2 := CofeMor (iprod_map f).
Instance iprodC_map_ne `{Finite A} {B1 B2 : A → ofeT} :
  NonExpansive (@iprodC_map A _ _ B1 B2).
Proof. intros n f1 f2 Hf g x; apply Hf. Qed.

Program Definition iprodCF `{Finite C} (F : C → cFunctor) : cFunctor := {|
  cFunctor_car A B := iprodC (λ c, cFunctor_car (F c) A B);
  cFunctor_map A1 A2 B1 B2 fg := iprodC_map (λ c, cFunctor_map (F c) fg)
|}.
Next Obligation.
  intros C ?? F A1 A2 B1 B2 n ?? g. by apply iprodC_map_ne=>?; apply cFunctor_ne.
Qed.
Next Obligation.
  intros C ?? F A B g; simpl. rewrite -{2}(iprod_map_id g).
  apply iprod_map_ext=> y; apply cFunctor_id.
Qed.
Next Obligation.
  intros C ?? F A1 A2 A3 B1 B2 B3 f1 f2 f1' f2' g. rewrite /= -iprod_map_compose.
  apply iprod_map_ext=>y; apply cFunctor_compose.
Qed.
Instance iprodCF_contractive `{Finite C} (F : C → cFunctor) :
  (∀ c, cFunctorContractive (F c)) → cFunctorContractive (iprodCF F).
Proof.
  intros ? A1 A2 B1 B2 n ?? g.
  (* FIXME: when using `apply` we get
    Anomaly "Uncaught exception Retyping.RetypeError(4)." Please report at http://coq.inria.fr/bugs/.
  *)
  apply: iprodC_map_ne=>c. by apply cFunctor_contractive.
Qed.

Program Definition iprodURF `{Finite C} (F : C → urFunctor) : urFunctor := {|
  urFunctor_car A B := iprodUR (λ c, urFunctor_car (F c) A B);
  urFunctor_map A1 A2 B1 B2 fg := iprodC_map (λ c, urFunctor_map (F c) fg)
|}.
Next Obligation.
  intros C ?? F A1 A2 B1 B2 n ?? g.
  by apply iprodC_map_ne=>?; apply urFunctor_ne.
Qed.
Next Obligation.
  intros C ?? F A B g; simpl. rewrite -{2}(iprod_map_id g).
  apply iprod_map_ext=> y; apply urFunctor_id.
Qed.
Next Obligation.
  intros C ?? F A1 A2 A3 B1 B2 B3 f1 f2 f1' f2' g. rewrite /=-iprod_map_compose.
  apply iprod_map_ext=>y; apply urFunctor_compose.
Qed.
Instance iprodURF_contractive `{Finite C} (F : C → urFunctor) :
  (∀ c, urFunctorContractive (F c)) → urFunctorContractive (iprodURF F).
Proof.
  intros ? A1 A2 B1 B2 n ?? g.
  by apply iprodC_map_ne=>c; apply urFunctor_contractive.
Qed.
