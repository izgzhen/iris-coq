Require Export algebra.base.

(** Unbundeled version *)
Class Dist A := dist : nat → relation A.
Instance: Params (@dist) 3.
Notation "x ={ n }= y" := (dist n x y)
  (at level 70, n at next level, format "x  ={ n }=  y").
Hint Extern 0 (?x ={_}= ?y) => reflexivity.
Hint Extern 0 (_ ={_}= _) => symmetry; assumption.

Tactic Notation "cofe_subst" ident(x) :=
  repeat match goal with
  | _ => progress simplify_equality'
  | H:@dist ?A ?d ?n x _ |- _ => setoid_subst_aux (@dist A d n) x
  | H:@dist ?A ?d ?n _ x |- _ => symmetry in H;setoid_subst_aux (@dist A d n) x
  end.
Tactic Notation "cofe_subst" :=
  repeat match goal with
  | _ => progress simplify_equality'
  | H:@dist ?A ?d ?n ?x _ |- _ => setoid_subst_aux (@dist A d n) x
  | H:@dist ?A ?d ?n _ ?x |- _ => symmetry in H;setoid_subst_aux (@dist A d n) x
  end.

Record chain (A : Type) `{Dist A} := {
  chain_car :> nat → A;
  chain_cauchy n i : n ≤ i → chain_car n ={n}= chain_car i
}.
Arguments chain_car {_ _} _ _.
Arguments chain_cauchy {_ _} _ _ _ _.
Class Compl A `{Dist A} := compl : chain A → A.

Record CofeMixin A `{Equiv A, Compl A} := {
  mixin_equiv_dist x y : x ≡ y ↔ ∀ n, x ={n}= y;
  mixin_dist_equivalence n : Equivalence (dist n);
  mixin_dist_S n x y : x ={S n}= y → x ={n}= y;
  mixin_dist_0 x y : x ={0}= y;
  mixin_conv_compl (c : chain A) n : compl c ={n}= c n
}.
Class Contractive `{Dist A, Dist B} (f : A -> B) :=
  contractive n : Proper (dist n ==> dist (S n)) f.

(** Bundeled version *)
Structure cofeT := CofeT {
  cofe_car :> Type;
  cofe_equiv : Equiv cofe_car;
  cofe_dist : Dist cofe_car;
  cofe_compl : Compl cofe_car;
  cofe_mixin : CofeMixin cofe_car
}.
Arguments CofeT {_ _ _ _} _.
Add Printing Constructor cofeT.
Existing Instances cofe_equiv cofe_dist cofe_compl.
Arguments cofe_car : simpl never.
Arguments cofe_equiv : simpl never.
Arguments cofe_dist : simpl never.
Arguments cofe_compl : simpl never.
Arguments cofe_mixin : simpl never.

(** Lifting properties from the mixin *)
Section cofe_mixin.
  Context {A : cofeT}.
  Implicit Types x y : A.
  Lemma equiv_dist x y : x ≡ y ↔ ∀ n, x ={n}= y.
  Proof. apply (mixin_equiv_dist _ (cofe_mixin A)). Qed.
  Global Instance dist_equivalence n : Equivalence (@dist A _ n).
  Proof. apply (mixin_dist_equivalence _ (cofe_mixin A)). Qed.
  Lemma dist_S n x y : x ={S n}= y → x ={n}= y.
  Proof. apply (mixin_dist_S _ (cofe_mixin A)). Qed.
  Lemma dist_0 x y : x ={0}= y.
  Proof. apply (mixin_dist_0 _ (cofe_mixin A)). Qed.
  Lemma conv_compl (c : chain A) n : compl c ={n}= c n.
  Proof. apply (mixin_conv_compl _ (cofe_mixin A)). Qed.
End cofe_mixin.

Hint Extern 0 (_ ={0}= _) => apply dist_0.

(** General properties *)
Section cofe.
  Context {A : cofeT}.
  Implicit Types x y : A.
  Global Instance cofe_equivalence : Equivalence ((≡) : relation A).
  Proof.
    split.
    * by intros x; rewrite equiv_dist.
    * by intros x y; rewrite !equiv_dist.
    * by intros x y z; rewrite !equiv_dist; intros; transitivity y.
  Qed.
  Global Instance dist_ne n : Proper (dist n ==> dist n ==> iff) (@dist A _ n).
  Proof.
    intros x1 x2 ? y1 y2 ?; split; intros.
    * by transitivity x1; [|transitivity y1].
    * by transitivity x2; [|transitivity y2].
  Qed.
  Global Instance dist_proper n : Proper ((≡) ==> (≡) ==> iff) (@dist A _ n).
  Proof.
    by move => x1 x2 /equiv_dist Hx y1 y2 /equiv_dist Hy; rewrite (Hx n) (Hy n).
  Qed.
  Global Instance dist_proper_2 n x : Proper ((≡) ==> iff) (dist n x).
  Proof. by apply dist_proper. Qed.
  Lemma dist_le (x y : A) n n' : x ={n}= y → n' ≤ n → x ={n'}= y.
  Proof. induction 2; eauto using dist_S. Qed.
  Instance ne_proper {B : cofeT} (f : A → B)
    `{!∀ n, Proper (dist n ==> dist n) f} : Proper ((≡) ==> (≡)) f | 100.
  Proof. by intros x1 x2; rewrite !equiv_dist; intros Hx n; rewrite (Hx n). Qed.
  Instance ne_proper_2 {B C : cofeT} (f : A → B → C)
    `{!∀ n, Proper (dist n ==> dist n ==> dist n) f} :
    Proper ((≡) ==> (≡) ==> (≡)) f | 100.
  Proof.
     unfold Proper, respectful; setoid_rewrite equiv_dist.
     by intros x1 x2 Hx y1 y2 Hy n; rewrite (Hx n) (Hy n).
  Qed.
  Lemma compl_ne (c1 c2: chain A) n : c1 n ={n}= c2 n → compl c1 ={n}= compl c2.
  Proof. intros. by rewrite (conv_compl c1 n) (conv_compl c2 n). Qed.
  Lemma compl_ext (c1 c2 : chain A) : (∀ i, c1 i ≡ c2 i) → compl c1 ≡ compl c2.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using compl_ne. Qed.
  Global Instance contractive_ne {B : cofeT} (f : A → B) `{!Contractive f} n :
    Proper (dist n ==> dist n) f | 100.
  Proof. by intros x1 x2 ?; apply dist_S, contractive. Qed.
  Global Instance contractive_proper {B : cofeT} (f : A → B) `{!Contractive f} :
    Proper ((≡) ==> (≡)) f | 100 := _.
End cofe.

(** Mapping a chain *)
Program Definition chain_map `{Dist A, Dist B} (f : A → B)
    `{!∀ n, Proper (dist n ==> dist n) f} (c : chain A) : chain B :=
  {| chain_car n := f (c n) |}.
Next Obligation. by intros ? A ? B f Hf c n i ?; apply Hf, chain_cauchy. Qed.

(** Timeless elements *)
Class Timeless {A : cofeT} (x : A) := timeless y : x ={1}= y → x ≡ y.
Arguments timeless {_} _ {_} _ _.
Lemma timeless_S {A : cofeT} (x y : A) n : Timeless x → x ≡ y ↔ x ={S n}= y.
Proof.
  split; intros; [by apply equiv_dist|].
  apply (timeless _), dist_le with (S n); auto with lia.
Qed.

(** Fixpoint *)
Program Definition fixpoint_chain {A : cofeT} `{Inhabited A} (f : A → A)
  `{!Contractive f} : chain A := {| chain_car i := Nat.iter i f inhabitant |}.
Next Obligation.
  intros A ? f ? n; induction n as [|n IH]; intros i ?; first done.
  destruct i as [|i]; simpl; first lia; apply contractive, IH; auto with lia.
Qed.
Program Definition fixpoint {A : cofeT} `{Inhabited A} (f : A → A)
  `{!Contractive f} : A := compl (fixpoint_chain f).

Section fixpoint.
  Context {A : cofeT} `{Inhabited A} (f : A → A) `{!Contractive f}.
  Lemma fixpoint_unfold : fixpoint f ≡ f (fixpoint f).
  Proof.
    apply equiv_dist; intros n; unfold fixpoint.
    rewrite (conv_compl (fixpoint_chain f) n).
    by rewrite {1}(chain_cauchy (fixpoint_chain f) n (S n)); last lia.
  Qed.
  Lemma fixpoint_ne (g : A → A) `{!Contractive g} n :
    (∀ z, f z ={n}= g z) → fixpoint f ={n}= fixpoint g.
  Proof.
    intros Hfg; unfold fixpoint.
    rewrite (conv_compl (fixpoint_chain f) n) (conv_compl (fixpoint_chain g) n).
    induction n as [|n IH]; simpl in *; first done.
    rewrite Hfg; apply contractive, IH; auto using dist_S.
  Qed.
  Lemma fixpoint_proper (g : A → A) `{!Contractive g} :
    (∀ x, f x ≡ g x) → fixpoint f ≡ fixpoint g.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_ne. Qed.
End fixpoint.
Global Opaque fixpoint.

(** Function space *)
Record cofeMor (A B : cofeT) : Type := CofeMor {
  cofe_mor_car :> A → B;
  cofe_mor_ne n : Proper (dist n ==> dist n) cofe_mor_car
}.
Arguments CofeMor {_ _} _ {_}.
Add Printing Constructor cofeMor.
Existing Instance cofe_mor_ne.

Section cofe_mor.
  Context {A B : cofeT}.
  Global Instance cofe_mor_proper (f : cofeMor A B) : Proper ((≡) ==> (≡)) f.
  Proof. apply ne_proper, cofe_mor_ne. Qed.
  Instance cofe_mor_equiv : Equiv (cofeMor A B) := λ f g, ∀ x, f x ≡ g x.
  Instance cofe_mor_dist : Dist (cofeMor A B) := λ n f g, ∀ x, f x ={n}= g x.
  Program Definition fun_chain `(c : chain (cofeMor A B)) (x : A) : chain B :=
    {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Program Instance cofe_mor_compl : Compl (cofeMor A B) := λ c,
    {| cofe_mor_car x := compl (fun_chain c x) |}.
  Next Obligation.
    intros c n x y Hx.
    rewrite (conv_compl (fun_chain c x) n) (conv_compl (fun_chain c y) n) /= Hx.
    apply (chain_cauchy c); lia.
  Qed.
  Definition cofe_mor_cofe_mixin : CofeMixin (cofeMor A B).
  Proof.
    split.
    * intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist; intros n; apply Hfg.
    * intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; transitivity (g x).
    * by intros n f g ? x; apply dist_S.
    * by intros f g x.
    * intros c n x; simpl.
      rewrite (conv_compl (fun_chain c x) n); apply (chain_cauchy c); lia.
  Qed.
  Canonical Structure cofe_mor : cofeT := CofeT cofe_mor_cofe_mixin.

  Global Instance cofe_mor_car_ne n :
    Proper (dist n ==> dist n ==> dist n) (@cofe_mor_car A B).
  Proof. intros f g Hfg x y Hx; rewrite Hx; apply Hfg. Qed.
  Global Instance cofe_mor_car_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@cofe_mor_car A B) := ne_proper_2 _.
  Lemma cofe_mor_ext (f g : cofeMor A B) : f ≡ g ↔ ∀ x, f x ≡ g x.
  Proof. done. Qed.
End cofe_mor.

Arguments cofe_mor : clear implicits.
Infix "-n>" := cofe_mor (at level 45, right associativity).
Instance cofe_more_inhabited {A B : cofeT} `{Inhabited B} :
  Inhabited (A -n> B) := populate (CofeMor (λ _, inhabitant)).

(** Identity and composition *)
Definition cid {A} : A -n> A := CofeMor id.
Instance: Params (@cid) 1.
Definition ccompose {A B C}
  (f : B -n> C) (g : A -n> B) : A -n> C := CofeMor (f ∘ g).
Instance: Params (@ccompose) 3.
Infix "◎" := ccompose (at level 40, left associativity).
Lemma ccompose_ne {A B C} (f1 f2 : B -n> C) (g1 g2 : A -n> B) n :
  f1 ={n}= f2 → g1 ={n}= g2 → f1 ◎ g1 ={n}= f2 ◎ g2.
Proof. by intros Hf Hg x; rewrite /= (Hg x) (Hf (g2 x)). Qed.

(** unit *)
Section unit.
  Instance unit_dist : Dist unit := λ _ _ _, True.
  Instance unit_compl : Compl unit := λ _, ().
  Definition unit_cofe_mixin : CofeMixin unit.
  Proof. by repeat split; try exists 0. Qed.
  Canonical Structure unitC : cofeT := CofeT unit_cofe_mixin.
  Global Instance unit_timeless (x : ()) : Timeless x.
  Proof. done. Qed.
End unit.

(** Product *)
Section product.
  Context {A B : cofeT}.

  Instance prod_dist : Dist (A * B) := λ n, prod_relation (dist n) (dist n).
  Global Instance pair_ne :
    Proper (dist n ==> dist n ==> dist n) (@pair A B) := _.
  Global Instance fst_ne : Proper (dist n ==> dist n) (@fst A B) := _.
  Global Instance snd_ne : Proper (dist n ==> dist n) (@snd A B) := _.
  Instance prod_compl : Compl (A * B) := λ c,
    (compl (chain_map fst c), compl (chain_map snd c)).
  Definition prod_cofe_mixin : CofeMixin (A * B).
  Proof.
    split.
    * intros x y; unfold dist, prod_dist, equiv, prod_equiv, prod_relation.
      rewrite !equiv_dist; naive_solver.
    * apply _.
    * by intros n [x1 y1] [x2 y2] [??]; split; apply dist_S.
    * by split.
    * intros c n; split. apply (conv_compl (chain_map fst c) n).
      apply (conv_compl (chain_map snd c) n).
  Qed.
  Canonical Structure prodC : cofeT := CofeT prod_cofe_mixin.
  Global Instance pair_timeless (x : A) (y : B) :
    Timeless x → Timeless y → Timeless (x,y).
  Proof. by intros ?? [x' y'] [??]; split; apply (timeless _). Qed.
End product.

Arguments prodC : clear implicits.
Typeclasses Opaque prod_dist.

Instance prod_map_ne {A A' B B' : cofeT} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@prod_map A A' B B').
Proof. by intros f f' Hf g g' Hg ?? [??]; split; [apply Hf|apply Hg]. Qed.
Definition prodC_map {A A' B B'} (f : A -n> A') (g : B -n> B') :
  prodC A B -n> prodC A' B' := CofeMor (prod_map f g).
Instance prodC_map_ne {A A' B B'} n :
  Proper (dist n ==> dist n ==> dist n) (@prodC_map A A' B B').
Proof. intros f f' Hf g g' Hg [??]; split; [apply Hf|apply Hg]. Qed.

(** Discrete cofe *)
Section discrete_cofe.
  Context `{Equiv A, @Equivalence A (≡)}.
  Instance discrete_dist : Dist A := λ n x y,
    match n with 0 => True | S n => x ≡ y end.
  Instance discrete_compl : Compl A := λ c, c 1.
  Definition discrete_cofe_mixin : CofeMixin A.
  Proof.
    split.
    * intros x y; split; [by intros ? []|intros Hn; apply (Hn 1)].
    * intros [|n]; [done|apply _].
    * by intros [|n].
    * done.
    * intros c [|n]; [done|apply (chain_cauchy c 1 (S n)); lia].
  Qed.
  Definition discreteC : cofeT := CofeT discrete_cofe_mixin.
  Global Instance discrete_timeless (x : A) : Timeless (x : discreteC).
  Proof. by intros y. Qed.
End discrete_cofe.
Arguments discreteC _ {_ _}.

Definition leibnizC (A : Type) : cofeT := @discreteC A equivL _.
Instance leibnizC_leibniz : LeibnizEquiv (leibnizC A).
Proof. by intros A x y. Qed.

Canonical Structure natC := leibnizC nat.
Canonical Structure boolC := leibnizC bool.

(** Later *)
Inductive later (A : Type) : Type := Later { later_car : A }.
Add Printing Constructor later.
Arguments Later {_} _.
Arguments later_car {_} _.
Lemma later_eta {A} (x : later A) : Later (later_car x) = x.
Proof. by destruct x. Qed.

Section later.
  Context {A : cofeT}.
  Instance later_equiv : Equiv (later A) := λ x y, later_car x ≡ later_car y.
  Instance later_dist : Dist (later A) := λ n x y,
    match n with 0 => True | S n => later_car x ={n}= later_car y end.
  Program Definition later_chain (c : chain (later A)) : chain A :=
    {| chain_car n := later_car (c (S n)) |}.
  Next Obligation. intros c n i ?; apply (chain_cauchy c (S n)); lia. Qed.
  Instance later_compl : Compl (later A) := λ c, Later (compl (later_chain c)).
  Definition later_cofe_mixin : CofeMixin (later A).
  Proof.
    split.
    * intros x y; unfold equiv, later_equiv; rewrite !equiv_dist.
      split. intros Hxy [|n]; [done|apply Hxy]. intros Hxy n; apply (Hxy (S n)).
    * intros [|n]; [by split|split]; unfold dist, later_dist.
      + by intros [x].
      + by intros [x] [y].
      + by intros [x] [y] [z] ??; transitivity y.
    * intros [|n] [x] [y] ?; [done|]; unfold dist, later_dist; by apply dist_S.
    * done.
    * intros c [|n]; [done|by apply (conv_compl (later_chain c) n)].
  Qed.
  Canonical Structure laterC : cofeT := CofeT later_cofe_mixin.
  Global Instance Later_contractive : Contractive (@Later A).
  Proof. by intros n ??. Qed.
  Global Instance Later_inj n : Injective (dist n) (dist (S n)) (@Later A).
  Proof. by intros x y. Qed.
End later.

Arguments laterC : clear implicits.

Definition later_map {A B} (f : A → B) (x : later A) : later B :=
  Later (f (later_car x)).
Instance later_map_ne {A B : cofeT} (f : A → B) n :
  Proper (dist (pred n) ==> dist (pred n)) f →
  Proper (dist n ==> dist n) (later_map f) | 0.
Proof. destruct n as [|n]; intros Hf [x] [y] ?; do 2 red; simpl; auto. Qed.
Lemma later_map_id {A} (x : later A) : later_map id x = x.
Proof. by destruct x. Qed.
Lemma later_map_compose {A B C} (f : A → B) (g : B → C) (x : later A) :
  later_map (g ∘ f) x = later_map g (later_map f x).
Proof. by destruct x. Qed.
Definition laterC_map {A B} (f : A -n> B) : laterC A -n> laterC B :=
  CofeMor (later_map f).
Instance laterC_map_contractive (A B : cofeT) : Contractive (@laterC_map A B).
Proof. intros n f g Hf n'; apply Hf. Qed.

(** Indexed product *)
(** Need to put this in a definition to make canonical structures to work. *)
Definition iprod {A} (B : A → cofeT) := ∀ x, B x.
Definition iprod_insert `{∀ x x' : A, Decision (x = x')} {B : A → cofeT}
    (x : A) (y : B x) (f : iprod B) : iprod B := λ x',
  match decide (x = x') with left H => eq_rect _ B y _ H | right _ => f x' end.
Definition iprod_singleton
    `{∀ x x' : A, Decision (x = x')} {B : A → cofeT} `{∀ x : A, Empty (B x)}
  (x : A) (y : B x) : iprod B := iprod_insert x y (λ _, ∅).

Section iprod_cofe.
  Context {A} {B : A → cofeT}.
  Implicit Types x : A.
  Implicit Types f g : iprod B.
  Instance iprod_equiv : Equiv (iprod B) := λ f g, ∀ x, f x ≡ g x.
  Instance iprod_dist : Dist (iprod B) := λ n f g, ∀ x, f x ={n}= g x.
  Program Definition iprod_chain (c : chain (iprod B)) (x : A) : chain (B x) :=
    {| chain_car n := c n x |}.
  Next Obligation. by intros c x n i ?; apply (chain_cauchy c). Qed.
  Program Instance iprod_compl : Compl (iprod B) := λ c x,
    compl (iprod_chain c x).
  Definition iprod_cofe_mixin : CofeMixin (iprod B).
  Proof.
    split.
    * intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist; intros n; apply Hfg.
    * intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; transitivity (g x).
    * intros n f g Hfg x; apply dist_S, Hfg.
    * by intros f g x.
    * intros c n x.
      rewrite /compl /iprod_compl (conv_compl (iprod_chain c x) n).
      apply (chain_cauchy c); lia.
  Qed.
  Canonical Structure iprodC : cofeT := CofeT iprod_cofe_mixin.

  Context `{∀ x x' : A, Decision (x = x')}.
  Global Instance iprod_insert_ne x n :
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

  Context `{∀ x : A, Empty (B x)}.
  Global Instance iprod_singleton_ne x n :
    Proper (dist n ==> dist n) (iprod_singleton x).
  Proof. by intros y1 y2 Hy; rewrite /iprod_singleton Hy. Qed.
  Global Instance iprod_singleton_proper x :
    Proper ((≡) ==> (≡)) (iprod_singleton x) := ne_proper _.
  Lemma iprod_lookup_singleton x y : (iprod_singleton x y) x = y.
  Proof. by rewrite /iprod_singleton iprod_lookup_insert. Qed.
  Lemma iprod_lookup_singleton_ne x x' y :
    x ≠ x' → (iprod_singleton x y) x' = ∅.
  Proof. intros; by rewrite /iprod_singleton iprod_lookup_insert_ne. Qed.
End iprod_cofe.

Arguments iprodC {_} _.

Definition iprod_map {A} {B1 B2 : A → cofeT} (f : ∀ x, B1 x → B2 x)
  (g : iprod B1) : iprod B2 := λ x, f _ (g x).
Instance iprod_map_ne {A} {B1 B2 : A → cofeT} (f : ∀ x, B1 x → B2 x) n :
  (∀ x, Proper (dist n ==> dist n) (f x)) →
  Proper (dist n ==> dist n) (iprod_map f).
Proof. by intros ? y1 y2 Hy x; rewrite /iprod_map (Hy x). Qed.
Definition iprodC_map {A} {B1 B2 : A → cofeT} (f : iprod (λ x, B1 x -n> B2 x)) :
  iprodC B1 -n> iprodC B2 := CofeMor (iprod_map f).
Instance laterC_map_ne {A} {B1 B2 : A → cofeT} n :
  Proper (dist n ==> dist n) (@iprodC_map A B1 B2).
Proof. intros f1 f2 Hf g x; apply Hf. Qed.
