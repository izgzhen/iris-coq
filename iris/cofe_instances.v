Require Export iris.cofe.
Require Import prelude.fin_maps prelude.pmap prelude.nmap prelude.zmap prelude.stringmap.

(** Discrete cofe *)
Section discrete_cofe.
  Context `{Equiv A, @Equivalence A (≡)}.
  Instance discrete_dist : Dist A := λ n x y,
    match n with 0 => True | S n => x ≡ y end.
  Instance discrete_compl `{Equiv A} : Compl A := λ c, c 1.
  Instance discrete_cofe : Cofe A.
  Proof.
    split.
    * intros x y; split; [by intros ? []|intros Hn; apply (Hn 1)].
    * intros [|n]; [done|apply _].
    * by intros [|n].
    * done.
    * intros c [|n]; [done|apply (chain_cauchy c 1 (S n)); lia].
  Qed.
  Definition discreteC : cofeT := CofeT A.
End discrete_cofe.
Arguments discreteC _ {_ _}.

(** Later *)
Inductive later (A : Type) : Type := Later { later_car : A }.
Arguments Later {_} _.
Arguments later_car {_} _.
Section later.
  Instance later_equiv `{Equiv A} : Equiv (later A) := λ x y,
    later_car x ≡ later_car y.
  Instance later_dist `{Dist A} : Dist (later A) := λ n x y,
    match n with 0 => True | S n => later_car x ={n}= later_car y end.
  Program Definition later_chain `{Dist A} (c : chain (later A)) : chain A :=
    {| chain_car n := later_car (c (S n)) |}.
  Next Obligation. intros A ? c n i ?; apply (chain_cauchy c (S n)); lia. Qed.
  Instance later_compl `{Compl A} : Compl (later A) := λ c,
    Later (compl (later_chain c)).
  Instance later_cofe `{Cofe A} : Cofe (later A).
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
  Canonical Structure laterC (A : cofeT) : cofeT := CofeT (later A).

  Instance later_fmap : FMap later := λ A B f x, Later (f (later_car x)).
  Instance later_fmap_ne `{Cofe A, Cofe B} (f : A → B) :
    (∀ n, Proper (dist n ==> dist n) f) →
    ∀ n, Proper (dist n ==> dist n) (fmap f : later A → later B).
  Proof. intros Hf [|n] [x] [y] ?; do 2 red; simpl. done. by apply Hf. Qed.
  Lemma later_fmap_id {A} (x : later A) : id <$> x = x.
  Proof. by destruct x. Qed.
  Lemma later_fmap_compose {A B C} (f : A → B) (g : B → C) (x : later A) :
    g ∘ f <$> x = g <$> f <$> x.
  Proof. by destruct x. Qed.
  Definition laterC_map {A B} (f : A -n> B) : laterC A -n> laterC B :=
    CofeMor (fmap f : laterC A → laterC B).
  Instance laterC_contractive (A B : cofeT) : Contractive (@laterC_map A B).
  Proof. intros n f g Hf n'; apply Hf. Qed.
End later.

(* Option *)
Instance option_dist `{Dist A} : Dist (option A) := λ n o1 o2,
  match n with 0 => True | S n => option_Forall2 (dist n) o1 o2 end.
Program Definition option_chain `{Dist A}
    (c : chain (option A)) (x : A) (H : c 1 = Some x) : chain A :=
  {| chain_car n := from_option x (c (S n)) |}.
Next Obligation.
  intros A ? c x ? n i ?.
  feed inversion (chain_cauchy c 1 (S i)); auto with lia congruence.
  feed inversion (chain_cauchy c (S n) (S i)); simpl; auto with lia congruence.
Qed.
Instance option_compl `{Compl A} : Compl (option A) := λ c,
  match Some_dec (c 1) with
  | inleft (exist x H) => Some (compl (option_chain c x H))
  | inright _ => None
  end.
Instance option_cofe `{Cofe A} : Cofe (option A).
Proof.
  split.
  * intros mx my; split.
    { by destruct 1; intros [|n]; constructor; apply equiv_dist. }
    intros Hxy; feed inversion (Hxy 1); constructor; apply equiv_dist.
    intros n. feed inversion (Hxy (S n)); congruence.
  * intros [|n]; [by split|split].
    + by intros [x|]; constructor.
    + by destruct 1; constructor.
    + by intros [x|] [y|] [z|]; do 2 inversion 1; constructor; transitivity y.
  * by destruct n; [|destruct 1; constructor; apply dist_S].
  * done.
  * intros c [|n]; unfold compl, option_compl; [constructor|].
    destruct (Some_dec (c 1)) as [[x Hx]|].
    + assert (is_Some (c (S n))) as [y Hy].
      { feed inversion (chain_cauchy c 1 (S n)); try congruence; eauto with lia. }
      rewrite Hy; constructor.
      by rewrite (conv_compl (option_chain c x Hx) n); simpl; rewrite Hy.
    + feed inversion (chain_cauchy c 1 (S n)); auto with lia congruence.
      by constructor.
Qed.
Instance Some_ne `{Cofe A} : Proper (dist n ==> dist n) Some.
Proof. by intros [|n];[done|constructor; apply dist_S]. Qed.
Instance option_fmap_ne `{Cofe A, Cofe B} (f : A → B) :
  (∀ n, Proper (dist n ==> dist n) f) →
  ∀ n, Proper (dist n ==> dist n) (fmap f : option A → option B).
Proof. intros Hf [|n];[done|destruct 1;constructor;by apply Hf]. Qed.

(** Finite maps *)
Section map.
  Context `{FinMap K M}.
  Instance map_dist `{Dist A} : Dist (M A) := λ n m1 m2,
    ∀ i, m1 !! i ={n}= m2 !! i.
  Program Definition map_chain `{Dist A} (c : chain (M A))
    (k : K) : chain (option A) := {| chain_car n := c n !! k |}.
  Next Obligation. by intros A ? c k n i ?; apply (chain_cauchy c). Qed.
  Instance map_compl `{Compl A} : Compl (M A) := λ c,
    map_imap (λ i _, compl (map_chain c i)) (c 1).
  Instance map_cofe `{Cofe A} : Cofe (M A).
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
    * done.
    * intros c [|n] k; unfold compl, map_compl; [apply dist_0|].
      rewrite lookup_imap.
      assert ((∃ x y, c 1 !! k = Some x ∧ c (S n) !! k = Some y) ∨
        c 1 !! k = None ∧ c (S n) !! k = None) as [(x&y&Hx&Hy)|[-> ->]]
        by (feed inversion (λ H, chain_cauchy c 1 (S n) H k);
          eauto with lia congruence); [|done].
      by rewrite Hx; simpl; rewrite conv_compl; simpl; rewrite Hy.
  Qed.
  Instance lookup_ne `{Cofe A} n :
    Proper ((=) ==> dist n ==> dist n) (lookup : K → M A → option A).
  Proof. by intros k1 k2 -> m1 m2 Hm; apply Hm. Qed.
  Instance map_fmap_ne `{Cofe A, Cofe B} (f : A → B) :
    (∀ n, Proper (dist n ==> dist n) f) →
    ∀ n, Proper (dist n ==> dist n) (fmap f : M A → M B).
  Proof. by intros ? n m1 m2 Hm k; rewrite !lookup_fmap, Hm. Qed.
  Definition mapC (A : cofeT) : cofeT := CofeT (M A).
  Definition mapC_map {A B} (f: A -n> B) : mapC A -n> mapC B :=
    CofeMor (fmap f : mapC A → mapC B).
  Global Instance mapC_map_ne (A B : cofeT) :
    Proper (dist n ==> dist n) (@mapC_map A B).
  Proof.
    intros [|n] f g Hf m k; simpl; rewrite !lookup_fmap; [apply dist_0|].
    destruct (_ !! k) eqn:?; simpl; constructor; apply dist_S, Hf.
  Qed.
End map.
Arguments mapC {_} _ {_ _ _ _ _ _ _ _ _} _.

Canonical Structure PmapC := mapC Pmap.
Canonical Structure NmapC := mapC Nmap.
Canonical Structure ZmapC := mapC Zmap.
Canonical Structure stringmapC := mapC stringmap.
