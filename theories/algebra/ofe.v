From iris.algebra Require Export base.

(** This files defines (a shallow embedding of) the category of OFEs:
    Complete ordered families of equivalences. This is a cartesian closed
    category, and mathematically speaking, the entire development lives
    in this category. However, we will generally prefer to work with raw
    Coq functions plus some registered Proper instances for non-expansiveness.
    This makes writing such functions much easier. It turns out that it many 
    cases, we do not even need non-expansiveness.
*)

(** Unbundeled version *)
Class Dist A := dist : nat → relation A.
Instance: Params (@dist) 3.
Notation "x ≡{ n }≡ y" := (dist n x y)
  (at level 70, n at next level, format "x  ≡{ n }≡  y").
Hint Extern 0 (_ ≡{_}≡ _) => reflexivity.
Hint Extern 0 (_ ≡{_}≡ _) => symmetry; assumption.

Tactic Notation "cofe_subst" ident(x) :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H:@dist ?A ?d ?n x _ |- _ => setoid_subst_aux (@dist A d n) x
  | H:@dist ?A ?d ?n _ x |- _ => symmetry in H;setoid_subst_aux (@dist A d n) x
  end.
Tactic Notation "cofe_subst" :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H:@dist ?A ?d ?n ?x _ |- _ => setoid_subst_aux (@dist A d n) x
  | H:@dist ?A ?d ?n _ ?x |- _ => symmetry in H;setoid_subst_aux (@dist A d n) x
  end.

Record OfeMixin A `{Equiv A, Dist A} := {
  mixin_equiv_dist x y : x ≡ y ↔ ∀ n, x ≡{n}≡ y;
  mixin_dist_equivalence n : Equivalence (dist n);
  mixin_dist_S n x y : x ≡{S n}≡ y → x ≡{n}≡ y
}.

(** Bundeled version *)
Structure ofeT := OfeT' {
  ofe_car :> Type;
  ofe_equiv : Equiv ofe_car;
  ofe_dist : Dist ofe_car;
  ofe_mixin : OfeMixin ofe_car;
  _ : Type
}.
Arguments OfeT' _ {_ _} _ _.
Notation OfeT A m := (OfeT' A m A).
Add Printing Constructor ofeT.
Hint Extern 0 (Equiv _) => eapply (@ofe_equiv _) : typeclass_instances.
Hint Extern 0 (Dist _) => eapply (@ofe_dist _) : typeclass_instances.
Arguments ofe_car : simpl never.
Arguments ofe_equiv : simpl never.
Arguments ofe_dist : simpl never.
Arguments ofe_mixin : simpl never.

(** Lifting properties from the mixin *)
Section ofe_mixin.
  Context {A : ofeT}.
  Implicit Types x y : A.
  Lemma equiv_dist x y : x ≡ y ↔ ∀ n, x ≡{n}≡ y.
  Proof. apply (mixin_equiv_dist _ (ofe_mixin A)). Qed.
  Global Instance dist_equivalence n : Equivalence (@dist A _ n).
  Proof. apply (mixin_dist_equivalence _ (ofe_mixin A)). Qed.
  Lemma dist_S n x y : x ≡{S n}≡ y → x ≡{n}≡ y.
  Proof. apply (mixin_dist_S _ (ofe_mixin A)). Qed.
End ofe_mixin.

Hint Extern 1 (_ ≡{_}≡ _) => apply equiv_dist; assumption.

(** Discrete OFEs and Timeless elements *)
(* TODO: On paper, We called these "discrete elements". I think that makes
   more sense. *)
Class Timeless `{Equiv A, Dist A} (x : A) := timeless y : x ≡{0}≡ y → x ≡ y.
Arguments timeless {_ _ _} _ {_} _ _.
Class Discrete (A : ofeT) := discrete_timeless (x : A) :> Timeless x.

(** OFEs with a completion *)
Record chain (A : ofeT) := {
  chain_car :> nat → A;
  chain_cauchy n i : n ≤ i → chain_car i ≡{n}≡ chain_car n
}.
Arguments chain_car {_} _ _.
Arguments chain_cauchy {_} _ _ _ _.

Program Definition chain_map {A B : ofeT} (f : A → B)
    `{!∀ n, Proper (dist n ==> dist n) f} (c : chain A) : chain B :=
  {| chain_car n := f (c n) |}.
Next Obligation. by intros A B f Hf c n i ?; apply Hf, chain_cauchy. Qed.

Notation Compl A := (chain A%type → A).
Class Cofe (A : ofeT) := {
  compl : Compl A;
  conv_compl n c : compl c ≡{n}≡ c n;
}.
Arguments compl : simpl never.

(** General properties *)
Section cofe.
  Context {A : ofeT}.
  Implicit Types x y : A.
  Global Instance cofe_equivalence : Equivalence ((≡) : relation A).
  Proof.
    split.
    - by intros x; rewrite equiv_dist.
    - by intros x y; rewrite !equiv_dist.
    - by intros x y z; rewrite !equiv_dist; intros; trans y.
  Qed.
  Global Instance dist_ne n : Proper (dist n ==> dist n ==> iff) (@dist A _ n).
  Proof.
    intros x1 x2 ? y1 y2 ?; split; intros.
    - by trans x1; [|trans y1].
    - by trans x2; [|trans y2].
  Qed.
  Global Instance dist_proper n : Proper ((≡) ==> (≡) ==> iff) (@dist A _ n).
  Proof.
    by move => x1 x2 /equiv_dist Hx y1 y2 /equiv_dist Hy; rewrite (Hx n) (Hy n).
  Qed.
  Global Instance dist_proper_2 n x : Proper ((≡) ==> iff) (dist n x).
  Proof. by apply dist_proper. Qed.
  Lemma dist_le n n' x y : x ≡{n}≡ y → n' ≤ n → x ≡{n'}≡ y.
  Proof. induction 2; eauto using dist_S. Qed.
  Lemma dist_le' n n' x y : n' ≤ n → x ≡{n}≡ y → x ≡{n'}≡ y.
  Proof. intros; eauto using dist_le. Qed.
  Instance ne_proper {B : ofeT} (f : A → B)
    `{!∀ n, Proper (dist n ==> dist n) f} : Proper ((≡) ==> (≡)) f | 100.
  Proof. by intros x1 x2; rewrite !equiv_dist; intros Hx n; rewrite (Hx n). Qed.
  Instance ne_proper_2 {B C : ofeT} (f : A → B → C)
    `{!∀ n, Proper (dist n ==> dist n ==> dist n) f} :
    Proper ((≡) ==> (≡) ==> (≡)) f | 100.
  Proof.
     unfold Proper, respectful; setoid_rewrite equiv_dist.
     by intros x1 x2 Hx y1 y2 Hy n; rewrite (Hx n) (Hy n).
  Qed.

  Lemma conv_compl' `{Cofe A} n (c : chain A) : compl c ≡{n}≡ c (S n).
  Proof.
    transitivity (c n); first by apply conv_compl. symmetry.
    apply chain_cauchy. omega.
  Qed.
  Lemma timeless_iff n (x : A) `{!Timeless x} y : x ≡ y ↔ x ≡{n}≡ y.
  Proof.
    split; intros; auto. apply (timeless _), dist_le with n; auto with lia.
  Qed.
End cofe.

(** Contractive functions *)
Definition dist_later {A : ofeT} (n : nat) (x y : A) : Prop :=
  match n with 0 => True | S n => x ≡{n}≡ y end.
Arguments dist_later _ !_ _ _ /.

Global Instance dist_later_equivalence A n : Equivalence (@dist_later A n).
Proof. destruct n as [|n]. by split. apply dist_equivalence. Qed.

Notation Contractive f := (∀ n, Proper (dist_later n ==> dist n) f).

Instance const_contractive {A B : ofeT} (x : A) : Contractive (@const A B x).
Proof. by intros n y1 y2. Qed.

Section contractive.
  Context {A B : ofeT} (f : A → B) `{!Contractive f}.
  Implicit Types x y : A.

  Lemma contractive_0 x y : f x ≡{0}≡ f y.
  Proof. by apply (_ : Contractive f). Qed.
  Lemma contractive_S n x y : x ≡{n}≡ y → f x ≡{S n}≡ f y.
  Proof. intros. by apply (_ : Contractive f). Qed.

  Global Instance contractive_ne n : Proper (dist n ==> dist n) f | 100.
  Proof. by intros x y ?; apply dist_S, contractive_S. Qed.
  Global Instance contractive_proper : Proper ((≡) ==> (≡)) f | 100.
  Proof. apply (ne_proper _). Qed.
End contractive.

Ltac f_contractive :=
  match goal with
  | |- ?f _ ≡{_}≡ ?f _ => apply (_ : Proper (dist_later _ ==> _) f)
  | |- ?f _ _ ≡{_}≡ ?f _ _ => apply (_ : Proper (dist_later _ ==> _ ==> _) f)
  | |- ?f _ _ ≡{_}≡ ?f _ _ => apply (_ : Proper (_ ==> dist_later _ ==> _) f)
  end;
  try match goal with
  | |- dist_later ?n ?x ?y => destruct n as [|n]; [done|change (x ≡{n}≡ y)]
  end;
  try reflexivity.

Ltac solve_contractive :=
  preprocess_solve_proper;
  solve [repeat (first [f_contractive|f_equiv]; try eassumption)].

(** Fixpoint *)
Program Definition fixpoint_chain {A : ofeT} `{Inhabited A} (f : A → A)
  `{!Contractive f} : chain A := {| chain_car i := Nat.iter (S i) f inhabitant |}.
Next Obligation.
  intros A ? f ? n.
  induction n as [|n IH]=> -[|i] //= ?; try omega.
  - apply (contractive_0 f).
  - apply (contractive_S f), IH; auto with omega.
Qed.

Program Definition fixpoint_def `{Cofe A, Inhabited A} (f : A → A)
  `{!Contractive f} : A := compl (fixpoint_chain f).
Definition fixpoint_aux : { x | x = @fixpoint_def }. by eexists. Qed.
Definition fixpoint {A AC AiH} f {Hf} := proj1_sig fixpoint_aux A AC AiH f Hf.
Definition fixpoint_eq : @fixpoint = @fixpoint_def := proj2_sig fixpoint_aux.

Section fixpoint.
  Context `{Cofe A, Inhabited A} (f : A → A) `{!Contractive f}.

  Lemma fixpoint_unfold : fixpoint f ≡ f (fixpoint f).
  Proof.
    apply equiv_dist=>n.
    rewrite fixpoint_eq /fixpoint_def (conv_compl n (fixpoint_chain f)) //.
    induction n as [|n IH]; simpl; eauto using contractive_0, contractive_S.
  Qed.

  Lemma fixpoint_unique (x : A) : x ≡ f x → x ≡ fixpoint f.
  Proof.
    rewrite !equiv_dist=> Hx n. induction n as [|n IH]; simpl in *.
    - rewrite Hx fixpoint_unfold; eauto using contractive_0.
    - rewrite Hx fixpoint_unfold. apply (contractive_S _), IH.
  Qed.

  Lemma fixpoint_ne (g : A → A) `{!Contractive g} n :
    (∀ z, f z ≡{n}≡ g z) → fixpoint f ≡{n}≡ fixpoint g.
  Proof.
    intros Hfg. rewrite fixpoint_eq /fixpoint_def
      (conv_compl n (fixpoint_chain f)) (conv_compl n (fixpoint_chain g)) /=.
    induction n as [|n IH]; simpl in *; [by rewrite !Hfg|].
    rewrite Hfg; apply contractive_S, IH; auto using dist_S.
  Qed.
  Lemma fixpoint_proper (g : A → A) `{!Contractive g} :
    (∀ x, f x ≡ g x) → fixpoint f ≡ fixpoint g.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_ne. Qed.
End fixpoint.

(** Mutual fixpoints *)
Section fixpoint2.
  Context `{Cofe A, Cofe B, !Inhabited A, !Inhabited B}.
  Context (fA : A → B → A).
  Context (fB : A → B → B).
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.

  Local Definition fixpoint_AB (x : A) : B := fixpoint (fB x).
  Local Instance fixpoint_AB_contractive : Contractive fixpoint_AB.
  Proof.
    intros n x x' Hx; rewrite /fixpoint_AB.
    apply fixpoint_ne=> y. by f_contractive.
  Qed.

  Local Definition fixpoint_AA (x : A) : A := fA x (fixpoint_AB x).
  Local Instance fixpoint_AA_contractive : Contractive fixpoint_AA.
  Proof. solve_contractive. Qed.

  Definition fixpoint_A : A := fixpoint fixpoint_AA.
  Definition fixpoint_B : B := fixpoint_AB fixpoint_A.

  Lemma fixpoint_A_unfold : fA fixpoint_A fixpoint_B ≡ fixpoint_A.
  Proof. by rewrite {2}/fixpoint_A (fixpoint_unfold _). Qed.
  Lemma fixpoint_B_unfold : fB fixpoint_A fixpoint_B ≡ fixpoint_B.
  Proof. by rewrite {2}/fixpoint_B /fixpoint_AB (fixpoint_unfold _). Qed.

  Instance: Proper ((≡) ==> (≡) ==> (≡)) fA.
  Proof.
    apply ne_proper_2=> n x x' ? y y' ?. f_contractive; auto using dist_S.
  Qed.
  Instance: Proper ((≡) ==> (≡) ==> (≡)) fB.
  Proof.
    apply ne_proper_2=> n x x' ? y y' ?. f_contractive; auto using dist_S.
  Qed.

  Lemma fixpoint_A_unique p q : fA p q ≡ p → fB p q ≡ q → p ≡ fixpoint_A.
  Proof.
    intros HfA HfB. rewrite -HfA. apply fixpoint_unique. rewrite /fixpoint_AA.
    f_equiv=> //. apply fixpoint_unique. by rewrite HfA HfB.
  Qed.
  Lemma fixpoint_B_unique p q : fA p q ≡ p → fB p q ≡ q → q ≡ fixpoint_B.
  Proof. intros. apply fixpoint_unique. by rewrite -fixpoint_A_unique. Qed.
End fixpoint2.

Section fixpoint2_ne.
  Context `{Cofe A, Cofe B, !Inhabited A, !Inhabited B}.
  Context (fA fA' : A → B → A).
  Context (fB fB' : A → B → B).
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA}.
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA'}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB'}.

  Lemma fixpoint_A_ne n :
    (∀ x y, fA x y ≡{n}≡ fA' x y) → (∀ x y, fB x y ≡{n}≡ fB' x y) →
    fixpoint_A fA fB ≡{n}≡ fixpoint_A fA' fB'.
  Proof.
    intros HfA HfB. apply fixpoint_ne=> z.
    rewrite /fixpoint_AA /fixpoint_AB HfA. f_equiv. by apply fixpoint_ne.
  Qed.
  Lemma fixpoint_B_ne n :
    (∀ x y, fA x y ≡{n}≡ fA' x y) → (∀ x y, fB x y ≡{n}≡ fB' x y) →
    fixpoint_B fA fB ≡{n}≡ fixpoint_B fA' fB'.
  Proof.
    intros HfA HfB. apply fixpoint_ne=> z. rewrite HfB. f_contractive.
    apply fixpoint_A_ne; auto using dist_S.
  Qed.

  Lemma fixpoint_A_proper :
    (∀ x y, fA x y ≡ fA' x y) → (∀ x y, fB x y ≡ fB' x y) →
    fixpoint_A fA fB ≡ fixpoint_A fA' fB'.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_A_ne. Qed.
  Lemma fixpoint_B_proper :
    (∀ x y, fA x y ≡ fA' x y) → (∀ x y, fB x y ≡ fB' x y) →
    fixpoint_B fA fB ≡ fixpoint_B fA' fB'.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_B_ne. Qed.
End fixpoint2_ne.

(** Function space *)
(* We make [ofe_fun] a definition so that we can register it as a canonical
structure. *)
Definition ofe_fun (A : Type) (B : ofeT) := A → B.

Section ofe_fun.
  Context {A : Type} {B : ofeT}.
  Instance ofe_fun_equiv : Equiv (ofe_fun A B) := λ f g, ∀ x, f x ≡ g x.
  Instance ofe_fun_dist : Dist (ofe_fun A B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition ofe_fun_ofe_mixin : OfeMixin (ofe_fun A B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - by intros n f g ? x; apply dist_S.
  Qed.
  Canonical Structure ofe_funC := OfeT (ofe_fun A B) ofe_fun_ofe_mixin.

  Program Definition ofe_fun_chain `(c : chain ofe_funC)
    (x : A) : chain B := {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Global Program Instance ofe_fun_cofe `{Cofe B} : Cofe ofe_funC :=
    { compl c x := compl (ofe_fun_chain c x) }.
  Next Obligation. intros ? n c x. apply (conv_compl n (ofe_fun_chain c x)). Qed.
End ofe_fun.

Arguments ofe_funC : clear implicits.
Notation "A -c> B" :=
  (ofe_funC A B) (at level 99, B at level 200, right associativity).
Instance ofe_fun_inhabited {A} {B : ofeT} `{Inhabited B} :
  Inhabited (A -c> B) := populate (λ _, inhabitant).

(** Non-expansive function space *)
Record ofe_mor (A B : ofeT) : Type := CofeMor {
  ofe_mor_car :> A → B;
  ofe_mor_ne n : Proper (dist n ==> dist n) ofe_mor_car
}.
Arguments CofeMor {_ _} _ {_}.
Add Printing Constructor ofe_mor.
Existing Instance ofe_mor_ne.

Notation "'λne' x .. y , t" :=
  (@CofeMor _ _ (λ x, .. (@CofeMor _ _ (λ y, t) _) ..) _)
  (at level 200, x binder, y binder, right associativity).

Section ofe_mor.
  Context {A B : ofeT}.
  Global Instance ofe_mor_proper (f : ofe_mor A B) : Proper ((≡) ==> (≡)) f.
  Proof. apply ne_proper, ofe_mor_ne. Qed.
  Instance ofe_mor_equiv : Equiv (ofe_mor A B) := λ f g, ∀ x, f x ≡ g x.
  Instance ofe_mor_dist : Dist (ofe_mor A B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition ofe_mor_ofe_mixin : OfeMixin (ofe_mor A B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - by intros n f g ? x; apply dist_S.
  Qed.
  Canonical Structure ofe_morC := OfeT (ofe_mor A B) ofe_mor_ofe_mixin.

  Program Definition ofe_mor_chain (c : chain ofe_morC)
    (x : A) : chain B := {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Program Definition ofe_mor_compl `{Cofe B} : Compl ofe_morC := λ c,
    {| ofe_mor_car x := compl (ofe_mor_chain c x) |}.
  Next Obligation.
    intros ? c n x y Hx. by rewrite (conv_compl n (ofe_mor_chain c x))
      (conv_compl n (ofe_mor_chain c y)) /= Hx.
  Qed.
  Global Program Instance ofe_more_cofe `{Cofe B} : Cofe ofe_morC :=
    {| compl := ofe_mor_compl |}.
  Next Obligation.
    intros ? n c x; simpl.
    by rewrite (conv_compl n (ofe_mor_chain c x)) /=.
  Qed.

  Global Instance ofe_mor_car_ne n :
    Proper (dist n ==> dist n ==> dist n) (@ofe_mor_car A B).
  Proof. intros f g Hfg x y Hx; rewrite Hx; apply Hfg. Qed.
  Global Instance ofe_mor_car_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@ofe_mor_car A B) := ne_proper_2 _.
  Lemma ofe_mor_ext (f g : ofe_mor A B) : f ≡ g ↔ ∀ x, f x ≡ g x.
  Proof. done. Qed.
End ofe_mor.

Arguments ofe_morC : clear implicits.
Notation "A -n> B" :=
  (ofe_morC A B) (at level 99, B at level 200, right associativity).
Instance ofe_mor_inhabited {A B : ofeT} `{Inhabited B} :
  Inhabited (A -n> B) := populate (λne _, inhabitant).

(** Identity and composition and constant function *)
Definition cid {A} : A -n> A := CofeMor id.
Instance: Params (@cid) 1.
Definition cconst {A B : ofeT} (x : B) : A -n> B := CofeMor (const x).
Instance: Params (@cconst) 2.

Definition ccompose {A B C}
  (f : B -n> C) (g : A -n> B) : A -n> C := CofeMor (f ∘ g).
Instance: Params (@ccompose) 3.
Infix "◎" := ccompose (at level 40, left associativity).
Lemma ccompose_ne {A B C} (f1 f2 : B -n> C) (g1 g2 : A -n> B) n :
  f1 ≡{n}≡ f2 → g1 ≡{n}≡ g2 → f1 ◎ g1 ≡{n}≡ f2 ◎ g2.
Proof. by intros Hf Hg x; rewrite /= (Hg x) (Hf (g2 x)). Qed.

(* Function space maps *)
Definition ofe_mor_map {A A' B B'} (f : A' -n> A) (g : B -n> B')
  (h : A -n> B) : A' -n> B' := g ◎ h ◎ f.
Instance ofe_mor_map_ne {A A' B B'} n :
  Proper (dist n ==> dist n ==> dist n ==> dist n) (@ofe_mor_map A A' B B').
Proof. intros ??? ??? ???. by repeat apply ccompose_ne. Qed.

Definition ofe_morC_map {A A' B B'} (f : A' -n> A) (g : B -n> B') :
  (A -n> B) -n> (A' -n>  B') := CofeMor (ofe_mor_map f g).
Instance ofe_morC_map_ne {A A' B B'} n :
  Proper (dist n ==> dist n ==> dist n) (@ofe_morC_map A A' B B').
Proof.
  intros f f' Hf g g' Hg ?. rewrite /= /ofe_mor_map.
  by repeat apply ccompose_ne.
Qed.

(** unit *)
Section unit.
  Instance unit_dist : Dist unit := λ _ _ _, True.
  Definition unit_ofe_mixin : OfeMixin unit.
  Proof. by repeat split; try exists 0. Qed.
  Canonical Structure unitC : ofeT := OfeT unit unit_ofe_mixin.

  Global Program Instance unit_cofe : Cofe unitC := { compl x := () }.
  Next Obligation. by repeat split; try exists 0. Qed.

  Global Instance unit_discrete_cofe : Discrete unitC.
  Proof. done. Qed.
End unit.

(** Product *)
Section product.
  Context {A B : ofeT}.

  Instance prod_dist : Dist (A * B) := λ n, prod_relation (dist n) (dist n).
  Global Instance pair_ne :
    Proper (dist n ==> dist n ==> dist n) (@pair A B) := _.
  Global Instance fst_ne : Proper (dist n ==> dist n) (@fst A B) := _.
  Global Instance snd_ne : Proper (dist n ==> dist n) (@snd A B) := _.
  Definition prod_ofe_mixin : OfeMixin (A * B).
  Proof.
    split.
    - intros x y; unfold dist, prod_dist, equiv, prod_equiv, prod_relation.
      rewrite !equiv_dist; naive_solver.
    - apply _.
    - by intros n [x1 y1] [x2 y2] [??]; split; apply dist_S.
  Qed.
  Canonical Structure prodC : ofeT := OfeT (A * B) prod_ofe_mixin.

  Global Program Instance prod_cofe `{Cofe A, Cofe B} : Cofe prodC :=
    { compl c := (compl (chain_map fst c), compl (chain_map snd c)) }.
  Next Obligation.
    intros ?? n c; split. apply (conv_compl n (chain_map fst c)).
    apply (conv_compl n (chain_map snd c)).
  Qed.

  Global Instance prod_timeless (x : A * B) :
    Timeless (x.1) → Timeless (x.2) → Timeless x.
  Proof. by intros ???[??]; split; apply (timeless _). Qed.
  Global Instance prod_discrete_cofe : Discrete A → Discrete B → Discrete prodC.
  Proof. intros ?? [??]; apply _. Qed.
End product.

Arguments prodC : clear implicits.
Typeclasses Opaque prod_dist.

Instance prod_map_ne {A A' B B' : ofeT} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@prod_map A A' B B').
Proof. by intros f f' Hf g g' Hg ?? [??]; split; [apply Hf|apply Hg]. Qed.
Definition prodC_map {A A' B B'} (f : A -n> A') (g : B -n> B') :
  prodC A B -n> prodC A' B' := CofeMor (prod_map f g).
Instance prodC_map_ne {A A' B B'} n :
  Proper (dist n ==> dist n ==> dist n) (@prodC_map A A' B B').
Proof. intros f f' Hf g g' Hg [??]; split; [apply Hf|apply Hg]. Qed.

(** Functors *)
Structure cFunctor := CFunctor {
  cFunctor_car : ofeT → ofeT → ofeT;
  cFunctor_map {A1 A2 B1 B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → cFunctor_car A1 B1 -n> cFunctor_car A2 B2;
  cFunctor_ne {A1 A2 B1 B2} n :
    Proper (dist n ==> dist n) (@cFunctor_map A1 A2 B1 B2);
  cFunctor_id {A B : ofeT} (x : cFunctor_car A B) :
    cFunctor_map (cid,cid) x ≡ x;
  cFunctor_compose {A1 A2 A3 B1 B2 B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    cFunctor_map (f◎g, g'◎f') x ≡ cFunctor_map (g,g') (cFunctor_map (f,f') x)
}.
Existing Instance cFunctor_ne.
Instance: Params (@cFunctor_map) 5.

Delimit Scope cFunctor_scope with CF.
Bind Scope cFunctor_scope with cFunctor.

Class cFunctorContractive (F : cFunctor) :=
  cFunctor_contractive A1 A2 B1 B2 :> Contractive (@cFunctor_map F A1 A2 B1 B2).

Definition cFunctor_diag (F: cFunctor) (A: ofeT) : ofeT := cFunctor_car F A A.
Coercion cFunctor_diag : cFunctor >-> Funclass.

Program Definition constCF (B : ofeT) : cFunctor :=
  {| cFunctor_car A1 A2 := B; cFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.

Instance constCF_contractive B : cFunctorContractive (constCF B).
Proof. rewrite /cFunctorContractive; apply _. Qed.

Program Definition idCF : cFunctor :=
  {| cFunctor_car A1 A2 := A2; cFunctor_map A1 A2 B1 B2 f := f.2 |}.
Solve Obligations with done.

Program Definition prodCF (F1 F2 : cFunctor) : cFunctor := {|
  cFunctor_car A B := prodC (cFunctor_car F1 A B) (cFunctor_car F2 A B);
  cFunctor_map A1 A2 B1 B2 fg :=
    prodC_map (cFunctor_map F1 fg) (cFunctor_map F2 fg)
|}.
Next Obligation.
  intros ?? A1 A2 B1 B2 n ???; by apply prodC_map_ne; apply cFunctor_ne.
Qed.
Next Obligation. by intros F1 F2 A B [??]; rewrite /= !cFunctor_id. Qed.
Next Obligation.
  intros F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl.
  by rewrite !cFunctor_compose.
Qed.

Instance prodCF_contractive F1 F2 :
  cFunctorContractive F1 → cFunctorContractive F2 →
  cFunctorContractive (prodCF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply prodC_map_ne; apply cFunctor_contractive.
Qed.

Instance compose_ne {A} {B B' : ofeT} (f : B -n> B') n :
  Proper (dist n ==> dist n) (compose f : (A -c> B) → A -c> B').
Proof. intros g g' Hf x; simpl. by rewrite (Hf x). Qed.

Definition ofe_funC_map {A B B'} (f : B -n> B') : (A -c> B) -n> (A -c> B') :=
  @CofeMor (_ -c> _) (_ -c> _) (compose f) _.
Instance ofe_funC_map_ne {A B B'} n :
  Proper (dist n ==> dist n) (@ofe_funC_map A B B').
Proof. intros f f' Hf g x. apply Hf. Qed.

Program Definition ofe_funCF (T : Type) (F : cFunctor) : cFunctor := {|
  cFunctor_car A B := ofe_funC T (cFunctor_car F A B);
  cFunctor_map A1 A2 B1 B2 fg := ofe_funC_map (cFunctor_map F fg)
|}.
Next Obligation.
  intros ?? A1 A2 B1 B2 n ???; by apply ofe_funC_map_ne; apply cFunctor_ne.
Qed.
Next Obligation. intros F1 F2 A B ??. by rewrite /= /compose /= !cFunctor_id. Qed.
Next Obligation.
  intros T F A1 A2 A3 B1 B2 B3 f g f' g' ??; simpl.
  by rewrite !cFunctor_compose.
Qed.

Instance ofe_funCF_contractive (T : Type) (F : cFunctor) :
  cFunctorContractive F → cFunctorContractive (ofe_funCF T F).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply ofe_funC_map_ne; apply cFunctor_contractive.
Qed.

Program Definition ofe_morCF (F1 F2 : cFunctor) : cFunctor := {|
  cFunctor_car A B := cFunctor_car F1 B A -n> cFunctor_car F2 A B;
  cFunctor_map A1 A2 B1 B2 fg :=
    ofe_morC_map (cFunctor_map F1 (fg.2, fg.1)) (cFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 A1 A2 B1 B2 n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morC_map_ne; apply cFunctor_ne; split; by apply Hfg.
Qed.
Next Obligation.
  intros F1 F2 A B [f ?] ?; simpl. rewrite /= !cFunctor_id.
  apply (ne_proper f). apply cFunctor_id.
Qed.
Next Obligation.
  intros F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [h ?] ?; simpl in *.
  rewrite -!cFunctor_compose. do 2 apply (ne_proper _). apply cFunctor_compose.
Qed.

Instance ofe_morCF_contractive F1 F2 :
  cFunctorContractive F1 → cFunctorContractive F2 →
  cFunctorContractive (ofe_morCF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morC_map_ne; apply cFunctor_contractive; destruct n, Hfg; by split.
Qed.

(** Sum *)
Section sum.
  Context {A B : ofeT}.

  Instance sum_dist : Dist (A + B) := λ n, sum_relation (dist n) (dist n).
  Global Instance inl_ne : Proper (dist n ==> dist n) (@inl A B) := _.
  Global Instance inr_ne : Proper (dist n ==> dist n) (@inr A B) := _.
  Global Instance inl_ne_inj : Inj (dist n) (dist n) (@inl A B) := _.
  Global Instance inr_ne_inj : Inj (dist n) (dist n) (@inr A B) := _.

  Definition sum_ofe_mixin : OfeMixin (A + B).
  Proof.
    split.
    - intros x y; split=> Hx.
      + destruct Hx=> n; constructor; by apply equiv_dist.
      + destruct (Hx 0); constructor; apply equiv_dist=> n; by apply (inj _).
    - apply _.
    - destruct 1; constructor; by apply dist_S.
  Qed.
  Canonical Structure sumC : ofeT := OfeT (A + B) sum_ofe_mixin.

  Program Definition inl_chain (c : chain sumC) (a : A) : chain A :=
    {| chain_car n := match c n return _ with inl a' => a' | _ => a end |}.
  Next Obligation. intros c a n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
  Program Definition inr_chain (c : chain sumC) (b : B) : chain B :=
    {| chain_car n := match c n return _ with inr b' => b' | _ => b end |}.
  Next Obligation. intros c b n i ?; simpl. by destruct (chain_cauchy c n i). Qed.

  Definition sum_compl `{Cofe A, Cofe B} : Compl sumC := λ c,
    match c 0 with
    | inl a => inl (compl (inl_chain c a))
    | inr b => inr (compl (inr_chain c b))
    end.
  Global Program Instance sum_cofe `{Cofe A, Cofe B} : Cofe sumC :=
    { compl := sum_compl }.
  Next Obligation.
    intros ?? n c; rewrite /compl /sum_compl.
    feed inversion (chain_cauchy c 0 n); first by auto with lia; constructor.
    - rewrite (conv_compl n (inl_chain c _)) /=. destruct (c n); naive_solver.
    - rewrite (conv_compl n (inr_chain c _)) /=. destruct (c n); naive_solver.
  Qed.

  Global Instance inl_timeless (x : A) : Timeless x → Timeless (inl x).
  Proof. inversion_clear 2; constructor; by apply (timeless _). Qed.
  Global Instance inr_timeless (y : B) : Timeless y → Timeless (inr y).
  Proof. inversion_clear 2; constructor; by apply (timeless _). Qed.
  Global Instance sum_discrete_cofe : Discrete A → Discrete B → Discrete sumC.
  Proof. intros ?? [?|?]; apply _. Qed.
End sum.

Arguments sumC : clear implicits.
Typeclasses Opaque sum_dist.

Instance sum_map_ne {A A' B B' : ofeT} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@sum_map A A' B B').
Proof.
  intros f f' Hf g g' Hg ??; destruct 1; constructor; [by apply Hf|by apply Hg].
Qed.
Definition sumC_map {A A' B B'} (f : A -n> A') (g : B -n> B') :
  sumC A B -n> sumC A' B' := CofeMor (sum_map f g).
Instance sumC_map_ne {A A' B B'} n :
  Proper (dist n ==> dist n ==> dist n) (@sumC_map A A' B B').
Proof. intros f f' Hf g g' Hg [?|?]; constructor; [apply Hf|apply Hg]. Qed.

Program Definition sumCF (F1 F2 : cFunctor) : cFunctor := {|
  cFunctor_car A B := sumC (cFunctor_car F1 A B) (cFunctor_car F2 A B);
  cFunctor_map A1 A2 B1 B2 fg :=
    sumC_map (cFunctor_map F1 fg) (cFunctor_map F2 fg)
|}.
Next Obligation.
  intros ?? A1 A2 B1 B2 n ???; by apply sumC_map_ne; apply cFunctor_ne.
Qed.
Next Obligation. by intros F1 F2 A B [?|?]; rewrite /= !cFunctor_id. Qed.
Next Obligation.
  intros F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [?|?]; simpl;
    by rewrite !cFunctor_compose.
Qed.

Instance sumCF_contractive F1 F2 :
  cFunctorContractive F1 → cFunctorContractive F2 →
  cFunctorContractive (sumCF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply sumC_map_ne; apply cFunctor_contractive.
Qed.

(** Discrete cofe *)
Section discrete_cofe.
  Context `{Equiv A, @Equivalence A (≡)}.

  Instance discrete_dist : Dist A := λ n x y, x ≡ y.
  Definition discrete_ofe_mixin : OfeMixin A.
  Proof.
    split.
    - intros x y; split; [done|intros Hn; apply (Hn 0)].
    - done.
    - done.
  Qed.

  Global Program Instance discrete_cofe : Cofe (OfeT A discrete_ofe_mixin) :=
    { compl c := c 0 }.
  Next Obligation.
    intros n c. rewrite /compl /=;
    symmetry; apply (chain_cauchy c 0 n). omega.
  Qed.
End discrete_cofe.

Notation discreteC A := (OfeT A discrete_ofe_mixin).
Notation leibnizC A := (OfeT A (@discrete_ofe_mixin _ equivL _)).

Instance discrete_discrete_cofe `{Equiv A, @Equivalence A (≡)} :
  Discrete (discreteC A).
Proof. by intros x y. Qed.
Instance leibnizC_leibniz A : LeibnizEquiv (leibnizC A).
Proof. by intros x y. Qed.

Canonical Structure boolC := leibnizC bool.
Canonical Structure natC := leibnizC nat.
Canonical Structure positiveC := leibnizC positive.
Canonical Structure NC := leibnizC N.
Canonical Structure ZC := leibnizC Z.

(* Option *)
Section option.
  Context {A : ofeT}.

  Instance option_dist : Dist (option A) := λ n, option_Forall2 (dist n).
  Lemma dist_option_Forall2 n mx my : mx ≡{n}≡ my ↔ option_Forall2 (dist n) mx my.
  Proof. done. Qed.

  Definition option_ofe_mixin : OfeMixin (option A).
  Proof.
    split.
    - intros mx my; split; [by destruct 1; constructor; apply equiv_dist|].
      intros Hxy; destruct (Hxy 0); constructor; apply equiv_dist.
      by intros n; feed inversion (Hxy n).
    - apply _.
    - destruct 1; constructor; by apply dist_S.
  Qed.
  Canonical Structure optionC := OfeT (option A) option_ofe_mixin.

  Program Definition option_chain (c : chain optionC) (x : A) : chain A :=
    {| chain_car n := from_option id x (c n) |}.
  Next Obligation. intros c x n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
  Definition option_compl `{Cofe A} : Compl optionC := λ c,
    match c 0 with Some x => Some (compl (option_chain c x)) | None => None end.
  Global Program Instance option_cofe `{Cofe A} : Cofe optionC :=
    { compl := option_compl }.
  Next Obligation.
    intros ? n c; rewrite /compl /option_compl.
    feed inversion (chain_cauchy c 0 n); auto with lia; [].
    constructor. rewrite (conv_compl n (option_chain c _)) /=.
    destruct (c n); naive_solver.
  Qed.

  Global Instance option_discrete : Discrete A → Discrete optionC.
  Proof. destruct 2; constructor; by apply (timeless _). Qed.

  Global Instance Some_ne : Proper (dist n ==> dist n) (@Some A).
  Proof. by constructor. Qed.
  Global Instance is_Some_ne n : Proper (dist n ==> iff) (@is_Some A).
  Proof. destruct 1; split; eauto. Qed.
  Global Instance Some_dist_inj : Inj (dist n) (dist n) (@Some A).
  Proof. by inversion_clear 1. Qed.
  Global Instance from_option_ne {B} (R : relation B) (f : A → B) n :
    Proper (dist n ==> R) f → Proper (R ==> dist n ==> R) (from_option f).
  Proof. destruct 3; simpl; auto. Qed.

  Global Instance None_timeless : Timeless (@None A).
  Proof. inversion_clear 1; constructor. Qed.
  Global Instance Some_timeless x : Timeless x → Timeless (Some x).
  Proof. by intros ?; inversion_clear 1; constructor; apply timeless. Qed.

  Lemma dist_None n mx : mx ≡{n}≡ None ↔ mx = None.
  Proof. split; [by inversion_clear 1|by intros ->]. Qed.
  Lemma dist_Some_inv_l n mx my x :
    mx ≡{n}≡ my → mx = Some x → ∃ y, my = Some y ∧ x ≡{n}≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma dist_Some_inv_r n mx my y :
    mx ≡{n}≡ my → my = Some y → ∃ x, mx = Some x ∧ x ≡{n}≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma dist_Some_inv_l' n my x : Some x ≡{n}≡ my → ∃ x', Some x' = my ∧ x ≡{n}≡ x'.
  Proof. intros ?%(dist_Some_inv_l _ _ _ x); naive_solver. Qed.
  Lemma dist_Some_inv_r' n mx y : mx ≡{n}≡ Some y → ∃ y', mx = Some y' ∧ y ≡{n}≡ y'.
  Proof. intros ?%(dist_Some_inv_r _ _ _ y); naive_solver. Qed.
End option.

Typeclasses Opaque option_dist.
Arguments optionC : clear implicits.

Instance option_fmap_ne {A B : ofeT} n:
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@fmap option _ A B).
Proof. intros f f' Hf ?? []; constructor; auto. Qed.
Definition optionC_map {A B} (f : A -n> B) : optionC A -n> optionC B :=
  CofeMor (fmap f : optionC A → optionC B).
Instance optionC_map_ne A B n : Proper (dist n ==> dist n) (@optionC_map A B).
Proof. by intros f f' Hf []; constructor; apply Hf. Qed.

Program Definition optionCF (F : cFunctor) : cFunctor := {|
  cFunctor_car A B := optionC (cFunctor_car F A B);
  cFunctor_map A1 A2 B1 B2 fg := optionC_map (cFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=>y; apply cFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=>y; apply cFunctor_compose.
Qed.

Instance optionCF_contractive F :
  cFunctorContractive F → cFunctorContractive (optionCF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, cFunctor_contractive.
Qed.

(** Later *)
Inductive later (A : Type) : Type := Next { later_car : A }.
Add Printing Constructor later.
Arguments Next {_} _.
Arguments later_car {_} _.

Section later.
  Context {A : ofeT}.
  Instance later_equiv : Equiv (later A) := λ x y, later_car x ≡ later_car y.
  Instance later_dist : Dist (later A) := λ n x y,
    dist_later n (later_car x) (later_car y).
  Definition later_ofe_mixin : OfeMixin (later A).
  Proof.
    split.
    - intros x y; unfold equiv, later_equiv; rewrite !equiv_dist.
      split. intros Hxy [|n]; [done|apply Hxy]. intros Hxy n; apply (Hxy (S n)).
    - split; rewrite /dist /later_dist.
      + by intros [x].
      + by intros [x] [y].
      + by intros [x] [y] [z] ??; trans y.
    - intros [|n] [x] [y] ?; [done|]; rewrite /dist /later_dist; by apply dist_S.
  Qed.
  Canonical Structure laterC : ofeT := OfeT (later A) later_ofe_mixin.

  Program Definition later_chain (c : chain laterC) : chain A :=
    {| chain_car n := later_car (c (S n)) |}.
  Next Obligation. intros c n i ?; apply (chain_cauchy c (S n)); lia. Qed.
  Global Program Instance later_cofe `{Cofe A} : Cofe laterC := 
    { compl c := Next (compl (later_chain c)) }.
  Next Obligation.
    intros ? [|n] c; [done|by apply (conv_compl n (later_chain c))].
  Qed.

  Global Instance Next_contractive : Contractive (@Next A).
  Proof. by intros [|n] x y. Qed.
  Global Instance Later_inj n : Inj (dist n) (dist (S n)) (@Next A).
  Proof. by intros x y. Qed.

  Instance later_car_anti_contractive n :
    Proper (dist n ==> dist_later n) later_car.
  Proof. move=> [x] [y] /= Hxy. done. Qed.

  (* f is contractive iff it can factor into `Next` and a non-expansive function. *)
  Lemma contractive_alt {B : ofeT} (f : A → B) :
    Contractive f ↔ ∃ g : later A → B,
      (∀ n, Proper (dist n ==> dist n) g) ∧ (∀ x, f x ≡ g (Next x)).
  Proof.
    split.
    - intros Hf. exists (f ∘ later_car); split=> // n x y ?. by f_equiv.
    - intros (g&Hg&Hf) n x y Hxy. rewrite !Hf. by apply Hg.
  Qed.
End later.

Arguments laterC : clear implicits.

Definition later_map {A B} (f : A → B) (x : later A) : later B :=
  Next (f (later_car x)).
Instance later_map_ne {A B : ofeT} (f : A → B) n :
  Proper (dist (pred n) ==> dist (pred n)) f →
  Proper (dist n ==> dist n) (later_map f) | 0.
Proof. destruct n as [|n]; intros Hf [x] [y] ?; do 2 red; simpl; auto. Qed.
Lemma later_map_id {A} (x : later A) : later_map id x = x.
Proof. by destruct x. Qed.
Lemma later_map_compose {A B C} (f : A → B) (g : B → C) (x : later A) :
  later_map (g ∘ f) x = later_map g (later_map f x).
Proof. by destruct x. Qed.
Lemma later_map_ext {A B : ofeT} (f g : A → B) x :
  (∀ x, f x ≡ g x) → later_map f x ≡ later_map g x.
Proof. destruct x; intros Hf; apply Hf. Qed.
Definition laterC_map {A B} (f : A -n> B) : laterC A -n> laterC B :=
  CofeMor (later_map f).
Instance laterC_map_contractive (A B : ofeT) : Contractive (@laterC_map A B).
Proof. intros [|n] f g Hf n'; [done|]; apply Hf; lia. Qed.

Program Definition laterCF (F : cFunctor) : cFunctor := {|
  cFunctor_car A B := laterC (cFunctor_car F A B);
  cFunctor_map A1 A2 B1 B2 fg := laterC_map (cFunctor_map F fg)
|}.
Next Obligation.
  intros F A1 A2 B1 B2 n fg fg' ?.
  by apply (contractive_ne laterC_map), cFunctor_ne.
Qed.
Next Obligation.
  intros F A B x; simpl. rewrite -{2}(later_map_id x).
  apply later_map_ext=>y. by rewrite cFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x; simpl. rewrite -later_map_compose.
  apply later_map_ext=>y; apply cFunctor_compose.
Qed.

Instance laterCF_contractive F : cFunctorContractive (laterCF F).
Proof.
  intros A1 A2 B1 B2 n fg fg' Hfg. apply laterC_map_contractive.
  destruct n as [|n]; simpl in *; first done. apply cFunctor_ne, Hfg.
Qed.

(** Notation for writing functors *)
Notation "∙" := idCF : cFunctor_scope.
Notation "T -c> F" := (ofe_funCF T%type F%CF) : cFunctor_scope.
Notation "F1 -n> F2" := (ofe_morCF F1%CF F2%CF) : cFunctor_scope.
Notation "F1 * F2" := (prodCF F1%CF F2%CF) : cFunctor_scope.
Notation "F1 + F2" := (sumCF F1%CF F2%CF) : cFunctor_scope.
Notation "▶ F"  := (laterCF F%CF) (at level 20, right associativity) : cFunctor_scope.
Coercion constCF : ofeT >-> cFunctor.
