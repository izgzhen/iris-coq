From iris.algebra Require Export cmra.
From iris.base_logic Require Import base_logic.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.

Inductive excl (A : Type) :=
  | Excl : A → excl A
  | ExclBot : excl A.
Arguments Excl {_} _.
Arguments ExclBot {_}.

Notation excl' A := (option (excl A)).
Notation Excl' x := (Some (Excl x)).
Notation ExclBot' := (Some ExclBot).

Instance maybe_Excl {A} : Maybe (@Excl A) := λ x,
  match x with Excl a => Some a | _ => None end.

Section excl.
Context {A : ofeT}.
Implicit Types a b : A.
Implicit Types x y : excl A.

(* Cofe *)
Inductive excl_equiv : Equiv (excl A) :=
  | Excl_equiv a b : a ≡ b → Excl a ≡ Excl b
  | ExclBot_equiv : ExclBot ≡ ExclBot.
Existing Instance excl_equiv.
Inductive excl_dist : Dist (excl A) :=
  | Excl_dist a b n : a ≡{n}≡ b → Excl a ≡{n}≡ Excl b
  | ExclBot_dist n : ExclBot ≡{n}≡ ExclBot.
Existing Instance excl_dist.

Global Instance Excl_ne n : Proper (dist n ==> dist n) (@Excl A).
Proof. by constructor. Qed.
Global Instance Excl_proper : Proper ((≡) ==> (≡)) (@Excl A).
Proof. by constructor. Qed.
Global Instance Excl_inj : Inj (≡) (≡) (@Excl A).
Proof. by inversion_clear 1. Qed.
Global Instance Excl_dist_inj n : Inj (dist n) (dist n) (@Excl A).
Proof. by inversion_clear 1. Qed.

Definition excl_ofe_mixin : OfeMixin (excl A).
Proof.
  split.
  - intros x y; split; [by destruct 1; constructor; apply equiv_dist|].
    intros Hxy; feed inversion (Hxy 1); subst; constructor; apply equiv_dist.
    by intros n; feed inversion (Hxy n).
  - intros n; split.
    + by intros []; constructor.
    + by destruct 1; constructor.
    + destruct 1; inversion_clear 1; constructor; etrans; eauto.
  - by inversion_clear 1; constructor; apply dist_S.
Qed.
Canonical Structure exclC : ofeT := OfeT (excl A) excl_ofe_mixin.

Program Definition excl_chain (c : chain exclC) (a : A) : chain A :=
  {| chain_car n := match c n return _ with Excl y => y | _ => a end |}.
Next Obligation. intros c a n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
Definition excl_compl `{Cofe A} : Compl exclC := λ c,
  match c 0 with Excl a => Excl (compl (excl_chain c a)) | x => x end.
Global Program Instance excl_cofe `{Cofe A} : Cofe exclC :=
  {| compl := excl_compl |}.
Next Obligation.
  intros ? n c; rewrite /compl /excl_compl.
  feed inversion (chain_cauchy c 0 n); auto with omega.
  rewrite (conv_compl n (excl_chain c _)) /=. destruct (c n); naive_solver.
Qed.

Global Instance excl_discrete : Discrete A → Discrete exclC.
Proof. by inversion_clear 2; constructor; apply (timeless _). Qed.
Global Instance excl_leibniz : LeibnizEquiv A → LeibnizEquiv (excl A).
Proof. by destruct 2; f_equal; apply leibniz_equiv. Qed.

Global Instance Excl_timeless a : Timeless a → Timeless (Excl a).
Proof. by inversion_clear 2; constructor; apply (timeless _). Qed.
Global Instance ExclBot_timeless : Timeless (@ExclBot A).
Proof. by inversion_clear 1; constructor. Qed.

(* CMRA *)
Instance excl_valid : Valid (excl A) := λ x,
  match x with Excl _ => True | ExclBot => False end.
Instance excl_validN : ValidN (excl A) := λ n x,
  match x with Excl _ => True | ExclBot => False end.
Instance excl_pcore : PCore (excl A) := λ _, None.
Instance excl_op : Op (excl A) := λ x y, ExclBot.

Lemma excl_cmra_mixin : CMRAMixin (excl A).
Proof.
  split; try discriminate.
  - by intros n []; destruct 1; constructor.
  - by destruct 1; intros ?.
  - intros x; split. done. by move=> /(_ 0).
  - intros n [?|]; simpl; auto with lia.
  - by intros [?|] [?|] [?|]; constructor.
  - by intros [?|] [?|]; constructor.
  - by intros n [?|] [?|].
  - intros n x [?|] [?|] ?; inversion_clear 1; eauto.
Qed.
Canonical Structure exclR :=
  CMRAT (excl A) excl_ofe_mixin excl_cmra_mixin.

Global Instance excl_cmra_discrete : Discrete A → CMRADiscrete exclR.
Proof. split. apply _. by intros []. Qed.

(** Internalized properties *)
Lemma excl_equivI {M} (x y : excl A) :
  x ≡ y ⊣⊢ (match x, y with
            | Excl a, Excl b => a ≡ b
            | ExclBot, ExclBot => True
            | _, _ => False
            end : uPred M).
Proof.
  uPred.unseal. do 2 split. by destruct 1. by destruct x, y; try constructor.
Qed.
Lemma excl_validI {M} (x : excl A) :
  ✓ x ⊣⊢ (if x is ExclBot then False else True : uPred M).
Proof. uPred.unseal. by destruct x. Qed.

(** Exclusive *)
Global Instance excl_exclusive x : Exclusive x.
Proof. by destruct x; intros n []. Qed.

(** Option excl *)
Lemma excl_validN_inv_l n mx a : ✓{n} (Excl' a ⋅ mx) → mx = None.
Proof. by destruct mx. Qed.
Lemma excl_validN_inv_r n mx a : ✓{n} (mx ⋅ Excl' a) → mx = None.
Proof. by destruct mx. Qed.

Lemma Excl_includedN n a b  : Excl' a ≼{n} Excl' b → a ≡{n}≡ b.
Proof. by intros [[c|] Hb%(inj Some)]; inversion_clear Hb. Qed.
Lemma Excl_included a b : Excl' a ≼ Excl' b → a ≡ b.
Proof. by intros [[c|] Hb%(inj Some)]; inversion_clear Hb. Qed.
End excl.

Arguments exclC : clear implicits.
Arguments exclR : clear implicits.

(* Functor *)
Definition excl_map {A B} (f : A → B) (x : excl A) : excl B :=
  match x with Excl a => Excl (f a) | ExclBot => ExclBot end.
Lemma excl_map_id {A} (x : excl A) : excl_map id x = x.
Proof. by destruct x. Qed.
Lemma excl_map_compose {A B C} (f : A → B) (g : B → C) (x : excl A) :
  excl_map (g ∘ f) x = excl_map g (excl_map f x).
Proof. by destruct x. Qed.
Lemma excl_map_ext {A B : ofeT} (f g : A → B) x :
  (∀ x, f x ≡ g x) → excl_map f x ≡ excl_map g x.
Proof. by destruct x; constructor. Qed.
Instance excl_map_ne {A B : ofeT} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@excl_map A B).
Proof. by intros f f' Hf; destruct 1; constructor; apply Hf. Qed.
Instance excl_map_cmra_monotone {A B : ofeT} (f : A → B) :
  (∀ n, Proper (dist n ==> dist n) f) → CMRAMonotone (excl_map f).
Proof.
  split; try apply _.
  - by intros n [a|].
  - intros x y [z Hy]; exists (excl_map f z); apply equiv_dist=> n.
    move: Hy=> /equiv_dist /(_ n) ->; by destruct x, z.
Qed.
Definition exclC_map {A B} (f : A -n> B) : exclC A -n> exclC B :=
  CofeMor (excl_map f).
Instance exclC_map_ne A B n : Proper (dist n ==> dist n) (@exclC_map A B).
Proof. by intros f f' Hf []; constructor; apply Hf. Qed.

Program Definition exclRF (F : cFunctor) : rFunctor := {|
  rFunctor_car A B := (exclR (cFunctor_car F A B));
  rFunctor_map A1 A2 B1 B2 fg := exclC_map (cFunctor_map F fg)
|}.
Next Obligation.
  intros F A1 A2 B1 B2 n x1 x2 ??. by apply exclC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros F A B x; simpl. rewrite -{2}(excl_map_id x).
  apply excl_map_ext=>y. by rewrite cFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x; simpl. rewrite -excl_map_compose.
  apply excl_map_ext=>y; apply cFunctor_compose.
Qed.

Instance exclRF_contractive F :
  cFunctorContractive F → rFunctorContractive (exclRF F).
Proof.
  intros A1 A2 B1 B2 n x1 x2 ??. by apply exclC_map_ne, cFunctor_contractive.
Qed.
