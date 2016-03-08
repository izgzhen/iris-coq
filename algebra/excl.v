From algebra Require Export cmra.
From algebra Require Import upred.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.

Inductive excl (A : Type) :=
  | Excl : A → excl A
  | ExclUnit : excl A
  | ExclBot : excl A.
Arguments Excl {_} _.
Arguments ExclUnit {_}.
Arguments ExclBot {_}.
Instance maybe_Excl {A} : Maybe (@Excl A) := λ x,
  match x with Excl a => Some a | _ => None end.

Section excl.
Context {A : cofeT}.
Implicit Types a b : A.
Implicit Types x y : excl A.

(* Cofe *)
Inductive excl_equiv : Equiv (excl A) :=
  | Excl_equiv a b : a ≡ b → Excl a ≡ Excl b
  | ExclUnit_equiv : ExclUnit ≡ ExclUnit
  | ExclBot_equiv : ExclBot ≡ ExclBot.
Existing Instance excl_equiv.
Inductive excl_dist : Dist (excl A) :=
  | Excl_dist a b n : a ≡{n}≡ b → Excl a ≡{n}≡ Excl b
  | ExclUnit_dist n : ExclUnit ≡{n}≡ ExclUnit
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

Program Definition excl_chain
    (c : chain (excl A)) (a : A) (H : maybe Excl (c 0) = Some a) : chain A :=
  {| chain_car n := match c n return _ with Excl y => y | _ => a end |}.
Next Obligation.
  intros c a ? n i ?; simpl.
  destruct (c 0) eqn:?; simplify_eq/=.
  by feed inversion (chain_cauchy c n i).
Qed.
Instance excl_compl : Compl (excl A) := λ c,
  match Some_dec (maybe Excl (c 0)) with
  | inleft (exist a H) => Excl (compl (excl_chain c a H)) | inright _ => c 0
  end.
Definition excl_cofe_mixin : CofeMixin (excl A).
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
  - intros n c; unfold compl, excl_compl.
    destruct (Some_dec (maybe Excl (c 0))) as [[a Ha]|].
    { assert (c 0 = Excl a) by (by destruct (c 0); simplify_eq/=).
      assert (∃ b, c n = Excl b) as [b Hb].
      { feed inversion (chain_cauchy c 0 n); eauto with lia congruence. }
      rewrite Hb; constructor.
      by rewrite (conv_compl n (excl_chain c a Ha)) /= Hb. }
    feed inversion (chain_cauchy c 0 n); first lia;
       constructor; destruct (c 0); simplify_eq/=.
Qed.
Canonical Structure exclC : cofeT := CofeT excl_cofe_mixin.
Global Instance excl_discrete : Discrete A → Discrete exclC.
Proof. by inversion_clear 2; constructor; apply (timeless _). Qed.
Global Instance excl_leibniz : LeibnizEquiv A → LeibnizEquiv (excl A).
Proof. by destruct 2; f_equal; apply leibniz_equiv. Qed.

Global Instance Excl_timeless a : Timeless a → Timeless (Excl a).
Proof. by inversion_clear 2; constructor; apply (timeless _). Qed.
Global Instance ExclUnit_timeless : Timeless (@ExclUnit A).
Proof. by inversion_clear 1; constructor. Qed.
Global Instance ExclBot_timeless : Timeless (@ExclBot A).
Proof. by inversion_clear 1; constructor. Qed.

(* CMRA *)
Instance excl_valid : Valid (excl A) := λ x,
  match x with Excl _ | ExclUnit => True | ExclBot => False end.
Instance excl_validN : ValidN (excl A) := λ n x,
  match x with Excl _ | ExclUnit => True | ExclBot => False end.
Global Instance excl_empty : Empty (excl A) := ExclUnit.
Instance excl_core : Core (excl A) := λ _, ∅.
Instance excl_op : Op (excl A) := λ x y,
  match x, y with
  | Excl a, ExclUnit | ExclUnit, Excl a => Excl a
  | ExclUnit, ExclUnit => ExclUnit
  | _, _=> ExclBot
  end.
Instance excl_div : Div (excl A) := λ x y,
  match x, y with
  | _, ExclUnit => x
  | Excl _, Excl _ => ExclUnit
  | _, _ => ExclBot
  end.
Definition excl_cmra_mixin : CMRAMixin (excl A).
Proof.
  split.
  - by intros n []; destruct 1; constructor.
  - constructor.
  - by destruct 1; intros ?.
  - by destruct 1; inversion_clear 1; constructor.
  - intros x; split. done. by move=> /(_ 0).
  - intros n [?| |]; simpl; auto with lia.
  - by intros [?| |] [?| |] [?| |]; constructor.
  - by intros [?| |] [?| |]; constructor.
  - by intros [?| |]; constructor.
  - constructor.
  - by intros [?| |] [?| |]; exists ∅.
  - by intros n [?| |] [?| |].
  - by intros [?| |] [?| |] [[?| |] Hz]; inversion_clear Hz; constructor.
  - intros n x y1 y2 ? Hx.
    by exists match y1, y2 with
      | Excl a1, Excl a2 => (Excl a1, Excl a2)
      | ExclBot, _ => (ExclBot, y2) | _, ExclBot => (y1, ExclBot)
      | ExclUnit, _ => (ExclUnit, x) | _, ExclUnit => (x, ExclUnit)
      end; destruct y1, y2; inversion_clear Hx; repeat constructor.
Qed.
Canonical Structure exclR : cmraT := CMRAT excl_cofe_mixin excl_cmra_mixin.
Global Instance excl_cmra_unit : CMRAUnit exclR.
Proof. split. done. by intros []. apply _. Qed.
Global Instance excl_cmra_discrete : Discrete A → CMRADiscrete exclR.
Proof. split. apply _. by intros []. Qed.

Lemma excl_validN_inv_l n x a : ✓{n} (Excl a ⋅ x) → x = ∅.
Proof. by destruct x. Qed.
Lemma excl_validN_inv_r n x a : ✓{n} (x ⋅ Excl a) → x = ∅.
Proof. by destruct x. Qed.
Lemma Excl_includedN n a x : ✓{n} x → Excl a ≼{n} x ↔ x ≡{n}≡ Excl a.
Proof.
  intros Hvalid; split; [|by intros ->].
  intros [z ?]; cofe_subst. by rewrite (excl_validN_inv_l n z a).
Qed.

(** Internalized properties *)
Lemma excl_equivI {M} (x y : excl A) :
  (x ≡ y)%I ≡ (match x, y with
               | Excl a, Excl b => a ≡ b
               | ExclUnit, ExclUnit | ExclBot, ExclBot => True
               | _, _ => False
               end : uPred M)%I.
Proof.
  uPred.unseal. do 2 split. by destruct 1. by destruct x, y; try constructor.
Qed.
Lemma excl_validI {M} (x : excl A) :
  (✓ x)%I ≡ (if x is ExclBot then False else True : uPred M)%I.
Proof. uPred.unseal. by destruct x. Qed.

(** ** Local updates *)
Global Instance excl_local_update y :
  LocalUpdate (λ x, if x is Excl _ then ✓ y else False) (λ _, y).
Proof. split. apply _. by destruct y; intros n [a| |] [b'| |]. Qed.

(** Updates *)
Lemma excl_update a y : ✓ y → Excl a ~~> y.
Proof. destruct y; by intros ?? [?| |]. Qed.
Lemma excl_updateP (P : excl A → Prop) a y : ✓ y → P y → Excl a ~~>: P.
Proof. intros ?? n z ?; exists y. by destruct y, z as [?| |]. Qed.
End excl.

Arguments exclC : clear implicits.
Arguments exclR : clear implicits.

(* Functor *)
Definition excl_map {A B} (f : A → B) (x : excl A) : excl B :=
  match x with
  | Excl a => Excl (f a) | ExclUnit => ExclUnit | ExclBot => ExclBot
  end.
Lemma excl_map_id {A} (x : excl A) : excl_map id x = x.
Proof. by destruct x. Qed.
Lemma excl_map_compose {A B C} (f : A → B) (g : B → C) (x : excl A) :
  excl_map (g ∘ f) x = excl_map g (excl_map f x).
Proof. by destruct x. Qed.
Lemma excl_map_ext {A B : cofeT} (f g : A → B) x :
  (∀ x, f x ≡ g x) → excl_map f x ≡ excl_map g x.
Proof. by destruct x; constructor. Qed.
Instance excl_map_cmra_ne {A B : cofeT} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@excl_map A B).
Proof. by intros f f' Hf; destruct 1; constructor; apply Hf. Qed.
Instance excl_map_cmra_monotone {A B : cofeT} (f : A → B) :
  (∀ n, Proper (dist n ==> dist n) f) → CMRAMonotone (excl_map f).
Proof.
  split; try apply _.
  - by intros n [a| |].
  - intros x y [z Hy]; exists (excl_map f z); apply equiv_dist=> n.
    move: Hy=> /equiv_dist /(_ n) ->; by destruct x, z.
Qed.
Definition exclC_map {A B} (f : A -n> B) : exclC A -n> exclC B :=
  CofeMor (excl_map f).
Instance exclC_map_ne A B n : Proper (dist n ==> dist n) (@exclC_map A B).
Proof. by intros f f' Hf []; constructor; apply Hf. Qed.

Program Definition exclRF (F : cFunctor) : rFunctor := {|
  rFunctor_car A B := exclR (cFunctor_car F A B);
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
