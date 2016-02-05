Require Export algebra.cmra.
Require Import algebra.agree algebra.excl algebra.auth.
Require Import algebra.option algebra.fin_maps.

(** * Functors from COFE to CMRA *)
(* The Iris program logic is parametrized by a functor from the category of
COFEs to the category of CMRAs, which is instantiated with [laterC iProp]. The
[laterC iProp] can be used to construct impredicate CMRAs, such as the stored
propositions using the agreement CMRA. *)
Structure iFunctor := IFunctor {
  ifunctor_car :> cofeT → cmraT;
  ifunctor_map {A B} (f : A -n> B) : ifunctor_car A -n> ifunctor_car B;
  ifunctor_map_ne {A B} n : Proper (dist n ==> dist n) (@ifunctor_map A B);
  ifunctor_map_id {A : cofeT} (x : ifunctor_car A) : ifunctor_map cid x ≡ x;
  ifunctor_map_compose {A B C} (f : A -n> B) (g : B -n> C) x :
    ifunctor_map (g ◎ f) x ≡ ifunctor_map g (ifunctor_map f x);
  ifunctor_map_mono {A B} (f : A -n> B) : CMRAMonotone (ifunctor_map f)
}.
Existing Instances ifunctor_map_ne ifunctor_map_mono.

Lemma ifunctor_map_ext (Σ : iFunctor) {A B} (f g : A -n> B) m :
  (∀ x, f x ≡ g x) → ifunctor_map Σ f m ≡ ifunctor_map Σ g m.
Proof. by intros; apply (ne_proper (@ifunctor_map Σ A B)). Qed.

(** * Functor combinators *)
(** We create a functor combinators for all CMRAs in the algebra directory.
These combinators can be used to conveniently construct the global CMRA of
the Iris program logic. Note that we have explicitly built in functor
composition into these combinators, instead of having a notion of a functor
from the category of CMRAs to the category of CMRAs which we can compose. This
way we can convenient deal with (indexed) products in a uniform way. *)
Program Definition constF (B : cmraT) : iFunctor :=
  {| ifunctor_car A := B; ifunctor_map A1 A2 f := cid |}.
Solve Obligations with done.

Program Definition prodF (Σ1 Σ2 : iFunctor) : iFunctor := {|
  ifunctor_car A := prodRA (Σ1 A) (Σ2 A);
  ifunctor_map A B f := prodC_map (ifunctor_map Σ1 f) (ifunctor_map Σ2 f)
|}.
Next Obligation.
  by intros Σ1 Σ2 A B n f g Hfg; apply prodC_map_ne; apply ifunctor_map_ne.
Qed.
Next Obligation. by intros Σ1 Σ2 A [??]; rewrite /= !ifunctor_map_id. Qed.
Next Obligation.
  by intros Σ1 Σ2 A B C f g [??]; rewrite /= !ifunctor_map_compose.
Qed.

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

Program Definition agreeF : iFunctor :=
  {| ifunctor_car := agreeRA; ifunctor_map := @agreeC_map |}.
Solve Obligations with done.

Program Definition exclF : iFunctor :=
  {| ifunctor_car := exclRA; ifunctor_map := @exclC_map |}.
Next Obligation. by intros A x; rewrite /= excl_map_id. Qed.
Next Obligation. by intros A B C f g x; rewrite /= excl_map_compose. Qed.

Program Definition authF (Σ : iFunctor) : iFunctor := {|
  ifunctor_car := authRA ∘ Σ; ifunctor_map A B := authC_map ∘ ifunctor_map Σ
|}.
Next Obligation.
  by intros Σ A B n f g Hfg; apply authC_map_ne, ifunctor_map_ne.
Qed.
Next Obligation.
  intros Σ A x. rewrite /= -{2}(auth_map_id x).
  apply auth_map_ext=>y; apply ifunctor_map_id.
Qed.
Next Obligation.
  intros Σ A B C f g x. rewrite /= -auth_map_compose.
  apply auth_map_ext=>y; apply ifunctor_map_compose.
Qed.

Program Definition optionF (Σ : iFunctor) : iFunctor := {|
  ifunctor_car := optionRA ∘ Σ; ifunctor_map A B := optionC_map ∘ ifunctor_map Σ
|}.
Next Obligation.
  by intros Σ A B n f g Hfg; apply optionC_map_ne, ifunctor_map_ne.
Qed.
Next Obligation.
  intros Σ A x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_setoid_ext=>y; apply ifunctor_map_id.
Qed.
Next Obligation.
  intros Σ A B C f g x. rewrite /= -option_fmap_compose.
  apply option_fmap_setoid_ext=>y; apply ifunctor_map_compose.
Qed.

Program Definition mapF K `{Countable K} (Σ : iFunctor) : iFunctor := {|
  ifunctor_car := mapRA K ∘ Σ; ifunctor_map A B := mapC_map ∘ ifunctor_map Σ
|}.
Next Obligation.
  by intros K ?? Σ A B n f g Hfg; apply mapC_map_ne, ifunctor_map_ne.
Qed.
Next Obligation.
  intros K ?? Σ A x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_setoid_ext=> ? y _; apply ifunctor_map_id.
Qed.
Next Obligation.
  intros K ?? Σ A B C f g x. rewrite /= -map_fmap_compose.
  apply map_fmap_setoid_ext=> ? y _; apply ifunctor_map_compose.
Qed.
