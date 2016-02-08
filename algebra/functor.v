Require Export algebra.cmra.

(** * Functors from COFE to CMRA *)
(* TODO RJ: Maybe find a better name for this? It is not PL-specific any more. *)
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
