Require Export modures.cmra.

Structure iFunctor := IFunctor {
  ifunctor_car :> cofeT → cmraT;
  ifunctor_empty A : Empty (ifunctor_car A);
  ifunctor_identity A : CMRAIdentity (ifunctor_car A);
  ifunctor_map {A B} (f : A -n> B) : ifunctor_car A -n> ifunctor_car B;
  ifunctor_map_ne {A B} n : Proper (dist n ==> dist n) (@ifunctor_map A B);
  ifunctor_map_id {A : cofeT} (x : ifunctor_car A) : ifunctor_map cid x ≡ x;
  ifunctor_map_compose {A B C} (f : A -n> B) (g : B -n> C) x :
    ifunctor_map (g ◎ f) x ≡ ifunctor_map g (ifunctor_map f x);
  ifunctor_map_mono {A B} (f : A -n> B) : CMRAMonotone (ifunctor_map f)
}.
Existing Instances ifunctor_empty ifunctor_identity.
Existing Instances ifunctor_map_ne ifunctor_map_mono.

Lemma ifunctor_map_ext (Σ : iFunctor) {A B} (f g : A -n> B) m :
  (∀ x, f x ≡ g x) → ifunctor_map Σ f m ≡ ifunctor_map Σ g m.
Proof.
  by intros; apply equiv_dist=> n; apply ifunctor_map_ne=> ?; apply equiv_dist.
Qed.

Program Definition iFunctor_const (icmra : cmraT) {icmra_empty : Empty icmra}
    {icmra_identity : CMRAIdentity icmra} : iFunctor :=
  {| ifunctor_car A := icmra; ifunctor_map A B f := cid |}.
Solve Obligations with done.