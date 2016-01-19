Require Export modures.cmra iris.language.

Set Bullet Behavior "Strict Subproofs".

Record iParam := IParam {
  iexpr : Type;
  ival : Type;
  istate : Type;
  ilanguage : Language iexpr ival istate;
  icmra : cofeT → cmraT;
  icmra_empty A : Empty (icmra A);
  icmra_empty_spec A : RAIdentity (icmra A);
  icmra_map {A B} (f : A -n> B) : icmra A -n> icmra B;
  icmra_map_ne {A B} n : Proper (dist n ==> dist n) (@icmra_map A B);
  icmra_map_id {A : cofeT} (x : icmra A) : icmra_map cid x ≡ x;
  icmra_map_compose {A B C} (f : A -n> B) (g : B -n> C) x :
    icmra_map (g ◎ f) x ≡ icmra_map g (icmra_map f x);
  icmra_map_mono {A B} (f : A -n> B) : CMRAMonotone (icmra_map f)
}.
Arguments IParam {_ _ _} _ _ {_ _} _ {_ _ _ _}.
Existing Instances ilanguage.
Existing Instances icmra_empty icmra_empty_spec icmra_map_ne icmra_map_mono.

Lemma icmra_map_ext (Σ : iParam) {A B} (f g : A -n> B) m :
  (∀ x, f x ≡ g x) → icmra_map Σ f m ≡ icmra_map Σ g m.
Proof.
  by intros ?; apply equiv_dist=> n; apply icmra_map_ne=> ?; apply equiv_dist.
Qed.

Definition IParamConst {iexpr ival istate : Type}
           (ilanguage : Language iexpr ival istate)
           (icmra : cmraT) {icmra_empty : Empty icmra}
           {icmra_empty_spec : RAIdentity icmra}:
  iParam.
eapply (IParam ilanguage (fun _ => icmra) (fun _ _ _ => cid)).
Unshelve.
- by intros.
- by intros.
Defined.

Canonical Structure istateC Σ := leibnizC (istate Σ).
