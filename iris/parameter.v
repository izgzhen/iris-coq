Require Export modures.cmra iris.language.

Record iParam := IParam {
  iexpr : Type;
  ival : Type;
  istate : Type;
  ilanguage : Language iexpr ival istate;
  icmra : cofeT → cmraT;
  icmra_empty A : Empty (icmra A);
  icmra_identity A : CMRAIdentity (icmra A);
  icmra_map {A B} (f : A -n> B) : icmra A -n> icmra B;
  icmra_map_ne {A B} n : Proper (dist n ==> dist n) (@icmra_map A B);
  icmra_map_id {A : cofeT} (x : icmra A) : icmra_map cid x ≡ x;
  icmra_map_compose {A B C} (f : A -n> B) (g : B -n> C) x :
    icmra_map (g ◎ f) x ≡ icmra_map g (icmra_map f x);
  icmra_map_mono {A B} (f : A -n> B) : CMRAMonotone (icmra_map f)
}.
Existing Instances ilanguage.
Existing Instances icmra_empty icmra_identity.
Existing Instances icmra_map_ne icmra_map_mono.
Canonical Structure istateC Σ := leibnizC (istate Σ).

Lemma icmra_map_ext (Σ : iParam) {A B} (f g : A -n> B) m :
  (∀ x, f x ≡ g x) → icmra_map Σ f m ≡ icmra_map Σ g m.
Proof.
  by intros ?; apply equiv_dist=> n; apply icmra_map_ne=> ?; apply equiv_dist.
Qed.

Program Definition iParam_const {iexpr ival istate : Type}
  (ilanguage : Language iexpr ival istate)
  (icmra : cmraT)
  {icmra_empty : Empty icmra} {icmra_identity : CMRAIdentity icmra} : iParam :=
{|
  iexpr := iexpr; ival := ival; istate := istate;
  icmra A := icmra; icmra_map A B f := cid
|}.
Solve Obligations with done.