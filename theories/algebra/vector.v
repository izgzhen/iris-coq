From iris.prelude Require Export vector.
From iris.algebra Require Export ofe.
From iris.algebra Require Import list.
Set Default Proof Using "Type".

Section ofe.
  Context {A : ofeT}.

  Instance vec_equiv m : Equiv (vec A m) := equiv (A:=list A).
  Instance vec_dist m : Dist (vec A m) := dist (A:=list A).

  Definition vec_ofe_mixin m : OfeMixin (vec A m).
  Proof.
    split.
    - intros x y. apply (equiv_dist (A:=listC A)).
    - unfold dist, vec_dist. split.
        by intros ?. by intros ??. by intros ?????; etrans.
    - intros. by apply (dist_S (A:=listC A)).
  Qed.
  Canonical Structure vecC m : ofeT := OfeT (vec A m) (vec_ofe_mixin m).

  Global Instance vnil_timeless : Timeless (@vnil A).
  Proof. intros v _. by inv_vec v. Qed.
  Global Instance vcons_timeless n x (v : vec A n) :
    Timeless x → Timeless v → Timeless (x ::: v).
  Proof.
    intros ?? v' ?. inv_vec v'=>x' v'. inversion_clear 1.
    constructor. by apply timeless. change (v ≡ v'). by apply timeless.
  Qed.
  Global Instance vec_discrete_cofe m : Discrete A → Discrete (vecC m).
  Proof. intros ? v. induction v; apply _. Qed.
End ofe.

Arguments vecC : clear implicits.
Typeclasses Opaque vec_dist.

Section proper.
  Context {A : ofeT}.

  Global Instance vcons_ne n :
    Proper (dist n ==> forall_relation (λ _, dist n ==> dist n)) (@vcons A).
  Proof. by constructor. Qed.
  Global Instance vcons_proper :
    Proper (equiv ==> forall_relation (λ _, equiv ==> equiv)) (@vcons A).
  Proof. by constructor. Qed.

  Global Instance vlookup_ne n m :
    Proper (dist n ==> eq ==> dist n) (@Vector.nth A m).
  Proof.
    intros v. induction v as [|x m v IH]; intros v'; inv_vec v'.
    - intros _ x. inversion x.
    - intros x' v' EQ i ? <-. inversion_clear EQ. inv_fin i; first done.
      intros i. by apply IH.
  Qed.
  Global Instance vlookup_proper m :
    Proper (equiv ==> eq ==> equiv) (@Vector.nth A m).
  Proof.
    intros ??????. apply equiv_dist=>?. subst. f_equiv. by apply equiv_dist.
  Qed.

  Global Instance vec_to_list_ne n m :
    Proper (dist n ==> dist n) (@vec_to_list A m).
  Proof. intros ?? H. apply H. Qed.
  Global Instance vec_to_list_proper m :
    Proper (equiv ==> equiv) (@vec_to_list A m).
  Proof. intros ?? H. apply H. Qed.
End proper.

Section cofe.
  Context `{Cofe A}.

  Global Program Instance list_cofe m : Cofe (vecC A m) :=
    {| compl c :=
         eq_rect _ (vec A) (list_to_vec (compl (chain_map vec_to_list c))) _ _ |}.
  Next Obligation.
    intros. by rewrite (conv_compl 0) vec_to_list_length.
  Qed.
  Next Obligation.
    simpl. intros m n c. unfold dist, ofe_dist, vecC, vec_dist.
    destruct (list_cofe_obligation_1 m c).
    by rewrite /= vec_to_list_of_list conv_compl.
  Qed.
End cofe.

(** Functor *)
Definition vec_map {A B : ofeT} m (f : A → B) : vecC A m → vecC B m :=
  @vmap A B f m.
Lemma vec_map_ext_ne {A B : ofeT} m (f g : A → B) (v : vec A m) n :
  (∀ x, f x ≡{n}≡ g x) → vec_map m f v ≡{n}≡ vec_map m g v.
Proof.
  intros Hf. eapply (list_fmap_ext_ne f g v) in Hf.
  by rewrite -!vec_to_list_map in Hf.
Qed.
Instance vec_map_ne {A B : ofeT} m f n :
  Proper (dist n ==> dist n) f →
  Proper (dist n ==> dist n) (@vec_map A B m f).
Proof.
  intros ??? H. eapply list_fmap_ne in H; last done.
  by rewrite -!vec_to_list_map in H.
Qed.
Definition vecC_map {A B : ofeT} m (f : A -n> B) : vecC A m -n> vecC B m :=
  CofeMor (vec_map m f).
Instance vecC_map_ne {A A'} m n :
  Proper (dist n ==> dist n) (@vecC_map A A' m).
Proof. intros f g ? v. by apply vec_map_ext_ne. Qed.

Program Definition vecCF (F : cFunctor) m : cFunctor := {|
  cFunctor_car A B := vecC (cFunctor_car F A B) m;
  cFunctor_map A1 A2 B1 B2 fg := vecC_map m (cFunctor_map F fg)
|}.
Next Obligation.
  intros F A1 A2 B1 B2 n m f g Hfg. by apply vecC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros F m A B l.
  change (vec_to_list (vec_map m (cFunctor_map F (cid, cid)) l) ≡ l).
  rewrite vec_to_list_map. apply listCF.
Qed.
Next Obligation.
  intros F m A1 A2 A3 B1 B2 B3 f g f' g' l.
  change (vec_to_list (vec_map m (cFunctor_map F (f ◎ g, g' ◎ f')) l)
    ≡ vec_map m (cFunctor_map F (g, g')) (vec_map m (cFunctor_map F (f, f')) l)).
  rewrite !vec_to_list_map. by apply (cFunctor_compose (listCF F)  f g f' g').
Qed.

Instance vecCF_contractive F m :
  cFunctorContractive F → cFunctorContractive (vecCF F m).
Proof.
  by intros ?? A1 A2 B1 B2 n ???; apply vecC_map_ne; first apply cFunctor_contractive.
Qed.
