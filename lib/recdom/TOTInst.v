Require Import CSetoid.

Require Import Relation_Definitions.

Require Import MetricCore.

Require Import MetricRec.

Record Object : Type :=
  {
    obj :> nat -> Type;
    obj_eq : forall n, relation (obj n);
    obj_eq_equiv : forall n, Equivalence (obj_eq n);
    restr : forall n, obj (S n) -> obj n;
    restr_proper : forall n, Proper (obj_eq (S n) ==> obj_eq n) (restr n)
  }.

Infix "≡" := (obj_eq _ _) (at level 70, no associativity).

Program Instance Object_Equiv (X : Object) (n : nat) : Equivalence (obj_eq X n) := obj_eq_equiv X n.

Program Instance Object_Setoid (X : Object) (n : nat) : Setoid (X n) :=
  {| equiv := obj_eq X n |}.

Record Morphism (X Y : Object) : Type :=
  {
    morph :> forall n, X n -> Y n;
    morph_proper : forall n, Proper (obj_eq _ _ ==> obj_eq _ _) (morph n);
    morph_natural : forall n, forall (x : X (S n)), restr _ _ (morph _ x) ≡ morph _ (restr _ _ x)
  }.

Infix "↝" := Morphism (at level 71, right associativity).

Definition Morphism_Eq (X Y : Object): relation (X ↝ Y).
  intros α β.
  destruct α as [f _ _] ; destruct β as [g _ _].
  exact (forall n, forall x, f n x ≡ g n x).
Defined.

Program Instance Morphism_Eq_Equivalence {X Y : Object}: Setoid (X ↝ Y) :=
  {| equiv := (Morphism_Eq X Y);
     setoid_equiv := Build_Equivalence _ _ _ _ _
  |}.
Next Obligation.
  intros [α αp αn] n x; simpl ; intuition.
Defined.
Next Obligation.
  intros [α αp αn] [β βp βn] Heq n; simpl ; symmetry ; auto.
Defined.
Next Obligation.
  intros [α αp αn] [β βp βn] [γ γp γn] Heq1 Heq2 n; etransitivity ; auto.
Defined.

Definition morph_dist (X Y : Object): nat -> X ↝ Y -> _ :=
  fun n α β => forall k, k < n -> forall (x : X k), α k x ≡ β k x.

Program Instance morph_metric {X Y : Object}: @metric (X ↝ Y) (@Morphism_Eq_Equivalence X Y) :=
  {| dist := morph_dist X Y |}.
Next Obligation.
  intros α β Hαβ γ δ Hγδ ; split ; intro Heq ;
  destruct α as [α αp αn] ; destruct β as [β βp βn] ; destruct γ as [γ γp γn] ; destruct δ as [δ δp δn] ;
  intros k Hlt x ; simpl ;
  assert (Hmid := Heq k Hlt x); assert (Hleft := Hαβ k x) ; assert (Hright := Hγδ k x) ; simpl in * ;
  destruct (obj_eq_equiv Y k) as [r s t] ; eauto.
Defined.
Next Obligation.
  destruct x as [α αp αn] ; destruct y as [β βp βn].
  split ; intros H n.
  - intros x ; assert (HH := (H (S n) n (le_n _) x)) ; auto.
  - intros m Hleq x ; apply H.
Defined.
Next Obligation.
  intros α β Hαβ k Hleq x.
  assert (Hn := Hαβ k Hleq x). 
  symmetry ; auto.
Defined.
Next Obligation.
  intros α β γ Hαβ Hβγ k Hleq x.
  assert (H1 := Hαβ k Hleq x).
  assert (H2 := Hβγ k Hleq x).
  etransitivity ; auto.
Defined.
Next Obligation.
  intros k Hleq ; apply H ; auto.
Defined.
Next Obligation.
  intros k Hq ; inversion Hq.
Defined.

Program Instance morph_metric_compl {X Y : Object}: @cmetric (X ↝ Y) _ (@morph_metric X Y) :=
  {| compl := fun σ Hcauchy =>
                {| morph := fun n x => σ (S (S n)) n x; (* This works because a Cauchy chain requires very
                                                           strong convergence in this formalization *) 
                   morph_proper := _;
                   morph_natural := fun n x => _
                |}
  |}.
Next Obligation.
  destruct (σ (S (S n))) as [α αp αr] ; apply αp.
Defined.
Next Obligation.
  remember (σ (S (S n))) as σn ; destruct σn as [α αp αr] ; simpl.  
  remember (σ (S (S (S n)))) as σSn ; destruct σSn as [β βp βr] ; simpl.
  destruct (obj_eq_equiv Y n) as [r s t].
  assert ((β n (restr X n x)) ≡ restr Y n (α (S n) x)).
  assert (α (S n) x ≡ β (S n) x).
  assert (forall y, α y = (σ (S (S n))) y) as Heqασ' by (intro y; rewrite <- Heqσn ; auto).
  rewrite Heqασ'.
  assert (forall y, β y = (σ (S (S (S n)))) y) as HeqαSσ' by (intro y; rewrite <- HeqσSn ; auto).
  rewrite HeqαSσ'.
  apply (Hcauchy _ _ _ _) ; auto.
  assert (HH := restr_proper Y n _ _ H) ; eauto.
  eapply (t _ _ _ (βr _ _) (t _ _ _ H (αr _ _))).
Defined.
Next Obligation.
  intros n.
  exists (S n) ; intros i Hi k Hlt x ; simpl.
  assert (S (S k) <= i) as Hleq by omega.
  assert (k < S (S k)) as Hlt' by omega.
  exact (σc (S (S k)) (S (S k)) i (le_n _) Hleq k Hlt' _).
Defined.

Program Definition comp {X Y Z : Object} (α : X ↝ Y) (β : Y ↝ Z): (X ↝ Z) :=
  {| morph := fun n x => β _ (α _ x);
     morph_proper := fun n => _;
     morph_natural := fun n x => _
  |}.
Next Obligation.
  destruct α as [α αp αr] ; destruct β as [β βp βr].
  intros x x' Heq ; apply βp ; apply αp ; auto.
Defined.
Next Obligation.  
  destruct α as [α αp αr] ; destruct β as [β βp βr] ; simpl.
  etransitivity ; auto.
  apply βp ; auto.
Defined.

Program Instance comp_proper {X Y Z : Object}: Proper (Morphism_Eq X Y ==> Morphism_Eq Y Z ==> Morphism_Eq X Z) comp.
Next Obligation.
  intros α β Heqαβ γ δ Heqγδ n x.
  destruct γ as [γ γp γr] ; destruct α as [α αp αr] ;
  destruct β as [β βp βr] ; destruct δ as [δ δp δr] ; simpl in *.
  etransitivity.
  - apply (γp n _ _ (Heqαβ n x)).
  - apply (Heqγδ _ _).
Defined.

Program Definition comp_metric_morph (X Y Z : Object): (X ↝ Y) -n> (Y ↝ Z) -n> (X ↝ Z) :=
  {| met_morph := {| CSetoid.morph := fun α => {| met_morph := {| CSetoid.morph := comp α ;
                                                                  morph_resp := _
                                                               |};
                                                  met_morph_nonexp := _
                                               |};
                     morph_resp := _
                  |};
     met_morph_nonexp := fun n α α' Hαα' => _
  |}.
Next Obligation.
  apply comp_proper, Morphism_Eq_Equivalence.
Defined.
Next Obligation.
  intros β γ Hβγ k Hlt x ; simpl ; auto.
Defined.
Next Obligation.
  intros α β Hαβ γ n x.
  destruct γ as [γ γp γr] ; simpl ; apply γp.
  destruct α as [α αp αr] ; destruct β as [β βp βr] ; auto.
Defined.
Next Obligation.
  intros k Hlt y ; simpl.
  destruct x as [β βp βr] ; apply βp ; auto.
Defined.

Program Definition hom_cmtyp (X Y : Object): cmtyp :=
  {| cmm := {| mtyp := {| eqtyp := X ↝ Y;
                          eqtype := Morphism_Eq_Equivalence
                       |};
               mmetr := morph_metric
            |};
     iscm := _
  |}.

Instance hom_BC_morph : BC_morph Object := hom_cmtyp.

(* Terminal object *)
Program Instance One : BC_term Object :=
  {| tto :=
       {| obj := fun n => unit;
          obj_eq := fun n => @eq unit
       |}
  |}.
Next Obligation.
  intuition.
Defined.

Program Instance morph_One : BC_terminal Object :=
  fun X => {| morph := fun n x => tt |}.
Next Obligation.
  intro ; auto. 
Defined.

Program Instance morph_Comp : BC_comp Object :=
  fun X Y Z => mkUMorph (mkMorph (fun α => mkUMorph (mkMorph (fun β => comp β α) _) _) _) _.
Next Obligation.
  intros β γ Heqβγ n x.
  destruct γ as [γ γp γr] ; destruct α as [α αp αr] ;
  destruct β as [β βp βr] ; simpl ; apply αp ; auto.
Defined.
Next Obligation.
  intros β γ Heqβγ k Hlt x ; simpl.
  destruct γ as [γ γp γr] ; destruct α as [α αp αr] ;
  destruct β as [β βp βr] ; simpl ; apply αp ; auto.
Defined.
Next Obligation.
  intros α α' Heqαα' β n x.
  destruct α' as [α' α'p α'r] ; destruct α as [α αp αr] ;
  destruct β as [β βp βr] ; simpl ; auto.
Defined.
Next Obligation.
  intros β γ Heqβγ δ k Hlt x ; simpl.
  destruct γ as [γ γp γr] ; destruct δ as [δ δp δr] ;
  destruct β as [β βp βr] ; simpl ; auto.
Defined.

Program Instance morph_id : BC_id Object :=
  fun X => {| morph := fun n x => x |}.
Next Obligation.
  intros x x' ; auto.
Defined.
Next Obligation.
  reflexivity.
Defined.

Program Instance TOT : BaseCat Object :=
  {| tcomp_assoc := fun X Y Z W => _;
     tid_left := fun X Y α => _;
     tid_right := fun X Y α => _;
     tto_term_unique := fun X α β => _ |}.
Next Obligation.
  reflexivity.
Defined.
Next Obligation.
  destruct α as [α αp αr] ; simpl ;  reflexivity. 
Defined.
Next Obligation.
  destruct α as [α αp αr] ; simpl ; reflexivity.
Defined.
Next Obligation.
  destruct α as [α αp αr] ; destruct β as [β βp βr] ; intros n x.
  destruct (α n x) ; destruct (β n x) ; reflexivity.
Defined.

Module TOTMcat <: MCat.
  Definition M := Object.
  Definition MArr : BC_morph M := _. 
  Definition MTermO : BC_term M := _.
  Definition MTermA : BC_terminal M := _.
  Definition MComp  : BC_comp M := _.
  Definition MId    : BC_id M := _.
  Definition Cat : BaseCat M := _.
  
  Program Definition Lim_Object (T : Tower) : Object :=
    {| obj := fun n => { x : forall k, tow_objs T k n | forall k, tow_morphs T k n (x (S k)) ≡ x k };
       obj_eq := fun n u v => let (x, _) := u in
                              let (y, _) := v in forall k, x k ≡ y k |}.
  Next Obligation.
    apply Build_Equivalence.
    intros u ; destruct u as [x Px] ; intros k ; reflexivity.
    intros u v H ; destruct u as [x Px] ; destruct v as [y Py] ; intros k ; symmetry ; auto.
    intros u v w H1 H2 ; destruct u as [x Px] ; destruct v as [y Py] ; destruct w as [z Pz] ;
    intros k ; etransitivity ; auto.
  Defined.
  Next Obligation.
    exists (fun k => restr (tow_objs T _) _ (X k)) ; intros k ; assert (Hk := H k).
    destruct (tow_morphs T k) as [α αp αr].
    symmetry ; etransitivity.
    - apply restr_proper.
      symmetry ; eassumption.
    - eauto.
  Defined.
  Next Obligation.
    intros [x Px] [y Py] Heq k.
    apply restr_proper ; auto.
  Defined.

  Program Definition AllLimits : forall T, Limit T :=
    fun T => {| lim_cone := {| cone_t := Lim_Object T;
                               cone_m := fun i => {| morph := fun n u => let (x, _) := u in x i |} |};
                lim_exists := fun C => {| morph := fun n Xn => exist _ (fun k => cone_m _ C k _ Xn) _ |}
             |}.
  Next Obligation.
    intros [x Px] [y Py] Heq ; auto.
  Defined.
  Next Obligation.
    reflexivity.
  Defined.
  Next Obligation.
    assert (HC := cone_m_com T C k).
    destruct (cone_m T C k) as [α αp αr] ; auto.
  Defined.
  Next Obligation.
    intros u v Heq k ; apply morph_proper ; auto.
  Defined.
  Next Obligation.
    apply morph_natural.
  Defined.
  Next Obligation.
    remember (cone_m T C n) as cn.
    destruct cn as [β βp βr] ; intros k x ; simpl.
    rewrite <- Heqcn.
    reflexivity.
  Defined.    
  Next Obligation.
    destruct h as [α αp αr] ; intros n x ; simpl.
    remember (α n x) as αnx.
    simpl in HEq ; destruct αnx as [u Pu] ; intros k.
    assert (HEqk := HEq k) ; clear HEq.
    destruct (cone_m T C k) as [β βp βr] ; simpl in HEqk ; simpl.
    assert (HEqnx := HEqk n x) ; rewrite <- Heqαnx in HEqnx.
    symmetry ; auto.
  Defined.    
End TOTMcat.


(* Example of the stream functor, F(X) = N × ▸X *)

Module StreamFunctor : InputType(TOTMcat).
  Import TOTMcat.

  Program Definition Prod (X Y : Object): Object :=
    {| obj := fun n => X n * Y n;
       obj_eq := fun n p q => let (x, y) := p in
                              let (x', y') := q in
                              x ≡ x' /\ y ≡ y';
       restr := fun n p => let (x, y) := p in
                           (restr _ _ x, restr _ _ y)
    |}%type.
  Next Obligation.
    apply Build_Equivalence.
    intros p ; destruct p ; split ; reflexivity.
    intros p q; destruct p ; destruct q ; intuition.
    intros [x y] [x' y'] [x'' y''] ; intuition ; etransitivity ; eauto.
  Defined.
  Next Obligation.
    intros [x y] [z w] ; intuition ; apply restr_proper ; auto.
  Defined.

  Program Definition Nat : Object :=
    {| obj := fun n => nat;
       restr := fun n x => x;
       obj_eq := fun n => eq
    |}.
  Next Obligation.
    apply Build_Equivalence ; intuition.
  Defined.

  Program Definition Later (X : Object) : Object :=
    {| obj := fun n => match n with
                         | O => unit
                         | S m => X m
                       end;
       restr := fun n => match n with
                           | O => fun x => tt
                           | S m => restr X m
                         end;
       obj_eq := fun n => match n with
                            | O => eq
                            | S m => obj_eq X m
                          end
    |}.
  Next Obligation.
    assert (H := obj_eq_equiv X).
    apply Build_Equivalence ; destruct n ; intuition.
  Defined.
  Next Obligation.
    intros x y Heq ; destruct n ; auto ; apply restr_proper ; auto.
  Defined.

  Program Definition next (X : Object): X ↝ Later X :=
    {| morph := fun n x => match n with
                             | O => tt
                             | S m => restr X m x
                           end
    |}.
  Next Obligation.
    intros x y Heq ; destruct n ; auto ; apply restr_proper ; auto.
  Defined.
  Next Obligation.
    destruct n ; eauto ; reflexivity.
  Defined.
  
  Program Definition F : M -> M -> M :=
    fun Xm Xp => Prod Nat (Later Xp).

  Program Definition Fmorph (X Y Z W : Object) (fs : (Y -t> X) * (Z -t> W)): forall n, F X Z n -> F Y W n :=
    fun k p => let (α, β) := fs in let (n, x) := p in (n, _).
  Next Obligation.
    destruct k.
    exact x.
    exact (β _ x).
  Defined.

  Program Definition FArr : BiFMap F :=
    fun X Y Z W => n[(fun fs => {| morph := Fmorph X Y Z W fs |})].
  Next Obligation.
    intros [ℓ x] [k y] Heq ; destruct n ; simpl ; intuition.
    apply morph_proper ; auto.
  Defined.
  Next Obligation.
    destruct n ; simpl ; intuition.
    apply morph_natural.
  Defined.
  Next Obligation.
    intros [ℓ x] [k y] [_ Heqxy] ; destruct n ; simpl ; [tauto | intros [a b]]; simpl.
    unfold snd in Heqxy; destruct x as [α αp αr] ; destruct y as [β βp βr] ; auto.
  Defined.
  Next Obligation.
    intros [ℓ x] [k y] [_ Heq] m Hlt [o u] ; destruct m ; simpl ; intuition.
  Defined.

  Program Definition FFun : @BiFunctor _ _ _ _ F FArr :=
    {| fmorph_comp := fun X Y Z W U V f g h k => _;
       fmorph_id := fun X Y => _
    |}.
  Next Obligation.
    destruct n ; simpl ; intuition.
  Defined.
  Next Obligation.
    destruct n ; simpl ; intuition.
  Defined.

  Program Definition tmorph_ne_fun n : One n -> F One One n := 
    fun _ => match n with
               | O => (O, tt)
               | S n => (O, tt)
             end.

  (* Program Definition does not work, that is, it gets confused for some reason. *)
  Definition tmorph_ne : 1 -t> (F 1 1).
    refine (Build_Morphism _ _ tmorph_ne_fun _ _).
    - intros n x ; destruct n ; simpl ; intuition.
  Defined.      

  Theorem F_contractive : forall {m0 m1 m2 m3 : M}, contractive (@fmorph _ hom_BC_morph F FArr m0 m1 m2 m3).
  Proof.
    intros X Y Z W n [z [α αp αr]] [w [β βp βr]] Heq k Lt [ℓ x] ; simpl ; destruct k ; intuition.
    assert (k < n) as Hkn by auto with arith.
    destruct Heq as [_ Heq] ; assert (Heqk := Heq k Hkn x) ; auto.
  Defined.           
End StreamFunctor.

Module Streams := Solution TOTMcat StreamFunctor.
