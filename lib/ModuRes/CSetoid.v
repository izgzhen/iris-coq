(** Basic categorical definitions. The role of objects is played by
    the class [type] which is a type equipped with an equivalence
    relation.

    Then there are standard constructions defined using these objects
    (product, exponential, initial objects and functors at the end)
    and some of their properties are proved.
 *)

Require Import Ssreflect.ssreflect.  
Require Export Coq.Program.Program.
Require Export Morphisms SetoidTactics.
Require Export SetoidClass.
Require Export Util.

Generalizable Variables T U V W.

(* Proof by reflexivity *)
Lemma equivR {T : Type} `{eqT : Setoid T} {a b : T} :
  a = b -> a == b.
Proof.
  intros Heq. subst a. reflexivity.
Qed.

Notation "'mkType' R" := (@Build_Setoid _ R _) (at level 10).

(** A morphism between two types is an actual function together with a
    proof that it preserves equality. *)
Record morphism S T `{eqS : Setoid S} `{eqT : Setoid T} :=
  mkMorph {
    morph :> S -> T;
    morph_resp : Proper (equiv ==> equiv) morph}.

Arguments mkMorph [S T eqS eqT] _ _.
Arguments morph_resp [S T eqS eqT] _ _ _ _.

Infix "-=>" := morphism (at level 45, right associativity).
Notation "'s[(' f ')]'" := (mkMorph f _).
Ltac resp_set :=
  intros t1 t2 HEqt; repeat (intros ?); simpl in *; try rewrite -> !HEqt; reflexivity.

Section Morphisms.
  Context `{eT : Setoid T} `{eU : Setoid U} `{eV : Setoid V}.

  (** The type of equivalence-preserving maps is again a type with
      equivalence, defined pointwise. *)
  Global Program Instance morph_type : Setoid (T -=> U) :=
    mkType (fun f g => forall x, f x == g x).
  Next Obligation.
    clear; split.
    - intros f x; reflexivity.
    - intros f g HS x; symmetry; apply HS.
    - intros f g h Hfg Hgh x; etransitivity; [apply Hfg | apply Hgh].
  Qed.

  (** The application of [morphsm] to its argument preserves equality
      in both the function and the argument. *)
  Global Instance equiv_morph :
    Proper (equiv ==> equiv ==> equiv) (morph T U).
  Proof.
    intros f g HEq x y HEq'; etransitivity; [apply HEq | apply g, HEq'].
  Qed.

  (** Definition of composition of morphisms. Note the different
      arrows, i.e., -=> and ->. *)
  Program Definition mcomp (f: U -=> V) (g: T -=> U) : (T -=> V) :=
    s[(f ∘ g)].
  Next Obligation.
    intros x y HEq; apply f, g; assumption.
  Qed.

  Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

  (** Two specific morphisms, identity and constant maps. *)
  Program Definition mid : T -=> T := s[(fun x => x)].

  Program Definition mconst (u : U) : T -=> U := s[(const u)].

End Morphisms.

Infix "<<" := mcomp (at level 35).
Arguments mid T {eT}.
Arguments compose {_ _ _} _ _ _ /.

Section MorphConsts.
  Context `{eT : Setoid T} `{eU : Setoid U} `{eV : Setoid V} `{eW : Setoid W}.

  (** Composition maps equal morphism to equal morphisms. *)
  Global Instance equiv_mcomp :
    Proper (equiv (A := U -=> V) ==> equiv ==> equiv) mcomp.
  Proof.
    intros f f' HEq g g' HEq' x; simpl; rewrite ->HEq, HEq'; reflexivity.
  Qed.

  (** Composition of morphisms is associative. *)
  Lemma mcomp_assoc (f: V -=> W) (g: U -=> V) (h: T -=> U) :
    f << (g << h) == (f << g) << h.
  Proof. intros x; reflexivity. Qed.

  (** Identity is left- and right- identity for composition *)
  Lemma mcomp_idR (f : U -=> V) :
    f << mid _ == f.
  Proof. intros x; reflexivity. Qed.
  Lemma mcomp_idL (f : U -=> V) :
    mid _ << f == f.
  Proof. intros x; reflexivity. Qed.

  (** Lift an ordinary function to a function on [type]'s. *)
  Definition lift2s (f : T -> U -> V) p q : (T -=> U -=> V) :=
    mkMorph (fun x => mkMorph (f x) (p x)) q.

  Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

  (** Pre- and postcomposition, as equality-preserving maps *)
  Program Definition precomp (f : T -=> U) : (U -=> V) -=> (T -=> V) :=
    s[(fun g => g << f)].

  Program Definition postcomp (f : T -=> U) : (V -=> T) -=> (V -=> U) :=
    s[(fun g => f << g)].

End MorphConsts.

(*Instance Equiv_PropP : Equiv Prop := iff.
Instance type_PropP : type Prop := iff_equivalence.*)

Section SetoidProducts.
  Context `{eU : Setoid U} `{eV : Setoid V}.

  (** The product of two types is another type, with equality defined pointwise. *)
  Global Program Instance prod_type : Setoid (U * V) :=
    mkType (fun p1 p2 : U * V => (fst p1) == (fst p2) /\ (snd p1) == (snd p2)).
  Next Obligation.
    split.
    - intros [u v]; split; reflexivity.
    - intros [u1 v1] [u2 v2] [Hu Hv]; split; symmetry; assumption.
    - intros [u1 v1] [u2 v2] [u3 v3] [Hu12 Hv12] [Hu23 Hv23]; split; etransitivity; eassumption.
  Qed.

  Global Instance prod_proper : Proper (equiv ==> equiv ==> equiv) (@pair U V).
  Proof.
    intros u1 u2 Hu v1 v2 Hv; split; assumption.
  Qed.

  Global Instance mfst_proper : Proper (equiv ==> equiv) (@fst U V).
  Proof.
    intros [u1 v1] [u2 v2] [Hu Hv]; assumption.
  Qed.

  Global Instance msnd_proper : Proper (equiv ==> equiv) (@snd U V).
  Proof.
    intros [u1 v1] [u2 v2] [Hu Hv]; assumption.
  Qed.

  Local Obligation Tactic := intros; resp_set || program_simpl.

  (** The projections are in fact proper morphisms, i.e. they preserve equality. *)
  Program Definition mfst : (U * V) -=> U := s[(fst)].

  Program Definition msnd : (U * V) -=> V := s[(snd)].

  Context `{eT : Setoid T}.

  (** Tupling is also a proper morphism, i.e. respects equality. *)
  Program Definition mprod (f: T -=> U) (g: T -=> V) : T -=> (U * V) :=
    s[(fun t => (f t, g t))].
  Next Obligation.
    add_morphism_tactic; intros.
    rewrite H. split; reflexivity.
  Qed.

  Lemma mprod_unique (f: T -=> U) (g: T -=> V) (h: T -=> U * V) :
    mfst << h == f -> msnd << h == g -> h == mprod f g.
  Proof.
    intros HL HR x; split; simpl; [rewrite <- HL | rewrite <- HR]; reflexivity.
  Qed.

End SetoidProducts.

Arguments mprod_unique [U eU V eV T eT f g h] _ _ _.


Section Exponentials.
  Context `{eT : Setoid T} `{eU : Setoid U} `{eV : Setoid V} `{eW : Setoid W}.

  Local Obligation Tactic := intros; resp_set || program_simpl.

  (** Composition of morphism _as a morphims_. *)
  Program Definition comps : (U -=> V) -=> (T -=> U) -=> T -=> V :=
    lift2s (fun f g => f << g) _ _.

  Program Definition muncurry (f : T -=> U -=> V) : T * U -=> V :=
    s[(fun p => f (fst p) (snd p))].
  Next Obligation.
    add_morphism_tactic; intros [t1 u1] [t2 u2] [Ht Hu]; simpl in *.
    rewrite ->Ht, Hu; reflexivity.
  Qed.

  (** Currying map, i.e. the exponential transpose. *)
  Program Definition mcurry (f : T * U -=> V) : T -=> U -=> V :=
    lift2s (fun t u => f (t, u)) _ _.

  (** f × g, i.e. 〈 f ∘ π, g ∘ π' 〉 *)
  Definition mprod_map (f : T -=> U) (g : V -=> W) := mprod (f << mfst) (g << msnd).

  (** Evaluation map. *)
  Program Definition meval : (T -=> U) * T -=> U :=
    s[(fun p => fst p (snd p))].
  Next Obligation.
    add_morphism_tactic; intros [f1 t1] [f2 t2] [Hf Ht]; simpl in *.
    rewrite ->Hf, Ht; reflexivity.
  Qed.

End Exponentials.

Section Exp_props.
  Context `{eT : Setoid T} `{eU : Setoid U} `{eV : Setoid V} `{eW : Setoid W}.

  (** (Λ(f) × id) ; eval = f, where Λ(f) is the exponential transpose. *)
  Lemma mcurry_com (f : T * U -=> V) : f == meval << (mprod_map (mcurry f) (mid _)).
  Proof. intros [a b]; reflexivity. Qed.

  (** Exponential transposes are unique. *)
  Lemma mcurry_unique (f : T * U -=> V) h :
    f == meval << (mprod_map h (mid _)) -> h == mcurry f.
  Proof. intros HEq a b; simpl; rewrite HEq; reflexivity. Qed.

End Exp_props.

Program Instance unit_type : Setoid unit := mkType (fun _ _ => True).
Next Obligation.
  split.
  - intros _; exact I.
  - intros _ _ _; exact I.
  - intros _ _ _ _ _; exact I.
Qed.

(** The [unit] type is the terminal object, i.e., there's a unique
    morphism from any [Setoid] to [unit] *)
Section Terminals.
  Context `{eT : Setoid T}.

  Definition mone_term : T -=> unit := mconst tt.

  Lemma mone_term_unique (f g : T -=> unit) : f == g.
  Proof.
    intros x; destruct (f x); destruct (g x); reflexivity.
  Qed.

End Terminals.

Inductive empty : Set :=.
Program Instance empty_type : Setoid empty := mkType (fun _ _ => False).
Next Obligation.
  split; intros x; case x.
Qed.


(** The empty [type] is the initial element, i.e. there is unique a
    morphism from it to any other [type]. *)
Section Initials.
  Context `{eT : Setoid T}.

  Program Definition mzero_init : empty -=> T := s[(fun x => match x with end)].
  Next Obligation. intros x; case x; fail. Qed.

  Lemma mzero_init_unique (f g : empty -=> T) : f == g.
  Proof. intros x; case x. Qed.

End Initials.

(** Subsets. *)
Section Subsetoid.
  Context `{eT : Setoid T} {P : T -> Prop}.

  (** [type] of elements that satisfy the predicate P, i.e. a
      subset. Equality is inherited from the carrier type. *)
  Global Program Instance subset_type : Setoid {t : T | P t} :=
    mkType (fun x y => ` x == ` y).
  Next Obligation.
    split.
    - intros [x Hx]; simpl; reflexivity.
    - intros [x Hx] [y Hy] HS; simpl in *; symmetry; assumption.
    - intros [x Hx] [y Hy] [z Hz] Hxy Hyz; simpl in *; etransitivity; eassumption.
  Qed.

  Global Instance proj1sig_proper :
    Proper (equiv (A := {t : T | P t}) ==> equiv) (@proj1_sig _ _).
  Proof. intros [x Hx] [y Hy] HEq; simpl in *; assumption. Qed.

  (** Inclusion from the subset to the superset is an
      equality-preserving morphism. *)
  Program Definition mincl : {t : T | P t} -=> T := s[(@proj1_sig _ _)].

  (** If we have a morphism from B to A whose image is in the subset
      determined by P, then this morphism restricts to the one into
      the subset determined by P. *)
  Context `{eU : Setoid U}.
  Program Definition minherit (f : U -=> T) (HB : forall u, P (f u)) :
    U -=> {t : T | P t} := s[(fun u => exist P (f u) (HB u))].
  Next Obligation.
    intros x y HEq; red; simpl; rewrite HEq; reflexivity.
  Qed.

  (** Inclusion from subset determined by P to the superset is a monomorphism. *)
  Lemma mforget_mono (f g : U -=> {t : T | P t}) :
    mincl << f == mincl << g -> f == g.
  Proof.
    intros HEq x; simpl; rewrite ->(HEq x); reflexivity.
  Qed.

End Subsetoid.

(** Lifting of a type by adding a new distinct element.

    This is used for several constructions: lookups in finite maps
    return function types, for instance.
 *)
Section Option.
  Context `{eT : Setoid T}.

  Definition opt_eq (x y : option T) :=
    match x, y with
      | None, None => True
      | Some x, Some y => x == y
      | _, _ => False
    end.

  Global Program Instance option_type : Setoid (option T) :=
    mkType opt_eq.
  Next Obligation.
    split.
    - intros [a |]; simpl; reflexivity.
    - intros [a |] [b |] HS; simpl in *; now trivial || symmetry; assumption.
    - intros [a |] [b |] [c |] Hab Hbc; simpl in *; try (exact I || contradiction); [].
      etransitivity; eassumption.
  Qed.

End Option.

Section OptDefs.
  Context `{eT : Setoid T} `{eU : Setoid U}.

  Global Instance Some_proper : Proper (equiv ==> equiv) (@Some T).
  Proof. intros a b HEq; simpl; apply HEq. Qed.

  Program Definition msome : T -=> option T := s[(@Some T)].

  Definition optbind (f : T -> option U) (ov : option T) : option U :=
    match ov with
      | Some v => f v
      | None   => None
    end.

  Program Definition moptbind : (T -=> option U) -=> option T -=> option U :=
    lift2s (T:=T-=>option U) optbind _ _.
  Next Obligation.
    intros [v1 |] [v2 |] EQv; try (contradiction EQv || exact I); [].
    unfold optbind; apply x, EQv.
  Qed.
  Next Obligation.
    intros f1 f2 EQf [x |]; [simpl morph | exact I].
    apply EQf.
  Qed.

  Lemma opt_eq_iff x y : (forall v, x == Some v <-> y == Some v) -> x == y.
  Proof.
    intros. destruct x as [vx|] eqn:X, y as [vy|] eqn:Y.
    - generalize (H vy). intros H1y.
      rewrite H1y. reflexivity.
    - specialize (H vx). destruct H as [H1 _]. destruct H1. reflexivity.
    - specialize (H vy). destruct H as [_ H1]. destruct H1. reflexivity.
    - reflexivity.
  Qed.

End OptDefs.

Section DiscreteType.
  Context {T : Type}.

  Program Instance discreteType : Setoid T := mkType (@eq T).
End DiscreteType.

Section ViewLemmas.
  Context {T} `{eqT : Setoid T}.
  Implicit Types (t : T).

  Lemma srefl t : t == t.
  Proof. by reflexivity. Qed.
  
  Lemma strans {t1 t2 t3} (HL : t1 == t2) (HU : t2 == t3) : t1 == t3.
  Proof. by transitivity t2. Qed.
End ViewLemmas.
