Require Import ssreflect.
Require Import Predom CSetoid RA.

Local Open Scope ra_scope.

(** Morphisms between RAs. *)
Section Morph.
  Context {T U} `{raT : RA T, raU : RA U}.
  Record RA_morphism  :=
    mkRAMorph
      { ra_morph :> T -=> U;
        ra_morph_unit : ra_morph 1 == 1;
        ra_morph_op {t t'} : ra_morph (t · t') == ra_morph t · ra_morph t';
        ra_morph_valid {t} : ↓t -> ↓ra_morph t }.
End Morph.
Arguments RA_morphism T U {eqT TU TOP TV eqU UU UOP UV} : rename.
Infix "-ra>" := RA_morphism (at level 45, right associativity) : type_scope.
Notation "'ra[(' f ')]'" := (mkRAMorph f _ _ _) (at level 0) : ra_scope.

Section MorphEq.
  Context {T U} `{raT : RA T, raU : RA U}.
  Implicit Types (f : T -ra> U).

  (** Equality is pointwise. *)
  Definition ra_morph_eq f f' : Prop := forall t, f t == f' t.
  Global Instance ra_equiv_morph : Equivalence ra_morph_eq.
  Proof.
    split.
    - move=> f t. by reflexivity.
    - move=> f f' HEq t. by symmetry.
    - move=> f f' f'' HEq HEq' t. by transitivity (f' t).
  Qed.
  Global Instance ra_type_morph : Setoid (T -ra> U) := mkType ra_morph_eq.
End MorphEq.

Section Comp.
  Context {T U V} `{raT : RA T, raU : RA U, raV : RA V}.
  Implicit Types (f : T -ra> U) (g : U -ra> V).

  Program Definition racomp g f : T -ra> V :=
    ra[(g << f)].
  Next Obligation. rewrite (ra_morph_unit f) (ra_morph_unit g). by reflexivity. Qed.
  Next Obligation. rewrite (ra_morph_op f) (ra_morph_op g). by reflexivity. Qed.
  Next Obligation. apply: ra_morph_valid. exact: ra_morph_valid. Qed.
End Comp.
Infix "<RA<" := racomp (at level 35) : ra_scope.

Section Id.
  Context {T} `{raT : RA T}.

  Program Definition raid : T -ra> T := ra[(mid T)].
  Solve Obligations using reflexivity.
End Id.

Section Const.
  Context {T U} `{raT : RA T, raU : RA U}.

  Program Definition raconst1 : T -ra> U := ra[(mconst 1)].
  Next Obligation. by reflexivity. Qed.
  Next Obligation. by rewrite ra_op_unit; reflexivity. Qed.
  Next Obligation. exact: ra_valid_unit. Qed.
End Const.

Section MorphLemmas.
  Context {T U V W} `{raT : RA T, raU : RA U, raV : RA V, raW : RA W}.
  Implicit Types (f : T -ra> U) (g : U -ra> V) (h : V -ra> W).

  (** Composition maps equal morphisms to equal morphisms. *)
  Global Instance equiv_racomp :
    Proper (equiv (A := U -ra> V) ==> equiv (A := T -ra> U) ==> equiv) racomp.
  Proof. move=> g g' Hg f f' Hf t. rewrite /= (Hf t) (Hg (f' t)). by reflexivity. Qed.

  (** Composition is associative, and raid is its identity. *)
  Lemma racomp_assoc f g h :
    h <RA< (g <RA< f) == (h <RA< g) <RA< f.
  Proof. move=> t. by reflexivity. Qed.

  Lemma racomp_idR f : f <RA< raid == f.
  Proof. move=> t. by reflexivity. Qed.

  Lemma racomp_idL f : raid <RA< f == f.
  Proof. move=> t. by reflexivity. Qed.

  (** RA-morphisms are monotone wrt ra_ord. *)
  Global Instance ra_morph_mono f : Proper (pord ==> pord) f.
  Proof.
    move=> t t' [t'' H]. exists (f t''). rewrite -ra_morph_op H. by reflexivity.
  Qed.
End MorphLemmas.
Arguments equiv_racomp {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} {_ _} _ {_ _} _ {_}.
Arguments ra_morph_mono {_ _ _ _ _ _ _ _ _ _ _ _} _ {_ _} _.

Section MorphProductLemmas.
  Context {S T: Type} `{raS : RA S, raT : RA T}.
  Context {U} `{raU : RA U}.
  Implicit Types (f : U -ra> S) (g : U -ra> T).

  Program Definition rafst : (S * T) -ra> S := ra[(mfst)].
  Next Obligation. by reflexivity. Qed.
  Next Obligation. by reflexivity. Qed.
  Next Obligation. by move: H => [H _]. Qed.

  Program Definition rasnd : (S * T) -ra> T := ra[(msnd)].
  Next Obligation. by reflexivity. Qed.
  Next Obligation. by reflexivity. Qed.
  Next Obligation. by move: H => [_ H]. Qed.

  Program Definition raprod f g : U -ra> (S * T) :=
    ra[(mprod f g)].
  Next Obligation. by split; exact: ra_morph_unit. Qed.
  Next Obligation. by split; exact: ra_morph_op. Qed.
  Next Obligation. by split; exact: ra_morph_valid. Qed.

  Lemma raprod_unique {f g} {h : U -ra> S * T}
      (HL : rafst <RA< h == f) (HR : rasnd <RA< h == g) :
    h == raprod f g.
  Proof. move=> u. split; [exact: HL | exact: HR]. Qed.
End MorphProductLemmas.

(** T -ra> U as a pointwise RA, if ·U total. *)
(* PDS: This can likely be improved. *)
Class RA_total (T : Type) {TOP : RA_op T} {TV : RA_valid T} :=
  ra_op_total : forall t t', ↓t -> ↓t' -> ↓(t · t').
Section MorphRA.
  Context {T U} `{raT : RA T, raU : RA U} {totU : RA_total U}.
  Implicit Types (f : T -ra> U).

  Global Instance ra_unit_morph : RA_unit (T -ra> U) := raconst1.

  Global Program Instance ra_op_morph : RA_op (T -ra> U) :=
    fun f f' => ra[(s[(fun t => f t · f' t)])].
  Next Obligation. move=> t t' Heq. rewrite Heq. by reflexivity. Qed.
  Next Obligation. rewrite 2!ra_morph_unit ra_op_unit. by reflexivity. Qed.
  Next Obligation.
    rewrite 2!ra_morph_op -assoc [f t' · _]assoc [f t' · _]comm 3!assoc.
    by reflexivity.
  Qed.
  Next Obligation.
    move/(ra_morph_valid f): (H)=> Hf.
    move/(ra_morph_valid f'): H => Hf'.
    exact: ra_op_total.
  Qed.

  Global Instance ra_valid_morph : RA_valid (T -ra> U) :=
    fun f => True.    (* The natural "fun f => forall t, ↓t -> ↓f t" restates ra_morph_valid.*)

  Global Instance ra_morph_ra : RA (T -ra> U).
  Proof.
    split.
    - move=> f f' Hf g g' Hg t /=. rewrite (Hf t) (Hg t). by reflexivity.
    - move=> f g h t /=. rewrite assoc. by reflexivity.
    - move=> f g t /=. rewrite comm. by reflexivity.
    - move=> f t/=. rewrite ra_op_unit. by reflexivity.
    - done.
    - done.
    - done.
  Qed.
End MorphRA.

Section MorphRALemmas.
  Context {T U V W} `{raT : RA T, raU : RA U, raV : RA V, raW : RA W}.
  Implicit Types (f : T -ra> U) (g : U -ra> V).

  Context {totV : RA_total V}.
  Context {totU : RA_total U}.

  (** Pre- and postcomposition as structure-preserving maps. *)
  Program Definition raprecomp f : (U -ra> V) -ra> (T -ra> V) :=
    ra[(s[(fun g => g <RA< f)])].
  Next Obligation. move=> g g' Hg t /=. rewrite (Hg (f t)). by reflexivity. Qed.
  Next Obligation. move=> t /=. by reflexivity. Qed.
  Next Obligation. move: t t' => g g' t. by reflexivity. Qed.

  Program Definition rapostcomp g : (T -ra> U) -ra> (T -ra> V) :=
    ra[(s[(fun f => g <RA< f)])].
  Next Obligation. move=> f f' Hf t /=. rewrite (Hf t). by reflexivity. Qed.
  Next Obligation. move=> t. exact: ra_morph_unit. Qed.
  Next Obligation. move: t t' => f f' t. exact: ra_morph_op. Qed.
End MorphRALemmas.


(** Sub-RAs.*)
Class RA_sub {T} `{raT : RA T} {P : T -> Prop} : Prop :=
  mkRASub
    { ra_sub_unit : P 1;
      ra_sub_op {t t'} : P t -> P t' -> P (t · t') }.
Arguments RA_sub {_ _ _ _ _ _} _.
Arguments mkRASub {_ _ _ _ _ _ _} _ _.

Section Subra.
  Context {T} `{subT : RA_sub T}.

  Let sub := { t : T | P t }.

  Global Instance ra_type_sub : Setoid sub := subset_type.
  Global Instance ra_unit_sub : RA_unit sub := exist P 1 ra_sub_unit.
  Global Program Instance ra_op_sub : RA_op sub := fun a b => `a · `b.
  Next Obligation. move: a b=> [a Ha] [b Hb]. by exact: ra_sub_op. Qed.
  Global Instance ra_valid_sub : RA_valid sub := fun a => ↓ (`a).
  Global Instance ra_sub : RA sub.
  Proof.
    split.
    - move=> a a' Ha b b' Hb. move: Ha Hb=>/=->->. by reflexivity.
    - move=> a b c. rewrite /= assoc. by reflexivity.
    - move=> a b. rewrite /= comm. by reflexivity.
    - move=> a. rewrite /= ra_op_unit. by reflexivity.
    - rewrite/ra_valid/ra_valid_sub. by move=> a a' ->.
    - rewrite/ra_valid/ra_valid_sub. exact: ra_valid_unit.
    - rewrite/ra_valid/ra_valid_sub. by move=> a b /ra_op_valid.
  Qed.

  (* The inclusion is an RA-morphism. *)
  Program Definition raincl : sub -ra> T := ra[(mincl)].
  Solve Obligations using reflexivity.

  (* The inclusion is monic. *)
  Context {U} `{raU : RA U}.
  Lemma raforget_mono {f g : U -ra> sub}
      (Heq : raincl <RA< f == raincl <RA< g) :
    f == g.
  Proof. move=> u. exact: Heq. Qed.

  (** If we have a morphism from U to T whose image is in the subset
      determined by P, then this morphism restricts to the one into
      the subset determined by P. *)
  Program Definition rainherit (f : U -ra> T) (HU : forall u, P (f u))
    : U -ra> sub := ra[(s[(minherit f HU)])].
  Next Obligation. exact: ra_morph_unit. Qed.
  Next Obligation. exact: ra_morph_op. Qed.
  Next Obligation. exact: ra_morph_valid. Qed.

  Lemma ra_sep_sub {a b : sub} : ↓a · b ->↓ `a · `b.
  Proof. done. Qed.

  Lemma ra_fps_sub {t t': T} (Ht : P t) (Hu : t ⇝ t') (Ht' : P t') :
    (exist P t Ht) ⇝ (exist P t' Ht').
  Proof. move=> f; exact: Hu. Qed.

  Lemma ra_fpu_sub {t : T} {B : T -> Prop}
      (Ht : P t) (Hu : t ⇝∈ B) (HT : forall t, B t -> P t) :
    (exist P t Ht) ⇝∈ (B ∘ (@proj1_sig T P))%prg.
  Proof.
    move=> [f Hf] /ra_sep_sub HSep. move/(_ _ HSep): Hu => [t' [HB Ht']].
    by exists (exist P t' (HT _ HB)).
  Qed.
End Subra.
Arguments ra_sub {_ _ _ _ _ _ _} _ : clear implicits.

(** The image of an RA-morphism is a sub-RA. *)
(* PDS: This is ad hoc. *)
Section Image.
  Context {T U} `{raT : RA T, raU : RA U} (f : T -ra> U).

  Definition in_rng u := exists t, f t == u.
  Global Instance ra_sub_img : RA_sub in_rng.
  Proof.
     apply: mkRASub.
     - exists (1 : T). exact: ra_morph_unit.
     - move=> u u' [t Ht] [t' Ht']. exists (t · t').
       rewrite ra_morph_op Ht Ht'. by reflexivity.
   Qed.
   Definition raimg := ra_sub ra_sub_img.
   Program Definition raimginj : T -ra> {u | in_rng u} :=
     rainherit f _.
   Next Obligation. move: u=> t. by exists t; reflexivity. Qed.
End Image.

(*
	Let f : T -> U.
	Define image and pre-image as usual:
		f> : (T -> Prop) -> U -> Prop
			(f>P)u if ∃t. t=fu ∧ Pt
		f< : (U -> Prop) -> T -> Prop
			(f<Q)t if Q(ft)

	f induces FPU's (writing a ⇝ B : M for a FPU in M):
		If ta ⇝∈ tB : T,
		then (f ta) ⇝∈ (f>tB) : U.

		If (f<{ua}) ⇝∈ (f<uB) : U,
		then (f<{ua}) ⇝∈ (f<uB) : T.
*)
