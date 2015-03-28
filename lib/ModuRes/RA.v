(** Resource algebras: Commutative monoids with a validity predicate. *)

Require Import Ssreflect.ssreflect.
Require Import Coq.Classes.RelationPairs.
Require Import Bool.
Require Import Predom.
Require Import CSetoid.
Require Import MetricCore.
Require Import PreoMet.

Set Bullet Behavior "Strict Subproofs".

Class Associative {T} `{eqT : Setoid T} (op : T -> T -> T) :=
  assoc : forall t1 t2 t3, op t1 (op t2 t3) == op (op t1 t2) t3.
Class Commutative {T} `{eqT : Setoid T} (op : T -> T -> T) :=
  comm  : forall t1 t2, op t1 t2 == op t2 t1.

Section RADef.
  Context {T : Type} {eqT : Setoid T}.

  Class RA_unit := ra_unit : T.
  Class RA_op   := ra_op : T -> T -> T.
  Class RA_valid:= ra_valid : T -> Prop.
  Class RA {TU : RA_unit} {TOP : RA_op} {TV : RA_valid}: Prop :=
    mkRA {
        ra_op_proper       :> Proper (equiv ==> equiv ==> equiv) ra_op;
        ra_op_assoc        :> Associative ra_op;
        ra_op_comm         :> Commutative ra_op;
        ra_op_unit {t}     : ra_op ra_unit t == t;
        ra_valid_proper    :> Proper (equiv ==> iff) ra_valid;
        ra_valid_unit      : ra_valid ra_unit;
        ra_op_valid {t1 t2}: ra_valid (ra_op t1 t2) -> ra_valid t1
      }.
End RADef.
Arguments RA_unit : clear implicits.
Arguments RA_op : clear implicits.
Arguments RA_valid : clear implicits.
Arguments RA T {_ _ _ _}: clear implicits.

Delimit Scope ra_scope with ra.
Local Open Scope ra_scope.

Notation "'1'" := (ra_unit) : ra_scope.
Notation "p · q" := (ra_op p q) (at level 40, left associativity) : ra_scope.
Notation "'↓' p" := (ra_valid p) (at level 48) : ra_scope.

Class Cancellative {T} `(raT : RA T) : Prop :=
  ra_cancel : forall {t1 t2 t3 : T}, ↓t1 · t3 -> t1 · t2 == t1 · t3 -> t2 == t3.

Section RA_FPU.
  Context {T} `{raT : RA T}.
  Implicit Types (t : T) (P : T -> Prop).

  (* Two judgments means we'll duplicate some work (e.g., for products). *)
  Definition RA_FPS t1 t2 := forall tf, ↓t1 · tf -> ↓t2 · tf.
  Definition RA_FPU t1 P := forall tf, ↓t1 · tf -> exists t2, P t2 /\ ↓t2 · tf.
End RA_FPU.
Notation "a ⇝ b" := (RA_FPS a b) (at level 48, no associativity) : ra_scope.
Notation "a '⇝∈' B" := (RA_FPU a B) (at level 48, no associativity) : ra_scope.

(* General RA lemmas *)
Section RALemmas.
  Context {T} `{raT : RA T}.

  Implicit Types (t : T).

  Lemma ra_op_unit2 {t} : t · 1 == t.
  Proof.
    rewrite comm. now eapply ra_op_unit.
  Qed.

  Lemma ra_op_valid2 {t1 t2} : ↓ (t1 · t2) -> ↓ t2.
  Proof.
    rewrite comm. now eapply ra_op_valid.
  Qed.

  Lemma ra_op_invalid {t1 t2} : ~↓t1 -> ~↓(t1 · t2).
  Proof.
    intros Hinval Hval.
    apply Hinval.
    eapply ra_op_valid; now eauto.
  Qed.

  Lemma ra_op_invalid2 {t1 t2} : ~↓t2 -> ~↓(t1 · t2).
  Proof.
    rewrite comm. now eapply ra_op_invalid.
  Qed.

  Lemma ra_fpu_fps {t1 t2} (Hu : t1 ⇝ t2) : t1 ⇝∈ (equiv t2).
  Proof. move=> f Hv; exists t2; split; [by reflexivity | exact: Hu]. Qed.

  Lemma ra_fps_id {t :T} : t ⇝ t.
  Proof. done. Qed.
  
  Lemma ra_fpu_id {t : T} {P : T -> Prop} (Ht : P t) : t ⇝∈ P.
  Proof. by move=> f Hv; exists t. Qed.
End RALemmas.



(** The usual algebraic order on RAs. *)
Section Order.
  Context {T} `{raT : RA T}.

  Let ra_ord t1 t2 :=
    exists t, t · t1 == t2.

  Global Instance ra_ord_preo: PreOrder ra_ord.
  Proof.
    split.
    - intros r; exists 1; erewrite ra_op_unit by apply _; reflexivity.
    - intros z yz xyz [y Hyz] [x Hxyz]; exists (x · y).
      rewrite <- Hxyz, <- Hyz; symmetry; apply assoc.
  Qed.

  (* Do not infer this automatically: It often ends in an endless loop searching for the unit of a type which is,
     not at all, an RA. *)
  Global Program Instance pord_ra : preoType T | 5 := mkPOType ra_ord _.
  Next Obligation.
    move=> x1 x2 Rx y1 y2 Ry [t Ht].
    exists t; by rewrite -Rx -Ry.
  Qed.

  Global Instance ra_op_mono : Proper (pord ++> pord ++> pord) ra_op.
  Proof.
    intros x1 x2 [x EQx] y1 y2 [y EQy]. exists (x · y).
    rewrite <- assoc, (comm y), <- assoc, assoc, (comm y1), EQx, EQy; reflexivity.
  Qed.

  (* PDS: Are we actually searching for validity proofs? *)
  Global Instance ra_valid_ord : Proper (pord ==> flip impl) ra_valid.
  Proof. move=>t1 t2 [t' HEq]; rewrite -HEq; exact: ra_op_valid2. Qed.

  Lemma unit_min {r} : 1 ⊑ r.
  Proof. exists r. exact: ra_op_unit2. Qed.

  Lemma ra_cancel_ord {HC : Cancellative raT} {a b c : T} :
    ↓a · c -> a · b ⊑ a · c -> b ⊑ c.
  Proof.
    move=> /ra_cancel Hc [t HEq]; exists t.
    by apply: Hc; move: HEq; rewrite assoc -[t · _]comm -assoc.
  Qed.
End Order.
Arguments ra_op_mono {_ _ _ _ _ _} {_ _} _ {_ _} _.
Arguments ra_valid_ord {_ _ _ _ _ _} {_ _} _ _.

Section OrdTests.
  Context {S T} `{raS : RA S, raT : RA T}.
  Implicit Types (s : S) (t : T).

  Goal forall s1 s2 t, s1 == s2 -> (s1,t) ⊑ (s2,t).
  Proof. move=> s1 s2 t ->. reflexivity. Qed.
End OrdTests.


(* CMRA ("camera"): RAs with a complete metric. *)
Section CMRA.
  Context {T: Type} {eqT: Setoid T} `{raT: RA (eqT:=eqT) T}.

  Class CMRA `{pcmT: pcmType (eqT:=eqT) (pTA:=pord_ra) T}: Prop := (* force this to become an actual argument *)
    { ra_op_dist n :> Proper (dist n ==> dist n ==> dist n) ra_op }.
End CMRA.
Arguments CMRA T {_ _ _ _ _ _ _ _}: clear implicits.

Section DiscreteCMRA.
  Context {T: Type} `{raT: RA T}.
  Existing Instance discreteMetric.
  Existing Instance discreteCMetric.

  Global Instance discreteCMRA : CMRA T.
  Proof.
    split. move=>n a1 a2 EQa b1 b2 EQb.
    destruct n as [|n]; first by exact I.
    simpl in *. rewrite EQa EQb. reflexivity.
  Qed.
End DiscreteCMRA.


(* RAs with cartesian products of carriers. *)
Section Pairs.
  Context {S T: Type}.
  Context `{raS : RA S, raT : RA T}.

  Global Instance ra_unit_prod : RA_unit (S * T) := (1, 1).
  Global Instance ra_op_prod : RA_op (S * T) :=
    fun st1 st2 =>
      match st1, st2 with
        | (s1, t1), (s2, t2) => (s1 · s2, t1 · t2)
      end.
  Global Instance ra_valid_prod : RA_valid (S * T) :=
    fun st => match st with (s, t) => ra_valid s /\ ra_valid t
              end.
  Global Instance ra_prod : RA (S * T).
  Proof.
    split.
    - intros [s1 t1] [s2 t2] [Heqs Heqt]. intros [s'1 t'1] [s'2 t'2] [Heqs' Heqt']. simpl in *.
      split; [rewrite -> Heqs, Heqs'|rewrite ->Heqt, Heqt']; reflexivity.
    - intros [s1 t1] [s2 t2] [s3 t3]. simpl; split; now rewrite assoc.
    - intros [s1 t1] [s2 t2]. simpl; split; now rewrite comm.
    - intros [s t]. simpl; split; now rewrite ra_op_unit.
    - intros [s1 t1] [s2 t2] [Heqs Heqt]. unfold ra_valid; simpl in *.
      rewrite -> Heqs, Heqt. reflexivity.
    - unfold ra_unit, ra_valid; simpl. split; eapply ra_valid_unit; now apply _.
    - intros [s1 t1] [s2 t2]. unfold ra_valid; simpl. intros [H1 H2]. split.
      + eapply ra_op_valid; now eauto.
      + eapply ra_op_valid; now eauto.
  Qed.

  Implicit Types (s : S) (t : T) (p : S * T).

  Lemma ra_op_prod_fst {p1 p2} :
    fst (p1 · p2) = fst p1 · fst p2.
  Proof.
    by move: p1=>[s1 t1]; move: p2=>[s2 t2]; reflexivity.
  Qed.

  Lemma ra_op_prod_snd {p1 p2} :
    snd (p1 · p2) = snd p1 · snd p2.
  Proof.
    by move: p1=>[s1 t1]; move: p2=>[s2 t2]; reflexivity.
  Qed.

  Lemma ra_prod_pord {p1 p2}:
    pord (preoType:=pord_ra) p1 p2 <-> (fst p1 ⊑ fst p2 /\ snd p1 ⊑ snd p2).
  Proof.
    move: p1=>[s1 t1]; move: p2=>[s2 t2]/=.
    split.
    - move=> [[s t] /= [Heqs Heqt]]. split; eexists; eassumption.
    - move=> [[s Heqs] [t Heqt]]. exists (s, t). simpl. tauto.
  Qed.

  Lemma ra_prod_valid {p} :
    ↓p <-> ↓fst p /\ ↓snd p.
  Proof. by move: p=>[s t]. Qed.

  Lemma ra_sep_prod {p1 p2} :
    ↓p1 · p2 -> ↓fst p1 · fst p2 /\ ↓snd p1 · snd p2.
  Proof. by move: p1 p2 => [s t] [s' t']. Qed.

  Lemma ra_fps_prod {s s' t t'} (Hs : s ⇝ s') (Ht : t ⇝ t') : (s,t) ⇝ (s',t').
  Proof.
    move=> [fs ft] /ra_sep_prod [Hvs Hvt]; split; [exact: Hs Hvs | exact: Ht Hvt].
  Qed.

  Lemma ra_fps_fst {s s' t} (Hs : s ⇝ s') : (s,t) ⇝ (s',t).
  Proof. exact: ra_fps_prod Hs ra_fps_id. Qed.

  Lemma ra_fps_snd {s t t'} (Ht : t ⇝ t') : (s,t) ⇝ (s,t').
  Proof. exact: ra_fps_prod ra_fps_id Ht. Qed.
  
  Lemma ra_fpu_prod {s t PS PT} (Hs : s ⇝∈ PS) (Ht : t ⇝∈ PT) :
    (s,t) ⇝∈ fun p => PS(fst p) /\ PT(snd p).
  Proof.
    move=> [fs ft] /ra_sep_prod [Hvs Hvt].
    move/(_ _ Hvs): Hs=> [s' [HPS Hs']]; move/(_ _ Hvt): Ht=> [t' [HPT Ht']].
    by exists (s',t').
  Qed.

  Lemma ra_fpu_fst {s t PS} (Hs : s ⇝∈ PS) : (s,t) ⇝∈ fun p => PS(fst p) /\ t == snd p.
  Proof. exact: ra_fpu_prod Hs (ra_fpu_id (srefl t)). Qed.
  
  Lemma ra_fpu_snd {s t PT} (Ht : t ⇝∈ PT) : (s,t) ⇝∈ fun p => s == fst p /\ PT(snd p).
  Proof. exact: ra_fpu_prod (ra_fpu_id (srefl s)) Ht. Qed.
  
  Global Instance ra_can_prod {cS : Cancellative raS} {cT : Cancellative raT} :
     Cancellative (ra_prod).
  Proof.
    move=> [f f'] [a a'] [b b'] [Hv Hv'] [/= /(ra_cancel Hv)-> /(ra_cancel Hv')->].
    by split; reflexivity.
  Qed.

  (* THe RA order of the product is the same as the product of the RA orders *)
  Lemma ra_pord_iff_prod_pord {p1 p2}:
    pord (preoType:=pord_ra) p1 p2 <-> pord (preoType:=preoType_prod) p1 p2.
  Proof.
    rewrite ra_prod_pord /pord /=. reflexivity.
  Qed.
End Pairs.
(* Pairs work as CMRA *)
Section PairsCMRA.
  Context {S T: Type} `{cmraS: CMRA S} `{cmraT: CMRA T}.

  Global Instance ra_prod_pcm: pcmType (pTA:=pord_ra) (S * T).
  Proof.
    split. intros σ ρ σc ρc HC.
    apply ra_pord_iff_prod_pord.
    eapply pcm_respC; first by apply _.
    move=>i. apply ra_pord_iff_prod_pord. by apply: HC.
  Qed.

  Global Instance ra_prod_cmra: CMRA (S * T).
  Proof.
    split. move=>n [s11 t11] [s12 t12] /= [EQs1 EQt1] [s21 t21] [s22 t22] /= [EQs2 EQt2].
    split.
    - rewrite EQs1 EQs2. reflexivity.
    - rewrite EQt1 EQt2. reflexivity.
  Qed.
End PairsCMRA.

Section PairsMap.
  Context {S T U V: Type} `{cmraS: CMRA S} `{cmraT: CMRA T} `{cmraU: CMRA U} `{cmraV: CMRA V}.

  Local Instance ra_force_pord_TS: preoType (T * S) := pord_ra.
  Local Instance ra_force_pord_UV: preoType (U * V) := pord_ra.
  
  Program Definition RAprod_map (f: T -m> U) (g: S -m> V): (T * S) -m> (U * V) :=
    mkMUMorph (pcmprod_map f g) _.
  Next Obligation. (* If one day, this obligation disappears, then probably the instances are not working out anymore *)
    move=>x y EQxy. change (pcmprod_map f g x ⊑ pcmprod_map f g y).
    apply ra_pord_iff_prod_pord. apply ra_pord_iff_prod_pord in EQxy.
    by eapply mu_mono.
  Qed.

  Global Instance RAprod_map_resp: Proper (equiv ==> equiv ==> equiv) RAprod_map.
  Proof.
    move=>f1 f2 EQf g1 g2 EQg. change (pcmprod_map f1 g1 == pcmprod_map f2 g2).
    rewrite EQf EQg. reflexivity.
  Qed.
  Global Instance RAprod_map_nonexp n : Proper (dist n ==> dist n ==> dist n) RAprod_map.
  Proof.
    move=>f1 f2 EQf g1 g2 EQg. change (pcmprod_map f1 g1 = n = pcmprod_map f2 g2).
    rewrite EQf EQg. reflexivity.
  Qed.
  Global Instance RAprod_map_monic : Proper (pord ++> pord ++> pord) RAprod_map.
  Proof.
    move=>f1 f2 EQf g1 g2 EQg x. apply ra_pord_iff_prod_pord. 
    revert x. change (pcmprod_map f1 g1 ⊑ pcmprod_map f2 g2).
    by eapply pcmprod_map_monic.
  Qed.
End PairsMap.
Section PairsMapComp.
  Context {S T: Type} `{cmraS: CMRA S} `{cmraT: CMRA T}.

  Lemma RAprod_map_id:
    RAprod_map (pid T) (pid S) == pid (T*S).
  Proof. (* doing the proof again here is actually easier than using the ones from PreoMet... *)
    intros x. simpl. split; reflexivity.
  Qed.

  Context {U V W X: Type} `{cmraU: CMRA U} `{cmraV: CMRA V} `{cmraW: CMRA W} `{cmraX: CMRA X}.

  Lemma RAprod_map_comp (f: T -m> U) (g: U -m> V) (h: S -m> W) (i: W -m> X):
    RAprod_map g i ∘ RAprod_map f h == RAprod_map (g ∘ f) (i ∘ h).
  Proof.
    intros x. simpl. split; reflexivity.
  Qed.
End PairsMapComp.
Lemma RAprod_map_comp_fst {S T U V W: Type}
      `{cmraS: CMRA S} `{cmraT: CMRA T} `{cmraU: CMRA U} `{cmraV: CMRA V} `{cmraW: CMRA W}
      (f: T -m> U) (g: U -m> V) (h: S -m> W):
  RAprod_map g h ∘ RAprod_map f (pid _) == RAprod_map (g ∘ f) h.
Proof.
  intros x. simpl. split; reflexivity.
Qed.

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
  Next Obligation.
    reflexivity.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.
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
  Next Obligation.
    reflexivity.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.

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



(* Package an RA as a module type (for use with other modules). *)
Module Type RA_T.

  Parameter res : Type.
  Declare Instance res_type : Setoid res.
  Declare Instance res_op : RA_op res.
  Declare Instance res_unit : RA_unit res.
  Declare Instance res_valid : RA_valid res.
  Declare Instance res_ra : RA res.

End RA_T.
