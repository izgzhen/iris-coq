(** Resource algebras: Commutative monoids with a validity predicate. *)

Require Import ssreflect.
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

Notation "1" := (ra_unit) : ra_scope.
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


(* RAs with cartesian products of carriers. *)
Section Products.
  Context {S T: Type} `{raS : RA S, raT : RA T}.

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
End Products.

Section ProductLemmas.
  Context {S T} `{raS : RA S, raT : RA T}.
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
     Cancellative (ra_prod (S := S) (T := T)).
  Proof.
    move=> [f f'] [a a'] [b b'] [Hv Hv'] [/= /(ra_cancel Hv)-> /(ra_cancel Hv')->].
    by split; reflexivity.
  Qed.
End ProductLemmas.


(** The usual algebraic order on RAs. *)
Section Order.
  Context {T} `{raT : RA T}.

  Definition ra_ord t1 t2 :=
    exists t, t · t1 == t2.

  Global Instance ra_ord_preo: PreOrder ra_ord.
  Proof.
    split.
    - intros r; exists 1; erewrite ra_op_unit by apply _; reflexivity.
    - intros z yz xyz [y Hyz] [x Hxyz]; exists (x · y).
      rewrite <- Hxyz, <- Hyz; symmetry; apply assoc.
  Qed.

  Global Program Instance ra_preo : preoType T := mkPOType ra_ord.

  Global Instance equiv_pord_ra : Proper (equiv ==> equiv ==> equiv) (pord (T := T)).
  Proof.
    intros s1 s2 EQs t1 t2 EQt; split; intros [s HS].
    - exists s; rewrite <- EQs, <- EQt; assumption.
    - exists s; rewrite -> EQs, EQt; assumption.
  Qed.

  Global Instance ra_op_mono : Proper (pord ++> pord ++> pord) ra_op.
  Proof.
    intros x1 x2 [x EQx] y1 y2 [y EQy]. exists (x · y).
    rewrite <- assoc, (comm y), <- assoc, assoc, (comm y1), EQx, EQy; reflexivity.
  Qed.

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
Arguments equiv_pord_ra {_ _ _ _ _ _} {_ _} _ {_ _} _.
Arguments ra_op_mono {_ _ _ _ _ _} {_ _} _ {_ _} _.
Arguments ra_valid_ord {_ _ _ _ _ _} {_ _} _ _.


(** The exclusive RA. *)
Section Exclusive.
  Context {T: Type} `{eqT : Setoid T}.

  Inductive ex: Type :=
  | ex_own: T -> ex
  | ex_unit: ex
  | ex_bot: ex.

  Implicit Types (r s : ex) (t : T).

  Definition ex_eq r s: Prop :=
    match r, s with
      | ex_own t1, ex_own t2 => t1 == t2
      | ex_unit, ex_unit => True
      | ex_bot, ex_bot => True
      | _, _ => False
    end.

  Global Instance ra_equiv_ex : Equivalence ex_eq.
  Proof.
    split.
    - intros [t| |]; simpl; now auto.
    - intros [t1| |] [t2| |]; simpl; now auto.
    - intros [t1| |] [t2| |] [t3| |]; simpl; try now auto.
      + intros ? ?. etransitivity; eassumption.
  Qed.

  Global Program Instance ra_type_ex : Setoid ex :=
    mkType ex_eq.

  Global Instance ra_unit_ex : RA_unit _ := ex_unit.
  Global Instance ra_op_ex : RA_op _ :=
    fun r s =>
      match r, s with
        | ex_own _, ex_unit => r
        | ex_unit, ex_own _ => s
        | ex_unit, ex_unit   => ex_unit
        | _, _               => ex_bot
      end.
  Global Instance ra_valid_ex : RA_valid _ :=
    fun r => match r with
               | ex_bot => False
               | _      => True
             end.

  Global Instance ra_ex : RA ex.
  Proof.
    split.
    - intros [t1| |] [t2| |] Heqt [t'1| |] [t'2| |] Heqt'; simpl; now auto.
    - intros [s1| |] [s2| |] [s3| |]; reflexivity.
    - intros [s1| |] [s2| |]; reflexivity.
    - intros [s1| |]; reflexivity.
    - intros [t1| |] [t2| |] Heqt; unfold ra_valid; simpl in *; now auto.
    - reflexivity.
    - intros [t1| |] [t2| |]; unfold ra_valid; simpl; now auto.
  Qed.

  Lemma ra_sep_ex {t r} : ↓ex_own t · r -> r == 1.
  Proof. by case: r. Qed.

  Lemma ra_fps_ex_any t {r} (Hr : ↓r) : ex_own t ⇝ r.
  Proof. by move=> f /ra_sep_ex ->; rewrite ra_op_unit2. Qed.

  Lemma ra_fps_ex t t' : ex_own t ⇝ ex_own t'.
  Proof. exact: ra_fps_ex_any. Qed.

  Global Instance ra_can_ex : Cancellative ra_ex.
  Proof.
    case=>[t ||] a b Hv HEq.
    - by rewrite (ra_sep_ex Hv); move: Hv; rewrite -HEq=> /ra_sep_ex->; reflexivity.
    - by move: HEq; rewrite 2!ra_op_unit.
    - by exfalso.
  Qed.
End Exclusive.
Arguments ex T : clear implicits.

(** The authoritative RA. *)
Section Authoritative.
  Context {T} `{raT : RA T}.

  CoInductive auth := Auth of ex T * T.

  Implicit Types (x : ex T) (g t u : T) (r s : auth).

  Definition auth_eq r s : Prop :=
    match r, s with
    | Auth p, Auth p' => p == p'
    end.

  Global Instance ra_equiv_auth : Equivalence auth_eq.
  Proof.
    split.
    - by move=> [p]; rewrite/auth_eq; reflexivity.
    - by move=> [p] [p']; rewrite/auth_eq; symmetry.
    - by move=> [p1] [p2] [p3]; rewrite/auth_eq; transitivity p2.
  Qed.
  Global Instance ra_type_auth : Setoid auth := mkType auth_eq.
  
  Global Instance ra_unit_auth : RA_unit auth := Auth(ex_unit, 1).

  Global Instance ra_op_auth : RA_op auth := fun r s =>
    match r, s with Auth(x, t), Auth(x', t') => Auth(x·x', t·t') end.

  Global Instance ra_valid_auth : RA_valid auth := fun r =>
    match r with
    | Auth(ex_unit, t) => ↓t
    | Auth(ex_own g, t) => ↓g /\ ↓t /\ t ⊑ g
    | Auth(ex_bot, _) => False
    end.

  Global Instance ra_auth : RA auth.
  Proof.
    split.
    - move=> [[x1 t1]] [[x1' t1']] [/= Hx1 Ht1] [[x2 t2]] [[x2' t2']] [/= Hx2 Ht2].
      by rewrite Hx1 Ht1 Hx2 Ht2; split; reflexivity.
    - by move=> [[x1 t1]] [[x2 t2]] [[x3 t3]] /=; split; rewrite assoc; reflexivity.
    - by move=> [[x1 t1]] [[x2 t2]] /=; split; rewrite comm; reflexivity.
    - by move=> [[x t]] /=; split; rewrite ra_op_unit; reflexivity.
    - move=> [[x t]] [[x' t']] [/= Hx Ht].
      move: Hx; case: x=>[g||]; case: x'=>[g'||] => //= Hg; rewrite/ra_valid/ra_valid_auth Ht; [by rewrite Hg | done].
    - rewrite/ra_unit/ra_unit_auth/ra_valid/ra_valid_auth; exact: ra_valid_unit.
    - move=> [[x t]] [[x' t']]. rewrite /ra_op/ra_op_auth/ra_valid/ra_valid_auth.
      case: x=>[g||]; case: x'=>[g'||] //=.
      + move=>[Hg [Htv [t'' Ht]]]; split; [done | split; [exact: ra_op_valid Htv |]].
        exists (t'' · t'); by rewrite -assoc [t' · _]comm.
      + move=>[_ [Htv _]]; exact: ra_op_valid Htv.
      + exact: ra_op_valid.
  Qed.

  Lemma ra_sep_auth {t u x u'} :
    ↓Auth(ex_own t, u) · Auth(x, u') -> ↓t /\ x == 1 /\ ↓u · u' /\ u · u' ⊑ t.
  Proof.
    case: x=>[g||]; [done | | done].
    rewrite {1}/ra_valid/ra_valid_auth {1}/ra_op/ra_op_auth.
    by move=> [Ht [HSep HLe]].
  Qed.

  Definition auth_side_cond t u t' : Prop :=
    ↓t · u -> forall tf, t · tf ⊑ t · u -> t' · tf ⊑ t' · u.

  Lemma ra_fps_auth {t u t'} (SIDE : auth_side_cond t u t') (Hu' : ↓t' · u) :
    Auth(ex_own(t · u), t) ⇝ Auth(ex_own(t' · u), t').
  Proof.
    move=> [[xf tf]] /ra_sep_auth [Htu [Hxf [Htf HLe]]].
    rewrite/ra_valid/ra_valid_auth [Auth _ · _]/ra_op/ra_op_auth.
    move: Hxf; case: xf=>[g||] H; [done| clear H |done].	(* i.e., "rewrite Hxf" despite the match. *)
    rewrite {1}/ra_op/ra_op_ex.
    split; first done.
    set LE' := _ ⊑ _; suff HLe': LE'.
    { split; last done; move: Hu'; move: HLe'=>[t'' <-]. exact: ra_op_valid2. }
    exact: SIDE.
  Qed.

  Lemma ra_fps_auth_canc {HC : Cancellative raT} t {u t'} (Hu' : ↓t' · u) :
    Auth(ex_own(t · u), t) ⇝ Auth(ex_own(t' · u), t').
  Proof.
    apply: ra_fps_auth Hu'.
    move=> Hu tf HLe.
    apply: (ra_op_mono (prefl t')).
    exact: ra_cancel_ord HLe.
  Qed.

  Definition ra_local_action (act : T -=> T) : Prop :=
    forall t tf, ↓act t -> ↓t · tf -> act(t · tf) == act t · tf.

  Lemma ra_fps_auth_local {act t u} (HL : ra_local_action act) (Hu' : ↓act t · u) :
    Auth(ex_own(t · u), t) ⇝ Auth(ex_own(act t · u), act t).
  Proof.
    apply: ra_fps_auth (Hu').
    move/(_ t _ (ra_op_valid Hu')): HL => HL {Hu'}.
    move=> Hu tf [w HEq]; exists w.
    move: HEq; rewrite comm -assoc => HEq; rewrite comm -assoc.
    rewrite -(HL _ Hu).
    move: Hu; rewrite -HEq => Hu; rewrite -(HL _ Hu).
    by reflexivity.
  Qed.
End Authoritative.
Arguments auth : clear implicits.
(*
Notation "• g" := (Auth (ex_own g,1)) (at level 48) : ra_scope.
Notation "∘ t" := (Auth (1,t)) (at level 48) : ra_scope.
*)



Section Agreement.
  Context T `{T_ty : Setoid T} (eq_dec : forall x y, {x == y} + {x =/= y}).
  Local Open Scope ra_scope.

  Inductive ra_res_agree : Type :=
    | ag_bottom
    | ag_unit
    | ag_inj (t : T).

  Global Instance ra_unit_agree : RA_unit _ := ag_unit.
  Global Instance ra_valid_ag : RA_valid _ :=
           fun x => match x with ag_bottom => False | _ => True end.
  Global Instance ra_op_ag : RA_op _ :=
    fun x y => match x, y with
               | ag_inj t1, ag_inj t2 =>
                   if eq_dec t1 t2 is left _ then ag_inj t1 else ag_bottom
               | ag_bottom , y => ag_bottom
               | x , ag_bottom => ag_bottom
               | ag_unit, y => y
               | x, ag_unit => x
             end.

  Definition ra_eq_ag (x : ra_res_agree) (y : ra_res_agree) : Prop :=
    match x,y with
      | ag_inj t1, ag_inj t2 => t1 == t2
      | x, y => x = y
    end.


  Global Instance ra_equivalence_agree : Equivalence ra_eq_ag.
  Proof.
    split; intro; intros; destruct x; try (destruct y; try destruct z); simpl; try reflexivity;
    simpl in *; try inversion H; try inversion H0; try rewrite <- H; try rewrite <- H0; try firstorder.
  Qed.
  Global Instance ra_type_agree : Setoid ra_res_agree := mkType ra_eq_ag.
  Global Instance res_agree : RA ra_res_agree.
  Proof.
    split; repeat intro.
    - repeat (match goal with [ x : ra_res_agree |- _ ] => destruct x end);
      simpl in *; try reflexivity; try rewrite H; try rewrite H0; try reflexivity;
      try inversion H; try inversion H0; compute;
      destruct (eq_dec t2 t0), (eq_dec t1 t); simpl; auto; exfalso;
      [ rewrite <- H, -> e in c | rewrite -> H, -> e in c; symmetry in c]; contradiction.
    - repeat (match goal with [ x : ra_res_agree |- _ ] => destruct x end);
      simpl in *; auto; try reflexivity; compute; try destruct (eq_dec _ _); try reflexivity.
      destruct (eq_dec t0 t), (eq_dec t1 t0), (eq_dec t1 t); simpl; auto; try reflexivity;
      rewrite -> e in e0; contradiction.
    -  destruct t1, t2; try reflexivity; compute; destruct (eq_dec t0 t), (eq_dec t t0);
       try reflexivity; auto; try contradiction; symmetry in e; contradiction.
    - destruct t; reflexivity.
    - destruct x, y; simpl; firstorder; now inversion H.
    - now constructor.
    - destruct t1, t2; try contradiction; now constructor.
  Qed.

End Agreement.


(* PDS: Perhaps we should bake non-expansiveness for · and ↓ into RA, and lift ModuRes products here. *)
Section InfiniteProduct.
  (* I is the index type (domain), S the type of the components (codomain) *)
  Context {I : Type} {S : forall (i : I), Type}
          {tyS : forall i, Setoid (S i)}
          {uS : forall i, RA_unit (S i)}
          {opS : forall i, RA_op (S i)}
          {vS : forall i, RA_valid (S i)}
          {raS : forall i, RA (S i)}.
  Local Open Scope ra_scope.

  Definition ra_res_infprod := forall (i : I), S i.

  Implicit Type (i : I) (f g : ra_res_infprod).

  Definition ra_eq_infprod := fun f g => forall i, f i == g i.
  Global Instance ra_equiv_infprod : Equivalence ra_eq_infprod.
  Proof. split; repeat intro; [ | rewrite (H i) | rewrite -> (H i), (H0 i) ]; reflexivity. Qed.

  Global Instance ra_type_infprod : Setoid ra_res_infprod | 5 := mkType ra_eq_infprod.
  Global Instance ra_unit_infprod : RA_unit ra_res_infprod := fun i => 1.
  Global Instance ra_op_infprod : RA_op ra_res_infprod := fun f g i => f i · g i.
  Global Instance ra_valid_infprod : RA_valid ra_res_infprod := fun f => forall i, ↓ (f i).
  Global Instance ra_infprod : RA ra_res_infprod.
  Proof.
    split; repeat intro.
    - exact: ra_op_proper.
    - compute; now rewrite -> (assoc (T := S i) (t1 i) (t2 i) (t3 i)).
    - compute; now rewrite -> (comm (T :=S i) (t1 i) (t2 i)).
    - compute; now rewrite -> (ra_op_unit (RA := raS i) (t := t i)).
    - compute; intros; split; intros; by move/(_ i): H0; rewrite (H i).
    - now eapply (ra_valid_unit (RA := raS i)).
    - eapply (ra_op_valid (RA := raS i)); now eauto.
  Qed.
End InfiniteProduct.


Section HomogeneousProduct.
  (* I is the index type (domain), S the type of the components (codomain) *)
  Context {I : Type} {S : Type} `{RA S}.

  Global Instance ra_homprod : RA (forall (i : I), S).
  Proof. now eapply ra_infprod; auto. Qed.
End HomogeneousProduct.



(* Package an RA as a module type (for use with other modules). *)
Module Type RA_T.

  Parameter res : Type.
  Declare Instance res_type : Setoid res.
  Declare Instance res_op : RA_op res.
  Declare Instance res_unit : RA_unit res.
  Declare Instance res_valid : RA_valid res.
  Declare Instance res_ra : RA res.

End RA_T.
