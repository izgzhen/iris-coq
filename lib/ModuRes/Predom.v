Require Import ssreflect.
Require Export Coq.Program.Program.
Require Import CSetoid.

Generalizable Variables T U V W.

Class preoType T {eqT : Setoid T} :=
  {pord   :  relation T;
   preoPO :> PreOrder pord;
   preoC  :> Proper (equiv ==> equiv ==> impl) pord}.

(** Rewriting under pord. *)
Instance preoType_compat T `{pT : preoType T} : Proper (equiv ==> equiv ==> iff) pord.
Proof.
  split; first by exact: preoC.
  symmetry in H, H0.
  exact: preoC.
Qed.

Arguments pord {_ _ _} !_ !_.
Notation "'mkPOType' R" := (Build_preoType _ _ R _) (at level 10).
Notation "s ⊑ t" := (pord s t) (at level 70, no associativity) : predom_scope.
Delimit Scope predom_scope with pd.

Ltac mono_resp :=
  intros t1 t2 HSub; repeat (intros ?); rewrite -> ?HSub; simpl in *; rewrite -> ?HSub; repeat split; reflexivity.

Section Monotone_Morphisms.
  Local Open Scope predom_scope.

  Record monotone_morphism T U `{pT : preoType T} `{pU : preoType U} := mkMMorph
    { mono_morph :> T -=> U;
      mono_mono  :  Proper (pord ++> pord) mono_morph}.

End Monotone_Morphisms.

Global Arguments mkMMorph [T U] {_ pT _ pU} _ _.
Arguments mono_mono {_ _} {_ _ _ _} _ {_ _} _.

Notation "T -m> U" := (monotone_morphism T U) (at level 45, right associativity) : predom_scope.

Section MMorphProps1.
  Local Open Scope predom_scope.
  Context `{pT : preoType T} `{pU : preoType U} `{pV : preoType V} `{pW : preoType W}.
  Implicit Types (t : T) (f : T -m> U).
  
  (* PDS: It seems strange to have to repeat the point-wise equivalence yet again. *)
  Let mon_morph_eq f1 f2 : Prop := forall t, f1 t == f2 t.
  Global Instance equiv_mon_morph : Equivalence mon_morph_eq.
  Proof.
    split.
    - move=> f t. by reflexivity.
    - move=> f1 f2 EQf t. by symmetry.
    - move=> f1 f2 f3 EQ12 EQ23 t. by transitivity (f2 t).
  Qed.
  Global Instance mon_morph_type : Setoid (T -m> U) := mkType mon_morph_eq.

  Global Program Instance mon_morph_preoT : preoType (T -m> U) :=
    mkPOType (fun f g => forall x, f x ⊑ g x) _.
  Next Obligation.
    split.
    - intros f x; reflexivity.
    - intros f g h Hfg Hgh x; etransitivity; [apply Hfg | apply Hgh].
  Qed.
  Next Obligation.
    move=> f1 f2 EQf f'1 f'2 EQf' HLe t.
    by rewrite -(EQf t) -(EQf' t).
  Qed.
    
  Global Instance pord_mono :
    Proper (pord ==> pord ==> pord) (mono_morph T U).
  Proof.
    intros f g HSub x y HSub'; etransitivity; [apply HSub | apply g, HSub'].
  Qed.

  Program Definition mmcomp (f : U -m> V) (g : T -m> U) : T -m> V :=
    mkMMorph (f << g) _.
  Next Obligation.
    intros x y Hxy; now apply f, g.
  Qed.

End MMorphProps1.

Notation "f ∘ g" := (mmcomp f g) (at level 40, left associativity) : predom_scope.

Section MMorphProps2.
  Local Open Scope predom_scope.
  Context `{pT : preoType T} `{pU : preoType U} `{pV : preoType V} `{pW : preoType W}.

  Global Instance pord_mmcomp :
    Proper (pord (T := T -m> U) ==> pord ==> pord) mmcomp.
  Proof.
    intros f1 f2 Hf g1 g2 Hg t; simpl; rewrite -> (Hf _); now apply mono_mono.
  Qed.

  Lemma mmcompAL (f: V -m> W) (g: U -m> V) (h: T -m> U) :
    f ∘ (g ∘ h) ⊑ f ∘ g ∘ h.
  Proof. intros x; reflexivity. Qed.

  Lemma mmcompAR (f: V -m> W) (g: U -m> V) (h: T -m> U) :
    f ∘ g ∘ h ⊑ f ∘ (g ∘ h).
  Proof. intros x; reflexivity. Qed.

  Program Definition lift2m (f : T -=> U -=> V) p q : T -m> U -m> V :=
    (mkMMorph (mkMorph (fun t : T => mkMMorph (f t) (p t)) _) q).
  Next Obligation.
    move=> t1 t2 EQt u /=; rewrite EQt; reflexivity.
  Qed.

End MMorphProps2.

Section MonotoneProducts.
  Local Open Scope predom_scope.
  Context `{pT : preoType T} `{pU : preoType U} `{pV : preoType V}.

  Definition prod_ord (p1 p2 : U * V) := (fst p1 ⊑ fst p2) /\ (snd p1 ⊑ snd p2).

  Global Program Instance preoType_prod : preoType (U * V) := mkPOType prod_ord _.
  Next Obligation.
    split.
    - intros [a b]; split; simpl; reflexivity.
    - intros [a1 b1] [a2 b2] [a3 b3] [Ha12 Hb12] [Ha13 Hb13]; split; simpl;
      etransitivity; eassumption.
  Qed.
  Next Obligation.
    move=> [u1 v1] [u2 v2] [/= EQu EQv] [u'1 v'1] [u'2 v'2] [/= EQu' EQv'] [/= LEu LEv]; split.
    - by rewrite -EQu -EQu'.
    - by rewrite -EQv -EQv'.
  Qed.

  Global Instance mprod_proper : Proper (pord ==> pord ==> pord) (@pair U V).
  Proof.
    intros a a' Ha b b' Hb; split; assumption.
  Qed.

  (** The next two are redundant, but speed up rewriting. *)
  Global Instance mprod_compat_fst : Proper (equiv ==> pord ==> pord) (@pair U V).
  Proof.
    move=> u1 u2 Ru v1 v2 Rv; split; last done.
    by rewrite Ru; reflexivity.
  Qed.

  Global Instance mprod_compat_snd : Proper (pord ==> equiv ==> pord) (@pair U V).
  Proof.
    move=> u1 u2 Ru v1 v2 Rv; split; first done.
    by rewrite Rv; reflexivity.
  Qed.

  Global Instance mmfst_proper : Proper (pord ==> pord) (@fst U V).
  Proof.
    intros [a1 b1] [a2 b2] [Ha Hb]; assumption.
  Qed.

  Global Instance msnd_proper : Proper (pord ==> pord) (@snd U V).
  Proof.
    intros [a1 b1] [a2 b2] [Ha Hb]; assumption.
  Qed.

  Local Obligation Tactic := intros; try mono_resp.

  Definition mfst : (U * V) -m> U := mkMMorph mfst _.
  Definition msnd : (U * V) -m> V := mkMMorph msnd _.

  Program Definition mprod (f: T -m> U) (g: T -m> V) : T -m> (U * V) :=
    mkMMorph (mprod f g) _.
  Next Obligation.
    move=> t1 t2 Ht; split; exact: mono_mono Ht.
  Qed.

  Lemma mprod_unique (f: T -m> U) (g: T -m> V) (h: T -m> U * V) :
    mfst ∘ h ⊑ f -> msnd ∘ h ⊑ g -> h ⊑ mprod f g.
  Proof.
    move=> HL HR x; split; [exact: HL | exact: HR].
  Qed.

End MonotoneProducts.

Section ProdTests.
  Local Open Scope predom_scope.
  Context `{pT : preoType T} `{pU : preoType U}.
  Implicit Types (t : T) (u : U).

  (*
   * Aside: The numbers count lines of
   *
   *	 Typeclasses eauto := debug.
   *
   * output before and after defining mprod_compat_{fst,snd}. (These
   * searches are worth speeding up. Iris uses pairs of resources.)
   *)
  Goal forall t1 t2 u, t1 == t2 -> (t1,u) ⊑ (t2,u).
  Proof. move=> t1 t2 u ->. reflexivity. Qed.	(* ~950 -> ~50 *)

  Goal forall t u1 u2, u1 == u2 -> (t,u1) ⊑ (t,u2).
  Proof. move=> t u1 u2 ->. reflexivity. Qed.	(* ~950 -> 50 *)

  Goal forall t1 t2 u1 u2, t1 == t2 -> u1 == u2 -> (t1,u1) ⊑ (t2,u2).
  Proof. move=> t1 t2 u1 u2 -> ->. reflexivity. Qed.	(* ~4,700 -> ~120 *)
End ProdTests.

Global Arguments prod_ord {_ _ _ _ _ _} _ _ /.
Notation "〈 f , g 〉" := (mprod f g) : predom_scope.


Section Extras.
  Local Open Scope predom_scope.
  Local Obligation Tactic := intros; mono_resp || eauto.
  Context `{pT : preoType T} `{pU : preoType U} `{pV : preoType V} `{pW : preoType W}.

  Definition mprod_map (f : T -m> U) (g : V -m> W) := 〈f ∘ mfst, g ∘ msnd〉.
  Program Definition mid : T -m> T := mkMMorph (mid T) _.
  Program Definition mconst u : U -m> T := mkMMorph (mconst u) _.

End Extras.

Arguments mid T {_ _}.
Notation "f × g" := (mprod_map f g) (at level 40, left associativity) : predom_scope.

Section MonoExponentials.
  Local Open Scope predom_scope.
  Local Obligation Tactic := intros; mono_resp || eauto.
  Context `{pT : preoType T} `{pU : preoType U} `{pV : preoType V} `{pW : preoType W}.

  Program Definition muncurry (f : T -m> U -m> V) : T * U -m> V :=
    mkMMorph s[(fun p => f (fst p) (snd p))] _.
  Next Obligation.
    move=> [t1 u1] [t2 u2] [/= Ht ->].
    exact: (morph_resp (mono_morph _ _ f)).
  Qed.
  Next Obligation.
    move=> [t1 u1] [t2 u2] [/= Ht Hu].
    transitivity (f t2 u1).
    - exact: (mono_mono f Ht).
    - exact: (mono_mono (f t2) Hu).
  Qed.

  Program Definition mcurry (f : T * U -m> V) : T -m> U -m> V :=
    lift2m (mcurry f) _ _.
  Next Obligation.
    move=> u1 u2 Ru.
    apply: (mono_mono f).
    split; [by reflexivity | done].
  Qed.
  Next Obligation.
    move=> t1 t2 Rt u.
    apply: (mono_mono f).
    split; [done | by reflexivity].
  Qed.
  
  Program Definition meval : (T -m> U) * T -m> U :=
    mkMMorph s[(fun p => fst p (snd p))] _.
  Next Obligation.
    move=> [f1 t1] [f2 t2] [/= Rf Rt].
    by rewrite (Rf t1) Rt; reflexivity.
  Qed.
  Next Obligation.
    move=> [f1 t1] [f2 t2] [/= Rf Rt].
    transitivity (f2 t1); [exact: Rf | exact: mono_mono].
  Qed.

End MonoExponentials.

Section MonoExpProps.
  Local Open Scope predom_scope.
  Local Obligation Tactic := intros; mono_resp || eauto.
  Context `{pT : preoType T} `{pU : preoType U} `{pV : preoType V} `{pW : preoType W}.

  Lemma mcurry_comL (f : T * U -m> V) : f ⊑ meval ∘ (mcurry f × mid _).
  Proof. intros [a b]; reflexivity. Qed.

  Lemma mcurry_comR (f : T * U -m> V) : meval ∘ (mcurry f × mid _) ⊑ f.
  Proof. intros [a b]; reflexivity. Qed.

  Lemma mcurry_uniqeL (f : T * U -m> V) h :
    f ⊑ meval ∘ (h × mid _) -> mcurry f ⊑ h.
  Proof.
    move=> HEq a b; exact: HEq.
  Qed.

  Lemma mcurry_uniqeR (f : T * U -m> V) h :
    meval ∘ (h × mid _) ⊑ f -> h ⊑ mcurry f.
  Proof.
    move=> HEq a b; exact: (HEq (a,b)).
  Qed.

End MonoExpProps.

Section SubPredom.
  Local Open Scope predom_scope.
  Local Obligation Tactic := intros; mono_resp || eauto.
  Context `{eT : preoType T} {P : T -> Prop}.

  Definition subset_ord (x y : {t : T | P t}) := proj1_sig x ⊑ proj1_sig y.
  Arguments subset_ord _ _ /.
  Global Program Instance subset_preo : preoType {a : T | P a} := mkPOType subset_ord _.
  Next Obligation.
    split.
    - intros [x Hx]; red; simpl; reflexivity.
    - intros [x Hx] [y Hy] [z Hz] Hxy Hyz; red; simpl;
      etransitivity; [apply Hxy | apply Hyz].
  Qed.
  Next Obligation.
    move=> x1 x2 EQx y1 y2 EQy.
    by rewrite /subset_ord EQx EQy.
  Qed.
    
  Global Instance proj1sig_proper :
    Proper (pord (T := {t : T | P t}) ==> pord) (@proj1_sig T P).
  Proof. intros [x Hx] [y Hy] HEq; simpl; apply HEq. Qed.

  Program Definition mforget : {a : T | P a} -m> T :=
    mkMMorph mincl _.

  Context `{eU : preoType U}.
  Program Definition minherit (f : U -m> T) (HB : forall b, P (f b)) : U -m> {a : T | P a} :=
    mkMMorph (minherit f HB) _.
  Next Obligation.
    move=> u1 u2 Ru; exact: mono_mono.
  Qed.
    
  Lemma mforget_mono (f g : U -m> {a : T | P a}) : mforget ∘ f ⊑ mforget ∘ g -> f ⊑ g.
  Proof.
    intros HEq x; red; simpl; rewrite -> (HEq x); reflexivity.
  Qed.

End SubPredom.

Global Arguments subset_ord {_ _ _ _} _ _ /.

(** Preorders on option types.

    Caution: this is *one* of the ways to define the order, and not necessarily the only useful.
    Thus, the instances are local, and should be declared w/ Existing Instance where needed. *)
Section Option.
  Context `{pcV : preoType V}.

  (* The preorder on options where None is the bottom element. *)
  Section Bot.

    Definition option_pord_bot (o1 o2 : option V) :=
      match o1 with
        | None => True
        | Some v1 => match o2 with
                       | None => False
                       | Some v2 => pord v1 v2
                     end
      end.
    Program Instance option_preo_bot : preoType (option V) := mkPOType option_pord_bot _.
    Next Obligation.
      split.
      - intros [v |]; simpl; [reflexivity | exact I].
      - intros [v1 |] [v2 |] [v3 |] Sub12 Sub23; simpl in *; try exact I || contradiction; [].
        etransitivity; eassumption.
    Qed.
    Next Obligation.
      move=> x1 x2 Rx y1 y2 Ry; move: Rx Ry.
      case: x1=>[x1|]; case: x2=>[x2|] //= Rx.
      case: y1=>[y1|]; case: y2=>[y2|] //= Ry; last done.
      by rewrite Rx Ry; reflexivity.
    Qed.

  End Bot.

  (* And the preorder, where None is a top element *)
  Section Top.

    Definition option_pord_top (o1 o2 : option V) :=
      match o2 with
        | None => True
        | Some v2 => match o1 with
                       | None => False
                       | Some v1 => pord v1 v2
                     end
      end.
    Program Instance option_preo_top : preoType (option V) := mkPOType option_pord_top _.
    Next Obligation.
      split.
      - intros [v |]; simpl; [reflexivity | exact I].
      - intros [v1 |] [v2 |] [v3 |] Sub12 Sub23; simpl in *; try exact I || contradiction; [].
        etransitivity; eassumption.
    Qed.
    Next Obligation.
      move=> x1 x2 Rx y1 y2 Ry; move: Rx Ry.
      case: x1=>[x1|]; case: x2=>[x2|] //= Rx;
      case: y1=>[y1|]; case: y2=>[y2|] //= Ry; last done.
      rewrite Rx Ry; by reflexivity.
    Qed.
      
  End Top.

End Option.


Section ViewLemmas.
  Context {T} `{oT : preoType T}.
  Implicit Types (t : T).
  Local Open Scope predom_scope.

  Lemma prefl t : t ⊑ t.
  Proof. by reflexivity. Qed.
  
  Lemma ptrans {t1 t2 t3} (HL : t1 ⊑ t2) (HU : t2 ⊑ t3) : t1 ⊑ t3.
  Proof. by transitivity t2. Qed.
End ViewLemmas.
