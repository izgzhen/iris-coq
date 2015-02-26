Require Export Coq.Program.Program.
Require Import CSetoid.

Generalizable Variables T U V W.

Class preoType T :=
  {pord   :  relation T;
   preoPO :> PreOrder pord}.

Arguments pord {_ _} _ _ /.
Notation "'mkPOType' R" := (Build_preoType _ R _) (at level 10).
Notation "s ⊑ t" := (pord s t) (at level 70, no associativity) : predom_scope.
Delimit Scope predom_scope with pd.

Record preotyp :=
  {ptyp   :> Type;
   pprTyp :  preoType ptyp}.
Instance preotyp_pTyp {T : preotyp} : preoType T := pprTyp T.

Ltac mono_resp :=
  intros t1 t2 HSub; repeat (intros ?); rewrite ?HSub; simpl in *; rewrite ?HSub; repeat split; reflexivity.

Section Monotone_Morphisms.
  Local Open Scope predom_scope.

  Record monotone_morphism T U `{pT : preoType T} `{pU : preoType U} := mkMMorph
    { mono_morph :> T -> U;
      mono_mono  :  Proper (pord ++> pord) mono_morph}.

End Monotone_Morphisms.

Global Arguments mkMMorph [T U] {pT pU} _ _.
Notation "T -m> U" := (monotone_morphism T U) (at level 45, right associativity) : predom_scope.

Section MMorphProps1.
  Local Open Scope predom_scope.
  Context `{pT : preoType T} `{pU : preoType U} `{pV : preoType V} `{pW : preoType W}.

  Global Program Instance mon_morph_preoT : preoType (T -m> U) :=
    mkPOType (fun f g => forall x, f x ⊑ g x).
  Next Obligation.
    split.
    - intros f x; reflexivity.
    - intros f g h Hfg Hgh x; etransitivity; [apply Hfg | apply Hgh].
  Qed.

  Global Instance pord_mono :
    Proper (pord ==> pord ==> pord) (mono_morph T U).
  Proof.
    intros f g HSub x y HSub'; etransitivity; [apply HSub | apply g, HSub'].
  Qed.

  Program Definition mmcomp (f : U -m> V) (g : T -m> U) : T -m> V :=
    mkMMorph (fun x => f (g x)) _.
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
    intros f f' HSubf g g' HSubg x; simpl; rewrite HSubf, HSubg; reflexivity.
  Qed.

  Lemma mmcompAL (f: V -m> W) (g: U -m> V) (h: T -m> U) :
    f ∘ (g ∘ h) ⊑ f ∘ g ∘ h.
  Proof. intros x; reflexivity. Qed.

  Lemma mmcompAR (f: V -m> W) (g: U -m> V) (h: T -m> U) :
    f ∘ g ∘ h ⊑ f ∘ (g ∘ h).
  Proof. intros x; reflexivity. Qed.

  Definition lift2m (f : T -> U -> V) p q : T -m> U -m> V :=
    mkMMorph (fun x => mkMMorph (f x) (p x)) q.

End MMorphProps2.

Section MonotoneProducts.
  Local Open Scope predom_scope.
  Context `{pT : preoType T} `{pU : preoType U} `{pV : preoType V}.

  Definition prod_ord (p1 p2 : U * V) := (fst p1 ⊑ fst p2) /\ (snd p1 ⊑ snd p2).

  Global Program Instance preoType_prod : preoType (U * V) := mkPOType prod_ord.
  Next Obligation.
    split.
    - intros [a b]; split; simpl; reflexivity.
    - intros [a1 b1] [a2 b2] [a3 b3] [Ha12 Hb12] [Ha13 Hb13]; split; simpl;
      etransitivity; eassumption.
  Qed.

  Global Instance mprod_proper : Proper (pord ==> pord ==> pord) (@pair U V).
  Proof.
    intros a a' Ha b b' Hb; split; assumption.
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

  Definition mfst : (U * V) -m> U := mkMMorph (@fst U V) _.
  Definition msnd : (U * V) -m> V := mkMMorph (@snd U V) _.

  Program Definition mprod (f: T -m> U) (g: T -m> V) : T -m> (U * V) :=
    mkMMorph (fun c => (f c, g c)) _.

  Lemma mprod_unique (f: T -m> U) (g: T -m> V) (h: T -m> U * V) :
    mfst ∘ h ⊑ f -> msnd ∘ h ⊑ g -> h ⊑ mprod f g.
  Proof.
    intros HL HR x; split; simpl; [rewrite <- HL | rewrite <- HR]; reflexivity.
  Qed.

End MonotoneProducts.

Global Arguments prod_ord {_ _ _ _} _ _ /.
Notation "〈 f , g 〉" := (mprod f g) : predom_scope.

Section IndexedProducts.
  Local Open Scope predom_scope.
  Context {I : Type} {P : I -> preotyp}.

  Definition ordI (f1 f2 : forall i, P i) := forall i, f1 i ⊑ f2 i.

  Global Program Instance ordTypeI : preoType (forall i, P i) := mkPOType ordI.
  Next Obligation.
    split.
    + intros f i; reflexivity.
    + intros f g h Hfg Hgh i; etransitivity; [apply Hfg | apply Hgh].
  Qed.

  Program Definition ordProjI (i : I) : (forall i, P i) -m> P i :=
    mkMMorph (fun X => X i) _.
  Next Obligation. intros x y HSub; apply HSub. Qed.

  Context `{pT : preoType T}.
  Program Definition ordProdI (f : forall i, T -m> P i) : T -m> forall i, P i :=
    mkMMorph (fun c i => f i c) _.
  Next Obligation. intros x y HSub i; simpl; apply f; assumption. Qed.

  Lemma ordProdI_proj f i : ordProjI i ∘ ordProdI f ⊑ f i.
  Proof. intros x; reflexivity. Qed.
  Lemma ordProdI_proj_rev f i : f i ⊑ ordProjI i ∘ ordProdI f.
  Proof. intros x; reflexivity. Qed.

  Lemma ordProdI_unique f g (HEq : forall i, ordProjI i ∘ g ⊑ f i) : g ⊑ ordProdI f.
  Proof. intros x i; apply (HEq i x). Qed.

  Lemma ordProdI_unique_rev f g (HEq : forall i, f i ⊑ ordProjI i ∘ g) : ordProdI f ⊑ g.
  Proof. intros x i; apply (HEq i x). Qed.

End IndexedProducts.

Global Arguments ordI {_ _} _ _ /.

Section Extras.
  Local Open Scope predom_scope.
  Local Obligation Tactic := intros; mono_resp || eauto.
  Context `{pT : preoType T} `{pU : preoType U} `{pV : preoType V} `{pW : preoType W}.

  Definition mprod_map (f : T -m> U) (g : V -m> W) := 〈f ∘ mfst, g ∘ msnd〉.
  Program Definition mid : T -m> T := mkMMorph (fun x => x) _.
  Program Definition mconst u : U -m> T := mkMMorph (const u) _.

End Extras.

Arguments mid T {_}.
Notation "f × g" := (mprod_map f g) (at level 40, left associativity) : predom_scope.

Section MonoExponentials.
  Local Open Scope predom_scope.
  Local Obligation Tactic := intros; mono_resp || eauto.
  Context `{pT : preoType T} `{pU : preoType U} `{pV : preoType V} `{pW : preoType W}.

  Program Definition muncurry (f : T -m> U -m> V) : T * U -m> V :=
    mkMMorph (fun p => f (fst p) (snd p)) _.

  Program Definition mcurry (f : T * U -m> V) : T -m> U -m> V :=
    lift2m (fun a b => f (a, b)) _ _.

  Program Definition meval : (T -m> U) * T -m> U :=
    mkMMorph (fun p => fst p (snd p)) _.

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
  Proof. intros HEq a b; simpl; rewrite HEq; reflexivity. Qed.

  Lemma mcurry_uniqeR (f : T * U -m> V) h :
    meval ∘ (h × mid _) ⊑ f -> h ⊑ mcurry f.
  Proof. intros HEq a b; simpl; rewrite <- HEq; reflexivity. Qed.

End MonoExpProps.

Section SubPredom.
  Local Open Scope predom_scope.
  Local Obligation Tactic := intros; mono_resp || eauto.
  Context `{eT : preoType T} {P : T -> Prop}.

  Definition subset_ord (x y : {t : T | P t}) := proj1_sig x ⊑ proj1_sig y.
  Arguments subset_ord _ _ /.
  Global Program Instance subset_preo : preoType {a : T | P a} := mkPOType subset_ord.
  Next Obligation.
    split.
    - intros [x Hx]; red; simpl; reflexivity.
    - intros [x Hx] [y Hy] [z Hz] Hxy Hyz; red; simpl;
      etransitivity; [apply Hxy | apply Hyz].
  Qed.

  Global Instance proj1sig_proper :
    Proper (pord (T := {t : T | P t}) ==> pord) (@proj1_sig T P).
  Proof. intros [x Hx] [y Hy] HEq; simpl; apply HEq. Qed.

  Program Definition mforget : {a : T | P a} -m> T :=
    mkMMorph (fun x => x) _.

  Context `{eU : preoType U}.
  Program Definition minherit (f : U -m> T) (HB : forall b, P (f b)) : U -m> {a : T | P a} :=
    mkMMorph (fun b => exist P (f b) (HB b)) _.

  Lemma mforget_mono (f g : U -m> {a : T | P a}) : mforget ∘ f ⊑ mforget ∘ g -> f ⊑ g.
  Proof.
    intros HEq x; red; simpl; rewrite (HEq x); reflexivity.
  Qed.

End SubPredom.

Global Arguments subset_ord {_ _ _} _ _ /.