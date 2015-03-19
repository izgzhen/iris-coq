(** This file provides the proof that CBUlt, the category of complete,
    bisected, ultrametric spaces, forms an M-category. *)

Require Import CSetoid.
Require Import MetricCore CatBasics MetricRec.

Module CBUlt <: MCat.
  Local Open Scope cat_scope.
  Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

  Definition M := cmtyp.
  Instance MArr   : BC_morph M := fun U V : cmtyp => cmfromType (U -n> V).
  Instance MComp  : BC_comp  M := fun U V W => comp.
  Instance MId    : BC_id    M := fun U => (umid _).
  Instance MTermO : BC_term  M := cmfromType unit.
  Program Instance MTermA : BC_terminal M := fun U => n[(const tt)].

  Instance Cat : BaseCat M.
  Proof.
    split; intros; intros n; simpl; reflexivity || exact I.
  Qed.

  Section Limits.
    Context (T : Tower).

    Definition guard := fun (σ : forall i, tow_objs T i) => forall n, tow_morphs T n (σ (S n)) == σ n.
    Instance lpg : LimitPreserving guard.
    Proof.
      intros σ σc HG n.
      rewrite !dep_chain_compl.
      rewrite nonexp_continuous; apply umet_complete_ext; intros k.
      simpl; apply HG.
    Qed.

    Definition lim_obj : cmtyp := cmfromType {σ : forall i, tow_objs T i | guard σ}.
    Definition lim_proj i : lim_obj -n> tow_objs T i := MprojI i <M< inclM.

    Program Definition lim_cone : Cone T := mkBaseCone T lim_obj lim_proj _.
    Next Obligation.
      intros [σ HG]; simpl; apply HG.
    Qed.

    Program Definition lim_map (C : Cone T) : (cone_t T C : cmtyp) -n> (cone_t T lim_cone : cmtyp) :=
      n[(fun m => exist _ (fun i => cone_m T C i m) _)].
    Next Obligation.
      intros n; simpl.
      assert (HT := cone_m_com T C n m); apply HT.
    Qed.

    Lemma AllLimits : Limit T.
    Proof.
      refine (mkBaseLimit T lim_cone lim_map _ _).
      + intros C n x; simpl; reflexivity.
      + intros C h HCom x n; simpl.
        specialize (HCom n x); simpl in HCom.
        symmetry; apply HCom.
    Qed.

  End Limits.
End CBUlt.

(* We can use the halve operation as functor *)
Section Halving_Fun.
  Context F {FA : BiFMap F} {FFun : BiFunctor F}.
  Local Obligation Tactic := intros; resp_set || eauto.

  Program Instance halveFMap : BiFMap (fun T1 T2 => halve (F T1 T2)) :=
    fun m1 m2 m3 m4 => lift2m (lift2s (fun ars ob => fmorph (F := F) ars ob) _ _) _ _.
  Next Obligation.
    intros p1 p2 EQp x; simpl; rewrite EQp; reflexivity.
  Qed.
  Next Obligation.
    intros e1 e2 EQ; simpl. unhalve.
    rewrite EQ; reflexivity.
  Qed.
  Next Obligation.
    intros p1 p2 EQ e; simpl; unhalve.
    apply dist_mono in EQ.
    rewrite EQ; reflexivity.
  Qed.

  Instance halveF : BiFunctor (fun T1 T2 => halve (F T1 T2)).
  Proof.
    split; intros.
    + intros T; simpl.
      apply (fmorph_comp _ _ _ _ _ _ _ _ _ _ T).
    + intros T; simpl.
      apply (fmorph_id _ _ T).
  Qed.

  Instance halve_contractive {m0 m1 m2 m3} :
    contractive (@fmorph _ _ (fun T1 T2 => halve (F T1 T2)) _ m0 m1 m2 m3).
  Proof.
    intros n p1 p2 EQ f; simpl.
    change ((fmorph (F := F) p1) f = n = (fmorph p2) f).
    rewrite EQ; reflexivity.
  Qed.

End Halving_Fun.

Module Type SimplInput(Cat : MCat).
  Import Cat.

  Parameter F : M -> M -> M.
  Parameter FArr : BiFMap F.
  Parameter FFun : BiFunctor F.

  Parameter F_ne : (1 -t> F 1 1)%cat.
End SimplInput.

Module InputHalve (S : SimplInput (CBUlt)) : InputType(CBUlt)
    with Definition F := fun T1 T2 => halve (S.F T1 T2).
  Import CBUlt.
  Local Existing Instance S.FArr.
  Local Existing Instance S.FFun.
  Local Open Scope cat_scope.

  Definition F T1 T2 := halve (S.F T1 T2).
  Definition FArr := halveFMap S.F.
  Definition FFun := halveF S.F.

  Definition tmorph_ne : 1 -t> F 1 1 :=
    umconst (S.F_ne tt : F 1 1).

  Definition F_contractive := @halve_contractive S.F _.
End InputHalve.
