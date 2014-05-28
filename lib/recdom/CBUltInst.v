(** This file provides the proof that CBUlt, the category of complete,
    bisected, ultrametric spaces, forms an M-category. *)

Require Import MetricCore.
Require Import MetricRec.

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
