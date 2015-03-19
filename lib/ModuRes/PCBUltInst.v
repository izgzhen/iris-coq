(** This module provides the proof that PCBUlt, the category of
    pre-ordered, complete, bisected ultrametric spaces, forms an
    M-category. *)

Require Import PreoMet.
Require Import CatBasics MetricRec.

Module PCBUlt <: MCat.
  Local Obligation Tactic := intros; resp_set || mono_resp || eauto with typeclass_instances.

  Definition M := pcmtyp.
  Instance MArr   : BC_morph M := fun U V => pcmFromType (U -m> V).
  Program Instance MComp  : BC_comp M := fun U V W => lift2m (lift2s pcomp _ _) _ _.
  Instance MId    : BC_id M := fun T => pid T.
  Local Instance unit_preo : preoType unit := disc_preo unit.
  Local Instance unit_pcm  : pcmType unit := disc_pcm unit.
  Instance MTermO : BC_term M := pcmFromType unit.
  Program Instance MTermA : BC_terminal M := fun U => m[(const tt)].

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

    Program Definition lim_obj : pcmtyp := pcmFromType {σ : forall i, tow_objs T i | guard σ}.

    Definition lim_proj i : lim_obj -m> tow_objs T i := (pcmProjI i ∘ muincl)%pm.

    Program Definition lim_cone : Cone T := mkBaseCone T lim_obj lim_proj _.
    Next Obligation.
      intros [σ HG]; simpl; apply HG.
    Qed.

    Program Definition lim_map (C : Cone T) : (cone_t T C : pcmtyp) -m> (cone_t T lim_cone : pcmtyp) :=
      m[(fun m => exist _ (fun i => cone_m T C i m) _)].
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
End PCBUlt.
