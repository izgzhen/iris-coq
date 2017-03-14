(** An axiomatization of languages based on evaluation context items, including
    a proof that these are instances of general ectx-based languages. *)
From iris.algebra Require Export base.
From iris.program_logic Require Import language ectx_language.
Set Default Proof Using "Type".

(* We need to make thos arguments indices that we want canonical structure
   inference to use a keys. *)
Class EctxiLanguage (expr val ectx_item state : Type) := {
  of_val : val → expr;
  to_val : expr → option val;
  fill_item : ectx_item → expr → expr;
  head_step : expr → state → expr → state → list expr → Prop;

  to_of_val v : to_val (of_val v) = Some v;
  of_to_val e v : to_val e = Some v → of_val v = e;
  val_stuck e1 σ1 e2 σ2 efs : head_step e1 σ1 e2 σ2 efs → to_val e1 = None;

  fill_item_inj Ki :> Inj (=) (=) (fill_item Ki);
  fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e);
  fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2;

  head_ctx_step_val Ki e σ1 e2 σ2 efs :
    head_step (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_val e);
}.

Arguments of_val {_ _ _ _ _} _.
Arguments to_val {_ _ _ _ _} _.
Arguments fill_item {_ _ _ _ _} _ _.
Arguments head_step {_ _ _ _ _} _ _ _ _ _.

Arguments to_of_val {_ _ _ _ _} _.
Arguments of_to_val {_ _ _ _ _} _ _ _.
Arguments val_stuck {_ _ _ _ _} _ _ _ _ _ _.
Arguments fill_item_val {_ _ _ _ _} _ _ _.
Arguments fill_item_no_val_inj {_ _ _ _ _} _ _ _ _ _ _ _.
Arguments head_ctx_step_val {_ _ _ _ _} _ _ _ _ _ _ _.
Arguments step_by_val {_ _ _ _ _} _ _ _ _ _ _ _ _ _ _ _.

Section ectxi_language.
  Context {expr val ectx_item state}
          {Λ : EctxiLanguage expr val ectx_item state}.
  Implicit Types (e : expr) (Ki : ectx_item).
  Notation ectx := (list ectx_item).

  Definition fill (K : ectx) (e : expr) : expr := foldl (flip fill_item) e K.

  Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
  Proof. apply foldl_app. Qed.

  Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. induction K as [|Ki K IH]; rewrite /Inj; naive_solver. Qed.

  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof.
    revert e.
    induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val.
  Qed.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  (* When something does a step, and another decomposition of the same expression
  has a non-val [e] in the hole, then [K] is a left sub-context of [K'] - in
  other words, [e] also contains the reducible expression *)
  Lemma step_by_val K K' e1 e1' σ1 e2 σ2 efs :
    fill K e1 = fill K' e1' → to_val e1 = None → head_step e1' σ1 e2 σ2 efs →
    exists K'', K' = K'' ++ K. (* K `prefix_of` K' *)
  Proof.
    intros Hfill Hred Hstep; revert K' Hfill.
    induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
    destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
    { rewrite fill_app in Hstep.
      exfalso; apply (eq_None_not_Some (to_val (fill K e1)));
        eauto using fill_not_val, head_ctx_step_val. }
    rewrite !fill_app /= in Hfill.
    assert (Ki = Ki') as ->
      by eauto using fill_item_no_val_inj, val_stuck, fill_not_val.
    simplify_eq. destruct (IH K') as [K'' ->]; auto.
    exists K''. by rewrite assoc.
  Qed.

  Global Program Instance ectxi_lang_ectx : EctxLanguage expr val ectx state := {|
    ectx_language.of_val := of_val; ectx_language.to_val := to_val;
    empty_ectx := []; comp_ectx := flip (++); ectx_language.fill := fill;
    ectx_language.head_step := head_step |}.
  Solve Obligations with simpl; eauto using to_of_val, of_to_val, val_stuck,
    fill_not_val, fill_app, step_by_val, foldl_app.
  Next Obligation. intros K1 K2 ?%app_eq_nil; tauto. Qed.

  Lemma ectxi_language_sub_values e :
    (∀ Ki e', e = fill_item Ki e' → is_Some (to_val e')) → sub_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
    intros []%eq_None_not_Some. eapply fill_val, Hsub. by rewrite /= fill_app.
  Qed.

  Global Instance ectxi_lang_ctx_item Ki :
    LanguageCtx (ectx_lang expr) (fill_item Ki).
  Proof. change (LanguageCtx _ (fill [Ki])). apply _. Qed.
End ectxi_language.
