(** An axiomatization of languages based on evaluation context items, including
    a proof that these are instances of general ectx-based languages. *)
From iris.algebra Require Export base.
From iris.program_logic Require Import language ectx_language.

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

  Definition fill (K : ectx) (e : expr) : expr := fold_right fill_item e K.

  Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. red; induction K as [|Ki K IH]; naive_solver. Qed.

  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof.
    induction K; simpl; first done. intros ?%fill_item_val. eauto.
  Qed.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  (* When something does a step, and another decomposition of the same expression
  has a non-val [e] in the hole, then [K] is a left sub-context of [K'] - in
  other words, [e] also contains the reducible expression *)
  Lemma step_by_val K K' e1 e1' σ1 e2 σ2 efs :
    fill K e1 = fill K' e1' → to_val e1 = None → head_step e1' σ1 e2 σ2 efs →
    exists K'', K' = K ++ K''. (* K `prefix_of` K' *)
  Proof.
    intros Hfill Hred Hnval; revert K' Hfill.
    induction K as [|Ki K IH]; simpl; intros K' Hfill; first by eauto.
    destruct K' as [|Ki' K']; simplify_eq/=.
    { exfalso; apply (eq_None_not_Some (to_val (fill K e1)));
      eauto using fill_not_val, head_ctx_step_val. }
    cut (Ki = Ki'); [naive_solver eauto using prefix_of_cons|].
    eauto using fill_item_no_val_inj, val_stuck, fill_not_val.
  Qed.

  Global Program Instance : EctxLanguage expr val ectx state :=
    (* For some reason, Coq always rejects the record syntax claiming I
       fixed fields of different records, even when I did not. *)
    Build_EctxLanguage expr val ectx state of_val to_val [] (++) fill head_step _ _ _ _ _ _ _ _ _.
  Solve Obligations with eauto using to_of_val, of_to_val, val_stuck,
    fill_not_val, step_by_val, fold_right_app, app_eq_nil.

  Global Instance ectxi_lang_ctx_item Ki :
    LanguageCtx (ectx_lang expr) (fill_item Ki).
  Proof. change (LanguageCtx _ (fill [Ki])). apply _. Qed.
End ectxi_language.
