Require Export barrier.parameter.
Require Import prelude.gmap iris.lifting.
Import uPred.

(* TODO RJ: Figure out a way to to always use our Σ. *)

(** Bind. *)
Lemma wp_bind E e K Q :
  wp E e (λ v, wp (Σ:=Σ) E (fill K (of_val v)) Q) ⊑ wp (Σ:=Σ) E (fill K e) Q.
Proof.
  by apply (wp_bind (Σ:=Σ) (K := fill K)), fill_is_ctx.
Qed.

(** Base axioms for core primitives of the language. *)

(* TODO RJ: Figure out some better way to make the
   postcondition a predicate over a *location* *)
(* TODO RJ: There is probably a specialized version of the lifting
   lemma that would be useful here. *)
Lemma wp_alloc E σ v:
  ownP (Σ:=Σ) σ ⊑ wp (Σ:=Σ) E (Alloc (v2e v))
       (λ v', ∃ l, ■(v' = LocV l ∧ σ !! l = None) ∧ ownP (Σ:=Σ) (<[l:=v]>σ)).
Proof.
  (* RJ FIXME: rewrite would be nicer... *)
  etransitivity; last eapply wp_lift_step with (σ1 := σ)
    (φ := λ e' σ' ef, ∃ l, e' = Loc l ∧ σ' = <[l:=v]>σ ∧ σ !! l = None ∧ ef = None);
    last first.
  - intros e2 σ2 ef Hstep%prim_ectx_step; last first.
    { exists ∅. do 3 eexists. eapply AllocS with (l:=0); by rewrite ?v2v. }
    inversion_clear Hstep.
    rewrite v2v in Hv. inversion_clear Hv.
    eexists; split_ands; done.
  - (* RJ FIXME: Need to find a fresh location. *) admit.
  - reflexivity.
  - reflexivity.
  - (* RJ FIXME I am sure there is a better way to invoke right_id, but I could not find it. *)
    rewrite -pvs_intro. rewrite -{1}[ownP σ](@right_id _ _ _ _ uPred.sep_True).
    apply sep_mono; first done. rewrite -later_intro.
    apply forall_intro=>e2. apply forall_intro=>σ2. apply forall_intro=>ef.
    apply wand_intro_l. rewrite right_id. rewrite -pvs_intro.
    apply const_elim_l. intros [l [-> [-> [Hl ->]]]]. rewrite right_id.
    rewrite -wp_value'; last reflexivity.
    erewrite <-exist_intro with (a := l). apply and_intro.
    + by apply const_intro.
    + done.
Abort.

Lemma wp_load E σ l v:
  σ !! l = Some v →
  ownP (Σ:=Σ) σ ⊑ wp (Σ:=Σ) E (Load (Loc l)) (λ v', ■(v' = v) ∧ ownP (Σ:=Σ) σ).
Proof.
  intros Hl. etransitivity; last eapply wp_lift_step with (σ1 := σ)
    (φ := λ e' σ' ef, e' = v2e v ∧ σ' = σ ∧ ef = None); last first.
  - intros e2 σ2 ef Hstep%prim_ectx_step; last first.
    { exists σ. do 3 eexists. eapply LoadS; eassumption. }
    move: Hl. inversion_clear Hstep=>{σ}. rewrite Hlookup.
    case=>->. done.
  - do 3 eexists. exists EmptyCtx. do 2 eexists.
    split_ands; try (by rewrite fill_empty); [].
    eapply LoadS; eassumption.
  - reflexivity.
  - reflexivity.
  - rewrite -pvs_intro. rewrite -{1}[ownP σ](@right_id _ _ _ _ uPred.sep_True).
    apply sep_mono; first done. rewrite -later_intro.
    apply forall_intro=>e2. apply forall_intro=>σ2. apply forall_intro=>ef.
    apply wand_intro_l. rewrite right_id. rewrite -pvs_intro.
    apply const_elim_l. intros [-> [-> ->]]. rewrite right_id.
    rewrite -wp_value. apply and_intro.
    + by apply const_intro.
    + done.
Qed.

Lemma wp_store E σ l v v':
  σ !! l = Some v' →
  ownP (Σ:=Σ) σ ⊑ wp (Σ:=Σ) E (Store (Loc l) (v2e v)) (λ v', ■(v' = LitVUnit) ∧ ownP (Σ:=Σ) (<[l:=v]>σ)).
Proof.
  intros Hl. etransitivity; last eapply wp_lift_step with (σ1 := σ)
    (φ := λ e' σ' ef, e' = LitUnit ∧ σ' = <[l:=v]>σ ∧ ef = None); last first.
  - intros e2 σ2 ef Hstep%prim_ectx_step; last first.
    { exists σ. do 3 eexists. eapply StoreS; last (eexists; eassumption). by rewrite v2v. }
    move: Hl. inversion_clear Hstep=>{σ2}. rewrite v2v in Hv. inversion_clear Hv.
    done.
  - do 3 eexists. exists EmptyCtx. do 2 eexists.
    split_ands; try (by rewrite fill_empty); [].
    eapply StoreS; last (eexists; eassumption). by rewrite v2v.
  - reflexivity.
  - reflexivity.
  - rewrite -pvs_intro. rewrite -{1}[ownP σ](@right_id _ _ _ _ uPred.sep_True).
    apply sep_mono; first done. rewrite -later_intro.
    apply forall_intro=>e2. apply forall_intro=>σ2. apply forall_intro=>ef.
    apply wand_intro_l. rewrite right_id. rewrite -pvs_intro.
    apply const_elim_l. intros [-> [-> ->]]. rewrite right_id.
    rewrite -wp_value'; last reflexivity. apply and_intro.
    + by apply const_intro.
    + done.
Qed.
