Require Export barrier.parameter.
Require Import prelude.gmap iris.lifting.
Import uPred.

(** Base axioms for core primitives of the language. *)

(* TODO RJ: Figure out some better way to make the
   postcondition a predicate over a *location* *)
(* TODO RJ: Figure out a way to to always use our Σ. *)
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
