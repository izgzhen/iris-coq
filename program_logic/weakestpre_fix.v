From Coq Require Import Wf_nat.
From iris.program_logic Require Import weakestpre wsat.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 10 (_ ⊥ _) => set_solver.
Local Hint Extern 10 (✓{_} _) =>
  repeat match goal with
  | H : wsat _ _ _ _ |- _ => apply wsat_valid in H; last omega
  end; solve_validN.

(** This files provides an alternative definition of wp in terms of a fixpoint
of a contractive function, rather than a CoInductive type. This is how we define
wp on paper.  We show that the two versions are equivalent. *)
Section def.
Context {Λ : language} {Σ : iFunctor}.
Local Notation iProp := (iProp Λ Σ).
Local Notation coPsetC := (leibnizC (coPset)).

Program Definition wp_pre
    (wp : coPsetC -n> exprC Λ -n> (valC Λ -n> iProp) -n> iProp)
    (E : coPset) (e1 : expr Λ) (Φ : valC Λ -n> iProp) :  iProp :=
  {| uPred_holds n r1 := ∀ rf k Ef σ1,
       0 ≤ k < n → E ⊥ Ef →
       wsat (S k) (E ∪ Ef) σ1 (r1 ⋅ rf) →
       (∀ v, to_val e1 = Some v →
         ∃ r2, Φ v (S k) r2 ∧ wsat (S k) (E ∪ Ef) σ1 (r2 ⋅ rf)) ∧
       (to_val e1 = None → 0 < k →
         reducible e1 σ1 ∧
         (∀ e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef →
           ∃ r2 r2',
             wsat k (E ∪ Ef) σ2 (r2 ⋅ r2' ⋅ rf) ∧
             wp E e2 Φ k r2 ∧
             default True ef (λ ef, wp ⊤ ef (cconst True%I) k r2'))) |}.
Next Obligation.
  intros wp E e1 Φ n r1 r2 Hwp [r3 Hr2] rf k Ef σ1 ??.
  rewrite (dist_le _ _ _ _ Hr2); last lia. intros Hws.
  destruct (Hwp (r3 ⋅ rf) k Ef σ1) as [Hval Hstep]; rewrite ?assoc; auto.
  split.
  - intros v Hv. destruct (Hval v Hv) as [r4 [??]].
    exists (r4 ⋅ r3). rewrite -assoc. eauto using uPred_mono, cmra_includedN_l.
  - intros ??. destruct Hstep as [Hred Hpstep]; auto.
    split; [done|]=> e2 σ2 ef ?.
    edestruct Hpstep as (r4&r4'&?&?&?); eauto.
    exists r4, (r4' ⋅ r3); split_and?; auto.
    + by rewrite assoc -assoc.
    + destruct ef; simpl in *; eauto using uPred_mono, cmra_includedN_l.
Qed.
Next Obligation. repeat intro; eauto. Qed.

Lemma wp_pre_contractive' n E e Φ1 Φ2 r
    (wp1 wp2 : coPsetC -n> exprC Λ -n> (valC Λ -n> iProp) -n> iProp) :
  (∀ i : nat, i < n → wp1 ≡{i}≡ wp2) → Φ1 ≡{n}≡ Φ2 →
  wp_pre wp1 E e Φ1 n r → wp_pre wp2 E e Φ2 n r.
Proof.
  intros HI HΦ Hwp rf k Ef σ1 ???.
  destruct (Hwp rf k Ef σ1) as [Hval Hstep]; auto.
  split.
  { intros v ?. destruct (Hval v) as (r2&?&?); auto.
    exists r2. split; [apply HΦ|]; auto. }
  intros ??. destruct Hstep as [Hred Hpstep]; auto.
  split; [done|]=> e2 σ2 ef ?.
  destruct (Hpstep e2 σ2 ef) as (r2&r2'&?&?&?); [done..|].
  exists r2, r2'; split_and?; auto.
  - apply HI with k; auto.
    assert (wp1 E e2 Φ2 ≡{n}≡ wp1 E e2 Φ1) as HwpΦ by (by rewrite HΦ).
    apply HwpΦ; auto.
  - destruct ef as [ef|]; simpl in *; last done.
    apply HI with k; auto.
Qed.
Instance wp_pre_ne n wp E e : Proper (dist n ==> dist n) (wp_pre wp E e).
Proof.
  split; split;
    eapply wp_pre_contractive'; eauto using dist_le, (symmetry (R:=dist _)).
Qed.

Definition wp_preC
    (wp : coPsetC -n> exprC Λ -n> (valC Λ -n> iProp) -n> iProp) :
    coPsetC -n> exprC Λ -n> (valC Λ -n> iProp) -n> iProp :=
  CofeMor (λ E : coPsetC, CofeMor (λ e : exprC Λ, CofeMor (wp_pre wp E e))).

Local Instance pre_wp_contractive : Contractive wp_preC.
Proof.
  split; split; eapply wp_pre_contractive'; auto using (symmetry (R:=dist _)).
Qed.

Definition wp_fix : coPsetC -n> exprC Λ -n> (valC Λ -n> iProp) -n> iProp := 
  fixpoint wp_preC.

Lemma wp_fix_unfold E e Φ : wp_fix E e Φ ⊣⊢ wp_preC wp_fix E e Φ.
Proof. by rewrite /wp_fix -fixpoint_unfold. Qed.

Lemma wp_fix_correct E e (Φ : valC Λ -n> iProp) : wp_fix E e Φ ⊣⊢ wp E e Φ.
Proof.
  split=> n r Hr. rewrite wp_eq /wp_def {2}/uPred_holds.
  split; revert r E e Φ Hr.
  - induction n as [n IH] using lt_wf_ind=> r1 E e Φ ? Hwp.
    case EQ: (to_val e)=>[v|].
    + rewrite -(of_to_val _ _ EQ) {IH}. constructor. rewrite pvs_eq.
      intros rf [|k] Ef σ ???; first omega.
      apply wp_fix_unfold in Hwp; last done.
      destruct (Hwp rf k Ef σ); auto.
    + constructor; [done|]=> rf k Ef σ1 ???.
      apply wp_fix_unfold in Hwp; last done.
      destruct (Hwp rf k Ef σ1) as [Hval [Hred Hpstep]]; auto.
      split; [done|]=> e2 σ2 ef ?.
      destruct (Hpstep e2 σ2 ef) as (r2&r2'&?&?&?); [done..|].
      exists r2, r2'; split_and?; auto.
      intros ? ->. change (weakestpre.wp_pre ⊤ (cconst True%I) e' k r2'); eauto.
  - induction n as [n IH] using lt_wf_ind=> r1 E e Φ ? Hwp.
    apply wp_fix_unfold; [done|]=> rf k Ef σ1 ???. split.
    + intros v Hval.
      destruct Hwp as [??? Hpvs|]; rewrite ?to_of_val in Hval; simplify_eq/=.
      rewrite pvs_eq in Hpvs.
      destruct (Hpvs rf (S k) Ef σ1) as (r2&?&?); eauto.
    + intros Hval ?.
      destruct Hwp as [|???? Hwp]; rewrite ?to_of_val in Hval; simplify_eq/=.
      edestruct (Hwp rf k Ef σ1) as [? Hpstep]; auto.
      split; [done|]=> e2 σ2 ef ?.
      destruct (Hpstep e2 σ2 ef) as (r2&r2'&?&?&?); auto.
      exists r2, r2'. destruct ef; simpl; auto.
Qed.
End def.
