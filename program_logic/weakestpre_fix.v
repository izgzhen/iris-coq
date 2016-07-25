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

Program Definition wp_pre
    (wp : coPset -c> expr Λ -c> (val Λ -c> iProp) -c> iProp) :
    coPset -c> expr Λ -c> (val Λ -c> iProp) -c> iProp := λ E e1 Φ,
  {| uPred_holds n r1 := ∀ k Ef σ1 rf,
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
  intros wp E e1 Φ n r1 r2 Hwp [r3 Hr2] k Ef σ1 rf ??.
  rewrite (dist_le _ _ _ _ Hr2); last lia. intros Hws.
  destruct (Hwp k Ef σ1 (r3 ⋅ rf)) as [Hval Hstep]; rewrite ?assoc; auto.
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

Local Instance pre_wp_contractive : Contractive wp_pre.
Proof.
  assert (∀ n E e Φ r
    (wp1 wp2 : coPset -c> expr Λ -c> (val Λ -c> iProp) -c> iProp),
    (∀ i : nat, i < n → wp1 ≡{i}≡ wp2) →
    wp_pre wp1 E e Φ n r → wp_pre wp2 E e Φ n r) as help.
  { intros n E e Φ r wp1 wp2 HI Hwp k Ef σ1 rf ???.
    destruct (Hwp k Ef σ1 rf) as [Hval Hstep]; auto.
    split; first done.
    intros ??. destruct Hstep as [Hred Hpstep]; auto.
    split; [done|]=> e2 σ2 ef ?.
    destruct (Hpstep e2 σ2 ef) as (r2&r2'&?&?&?); [done..|].
    exists r2, r2'; split_and?; auto.
    - apply HI with k; auto.
    - destruct ef as [ef|]; simpl in *; last done.
      apply HI with k; auto. }
  split; split; eapply help; auto using (symmetry (R:=dist _)).
Qed.

Definition wp_fix : coPset → expr Λ → (val Λ → iProp) → iProp := 
  fixpoint wp_pre.

Lemma wp_fix_unfold E e Φ : wp_fix E e Φ ⊣⊢ wp_pre wp_fix E e Φ.
Proof. apply (fixpoint_unfold wp_pre). Qed.

Lemma wp_fix_correct E e (Φ : val Λ → iProp) : wp_fix E e Φ ⊣⊢ wp E e Φ.
Proof.
  split=> n r Hr. rewrite wp_eq /wp_def {2}/uPred_holds.
  split; revert r E e Φ Hr.
  - induction n as [n IH] using lt_wf_ind=> r1 E e Φ ? Hwp.
    case EQ: (to_val e)=>[v|].
    + rewrite -(of_to_val _ _ EQ) {IH}. constructor. rewrite pvs_eq.
      intros [|k] Ef σ rf ???; first omega.
      apply wp_fix_unfold in Hwp; last done.
      destruct (Hwp k Ef σ rf); auto.
    + constructor; [done|]=> k Ef σ1 rf ???.
      apply wp_fix_unfold in Hwp; last done.
      destruct (Hwp k Ef σ1 rf) as [Hval [Hred Hpstep]]; auto.
      split; [done|]=> e2 σ2 ef ?.
      destruct (Hpstep e2 σ2 ef) as (r2&r2'&?&?&?); [done..|].
      exists r2, r2'; split_and?; auto.
      intros ? ->. change (weakestpre.wp_pre ⊤ (cconst True%I) e' k r2'); eauto.
  - induction n as [n IH] using lt_wf_ind=> r1 E e Φ ? Hwp.
    apply wp_fix_unfold; [done|]=> k Ef σ1 rf ???. split.
    + intros v Hval.
      destruct Hwp as [??? Hpvs|]; rewrite ?to_of_val in Hval; simplify_eq/=.
      rewrite pvs_eq in Hpvs.
      destruct (Hpvs (S k) Ef σ1 rf) as (r2&?&?); eauto.
    + intros Hval ?.
      destruct Hwp as [|???? Hwp]; rewrite ?to_of_val in Hval; simplify_eq/=.
      edestruct (Hwp k Ef σ1 rf) as [? Hpstep]; auto.
      split; [done|]=> e2 σ2 ef ?.
      destruct (Hpstep e2 σ2 ef) as (r2&r2'&?&?&?); auto.
      exists r2, r2'. destruct ef; simpl; auto.
Qed.
End def.
