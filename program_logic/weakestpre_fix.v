From iris.program_logic Require Import weakestpre wsat.

(** This files provides an alternative definition of wp in terms of a
    fixpoint of a contractive function, rather than a CoInductive type.
    This is how we define wp on paper.
    We show that the two versions are equivalent. *)

Section def.
  Context {Λ : language} {Σ : iFunctor}.
  Local Notation iProp := (iProp Λ Σ).

  Definition valC := leibnizC (val Λ).
  Definition exprC := leibnizC (expr Λ).
  Definition coPsetC := leibnizC (coPset).

  Definition pre_wp_def (wp : coPsetC -n> exprC -n> (valC -n> iProp) -n> iProp)
             (E : coPset) (e1 : expr Λ) (Φ : valC -n> iProp)
             (n : nat) (r1 : iRes Λ Σ) : Prop :=
    ∀ rf k Ef σ1, 0 ≤ k < n → E ∩ Ef = ∅ →
                  wsat (S k) (E ∪ Ef) σ1 (r1 ⋅ rf) →
                  (∀ v, to_val e1 = Some v →
                        ∃ r2, Φ v (S k) r2 ∧ wsat (S k) (E ∪ Ef) σ1 (r2 ⋅ rf)) ∧
                  (to_val e1 = None → 0 < k →
                   reducible e1 σ1 ∧
                   (∀ e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef →
                      ∃ r2 r2',
                        wsat k (E ∪ Ef) σ2 (r2 ⋅ r2' ⋅ rf) ∧
                        wp E e2 Φ k r2 ∧
                        default True ef (λ ef, wp ⊤ ef (cconst True%I) k r2'))).

  Program Definition pre_wp
          (wp : coPsetC -n> exprC -n> (valC -n> iProp) -n> iProp)
          (E : coPset) (e1 : expr Λ) (Φ : valC -n> iProp) :  iProp :=
    {| uPred_holds := pre_wp_def wp E e1 Φ |}.
  Next Obligation.
    intros ????? r1 r1' Hwp EQr.
    intros ???? Hk ??. edestruct Hwp as [Hval Hstep]; [done..| |].
    { eapply wsat_ne'; last done. apply (dist_le n); last omega.
      by rewrite EQr. }
    split; done.
  Qed.
  Next Obligation.
    intros ???? n1 n2 r1 r2 Hwp [r3 Hr] Hn Hvalid.
    intros ???? Hk ??. edestruct (Hwp (r3 ⋅ rf) k) as [Hval Hstep]; [|done..| |].
    { omega. }
    {  eapply wsat_ne'; last done. by rewrite Hr assoc. }
    split.
    - intros v Hv. destruct (Hval v Hv) as [r4 [HΦ Hw]].
      exists (r4 ⋅ r3). split.
      + eapply uPred_weaken; first exact: HΦ; eauto.
        * by eexists.
        * apply wsat_valid in Hw; last done. solve_validN.
      + by rewrite -assoc.
    - intros ??. edestruct Hstep as [Hred Hpstep]; [done..|].
      split; first done. intros ????.
      edestruct Hpstep as (r4 & r4' & Hw & He2 & Hef); [done..|].
      exists r4, (r4' ⋅ r3). split_and?.
      + move: Hw. by rewrite -!assoc.
      + done.
      + destruct ef; last done.
        eapply uPred_weaken; first exact: Hef; eauto.
        * by eexists.
        * apply wsat_valid in Hw; last omega. solve_validN.
  Qed.

  Local Instance pre_wp_ne n wp E e :
    Proper (dist n ==> dist n) (pre_wp wp E e).
  Proof.
    cut (∀ n Φ1 Φ2, Φ1 ≡{n}≡ Φ2 → ∀ r,
              pre_wp wp E e Φ1 n r → pre_wp wp E e Φ2 n r).
    { intros H Φ1 Φ2 EQΦ. split; split; eapply H.
      - eauto using dist_le.
      - symmetry. eauto using dist_le. }
    clear n. intros n Φ1 Φ2 EQΦ r Hwp.
    intros ???? Hk ??. edestruct Hwp as [Hval Hstep]; [done..|].
    split.
    - intros ??. edestruct Hval as [r2 [HΦ Hw]]; [done..|].
      exists r2. split; last done. apply EQΦ, HΦ.
      + omega.
      + apply wsat_valid in Hw; last omega. solve_validN.
    - intros ??. edestruct Hstep as [Hred Hpstep]; [done..|].
      split; first done. intros ????.
      edestruct Hpstep as (r2 & r2' & Hw & He2 & Hef); [done..|].
      exists r2, r2'. split_and?; try done.
      eapply uPred_holds_ne, He2.
      + apply (dist_le n); last omega. by rewrite -EQΦ.
      + apply wsat_valid in Hw; last omega. solve_validN.
  Qed.

  Definition pre_wp_mor wp : coPsetC -n> exprC -n> (valC -n> iProp) -n> iProp :=
    CofeMor (λ E : coPsetC, CofeMor (λ e : exprC, CofeMor (pre_wp wp E e))).

  Local Instance pre_wp_contractive : Contractive pre_wp_mor.
  Proof.
    cut (∀ n (wp1 wp2 : coPsetC -n> exprC -n> (valC -n> iProp) -n> iProp),
           (∀ i : nat, i < n → wp1 ≡{i}≡ wp2) → ∀ E e Φ r,
              pre_wp wp1 E e Φ n r → pre_wp wp2 E e Φ n r).
    { intros H n wp1 wp2 HI. split; split; eapply H; intros.
      - apply HI. omega.
      - symmetry. apply HI. omega. }
    intros n wp1 wp2 HI E e1 Φ r1 Hwp.
    intros ???? Hk ??. edestruct Hwp as [Hval Hstep]; [done..|].
    split; first done.
    intros ??. edestruct Hstep as [Hred Hpstep]; [done..|].
    split; first done. intros ????.
    edestruct Hpstep as (r2 & r2' & Hw & He2 & Hef); [done..|].
    exists r2, r2'. split_and?; try done.
    - eapply uPred_holds_ne, He2.
      + apply HI. omega.
      + apply wsat_valid in Hw; last omega. solve_validN.
    - destruct ef; last done. eapply uPred_holds_ne, Hef.
      + apply HI. omega.
      + apply wsat_valid in Hw; last omega. solve_validN.
  Qed.

  Definition wp_fix : coPsetC -n> exprC -n> (valC -n> iProp) -n> iProp := 
    fixpoint pre_wp_mor.

End def.
