Require Export iris.hoare.
Require Import iris.wsat.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 100 (@eq coPset _ _) => eassumption || solve_elem_of.
Local Hint Extern 10 (✓{_} _) =>
  repeat match goal with H : wsat _ _ _ _ |- _ => apply wsat_valid in H end;
  solve_validN.

Section adequacy.
Context {Σ : iParam}.
Implicit Types e : iexpr Σ.
Implicit Types Q : ival Σ → iProp Σ.
Transparent uPred_holds.

Notation wptp n := (Forall3 (λ e Q r, uPred_holds (wp coPset_all e Q) n r)).
Lemma wptp_le Qs es rs n n' :
  ✓{n'} (big_op rs) → wptp n es Qs rs → n' ≤ n → wptp n' es Qs rs.
Proof. induction 2; constructor; eauto using uPred_weaken. Qed.
Lemma nsteps_wptp Qs k n tσ1 tσ2 rs1 :
  nsteps step k tσ1 tσ2 →
  1 < n → wptp (k + n) (tσ1.1) Qs rs1 →
  wsat (k + n) coPset_all (tσ1.2) (big_op rs1) →
  ∃ rs2 Qs', wptp n (tσ2.1) (Qs ++ Qs') rs2 ∧
             wsat n coPset_all (tσ2.2) (big_op rs2).
Proof.
  intros Hsteps Hn; revert Qs rs1.
  induction Hsteps as [|k ?? tσ3 [e1 σ1 e2 σ2 ef t1 t2 ?? Hstep] Hsteps IH];
    simplify_equality'; intros Qs rs.
  { by intros; exists rs, []; rewrite right_id_L. }
  intros (Qs1&?&rs1&?&->&->&?&
    (Q&Qs2&r&rs2&->&->&Hwp&?)%Forall3_cons_inv_l)%Forall3_app_inv_l ?.
  destruct (wp_step_inv coPset_all ∅ Q e1 (k + n) (S (k + n)) σ1 r
    (big_op (rs1 ++ rs2))) as [_ Hwpstep]; eauto using values_stuck.
  { by rewrite right_id_L -big_op_cons Permutation_middle. }
  destruct (Hwpstep e2 σ2 ef) as (r2&r2'&Hwsat&?&?); auto; clear Hwpstep.
  revert Hwsat; rewrite big_op_app right_id_L=>Hwsat.
  destruct ef as [e'|].
  * destruct (IH (Qs1 ++ Q :: Qs2 ++ [λ _, True%I])
      (rs1 ++ r2 :: rs2 ++ [r2'])) as (rs'&Qs'&?&?).
    { apply Forall3_app, Forall3_cons,
        Forall3_app, Forall3_cons, Forall3_nil; eauto using wptp_le. }
    { by rewrite -Permutation_middle /= (associative (++))
        (commutative (++)) /= associative big_op_app. }
    exists rs', ([λ _, True%I] ++ Qs'); split; auto.
    by rewrite (associative _ _ _ Qs') -(associative _ Qs1).
  * apply (IH (Qs1 ++ Q :: Qs2) (rs1 ++ r2 ⋅ r2' :: rs2)).
    { rewrite /option_list right_id_L.
      apply Forall3_app, Forall3_cons; eauto using wptp_le.
      apply uPred_weaken with r2 (k + n); eauto using @ra_included_l. }
    by rewrite -Permutation_middle /= big_op_app.
Qed.
Lemma ht_adequacy_steps P Q k n e1 t2 σ1 σ2 r1 :
  {{ P }} e1 @ coPset_all {{ Q }} →
  nsteps step k ([e1],σ1) (t2,σ2) →
  1 < n → wsat (k + n) coPset_all σ1 r1 →
  P (k + n) r1 →
  ∃ rs2 Qs', wptp n t2 ((λ v, pvs coPset_all coPset_all (Q v)) :: Qs') rs2 ∧
             wsat n coPset_all σ2 (big_op rs2).
Proof.
  intros Hht ????; apply (nsteps_wptp [pvs coPset_all coPset_all ∘ Q] k n
    ([e1],σ1) (t2,σ2) [r1]); rewrite /big_op ?right_id; auto.
  constructor; last constructor.
  apply Hht with r1 (k + n); eauto using @ra_included_unit.
  by destruct (k + n).
Qed.
Theorem ht_adequacy_result E φ e v t2 σ1 σ2 :
  {{ ownP σ1 }} e @ E {{ λ v', ■ φ v' }} →
  rtc step ([e], σ1) (of_val v :: t2, σ2) →
  φ v.
Proof.
  intros ? [k ?]%rtc_nsteps.
  destruct (ht_adequacy_steps (ownP σ1) (λ v', ■ φ v')%I k 2 e
    (of_val v :: t2) σ1 σ2 (Res ∅ (Excl σ1) ∅)) as (rs2&Qs&Hwptp&?); auto.
  { by rewrite -(ht_mask_weaken E coPset_all). }
  { rewrite Nat.add_comm; apply wsat_init. }
  { by rewrite /uPred_holds /=. }
  inversion Hwptp as [|?? r ?? rs Hwp _]; clear Hwptp; subst.
  apply wp_value_inv in Hwp; destruct (Hwp (big_op rs) 2 ∅ σ2) as [r' []]; auto.
  by rewrite right_id_L.
Qed.
Lemma ht_adequacy_reducible E Q e1 e2 t2 σ1 σ2 :
  {{ ownP σ1 }} e1 @ E {{ Q }} →
  rtc step ([e1], σ1) (t2, σ2) →
  e2 ∈ t2 → to_val e2 = None → reducible e2 σ2.
Proof.
  intros ? [k ?]%rtc_nsteps [i ?]%elem_of_list_lookup He.
  destruct (ht_adequacy_steps (ownP σ1) Q k 3 e1
    t2 σ1 σ2 (Res ∅ (Excl σ1) ∅)) as (rs2&Qs&?&?); auto.
  { by rewrite -(ht_mask_weaken E coPset_all). }
  { rewrite Nat.add_comm; apply wsat_init. }
  { by rewrite /uPred_holds /=. }
  destruct (Forall3_lookup_l (λ e Q r, wp coPset_all e Q 3 r) t2
    (pvs coPset_all coPset_all ∘ Q :: Qs) rs2 i e2) as (Q'&r2&?&?&Hwp); auto.
  destruct (wp_step_inv coPset_all ∅ Q' e2 2 3 σ2 r2 (big_op (delete i rs2)));
    rewrite ?right_id_L ?big_op_delete; auto.
Qed.
Theorem ht_adequacy_safe E Q e1 t2 σ1 σ2 :
  {{ ownP σ1 }} e1 @ E {{ Q }} →
  rtc step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, step (t2, σ2) (t3, σ3).
Proof.
  intros.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (ht_adequacy_reducible E Q e1 e2 t2 σ1 σ2) as (e3&σ3&ef&?);
    rewrite ?eq_None_not_Some; auto.
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ option_list ef), σ3; econstructor; eauto.
Qed.
End adequacy.
