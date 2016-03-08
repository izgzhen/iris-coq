From program_logic Require Export hoare.
From program_logic Require Import wsat ownership.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 100 (@eq coPset _ _) => eassumption || set_solver.
Local Hint Extern 10 (✓{_} _) =>
  repeat match goal with
  | H : wsat _ _ _ _ |- _ => apply wsat_valid in H; last omega
  end; solve_validN.

Section adequacy.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Λ Σ.
Implicit Types Φ : val Λ → iProp Λ Σ.
Implicit Types Φs : list (val Λ → iProp Λ Σ).
Implicit Types m : iGst Λ Σ.

Notation wptp n := (Forall3 (λ e Φ r, uPred_holds (wp ⊤ e Φ) n r)).
Lemma wptp_le Φs es rs n n' :
  ✓{n'} (big_op rs) → wptp n es Φs rs → n' ≤ n → wptp n' es Φs rs.
Proof. induction 2; constructor; eauto using uPred_weaken. Qed.
Lemma nsteps_wptp Φs k n tσ1 tσ2 rs1 :
  nsteps step k tσ1 tσ2 →
  1 < n → wptp (k + n) (tσ1.1) Φs rs1 →
  wsat (k + n) ⊤ (tσ1.2) (big_op rs1) →
  ∃ rs2 Φs', wptp n (tσ2.1) (Φs ++ Φs') rs2 ∧ wsat n ⊤ (tσ2.2) (big_op rs2).
Proof.
  intros Hsteps Hn; revert Φs rs1.
  induction Hsteps as [|k ?? tσ3 [e1 σ1 e2 σ2 ef t1 t2 ?? Hstep] Hsteps IH];
    simplify_eq/=; intros Φs rs.
  { by intros; exists rs, []; rewrite right_id_L. }
  intros (Φs1&?&rs1&?&->&->&?&
    (Φ&Φs2&r&rs2&->&->&Hwp&?)%Forall3_cons_inv_l)%Forall3_app_inv_l ?.
  rewrite wp_eq in Hwp.
  destruct (wp_step_inv ⊤ ∅ Φ e1 (k + n) (S (k + n)) σ1 r
    (big_op (rs1 ++ rs2))) as [_ Hwpstep]; eauto using val_stuck.
  { by rewrite right_id_L -big_op_cons Permutation_middle. }
  destruct (Hwpstep e2 σ2 ef) as (r2&r2'&Hwsat&?&?); auto; clear Hwpstep.
  revert Hwsat; rewrite big_op_app right_id_L=>Hwsat.
  destruct ef as [e'|].
  - destruct (IH (Φs1 ++ Φ :: Φs2 ++ [λ _, True%I])
      (rs1 ++ r2 :: rs2 ++ [r2'])) as (rs'&Φs'&?&?).
    { apply Forall3_app, Forall3_cons,
        Forall3_app, Forall3_cons, Forall3_nil; eauto using wptp_le; [|];
      rewrite wp_eq; eauto. }
    { by rewrite -Permutation_middle /= (assoc (++))
        (comm (++)) /= assoc big_op_app. }
    exists rs', ([λ _, True%I] ++ Φs'); split; auto.
    by rewrite (assoc _ _ _ Φs') -(assoc _ Φs1).
  - apply (IH (Φs1 ++ Φ :: Φs2) (rs1 ++ r2 ⋅ r2' :: rs2)).
    { rewrite /option_list right_id_L.
      apply Forall3_app, Forall3_cons; eauto using wptp_le.
      rewrite wp_eq.
      apply uPred_weaken with (k + n) r2; eauto using cmra_included_l. }
    by rewrite -Permutation_middle /= big_op_app.
Qed.
Lemma wp_adequacy_steps P Φ k n e1 t2 σ1 σ2 r1 :
  P ⊑ #> e1 {{ Φ }} →
  nsteps step k ([e1],σ1) (t2,σ2) →
  1 < n → wsat (k + n) ⊤ σ1 r1 →
  P (k + n) r1 →
  ∃ rs2 Φs', wptp n t2 (Φ :: Φs') rs2 ∧ wsat n ⊤ σ2 (big_op rs2).
Proof.
  intros Hht ????; apply (nsteps_wptp [Φ] k n ([e1],σ1) (t2,σ2) [r1]);
    rewrite /big_op ?right_id; auto.
  constructor; last constructor.
  apply Hht; by eauto using cmra_included_core.
Qed.

Lemma wp_adequacy_own Φ e1 t2 σ1 m σ2 :
  ✓ m →
  (ownP σ1 ★ ownG m) ⊑ #> e1 {{ Φ }} →
  rtc step ([e1],σ1) (t2,σ2) →
  ∃ rs2 Φs', wptp 2 t2 (Φ :: Φs') rs2 ∧ wsat 2 ⊤ σ2 (big_op rs2).
Proof.
  intros Hv ? [k ?]%rtc_nsteps.
  eapply wp_adequacy_steps with (r1 := (Res ∅ (Excl σ1) m)); eauto; [|].
  { by rewrite Nat.add_comm; apply wsat_init, cmra_valid_validN. }
  uPred.unseal; exists (Res ∅ (Excl σ1) ∅), (Res ∅ ∅ m); split_and?.
  - by rewrite Res_op ?left_id ?right_id.
  - rewrite /ownP; uPred.unseal; rewrite /uPred_holds //=.
  - by apply ownG_spec.
Qed.

Theorem wp_adequacy_result E φ e v t2 σ1 m σ2 :
  ✓ m →
  (ownP σ1 ★ ownG m) ⊑ #> e @ E {{ λ v', ■ φ v' }} →
  rtc step ([e], σ1) (of_val v :: t2, σ2) →
  φ v.
Proof.
  intros Hv ? Hs.
  destruct (wp_adequacy_own (λ v', ■ φ v')%I e (of_val v :: t2) σ1 m σ2)
             as (rs2&Qs&Hwptp&?); auto.
  { by rewrite -(wp_mask_weaken E ⊤). }
  inversion Hwptp as [|?? r ?? rs Hwp _]; clear Hwptp; subst.
  move: Hwp. rewrite wp_eq. uPred.unseal=> /wp_value_inv Hwp.
  rewrite pvs_eq in Hwp.
  destruct (Hwp (big_op rs) 2 ∅ σ2) as [r' []]; rewrite ?right_id_L; auto.
Qed.

Lemma ht_adequacy_result E φ e v t2 σ1 m σ2 :
  ✓ m →
  {{ ownP σ1 ★ ownG m }} e @ E {{ λ v', ■ φ v' }} →
  rtc step ([e], σ1) (of_val v :: t2, σ2) →
  φ v.
Proof.
  intros ? Hht. eapply wp_adequacy_result with (E:=E); first done.
  move:Hht. by rewrite /ht uPred.always_elim=>/uPred.impl_entails.
Qed.

Lemma wp_adequacy_reducible E Φ e1 e2 t2 σ1 m σ2 :
  ✓ m →
  (ownP σ1 ★ ownG m) ⊑ #> e1 @ E {{ Φ }} →
  rtc step ([e1], σ1) (t2, σ2) →
  e2 ∈ t2 → to_val e2 = None → reducible e2 σ2.
Proof.
  intros Hv ? Hs [i ?]%elem_of_list_lookup He.
  destruct (wp_adequacy_own Φ e1 t2 σ1 m σ2) as (rs2&Φs&?&?); auto.
  { by rewrite -(wp_mask_weaken E ⊤). }
  destruct (Forall3_lookup_l (λ e Φ r, wp ⊤ e Φ 2 r) t2
    (Φ :: Φs) rs2 i e2) as (Φ'&r2&?&?&Hwp); auto.
  destruct (wp_step_inv ⊤ ∅ Φ' e2 1 2 σ2 r2 (big_op (delete i rs2)));
    rewrite ?right_id_L ?big_op_delete; auto.
  by rewrite -wp_eq.
Qed.

Theorem wp_adequacy_safe E Φ e1 t2 σ1 m σ2 :
  ✓ m →
  (ownP σ1 ★ ownG m) ⊑ #> e1 @ E {{ Φ }} →
  rtc step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, step (t2, σ2) (t3, σ3).
Proof.
  intros.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (wp_adequacy_reducible E Φ e1 e2 t2 σ1 m σ2) as (e3&σ3&ef&?);
    rewrite ?eq_None_not_Some; auto.
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ option_list ef), σ3; econstructor; eauto.
Qed.

Lemma ht_adequacy_safe E Φ e1 t2 σ1 m σ2 :
  ✓ m →
  {{ ownP σ1 ★ ownG m }} e1 @ E {{ Φ }} →
  rtc step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, step (t2, σ2) (t3, σ3).
Proof.
  intros ? Hht. eapply wp_adequacy_safe with (E:=E) (Φ:=Φ); first done.
  move:Hht. by rewrite /ht uPred.always_elim=>/uPred.impl_entails.
Qed.

End adequacy.
