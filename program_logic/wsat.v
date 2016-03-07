From prelude Require Export co_pset.
From program_logic Require Export model.
From algebra Require Export cmra_big_op cmra_tactics.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 10 (✓{_} _) => solve_validN.
Local Hint Extern 1 (✓{_} gst _) => apply gst_validN.
Local Hint Extern 1 (✓{_} wld _) => apply wld_validN.

Record wsat_pre {Λ Σ} (n : nat) (E : coPset)
    (σ : state Λ) (rs : gmap positive (iRes Λ Σ)) (r : iRes Λ Σ) := {
  wsat_pre_valid : ✓{S n} r;
  wsat_pre_state : pst r ≡ Excl σ;
  wsat_pre_dom i : is_Some (rs !! i) → i ∈ E ∧ is_Some (wld r !! i);
  wsat_pre_wld i P :
    i ∈ E →
    wld r !! i ≡{S n}≡ Some (to_agree (Next (iProp_unfold P))) →
    ∃ r', rs !! i = Some r' ∧ P n r'
}.
Arguments wsat_pre_valid {_ _ _ _ _ _ _} _.
Arguments wsat_pre_state {_ _ _ _ _ _ _} _.
Arguments wsat_pre_dom {_ _ _ _ _ _ _} _ _ _.
Arguments wsat_pre_wld {_ _ _ _ _ _ _} _ _ _ _ _.

Definition wsat {Λ Σ}
  (n : nat) (E : coPset) (σ : state Λ) (r : iRes Λ Σ) : Prop :=
  match n with 0 => True | S n => ∃ rs, wsat_pre n E σ rs (r ⋅ big_opM rs) end.
Instance: Params (@wsat) 5.
Arguments wsat : simpl never.

Section wsat.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types σ : state Λ.
Implicit Types r : iRes Λ Σ.
Implicit Types rs : gmap positive (iRes Λ Σ).
Implicit Types P : iProp Λ Σ.
Implicit Types m : iGst Λ Σ.

Instance wsat_ne' : Proper (dist n ==> impl) (@wsat Λ Σ n E σ).
Proof.
  intros [|n] E σ r1 r2 Hr; first done; intros [rs [Hdom Hv Hs Hinv]].
  exists rs; constructor; intros until 0; setoid_rewrite <-Hr; eauto.
Qed.
Global Instance wsat_ne n : Proper (dist n ==> iff) (@wsat Λ Σ n E σ) | 1.
Proof. by intros E σ w1 w2 Hw; split; apply wsat_ne'. Qed.
Global Instance wsat_proper n : Proper ((≡) ==> iff) (@wsat Λ Σ n E σ) | 1.
Proof. by intros E σ w1 w2 Hw; apply wsat_ne, equiv_dist. Qed.
Lemma wsat_le n n' E σ r : wsat n E σ r → n' ≤ n → wsat n' E σ r.
Proof.
  destruct n as [|n], n' as [|n']; simpl; try by (auto with lia).
  intros [rs [Hval Hσ HE Hwld]] ?; exists rs; constructor; auto.
  intros i P ? HiP; destruct (wld (r ⋅ big_opM rs) !! i) as [P'|] eqn:HP';
    [apply (inj Some) in HiP|inversion_clear HiP].
  assert (P' ≡{S n}≡ to_agree $ Next $ iProp_unfold $
                       iProp_fold $ later_car $ P' (S n)) as HPiso.
  { rewrite iProp_unfold_fold later_eta to_agree_car //.
    apply (map_lookup_validN _ (wld (r ⋅ big_opM rs)) i); rewrite ?HP'; auto. }
  assert (P ≡{n'}≡ iProp_fold (later_car (P' (S n)))) as HPP'.
  { apply (inj iProp_unfold), (inj Next), (inj to_agree).
    by rewrite -HiP -(dist_le _ _ _ _ HPiso). }
  destruct (Hwld i (iProp_fold (later_car (P' (S n))))) as (r'&?&?); auto.
  { by rewrite HP' -HPiso. }
  assert (✓{S n} r') by (apply (big_opM_lookup_valid _ rs i); auto).
  exists r'; split; [done|apply HPP', uPred_weaken with n r'; auto].
Qed.
Lemma wsat_valid n E σ r : n ≠ 0 → wsat n E σ r → ✓{n} r.
Proof.
  destruct n; first done.
  intros _ [rs ?]; eapply cmra_validN_op_l, wsat_pre_valid; eauto.
Qed.
Lemma wsat_init k E σ m : ✓{S k} m → wsat (S k) E σ (Res ∅ (Excl σ) m).
Proof.
  intros Hv. exists ∅; constructor; auto.
  - rewrite big_opM_empty right_id.
    split_and!; try (apply cmra_valid_validN, ra_empty_valid);
      constructor || apply Hv.
  - by intros i; rewrite lookup_empty=>-[??].
  - intros i P ?; rewrite /= left_id lookup_empty; inversion_clear 1.
Qed.
Lemma wsat_open n E σ r i P :
  wld r !! i ≡{S n}≡ Some (to_agree (Next (iProp_unfold P))) → i ∉ E →
  wsat (S n) ({[i]} ∪ E) σ r → ∃ rP, wsat (S n) E σ (rP ⋅ r) ∧ P n rP.
Proof.
  intros HiP Hi [rs [Hval Hσ HE Hwld]].
  destruct (Hwld i P) as (rP&?&?); [set_solver +|by apply lookup_wld_op_l|].
  assert (rP ⋅ r ⋅ big_opM (delete i rs) ≡ r ⋅ big_opM rs) as Hr.
  { by rewrite (comm _ rP) -assoc big_opM_delete. }
  exists rP; split; [exists (delete i rs); constructor; rewrite ?Hr|]; auto.
  - intros j; rewrite lookup_delete_is_Some Hr.
    generalize (HE j); set_solver +Hi.
  - intros j P'; rewrite Hr=> Hj ?.
    setoid_rewrite lookup_delete_ne; last (set_solver +Hi Hj).
    apply Hwld; [set_solver +Hj|done].
Qed.
Lemma wsat_close n E σ r i P rP :
  wld rP !! i ≡{S n}≡ Some (to_agree (Next (iProp_unfold P))) → i ∉ E →
  wsat (S n) E σ (rP ⋅ r) → P n rP → wsat (S n) ({[i]} ∪ E) σ r.
Proof.
  intros HiP HiE [rs [Hval Hσ HE Hwld]] ?.
  assert (rs !! i = None) by (apply eq_None_not_Some; naive_solver).
  assert (r ⋅ big_opM (<[i:=rP]> rs) ≡ rP ⋅ r ⋅ big_opM rs) as Hr.
  { by rewrite (comm _ rP) -assoc big_opM_insert. }
  exists (<[i:=rP]>rs); constructor; rewrite ?Hr; auto.
  - intros j; rewrite Hr lookup_insert_is_Some=>-[?|[??]]; subst.
    + split. set_solver. rewrite !lookup_op HiP !op_is_Some; eauto.
    + destruct (HE j) as [Hj Hj']; auto; set_solver +Hj Hj'.
  - intros j P'; rewrite Hr elem_of_union elem_of_singleton=>-[?|?]; subst.
    + rewrite !lookup_wld_op_l ?HiP; auto=> HP.
      apply (inj Some), (inj to_agree), (inj Next), (inj iProp_unfold) in HP.
      exists rP; split; [rewrite lookup_insert|apply HP]; auto.
    + intros. destruct (Hwld j P') as (r'&?&?); auto.
      exists r'; rewrite lookup_insert_ne; naive_solver.
Qed.
Lemma wsat_update_pst n E σ1 σ1' r rf :
  pst r ≡{S n}≡ Excl σ1 → wsat (S n) E σ1' (r ⋅ rf) →
  σ1' = σ1 ∧ ∀ σ2, wsat (S n) E σ2 (update_pst σ2 r ⋅ rf).
Proof.
  intros Hpst_r [rs [(?&?&?) Hpst HE Hwld]]; simpl in *.
  assert (pst rf ⋅ pst (big_opM rs) = ∅) as Hpst'.
  { by apply: (excl_validN_inv_l (S n) _ σ1); rewrite -Hpst_r assoc. }
  assert (σ1' = σ1) as ->.
  { apply leibniz_equiv, (timeless _), dist_le with (S n); auto.
    apply (inj Excl).
    by rewrite -Hpst_r -Hpst -assoc Hpst' right_id. }
  split; [done|exists rs].
  by constructor; first split_and!; try rewrite /= -assoc Hpst'.
Qed.
Lemma wsat_update_gst n E σ r rf m1 (P : iGst Λ Σ → Prop) :
  m1 ≼{S n} gst r → m1 ~~>: P →
  wsat (S n) E σ (r ⋅ rf) → ∃ m2, wsat (S n) E σ (update_gst m2 r ⋅ rf) ∧ P m2.
Proof.
  intros [mf Hr] Hup [rs [(?&?&?) Hσ HE Hwld]].
  destruct (Hup (S n) (mf ⋅ gst (rf ⋅ big_opM rs))) as (m2&?&Hval'); try done.
  { by rewrite /= (assoc _ m1) -Hr assoc. }
  exists m2; split; [exists rs|done].
  by constructor; first split_and!; auto.
Qed.
Lemma wsat_alloc n E1 E2 σ r P rP :
  ¬set_finite E1 → P n rP → wsat (S n) (E1 ∪ E2) σ (rP ⋅ r) →
  ∃ i, wsat (S n) (E1 ∪ E2) σ
         (Res {[i := to_agree (Next (iProp_unfold P))]} ∅ ∅ ⋅ r) ∧
       wld r !! i = None ∧ i ∈ E1.
Proof.
  intros HE1 ? [rs [Hval Hσ HE Hwld]].
  assert (∃ i, i ∈ E1 ∧ wld r !! i = None ∧ wld rP !! i = None ∧
                        wld (big_opM rs) !! i = None) as (i&Hi&Hri&HrPi&Hrsi).
  { exists (coPpick (E1 ∖
      (dom _ (wld r) ∪ (dom _ (wld rP) ∪ dom _ (wld (big_opM rs)))))).
    rewrite -!not_elem_of_dom -?not_elem_of_union -elem_of_difference.
    apply coPpick_elem_of=>HE'; eapply HE1, (difference_finite_inv _ _), HE'.
    by repeat apply union_finite; apply dom_finite. }
  assert (rs !! i = None).
  { apply eq_None_not_Some=>?; destruct (HE i) as [_ Hri']; auto; revert Hri'.
    rewrite /= !lookup_op !op_is_Some -!not_eq_None_Some; tauto. }
  assert (r ⋅ big_opM (<[i:=rP]> rs) ≡ rP ⋅ r ⋅ big_opM rs) as Hr.
  { by rewrite (comm _ rP) -assoc big_opM_insert. }
  exists i; split_and?; [exists (<[i:=rP]>rs); constructor| |]; auto.
  - destruct Hval as (?&?&?);  rewrite -assoc Hr.
    split_and!; rewrite /= ?left_id; [|eauto|eauto].
    intros j; destruct (decide (j = i)) as [->|].
    + by rewrite !lookup_op Hri HrPi Hrsi !right_id lookup_singleton.
    + by rewrite lookup_op lookup_singleton_ne // left_id.
  - by rewrite -assoc Hr /= left_id.
  - intros j; rewrite -assoc Hr; destruct (decide (j = i)) as [->|].
    + intros _; split; first set_solver +Hi.
      rewrite /= !lookup_op lookup_singleton !op_is_Some; eauto.
    + rewrite lookup_insert_ne //.
      rewrite lookup_op lookup_singleton_ne // left_id; eauto.
  - intros j P'; rewrite -assoc Hr; destruct (decide (j=i)) as [->|].
    + rewrite /= !lookup_op Hri HrPi Hrsi right_id lookup_singleton=>? HP.
      apply (inj Some), (inj to_agree), (inj Next), (inj iProp_unfold) in HP.
      exists rP; rewrite lookup_insert; split; [|apply HP]; auto.
    + rewrite /= lookup_op lookup_singleton_ne // left_id=> ??.
      destruct (Hwld j P') as [r' ?]; auto.
      by exists r'; rewrite lookup_insert_ne.
Qed.
End wsat.
