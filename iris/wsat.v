Require Export iris.model prelude.co_pset.
Local Hint Extern 10 (✓{_} _) => solve_validN.
Local Hint Extern 1 (✓{_} (gst _)) => apply gst_validN.
Local Hint Extern 1 (✓{_} (wld _)) => apply wld_validN.

Record wsat_pre {Σ} (n : nat) (E : coPset)
    (σ : istate Σ) (rs : gmap positive (res' Σ)) (r : res' Σ) := {
  wsat_pre_valid : ✓{S n} r;
  wsat_pre_state : pst r ≡ Excl σ;
  wsat_pre_dom i : is_Some (rs !! i) → i ∈ E ∧ is_Some (wld r !! i);
  wsat_pre_wld i P :
    i ∈ E →
    wld r !! i ={S n}= Some (to_agree (Later (iProp_unfold P))) →
    ∃ r', rs !! i = Some r' ∧ P n r'
}.
Arguments wsat_pre_valid {_ _ _ _ _ _} _.
Arguments wsat_pre_state {_ _ _ _ _ _} _.
Arguments wsat_pre_dom {_ _ _ _ _ _} _ _ _.
Arguments wsat_pre_wld {_ _ _ _ _ _} _ _ _ _ _.

Definition wsat {Σ} (n : nat) (E : coPset) (σ : istate Σ) (r : res' Σ) : Prop :=
  match n with 0 => True | S n => ∃ rs, wsat_pre n E σ rs (r ⋅ big_opM rs) end.
Instance: Params (@wsat) 4.

Section wsat.
Context {Σ : iParam}.
Implicit Types σ : istate Σ.
Implicit Types r : res' Σ.
Implicit Types rs : gmap positive (res' Σ).
Implicit Types P : iProp Σ.

Instance wsat_ne' : Proper (dist n ==> impl) (wsat (Σ:=Σ) n E σ).
Proof.
  intros [|n] E σ r1 r2 Hr; first done; intros [rs [Hdom Hv Hs Hinv]].
  exists rs; constructor; intros until 0; setoid_rewrite <-Hr; eauto.
Qed.
Global Instance wsat_ne n : Proper (dist n ==> iff) (wsat (Σ:=Σ) n E σ) | 1.
Proof. by intros E σ w1 w2 Hw; split; apply wsat_ne'. Qed.
Global Instance wsat_proper n : Proper ((≡) ==> iff) (wsat (Σ:=Σ) n E σ) | 1.
Proof. by intros E σ w1 w2 Hw; apply wsat_ne, equiv_dist. Qed.
Lemma wsat_valid n E σ (r : res' Σ) : wsat n E σ r → ✓{n} r.
Proof.
  destruct n; [intros; apply cmra_valid_0|intros [rs ?]].
  eapply cmra_valid_op_l, wsat_pre_valid; eauto.
Qed.
Lemma wsat_open n E σ r i P :
  wld r !! i ={S n}= Some (to_agree (Later (iProp_unfold P))) → i ∉ E →
  wsat (S n) ({[i]} ∪ E) σ r → ∃ rP, wsat (S n) E σ (rP ⋅ r) ∧ P n rP.
Proof.
  intros HiP Hi [rs [Hval Hσ HE Hwld]].
  destruct (Hwld i P) as (rP&?&?); [solve_elem_of +|by apply lookup_wld_op_l|].
  assert (rP ⋅ r ⋅ big_opM (delete i rs) ≡ r ⋅ big_opM rs) as Hr.
  { by rewrite (commutative _ rP) -(associative _) big_opM_delete. }
  exists rP; split; [exists (delete i rs); constructor; rewrite ?Hr|]; auto.
  * intros j; rewrite lookup_delete_is_Some Hr.
    generalize (HE j); solve_elem_of +Hi.
  * intros j P'; rewrite Hr=> Hj ?.
    setoid_rewrite lookup_delete_ne; last (solve_elem_of +Hi Hj).
    apply Hwld; [solve_elem_of +Hj|done].
Qed.
Lemma wsat_close n E σ r i P rP :
  wld rP !! i ={S n}= Some (to_agree (Later (iProp_unfold P))) → i ∉ E →
  wsat (S n) E σ (rP ⋅ r) → P n rP → wsat (S n) ({[i]} ∪ E) σ r.
Proof.
  intros HiP HiE [rs [Hval Hσ HE Hwld]] ?.
  assert (rs !! i = None) by (apply eq_None_not_Some; naive_solver).
  assert (r ⋅ big_opM (<[i:=rP]> rs) ≡ rP ⋅ r ⋅ big_opM rs) as Hr.
  { by rewrite (commutative _ rP) -(associative _) big_opM_insert. }
  exists (<[i:=rP]>rs); constructor; rewrite ?Hr; auto.
  * intros j; rewrite Hr lookup_insert_is_Some=>-[?|[??]]; subst.
    + rewrite !lookup_op HiP !op_is_Some; solve_elem_of -.
    + destruct (HE j) as [Hj Hj']; auto; solve_elem_of +Hj Hj'.
  * intros j P'; rewrite Hr elem_of_union elem_of_singleton=>-[?|?]; subst.
    + rewrite !lookup_wld_op_l ?HiP; auto=> HP.
      apply (injective Some), (injective to_agree),
        (injective Later), (injective iProp_unfold) in HP.
      exists rP; split; [rewrite lookup_insert|apply HP]; auto.
    + intros. destruct (Hwld j P') as (r'&?&?); auto.
      exists r'; rewrite lookup_insert_ne; naive_solver.
Qed.
Lemma wsat_update_pst n E σ1 σ2 r :
  pst r ={S n}= Excl σ1 → wsat (S n) E σ1 r → wsat (S n) E σ2 (update_pst σ2 r).
Proof.
  intros Hr [rs [(?&Hpst&?) Hσ HE Hwld]]; simpl in *.
  assert (pst (big_opM rs) = ∅) as Hpst_rs.
  { by apply: (excl_validN_inv_l n σ1); rewrite -Hr. }
  by exists rs; constructor; split_ands'; rewrite /= ?Hpst_rs.
Qed.
Lemma wsat_update_gst n E σ r rf m1 (P : icmra' Σ → Prop) :
  m1 ≼{S n} gst r → m1 ⇝: P →
  wsat (S n) E σ (r ⋅ rf) → ∃ m2, wsat (S n) E σ (update_gst m2 r ⋅ rf) ∧ P m2.
Proof.
  intros [mf Hr] Hup [rs [(?&?&?) Hσ HE Hwld]].
  destruct (Hup (mf ⋅ gst (rf ⋅ big_opM rs)) (S n)) as (m2&?&Hval').
  { by rewrite /= (associative _ m1) -Hr (associative _). }
  exists m2; split; [exists rs; split; split_ands'; auto|done].
Qed.
Lemma wsat_alloc n E1 E2 σ r P rP :
  ¬set_finite E1 → P n rP → wsat (S n) (E1 ∪ E2) σ (rP ⋅ r) →
  ∃ i, wsat (S n) (E1 ∪ E2) σ
         (Res {[i ↦ to_agree (Later (iProp_unfold P))]} ∅ ∅ ⋅ r) ∧
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
  { by rewrite (commutative _ rP) -(associative _) big_opM_insert. }
  exists i; split_ands; [exists (<[i:=rP]>rs); constructor| |]; auto.
  * destruct Hval as (?&?&?);  rewrite -(associative _) Hr.
    split_ands'; rewrite /= ?(left_id _ _); [|eauto|eauto].
    intros j; destruct (decide (j = i)) as [->|].
    + by rewrite !lookup_op Hri HrPi Hrsi !(right_id _ _) lookup_singleton.
    + by rewrite lookup_op lookup_singleton_ne // (left_id _ _).
  * by rewrite -(associative _) Hr /= (left_id _ _).
  * intros j; rewrite -(associative _) Hr; destruct (decide (j = i)) as [->|].
    + rewrite /= !lookup_op lookup_singleton !op_is_Some; solve_elem_of +Hi.
    + rewrite lookup_insert_ne //.
      rewrite lookup_op lookup_singleton_ne // (left_id _ _); eauto.
  * intros j P'; rewrite -(associative _) Hr; destruct (decide (j=i)) as [->|].
    + rewrite /= !lookup_op Hri HrPi Hrsi (right_id _ _) lookup_singleton=>? HP.
      apply (injective Some), (injective to_agree),
        (injective Later), (injective iProp_unfold) in HP.
      exists rP; rewrite lookup_insert; split; [|apply HP]; auto.
    + rewrite /= lookup_op lookup_singleton_ne // (left_id _ _)=> ??.
      destruct (Hwld j P') as [r' ?]; auto.
      by exists r'; rewrite lookup_insert_ne.
Qed.
End wsat.
