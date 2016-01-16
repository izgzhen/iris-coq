Require Export iris.ownership prelude.co_pset.
Require Import iris.wsat.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 100 (@eq coPset _ _) => solve_elem_of.
Local Hint Extern 100 (_ ∉ _) => solve_elem_of.
Local Hint Extern 10 (✓{_} _) =>
  repeat match goal with H : wsat _ _ _ _ |- _ => apply wsat_valid in H end;
  solve_validN.

Program Definition pvs {Σ} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  {| uPred_holds n r1 := ∀ rf k Ef σ,
       1 < k ≤ n → (E1 ∪ E2) ∩ Ef = ∅ →
       wsat k (E1 ∪ Ef) σ (r1 ⋅ rf) →
       ∃ r2, P k r2 ∧ wsat k (E2 ∪ Ef) σ (r2 ⋅ rf) |}.
Next Obligation.
  intros Σ E1 E2 P r1 r2 n HP Hr rf k Ef σ ?? Hwsat; simpl in *.
  apply HP; auto. by rewrite (dist_le _ _ _ _ Hr); last lia.
Qed.
Next Obligation. intros Σ E1 E2 P r rf k Ef σ; simpl in *; lia. Qed.
Next Obligation.
  intros Σ E1 E2 P r1 r2 n1 n2 HP [r3 ?] Hn ? rf k Ef σ ?? Hws; setoid_subst.
  destruct (HP (r3⋅rf) k Ef σ) as (r'&?&Hws'); rewrite ?(associative op); auto.
  exists (r' ⋅ r3); rewrite -(associative _); split; last done.
  apply uPred_weaken with r' k; eauto using @ra_included_l.
Qed.
Arguments pvs {_} _ _ _%I : simpl never.
Instance: Params (@pvs) 3.

Section pvs.
Context {Σ : iParam}.
Implicit Types P Q : iProp Σ.
Implicit Types m : icmra' Σ.

Global Instance pvs_ne E1 E2 n : Proper (dist n ==> dist n) (@pvs Σ E1 E2).
Proof.
  intros P Q HPQ r1 n' ??; simpl; split; intros HP rf k Ef σ ???;
    destruct (HP rf k Ef σ) as (r2&?&?); auto;
    exists r2; split_ands; auto; apply HPQ; eauto.
Qed.
Global Instance pvs_proper E1 E2 : Proper ((≡) ==> (≡)) (@pvs Σ E1 E2).
Proof. apply ne_proper, _. Qed.

Lemma pvs_intro E P : P ⊑ pvs E E P.
Proof.
  intros r n ? HP rf k Ef σ ???; exists r; split; last done.
  apply uPred_weaken with r n; eauto.
Qed.
Lemma pvs_mono E1 E2 P Q : P ⊑ Q → pvs E1 E2 P ⊑ pvs E1 E2 Q.
Proof.
  intros HPQ r n ? HP rf k Ef σ ???.
  destruct (HP rf k Ef σ) as (r2&?&?); eauto; exists r2; eauto.
Qed.
Lemma pvs_timeless E P : TimelessP P → (▷ P) ⊑ pvs E E P.
Proof.
  rewrite uPred.timelessP_spec=> HP r [|n] ? HP' rf k Ef σ ???; first lia.
  exists r; split; last done.
  apply HP, uPred_weaken with r n; eauto using cmra_valid_le.
Qed.
Lemma pvs_trans E1 E2 E3 P :
  E2 ⊆ E1 ∪ E3 → pvs E1 E2 (pvs E2 E3 P) ⊑ pvs E1 E3 P.
Proof.
  intros ? r1 n ? HP1 rf k Ef σ ???.
  destruct (HP1 rf k Ef σ) as (r2&HP2&?); auto.
Qed.
Lemma pvs_mask_frame E1 E2 Ef P :
  Ef ∩ (E1 ∪ E2) = ∅ → pvs E1 E2 P ⊑ pvs (E1 ∪ Ef) (E2 ∪ Ef) P.
Proof.
  intros ? r n ? HP rf k Ef' σ ???.
  destruct (HP rf k (Ef∪Ef') σ) as (r'&?&?); rewrite ?(associative_L _); eauto.
  by exists r'; rewrite -(associative_L _).
Qed.
Lemma pvs_frame_r E1 E2 P Q : (pvs E1 E2 P ★ Q) ⊑ pvs E1 E2 (P ★ Q).
Proof.
  intros r n ? (r1&r2&Hr&HP&?) rf k Ef σ ???.
  destruct (HP (r2 ⋅ rf) k Ef σ) as (r'&?&?); eauto.
  { by rewrite (associative _) -(dist_le _ _ _ _ Hr); last lia. }
  exists (r' ⋅ r2); split; last by rewrite -(associative _).
  exists r', r2; split_ands; auto; apply uPred_weaken with r2 n; auto.
Qed.
Lemma pvs_open i P : inv i P ⊑ pvs {[ i ]} ∅ (▷ P).
Proof.
  intros r [|n] ? Hinv rf [|k] Ef σ ???; try lia.
  apply inv_spec in Hinv; last auto.
  destruct (wsat_open k Ef σ (r ⋅ rf) i P) as (rP&?&?); auto.
  { rewrite lookup_wld_op_l ?Hinv; eauto; apply dist_le with (S n); eauto. }
  exists (rP ⋅ r); split; last by rewrite (left_id_L _ _) -(associative _).
  eapply uPred_weaken with rP (S k); eauto using @ra_included_l.
Qed.
Lemma pvs_close i P : (inv i P ∧ ▷ P) ⊑ pvs ∅ {[ i ]} True.
Proof.
  intros r [|n] ? [? HP] rf [|k] Ef σ ? HE ?; try lia; exists ∅; split; [done|].
  rewrite (left_id _ _); apply wsat_close with P r.
  * apply inv_spec, uPred_weaken with r (S n); auto.
  * solve_elem_of +HE.
  * by rewrite -(left_id_L ∅ (∪) Ef).
  * apply uPred_weaken with r n; auto.
Qed.
Lemma pvs_updateP E m (P : icmra' Σ → Prop) :
  m ⇝: P → ownG m ⊑ pvs E E (∃ m', ■ P m' ∧ ownG m').
Proof.
  intros Hup r [|n] ? Hinv%ownG_spec rf [|k] Ef σ ???; try lia.
  destruct (wsat_update_gst k (E ∪ Ef) σ r rf m P)
    as (m'&?&?); eauto using cmra_included_le.
  by exists (update_gst m' r); split; [exists m'; split; [|apply ownG_spec]|].
Qed.
Lemma pvs_alloc E P : ¬set_finite E → ▷ P ⊑ pvs E E (∃ i, ■ (i ∈ E) ∧ inv i P).
Proof.
  intros ? r [|n] ? HP rf [|k] Ef σ ???; try lia.
  destruct (wsat_alloc k E Ef σ rf P r) as (i&?&?&?); auto.
  { apply uPred_weaken with r n; eauto. }
  exists (Res {[ i ↦ to_agree (Later (iProp_unfold P)) ]} ∅ ∅).
  by split; [by exists i; split; rewrite /uPred_holds /=|].
Qed.

(* Derived rules *)
Import uPred.
Global Instance pvs_mono' E1 E2 : Proper ((⊑) ==> (⊑)) (@pvs Σ E1 E2).
Proof. intros P Q; apply pvs_mono. Qed.
Lemma pvs_trans' E P : pvs E E (pvs E E P) ⊑ pvs E E P.
Proof. apply pvs_trans; solve_elem_of. Qed.
Lemma pvs_frame_l E1 E2 P Q : (P ★ pvs E1 E2 Q) ⊑ pvs E1 E2 (P ★ Q).
Proof. rewrite !(commutative _ P); apply pvs_frame_r. Qed.
Lemma pvs_always_l E1 E2 P Q : (□ P ∧ pvs E1 E2 Q) ⊑ pvs E1 E2 (□ P ∧ Q).
Proof. by rewrite !always_and_sep_l pvs_frame_l. Qed.
Lemma pvs_always_r E1 E2 P Q : (pvs E1 E2 P ∧ □ Q) ⊑ pvs E1 E2 (P ∧ □ Q).
Proof. by rewrite !always_and_sep_r pvs_frame_r. Qed.
Lemma pvs_impl_l E1 E2 P Q : (□ (P → Q) ∧ pvs E1 E2 P) ⊑ pvs E1 E2 Q.
Proof. by rewrite pvs_always_l always_elim impl_elim_l. Qed.
Lemma pvs_impl_r E1 E2 P Q : (pvs E1 E2 P ∧ □ (P → Q)) ⊑ pvs E1 E2 Q.
Proof. by rewrite (commutative _) pvs_impl_l. Qed.
Lemma pvs_mask_weaken E1 E2 P : E1 ⊆ E2 → pvs E1 E1 P ⊑ pvs E2 E2 P.
Proof.
  intros; rewrite (union_difference_L E1 E2) //; apply pvs_mask_frame; auto.
Qed.
Lemma pvs_update E m m' : m ⇝ m' → ownG m ⊑ pvs E E (ownG m').
Proof.
  intros; rewrite ->(pvs_updateP E _ (m' =)); last by apply cmra_update_updateP.
  by apply pvs_mono, uPred.exist_elim=> m''; apply uPred.const_elim_l=> ->.
Qed.
End pvs.
