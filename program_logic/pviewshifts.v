From prelude Require Export co_pset.
From program_logic Require Export model.
From program_logic Require Import ownership wsat.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 100 (@eq coPset _ _) => set_solver.
Local Hint Extern 100 (_ ∉ _) => set_solver.
Local Hint Extern 10 (✓{_} _) =>
  repeat match goal with
  | H : wsat _ _ _ _ |- _ => apply wsat_valid in H; last omega
  end; solve_validN.

Program Definition pvs {Λ Σ} (E1 E2 : coPset) (P : iProp Λ Σ) : iProp Λ Σ :=
  {| uPred_holds n r1 := ∀ rf k Ef σ,
       0 < k ≤ n → (E1 ∪ E2) ∩ Ef = ∅ →
       wsat k (E1 ∪ Ef) σ (r1 ⋅ rf) →
       ∃ r2, P k r2 ∧ wsat k (E2 ∪ Ef) σ (r2 ⋅ rf) |}.
Next Obligation.
  intros Λ Σ E1 E2 P r1 r2 n HP Hr rf k Ef σ ?? Hwsat; simpl in *.
  apply HP; auto. by rewrite (dist_le _ _ _ _ Hr); last lia.
Qed.
Next Obligation.
  intros Λ Σ E1 E2 P r1 r2 n1 n2 HP [r3 ?] Hn ? rf k Ef σ ?? Hws; setoid_subst.
  destruct (HP (r3⋅rf) k Ef σ) as (r'&?&Hws'); rewrite ?(assoc op); auto.
  exists (r' ⋅ r3); rewrite -assoc; split; last done.
  apply uPred_weaken with k r'; eauto using cmra_included_l.
Qed.
Arguments pvs {_ _} _ _ _%I : simpl never.
Instance: Params (@pvs) 4.

Notation "|={ E1 , E2 }=> Q" := (pvs E1 E2 Q%I)
  (at level 199, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }=>  Q") : uPred_scope.
Notation "|={ E }=> Q" := (pvs E E Q%I)
  (at level 199, E at level 50, Q at level 200,
   format "|={ E }=>  Q") : uPred_scope.

Section pvs.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P Q : iProp Λ Σ.
Implicit Types m : iGst Λ Σ.
Transparent uPred_holds.

Global Instance pvs_ne E1 E2 n : Proper (dist n ==> dist n) (@pvs Λ Σ E1 E2).
Proof.
  intros P Q HPQ; split=> n' r1 ??; simpl; split; intros HP rf k Ef σ ???;
    destruct (HP rf k Ef σ) as (r2&?&?); auto;
    exists r2; split_and?; auto; apply HPQ; eauto.
Qed.
Global Instance pvs_proper E1 E2 : Proper ((≡) ==> (≡)) (@pvs Λ Σ E1 E2).
Proof. apply ne_proper, _. Qed.

Lemma pvs_intro E P : P ⊑ |={E}=> P.
Proof.
  split=> n r ? HP rf k Ef σ ???; exists r; split; last done.
  apply uPred_weaken with n r; eauto.
Qed.
Lemma pvs_mono E1 E2 P Q : P ⊑ Q → (|={E1,E2}=> P) ⊑ (|={E1,E2}=> Q).
Proof.
  intros HPQ; split=> n r ? HP rf k Ef σ ???.
  destruct (HP rf k Ef σ) as (r2&?&?); eauto.
  exists r2; eauto using uPred_in_entails.
Qed.
Lemma pvs_timeless E P : TimelessP P → (▷ P) ⊑ (|={E}=> P).
Proof.
  rewrite uPred.timelessP_spec=> HP.
  split=>-[|n] r ? HP' rf k Ef σ ???; first lia.
  exists r; split; last done.
  apply HP, uPred_weaken with n r; eauto using cmra_validN_le.
Qed.
Lemma pvs_trans E1 E2 E3 P :
  E2 ⊆ E1 ∪ E3 → (|={E1,E2}=> |={E2,E3}=> P) ⊑ (|={E1,E3}=> P).
Proof.
  intros ?; split=> n r1 ? HP1 rf k Ef σ ???.
  destruct (HP1 rf k Ef σ) as (r2&HP2&?); auto.
Qed.
Lemma pvs_mask_frame E1 E2 Ef P :
  Ef ∩ (E1 ∪ E2) = ∅ → (|={E1,E2}=> P) ⊑ (|={E1 ∪ Ef,E2 ∪ Ef}=> P).
Proof.
  intros ?; split=> n r ? HP rf k Ef' σ ???.
  destruct (HP rf k (Ef∪Ef') σ) as (r'&?&?); rewrite ?(assoc_L _); eauto.
  by exists r'; rewrite -(assoc_L _).
Qed.
Lemma pvs_frame_r E1 E2 P Q : ((|={E1,E2}=> P) ★ Q) ⊑ (|={E1,E2}=> P ★ Q).
Proof.
  split; intros n r ? (r1&r2&Hr&HP&?) rf k Ef σ ???.
  destruct (HP (r2 ⋅ rf) k Ef σ) as (r'&?&?); eauto.
  { by rewrite assoc -(dist_le _ _ _ _ Hr); last lia. }
  exists (r' ⋅ r2); split; last by rewrite -assoc.
  exists r', r2; split_and?; auto; apply uPred_weaken with n r2; auto.
Qed.
Lemma pvs_openI i P : ownI i P ⊑ (|={{[i]},∅}=> ▷ P).
Proof.
  split=> -[|n] r ? Hinv rf [|k] Ef σ ???; try lia.
  apply ownI_spec in Hinv; last auto.
  destruct (wsat_open k Ef σ (r ⋅ rf) i P) as (rP&?&?); auto.
  { rewrite lookup_wld_op_l ?Hinv; eauto; apply dist_le with (S n); eauto. }
  exists (rP ⋅ r); split; last by rewrite (left_id_L _ _) -assoc.
  eapply uPred_weaken with (S k) rP; eauto using cmra_included_l.
Qed.
Lemma pvs_closeI i P : (ownI i P ∧ ▷ P) ⊑ (|={∅,{[i]}}=> True).
Proof.
  split=> -[|n] r ? [? HP] rf [|k] Ef σ ? HE ?; try lia.
  exists ∅; split; [done|].
  rewrite left_id; apply wsat_close with P r.
  - apply ownI_spec, uPred_weaken with (S n) r; auto.
  - set_solver +HE.
  - by rewrite -(left_id_L ∅ (∪) Ef).
  - apply uPred_weaken with n r; auto.
Qed.
Lemma pvs_ownG_updateP E m (P : iGst Λ Σ → Prop) :
  m ~~>: P → ownG m ⊑ (|={E}=> ∃ m', ■ P m' ∧ ownG m').
Proof.
  intros Hup%option_updateP'.
  split=> -[|n] r ? /ownG_spec Hinv rf [|k] Ef σ ???; try lia.
  destruct (wsat_update_gst k (E ∪ Ef) σ r rf (Some m) P) as (m'&?&?); eauto.
  { apply cmra_includedN_le with (S n); auto. }
  by exists (update_gst m' r); split; [exists m'; split; [|apply ownG_spec]|].
Qed.
Lemma pvs_ownG_updateP_empty `{Empty (iGst Λ Σ), !CMRAIdentity (iGst Λ Σ)}
    E (P : iGst Λ Σ → Prop) :
  ∅ ~~>: P → True ⊑ (|={E}=> ∃ m', ■ P m' ∧ ownG m').
Proof.
  intros Hup; split=> -[|n] r ? _ rf [|k] Ef σ ???; try lia.
  destruct (wsat_update_gst k (E ∪ Ef) σ r rf ∅ P) as (m'&?&?); eauto.
  { apply cmra_empty_leastN. }
  { apply cmra_updateP_compose_l with (Some ∅), option_updateP with P;
      auto using option_update_None. }
  by exists (update_gst m' r); split; [exists m'; split; [|apply ownG_spec]|].
Qed.
Lemma pvs_allocI E P : ¬set_finite E → ▷ P ⊑ (|={E}=> ∃ i, ■ (i ∈ E) ∧ ownI i P).
Proof.
  intros ?; split=> -[|n] r ? HP rf [|k] Ef σ ???; try lia.
  destruct (wsat_alloc k E Ef σ rf P r) as (i&?&?&?); auto.
  { apply uPred_weaken with n r; eauto. }
  exists (Res {[ i := to_agree (Next (iProp_unfold P)) ]} ∅ ∅).
  by split; [by exists i; split; rewrite /uPred_holds /=|].
Qed.

(** * Derived rules *)
Opaque uPred_holds.
Import uPred.
Global Instance pvs_mono' E1 E2 : Proper ((⊑) ==> (⊑)) (@pvs Λ Σ E1 E2).
Proof. intros P Q; apply pvs_mono. Qed.
Global Instance pvs_flip_mono' E1 E2 :
  Proper (flip (⊑) ==> flip (⊑)) (@pvs Λ Σ E1 E2).
Proof. intros P Q; apply pvs_mono. Qed.
Lemma pvs_trans' E P : (|={E}=> |={E}=> P) ⊑ (|={E}=> P).
Proof. apply pvs_trans; set_solver. Qed.
Lemma pvs_strip_pvs E P Q : P ⊑ (|={E}=> Q) → (|={E}=> P) ⊑ (|={E}=> Q).
Proof. move=>->. by rewrite pvs_trans'. Qed.
Lemma pvs_frame_l E1 E2 P Q : (P ★ |={E1,E2}=> Q) ⊑ (|={E1,E2}=> P ★ Q).
Proof. rewrite !(comm _ P); apply pvs_frame_r. Qed.
Lemma pvs_always_l E1 E2 P Q `{!AlwaysStable P} :
  (P ∧ |={E1,E2}=> Q) ⊑ (|={E1,E2}=> P ∧ Q).
Proof. by rewrite !always_and_sep_l pvs_frame_l. Qed.
Lemma pvs_always_r E1 E2 P Q `{!AlwaysStable Q} :
  ((|={E1,E2}=> P) ∧ Q) ⊑ (|={E1,E2}=> P ∧ Q).
Proof. by rewrite !always_and_sep_r pvs_frame_r. Qed.
Lemma pvs_impl_l E1 E2 P Q : (□ (P → Q) ∧ (|={E1,E2}=> P)) ⊑ (|={E1,E2}=> Q).
Proof. by rewrite pvs_always_l always_elim impl_elim_l. Qed.
Lemma pvs_impl_r E1 E2 P Q : ((|={E1,E2}=> P) ∧ □ (P → Q)) ⊑ (|={E1,E2}=> Q).
Proof. by rewrite comm pvs_impl_l. Qed.
Lemma pvs_wand_l E1 E2 P Q R :
  P ⊑ (|={E1,E2}=> Q) → ((Q -★ R) ★ P) ⊑ (|={E1,E2}=> R).
Proof. intros ->. rewrite pvs_frame_l. apply pvs_mono, wand_elim_l. Qed.
Lemma pvs_wand_r E1 E2 P Q R :
  P ⊑ (|={E1,E2}=> Q) → (P ★ (Q -★ R)) ⊑ (|={E1,E2}=> R).
Proof. rewrite comm. apply pvs_wand_l. Qed.
Lemma pvs_sep E P Q:
  ((|={E}=> P) ★ (|={E}=> Q)) ⊑ (|={E}=> P ★ Q).
Proof. rewrite pvs_frame_r pvs_frame_l pvs_trans //. set_solver. Qed.

Lemma pvs_mask_frame' E1 E1' E2 E2' P :
  E1' ⊆ E1 → E2' ⊆ E2 → E1 ∖ E1' = E2 ∖ E2' →
  (|={E1',E2'}=> P) ⊑ (|={E1,E2}=> P).
Proof.
  intros HE1 HE2 HEE.
  rewrite (pvs_mask_frame _ _ (E1 ∖ E1')); last set_solver.
  by rewrite {2}HEE -!union_difference_L.
Qed.

Lemma pvs_mask_frame_mono E1 E1' E2 E2' P Q :
  E1' ⊆ E1 → E2' ⊆ E2 → E1 ∖ E1' = E2 ∖ E2' →
  P ⊑ Q → (|={E1',E2'}=> P) ⊑ (|={E1,E2}=> Q).
Proof. intros HE1 HE2 HEE ->. by apply pvs_mask_frame'. Qed.

(** It should be possible to give a stronger version of this rule
   that does not force the conclusion view shift to have twice the
   same mask. However, even expressing the side-conditions on the
   mask becomes really ugly then, and we have not found an instance
   where that would be useful. *)
Lemma pvs_trans3 E1 E2 Q :
  E2 ⊆ E1 → (|={E1,E2}=> |={E2}=> |={E2,E1}=> Q) ⊑ (|={E1}=> Q).
Proof. intros HE. rewrite !pvs_trans; set_solver. Qed.

Lemma pvs_mask_weaken E1 E2 P : E1 ⊆ E2 → (|={E1}=> P) ⊑ (|={E2}=> P).
Proof. auto using pvs_mask_frame'. Qed.

Lemma pvs_ownG_update E m m' : m ~~> m' → ownG m ⊑ (|={E}=> ownG m').
Proof.
  intros; rewrite (pvs_ownG_updateP E _ (m' =)); last by apply cmra_update_updateP.
  by apply pvs_mono, uPred.exist_elim=> m''; apply uPred.const_elim_l=> ->.
Qed.
End pvs.

(** * Frame Shift Assertions. *)
(* Yes, the name is horrible...
   Frame Shift Assertions take a mask and a predicate over some type (that's
   their "postcondition"). They support weakening the mask, framing resources
   into the postcondition, and composition witn mask-changing view shifts. *)
Notation FSA Λ Σ A := (coPset → (A → iProp Λ Σ) → iProp Λ Σ).
Class FrameShiftAssertion {Λ Σ A} (fsaV : Prop) (fsa : FSA Λ Σ A) := {
  fsa_mask_frame_mono E1 E2 Φ Ψ :
    E1 ⊆ E2 → (∀ a, Φ a ⊑ Ψ a) → fsa E1 Φ ⊑ fsa E2 Ψ;
  fsa_trans3 E Φ : (|={E}=> fsa E (λ a, |={E}=> Φ a)) ⊑ fsa E Φ;
  fsa_open_close E1 E2 Φ :
    fsaV → E2 ⊆ E1 → (|={E1,E2}=> fsa E2 (λ a, |={E2,E1}=> Φ a)) ⊑ fsa E1 Φ;
  fsa_frame_r E P Φ : (fsa E Φ ★ P) ⊑ fsa E (λ a, Φ a ★ P)
}.

Section fsa.
Context {Λ Σ A} (fsa : FSA Λ Σ A) `{!FrameShiftAssertion fsaV fsa}.
Implicit Types Φ Ψ : A → iProp Λ Σ.

Lemma fsa_mono E Φ Ψ : (∀ a, Φ a ⊑ Ψ a) → fsa E Φ ⊑ fsa E Ψ.
Proof. apply fsa_mask_frame_mono; auto. Qed.
Lemma fsa_mask_weaken E1 E2 Φ : E1 ⊆ E2 → fsa E1 Φ ⊑ fsa E2 Φ.
Proof. intros. apply fsa_mask_frame_mono; auto. Qed.
Lemma fsa_frame_l E P Φ : (P ★ fsa E Φ) ⊑ fsa E (λ a, P ★ Φ a).
Proof. rewrite comm fsa_frame_r. apply fsa_mono=>a. by rewrite comm. Qed.
Lemma fsa_strip_pvs E P Φ : P ⊑ fsa E Φ → (|={E}=> P) ⊑ fsa E Φ.
Proof.
  move=>->. rewrite -{2}fsa_trans3.
  apply pvs_mono, fsa_mono=>a; apply pvs_intro.
Qed.
Lemma fsa_mono_pvs E Φ Ψ : (∀ a, Φ a ⊑ (|={E}=> Ψ a)) → fsa E Φ ⊑ fsa E Ψ.
Proof. intros. rewrite -[fsa E Ψ]fsa_trans3 -pvs_intro. by apply fsa_mono. Qed.
End fsa.

Definition pvs_fsa {Λ Σ} : FSA Λ Σ () := λ E Φ, (|={E}=> Φ ())%I.
Instance pvs_fsa_prf {Λ Σ} : FrameShiftAssertion True (@pvs_fsa Λ Σ).
Proof.
  rewrite /pvs_fsa.
  split; auto using pvs_mask_frame_mono, pvs_trans3, pvs_frame_r.
Qed.
