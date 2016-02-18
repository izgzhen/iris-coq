From program_logic Require Export pviewshifts.
From program_logic Require Import wsat.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 100 (@eq coPset _ _) => eassumption || set_solver.
Local Hint Extern 100 (_ ∉ _) => set_solver.
Local Hint Extern 100 (@subseteq coPset _ _ _) => set_solver.
Local Hint Extern 10 (✓{_} _) =>
  repeat match goal with
  | H : wsat _ _ _ _ |- _ => apply wsat_valid in H; last omega
  end; solve_validN.

Record wp_go {Λ Σ} (E : coPset) (Φ Φfork : expr Λ → nat → iRes Λ Σ → Prop)
    (k : nat) (rf : iRes Λ Σ) (e1 : expr Λ) (σ1 : state Λ) := {
  wf_safe : reducible e1 σ1;
  wp_step e2 σ2 ef :
    prim_step e1 σ1 e2 σ2 ef →
    ∃ r2 r2',
      wsat k E σ2 (r2 ⋅ r2' ⋅ rf) ∧
      Φ e2 k r2 ∧
      ∀ e', ef = Some e' → Φfork e' k r2'
}.
CoInductive wp_pre {Λ Σ} (E : coPset)
     (Φ : val Λ → iProp Λ Σ) : expr Λ → nat → iRes Λ Σ → Prop :=
  | wp_pre_value n r v : pvs E E (Φ v) n r → wp_pre E Φ (of_val v) n r
  | wp_pre_step n r1 e1 :
     to_val e1 = None →
     (∀ rf k Ef σ1,
       0 < k < n → E ∩ Ef = ∅ →
       wsat (S k) (E ∪ Ef) σ1 (r1 ⋅ rf) →
       wp_go (E ∪ Ef) (wp_pre E Φ)
                      (wp_pre ⊤ (λ _, True%I)) k rf e1 σ1) →
     wp_pre E Φ e1 n r1.
Program Definition wp {Λ Σ} (E : coPset) (e : expr Λ)
  (Φ : val Λ → iProp Λ Σ) : iProp Λ Σ := {| uPred_holds := wp_pre E Φ e |}.
Next Obligation.
  intros Λ Σ E e Φ r1 r2 n Hwp Hr.
  destruct Hwp as [|n r1 e2 ? Hgo]; constructor; rewrite -?Hr; auto.
  intros rf k Ef σ1 ?; rewrite -(dist_le _ _ _ _ Hr); naive_solver.
Qed.
Next Obligation.
  intros Λ Σ E e Φ r1 r2 n1; revert Φ E e r1 r2.
  induction n1 as [n1 IH] using lt_wf_ind; intros Φ E e r1 r1' n2.
  destruct 1 as [|n1 r1 e1 ? Hgo].
  - constructor; eauto using uPred_weaken.
  - intros [rf' Hr] ??; constructor; [done|intros rf k Ef σ1 ???].
    destruct (Hgo (rf' ⋅ rf) k Ef σ1) as [Hsafe Hstep];
      rewrite ?assoc -?Hr; auto; constructor; [done|].
    intros e2 σ2 ef ?; destruct (Hstep e2 σ2 ef) as (r2&r2'&?&?&?); auto.
    exists r2, (r2' ⋅ rf'); split_ands; eauto 10 using (IH k), cmra_included_l.
    by rewrite -!assoc (assoc _ r2).
Qed.
Instance: Params (@wp) 4.

Section wp.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P : iProp Λ Σ.
Implicit Types Φ : val Λ → iProp Λ Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Transparent uPred_holds.

Global Instance wp_ne E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@wp Λ Σ E e).
Proof.
  cut (∀ Φ Ψ, (∀ v, Φ v ≡{n}≡ Ψ v) →
    ∀ r n', n' ≤ n → ✓{n'} r → wp E e Φ n' r → wp E e Ψ n' r).
  { by intros help Φ Ψ HΦΨ; split; apply help. }
  intros Φ Ψ HΦΨ r n'; revert e r.
  induction n' as [n' IH] using lt_wf_ind=> e r.
  destruct 3 as [n' r v HpvsQ|n' r e1 ? Hgo].
  { constructor. by eapply pvs_ne, HpvsQ; eauto. }
  constructor; [done|]=> rf k Ef σ1 ???.
  destruct (Hgo rf k Ef σ1) as [Hsafe Hstep]; auto.
  split; [done|intros e2 σ2 ef ?].
  destruct (Hstep e2 σ2 ef) as (r2&r2'&?&?&?); auto.
  exists r2, r2'; split_ands; [|eapply IH|]; eauto.
Qed.
Global Instance wp_proper E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@wp Λ Σ E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
Lemma wp_mask_frame_mono E1 E2 e Φ Ψ :
  E1 ⊆ E2 → (∀ v, Φ v ⊑ Ψ v) → wp E1 e Φ ⊑ wp E2 e Ψ.
Proof.
  intros HE HΦ r n; revert e r; induction n as [n IH] using lt_wf_ind=> e r.
  destruct 2 as [n' r v HpvsQ|n' r e1 ? Hgo].
  { constructor; eapply pvs_mask_frame_mono, HpvsQ; eauto. }
  constructor; [done|]=> rf k Ef σ1 ???.
  assert (E2 ∪ Ef = E1 ∪ (E2 ∖ E1 ∪ Ef)) as HE'.
  { by rewrite assoc_L -union_difference_L. }
  destruct (Hgo rf k ((E2 ∖ E1) ∪ Ef) σ1) as [Hsafe Hstep]; rewrite -?HE'; auto.
  split; [done|intros e2 σ2 ef ?].
  destruct (Hstep e2 σ2 ef) as (r2&r2'&?&?&?); auto.
  exists r2, r2'; split_ands; [rewrite HE'|eapply IH|]; eauto.
Qed.

Lemma wp_value_inv E Φ v n r : wp E (of_val v) Φ n r → pvs E E (Φ v) n r.
Proof.
  by inversion 1 as [|??? He]; [|rewrite ?to_of_val in He]; simplify_eq.
Qed.
Lemma wp_step_inv E Ef Φ e k n σ r rf :
  to_val e = None → 0 < k < n → E ∩ Ef = ∅ →
  wp E e Φ n r → wsat (S k) (E ∪ Ef) σ (r ⋅ rf) →
  wp_go (E ∪ Ef) (λ e, wp E e Φ) (λ e, wp ⊤ e (λ _, True%I)) k rf e σ.
Proof. intros He; destruct 3; [by rewrite ?to_of_val in He|eauto]. Qed.

Lemma wp_value' E Φ v : Φ v ⊑ wp E (of_val v) Φ.
Proof. by constructor; apply pvs_intro. Qed.
Lemma pvs_wp E e Φ : pvs E E (wp E e Φ) ⊑ wp E e Φ.
Proof.
  intros r n ? Hvs.
  destruct (to_val e) as [v|] eqn:He; [apply of_to_val in He; subst|].
  { constructor; eapply pvs_trans', pvs_mono, Hvs; eauto.
    intros ???; apply wp_value_inv. }
  constructor; [done|]=> rf k Ef σ1 ???.
  destruct (Hvs rf (S k) Ef σ1) as (r'&Hwp&?); auto.
  eapply wp_step_inv with (S k) r'; eauto.
Qed.
Lemma wp_pvs E e Φ : wp E e (λ v, pvs E E (Φ v)) ⊑ wp E e Φ.
Proof.
  intros r n; revert e r; induction n as [n IH] using lt_wf_ind=> e r Hr HΦ.
  destruct (to_val e) as [v|] eqn:He; [apply of_to_val in He; subst|].
  { constructor; apply pvs_trans', (wp_value_inv _ (pvs E E ∘ Φ)); auto. }
  constructor; [done|]=> rf k Ef σ1 ???.
  destruct (wp_step_inv E Ef (pvs E E ∘ Φ) e k n σ1 r rf) as [? Hstep]; auto.
  split; [done|intros e2 σ2 ef ?].
  destruct (Hstep e2 σ2 ef) as (r2&r2'&?&Hwp'&?); auto.
  exists r2, r2'; split_ands; [|apply (IH k)|]; auto.
Qed.
Lemma wp_atomic E1 E2 e Φ :
  E2 ⊆ E1 → atomic e → pvs E1 E2 (wp E2 e (λ v, pvs E2 E1 (Φ v))) ⊑ wp E1 e Φ.
Proof.
  intros ? He r n ? Hvs; constructor; eauto using atomic_not_val.
  intros rf k Ef σ1 ???.
  destruct (Hvs rf (S k) Ef σ1) as (r'&Hwp&?); auto.
  destruct (wp_step_inv E2 Ef (pvs E2 E1 ∘ Φ) e k (S k) σ1 r' rf)
    as [Hsafe Hstep]; auto using atomic_not_val.
  split; [done|]=> e2 σ2 ef ?.
  destruct (Hstep e2 σ2 ef) as (r2&r2'&?&Hwp'&?); clear Hsafe Hstep; auto.
  destruct Hwp' as [k r2 v Hvs'|k r2 e2 Hgo];
    [|destruct (atomic_step e σ1 e2 σ2 ef); naive_solver].
  apply pvs_trans in Hvs'; auto.
  destruct (Hvs' (r2' ⋅ rf) k Ef σ2) as (r3&[]); rewrite ?assoc; auto.
  exists r3, r2'; split_ands; last done.
  - by rewrite -assoc.
  - constructor; apply pvs_intro; auto.
Qed.
Lemma wp_frame_r E e Φ R : (wp E e Φ ★ R) ⊑ wp E e (λ v, Φ v ★ R).
Proof.
  intros r' n Hvalid (r&rR&Hr&Hwp&?); revert Hvalid.
  rewrite Hr; clear Hr; revert e r Hwp.
  induction n as [n IH] using lt_wf_ind; intros e r1.
  destruct 1 as [|n r e ? Hgo]=>?.
  { constructor; apply pvs_frame_r; auto. exists r, rR; eauto. }
  constructor; [done|]=> rf k Ef σ1 ???.
  destruct (Hgo (rR⋅rf) k Ef σ1) as [Hsafe Hstep]; auto.
  { by rewrite assoc. }
  split; [done|intros e2 σ2 ef ?].
  destruct (Hstep e2 σ2 ef) as (r2&r2'&?&?&?); auto.
  exists (r2 ⋅ rR), r2'; split_ands; auto.
  - by rewrite -(assoc _ r2)
      (comm _ rR) !assoc -(assoc _ _ rR).
  - apply IH; eauto using uPred_weaken.
Qed.
Lemma wp_frame_later_r E e Φ R :
  to_val e = None → (wp E e Φ ★ ▷ R) ⊑ wp E e (λ v, Φ v ★ R).
Proof.
  intros He r' n Hvalid (r&rR&Hr&Hwp&?); revert Hvalid; rewrite Hr; clear Hr.
  destruct Hwp as [|n r e ? Hgo]; [by rewrite to_of_val in He|].
  constructor; [done|]=>rf k Ef σ1 ???; destruct n as [|n]; first omega.
  destruct (Hgo (rR⋅rf) k Ef σ1) as [Hsafe Hstep];rewrite ?assoc;auto.
  split; [done|intros e2 σ2 ef ?].
  destruct (Hstep e2 σ2 ef) as (r2&r2'&?&?&?); auto.
  exists (r2 ⋅ rR), r2'; split_ands; auto.
  - by rewrite -(assoc _ r2)
      (comm _ rR) !assoc -(assoc _ _ rR).
  - apply wp_frame_r; [auto|exists r2, rR; split_ands; auto].
    eapply uPred_weaken with rR n; eauto.
Qed.
Lemma wp_bind `{LanguageCtx Λ K} E e Φ :
  wp E e (λ v, wp E (K (of_val v)) Φ) ⊑ wp E (K e) Φ.
Proof.
  intros r n; revert e r; induction n as [n IH] using lt_wf_ind=> e r ?.
  destruct 1 as [|n r e ? Hgo]; [by apply pvs_wp|].
  constructor; auto using fill_not_val=> rf k Ef σ1 ???.
  destruct (Hgo rf k Ef σ1) as [Hsafe Hstep]; auto.
  split.
  { destruct Hsafe as (e2&σ2&ef&?).
    by exists (K e2), σ2, ef; apply fill_step. }
  intros e2 σ2 ef ?.
  destruct (fill_step_inv e σ1 e2 σ2 ef) as (e2'&->&?); auto.
  destruct (Hstep e2' σ2 ef) as (r2&r2'&?&?&?); auto.
  exists r2, r2'; split_ands; try eapply IH; eauto.
Qed.

(** * Derived rules *)
Opaque uPred_holds.
Import uPred.
Lemma wp_mono E e Φ Ψ : (∀ v, Φ v ⊑ Ψ v) → wp E e Φ ⊑ wp E e Ψ.
Proof. by apply wp_mask_frame_mono. Qed.
Global Instance wp_mono' E e :
  Proper (pointwise_relation _ (⊑) ==> (⊑)) (@wp Λ Σ E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Lemma wp_strip_pvs E e P Φ : P ⊑ wp E e Φ → pvs E E P ⊑ wp E e Φ.
Proof. move=>->. by rewrite pvs_wp. Qed.
Lemma wp_value E Φ e v : to_val e = Some v → Φ v ⊑ wp E e Φ.
Proof. intros; rewrite -(of_to_val e v) //; by apply wp_value'. Qed.
Lemma wp_value_pvs E Φ e v : to_val e = Some v → pvs E E (Φ v) ⊑ wp E e Φ.
Proof. intros. rewrite -wp_pvs. rewrite -wp_value //. Qed.
Lemma wp_frame_l E e Φ R : (R ★ wp E e Φ) ⊑ wp E e (λ v, R ★ Φ v).
Proof. setoid_rewrite (comm _ R); apply wp_frame_r. Qed.
Lemma wp_frame_later_l E e Φ R :
  to_val e = None → (▷ R ★ wp E e Φ) ⊑ wp E e (λ v, R ★ Φ v).
Proof.
  rewrite (comm _ (▷ R)%I); setoid_rewrite (comm _ R).
  apply wp_frame_later_r.
Qed.
Lemma wp_always_l E e Φ R `{!AlwaysStable R} :
  (R ∧ wp E e Φ) ⊑ wp E e (λ v, R ∧ Φ v).
Proof. by setoid_rewrite (always_and_sep_l _ _); rewrite wp_frame_l. Qed.
Lemma wp_always_r E e Φ R `{!AlwaysStable R} :
  (wp E e Φ ∧ R) ⊑ wp E e (λ v, Φ v ∧ R).
Proof. by setoid_rewrite (always_and_sep_r _ _); rewrite wp_frame_r. Qed.
Lemma wp_impl_l E e Φ Ψ : ((□ ∀ v, Φ v → Ψ v) ∧ wp E e Φ) ⊑ wp E e Ψ.
Proof.
  rewrite wp_always_l; apply wp_mono=> // v.
  by rewrite always_elim (forall_elim v) impl_elim_l.
Qed.
Lemma wp_impl_r E e Φ Ψ : (wp E e Φ ∧ □ ∀ v, Φ v → Ψ v) ⊑ wp E e Ψ.
Proof. by rewrite comm wp_impl_l. Qed.
Lemma wp_mask_weaken E1 E2 e Φ : E1 ⊆ E2 → wp E1 e Φ ⊑ wp E2 e Φ.
Proof. auto using wp_mask_frame_mono. Qed.

(** * Weakest-pre is a FSA. *)
Definition wp_fsa (e : expr Λ) : FSA Λ Σ (val Λ) := λ E, wp E e.
Global Instance wp_fsa_prf : FrameShiftAssertion (atomic e) (wp_fsa e).
Proof.
  rewrite /wp_fsa; split; auto using wp_mask_frame_mono, wp_atomic, wp_frame_r.
  intros E Φ. by rewrite -(pvs_wp E e Φ) -(wp_pvs E e Φ).
Qed.
End wp.
