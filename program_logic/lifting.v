From program_logic Require Export weakestpre.
From program_logic Require Import wsat ownership.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 100 (@eq coPset _ _) => set_solver.
Local Hint Extern 10 (✓{_} _) =>
  repeat match goal with
  | H : wsat _ _ _ _ |- _ => apply wsat_valid in H; last omega
  end; solve_validN.

Section lifting.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Λ Σ.
Implicit Types Φ : val Λ → iProp Λ Σ.
Transparent uPred_holds.

Notation wp_fork ef := (default True ef (flip (wp ⊤) (λ _, True)))%I.

Lemma wp_lift_step E1 E2
    (φ : expr Λ → state Λ → option (expr Λ) → Prop) Φ e1 σ1 :
  E1 ⊆ E2 → to_val e1 = None →
  reducible e1 σ1 →
  (∀ e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → φ e2 σ2 ef) →
  (|={E2,E1}=> ownP σ1 ★ ▷ ∀ e2 σ2 ef,
    (■ φ e2 σ2 ef ∧ ownP σ2) -★ |={E1,E2}=> || e2 @ E2 {{ Φ }} ★ wp_fork ef)
  ⊑ || e1 @ E2 {{ Φ }}.
Proof.
  intros ? He Hsafe Hstep n r ? Hvs; constructor; auto.
  intros rf k Ef σ1' ???; destruct (Hvs rf (S k) Ef σ1')
    as (r'&(r1&r2&?&?&Hwp)&Hws); auto; clear Hvs; cofe_subst r'.
  destruct (wsat_update_pst k (E1 ∪ Ef) σ1 σ1' r1 (r2 ⋅ rf)) as [-> Hws'].
  { by apply ownP_spec; auto. }
  { by rewrite assoc. }
  constructor; [done|intros e2 σ2 ef ?; specialize (Hws' σ2)].
  destruct (λ H1 H2 H3, Hwp e2 σ2 ef k (update_pst σ2 r1) H1 H2 H3 rf k Ef σ2)
    as (r'&(r1'&r2'&?&?&?)&?); auto; cofe_subst r'.
  { split. destruct k; try eapply Hstep; eauto. apply ownP_spec; auto. }
  { rewrite (comm _ r2) -assoc; eauto using wsat_le. }
  by exists r1', r2'; split_and?; [| |by intros ? ->].
Qed.

Lemma wp_lift_pure_step E (φ : expr Λ → option (expr Λ) → Prop) Φ e1 :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → σ1 = σ2 ∧ φ e2 ef) →
  (▷ ∀ e2 ef, ■ φ e2 ef → || e2 @ E {{ Φ }} ★ wp_fork ef) ⊑ || e1 @ E {{ Φ }}.
Proof.
  intros He Hsafe Hstep n r ? Hwp; constructor; auto.
  intros rf k Ef σ1 ???; split; [done|]. destruct n as [|n]; first lia.
  intros e2 σ2 ef ?; destruct (Hstep σ1 e2 σ2 ef); auto; subst.
  destruct (Hwp e2 ef k r) as (r1&r2&Hr&?&?); auto.
  exists r1,r2; split_and?; [rewrite -Hr| |by intros ? ->]; eauto using wsat_le.
Qed.

(** Derived lifting lemmas. *)
Opaque uPred_holds.
Import uPred.

Lemma wp_lift_atomic_step {E Φ} e1
    (φ : val Λ → state Λ → option (expr Λ) → Prop) σ1 :
  to_val e1 = None →
  reducible e1 σ1 →
  (∀ e2 σ2 ef,
    prim_step e1 σ1 e2 σ2 ef → ∃ v2, to_val e2 = Some v2 ∧ φ v2 σ2 ef) →
  (ownP σ1 ★ ▷ ∀ v2 σ2 ef, ■ φ v2 σ2 ef ∧ ownP σ2 -★ Φ v2 ★ wp_fork ef)
  ⊑ || e1 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_step E E (λ e2 σ2 ef, ∃ v2,
    to_val e2 = Some v2 ∧ φ v2 σ2 ef) _ e1 σ1) //; [].
  rewrite -pvs_intro. apply sep_mono, later_mono; first done.
  apply forall_intro=>e2'; apply forall_intro=>σ2'.
  apply forall_intro=>ef; apply wand_intro_l.
  rewrite always_and_sep_l -assoc -always_and_sep_l.
  apply const_elim_l=>-[v2' [Hv ?]] /=.
  rewrite -pvs_intro.
  rewrite (forall_elim v2') (forall_elim σ2') (forall_elim ef) const_equiv //.
  by rewrite left_id wand_elim_r -(wp_value _ _ e2' v2').
Qed.

Lemma wp_lift_atomic_det_step {E Φ e1} σ1 v2 σ2 ef :
  to_val e1 = None →
  reducible e1 σ1 →
  (∀ e2' σ2' ef', prim_step e1 σ1 e2' σ2' ef' →
    σ2 = σ2' ∧ to_val e2' = Some v2 ∧ ef = ef') →
  (ownP σ1 ★ ▷ (ownP σ2 -★ Φ v2 ★ wp_fork ef)) ⊑ || e1 @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_atomic_step _ (λ v2' σ2' ef',
    σ2 = σ2' ∧ v2 = v2' ∧ ef = ef') σ1) //; last naive_solver.
  apply sep_mono, later_mono; first done.
  apply forall_intro=>e2'; apply forall_intro=>σ2'; apply forall_intro=>ef'.
  apply wand_intro_l.
  rewrite always_and_sep_l -assoc -always_and_sep_l.
  apply const_elim_l=>-[-> [-> ->]] /=. by rewrite wand_elim_r.
Qed.

Lemma wp_lift_pure_det_step {E Φ} e1 e2 ef :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2' σ2 ef', prim_step e1 σ1 e2' σ2 ef' → σ1 = σ2 ∧ e2 = e2' ∧ ef = ef')→
  ▷ (|| e2 @ E {{ Φ }} ★ wp_fork ef) ⊑ || e1 @ E {{ Φ }}.
Proof.
  intros.
  rewrite -(wp_lift_pure_step E (λ e2' ef', e2 = e2' ∧ ef = ef') _ e1) //=.
  apply later_mono, forall_intro=>e'; apply forall_intro=>ef'.
  by apply impl_intro_l, const_elim_l=>-[-> ->].
Qed.

End lifting.
