From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import wsat ownership.
From iris.proofmode Require Import pviewshifts.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 100 (_ ⊥ _) => set_solver.
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

Notation wp_fork ef := (default True ef (flip (wp ⊤) (λ _, True)))%I.

Lemma wp_lift_step E1 E2 Φ e1 :
  E2 ⊆ E1 → to_val e1 = None →
  (|={E1,E2}=> ∃ σ1, ■ reducible e1 σ1 ∧ ▷ ownP σ1 ★
       ▷ ∀ e2 σ2 ef, (■ prim_step e1 σ1 e2 σ2 ef ∧ ownP σ2)
                     ={E2,E1}=★ WP e2 @ E1 {{ Φ }} ★ wp_fork ef)
  ⊢ WP e1 @ E1 {{ Φ }}.
Proof.
  intros ? He. rewrite pvs_eq wp_eq.
  uPred.unseal; split=> n r ? Hvs; constructor; auto. intros k Ef σ1' rf ???.
  destruct (Hvs (S k) Ef σ1' rf) as (r'&(σ1&Hsafe&r1&r2&?&?&Hwp)&Hws);
    auto; clear Hvs; cofe_subst r'.
  destruct (wsat_update_pst k (E2 ∪ Ef) σ1 σ1' r1 (r2 ⋅ rf)) as [-> Hws'].
  { apply equiv_dist. rewrite -(ownP_spec k); auto. }
  { by rewrite assoc. }
  constructor; [done|intros e2 σ2 ef ?; specialize (Hws' σ2)].
  destruct (λ H1 H2 H3, Hwp e2 σ2 ef k (update_pst σ2 r1) H1 H2 H3 k Ef σ2 rf)
    as (r'&(r1'&r2'&?&?&?)&?); auto; cofe_subst r'.
  { split. done. apply ownP_spec; auto. }
  { rewrite (comm _ r2) -assoc; eauto using wsat_le. }
  exists r1', r2'; split_and?; try done. by uPred.unseal; intros ? ->.
Qed.

Lemma wp_lift_pure_step E Φ e1 :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → σ1 = σ2) →
  (▷ ∀ e2 ef σ, ■ prim_step e1 σ e2 σ ef → WP e2 @ E {{ Φ }} ★ wp_fork ef)
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  intros He Hsafe Hstep; rewrite wp_eq; uPred.unseal.
  split=> n r ? Hwp; constructor; auto.
  intros k Ef σ1 rf ???; split; [done|]. destruct n as [|n]; first lia.
  intros e2 σ2 ef ?; destruct (Hstep σ1 e2 σ2 ef); auto; subst.
  destruct (Hwp e2 ef σ1 k r) as (r1&r2&Hr&?&?); auto.
  exists r1,r2; split_and?; try done.
  - rewrite -Hr; eauto using wsat_le.
  - uPred.unseal; by intros ? ->.
Qed.

(** Derived lifting lemmas. *)
Import uPred.

Lemma wp_lift_atomic_step {E Φ} e1 σ1 :
  atomic e1 →
  reducible e1 σ1 →
  ▷ ownP σ1 ★ ▷ (∀ v2 σ2 ef,
    ■ prim_step e1 σ1 (of_val v2) σ2 ef ∧ ownP σ2 -★ (|={E}=> Φ v2) ★ wp_fork ef)
  ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros {??} "[Hσ1 Hwp]". iApply (wp_lift_step E E _ e1); auto using atomic_not_val.
  iPvsIntro. iExists σ1. repeat iSplit; eauto 10 using atomic_step.
  iFrame. iNext. iIntros {e2 σ2 ef} "[% Hσ2]".
  edestruct @atomic_step as [v2 Hv%of_to_val]; eauto. subst e2.
  iDestruct ("Hwp" $! v2 σ2 ef with "[Hσ2]") as "[HΦ ?]". by eauto.
  iFrame. iPvs "HΦ". iPvsIntro. iApply wp_value; auto using to_of_val.
Qed.

Lemma wp_lift_atomic_det_step {E Φ e1} σ1 v2 σ2 ef :
  atomic e1 →
  reducible e1 σ1 →
  (∀ e2' σ2' ef', prim_step e1 σ1 e2' σ2' ef' →
                  σ2 = σ2' ∧ to_val e2' = Some v2 ∧ ef = ef') →
  ▷ ownP σ1 ★ ▷ (ownP σ2 -★ (|={E}=> Φ v2) ★ wp_fork ef) ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros {?? Hdet} "[Hσ1 Hσ2]". iApply (wp_lift_atomic_step _ σ1); try done.
  iFrame. iNext. iIntros {v2' σ2' ef'} "[% Hσ2']".
  edestruct Hdet as (->&->%of_to_val%(inj of_val)&->). done. by iApply "Hσ2".
Qed.

Lemma wp_lift_pure_det_step {E Φ} e1 e2 ef :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2' σ2 ef', prim_step e1 σ1 e2' σ2 ef' → σ1 = σ2 ∧ e2 = e2' ∧ ef = ef')→
  ▷ (WP e2 @ E {{ Φ }} ★ wp_fork ef) ⊢ WP e1 @ E {{ Φ }}.
Proof.
  iIntros {?? Hpuredet} "?". iApply (wp_lift_pure_step E); try done.
  by intros; eapply Hpuredet. iNext. by iIntros {e' ef' σ (_&->&->)%Hpuredet}.
Qed.
End lifting.
