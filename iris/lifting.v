Require Export iris.weakestpre.
Require Import iris.wsat.
Local Hint Extern 10 (_ ≤ _) => omega.
Local Hint Extern 100 (@eq coPset _ _) => solve_elem_of.
Local Hint Extern 10 (✓{_} _) =>
  repeat match goal with H : wsat _ _ _ _ |- _ => apply wsat_valid in H end;
  solve_validN.

Section lifting.
Context {Σ : iParam}.
Implicit Types v : ival Σ.
Implicit Types e : iexpr Σ.
Implicit Types σ : istate Σ.

Lemma wp_lift_step E1 E2
    (φ : iexpr Σ → istate Σ → option (iexpr Σ) → Prop) Q e1 σ1 :
  E1 ⊆ E2 → to_val e1 = None →
  (∃ e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef) →
  (∀ e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → φ e2 σ2 ef) →
  pvs E2 E1 (ownP σ1 ★ ▷ ∀ e2 σ2 ef, (■ φ e2 σ2 ef ∧ ownP σ2) -★
    pvs E1 E2 (wp E2 e2 Q ★ default True ef (flip (wp coPset_all) (λ _, True))))
  ⊑ wp E2 e1 Q.
Proof.
  intros ? He Hsafe Hstep r n ? Hvs; constructor; auto.
  intros rf k Ef σ1' ???; destruct (Hvs rf (S k) Ef σ1')
    as (r'&(r1&r2&?&?&Hwp)&Hws); auto; clear Hvs; cofe_subst r'.
  destruct (wsat_update_pst k (E1 ∪ Ef) σ1 σ1' r1 (r2 ⋅ rf)) as [-> Hws'].
  { by apply ownP_spec; auto. }
  { by rewrite (associative _). }
  constructor; [done|intros e2 σ2 ef ?; specialize (Hws' σ2)].
  destruct (λ H1 H2 H3, Hwp e2 σ2 ef (update_pst σ2 r1) k H1 H2 H3 rf k Ef σ2)
    as (r'&(r1'&r2'&?&?&?)&?); auto; cofe_subst r'.
  { split. destruct k; try eapply Hstep; eauto. apply ownP_spec; auto. }
  { rewrite (commutative _ r2) -(associative _); eauto using wsat_le. }
  by exists r1', r2'; split_ands; [| |by intros ? ->].
Qed.
Lemma wp_lift_pure_step E (φ : iexpr Σ → option (iexpr Σ) → Prop) Q e1 :
  to_val e1 = None →
  (∀ σ1, ∃ e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef) →
  (∀ σ1 e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → σ1 = σ2 ∧ φ e2 ef) →
  (▷ ∀ e2 ef, ■ φ e2 ef →
    wp E e2 Q ★ default True ef (flip (wp coPset_all) (λ _, True)))
  ⊑ wp E e1 Q.
Proof.
  intros He Hsafe Hstep r [|n] ?; [done|]; intros Hwp; constructor; auto.
  intros rf k Ef σ1 ???; split; [done|].
  intros e2 σ2 ef ?; destruct (Hstep σ1 e2 σ2 ef); auto; subst.
  destruct (Hwp e2 ef r k) as (r1&r2&Hr&?&?); auto; [by destruct k|].
  exists r1,r2; split_ands; [rewrite -Hr| |by intros ? ->]; eauto using wsat_le.
Qed.
End lifting.
