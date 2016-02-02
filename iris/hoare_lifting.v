Require Export iris.hoare iris.lifting.

Local Notation "{{ P } } ef ?@ E {{ Q } }" :=
  (default True%I ef (λ e, ht E P e Q))
  (at level 74, format "{{  P  } }  ef  ?@  E  {{  Q  } }") : uPred_scope.
Local Notation "{{ P } } ef ?@ E {{ Q } }" :=
  (True ⊑ default True ef (λ e, ht E P e Q))
  (at level 74, format "{{  P  } }  ef  ?@  E  {{  Q  } }") : C_scope.

Section lifting.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types e : expr Λ.
Implicit Types P : iProp Λ Σ.
Implicit Types R : val Λ → iProp Λ Σ.
Import uPred.

Lemma ht_lift_step E1 E2
    (φ : expr Λ → state Λ → option (expr Λ) → Prop) P P' Q1 Q2 R e1 σ1 :
  E1 ⊆ E2 → to_val e1 = None →
  reducible e1 σ1 →
  (∀ e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → φ e2 σ2 ef) →
  (P >{E2,E1}> (ownP σ1 ★ ▷ P') ∧ ∀ e2 σ2 ef,
    (■ φ e2 σ2 ef ★ ownP σ2 ★ P') >{E1,E2}> (Q1 e2 σ2 ef ★ Q2 e2 σ2 ef) ∧
    {{ Q1 e2 σ2 ef }} e2 @ E2 {{ R }} ∧
    {{ Q2 e2 σ2 ef }} ef ?@ coPset_all {{ λ _, True }})
  ⊑ {{ P }} e1 @ E2 {{ R }}.
Proof.
  intros ?? Hsafe Hstep; apply (always_intro' _ _), impl_intro_l.
  rewrite (associative _ P) {1}/vs always_elim impl_elim_r pvs_always_r.
  rewrite -(wp_lift_step E1 E2 φ _ e1 σ1) //; apply pvs_mono.
  rewrite always_and_sep_r' -associative; apply sep_mono; first done.
  rewrite (later_intro (∀ _, _)) -later_sep; apply later_mono.
  apply forall_intro=>e2; apply forall_intro=>σ2; apply forall_intro=>ef.
  rewrite (forall_elim e2) (forall_elim σ2) (forall_elim ef).
  apply wand_intro_l; rewrite !always_and_sep_l'.
  rewrite (associative _ _ P') -(associative _ _ _ P') associative.
  rewrite {1}/vs -always_wand_impl always_elim wand_elim_r.
  rewrite pvs_frame_r; apply pvs_mono.
  rewrite (commutative _ (Q1 _ _ _)) -associative (associative _ (Q1 _ _ _)).
  rewrite {1}/ht -always_wand_impl always_elim wand_elim_r.
  rewrite associative (commutative _ _ (wp _ _ _)) -associative.
  apply sep_mono; first done.
  destruct ef as [e'|]; simpl; [|by apply const_intro].
  rewrite {1}/ht -always_wand_impl always_elim wand_elim_r; apply wp_mono=>v.
  by apply const_intro.
Qed.
Lemma ht_lift_atomic_step
    E (φ : expr Λ → state Λ → option (expr Λ) → Prop) P e1 σ1 :
  atomic e1 →
  reducible e1 σ1 →
  (∀ e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → φ e2 σ2 ef) →
  (∀ e2 σ2 ef, {{ ■ φ e2 σ2 ef ★ P }} ef ?@ coPset_all {{ λ _, True }}) ⊑
  {{ ownP σ1 ★ ▷ P }} e1 @ E {{ λ v, ∃ σ2 ef, ownP σ2 ★ ■ φ (of_val v) σ2 ef }}.
Proof.
  intros ? Hsafe Hstep; set (φ' e σ ef := is_Some (to_val e) ∧ φ e σ ef).
  rewrite -(ht_lift_step E E φ'  _ P
    (λ e2 σ2 ef, ownP σ2 ★ ■ (φ' e2 σ2 ef))%I
    (λ e2 σ2 ef, ■ φ e2 σ2 ef ★ P)%I);
    try by (rewrite /φ'; eauto using atomic_not_val, atomic_step).
  apply and_intro; [by rewrite -vs_reflexive; apply const_intro|].
  apply forall_mono=>e2; apply forall_mono=>σ2; apply forall_mono=>ef.
  apply and_intro; [|apply and_intro; [|done]].
  * rewrite -vs_impl; apply (always_intro' _ _),impl_intro_l;rewrite and_elim_l.
    rewrite !associative; apply sep_mono; last done.
    rewrite -!always_and_sep_l' -!always_and_sep_r'; apply const_elim_l=>-[??].
    by repeat apply and_intro; try apply const_intro.
  * apply (always_intro' _ _), impl_intro_l; rewrite and_elim_l.
    rewrite -always_and_sep_r'; apply const_elim_r=>-[[v Hv] ?].
    rewrite -(of_to_val e2 v) // -wp_value -pvs_intro.
    rewrite -(exist_intro σ2) -(exist_intro ef) (of_to_val e2) //.
    by rewrite -always_and_sep_r'; apply and_intro; try apply const_intro.
Qed.
Lemma ht_lift_pure_step E (φ : expr Λ → option (expr Λ) → Prop) P P' Q e1 :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → σ1 = σ2 ∧ φ e2 ef) →
  (∀ e2 ef,
    {{ ■ φ e2 ef ★ P }} e2 @ E {{ Q }} ∧
    {{ ■ φ e2 ef ★ P' }} ef ?@ coPset_all {{ λ _, True }})
  ⊑ {{ ▷(P ★ P') }} e1 @ E {{ Q }}.
Proof.
  intros ? Hsafe Hstep; apply (always_intro' _ _), impl_intro_l.
  rewrite -(wp_lift_pure_step E φ _ e1) //.
  rewrite (later_intro (∀ _, _)) -later_and; apply later_mono.
  apply forall_intro=>e2; apply forall_intro=>ef; apply impl_intro_l.
  rewrite (forall_elim e2) (forall_elim ef).
  rewrite always_and_sep_l' !always_and_sep_r' {1}(always_sep_dup' (■ _)).
  rewrite {1}(associative _ (_ ★ _)%I) -(associative _ (■ _)%I).
  rewrite (associative _ (■ _)%I P) -{1}(commutative _ P) -(associative _ P).
  rewrite (associative _ (■ _)%I) associative -(associative _ (■ _ ★ P))%I.
  rewrite (commutative _ (■ _ ★ P'))%I associative.
  rewrite {1}/ht -always_wand_impl always_elim wand_elim_r.
  rewrite -associative; apply sep_mono; first done.
  destruct ef as [e'|]; simpl; [|by apply const_intro].
  rewrite {1}/ht -always_wand_impl always_elim wand_elim_r; apply wp_mono=>v.
  by apply const_intro.
Qed.
Lemma ht_lift_pure_det_step
    E (φ : expr Λ → option (expr Λ) → Prop) P P' Q e1 e2 ef :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2' σ2 ef', prim_step e1 σ1 e2' σ2 ef' → σ1 = σ2 ∧ e2 = e2' ∧ ef = ef')→
  ({{ P }} e2 @ E {{ Q }} ∧ {{ P' }} ef ?@ coPset_all {{ λ _, True }})
  ⊑ {{ ▷(P ★ P') }} e1 @ E {{ Q }}.
Proof.
  intros ? Hsafe Hdet.
  rewrite -(ht_lift_pure_step _ (λ e2' ef', e2 = e2' ∧ ef = ef')); eauto.
  apply forall_intro=>e2'; apply forall_intro=>ef'; apply and_mono.
  * apply (always_intro' _ _), impl_intro_l.
    rewrite -always_and_sep_l' -associative; apply const_elim_l=>-[??]; subst.
    by rewrite /ht always_elim impl_elim_r.
  * destruct ef' as [e'|]; simpl; [|by apply const_intro].
    apply (always_intro' _ _), impl_intro_l.
    rewrite -always_and_sep_l' -associative; apply const_elim_l=>-[??]; subst.
    by rewrite /= /ht always_elim impl_elim_r.
Qed.
End lifting.
