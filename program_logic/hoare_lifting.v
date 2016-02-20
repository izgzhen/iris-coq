From program_logic Require Export hoare lifting.
From program_logic Require Import ownership.
Import uPred.

Local Notation "{{ P } } ef ?@ E {{ Φ } }" :=
  (default True%I ef (λ e, ht E P e Φ))
  (at level 20, P, ef, Φ at level 200,
   format "{{  P  } }  ef  ?@  E  {{  Φ  } }") : uPred_scope.
Local Notation "{{ P } } ef ?@ E {{ Φ } }" :=
  (True ⊑ default True ef (λ e, ht E P e Φ))
  (at level 20, P, ef, Φ at level 200,
   format "{{  P  } }  ef  ?@  E  {{  Φ  } }") : C_scope.

Section lifting.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types e : expr Λ.
Implicit Types P Q R : iProp Λ Σ.
Implicit Types Ψ : val Λ → iProp Λ Σ.

Lemma ht_lift_step E1 E2
    (φ : expr Λ → state Λ → option (expr Λ) → Prop) P P' Φ1 Φ2 Ψ e1 σ1 :
  E1 ⊆ E2 → to_val e1 = None →
  reducible e1 σ1 →
  (∀ e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → φ e2 σ2 ef) →
  ((P ={E2,E1}=> ▷ ownP σ1 ★ ▷ P') ∧ ∀ e2 σ2 ef,
    (■ φ e2 σ2 ef ★ ownP σ2 ★ P' ={E1,E2}=> Φ1 e2 σ2 ef ★ Φ2 e2 σ2 ef) ∧
    {{ Φ1 e2 σ2 ef }} e2 @ E2 {{ Ψ }} ∧
    {{ Φ2 e2 σ2 ef }} ef ?@ ⊤ {{ λ _, True }})
  ⊑ {{ P }} e1 @ E2 {{ Ψ }}.
Proof.
  intros ?? Hsafe Hstep; apply: always_intro. apply impl_intro_l.
  rewrite (assoc _ P) {1}/vs always_elim impl_elim_r pvs_always_r.
  rewrite -(wp_lift_step E1 E2 φ _ e1 σ1) //; apply pvs_mono.
  rewrite always_and_sep_r -assoc; apply sep_mono; first done.
  rewrite (later_intro (∀ _, _)) -later_sep; apply later_mono.
  apply forall_intro=>e2; apply forall_intro=>σ2; apply forall_intro=>ef.
  rewrite (forall_elim e2) (forall_elim σ2) (forall_elim ef).
  apply wand_intro_l; rewrite !always_and_sep_l.
  rewrite (assoc _ _ P') -(assoc _ _ _ P') assoc.
  rewrite {1}/vs -always_wand_impl always_elim wand_elim_r.
  rewrite pvs_frame_r; apply pvs_mono.
  rewrite (comm _ (Φ1 _ _ _)) -assoc (assoc _ (Φ1 _ _ _)).
  rewrite {1}/ht -always_wand_impl always_elim wand_elim_r.
  rewrite assoc (comm _ _ (wp _ _ _)) -assoc.
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
  (∀ e2 σ2 ef, {{ ■ φ e2 σ2 ef ★ P }} ef ?@ ⊤ {{ λ _, True }}) ⊑
  {{ ▷ ownP σ1 ★ ▷ P }} e1 @ E {{ λ v, ∃ σ2 ef, ownP σ2 ★ ■ φ (of_val v) σ2 ef }}.
Proof.
  intros ? Hsafe Hstep; set (φ' e σ ef := is_Some (to_val e) ∧ φ e σ ef).
  rewrite -(ht_lift_step E E φ'  _ P
    (λ e2 σ2 ef, ownP σ2 ★ ■ (φ' e2 σ2 ef))%I
    (λ e2 σ2 ef, ■ φ e2 σ2 ef ★ P)%I);
    try by (rewrite /φ'; eauto using atomic_not_val, atomic_step).
  apply and_intro; [by rewrite -vs_reflexive; apply const_intro|].
  apply forall_mono=>e2; apply forall_mono=>σ2; apply forall_mono=>ef.
  apply and_intro; [|apply and_intro; [|done]].
  - rewrite -vs_impl; apply: always_intro. apply impl_intro_l.
    rewrite and_elim_l !assoc; apply sep_mono; last done.
    rewrite -!always_and_sep_l -!always_and_sep_r; apply const_elim_l=>-[??].
    by repeat apply and_intro; try apply const_intro.
  - apply (always_intro _ _), impl_intro_l; rewrite and_elim_l.
    rewrite -always_and_sep_r; apply const_elim_r=>-[[v Hv] ?].
    rewrite -(of_to_val e2 v) // -wp_value'; [].
    rewrite -(exist_intro σ2) -(exist_intro ef) (of_to_val e2) //.
    by rewrite -always_and_sep_r; apply and_intro; try apply const_intro.
Qed.

Lemma ht_lift_pure_step E (φ : expr Λ → option (expr Λ) → Prop) P P' Ψ e1 :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → σ1 = σ2 ∧ φ e2 ef) →
  (∀ e2 ef,
    {{ ■ φ e2 ef ★ P }} e2 @ E {{ Ψ }} ∧
    {{ ■ φ e2 ef ★ P' }} ef ?@ ⊤ {{ λ _, True }})
  ⊑ {{ ▷(P ★ P') }} e1 @ E {{ Ψ }}.
Proof.
  intros ? Hsafe Hstep; apply: always_intro. apply impl_intro_l.
  rewrite -(wp_lift_pure_step E φ _ e1) //.
  rewrite (later_intro (∀ _, _)) -later_and; apply later_mono.
  apply forall_intro=>e2; apply forall_intro=>ef; apply impl_intro_l.
  rewrite (forall_elim e2) (forall_elim ef).
  rewrite always_and_sep_l !always_and_sep_r {1}(always_sep_dup (■ _)).
  rewrite {1}(assoc _ (_ ★ _)%I) -(assoc _ (■ _)%I).
  rewrite (assoc _ (■ _)%I P) -{1}(comm _ P) -(assoc _ P).
  rewrite (assoc _ (■ _)%I) assoc -(assoc _ (■ _ ★ P))%I.
  rewrite (comm _ (■ _ ★ P'))%I assoc.
  rewrite {1}/ht -always_wand_impl always_elim wand_elim_r.
  rewrite -assoc; apply sep_mono; first done.
  destruct ef as [e'|]; simpl; [|by apply const_intro].
  rewrite {1}/ht -always_wand_impl always_elim wand_elim_r; apply wp_mono=>v.
  by apply const_intro.
Qed.

Lemma ht_lift_pure_det_step
    E (φ : expr Λ → option (expr Λ) → Prop) P P' Ψ e1 e2 ef :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2' σ2 ef', prim_step e1 σ1 e2' σ2 ef' → σ1 = σ2 ∧ e2 = e2' ∧ ef = ef')→
  ({{ P }} e2 @ E {{ Ψ }} ∧ {{ P' }} ef ?@ ⊤ {{ λ _, True }})
  ⊑ {{ ▷(P ★ P') }} e1 @ E {{ Ψ }}.
Proof.
  intros ? Hsafe Hdet.
  rewrite -(ht_lift_pure_step _ (λ e2' ef', e2 = e2' ∧ ef = ef')); eauto.
  apply forall_intro=>e2'; apply forall_intro=>ef'; apply and_mono.
  - apply: always_intro. apply impl_intro_l.
    rewrite -always_and_sep_l -assoc; apply const_elim_l=>-[??]; subst.
    by rewrite /ht always_elim impl_elim_r.
  - destruct ef' as [e'|]; simpl; [|by apply const_intro].
    apply: always_intro. apply impl_intro_l.
    rewrite -always_and_sep_l -assoc; apply const_elim_l=>-[??]; subst.
    by rewrite /= /ht always_elim impl_elim_r.
Qed.

End lifting.
