From iris.algebra Require Import upred_tactics.
From iris.program_logic Require Export hoare lifting.
From iris.program_logic Require Import ownership.
From iris.proofmode Require Import tactics pviewshifts.

Local Notation "{{ P } } ef ?@ E {{ v , Q } }" :=
  (default True%I ef (λ e, ht E P e (λ v, Q)))
  (at level 20, P, ef, Q at level 200,
   format "{{  P  } }  ef  ?@  E  {{  v ,  Q  } }") : uPred_scope.
Local Notation "{{ P } } ef ?@ E {{ v , Q } }" :=
  (True ⊢ default True ef (λ e, ht E P e (λ v, Q)))
  (at level 20, P, ef, Q at level 200,
   format "{{  P  } }  ef  ?@  E  {{  v ,  Q  } }") : C_scope.

Section lifting.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types e : expr Λ.
Implicit Types P Q R : iProp Λ Σ.
Implicit Types Ψ : val Λ → iProp Λ Σ.

Lemma ht_lift_step E1 E2
    (φ : expr Λ → state Λ → option (expr Λ) → Prop) P P' Φ1 Φ2 Ψ e1 σ1 :
  E2 ⊆ E1 → to_val e1 = None →
  reducible e1 σ1 →
  (∀ e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → φ e2 σ2 ef) →
  ((P ={E1,E2}=> ▷ ownP σ1 ★ ▷ P') ∧
   (∀ e2 σ2 ef, ■ φ e2 σ2 ef ★ ownP σ2 ★ P' ={E2,E1}=> Φ1 e2 σ2 ef ★ Φ2 e2 σ2 ef) ∧
   (∀ e2 σ2 ef, {{ Φ1 e2 σ2 ef }} e2 @ E1 {{ Ψ }}) ∧
   (∀ e2 σ2 ef, {{ Φ2 e2 σ2 ef }} ef ?@ ⊤ {{ _, True }}))
  ⊢ {{ P }} e1 @ E1 {{ Ψ }}.
Proof.
  iIntros {?? Hsafe Hstep} "#(#Hvs&HΦ&He2&Hef) ! HP".
  iApply (wp_lift_step E1 E2 φ _ e1 σ1); auto.
  iPvs "Hvs" "HP" as "[Hσ HP]"; first set_solver.
  iPvsIntro. iNext. iSplitL "Hσ"; [done|iIntros {e2 σ2 ef} "[#Hφ Hown]"].
  iSpecialize "HΦ" {e2 σ2 ef} "! -". by iFrame "Hφ HP Hown".
  iPvs "HΦ" as "[H1 H2]"; first by set_solver.
  iPvsIntro. iSplitL "H1".
  - by iApply "He2" "!".
  - destruct ef as [e|]; last done. by iApply "Hef" {_ _ (Some e)} "!".
Qed.

Lemma ht_lift_atomic_step
    E (φ : expr Λ → state Λ → option (expr Λ) → Prop) P e1 σ1 :
  atomic e1 →
  reducible e1 σ1 →
  (∀ e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → φ e2 σ2 ef) →
  (∀ e2 σ2 ef, {{ ■ φ e2 σ2 ef ★ P }} ef ?@ ⊤ {{ _, True }}) ⊢
  {{ ▷ ownP σ1 ★ ▷ P }} e1 @ E {{ v, ∃ σ2 ef, ownP σ2 ★ ■ φ (of_val v) σ2 ef }}.
Proof.
  iIntros {? Hsafe Hstep} "#Hef".
  set (φ' e σ ef := is_Some (to_val e) ∧ φ e σ ef).
  iApply (ht_lift_step E E φ'  _ P
    (λ e2 σ2 ef, ownP σ2 ★ ■ (φ' e2 σ2 ef))%I
    (λ e2 σ2 ef, ■ φ e2 σ2 ef ★ P)%I);
    try by (rewrite /φ'; eauto using atomic_not_val, atomic_step).
  repeat iSplit.
  - by iApply vs_reflexive.
  - iIntros {e2 σ2 ef} "! (#Hφ&Hown&HP)"; iPvsIntro.
    iSplitL "Hown". by iSplit. iSplit. by iDestruct "Hφ" as %[_ ?]. done.
  - iIntros {e2 σ2 ef} "! [Hown #Hφ]"; iDestruct "Hφ" as %[[v2 <-%of_to_val] ?].
    iApply wp_value'. iExists σ2, ef. by iSplit.
  - done.
Qed.

Lemma ht_lift_pure_step E (φ : expr Λ → option (expr Λ) → Prop) P P' Ψ e1 :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → σ1 = σ2 ∧ φ e2 ef) →
  ((∀ e2 ef, {{ ■ φ e2 ef ★ P }} e2 @ E {{ Ψ }}) ∧
   (∀ e2 ef, {{ ■ φ e2 ef ★ P' }} ef ?@ ⊤ {{ _, True }}))
  ⊢ {{ ▷(P ★ P') }} e1 @ E {{ Ψ }}.
Proof.
  iIntros {? Hsafe Hstep} "[#He2 #Hef] ! HP".
  iApply (wp_lift_pure_step E φ _ e1); auto.
  iNext; iIntros {e2 ef Hφ}. iDestruct "HP" as "[HP HP']"; iSplitL "HP".
  - iApply "He2" "!"; by iSplit.
  - destruct ef as [e|]; last done. iApply "Hef" {_ (Some e)} "!"; by iSplit.
Qed.

Lemma ht_lift_pure_det_step
    E (φ : expr Λ → option (expr Λ) → Prop) P P' Ψ e1 e2 ef :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2' σ2 ef', prim_step e1 σ1 e2' σ2 ef' → σ1 = σ2 ∧ e2 = e2' ∧ ef = ef')→
  ({{ P }} e2 @ E {{ Ψ }} ∧ {{ P' }} ef ?@ ⊤ {{ _, True }})
  ⊢ {{ ▷(P ★ P') }} e1 @ E {{ Ψ }}.
Proof.
  iIntros {? Hsafe Hdet} "[#He2 #Hef]".
  iApply (ht_lift_pure_step _ (λ e2' ef', e2 = e2' ∧ ef = ef')); eauto.
  iSplit; iIntros {e2' ef'}.
  - iIntros "! [#He ?]"; iDestruct "He" as %[-> ->]. by iApply "He2".
  - destruct ef' as [e'|]; last done.
    iIntros "! [#He ?]"; iDestruct "He" as %[-> ->]. by iApply "Hef" "!".
Qed.
End lifting.
