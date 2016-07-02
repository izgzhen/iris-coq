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

Lemma ht_lift_step E1 E2 P Pσ1 Φ1 Φ2 Ψ e1 :
  E2 ⊆ E1 → to_val e1 = None →
  (P ={E1,E2}=> ∃ σ1, ■ reducible e1 σ1 ∧
      ▷ ownP σ1 ★ ▷ Pσ1 σ1) ∧
   (∀ σ1 e2 σ2 ef, ■ prim_step e1 σ1 e2 σ2 ef ★ ownP σ2 ★ Pσ1 σ1
                 ={E2,E1}=> Φ1 e2 σ2 ef ★ Φ2 e2 σ2 ef) ∧
   (∀ e2 σ2 ef, {{ Φ1 e2 σ2 ef }} e2 @ E1 {{ Ψ }}) ∧
   (∀ e2 σ2 ef, {{ Φ2 e2 σ2 ef }} ef ?@ ⊤ {{ _, True }})
  ⊢ {{ P }} e1 @ E1 {{ Ψ }}.
Proof.
  iIntros {??} "#(#Hvs&HΦ&He2&Hef) ! HP".
  iApply (wp_lift_step E1 E2 _ e1); auto.
  iPvs ("Hvs" with "HP") as {σ1} "(%&Hσ&HP)"; first set_solver.
  iPvsIntro. iExists σ1. repeat iSplit. by eauto. iFrame.
  iNext. iIntros {e2 σ2 ef} "[#Hφ Hown]".
  iSpecialize ("HΦ" $! σ1 e2 σ2 ef with "[-]"). by iFrame "Hφ HP Hown".
  iPvs "HΦ" as "[H1 H2]"; first by set_solver. iPvsIntro. iSplitL "H1".
  - by iApply "He2".
  - destruct ef as [e|]; last done. by iApply ("Hef" $! _ _ (Some e)).
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
  set (φ' (_:state Λ) e σ ef := is_Some (to_val e) ∧ φ e σ ef).
  iApply (ht_lift_step E E _ (λ σ1', P ∧ σ1 = σ1')%I
    (λ e2 σ2 ef, ownP σ2 ★ ■ (φ' σ1 e2 σ2 ef))%I (λ e2 σ2 ef, ■ φ e2 σ2 ef ★ P)%I);
    try by (eauto using atomic_not_val).
  repeat iSplit.
  - iIntros "![Hσ1 HP]". iExists σ1. iPvsIntro.
    iSplit. by eauto using atomic_step. iFrame. by auto.
  - iIntros {? e2 σ2 ef} "! (%&Hown&HP&%)". iPvsIntro. subst.
    iFrame. iSplit; iPureIntro; auto. split; eauto using atomic_step.
  - iIntros {e2 σ2 ef} "! [Hown #Hφ]"; iDestruct "Hφ" as %[[v2 <-%of_to_val] ?].
    iApply wp_value'. iExists σ2, ef. by iSplit.
  - done.
Qed.

Lemma ht_lift_pure_step E (φ : expr Λ → option (expr Λ) → Prop) P P' Ψ e1 :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2 ef, prim_step e1 σ1 e2 σ2 ef → σ1 = σ2 ∧ φ e2 ef) →
  (∀ e2 ef, {{ ■ φ e2 ef ★ P }} e2 @ E {{ Ψ }}) ∧
    (∀ e2 ef, {{ ■ φ e2 ef ★ P' }} ef ?@ ⊤ {{ _, True }})
  ⊢ {{ ▷(P ★ P') }} e1 @ E {{ Ψ }}.
Proof.
  iIntros {? Hsafe Hstep} "[#He2 #Hef] ! HP".
  iApply (wp_lift_pure_step E φ _ e1); auto.
  iNext; iIntros {e2 ef Hφ}. iDestruct "HP" as "[HP HP']"; iSplitL "HP".
  - iApply "He2"; by iSplit.
  - destruct ef as [e|]; last done.
    iApply ("Hef" $! _ (Some e)); by iSplit.
Qed.

Lemma ht_lift_pure_det_step
    E (φ : expr Λ → option (expr Λ) → Prop) P P' Ψ e1 e2 ef :
  to_val e1 = None →
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2' σ2 ef', prim_step e1 σ1 e2' σ2 ef' → σ1 = σ2 ∧ e2 = e2' ∧ ef = ef')→
  {{ P }} e2 @ E {{ Ψ }} ∧ {{ P' }} ef ?@ ⊤ {{ _, True }}
  ⊢ {{ ▷(P ★ P') }} e1 @ E {{ Ψ }}.
Proof.
  iIntros {? Hsafe Hdet} "[#He2 #Hef]".
  iApply (ht_lift_pure_step _ (λ e2' ef', e2 = e2' ∧ ef = ef')); eauto.
  iSplit; iIntros {e2' ef'}.
  - iIntros "! [#He ?]"; iDestruct "He" as %[-> ->]. by iApply "He2".
  - destruct ef' as [e'|]; last done.
    iIntros "! [#He ?]"; iDestruct "He" as %[-> ->]. by iApply "Hef".
Qed.
End lifting.
