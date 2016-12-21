From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export viewshifts.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Definition ht `{irisG Λ Σ} (p : pbit) (E : coPset) (P : iProp Σ)
    (e : expr Λ) (Φ : val Λ → iProp Σ) : iProp Σ :=
  (□ (P -∗ WP e @ p; E {{ Φ }}))%I.
Instance: Params (@ht) 5.

Notation "{{ P } } e @ p ; E {{ Φ } }" := (ht p E P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  @  p ;  E  {{  Φ  } }") : C_scope.
Notation "{{ P } } e @ E {{ Φ } }" := (ht progress E P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  @  E  {{  Φ  } }") : C_scope.
Notation "{{ P } } e @ E ? {{ Φ } }" := (ht noprogress E P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  @  E  ? {{  Φ  } }") : C_scope.
Notation "{{ P } } e {{ Φ } }" := (ht progress ⊤ P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  {{  Φ  } }") : C_scope.
Notation "{{ P } } e ? {{ Φ } }" := (ht noprogress ⊤ P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  ? {{  Φ  } }") : C_scope.

Notation "{{ P } } e @ p ; E {{ v , Q } }" := (ht p E P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  @  p ;  E  {{  v ,  Q  } }") : C_scope.
Notation "{{ P } } e @ E {{ v , Q } }" := (ht progress E P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  @  E  {{  v ,  Q  } }") : C_scope.
Notation "{{ P } } e @ E ? {{ v , Q } }" := (ht noprogress E P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  @  E  ? {{  v ,  Q  } }") : C_scope.
Notation "{{ P } } e {{ v , Q } }" := (ht progress ⊤ P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  {{  v ,  Q  } }") : C_scope.
Notation "{{ P } } e ? {{ v , Q } }" := (ht noprogress ⊤ P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  ? {{  v ,  Q  } }") : C_scope.

Section hoare.
Context `{irisG Λ Σ}.
Implicit Types p : pbit.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Import uPred.

Global Instance ht_ne p E n :
  Proper (dist n ==> eq ==> pointwise_relation _ (dist n) ==> dist n) (ht p E).
Proof. solve_proper. Qed.
Global Instance ht_proper p E :
  Proper ((≡) ==> eq ==> pointwise_relation _ (≡) ==> (≡)) (ht p E).
Proof. solve_proper. Qed.
Lemma ht_mono p E P P' Φ Φ' e :
  (P ⊢ P') → (∀ v, Φ' v ⊢ Φ v) → {{ P' }} e @ p; E {{ Φ' }} ⊢ {{ P }} e @ p; E {{ Φ }}.
Proof. by intros; apply persistently_mono, wand_mono, wp_mono. Qed.
Global Instance ht_mono' p E :
  Proper (flip (⊢) ==> eq ==> pointwise_relation _ (⊢) ==> (⊢)) (ht p E).
Proof. solve_proper. Qed.

Lemma ht_alt p E P Φ e : (P ⊢ WP e @ p; E {{ Φ }}) → {{ P }} e @ p; E {{ Φ }}.
Proof. iIntros (Hwp) "!# HP". by iApply Hwp. Qed.

Lemma ht_val p E v : {{ True }} of_val v @ p; E {{ v', ⌜v = v'⌝ }}.
Proof. iIntros "!# _". by iApply wp_value'. Qed.

Lemma ht_vs p E P P' Φ Φ' e :
  (P ={E}=> P') ∧ {{ P' }} e @ p; E {{ Φ' }} ∧ (∀ v, Φ' v ={E}=> Φ v)
  ⊢ {{ P }} e @ p; E {{ Φ }}.
Proof.
  iIntros "(#Hvs & #Hwp & #HΦ) !# HP". iMod ("Hvs" with "HP") as "HP".
  iApply wp_fupd. iApply (wp_wand with "[HP]"); [by iApply "Hwp"|].
  iIntros (v) "Hv". by iApply "HΦ".
Qed.

Lemma ht_atomic' p E1 E2 P P' Φ Φ' e :
  StronglyAtomic e ∨ p = progress ∧ Atomic e →
  (P ={E1,E2}=> P') ∧ {{ P' }} e @ p; E2 {{ Φ' }} ∧ (∀ v, Φ' v ={E2,E1}=> Φ v)
  ⊢ {{ P }} e @ p; E1 {{ Φ }}.
Proof.
  iIntros (?) "(#Hvs & #Hwp & #HΦ) !# HP". iApply (wp_atomic' _ _ E2); auto.
  iMod ("Hvs" with "HP") as "HP". iModIntro.
  iApply (wp_wand with "[HP]"); [by iApply "Hwp"|].
  iIntros (v) "Hv". by iApply "HΦ".
Qed.

Lemma ht_strong_atomic p E1 E2 P P' Φ Φ' e :
  StronglyAtomic e →
  (P ={E1,E2}=> P') ∧ {{ P' }} e @ p; E2 {{ Φ' }} ∧ (∀ v, Φ' v ={E2,E1}=> Φ v)
  ⊢ {{ P }} e @ p; E1 {{ Φ }}.
Proof. by eauto using ht_atomic'. Qed.

Lemma ht_atomic E1 E2 P P' Φ Φ' e :
  Atomic e →
  (P ={E1,E2}=> P') ∧ {{ P' }} e @ E2 {{ Φ' }} ∧ (∀ v, Φ' v ={E2,E1}=> Φ v)
  ⊢ {{ P }} e @ E1 {{ Φ }}.
Proof. by eauto using ht_atomic'. Qed.

Lemma ht_bind `{LanguageCtx Λ K} p E P Φ Φ' e :
  {{ P }} e @ p; E {{ Φ }} ∧ (∀ v, {{ Φ v }} K (of_val v) @ p; E {{ Φ' }})
  ⊢ {{ P }} K e @ p; E {{ Φ' }}.
Proof.
  iIntros "[#Hwpe #HwpK] !# HP". iApply wp_bind.
  iApply (wp_wand with "[HP]"); [by iApply "Hwpe"|].
  iIntros (v) "Hv". by iApply "HwpK".
Qed.

Lemma ht_forget_progress p E P Φ e :
  {{ P }} e @ p; E {{ Φ }} ⊢ {{ P }} e @ E ?{{ Φ }}.
Proof.
  by iIntros "#Hwp !# ?"; iApply wp_forget_progress; iApply "Hwp".
Qed.

Lemma ht_mask_weaken p E1 E2 P Φ e :
  E1 ⊆ E2 → {{ P }} e @ p; E1 {{ Φ }} ⊢ {{ P }} e @ p; E2 {{ Φ }}.
Proof.
  iIntros (?) "#Hwp !# HP". iApply (wp_mask_mono _ E1 E2); try done.
  by iApply "Hwp".
Qed.

Lemma ht_frame_l p E P Φ R e :
  {{ P }} e @ p; E {{ Φ }} ⊢ {{ R ∗ P }} e @ p; E {{ v, R ∗ Φ v }}.
Proof. iIntros "#Hwp !# [$ HP]". by iApply "Hwp". Qed.

Lemma ht_frame_r p E P Φ R e :
  {{ P }} e @ p; E {{ Φ }} ⊢ {{ P ∗ R }} e @ p; E {{ v, Φ v ∗ R }}.
Proof. iIntros "#Hwp !# [HP $]". by iApply "Hwp". Qed.

Lemma ht_frame_step_l p E1 E2 P R1 R2 e Φ :
  to_val e = None → E2 ⊆ E1 →
  (R1 ={E1,E2}=> ▷ |={E2,E1}=> R2) ∧ {{ P }} e @ p; E2 {{ Φ }}
  ⊢ {{ R1 ∗ P }} e @ p; E1 {{ λ v, R2 ∗ Φ v }}.
Proof.
  iIntros (??) "[#Hvs #Hwp] !# [HR HP]".
  iApply (wp_frame_step_l _ E1 E2); try done.
  iSplitL "HR"; [by iApply "Hvs"|by iApply "Hwp"].
Qed.

Lemma ht_frame_step_r p E1 E2 P R1 R2 e Φ :
  to_val e = None → E2 ⊆ E1 →
  (R1 ={E1,E2}=> ▷ |={E2,E1}=> R2) ∧ {{ P }} e @ p; E2 {{ Φ }}
  ⊢ {{ P ∗ R1 }} e @ p; E1 {{ λ v, Φ v ∗ R2 }}.
Proof.
  iIntros (??) "[#Hvs #Hwp] !# [HP HR]".
  iApply (wp_frame_step_r _ E1 E2); try done.
  iSplitR "HR"; [by iApply "Hwp"|by iApply "Hvs"].
Qed.

Lemma ht_frame_step_l' p E P R e Φ :
  to_val e = None →
  {{ P }} e @ p; E {{ Φ }} ⊢ {{ ▷ R ∗ P }} e @ p; E {{ v, R ∗ Φ v }}.
Proof.
  iIntros (?) "#Hwp !# [HR HP]".
  iApply wp_frame_step_l'; try done. iFrame "HR". by iApply "Hwp".
Qed.

Lemma ht_frame_step_r' p E P Φ R e :
  to_val e = None →
  {{ P }} e @ p; E {{ Φ }} ⊢ {{ P ∗ ▷ R }} e @ p; E {{ v, Φ v ∗ R }}.
Proof.
  iIntros (?) "#Hwp !# [HP HR]".
  iApply wp_frame_step_r'; try done. iFrame "HR". by iApply "Hwp".
Qed.
End hoare.
