From iris.program_logic Require Export weakestpre viewshifts.
From iris.proofmode Require Import weakestpre invariants.

Definition ht {Λ Σ} (E : coPset) (P : iProp Λ Σ)
    (e : expr Λ) (Φ : val Λ → iProp Λ Σ) : iProp Λ Σ :=
  (□ (P → WP e @ E {{ Φ }}))%I.
Instance: Params (@ht) 3.

Notation "{{ P } } e @ E {{ Φ } }" := (ht E P e Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  @  E  {{  Φ  } }") : uPred_scope.
Notation "{{ P } } e {{ Φ } }" := (ht ⊤ P e Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  {{  Φ  } }") : uPred_scope.
Notation "{{ P } } e @ E {{ Φ } }" := (True ⊢ ht E P e Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  @  E  {{  Φ  } }") : C_scope.
Notation "{{ P } } e {{ Φ } }" := (True ⊢ ht ⊤ P e Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  {{  Φ  } }") : C_scope.

Notation "{{ P } } e @ E {{ v , Q } }" := (ht E P e (λ v, Q))
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  @  E  {{  v ,  Q  } }") : uPred_scope.
Notation "{{ P } } e {{ v , Q } }" := (ht ⊤ P e (λ v, Q))
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  {{  v ,  Q  } }") : uPred_scope.
Notation "{{ P } } e @ E {{ v , Q } }" := (True ⊢ ht E P e (λ v, Q))
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  @  E  {{  v ,  Q  } }") : C_scope.
Notation "{{ P } } e {{ v , Q } }" := (True ⊢ ht ⊤ P e (λ v, Q))
  (at level 20, P, e, Q at level 200,
   format "{{  P  } }  e  {{  v ,  Q  } }") : C_scope.

Section hoare.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P Q : iProp Λ Σ.
Implicit Types Φ Ψ : val Λ → iProp Λ Σ.
Implicit Types v : val Λ.
Import uPred.

Global Instance ht_ne E n :
  Proper (dist n ==> eq==>pointwise_relation _ (dist n) ==> dist n) (@ht Λ Σ E).
Proof. solve_proper. Qed.
Global Instance ht_proper E :
  Proper ((≡) ==> eq ==> pointwise_relation _ (≡) ==> (≡)) (@ht Λ Σ E).
Proof. solve_proper. Qed.
Lemma ht_mono E P P' Φ Φ' e :
  (P ⊢ P') → (∀ v, Φ' v ⊢ Φ v) → {{ P' }} e @ E {{ Φ' }} ⊢ {{ P }} e @ E {{ Φ }}.
Proof. by intros; apply always_mono, impl_mono, wp_mono. Qed.
Global Instance ht_mono' E :
  Proper (flip (⊢) ==> eq ==> pointwise_relation _ (⊢) ==> (⊢)) (@ht Λ Σ E).
Proof. solve_proper. Qed.

Lemma ht_alt E P Φ e : (P ⊢ WP e @ E {{ Φ }}) → {{ P }} e @ E {{ Φ }}.
Proof. iIntros {Hwp} "! HP". by iApply Hwp. Qed.

Lemma ht_val E v : {{ True : iProp Λ Σ }} of_val v @ E {{ v', v = v' }}.
Proof. iIntros "! _". by iApply wp_value'. Qed.

Lemma ht_vs E P P' Φ Φ' e :
  (P ={E}=> P') ∧ {{ P' }} e @ E {{ Φ' }} ∧ (∀ v, Φ' v ={E}=> Φ v)
  ⊢ {{ P }} e @ E {{ Φ }}.
Proof.
  iIntros "(#Hvs&#Hwp&#HΦ) ! HP". iPvs ("Hvs" with "HP") as "HP".
  iApply wp_pvs; iApply wp_wand_r; iSplitL; [by iApply "Hwp"|].
  iIntros {v} "Hv". by iApply "HΦ".
Qed.

Lemma ht_atomic E1 E2 P P' Φ Φ' e :
  E2 ⊆ E1 → atomic e →
  (P ={E1,E2}=> P') ∧ {{ P' }} e @ E2 {{ Φ' }} ∧ (∀ v, Φ' v ={E2,E1}=> Φ v)
  ⊢ {{ P }} e @ E1 {{ Φ }}.
Proof.
  iIntros {??} "(#Hvs&#Hwp&#HΦ) ! HP". iApply (wp_atomic _ E2); auto.
  iPvs ("Hvs" with "HP") as "HP"; first set_solver. iPvsIntro.
  iApply wp_wand_r; iSplitL; [by iApply "Hwp"|].
  iIntros {v} "Hv". by iApply "HΦ".
Qed.

Lemma ht_bind `{LanguageCtx Λ K} E P Φ Φ' e :
  {{ P }} e @ E {{ Φ }} ∧ (∀ v, {{ Φ v }} K (of_val v) @ E {{ Φ' }})
  ⊢ {{ P }} K e @ E {{ Φ' }}.
Proof.
  iIntros "(#Hwpe&#HwpK) ! HP". iApply wp_bind.
  iApply wp_wand_r; iSplitL; [by iApply "Hwpe"|].
  iIntros {v} "Hv". by iApply "HwpK".
Qed.

Lemma ht_mask_weaken E1 E2 P Φ e :
  E1 ⊆ E2 → {{ P }} e @ E1 {{ Φ }} ⊢ {{ P }} e @ E2 {{ Φ }}.
Proof.
  iIntros {?} "#Hwp ! HP". iApply (wp_mask_frame_mono E1 E2); try done.
  by iApply "Hwp".
Qed.

Lemma ht_frame_l E P Φ R e :
  {{ P }} e @ E {{ Φ }} ⊢ {{ R ★ P }} e @ E {{ v, R ★ Φ v }}.
Proof. iIntros "#Hwp ! [$ HP]". by iApply "Hwp". Qed.

Lemma ht_frame_r E P Φ R e :
  {{ P }} e @ E {{ Φ }} ⊢ {{ P ★ R }} e @ E {{ v, Φ v ★ R }}.
Proof. iIntros "#Hwp ! [HP $]". by iApply "Hwp". Qed.

Lemma ht_frame_step_l E E1 E2 P R1 R2 R3 e Φ :
  to_val e = None → E ⊥ E1 → E2 ⊆ E1 →
  (R1 ={E1,E2}=> ▷ R2) ∧ (R2 ={E2,E1}=> R3) ∧ {{ P }} e @ E {{ Φ }}
  ⊢ {{ R1 ★ P }} e @ E ∪ E1 {{ λ v, R3 ★ Φ v }}.
Proof.
  iIntros {???} "[#Hvs1 [#Hvs2 #Hwp]] ! [HR HP]".
  iApply (wp_frame_step_l E E1 E2); try done.
  iSplitL "HR"; [|by iApply "Hwp"].
  iPvs ("Hvs1" with "HR"); first by set_solver.
  iPvsIntro. iNext. by iApply "Hvs2".
Qed.

Lemma ht_frame_step_r E E1 E2 P R1 R2 R3 e Φ :
  to_val e = None → E ⊥ E1 → E2 ⊆ E1 →
  (R1 ={E1,E2}=> ▷ R2) ∧ (R2 ={E2,E1}=> R3) ∧ {{ P }} e @ E {{ Φ }}
  ⊢ {{ P ★ R1 }} e @ (E ∪ E1) {{ λ v, Φ v ★ R3 }}.
Proof.
  iIntros {???} "[#Hvs1 [#Hvs2 #Hwp]]".
  setoid_rewrite (comm _ _ R3); rewrite (comm _ _ R1).
  iApply (ht_frame_step_l _ _ E2); by repeat iSplit.
Qed.

Lemma ht_frame_step_l' E P R e Φ :
  to_val e = None →
  {{ P }} e @ E {{ Φ }} ⊢ {{ ▷ R ★ P }} e @ E {{ v, R ★ Φ v }}.
Proof.
  iIntros {?} "#Hwp ! [HR HP]".
  iApply wp_frame_step_l'; try done. iFrame "HR". by iApply "Hwp".
Qed.

Lemma ht_frame_step_r' E P Φ R e :
  to_val e = None →
  {{ P }} e @ E {{ Φ }} ⊢ {{ P ★ ▷ R }} e @ E {{ v, Φ v ★ R }}.
Proof.
  iIntros {?} "#Hwp ! [HP HR]".
  iApply wp_frame_step_r'; try done. iFrame "HR". by iApply "Hwp".
Qed.

Lemma ht_inv N E P Φ R e :
  atomic e → nclose N ⊆ E →
  inv N R ★ {{ ▷ R ★ P }} e @ E ∖ nclose N {{ v, ▷ R ★ Φ v }}
  ⊢ {{ P }} e @ E {{ Φ }}.
Proof.
  iIntros {??} "[#? #Hwp] ! HP". iInv N as "HR". iApply "Hwp". by iSplitL "HR".
Qed.
End hoare.
