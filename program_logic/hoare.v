From program_logic Require Export weakestpre viewshifts.

Definition ht {Λ Σ} (E : coPset) (P : iProp Λ Σ)
    (e : expr Λ) (Φ : val Λ → iProp Λ Σ) : iProp Λ Σ :=
  (□ (P → || e @ E {{ Φ }}))%I.
Instance: Params (@ht) 3.

Notation "{{ P } } e @ E {{ Φ } }" := (ht E P e Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  @  E  {{  Φ  } }") : uPred_scope.
Notation "{{ P } } e {{ Φ } }" := (ht ⊤ P e Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  {{  Φ  } }") : uPred_scope.
Notation "{{ P } } e @ E {{ Φ } }" := (True ⊑ ht E P e Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  @  E  {{  Φ  } }") : C_scope.
Notation "{{ P } } e {{ Φ } }" := (True ⊑ ht ⊤ P e Φ)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  {{  Φ  } }") : C_scope.

Section hoare.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P Q : iProp Λ Σ.
Implicit Types Φ Ψ : val Λ → iProp Λ Σ.
Implicit Types v : val Λ.
Import uPred.

Global Instance ht_ne E n :
  Proper (dist n ==> eq==>pointwise_relation _ (dist n) ==> dist n) (@ht Λ Σ E).
Proof. by intros P P' HP e ? <- Φ Φ' HΦ; rewrite /ht HP; setoid_rewrite HΦ. Qed.
Global Instance ht_proper E :
  Proper ((≡) ==> eq ==> pointwise_relation _ (≡) ==> (≡)) (@ht Λ Σ E).
Proof. by intros P P' HP e ? <- Φ Φ' HΦ; rewrite /ht HP; setoid_rewrite HΦ. Qed.
Lemma ht_mono E P P' Φ Φ' e :
  P ⊑ P' → (∀ v, Φ' v ⊑ Φ v) → {{ P' }} e @ E {{ Φ' }} ⊑ {{ P }} e @ E {{ Φ }}.
Proof. by intros; apply always_mono, impl_mono, wp_mono. Qed.
Global Instance ht_mono' E :
  Proper (flip (⊑) ==> eq ==> pointwise_relation _ (⊑) ==> (⊑)) (@ht Λ Σ E).
Proof. by intros P P' HP e ? <- Φ Φ' HΦ; apply ht_mono. Qed.

Lemma ht_alt E P Φ e : (P ⊑ || e @ E {{ Φ }}) → {{ P }} e @ E {{ Φ }}.
Proof.
  intros; rewrite -{1}always_const. apply: always_intro. apply impl_intro_l.
  by rewrite always_const right_id.
Qed.

Lemma ht_val E v :
  {{ True : iProp Λ Σ }} of_val v @ E {{ λ v', v = v' }}.
Proof. apply ht_alt. by rewrite -wp_value'; apply const_intro. Qed.

Lemma ht_vs E P P' Φ Φ' e :
  ((P ={E}=> P') ∧ {{ P' }} e @ E {{ Φ' }} ∧ ∀ v, Φ' v ={E}=> Φ v)
  ⊑ {{ P }} e @ E {{ Φ }}.
Proof.
  apply: always_intro. apply impl_intro_l.
  rewrite (assoc _ P) {1}/vs always_elim impl_elim_r.
  rewrite assoc pvs_impl_r pvs_always_r wp_always_r.
  rewrite -(pvs_wp E e Φ) -(wp_pvs E e Φ); apply pvs_mono, wp_mono=> v.
  by rewrite (forall_elim v) {1}/vs always_elim impl_elim_r.
Qed.

Lemma ht_atomic E1 E2 P P' Φ Φ' e :
  E2 ⊆ E1 → atomic e →
  ((P ={E1,E2}=> P') ∧ {{ P' }} e @ E2 {{ Φ' }} ∧ ∀ v, Φ' v ={E2,E1}=> Φ v)
  ⊑ {{ P }} e @ E1 {{ Φ }}.
Proof.
  intros ??; apply: always_intro. apply impl_intro_l.
  rewrite (assoc _ P) {1}/vs always_elim impl_elim_r.
  rewrite assoc pvs_impl_r pvs_always_r wp_always_r.
  rewrite -(wp_atomic E1 E2) //; apply pvs_mono, wp_mono=> v.
  by rewrite (forall_elim v) {1}/vs always_elim impl_elim_r.
Qed.

Lemma ht_bind `{LanguageCtx Λ K} E P Φ Φ' e :
  ({{ P }} e @ E {{ Φ }} ∧ ∀ v, {{ Φ v }} K (of_val v) @ E {{ Φ' }})
  ⊑ {{ P }} K e @ E {{ Φ' }}.
Proof.
  intros; apply: always_intro. apply impl_intro_l.
  rewrite (assoc _ P) {1}/ht always_elim impl_elim_r.
  rewrite wp_always_r -wp_bind //; apply wp_mono=> v.
  by rewrite (forall_elim v) /ht always_elim impl_elim_r.
Qed.

Lemma ht_mask_weaken E1 E2 P Φ e :
  E1 ⊆ E2 → {{ P }} e @ E1 {{ Φ }} ⊑ {{ P }} e @ E2 {{ Φ }}.
Proof. intros. by apply always_mono, impl_mono, wp_mask_frame_mono. Qed.

Lemma ht_frame_l E P Φ R e :
  {{ P }} e @ E {{ Φ }} ⊑ {{ R ★ P }} e @ E {{ λ v, R ★ Φ v }}.
Proof.
  apply always_intro', impl_intro_l.
  rewrite always_and_sep_r -assoc (sep_and P) always_elim impl_elim_r.
  by rewrite wp_frame_l.
Qed.

Lemma ht_frame_r E P Φ R e :
  {{ P }} e @ E {{ Φ }} ⊑ {{ P ★ R }} e @ E {{ λ v, Φ v ★ R }}.
Proof. setoid_rewrite (comm _ _ R); apply ht_frame_l. Qed.

Lemma ht_frame_later_l E P R e Φ :
  to_val e = None →
  {{ P }} e @ E {{ Φ }} ⊑ {{ ▷ R ★ P }} e @ E {{ λ v, R ★ Φ v }}.
Proof.
  intros; apply always_intro', impl_intro_l.
  rewrite always_and_sep_r -assoc (sep_and P) always_elim impl_elim_r.
  by rewrite wp_frame_later_l //; apply wp_mono=>v; rewrite pvs_frame_l.
Qed.

Lemma ht_frame_later_r E P Φ R e :
  to_val e = None →
  {{ P }} e @ E {{ Φ }} ⊑ {{ P ★ ▷ R }} e @ E {{ λ v, Φ v ★ R }}.
Proof.
  rewrite (comm _ _ (▷ R)%I); setoid_rewrite (comm _ _ R).
  apply ht_frame_later_l.
Qed.
End hoare.
