Require Export program_logic.weakestpre program_logic.viewshifts.

Definition ht {Λ Σ} (E : coPset) (P : iProp Λ Σ)
    (e : expr Λ) (Q : val Λ → iProp Λ Σ) : iProp Λ Σ := (□ (P → wp E e Q))%I.
Instance: Params (@ht) 3.

Notation "{{ P } } e @ E {{ Q } }" := (ht E P e Q)
  (at level 74, format "{{  P  } }  e  @  E  {{  Q  } }") : uPred_scope.
Notation "{{ P } } e @ E {{ Q } }" := (True ⊑ ht E P e Q)
  (at level 74, format "{{  P  } }  e  @  E  {{  Q  } }") : C_scope.

Section hoare.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P : iProp Λ Σ.
Implicit Types Q : val Λ → iProp Λ Σ.
Implicit Types v : val Λ.
Import uPred.

Global Instance ht_ne E n :
  Proper (dist n ==> eq==>pointwise_relation _ (dist n) ==> dist n) (@ht Λ Σ E).
Proof. by intros P P' HP e ? <- Q Q' HQ; rewrite /ht HP; setoid_rewrite HQ. Qed.
Global Instance ht_proper E :
  Proper ((≡) ==> eq ==> pointwise_relation _ (≡) ==> (≡)) (@ht Λ Σ E).
Proof. by intros P P' HP e ? <- Q Q' HQ; rewrite /ht HP; setoid_rewrite HQ. Qed.
Lemma ht_mono E P P' Q Q' e :
  P ⊑ P' → (∀ v, Q' v ⊑ Q v) → {{ P' }} e @ E {{ Q' }} ⊑ {{ P }} e @ E {{ Q }}.
Proof. by intros; apply always_mono, impl_mono, wp_mono. Qed.
Global Instance ht_mono' E :
  Proper (flip (⊑) ==> eq ==> pointwise_relation _ (⊑) ==> (⊑)) (@ht Λ Σ E).
Proof. by intros P P' HP e ? <- Q Q' HQ; apply ht_mono. Qed.

Lemma ht_val E v :
  {{ True : iProp Λ Σ }} of_val v @ E {{ λ v', v = v' }}.
Proof.
  apply (always_intro' _ _), impl_intro_l.
  by rewrite -wp_value; apply const_intro.
Qed.
Lemma ht_vs E P P' Q Q' e :
  ((P ={E}=> P') ∧ {{ P' }} e @ E {{ Q' }} ∧ ∀ v, Q' v ={E}=> Q v)
  ⊑ {{ P }} e @ E {{ Q }}.
Proof.
  apply (always_intro' _ _), impl_intro_l.
  rewrite (assoc _ P) {1}/vs always_elim impl_elim_r.
  rewrite assoc pvs_impl_r pvs_always_r wp_always_r.
  rewrite -(pvs_wp E e Q) -(wp_pvs E e Q); apply pvs_mono, wp_mono=> v.
  by rewrite (forall_elim v) {1}/vs always_elim impl_elim_r.
Qed.
Lemma ht_atomic E1 E2 P P' Q Q' e :
  E2 ⊆ E1 → atomic e →
  ((P ={E1,E2}=> P') ∧ {{ P' }} e @ E2 {{ Q' }} ∧ ∀ v, Q' v ={E2,E1}=> Q v)
  ⊑ {{ P }} e @ E1 {{ Q }}.
Proof.
  intros ??; apply (always_intro' _ _), impl_intro_l.
  rewrite (assoc _ P) {1}/vs always_elim impl_elim_r.
  rewrite assoc pvs_impl_r pvs_always_r wp_always_r.
  rewrite -(wp_atomic E1 E2) //; apply pvs_mono, wp_mono=> v.
  by rewrite (forall_elim v) {1}/vs always_elim impl_elim_r.
Qed.
Lemma ht_bind `{LanguageCtx Λ K} E P Q Q' e :
  ({{ P }} e @ E {{ Q }} ∧ ∀ v, {{ Q v }} K (of_val v) @ E {{ Q' }})
  ⊑ {{ P }} K e @ E {{ Q' }}.
Proof.
  intros; apply (always_intro' _ _), impl_intro_l.
  rewrite (assoc _ P) {1}/ht always_elim impl_elim_r.
  rewrite wp_always_r -wp_bind //; apply wp_mono=> v.
  by rewrite (forall_elim v) /ht always_elim impl_elim_r.
Qed.
Lemma ht_mask_weaken E1 E2 P Q e :
  E1 ⊆ E2 → {{ P }} e @ E1 {{ Q }} ⊑ {{ P }} e @ E2 {{ Q }}.
Proof. intros. by apply always_mono, impl_mono, wp_mask_frame_mono. Qed.
Lemma ht_frame_l E P Q R e :
  {{ P }} e @ E {{ Q }} ⊑ {{ R ★ P }} e @ E {{ λ v, R ★ Q v }}.
Proof.
  apply always_intro, impl_intro_l.
  rewrite always_and_sep_r -assoc (sep_and P) always_elim impl_elim_r.
  by rewrite wp_frame_l.
Qed.
Lemma ht_frame_r E P Q R e :
  {{ P }} e @ E {{ Q }} ⊑ {{ P ★ R }} e @ E {{ λ v, Q v ★ R }}.
Proof. setoid_rewrite (comm _ _ R); apply ht_frame_l. Qed.
Lemma ht_frame_later_l E P R e Q :
  to_val e = None →
  {{ P }} e @ E {{ Q }} ⊑ {{ ▷ R ★ P }} e @ E {{ λ v, R ★ Q v }}.
Proof.
  intros; apply always_intro, impl_intro_l.
  rewrite always_and_sep_r -assoc (sep_and P) always_elim impl_elim_r.
  by rewrite wp_frame_later_l //; apply wp_mono=>v; rewrite pvs_frame_l.
Qed.
Lemma ht_frame_later_r E P R e Q :
  to_val e = None →
  {{ P }} e @ E {{ Q }} ⊑ {{ P ★ ▷ R }} e @ E {{ λ v, Q v ★ R }}.
Proof.
  rewrite (comm _ _ (▷ R)%I); setoid_rewrite (comm _ _ R).
  apply ht_frame_later_l.
Qed.
End hoare.
