Require Export iris.weakestpre iris.viewshifts.

Definition ht {Σ} (E : coPset) (P : iProp Σ)
    (e : iexpr Σ) (Q : ival Σ → iProp Σ) : iProp Σ :=
  (□ (P → wp E e (λ v, pvs E E (Q v))))%I.
Instance: Params (@ht) 2.

Notation "{{ P } } e @ E {{ Q } }" := (ht E P e Q)
  (at level 74, format "{{  P  } }  e  @  E  {{  Q  } }") : uPred_scope.
Notation "{{ P } } e @ E {{ Q } }" := (True ⊑ ht E P e Q)
  (at level 74, format "{{  P  } }  e  @  E  {{  Q  } }") : C_scope.

Section hoare.
Context {Σ : iParam}.
Implicit Types P : iProp Σ.
Implicit Types Q : ival Σ → iProp Σ.
Implicit Types v : ival Σ.
Import uPred.

Global Instance ht_ne E n :
  Proper (dist n ==> eq ==> pointwise_relation _ (dist n) ==> dist n) (@ht Σ E).
Proof. by intros P P' HP e ? <- Q Q' HQ; rewrite /ht HP; setoid_rewrite HQ. Qed.
Global Instance ht_proper E :
  Proper ((≡) ==> eq ==> pointwise_relation _ (≡) ==> (≡)) (@ht Σ E).
Proof. by intros P P' HP e ? <- Q Q' HQ; rewrite /ht HP; setoid_rewrite HQ. Qed.
Lemma ht_mono E P P' Q Q' e :
  P ⊑ P' → (∀ v, Q' v ⊑ Q v) → {{ P' }} e @ E {{ Q' }} ⊑ {{ P }} e @ E {{ Q }}.
Proof. by intros HP HQ; rewrite /ht -HP; setoid_rewrite HQ. Qed.
Global Instance ht_mono' E :
  Proper (flip (⊑) ==> eq ==> pointwise_relation _ (⊑) ==> (⊑)) (@ht Σ E).
Proof. by intros P P' HP e ? <- Q Q' HQ; apply ht_mono. Qed.

Lemma ht_val E v :
  {{ True }} of_val v @ E {{ λ v', ■ (v = v') }}.
Proof.
  apply (always_intro' _ _), impl_intro_l.
  by rewrite -wp_value -pvs_intro; apply const_intro.
Qed.
Lemma ht_vs E P P' Q Q' e :
  (P >{E}> P' ∧ {{ P' }} e @ E {{ Q' }} ∧ ∀ v, Q' v >{E}> Q v)
  ⊑ {{ P }} e @ E {{ Q }}.
Proof.
  apply (always_intro' _ _), impl_intro_l.
  rewrite (associative _ P) {1}/vs always_elim impl_elim_r.
  rewrite (associative _) pvs_impl_r pvs_always_r wp_always_r.
  rewrite wp_pvs; apply wp_mono=> v.
  by rewrite (forall_elim v) pvs_impl_r !pvs_trans'.
Qed.
Lemma ht_atomic E1 E2 P P' Q Q' e :
  E2 ⊆ E1 → atomic e →
  (P >{E1,E2}> P' ∧ {{ P' }} e @ E2 {{ Q' }} ∧ ∀ v, Q' v >{E2,E1}> Q v)
  ⊑ {{ P }} e @ E1 {{ Q }}.
Proof.
  intros ??; apply (always_intro' _ _), impl_intro_l.
  rewrite (associative _ P) {1}/vs always_elim impl_elim_r.
  rewrite (associative _) pvs_impl_r pvs_always_r wp_always_r.
  rewrite -(wp_atomic E1 E2) //; apply pvs_mono, wp_mono=> v.
  rewrite (forall_elim v) pvs_impl_r -(pvs_intro E1) pvs_trans; solve_elem_of.
Qed.
Lemma ht_bind `(HK : is_ctx K) E P Q Q' e :
  ({{ P }} e @ E {{ Q }} ∧ ∀ v, {{ Q v }} K (of_val v) @ E {{ Q' }})
  ⊑ {{ P }} K e @ E {{ Q' }}.
Proof.
  intros; apply (always_intro' _ _), impl_intro_l.
  rewrite (associative _ P) {1}/ht always_elim impl_elim_r.
  rewrite wp_always_r -wp_bind //; apply wp_mono=> v.
  rewrite (forall_elim v) pvs_impl_r wp_pvs; apply wp_mono=> v'.
  by rewrite pvs_trans'.
Qed.
Lemma ht_mask_weaken E1 E2 P Q e :
  E1 ⊆ E2 → {{ P }} e @ E1 {{ Q }} ⊑ {{ P }} e @ E2 {{ Q }}.
Proof.
  intros; apply always_mono, impl_intro_l; rewrite impl_elim_r.
  by rewrite -(wp_mask_weaken E1) //; apply wp_mono=> v; apply pvs_mask_weaken.
Qed.
Lemma ht_frame_l E P Q R e :
  {{ P }} e @ E {{ Q }} ⊑ {{ R ★ P }} e @ E {{ λ v, R ★ Q v }}.
Proof.
  apply always_intro, impl_intro_l.
  rewrite always_and_sep_r -(associative _) (sep_and P) always_elim impl_elim_r.
  by rewrite wp_frame_l; apply wp_mono=>v; rewrite pvs_frame_l.
Qed.
Lemma ht_frame_r E P Q R e :
  {{ P }} e @ E {{ Q }} ⊑ {{ P ★ R }} e @ E {{ λ v, Q v ★ R }}.
Proof. setoid_rewrite (commutative _ _ R); apply ht_frame_l. Qed.
Lemma ht_frame_later_l E P R e Q :
  to_val e = None →
  {{ P }} e @ E {{ Q }} ⊑ {{ ▷ R ★ P }} e @ E {{ λ v, R ★ Q v }}.
Proof.
  intros; apply always_intro, impl_intro_l.
  rewrite always_and_sep_r -(associative _) (sep_and P) always_elim impl_elim_r.
  by rewrite wp_frame_later_l //; apply wp_mono=>v; rewrite pvs_frame_l.
Qed.
Lemma ht_frame_later_r E P R e Q :
  to_val e = None →
  {{ P }} e @ E {{ Q }} ⊑ {{ P ★ ▷ R }} e @ E {{ λ v, Q v ★ R }}.
Proof.
  rewrite (commutative _ _ (▷ R)%I); setoid_rewrite (commutative _ _ R).
  apply ht_frame_later_l.
Qed.
End hoare.