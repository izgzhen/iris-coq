From program_logic Require Import ownership.
From program_logic Require Export pviewshifts invariants ghost_ownership.
Import uPred.

Definition vs {Λ Σ} (E1 E2 : coPset) (P Q : iProp Λ Σ) : iProp Λ Σ :=
  (□ (P → |={E1,E2}=> Q))%I.
Arguments vs {_ _} _ _ _%I _%I.
Instance: Params (@vs) 4.
Notation "P ={ E1 , E2 }=> Q" := (vs E1 E2 P%I Q%I)
  (at level 199, E1,E2 at level 50,
   format "P  ={ E1 , E2 }=>  Q") : uPred_scope.
Notation "P ={ E1 , E2 }=> Q" := (True ⊑ vs E1 E2 P%I Q%I)
  (at level 199, E1, E2 at level 50,
   format "P  ={ E1 , E2 }=>  Q") : C_scope.
Notation "P ={ E }=> Q" := (vs E E P%I Q%I)
  (at level 199, E at level 50, format "P  ={ E }=>  Q") : uPred_scope.
Notation "P ={ E }=> Q" := (True ⊑ vs E E P%I Q%I)
  (at level 199, E at level 50, format "P  ={ E }=>  Q") : C_scope.

Section vs.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P Q R : iProp Λ Σ.
Implicit Types N : namespace.

Lemma vs_alt E1 E2 P Q : P ⊑ (|={E1,E2}=> Q) → P ={E1,E2}=> Q.
Proof.
  intros; rewrite -{1}always_const. apply: always_intro. apply impl_intro_l.
  by rewrite always_const right_id.
Qed.

Global Instance vs_ne E1 E2 n :
  Proper (dist n ==> dist n ==> dist n) (@vs Λ Σ E1 E2).
Proof. solve_proper. Qed.

Global Instance vs_proper E1 E2 : Proper ((≡) ==> (≡) ==> (≡)) (@vs Λ Σ E1 E2).
Proof. apply ne_proper_2, _. Qed.

Lemma vs_mono E1 E2 P P' Q Q' :
  P ⊑ P' → Q' ⊑ Q → (P' ={E1,E2}=> Q') ⊑ (P ={E1,E2}=> Q).
Proof. by intros HP HQ; rewrite /vs -HP HQ. Qed.

Global Instance vs_mono' E1 E2 :
  Proper (flip (⊑) ==> (⊑) ==> (⊑)) (@vs Λ Σ E1 E2).
Proof. solve_proper. Qed.

Lemma vs_false_elim E1 E2 P : False ={E1,E2}=> P.
Proof. apply vs_alt, False_elim. Qed.
Lemma vs_timeless E P : TimelessP P → ▷ P ={E}=> P.
Proof. by intros ?; apply vs_alt, pvs_timeless. Qed.

Lemma vs_transitive E1 E2 E3 P Q R :
  E2 ⊆ E1 ∪ E3 → ((P ={E1,E2}=> Q) ∧ (Q ={E2,E3}=> R)) ⊑ (P ={E1,E3}=> R).
Proof.
  intros; rewrite -always_and; apply: always_intro. apply impl_intro_l.
  rewrite always_and assoc (always_elim (P → _)) impl_elim_r.
  by rewrite pvs_impl_r; apply pvs_trans.
Qed.

Lemma vs_transitive' E P Q R : ((P ={E}=> Q) ∧ (Q ={E}=> R)) ⊑ (P ={E}=> R).
Proof. apply vs_transitive; set_solver. Qed.
Lemma vs_reflexive E P : P ={E}=> P.
Proof. apply vs_alt, pvs_intro. Qed.

Lemma vs_impl E P Q : □ (P → Q) ⊑ (P ={E}=> Q).
Proof.
  apply always_intro', impl_intro_l.
  by rewrite always_elim impl_elim_r -pvs_intro.
Qed.

Lemma vs_frame_l E1 E2 P Q R : (P ={E1,E2}=> Q) ⊑ (R ★ P ={E1,E2}=> R ★ Q).
Proof.
  apply always_intro', impl_intro_l.
  rewrite -pvs_frame_l always_and_sep_r -always_wand_impl -assoc.
  by rewrite always_elim wand_elim_r.
Qed.

Lemma vs_frame_r E1 E2 P Q R : (P ={E1,E2}=> Q) ⊑ (P ★ R ={E1,E2}=> Q ★ R).
Proof. rewrite !(comm _ _ R); apply vs_frame_l. Qed.

Lemma vs_mask_frame E1 E2 Ef P Q :
  Ef ∩ (E1 ∪ E2) = ∅ → (P ={E1,E2}=> Q) ⊑ (P ={E1 ∪ Ef,E2 ∪ Ef}=> Q).
Proof.
  intros ?; apply always_intro', impl_intro_l; rewrite (pvs_mask_frame _ _ Ef)//.
  by rewrite always_elim impl_elim_r.
Qed.

Lemma vs_mask_frame' E Ef P Q : Ef ∩ E = ∅ → (P ={E}=> Q) ⊑ (P ={E ∪ Ef}=> Q).
Proof. intros; apply vs_mask_frame; set_solver. Qed.

Lemma vs_open_close N E P Q R :
  nclose N ⊆ E →
  (inv N R ★ (▷ R ★ P ={E ∖ nclose N}=> ▷ R ★ Q)) ⊑ (P ={E}=> Q).
Proof.
  intros; apply: always_intro. apply impl_intro_l.
  rewrite always_and_sep_r assoc [(P ★ _)%I]comm -assoc.
  eapply pvs_open_close; [by eauto with I..|].
  rewrite sep_elim_r. apply wand_intro_l.
  (* Oh wow, this is annyoing... *)
  rewrite assoc -always_and_sep_r'.
  by rewrite /vs always_elim impl_elim_r.
Qed.

Lemma vs_alloc N P : ▷ P ={N}=> inv N P.
Proof. by intros; apply vs_alt, inv_alloc. Qed.

End vs.

Section vs_ghost.
Context `{inG Λ Σ A}.
Implicit Types a : A.
Implicit Types P Q R : iPropG Λ Σ.

Lemma vs_own_updateP E γ a φ :
  a ~~>: φ → own γ a ={E}=> ∃ a', ■ φ a' ∧ own γ a'.
Proof. by intros; apply vs_alt, own_updateP. Qed.

Lemma vs_update E γ a a' : a ~~> a' → own γ a ={E}=> own γ a'.
Proof. by intros; apply vs_alt, own_update. Qed.

Lemma vs_own_empty `{Empty A, !CMRAUnit A} E γ :
  True ={E}=> own γ ∅.
Proof. by intros; eapply vs_alt, own_empty. Qed.

End vs_ghost.
