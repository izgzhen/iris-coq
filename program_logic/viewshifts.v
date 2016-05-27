From iris.program_logic Require Import ownership.
From iris.program_logic Require Export pviewshifts invariants ghost_ownership.
From iris.proofmode Require Import pviewshifts invariants.
Import uPred.

Definition vs {Λ Σ} (E1 E2 : coPset) (P Q : iProp Λ Σ) : iProp Λ Σ :=
  (□ (P → |={E1,E2}=> Q))%I.
Arguments vs {_ _} _ _ _%I _%I.
Instance: Params (@vs) 4.
Notation "P ={ E1 , E2 }=> Q" := (vs E1 E2 P%I Q%I)
  (at level 99, E1,E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }=>  Q") : uPred_scope.
Notation "P ={ E1 , E2 }=> Q" := (True ⊢ (P ={E1,E2}=> Q)%I)
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }=>  Q") : C_scope.
Notation "P ={ E }=> Q" := (P ={E,E}=> Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }=>  Q") : uPred_scope.
Notation "P ={ E }=> Q" := (True ⊢ (P ={E}=> Q)%I)
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }=>  Q") : C_scope.

Notation "P <={ E1 , E2 }=> Q" := ((P ={E1,E2}=> Q) ∧ (Q ={E2,E1}=> P))%I
  (at level 99, E1,E2 at level 50, Q at level 200,
   format "P  <={ E1 , E2 }=>  Q") : uPred_scope.
Notation "P <={ E1 , E2 }=> Q" := (True ⊢ (P <={E1,E2}=> Q)%I)
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "P  <={ E1 , E2 }=>  Q") : C_scope.
Notation "P <={ E }=> Q" := (P <={E,E}=> Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  <={ E }=>  Q") : uPred_scope.
Notation "P <={ E }=> Q" := (True ⊢ (P <={E}=> Q)%I)
  (at level 99, E at level 50, Q at level 200,
   format "P  <={ E }=>  Q") : C_scope.

Section vs.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P Q R : iProp Λ Σ.
Implicit Types N : namespace.

Lemma vs_alt E1 E2 P Q : P ⊢ (|={E1,E2}=> Q) → P ={E1,E2}=> Q.
Proof. iIntros {Hvs} "! ?". by iApply Hvs. Qed.

Global Instance vs_ne E1 E2 n :
  Proper (dist n ==> dist n ==> dist n) (@vs Λ Σ E1 E2).
Proof. solve_proper. Qed.

Global Instance vs_proper E1 E2 : Proper ((≡) ==> (≡) ==> (≡)) (@vs Λ Σ E1 E2).
Proof. apply ne_proper_2, _. Qed.

Lemma vs_mono E1 E2 P P' Q Q' :
  P ⊢ P' → Q' ⊢ Q → (P' ={E1,E2}=> Q') ⊢ (P ={E1,E2}=> Q).
Proof. by intros HP HQ; rewrite /vs -HP HQ. Qed.

Global Instance vs_mono' E1 E2 :
  Proper (flip (⊢) ==> (⊢) ==> (⊢)) (@vs Λ Σ E1 E2).
Proof. solve_proper. Qed.

Lemma vs_false_elim E1 E2 P : False ={E1,E2}=> P.
Proof. iIntros "! []". Qed.
Lemma vs_timeless E P : TimelessP P → ▷ P ={E}=> P.
Proof. iIntros {?} "! HP". by iApply pvs_timeless. Qed.

Lemma vs_transitive E1 E2 E3 P Q R :
  E2 ⊆ E1 ∪ E3 → ((P ={E1,E2}=> Q) ∧ (Q ={E2,E3}=> R)) ⊢ (P ={E1,E3}=> R).
Proof.
  iIntros {?} "#[HvsP HvsQ] ! HP".
  iPvs ("HvsP" with "HP") as "HQ"; first done. by iApply "HvsQ".
Qed.

Lemma vs_transitive' E P Q R : ((P ={E}=> Q) ∧ (Q ={E}=> R)) ⊢ (P ={E}=> R).
Proof. apply vs_transitive; set_solver. Qed.
Lemma vs_reflexive E P : P ={E}=> P.
Proof. by iIntros "! HP". Qed.

Lemma vs_impl E P Q : □ (P → Q) ⊢ (P ={E}=> Q).
Proof. iIntros "#HPQ ! HP". by iApply "HPQ". Qed.

Lemma vs_frame_l E1 E2 P Q R : (P ={E1,E2}=> Q) ⊢ (R ★ P ={E1,E2}=> R ★ Q).
Proof. iIntros "#Hvs ! [$ HP]". by iApply "Hvs". Qed.

Lemma vs_frame_r E1 E2 P Q R : (P ={E1,E2}=> Q) ⊢ (P ★ R ={E1,E2}=> Q ★ R).
Proof. iIntros "#Hvs ! [HP $]". by iApply "Hvs". Qed.

Lemma vs_mask_frame E1 E2 Ef P Q :
  Ef ⊥ E1 ∪ E2 → (P ={E1,E2}=> Q) ⊢ (P ={E1 ∪ Ef,E2 ∪ Ef}=> Q).
Proof.
  iIntros {?} "#Hvs ! HP". iApply pvs_mask_frame; auto. by iApply "Hvs".
Qed.

Lemma vs_mask_frame' E Ef P Q : Ef ⊥ E → (P ={E}=> Q) ⊢ (P ={E ∪ Ef}=> Q).
Proof. intros; apply vs_mask_frame; set_solver. Qed.

Lemma vs_inv N E P Q R :
  nclose N ⊆ E → (inv N R ★ (▷ R ★ P ={E ∖ nclose N}=> ▷ R ★ Q)) ⊢ (P ={E}=> Q).
Proof.
  iIntros {?} "#[? Hvs] ! HP". iInv N as "HR". iApply "Hvs". by iSplitL "HR".
Qed.

Lemma vs_alloc N P : ▷ P ={N}=> inv N P.
Proof. iIntros "! HP". by iApply inv_alloc. Qed.
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
End vs_ghost.

Lemma vs_own_empty `{inG Λ Σ (A:ucmraT)} E γ : True ={E}=> own γ ∅.
Proof. by intros; eapply vs_alt, own_empty. Qed.
