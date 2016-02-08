Require Export program_logic.pviewshifts.
Require Import program_logic.ownership.

(* TODO: State lemmas in terms of inv and own. *)

Definition vs {Λ Σ} (E1 E2 : coPset) (P Q : iProp Λ Σ) : iProp Λ Σ :=
  (□ (P → pvs E1 E2 Q))%I.
Arguments vs {_ _} _ _ _%I _%I.
Instance: Params (@vs) 4.
Notation "P >{ E1 , E2 }> Q" := (vs E1 E2 P%I Q%I)
  (at level 69, E1 at level 1, format "P  >{ E1 , E2 }>  Q") : uPred_scope.
Notation "P >{ E1 , E2 }> Q" := (True ⊑ vs E1 E2 P%I Q%I)
  (at level 69, E1 at level 1, format "P  >{ E1 , E2 }>  Q") : C_scope.
Notation "P >{ E }> Q" := (vs E E P%I Q%I)
  (at level 69, E at level 1, format "P  >{ E }>  Q") : uPred_scope.
Notation "P >{ E }> Q" := (True ⊑ vs E E P%I Q%I)
  (at level 69, E at level 1, format "P  >{ E }>  Q") : C_scope.

Section vs.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types P Q : iProp Λ Σ.
Implicit Types m : iGst Λ Σ.
Import uPred.

Lemma vs_alt E1 E2 P Q : (P ⊑ pvs E1 E2 Q) → P >{E1,E2}> Q.
Proof.
  intros; rewrite -{1}always_const; apply always_intro, impl_intro_l.
  by rewrite always_const (right_id _ _).
Qed.

Global Instance vs_ne E1 E2 n :
  Proper (dist n ==> dist n ==> dist n) (@vs Λ Σ E1 E2).
Proof. by intros P P' HP Q Q' HQ; rewrite /vs HP HQ. Qed.

Global Instance vs_proper E1 E2 : Proper ((≡) ==> (≡) ==> (≡)) (@vs Λ Σ E1 E2).
Proof. apply ne_proper_2, _. Qed.

Lemma vs_mono E1 E2 P P' Q Q' :
  P ⊑ P' → Q' ⊑ Q → P' >{E1,E2}> Q' ⊑ P >{E1,E2}> Q.
Proof. by intros HP HQ; rewrite /vs -HP HQ. Qed.

Global Instance vs_mono' E1 E2 :
  Proper (flip (⊑) ==> (⊑) ==> (⊑)) (@vs Λ Σ E1 E2).
Proof. by intros until 2; apply vs_mono. Qed.

Lemma vs_false_elim E1 E2 P : False >{E1,E2}> P.
Proof. apply vs_alt, False_elim. Qed.
Lemma vs_timeless E P : TimelessP P → ▷ P >{E}> P.
Proof. by intros ?; apply vs_alt, pvs_timeless. Qed.

Lemma vs_transitive E1 E2 E3 P Q R :
  E2 ⊆ E1 ∪ E3 → (P >{E1,E2}> Q ∧ Q >{E2,E3}> R) ⊑ P >{E1,E3}> R.
Proof.
  intros; rewrite -always_and; apply always_intro, impl_intro_l.
  rewrite always_and (associative _) (always_elim (P → _)) impl_elim_r.
  by rewrite pvs_impl_r; apply pvs_trans.
Qed.

Lemma vs_transitive' E P Q R : (P >{E}> Q ∧ Q >{E}> R) ⊑ P >{E}> R.
Proof. apply vs_transitive; solve_elem_of. Qed.
Lemma vs_reflexive E P : P >{E}> P.
Proof. apply vs_alt, pvs_intro. Qed.

Lemma vs_impl E P Q : □ (P → Q) ⊑ P >{E}> Q.
Proof.
  apply always_intro, impl_intro_l.
  by rewrite always_elim impl_elim_r -pvs_intro.
Qed.

Lemma vs_frame_l E1 E2 P Q R : P >{E1,E2}> Q ⊑ (R ★ P) >{E1,E2}> (R ★ Q).
Proof.
  apply always_intro, impl_intro_l.
  rewrite -pvs_frame_l always_and_sep_r -always_wand_impl -(associative _).
  by rewrite always_elim wand_elim_r.
Qed.

Lemma vs_frame_r E1 E2 P Q R : P >{E1,E2}> Q ⊑ (P ★ R) >{E1,E2}> (Q ★ R).
Proof. rewrite !(commutative _ _ R); apply vs_frame_l. Qed.

Lemma vs_mask_frame E1 E2 Ef P Q :
  Ef ∩ (E1 ∪ E2) = ∅ → P >{E1,E2}> Q ⊑ P >{E1 ∪ Ef,E2 ∪ Ef}> Q.
Proof.
  intros ?; apply always_intro, impl_intro_l; rewrite (pvs_mask_frame _ _ Ef)//.
  by rewrite always_elim impl_elim_r.
Qed.

Lemma vs_mask_frame' E Ef P Q : Ef ∩ E = ∅ → P >{E}> Q ⊑ P >{E ∪ Ef}> Q.
Proof. intros; apply vs_mask_frame; solve_elem_of. Qed.
Lemma vs_open i P : ownI i P >{{[i]},∅}> ▷ P.
Proof. intros; apply vs_alt, pvs_open. Qed.

Lemma vs_open' E i P : i ∉ E → ownI i P >{{[i]} ∪ E,E}> ▷ P.
Proof.
  intros; rewrite -{2}(left_id_L ∅ (∪) E) -vs_mask_frame; last solve_elem_of.
  apply vs_open.
Qed.

Lemma vs_close i P : (ownI i P ∧ ▷ P) >{∅,{[i]}}> True.
Proof. intros; apply vs_alt, pvs_close. Qed.

Lemma vs_close' E i P : i ∉ E → (ownI i P ∧ ▷ P) >{E,{[i]} ∪ E}> True.
Proof.
  intros; rewrite -{1}(left_id_L ∅ (∪) E) -vs_mask_frame; last solve_elem_of.
  apply vs_close.
Qed.

Lemma vs_ownG_updateP E m (P : iGst Λ Σ → Prop) :
  m ~~>: P → ownG m >{E}> (∃ m', ■ P m' ∧ ownG m').
Proof. by intros; apply vs_alt, pvs_ownG_updateP. Qed.

Lemma vs_ownG_updateP_empty `{Empty (iGst Λ Σ), !CMRAIdentity (iGst Λ Σ)}
    E (P : iGst Λ Σ → Prop) :
  ∅ ~~>: P → True >{E}> (∃ m', ■ P m' ∧ ownG m').
Proof. by intros; apply vs_alt, pvs_ownG_updateP_empty. Qed.

Lemma vs_update E m m' : m ~~> m' → ownG m >{E}> ownG m'.
Proof. by intros; apply vs_alt, pvs_ownG_update. Qed.
Lemma vs_alloc E P : ¬set_finite E → ▷ P >{E}> (∃ i, ■ (i ∈ E) ∧ ownI i P).
Proof. by intros; apply vs_alt, pvs_alloc. Qed.

End vs.
