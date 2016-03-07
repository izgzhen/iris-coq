From algebra Require Export base.
From program_logic Require Import ownership.
From program_logic Require Export namespaces pviewshifts weakestpre.
Import uPred.
Local Hint Extern 100 (@eq coPset _ _) => set_solver.
Local Hint Extern 100 (@subseteq coPset _ _) => set_solver.
Local Hint Extern 100 (_ ∉ _) => set_solver.
Local Hint Extern 99 ({[ _ ]} ⊆ _) => apply elem_of_subseteq_singleton.

(** Derived forms and lemmas about them. *)
Definition inv {Λ Σ} (N : namespace) (P : iProp Λ Σ) : iProp Λ Σ :=
  (∃ i, ■ (i ∈ nclose N) ∧ ownI i P)%I.
Instance: Params (@inv) 3.
Typeclasses Opaque inv.

Section inv.
Context {Λ : language} {Σ : iFunctor}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Λ Σ.
Implicit Types Φ : val Λ → iProp Λ Σ.

Global Instance inv_contractive N : Contractive (@inv Λ Σ N).
Proof. intros n ???. apply exist_ne=>i. by apply and_ne, ownI_contractive. Qed.

Global Instance inv_always_stable N P : AlwaysStable (inv N P).
Proof. rewrite /inv; apply _. Qed.

Lemma always_inv N P : (□ inv N P)%I ≡ inv N P.
Proof. by rewrite always_always. Qed.

(** Invariants can be opened around any frame-shifting assertion. *)
Lemma inv_fsa {A} (fsa : FSA Λ Σ A) `{!FrameShiftAssertion fsaV fsa} E N P Ψ R :
  fsaV → nclose N ⊆ E →
  R ⊑ inv N P →
  R ⊑ (▷ P -★ fsa (E ∖ nclose N) (λ a, ▷ P ★ Ψ a)) →
  R ⊑ fsa E Ψ.
Proof.
  intros ? HN Hinv Hinner.
  rewrite -[R](idemp (∧)%I) {1}Hinv Hinner =>{Hinv Hinner R}.
  rewrite always_and_sep_l /inv sep_exist_r. apply exist_elim=>i.
  rewrite always_and_sep_l -assoc. apply const_elim_sep_l=>HiN.
  rewrite -(fsa_open_close E (E ∖ {[encode i]})) //; last by set_solver+.
  (* Add this to the local context, so that set_solver finds it. *)
  assert ({[encode i]} ⊆ nclose N) by eauto.
  rewrite (always_sep_dup (ownI _ _)).
  rewrite {1}pvs_openI !pvs_frame_r.
  apply pvs_mask_frame_mono; [set_solver..|].
  rewrite (comm _ (▷_)%I) -assoc wand_elim_r fsa_frame_l.
  apply fsa_mask_frame_mono; [set_solver..|]. intros a.
  rewrite assoc -always_and_sep_l pvs_closeI pvs_frame_r left_id.
  apply pvs_mask_frame'; set_solver.
Qed.

(* Derive the concrete forms for pvs and wp, because they are useful. *)

Lemma pvs_open_close E N P Q R :
  nclose N ⊆ E →
  R ⊑ inv N P →
  R ⊑ (▷ P -★ pvs (E ∖ nclose N) (E ∖ nclose N) (▷ P ★ Q)) →
  R ⊑ (|={E}=> Q).
Proof. intros. by apply: (inv_fsa pvs_fsa). Qed.

Lemma wp_open_close E e N P Φ R :
  atomic e → nclose N ⊆ E →
  R ⊑ inv N P →
  R ⊑ (▷ P -★ #> e @ E ∖ nclose N {{ λ v, ▷ P ★ Φ v }}) →
  R ⊑ #> e @ E {{ Φ }}.
Proof. intros. by apply: (inv_fsa (wp_fsa e)). Qed.

Lemma inv_alloc N E P : nclose N ⊆ E → ▷ P ⊑ pvs E E (inv N P).
Proof. 
  intros. rewrite -(pvs_mask_weaken N) //.
  by rewrite /inv (pvs_allocI N); last apply coPset_suffixes_infinite.
Qed.

End inv.
