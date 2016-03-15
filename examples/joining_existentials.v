From iris.program_logic Require Import saved_one_shot hoare tactics.
From iris.barrier Require Import proof specification.
From iris.heap_lang Require Import notation par.
Import uPred.

Definition client eM eW1 eW2 : expr [] :=
  (let: "b" := newbarrier #() in (eM ;; ^signal '"b") ||
                              ((^wait '"b" ;; eW1) || (^wait '"b" ;; eW2))).

Section proof.
Context (G : cFunctor).
Context {Σ : gFunctors} `{!heapG Σ, !barrierG Σ, !oneShotG heap_lang Σ G}.
Context (heapN N : namespace).
Local Notation iProp := (iPropG heap_lang Σ).
Local Notation X := (G iProp).

Definition barrier_res γ (P : X → iProp) : iProp :=
  (∃ x:X, one_shot_own γ x ★ P x)%I.


Lemma worker_spec e γ l (P Q : X → iProp) (R : iProp) Φ :
  R ⊢ (∀ x, {{ P x }} e {{ λ _, Q x }}) →
  R ⊢ (recv heapN N l (barrier_res γ P) ★ (∀ v : val, barrier_res γ Q -★ Φ v )) →
  R ⊢ WP wait (%l) ;; e {{ Φ }}.
Proof.
  intros He HΦ. rewrite -[R](idemp (∧)%I) {1}He HΦ always_and_sep_l {He HΦ}.
  ewp (eapply wait_spec). ecancel [recv _ _ l _]. apply wand_intro_r. wp_seq.
  rewrite /barrier_res sep_exist_l. apply exist_elim=>x.
  rewrite (forall_elim x) /ht always_elim impl_wand !assoc.
  to_front [P x; _ -★ _]%I. rewrite wand_elim_r !wp_frame_r.
  apply wp_mono=>v. rewrite (forall_elim v). rewrite -(exist_intro x).
  to_front [one_shot_own _ _; Q _]. by rewrite wand_elim_r.
Qed.

Context (P' : iProp) (P P1 P2 Q Q1 Q2 : X → iProp).
Context {P_split : (∃ x:X, P x) ⊢ ((∃ x:X, P1 x) ★ (∃ x:X, P2 x))}.
Context {Q_join  : ((∃ x:X, Q1 x) ★ (∃ x:X, Q2 x)) ⊢ (∃ x:X, Q x)}.

Lemma client_spec (eM eW1 eW2 : expr []) (eM' eW1' eW2' : expr ("b" :b: [])) (R : iProp) :
  eM' = wexpr' eM → eW1' = wexpr' eW1 → eW2' = wexpr' eW2 →
  R ⊢ ({{ P' }} eM {{ λ _, ∃ x, P x }}) →
  R ⊢ (∀ x, {{ P1 x }} eW1 {{ λ _, Q1 x }}) →
  R ⊢ (∀ x, {{ P2 x }} eW2 {{ λ _, Q2 x }}) →
  R ⊢ heap_ctx heapN →
  R ⊢ WP client eM' eW1' eW2' {{ λ _, ∃ γ, barrier_res γ Q }}.
Proof.
Abort.
  

End proof.
