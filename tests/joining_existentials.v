From iris.program_logic Require Import saved_one_shot hoare tactics.
From iris.heap_lang.lib.barrier Require Import proof specification.
From iris.heap_lang Require Import notation par.
Import uPred.

Definition client eM eW1 eW2 : expr [] :=
  (let: "b" := newbarrier #() in (eM ;; ^signal '"b") ||
                              ((^wait '"b" ;; eW1) || (^wait '"b" ;; eW2))).

Section proof.
Context (G : cFunctor).
Context {Σ : gFunctors} `{!heapG Σ, !barrierG Σ, !spawnG Σ, !oneShotG heap_lang Σ G}.
Context (heapN N : namespace).
Local Notation iProp := (iPropG heap_lang Σ).
Local Notation X := (G iProp).

Definition barrier_res γ (P : X → iProp) : iProp :=
  (∃ x:X, one_shot_own γ x ★ P x)%I.


Lemma worker_spec e γ l (P Q : X → iProp) (R : iProp) :
  R ⊢ (∀ x, {{ P x }} e {{ λ _, Q x }}) →
  R ⊢ (recv heapN N l (barrier_res γ P)) →
  R ⊢ WP wait (%l) ;; e {{ λ _, barrier_res γ Q }}.
Proof.
  intros He HΦ. rewrite -[R](idemp (∧)%I) {1}He HΦ always_and_sep_l {He HΦ}.
  ewp (eapply wait_spec). ecancel [recv _ _ l _]. apply wand_intro_r. wp_seq.
  rewrite /barrier_res sep_exist_l. apply exist_elim=>x.
  rewrite (forall_elim x) /ht always_elim impl_wand !assoc.
  to_front [P x; _ -★ _]%I. rewrite wand_elim_r !wp_frame_r.
  apply wp_mono=>v. by rewrite -(exist_intro x) comm.
Qed.

Context (P' : iProp) (P P1 P2 Q Q1 Q2 : X -n> iProp).
Context {P_split : ∀ x:X, P x ⊢ (P1 x ★ P2 x)}.
Context {Q_join  : ∀ x:X, (Q1 x ★ Q2 x) ⊢ Q x}.

Lemma P_res_split γ :
  barrier_res γ P ⊢ (barrier_res γ P1 ★ barrier_res γ P2).
Proof.
  rewrite /barrier_res. apply exist_elim=>x. do 2 rewrite -(exist_intro x).
  rewrite P_split {1}[one_shot_own _ _]always_sep_dup.
  solve_sep_entails.
Qed.

Lemma Q_res_join γ :
  (barrier_res γ Q1 ★ barrier_res γ Q2) ⊢ ▷ barrier_res γ Q.
Proof.
  rewrite /barrier_res sep_exist_r. apply exist_elim=>x1.
  rewrite sep_exist_l. apply exist_elim=>x2.
  rewrite [one_shot_own γ x1]always_sep_dup.
  to_front [one_shot_own γ x1; one_shot_own γ x2]. rewrite one_shot_agree.
  strip_later. rewrite -(exist_intro x1) -Q_join.
  ecancel [one_shot_own γ _; Q1 _].
  eapply (eq_rewrite x2 x1 (λ x, Q2 x)); last by eauto with I.
  { (* FIXME typeclass search should find this. *)
    apply cofe_mor_ne. }
  rewrite eq_sym. eauto with I.
Qed.

Lemma client_spec (eM eW1 eW2 : expr []) (eM' eW1' eW2' : expr ("b" :b: [])) (R : iProp) :
  heapN ⊥ N → eM' = wexpr' eM → eW1' = wexpr' eW1 → eW2' = wexpr' eW2 →
  R ⊢ ({{ P' }} eM {{ λ _, ∃ x, P x }}) →
  R ⊢ (∀ x, {{ P1 x }} eW1 {{ λ _, Q1 x }}) →
  R ⊢ (∀ x, {{ P2 x }} eW2 {{ λ _, Q2 x }}) →
  R ⊢ heap_ctx heapN →
  R ⊢ P' →
  R ⊢ WP client eM' eW1' eW2' {{ λ _, ∃ γ, barrier_res γ Q }}.
Proof.
  intros HN -> -> -> HeM HeW1 HeW2 Hheap HP'.
  rewrite -4!{1}[R](idemp (∧)%I) {1}HeM {1}HeW1 {1}HeW2 {1}Hheap {1}HP' !always_and_sep_l {Hheap} /client.
  to_front []. rewrite one_shot_alloc !pvs_frame_r !sep_exist_r.
  apply wp_strip_pvs, exist_elim=>γ. rewrite {1}[heap_ctx _]always_sep_dup.
  (ewp (eapply (newbarrier_spec heapN N (barrier_res γ P)))); last done.
  cancel [heap_ctx heapN]. apply forall_intro=>l. apply wand_intro_r.
  set (workers_post (v : val) := (barrier_res γ Q1 ★ barrier_res γ Q2)%I).
  wp_let. (ewp (eapply wp_par with (Ψ1 := λ _, True%I) (Ψ2 := workers_post))); last first.
  { done. } (* FIXME why does this simple goal even appear? *)
  rewrite {1}[heap_ctx _]always_sep_dup. cancel [heap_ctx heapN].
  sep_split left: [one_shot_pending γ; send _ _ _ _ ; P'; {{ _ }} eM {{ _ }}]%I.
  { (* Main thread. *)
    wp_focus eM. rewrite /ht always_elim impl_wand wand_elim_r !wp_frame_l.
    apply wp_mono=>v. wp_seq. rewrite !sep_exist_l. apply exist_elim=>x.
    rewrite (one_shot_init _ γ x) !pvs_frame_r. apply wp_strip_pvs.
    ewp (eapply signal_spec). ecancel [send _ _ _ _].
    by rewrite /barrier_res -(exist_intro x). }
  sep_split right: [].
  - (* Worker threads. *)
    rewrite recv_mono; last exact: P_res_split. rewrite (recv_split _ _ ⊤) //.
    rewrite ?pvs_frame_r !pvs_frame_l. apply wp_strip_pvs.
    (ewp (eapply wp_par with (Ψ1 := λ _, barrier_res γ Q1) (Ψ2 := λ _, barrier_res γ Q2))); last first.
    { done. } ecancel [heap_ctx _].
    sep_split left: [recv _ _ _ (barrier_res γ P1); ∀ _, {{ _ }} eW1 {{ _ }}]%I.
    { eapply worker_spec; eauto with I. }
    sep_split left: [recv _ _ _ (barrier_res γ P2); ∀ _, {{ _ }} eW2 {{ _ }}]%I.
    { eapply worker_spec; eauto with I. }
    rewrite /workers_post. do 2 apply forall_intro=>_. 
    (* FIXME: this should work: rewrite -later_intro. *)
    apply wand_intro_r. rewrite -later_intro. solve_sep_entails.
  - (* Merging. *)
    rewrite /workers_post. do 2 apply forall_intro=>_. apply wand_intro_r.
    rewrite !left_id Q_res_join. strip_later. by rewrite -(exist_intro γ).
Qed.

End proof.
