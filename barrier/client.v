From barrier Require Import proof.
From heap_lang Require Import par.
From program_logic Require Import auth sts saved_prop hoare ownership.
Import uPred.

Definition worker (n : Z) : val :=
  λ: "b" "y", ^wait '"b" ;; !'"y" #n.
Definition client : expr [] :=
  let: "y" := ref #0 in
  let: "b" := ^newbarrier #() in
  ('"y" <- (λ: "z", '"z" + #42) ;; ^signal '"b") ||
    (^(worker 12) '"b" '"y" || ^(worker 17) '"b" '"y").

Section client.
  Context {Σ : gFunctors} `{!heapG Σ, !barrierG Σ, !spawnG Σ} (heapN N : namespace).
  Local Notation iProp := (iPropG heap_lang Σ).

  Definition y_inv q y : iProp :=
    (∃ f : val, y ↦{q} f ★ □ ∀ n : Z, #> f #n {{ λ v, v = #(n + 42) }})%I.

  Lemma y_inv_split q y :
    y_inv q y ⊑ (y_inv (q/2) y ★ y_inv (q/2) y).
  Proof.
    rewrite /y_inv. apply exist_elim=>f.
    rewrite -!(exist_intro f). rewrite heap_mapsto_op_split.
    ecancel [y ↦{_} _; y ↦{_} _]%I. by rewrite [X in X ⊑ _]always_sep_dup.
  Qed.

  Lemma worker_safe q (n : Z) (b y : loc) :
    (heap_ctx heapN ★ recv heapN N b (y_inv q y))
      ⊑ #> worker n (%b) (%y) {{ λ _, True }}.
  Proof.
    rewrite /worker. wp_lam. wp_let. ewp apply wait_spec.
    rewrite comm. apply sep_mono_r. apply wand_intro_l.
    rewrite sep_exist_r. apply exist_elim=>f. wp_seq.
    (* TODO these parenthesis are rather surprising. *)
    (ewp apply: (wp_load heapN _ _ q f)); eauto with I.
    strip_later. (* hu, shouldn't it do that? *)
    rewrite -assoc. apply sep_mono_r. apply wand_intro_l.
    rewrite always_elim (forall_elim n) sep_elim_r sep_elim_l.
    apply wp_mono=>?. eauto with I.
  Qed.

  Lemma client_safe :
    heapN ⊥ N → heap_ctx heapN ⊑ #> client {{ λ _, True }}.
  Proof.
    intros ?. rewrite /client.
    (ewp eapply wp_alloc); eauto with I. strip_later. apply forall_intro=>y.
    apply wand_intro_l. wp_let.
    ewp eapply (newbarrier_spec heapN N (y_inv 1 y)); last done.
    rewrite comm. rewrite {1}[heap_ctx _]always_sep_dup -!assoc.
    apply sep_mono_r. apply forall_intro=>b. apply wand_intro_l. 
    wp_let. (ewp eapply (wp_par heapN N (λ _, True%I) (λ _, True%I))); eauto.
    rewrite 2!{1}[heap_ctx _]always_sep_dup !assoc [(_ ★ heap_ctx _)%I]comm.
    ecancel [heap_ctx _]. sep_split right: []; last first.
    { do 2 apply forall_intro=>_. apply wand_intro_l.
      eauto using later_intro with I. }
    sep_split left: [send heapN _ _ _; heap_ctx _; y ↦ _]%I.
    - (* The original thread, the sender. *)
      (ewp eapply wp_store); eauto with I. strip_later.
      ecancel [y ↦ _]%I. apply wand_intro_l.
      wp_seq. rewrite -signal_spec right_id assoc sep_elim_l comm.
      apply sep_mono_r. rewrite /y_inv -(exist_intro (λ: "z", '"z" + #42)%V).
      apply sep_intro_True_r; first done. apply: always_intro.
      apply forall_intro=>n. wp_let. wp_op. by apply const_intro.
    - (* The two spawned threads, the waiters. *)
      rewrite recv_mono; last exact: y_inv_split.
      rewrite (recv_split _ _ ⊤) // pvs_frame_r. apply wp_strip_pvs.
      (ewp eapply (wp_par heapN N (λ _, True%I) (λ _, True%I))); eauto.
      do 2 rewrite {1}[heap_ctx _]always_sep_dup.
      ecancel [heap_ctx _]. rewrite !assoc. sep_split right: []; last first.
      { do 2 apply forall_intro=>_. apply wand_intro_l.
        eauto using later_intro with I. }
      sep_split left: [recv heapN _ _ _; heap_ctx _]%I; by rewrite -worker_safe comm.
Qed.
End client.

Section ClosedProofs.
  Definition Σ : gFunctors := #[ heapGF ; barrierGF ; spawnGF ].
  Notation iProp := (iPropG heap_lang Σ).

  Lemma client_safe_closed σ : {{ ownP σ : iProp }} client {{ λ v, True }}.
  Proof.
    apply ht_alt. rewrite (heap_alloc (nroot .@ "Barrier")); last done.
    apply wp_strip_pvs, exist_elim=> ?. rewrite and_elim_l.
    rewrite -(client_safe (nroot .@ "Barrier") (nroot .@ "Heap")) //.
    (* This, too, should be automated. *)
    by apply ndot_ne_disjoint.
  Qed.

  Print Assumptions client_safe_closed.
End ClosedProofs.
