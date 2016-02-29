From barrier Require Import proof.
From program_logic Require Import auth sts saved_prop hoare ownership.
Import uPred.

Definition worker (n : Z) := (λ: "b" "y", wait "b" ;; (!"y") 'n)%L.
Definition client := (let: "y" := ref '0 in let: "b" := newbarrier '() in
                      Fork (Skip ;; Fork (worker 12 "b" "y") ;; worker 17 "b" "y") ;;
                      "y" <- (λ: "z", "z" + '42) ;; signal "b")%L.

Section client.
  Context {Σ : iFunctorG} `{!heapG Σ, !barrierG Σ} (heapN N : namespace).
  Local Notation iProp := (iPropG heap_lang Σ).

  Definition y_inv q y : iProp := (∃ f : val, y ↦{q} f ★ □ ∀ n : Z,
                            (* TODO: '() conflicts with '(n + 42)... *)
                            || f 'n {{ λ v, v = LitV (n + 42)%Z }})%I.
  
  Lemma y_inv_split q y :
    y_inv q y ⊑ (y_inv (q/2) y ★ y_inv (q/2) y).
  Proof.
    rewrite /y_inv. apply exist_elim=>f.
    rewrite -!(exist_intro f). rewrite heap_mapsto_op_split.
    ecancel [y ↦{_} _; y ↦{_} _]%I. by rewrite [X in X ⊑ _]always_sep_dup.
  Qed.

  Lemma worker_safe q (n : Z) (b y : loc) :
    (heap_ctx heapN ★ recv heapN N b (y_inv q y))
      ⊑ || worker n (Loc b) (Loc y) {{ λ _, True }}.
  Proof.
    rewrite /worker. wp_lam. wp_let. ewp apply wait_spec.
    rewrite comm. apply sep_mono_r. apply wand_intro_l.
    rewrite sep_exist_r. apply exist_elim=>f. wp_seq.
    (* TODO these aprenthesis are rather surprising. *)
    (ewp apply: (wp_load heapN _ _ q f)); eauto with I.
    strip_later. (* hu, shouldn't it do that? *)
    rewrite -assoc. apply sep_mono_r. apply wand_intro_l.
    rewrite always_elim (forall_elim n) sep_elim_r sep_elim_l.
    apply wp_mono=>?. eauto with I.
  Qed.

  Lemma client_safe :
    heapN ⊥ N → heap_ctx heapN ⊑ || client {{ λ _, True }}.
  Proof.
    intros ?. rewrite /client.
    (ewp eapply wp_alloc); eauto with I. strip_later. apply forall_intro=>y.
    apply wand_intro_l. wp_let.
    ewp eapply (newbarrier_spec heapN N (y_inv 1 y)); last done.
    rewrite comm. rewrite {1}[heap_ctx _]always_sep_dup -!assoc.
    apply sep_mono_r. apply forall_intro=>b. apply wand_intro_l. 
    wp_let. ewp eapply wp_fork.
    rewrite [heap_ctx _]always_sep_dup !assoc [(_ ★ heap_ctx _)%I]comm.
    rewrite [(|| _ {{ _ }} ★ _)%I]comm -!assoc assoc. apply sep_mono;last first.
    { (* The original thread, the sender. *)
      wp_seq. (ewp eapply wp_store); eauto with I. strip_later.
      rewrite assoc [(_ ★ y ↦ _)%I]comm. apply sep_mono_r, wand_intro_l.
      wp_seq. rewrite -signal_spec right_id assoc sep_elim_l comm.
      apply sep_mono_r. rewrite /y_inv -(exist_intro (λ: "z", "z" + '42)%L).
      apply sep_intro_True_r; first done. apply: always_intro.
      apply forall_intro=>n. wp_let. wp_op. by apply const_intro. }
    (* The two spawned threads, the waiters. *)
    ewp eapply recv_split. rewrite comm. apply sep_mono.
    { apply recv_mono. rewrite y_inv_split. done. }
    apply wand_intro_r. wp_seq. ewp eapply wp_fork.
    rewrite [heap_ctx _]always_sep_dup !assoc [(_ ★ recv _ _ _ _)%I]comm.
    rewrite -!assoc assoc. apply sep_mono.
    - wp_seq. by rewrite -worker_safe comm.
    - by rewrite -worker_safe.
  Qed.
End client.

Section ClosedProofs.
  Definition Σ : iFunctorG := #[ heapGF ; barrierGF ].
  Notation iProp := (iPropG heap_lang Σ).

  Lemma client_safe_closed σ : {{ ownP σ : iProp }} client {{ λ v, True }}.
  Proof.
    apply ht_alt. rewrite (heap_alloc ⊤ (nroot .@ "Barrier")); last first.
    { (* FIXME Really?? set_solver takes forever on "⊆ ⊤"?!? *)
      by move=>? _. }
    apply wp_strip_pvs, exist_elim=> ?. rewrite and_elim_l.
    rewrite -(client_safe (nroot .@ "Barrier") (nroot .@ "Heap")) //.
    (* This, too, should be automated. *)
    by apply ndot_ne_disjoint.
  Qed.

  Print Assumptions client_safe_closed.
End ClosedProofs.
