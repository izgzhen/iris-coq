From barrier Require Import barrier.
From program_logic Require Import auth sts saved_prop hoare ownership.
Import uPred.

Definition client := (let: "b" := newchan '() in wait "b")%L.

Section client.
  Context {Σ : iFunctorG} `{!heapG Σ} `{!barrierG Σ}.
  Context (N : namespace) (heapN : namespace).

  Local Notation iProp := (iPropG heap_lang Σ).

  Lemma client_safe :
    heapN ⊥ N → heap_ctx heapN ⊑ || client {{ λ _, True }}.
  Proof.
    intros ?. rewrite /client.
    ewp eapply (newchan_spec N heapN True%I); last done.
    apply sep_intro_True_r; first done.
    apply forall_intro=>l. apply wand_intro_l. rewrite right_id.
    wp_let. etrans; last eapply wait_spec.
    apply sep_mono_r. apply wand_intro_r. eauto.
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
    rewrite -(client_safe (nroot .@ "Heap" ) (nroot .@ "Barrier" )) //.
    (* This, too, should be automated. *)
    by apply ndot_ne_disjoint.
  Qed.

  Print Assumptions client_safe_closed.
End ClosedProofs.
