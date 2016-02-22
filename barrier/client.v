From barrier Require Import barrier.
(* FIXME This needs to be imported even though barrier exports it *)
From heap_lang Require Import notation.
Import uPred.

Definition client := (let: "b" := newchan '() in wait "b")%L.

Section client.
  Context {Σ : iFunctorG} (N : namespace).
  Context `{heapG Σ} (heapN : namespace).
  Context `{stsG heap_lang Σ barrier_proto.sts}.
  Context `{savedPropG heap_lang Σ}.

  Local Notation iProp := (iPropG heap_lang Σ).

  Lemma client_safe :
    heapN ⊥ N → heap_ctx heapN ⊑ || client {{ λ _, True }}.
  Proof.
    intros ?. rewrite /client.
    (* FIXME: wp (eapply newchan_spec with (P:=True%I)). *)
    wp_focus (newchan _).
    rewrite -(newchan_spec N heapN True%I) //.
    apply sep_intro_True_r; first done.
    apply forall_intro=>l. apply wand_intro_l. rewrite right_id.
    wp_let. etrans; last eapply wait_spec.
    apply sep_mono_r. apply wand_intro_r. eauto.
  Qed.

End client.
