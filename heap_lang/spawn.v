From program_logic Require Export global_functor.
From heap_lang Require Export heap.
From heap_lang Require Import wp_tactics notation.
Import uPred.

Definition spawn : val :=
  λ: "f", let: "c" := ref (InjL #0) in
          Fork ('"c" <- InjR ('"f" #())) ;; '"c".
Definition join : val :=
  rec: "join" "c" := match: !'"c" with InjR "x" => '"x"
                                     | InjL <>  => '"join" '"c" end.

(** The monoids we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class spawnG Σ := SpawnG {
  spawn_tokG :> inG heap_lang Σ (exclR unitC);
}.
Definition spawnGF : rFunctors := [constRF (exclR unitC)].

Instance inGF_spawnG
  `{inGF heap_lang Σ (constRF (exclR unitC))} : spawnG Σ.
Proof. split. apply: inGF_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context {Σ : rFunctorG} `{!heapG Σ, !spawnG Σ}.
Context (heapN N : namespace).
Local Notation iProp := (iPropG heap_lang Σ).

Definition spawn_inv (γ : gname) (l : loc) (Ψ : val → iProp) : iProp :=
  (∃ lv, l ↦ lv ★ (lv = InjLV #0 ∨ ∃ v, lv = InjRV v ★ (Ψ v ∨ own γ (Excl ()))))%I.

Definition join_handle (l : loc) (Ψ : val → iProp) : iProp :=
  (■ (heapN ⊥ N) ★ ∃ γ, heap_ctx heapN ★ own γ (Excl ()) ★
                        inv N (spawn_inv γ l Ψ))%I.

Global Instance spawn_inv_ne n γ l :
  Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γ l).
Proof. solve_proper. Qed.
Global Instance join_handle_ne n l :
  Proper (pointwise_relation val (dist n) ==> dist n) (join_handle l).
Proof. solve_proper. Qed.

(** The main proofs. *)
Lemma spawn_spec (Ψ : val → iProp) (f : val) (Φ : val → iProp) :
  heapN ⊥ N →
  (heap_ctx heapN ★ #> f #() {{ Ψ }} ★ ∀ l, join_handle l Ψ -★ Φ (%l))
  ⊑ #> spawn f {{ Φ }}.
Proof.
  intros Hdisj. rewrite /spawn. wp_let. (ewp eapply wp_alloc); eauto with I.
  strip_later. apply forall_intro=>l. apply wand_intro_l. wp_let.
  rewrite (forall_elim l). eapply sep_elim_True_l.
  { eapply (own_alloc (Excl ())). done. }
  rewrite !pvs_frame_r. eapply wp_strip_pvs. rewrite !sep_exist_r.
  apply exist_elim=>γ.
  (* TODO: Figure out a better way to say "I want to establish ▷ spawn_inv". *)
  trans (heap_ctx heapN ★ #> f #() {{ Ψ }} ★ (join_handle l Ψ -★ Φ (%l)%V) ★
         own γ (Excl ()) ★ ▷ (spawn_inv γ l Ψ))%I.
  { ecancel [ #> f #() {{ _ }}; _ -★ _; heap_ctx _; own _ _]%I.
    rewrite -later_intro /spawn_inv -(exist_intro (InjLV #0)).
    cancel [l ↦ InjLV #0]%I. apply or_intro_l'. by rewrite const_equiv. }
  rewrite (inv_alloc N) // !pvs_frame_l. eapply wp_strip_pvs.
  ewp eapply wp_fork. rewrite [heap_ctx _]always_sep_dup [inv _ _]always_sep_dup.
  rewrite !assoc [(_ ★ (own _ _))%I]comm !assoc [(_ ★ (inv _ _))%I]comm.
  rewrite !assoc [(_ ★ (_ -★ _))%I]comm. rewrite -!assoc 3!assoc. apply sep_mono.
  - wp_seq. rewrite -!assoc. eapply wand_apply_l; [done..|].
    rewrite /join_handle. rewrite const_equiv // left_id -(exist_intro γ).
    solve_sep_entails.
  - wp_focus (f _). rewrite wp_frame_r wp_frame_l. apply wp_mono=>v.
    eapply (inv_fsa (wp_fsa _)) with (N0:=N); simpl;
      (* TODO: Collect these in some Hint DB? Or add to an existing one? *)
      eauto using to_val_InjR,to_val_InjL,to_of_val with I ndisj.
    apply wand_intro_l. rewrite /spawn_inv {1}later_exist !sep_exist_r.
    apply exist_elim=>vl. rewrite later_sep.
    eapply wp_store; eauto using to_val_InjR,to_val_InjL,to_of_val with I ndisj.
    cancel [▷ (l ↦ vl)]%I. strip_later. apply wand_intro_l.
    rewrite right_id -later_intro -{2}[(∃ _, _ ↦ _ ★ _)%I](exist_intro (InjRV v)).
    ecancel [l ↦ _]%I. apply or_intro_r'. rewrite sep_elim_r sep_elim_r sep_elim_l.
    rewrite -(exist_intro v). rewrite const_equiv // left_id. apply or_intro_l.
Qed.

Lemma join_spec (Ψ : val → iProp) l (Φ : val → iProp) :
  (join_handle l Ψ ★ ∀ v, Ψ v -★ Φ (%l))
  ⊑ #> join (%l) {{ Φ }}.
Proof.
Abort.

End proof.
