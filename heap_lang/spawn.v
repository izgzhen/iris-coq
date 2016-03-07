From program_logic Require Export global_functor.
From heap_lang Require Export heap.
From heap_lang Require Import wp_tactics notation.
Import uPred.

Definition spawn : val :=
  λ: "f",
    let: "c" := ref (InjL #0) in
    Fork ('"c" <- InjR ('"f" #())) ;; '"c".
Definition join : val :=
  rec: "join" "c" :=
    match: !'"c" with
      InjR "x" => '"x"
    | InjL <>  => '"join" '"c"
    end.

(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class spawnG Σ := SpawnG {
  spawn_tokG :> inG heap_lang Σ (exclR unitC);
}.
(** The functor we need. *)
Definition spawnGF : gFunctorList := [GFunctor (constRF (exclR unitC))].
(* Show and register that they match. *)
Instance inGF_spawnG
  `{H : inGFs heap_lang Σ spawnGF} : spawnG Σ.
Proof. destruct H as (?&?). split. apply: inGF_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context {Σ : gFunctors} `{!heapG Σ, !spawnG Σ}.
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
Lemma spawn_spec (Ψ : val → iProp) e (f : val) (Φ : val → iProp) :
  to_val e = Some f →
  heapN ⊥ N →
  (heap_ctx heapN ★ #> f #() {{ Ψ }} ★ ∀ l, join_handle l Ψ -★ Φ (%l))
  ⊑ #> spawn e {{ Φ }}.
Proof.
  intros Hval Hdisj. rewrite /spawn. ewp (by eapply wp_value). wp_let.
  wp eapply wp_alloc; eauto with I.
  apply forall_intro=>l. apply wand_intro_l. wp_let.
  rewrite (forall_elim l). eapply sep_elim_True_l.
  { by eapply (own_alloc (Excl ())). }
  rewrite !pvs_frame_r. eapply wp_strip_pvs. rewrite !sep_exist_r.
  apply exist_elim=>γ.
  (* TODO: Figure out a better way to say "I want to establish ▷ spawn_inv". *)
  trans (heap_ctx heapN ★ #> f #() {{ Ψ }} ★ (join_handle l Ψ -★ Φ (%l)%V) ★
         own γ (Excl ()) ★ ▷ (spawn_inv γ l Ψ))%I.
  { ecancel [ #> _ {{ _ }}; _ -★ _; heap_ctx _; own _ _]%I.
    rewrite -later_intro /spawn_inv -(exist_intro (InjLV #0)).
    cancel [l ↦ InjLV #0]%I. by apply or_intro_l', const_intro. }
  rewrite (inv_alloc N) // !pvs_frame_l. eapply wp_strip_pvs.
  ewp eapply wp_fork. rewrite [heap_ctx _]always_sep_dup [inv _ _]always_sep_dup.
  sep_split left: [_ -★ _; inv _ _; own _ _; heap_ctx _]%I.
  - wp_seq. eapply wand_apply_l; [done..|].
    rewrite /join_handle. rewrite const_equiv // left_id -(exist_intro γ).
    solve_sep_entails.
  - wp_focus (f _). rewrite wp_frame_r wp_frame_l.
    rewrite (of_to_val e) //. apply wp_mono=>v.
    eapply (inv_fsa (wp_fsa _)) with (N0:=N); simpl;
      (* TODO: Collect these in some Hint DB? Or add to an existing one? *)
      eauto using to_val_InjR,to_val_InjL,to_of_val with I ndisj.
    apply wand_intro_l. rewrite /spawn_inv {1}later_exist !sep_exist_r.
    apply exist_elim=>lv. rewrite later_sep.
    eapply wp_store; eauto using to_val_InjR,to_val_InjL,to_of_val with I ndisj.
    cancel [▷ (l ↦ lv)]%I. strip_later. apply wand_intro_l.
    rewrite right_id -later_intro -{2}[(∃ _, _ ↦ _ ★ _)%I](exist_intro (InjRV v)).
    ecancel [l ↦ _]%I. apply or_intro_r'. rewrite sep_elim_r sep_elim_r sep_elim_l.
    rewrite -(exist_intro v). rewrite const_equiv // left_id. apply or_intro_l.
Qed.

Lemma join_spec (Ψ : val → iProp) l (Φ : val → iProp) :
  (join_handle l Ψ ★ ∀ v, Ψ v -★ Φ v)
  ⊑ #> join (%l) {{ Φ }}.
Proof.
  wp_rec. wp_focus (! _)%E.
  rewrite {1}/join_handle sep_exist_l !sep_exist_r. apply exist_elim=>γ.
  rewrite -!assoc. apply const_elim_sep_l=>Hdisj.
  eapply (inv_fsa (wp_fsa _)) with (N0:=N); simpl; eauto with I ndisj.
  apply wand_intro_l. rewrite /spawn_inv {1}later_exist !sep_exist_r.
  apply exist_elim=>lv. rewrite later_sep.
  eapply wp_load; eauto with I ndisj. cancel [▷ (l ↦ lv)]%I. strip_later.
  apply wand_intro_l. rewrite -later_intro -[X in _ ⊑ (X ★ _)](exist_intro lv).
  cancel [l ↦ lv]%I. rewrite sep_or_r. apply or_elim.
  - (* Case 1 : nothing sent yet, we wait. *)
    rewrite -or_intro_l. apply const_elim_sep_l=>-> {lv}.
    do 2 rewrite const_equiv // left_id. wp_case.
    wp_seq. rewrite -always_wand_impl always_elim.
    rewrite !assoc. eapply wand_apply_r'; first done.
    rewrite -(exist_intro γ). solve_sep_entails.
  - rewrite [(_ ★ □ _)%I]sep_elim_l -or_intro_r !sep_exist_r. apply exist_mono=>v.
    rewrite -!assoc. apply const_elim_sep_l=>->{lv}. rewrite const_equiv // left_id.
    rewrite sep_or_r. apply or_elim; last first.
    { (* contradiction: we have the token twice. *)
      rewrite [(heap_ctx _ ★ _)%I]sep_elim_r !assoc. rewrite -own_op own_valid_l.
      rewrite -!assoc discrete_valid. apply const_elim_sep_l=>-[]. }
    rewrite -or_intro_r. ecancel [own _ _].
    wp_case. wp_let. ewp (eapply wp_value; wp_done).
    rewrite (forall_elim v). rewrite !assoc. eapply wand_apply_r'; eauto with I.
Qed.

End proof.
