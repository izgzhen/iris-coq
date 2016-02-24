From prelude Require Import functions.
From algebra Require Import upred_big_op upred_tactics.
From program_logic Require Import sts saved_prop.
From heap_lang Require Export heap wp_tactics.
From barrier Require Import protocol.
From barrier Require Export barrier.
Import uPred.

(** The monoids we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class barrierG Σ := BarrierG {
  barrier_stsG :> stsG heap_lang Σ sts;
  barrier_savedPropG :> savedPropG heap_lang Σ;
}.
Definition barrierGF : iFunctors := [stsGF sts; agreeF].

Instance inGF_barrierG
  `{inGF heap_lang Σ (stsGF sts), inGF heap_lang Σ agreeF} : barrierG Σ.
Proof. split; apply _. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context {Σ : iFunctorG} `{!heapG Σ, !barrierG Σ}.
Context (heapN N : namespace).
Local Notation iProp := (iPropG heap_lang Σ).

Definition waiting (P : iProp) (I : gset gname) : iProp :=
  (∃ Ψ : gname → iProp,
    ▷ (P -★ Π★{set I} Ψ) ★ Π★{set I} (λ i, saved_prop_own i (Ψ i)))%I.

Definition ress (I : gset gname) : iProp :=
  (Π★{set I} (λ i, ∃ R, saved_prop_own i R ★ ▷ R))%I.

Coercion state_to_val (s : state) : val :=
  match s with State Low _ => '0 | State High _ => '1 end.
Arguments state_to_val !_ /.

Definition barrier_inv (l : loc) (P : iProp) (s : state) : iProp :=
  (l ↦ s ★
   match s with State Low I' => waiting P I' | State High I' => ress I' end
  )%I.

Definition barrier_ctx (γ : gname) (l : loc) (P : iProp) : iProp :=
  (■ (heapN ⊥ N) ★ heap_ctx heapN ★ sts_ctx γ N (barrier_inv l P))%I.

Definition send (l : loc) (P : iProp) : iProp :=
  (∃ γ, barrier_ctx γ l P ★ sts_ownS γ low_states {[ Send ]})%I.

Definition recv (l : loc) (R : iProp) : iProp :=
  (∃ γ P Q i,
    barrier_ctx γ l P ★ sts_ownS γ (i_states i) {[ Change i ]} ★
    saved_prop_own i Q ★ ▷ (Q -★ R))%I.

(** Setoids *)
(* These lemmas really ought to be doable by just calling a tactic.
   It is just application of already registered congruence lemmas. *)
Global Instance waiting_ne n : Proper (dist n ==> (=) ==> dist n) waiting.
Proof. intros P P' HP I ? <-. rewrite /waiting. by setoid_rewrite HP. Qed.
Global Instance barrier_inv_ne n l :
  Proper (dist n ==> pointwise_relation _ (dist n)) (barrier_inv l).
Proof. intros P P' HP [[]]; rewrite /barrier_inv //=. by setoid_rewrite HP. Qed.
Global Instance barrier_ctx_ne n γ l : Proper (dist n ==> dist n) (barrier_ctx γ l).
Proof. intros P P' HP. rewrite /barrier_ctx. by setoid_rewrite HP. Qed.
Global Instance send_ne n l : Proper (dist n ==> dist n) (send l).
Proof. intros P P' HP. rewrite /send. by setoid_rewrite HP. Qed.
Global Instance recv_ne n l : Proper (dist n ==> dist n) (recv l).
Proof. intros R R' HR. rewrite /recv. by setoid_rewrite HR. Qed.

(** Helper lemmas *)
Lemma waiting_split i i1 i2 Q R1 R2 P I :
  i ∈ I → i1 ∉ I → i2 ∉ I → i1 ≠ i2 →
  (saved_prop_own i2 R2 ★ saved_prop_own i1 R1 ★ saved_prop_own i Q ★
   (Q -★ R1 ★ R2) ★ waiting P I)
  ⊑ waiting P ({[i1]} ∪ ({[i2]} ∪ (I ∖ {[i]}))).
Proof.
  intros. rewrite /waiting !sep_exist_l. apply exist_elim=>Ψ.
  rewrite -(exist_intro (<[i1:=R1]> (<[i2:=R2]> Ψ))).
  rewrite [(Π★{set _} (λ _, saved_prop_own _ _))%I](big_sepS_delete _ I i) //.
  rewrite !assoc [(_ ★ (_ -★ _))%I]comm !assoc [(_ ★ ▷ _)%I]comm.
  rewrite !assoc [(_ ★ _ i _)%I]comm !assoc [(_ ★ _ i _)%I]comm -!assoc.
  do 4 (rewrite big_sepS_insert; last set_solver).
  rewrite !fn_lookup_insert fn_lookup_insert_ne // !fn_lookup_insert.
  rewrite 3!assoc. apply sep_mono.
  - rewrite saved_prop_agree. u_strip_later.
    apply wand_intro_l. rewrite [(_ ★ (_ -★ Π★{set _} _))%I]comm !assoc wand_elim_r.
    rewrite (big_sepS_delete _ I i) //.
    rewrite [(_ ★ Π★{set _} _)%I]comm [(_ ★ Π★{set _} _)%I]comm -!assoc.
    apply sep_mono.
    + apply big_sepS_mono; [done|] => j.
      rewrite elem_of_difference not_elem_of_singleton=> -[??].
      by do 2 (rewrite fn_lookup_insert_ne; last naive_solver).
    + rewrite !assoc.
      eapply wand_apply_r'; first done.
      apply: (eq_rewrite (Ψ i) Q (λ x, x)%I); last by eauto with I.
      rewrite eq_sym. eauto with I.
  - rewrite !assoc [(saved_prop_own i2 _ ★ _)%I]comm; apply sep_mono_r.
    apply big_sepS_mono; [done|]=> j.
    rewrite elem_of_difference not_elem_of_singleton=> -[??].
    by do 2 (rewrite fn_lookup_insert_ne; last naive_solver).
Qed. 

Lemma ress_split i i1 i2 Q R1 R2 I :
  i ∈ I → i1 ∉ I → i2 ∉ I → i1 ≠ i2 →
  (saved_prop_own i2 R2 ★ saved_prop_own i1 R1 ★ saved_prop_own i Q ★
   (Q -★ R1 ★ R2) ★ ress I)
  ⊑ ress ({[i1]} ∪ ({[i2]} ∪ (I ∖ {[i]}))).
Proof.
  intros. rewrite /ress.
  rewrite [(Π★{set _} _)%I](big_sepS_delete _ I i) // !assoc !sep_exist_l !sep_exist_r.
  apply exist_elim=>R.
  do 2 (rewrite big_sepS_insert; last set_solver).
  rewrite -(exist_intro R1) -(exist_intro R2) [(_ i2 _ ★ _)%I]comm -!assoc.
  apply sep_mono_r. rewrite !assoc. apply sep_mono_l.
  rewrite [(▷ _ ★ _ i2 _)%I]comm -!assoc. apply sep_mono_r.
  rewrite !assoc [(_ ★ _ i R)%I]comm !assoc saved_prop_agree.
  rewrite [(▷ _ ★ _)%I]comm -!assoc. eapply wand_apply_l.
  { by rewrite <-later_wand, <-later_intro. }
  { by rewrite later_sep. }
  u_strip_later.
  apply: (eq_rewrite R Q (λ x, x)%I); eauto with I.
Qed.

(** Actual proofs *)
Lemma newchan_spec (P : iProp) (Φ : val → iProp) :
  heapN ⊥ N →
  (heap_ctx heapN ★ ∀ l, recv l P ★ send l P -★ Φ (LocV l))
  ⊑ || newchan '() {{ Φ }}.
Proof.
  intros HN. rewrite /newchan. wp_seq.
  rewrite -wp_pvs. wp eapply wp_alloc; eauto with I ndisj.
  apply forall_intro=>l. rewrite (forall_elim l). apply wand_intro_l.
  rewrite !assoc. apply pvs_wand_r.
  (* The core of this proof: Allocating the STS and the saved prop. *)
  eapply sep_elim_True_r; first by eapply (saved_prop_alloc _ P).
  rewrite pvs_frame_l. apply pvs_strip_pvs. rewrite sep_exist_l.
  apply exist_elim=>i.
  trans (pvs ⊤ ⊤ (heap_ctx heapN ★ ▷ (barrier_inv l P (State Low {[ i ]})) ★ saved_prop_own i P)).
  - rewrite -pvs_intro. cancel [heap_ctx heapN].
    rewrite {1}[saved_prop_own _ _]always_sep_dup. cancel [saved_prop_own i P].
    rewrite /barrier_inv /waiting -later_intro. cancel [l ↦ '0]%I.
    rewrite -(exist_intro (const P)) /=. rewrite -[saved_prop_own _ _](left_id True%I (★)%I).
    by rewrite !big_sepS_singleton /= wand_diag -later_intro.
  - rewrite (sts_alloc (barrier_inv l P) ⊤ N); last by eauto.
    rewrite !pvs_frame_r !pvs_frame_l. 
    rewrite pvs_trans'. apply pvs_strip_pvs. rewrite sep_exist_r sep_exist_l.
    apply exist_elim=>γ.
    rewrite /recv /send. rewrite -(exist_intro γ) -(exist_intro P).
    rewrite -(exist_intro P) -(exist_intro i) -(exist_intro γ).
    (* This is even more annoying than usually, since rewrite sometimes unfolds stuff... *)
    rewrite [barrier_ctx _ _ _]lock !assoc
            [(_ ★ locked (barrier_ctx _ _ _))%I]comm !assoc -lock.
    rewrite -always_sep_dup.
    (* TODO: This is cancelling below a pvs. *)
    rewrite [barrier_ctx _ _ _]lock always_and_sep_l -!assoc assoc -lock.
    rewrite -pvs_frame_l. rewrite /barrier_ctx const_equiv // left_id. apply sep_mono_r.
    rewrite [(saved_prop_own _ _ ★ _)%I]comm !assoc. rewrite -pvs_frame_r.
    apply sep_mono_l.
    rewrite -assoc [(▷ _ ★ _)%I]comm assoc -pvs_frame_r.
    eapply sep_elim_True_r; last eapply sep_mono_l.
    { rewrite -later_intro. apply wand_intro_l. by rewrite right_id. }
    rewrite (sts_own_weaken ⊤ _ _ (i_states i ∩ low_states) _ 
                            ({[ Change i ]} ∪ {[ Send ]})).
    + apply pvs_mono.
      rewrite -sts_ownS_op; eauto using i_states_closed, low_states_closed.
      set_solver.
    + move=> /= t. rewrite !elem_of_mkSet; intros [<-|<-]; set_solver.
    + rewrite !elem_of_mkSet; set_solver.
    + auto using sts.closed_op, i_states_closed, low_states_closed.
Qed.

Lemma signal_spec l P (Φ : val → iProp) :
  (send l P ★ P ★ Φ '()) ⊑ || signal (LocV l) {{ Φ }}.
Proof.
  rewrite /signal /send /barrier_ctx. rewrite sep_exist_r.
  apply exist_elim=>γ. rewrite -!assoc. apply const_elim_sep_l=>?. wp_let.
  (* I think some evars here are better than repeating *everything* *)
  eapply (sts_fsaS _ (wp_fsa _)) with (N0:=N) (γ0:=γ); simpl;
    eauto with I ndisj.
  rewrite !assoc [(_ ★ sts_ownS _ _ _)%I]comm -!assoc. apply sep_mono_r.
  apply forall_intro=>-[p I]. apply wand_intro_l. rewrite -!assoc.
  apply const_elim_sep_l=>Hs. destruct p; last done.
  rewrite {1}/barrier_inv =>/={Hs}. rewrite later_sep.
  eapply wp_store with (v' := '0); eauto with I ndisj. 
  u_strip_later. cancel [l ↦ '0]%I.
  apply wand_intro_l. rewrite -(exist_intro (State High I)).
  rewrite -(exist_intro ∅). rewrite const_equiv /=; last by eauto using signal_step.
  rewrite left_id -later_intro {2}/barrier_inv -!assoc. apply sep_mono_r.
  rewrite !assoc [(_ ★ P)%I]comm !assoc -2!assoc.
  apply sep_mono; last first.
  { apply wand_intro_l. eauto with I. }
  (* Now we come to the core of the proof: Updating from waiting to ress. *)
  rewrite /waiting /ress sep_exist_l. apply exist_elim=>{Φ} Φ.
  rewrite later_wand {1}(later_intro P) !assoc wand_elim_r.
  rewrite big_sepS_later -big_sepS_sepS. apply big_sepS_mono'=>i.
  by rewrite -(exist_intro (Φ i)) comm.
Qed.

Lemma wait_spec l P (Φ : val → iProp) :
  (recv l P ★ (P -★ Φ '())) ⊑ || wait (LocV l) {{ Φ }}.
Proof.
  rename P into R. wp_rec.
  rewrite {1}/recv /barrier_ctx. rewrite !sep_exist_r.
  apply exist_elim=>γ. rewrite !sep_exist_r. apply exist_elim=>P.
  rewrite !sep_exist_r. apply exist_elim=>Q. rewrite !sep_exist_r.
  apply exist_elim=>i. rewrite -!assoc. apply const_elim_sep_l=>?.
  wp_focus (! _)%L.
  (* I think some evars here are better than repeating *everything* *)
  eapply (sts_fsaS _ (wp_fsa _)) with (N0:=N) (γ0:=γ); simpl;
    eauto with I ndisj.
  rewrite !assoc [(_ ★ sts_ownS _ _ _)%I]comm -!assoc. apply sep_mono_r.
  apply forall_intro=>-[p I]. apply wand_intro_l. rewrite -!assoc.
  apply const_elim_sep_l=>Hs.
  rewrite {1}/barrier_inv =>/=. rewrite later_sep.
  eapply wp_load; eauto with I ndisj.
  rewrite -!assoc. apply sep_mono_r. u_strip_later.
  apply wand_intro_l. destruct p.
  { (* a Low state. The comparison fails, and we recurse. *)
    rewrite -(exist_intro (State Low I)) -(exist_intro {[ Change i ]}).
    rewrite [(■ sts.steps _ _ )%I]const_equiv /=; last by apply rtc_refl.
    rewrite left_id -[(▷ barrier_inv _ _ _)%I]later_intro {3}/barrier_inv.
    rewrite -!assoc. apply sep_mono_r, sep_mono_r, wand_intro_l.
    wp_op; first done. intros _. wp_if. rewrite !assoc.
    rewrite -always_wand_impl always_elim.
    rewrite -{2}pvs_wp. apply pvs_wand_r.
    rewrite -(exist_intro γ) -(exist_intro P) -(exist_intro Q) -(exist_intro i).
    rewrite !assoc.
    do 3 (rewrite -pvs_frame_r; apply sep_mono; last (try apply later_intro; reflexivity)).
    rewrite [(_ ★ heap_ctx _)%I]comm -!assoc.
    rewrite const_equiv // left_id -pvs_frame_l. apply sep_mono_r.
    rewrite comm -pvs_frame_l. apply sep_mono_r.
    apply sts_own_weaken; eauto using i_states_closed. }
  (* a High state: the comparison succeeds, and we perform a transition and
     return to the client *)
  rewrite [(_ ★ □ (_ → _ ))%I]sep_elim_l.
  rewrite -(exist_intro (State High (I ∖ {[ i ]}))) -(exist_intro ∅).
  change (i ∈ I) in Hs.
  rewrite const_equiv /=; last by eauto using wait_step.
  rewrite left_id -[(▷ barrier_inv _ _ _)%I]later_intro {2}/barrier_inv.
  rewrite -!assoc. apply sep_mono_r. rewrite /ress.
  rewrite (big_sepS_delete _ I i) // [(_ ★ Π★{set _} _)%I]comm -!assoc.
  apply sep_mono_r. rewrite !sep_exist_r. apply exist_elim=>Q'.
  apply wand_intro_l. rewrite [(heap_ctx _ ★ _)%I]sep_elim_r.
  rewrite [(sts_own _ _ _ ★ _)%I]sep_elim_r [(sts_ctx _ _ _ ★ _)%I]sep_elim_r.
  rewrite !assoc [(_ ★ saved_prop_own i Q)%I]comm !assoc saved_prop_agree.
  wp_op>; last done. intros _. u_strip_later.
  wp_if. 
  eapply wand_apply_r; [done..|]. eapply wand_apply_r; [done..|].
  apply: (eq_rewrite Q' Q (λ x, x)%I); last by eauto with I.
  rewrite eq_sym. eauto with I.
Qed.

Lemma recv_split l P1 P2 Φ :
  (recv l (P1 ★ P2) ★ (recv l P1 ★ recv l P2 -★ Φ '())) ⊑ || Skip {{ Φ }}.
Proof.
  rename P1 into R1. rename P2 into R2.
  rewrite {1}/recv /barrier_ctx. rewrite sep_exist_r.
  apply exist_elim=>γ. rewrite sep_exist_r.  apply exist_elim=>P. 
  rewrite sep_exist_r.  apply exist_elim=>Q. rewrite sep_exist_r.
  apply exist_elim=>i. rewrite -!assoc. apply const_elim_sep_l=>?. rewrite -wp_pvs.
  (* I think some evars here are better than repeating *everything* *)
  eapply (sts_fsaS _ (wp_fsa _)) with (N0:=N) (γ0:=γ); simpl;
    eauto with I ndisj.
  rewrite !assoc [(_ ★ sts_ownS _ _ _)%I]comm -!assoc. apply sep_mono_r.
  apply forall_intro=>-[p I]. apply wand_intro_l. rewrite -!assoc.
  apply const_elim_sep_l=>Hs. rewrite -wp_pvs. wp_seq.
  eapply sep_elim_True_l.
  { eapply saved_prop_alloc_strong with (P0 := R1) (G := I). }
  rewrite pvs_frame_r. apply pvs_strip_pvs. rewrite sep_exist_r.
  apply exist_elim=>i1. rewrite always_and_sep_l. rewrite -assoc.
  apply const_elim_sep_l=>Hi1. eapply sep_elim_True_l.
  { eapply saved_prop_alloc_strong with (P0 := R2) (G := I ∪ {[ i1 ]}). }
  rewrite pvs_frame_r. apply pvs_mono. rewrite sep_exist_r.
  apply exist_elim=>i2. rewrite always_and_sep_l. rewrite -assoc.
  apply const_elim_sep_l=>Hi2.
  rewrite ->not_elem_of_union, elem_of_singleton in Hi2.
  destruct Hi2 as [Hi2 Hi12]. change (i ∈ I) in Hs. destruct p.
  (* Case I: Low state. *)
  - rewrite -(exist_intro (State Low ({[i1]} ∪ ({[i2]} ∪ (I ∖ {[i]}))))).
    rewrite -(exist_intro ({[Change i1 ]} ∪ {[ Change i2 ]})).
    rewrite [(■ sts.steps _ _)%I]const_equiv; last by eauto using split_step.
    rewrite left_id -later_intro {1 3}/barrier_inv.
    (* FIXME ssreflect rewrite fails if there are evars around. Also, this is very slow because we don't have a proof mode. *)
    rewrite -(waiting_split _ _ _ Q R1 R2); [|done..].
    rewrite {1}[saved_prop_own i1 _]always_sep_dup.
    rewrite {1}[saved_prop_own i2 _]always_sep_dup.
    ecancel [l ↦ _; saved_prop_own i1 _; saved_prop_own i2 _; waiting _ _;
             _ -★ _; saved_prop_own i _]%I. 
    apply wand_intro_l. rewrite !assoc. eapply pvs_wand_r. rewrite /recv.
    rewrite -(exist_intro γ) -(exist_intro P) -(exist_intro R1) -(exist_intro i1).
    rewrite -(exist_intro γ) -(exist_intro P) -(exist_intro R2) -(exist_intro i2).
    do 2 rewrite !(assoc (★)%I) [(_ ★ sts_ownS _ _ _)%I]comm.
    rewrite -!assoc. rewrite [(sts_ownS _ _ _ ★ _ ★ _)%I]assoc -pvs_frame_r.
    apply sep_mono.
    * rewrite -sts_ownS_op; eauto using i_states_closed.
      + apply sts_own_weaken; eauto using sts.closed_op, i_states_closed.
        rewrite !elem_of_mkSet; set_solver.
      + set_solver.
    * rewrite const_equiv // !left_id.
      rewrite {1}[heap_ctx _]always_sep_dup {1}[sts_ctx _ _ _]always_sep_dup.
      rewrite !wand_diag -!later_intro. solve_sep_entails.
(* Case II: High state. TODO: Lots of this script is just copy-n-paste of the previous one.
 Most of that is because the goals are fairly similar in structure, and the proof scripts
 are mostly concerned with manually managaing the structure (assoc, comm, dup) of
 the context. *)
  - rewrite -(exist_intro (State High ({[i1]} ∪ ({[i2]} ∪ (I ∖ {[i]}))))).
    rewrite -(exist_intro ({[Change i1 ]} ∪ {[ Change i2 ]})).
    rewrite const_equiv; last by eauto using split_step.
    rewrite left_id -later_intro {1 3}/barrier_inv.
    rewrite -(ress_split _ _ _ Q R1 R2); [|done..].
    rewrite {1}[saved_prop_own i1 _]always_sep_dup.
    rewrite {1}[saved_prop_own i2 _]always_sep_dup.
    ecancel [l ↦ _; saved_prop_own i1 _; saved_prop_own i2 _; ress _;
             _ -★ _; saved_prop_own i _]%I. 
    apply wand_intro_l. rewrite !assoc. eapply pvs_wand_r. rewrite /recv.
    rewrite -(exist_intro γ) -(exist_intro P) -(exist_intro R1) -(exist_intro i1).
    rewrite -(exist_intro γ) -(exist_intro P) -(exist_intro R2) -(exist_intro i2).
    do 2 rewrite !(assoc (★)%I) [(_ ★ sts_ownS _ _ _)%I]comm.
    rewrite -!assoc. rewrite [(sts_ownS _ _ _ ★ _ ★ _)%I]assoc -pvs_frame_r.
    apply sep_mono.
    * rewrite -sts_ownS_op; eauto using i_states_closed.
      + apply sts_own_weaken; eauto using sts.closed_op, i_states_closed.
        rewrite !elem_of_mkSet; set_solver.
      + set_solver.
    * rewrite const_equiv // !left_id.
      rewrite {1}[heap_ctx _]always_sep_dup {1}[sts_ctx _ _ _]always_sep_dup.
      rewrite !wand_diag -!later_intro. solve_sep_entails.
Qed.

Lemma recv_strengthen l P1 P2 :
  (P1 -★ P2) ⊑ (recv l P1 -★ recv l P2).
Proof.
  apply wand_intro_l. rewrite /recv. rewrite sep_exist_r. apply exist_mono=>γ.
  rewrite sep_exist_r. apply exist_mono=>P. rewrite sep_exist_r.
  apply exist_mono=>Q. rewrite sep_exist_r. apply exist_mono=>i.
  rewrite -!assoc. apply sep_mono_r, sep_mono_r, sep_mono_r, sep_mono_r, sep_mono_r.
  rewrite (later_intro (P1 -★ _)%I) -later_sep. apply later_mono.
  apply wand_intro_l. by rewrite !assoc wand_elim_r wand_elim_r.
Qed.
End proof.
