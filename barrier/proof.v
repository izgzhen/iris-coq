From prelude Require Import functions.
From algebra Require Import upred_big_op.
From program_logic Require Import sts saved_prop tactics.
From heap_lang Require Export heap wp_tactics.
From barrier Require Export barrier.
From barrier Require Import protocol.
Import uPred.

(** The CMRAs we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class barrierG Σ := BarrierG {
  barrier_stsG :> stsG heap_lang Σ sts;
  barrier_savedPropG :> savedPropG heap_lang Σ idCF;
}.
(** The Functors we need. *)
Definition barrierGF : gFunctorList := [stsGF sts; savedPropGF idCF].
(* Show and register that they match. *)
Instance inGF_barrierG `{H : inGFs heap_lang Σ barrierGF} : barrierG Σ.
Proof. destruct H as (?&?&?). split; apply _. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context {Σ : gFunctors} `{!heapG Σ, !barrierG Σ}.
Context (heapN N : namespace).
Local Notation iProp := (iPropG heap_lang Σ).

Definition ress (P : iProp) (I : gset gname) : iProp :=
  (∃ Ψ : gname → iProp,
    ▷ (P -★ Π★{set I} Ψ) ★ Π★{set I} (λ i, saved_prop_own i (Ψ i)))%I.

Coercion state_to_val (s : state) : val :=
  match s with State Low _ => #0 | State High _ => #1 end.
Arguments state_to_val !_ /.

Definition state_to_prop (s : state) (P : iProp) : iProp :=
  match s with State Low _ => P | State High _ => True%I end.
Arguments state_to_val !_ /.

Definition barrier_inv (l : loc) (P : iProp) (s : state) : iProp :=
  (l ↦ s ★ ress (state_to_prop s P) (state_I s))%I.

Definition barrier_ctx (γ : gname) (l : loc) (P : iProp) : iProp :=
  (■ (heapN ⊥ N) ★ heap_ctx heapN ★ sts_ctx γ N (barrier_inv l P))%I.

Definition send (l : loc) (P : iProp) : iProp :=
  (∃ γ, barrier_ctx γ l P ★ sts_ownS γ low_states {[ Send ]})%I.

Definition recv (l : loc) (R : iProp) : iProp :=
  (∃ γ P Q i,
    barrier_ctx γ l P ★ sts_ownS γ (i_states i) {[ Change i ]} ★
    saved_prop_own i Q ★ ▷ (Q -★ R))%I.

Global Instance barrier_ctx_always_stable (γ : gname) (l : loc) (P : iProp) :
  AlwaysStable (barrier_ctx γ l P).
Proof. apply _. Qed.

(* TODO: Figure out if this has a "Global" or "Local" effect.
   We want it to be Global. *)
Typeclasses Opaque barrier_ctx send recv.

Implicit Types I : gset gname.

(** Setoids *)
Global Instance ress_ne n : Proper (dist n ==> (=) ==> dist n) ress.
Proof. solve_proper. Qed.
Global Instance state_to_prop_ne n s :
  Proper (dist n ==> dist n) (state_to_prop s).
Proof. solve_proper. Qed.
Global Instance barrier_inv_ne n l :
  Proper (dist n ==> eq ==> dist n) (barrier_inv l).
Proof. solve_proper. Qed.
Global Instance barrier_ctx_ne n γ l : Proper (dist n ==> dist n) (barrier_ctx γ l).
Proof. solve_proper. Qed. 
Global Instance send_ne n l : Proper (dist n ==> dist n) (send l).
Proof. solve_proper. Qed.
Global Instance recv_ne n l : Proper (dist n ==> dist n) (recv l).
Proof. solve_proper. Qed.

(** Helper lemmas *)
Lemma ress_split i i1 i2 Q R1 R2 P I :
  i ∈ I → i1 ∉ I → i2 ∉ I → i1 ≠ i2 →
  (saved_prop_own i2 R2 ★
    saved_prop_own i1 R1 ★ saved_prop_own i Q ★
    (Q -★ R1 ★ R2) ★ ress P I)
  ⊑ ress P ({[i1]} ∪ ({[i2]} ∪ (I ∖ {[i]}))).
Proof.
  intros. rewrite /ress !sep_exist_l. apply exist_elim=>Ψ.
  rewrite -(exist_intro (<[i1:=R1]> (<[i2:=R2]> Ψ))).
  rewrite [(Π★{set _} (λ _, saved_prop_own _ _))%I](big_sepS_delete _ I i) //.
  do 4 (rewrite big_sepS_insert; last set_solver).
  rewrite !fn_lookup_insert fn_lookup_insert_ne // !fn_lookup_insert.
  set savedQ := _ i Q. set savedΨ := _ i (Ψ _).
  sep_split left: [savedQ; savedΨ; Q -★ _; ▷ (_ -★ Π★{set I} _)]%I.
  - rewrite !assoc saved_prop_agree /=. strip_later.
    apply wand_intro_l. to_front [P; P -★ _]%I. rewrite wand_elim_r.
    rewrite (big_sepS_delete _ I i) //.
    sep_split right: [Π★{set _} _]%I.
    + rewrite !assoc.
      eapply wand_apply_r'; first done.
      apply: (eq_rewrite (Ψ i) Q (λ x, x)%I); last by eauto with I.
      rewrite eq_sym. eauto with I.
    + apply big_sepS_mono; [done|] => j.
      rewrite elem_of_difference not_elem_of_singleton=> -[??].
      by do 2 (rewrite fn_lookup_insert_ne; last naive_solver).
  - rewrite !assoc [(saved_prop_own i2 _ ★ _)%I]comm; apply sep_mono_r.
    apply big_sepS_mono; [done|]=> j.
    rewrite elem_of_difference not_elem_of_singleton=> -[??].
    by do 2 (rewrite fn_lookup_insert_ne; last naive_solver).
Qed.

(** Actual proofs *)
Lemma newbarrier_spec (P : iProp) (Φ : val → iProp) :
  heapN ⊥ N →
  (heap_ctx heapN ★ ∀ l, recv l P ★ send l P -★ Φ (%l))
  ⊑ #> newbarrier #() {{ Φ }}.
Proof.
  intros HN. rewrite /newbarrier. wp_seq.
  rewrite -wp_pvs. wp eapply wp_alloc; eauto with I ndisj.
  apply forall_intro=>l. rewrite (forall_elim l). apply wand_intro_l.
  rewrite !assoc. apply pvs_wand_r.
  (* The core of this proof: Allocating the STS and the saved prop. *)
  eapply sep_elim_True_r; first by eapply (saved_prop_alloc (F:=idCF) _ P).
  rewrite pvs_frame_l. apply pvs_strip_pvs. rewrite sep_exist_l.
  apply exist_elim=>i.
  trans (pvs ⊤ ⊤ (heap_ctx heapN ★
    ▷ (barrier_inv l P (State Low {[ i ]})) ★ saved_prop_own i P)).
  - rewrite -pvs_intro. cancel [heap_ctx heapN].
    rewrite {1}[saved_prop_own _ _]always_sep_dup. cancel [saved_prop_own i P].
    rewrite /barrier_inv /ress -later_intro. cancel [l ↦ #0]%I.
    rewrite -(exist_intro (const P)) /=. rewrite -[saved_prop_own _ _](left_id True%I (★)%I).
    by rewrite !big_sepS_singleton /= wand_diag -later_intro.
  - rewrite (sts_alloc (barrier_inv l P) ⊤ N); last by eauto.
    rewrite !pvs_frame_r !pvs_frame_l. 
    rewrite pvs_trans'. apply pvs_strip_pvs. rewrite sep_exist_r sep_exist_l.
    apply exist_elim=>γ.
    rewrite /recv /send. rewrite -(exist_intro γ) -(exist_intro P).
    rewrite -(exist_intro P) -(exist_intro i) -(exist_intro γ).
    rewrite always_and_sep_l wand_diag later_True right_id.
    rewrite [heap_ctx _]always_sep_dup [sts_ctx _ _ _]always_sep_dup.
    rewrite /barrier_ctx const_equiv // left_id.
    ecancel_pvs [saved_prop_own i _; heap_ctx _; heap_ctx _;
                 sts_ctx _ _ _; sts_ctx _ _ _].
    rewrite (sts_own_weaken ⊤ _ _ (i_states i ∩ low_states) _ 
                            ({[ Change i ]} ∪ {[ Send ]})).
    + apply pvs_mono.
      rewrite -sts_ownS_op; eauto using i_states_closed, low_states_closed.
      set_solver.
    + intros []; set_solver.
    + set_solver.
    + auto using sts.closed_op, i_states_closed, low_states_closed.
Qed.

Lemma signal_spec l P (Φ : val → iProp) :
  (send l P ★ P ★ Φ #()) ⊑ #> signal (%l) {{ Φ }}.
Proof.
  rewrite /signal /send /barrier_ctx. rewrite sep_exist_r.
  apply exist_elim=>γ. rewrite -!assoc. apply const_elim_sep_l=>?. wp_let.
  (* I think some evars here are better than repeating *everything* *)
  eapply (sts_fsaS _ (wp_fsa _)) with (N0:=N) (γ0:=γ); simpl;
    eauto with I ndisj.
  ecancel [sts_ownS γ _ _]. 
  apply forall_intro=>-[p I]. apply wand_intro_l. rewrite -!assoc.
  apply const_elim_sep_l=>Hs. destruct p; last done.
  rewrite {1}/barrier_inv =>/={Hs}. rewrite later_sep.
  eapply wp_store with (v' := #0); eauto with I ndisj. 
  strip_later. cancel [l ↦ #0]%I.
  apply wand_intro_l. rewrite -(exist_intro (State High I)).
  rewrite -(exist_intro ∅). rewrite const_equiv /=; last by eauto using signal_step.
  rewrite left_id -later_intro {2}/barrier_inv -!assoc. apply sep_mono_r.
  sep_split right: [Φ _]; last first.
  { apply wand_intro_l. eauto with I. }
  (* Now we come to the core of the proof: Updating from waiting to ress. *)
  rewrite /ress sep_exist_r. apply exist_mono=>{Φ} Φ.
  ecancel [Π★{set I} (λ _, saved_prop_own _ _)]%I. strip_later.
  rewrite wand_True. eapply wand_apply_l'; eauto with I.
Qed.

Lemma wait_spec l P (Φ : val → iProp) :
  (recv l P ★ (P -★ Φ #())) ⊑ #> wait (%l) {{ Φ }}.
Proof.
  rename P into R. wp_rec.
  rewrite {1}/recv /barrier_ctx. rewrite !sep_exist_r.
  apply exist_elim=>γ. rewrite !sep_exist_r. apply exist_elim=>P.
  rewrite !sep_exist_r. apply exist_elim=>Q. rewrite !sep_exist_r.
  apply exist_elim=>i. rewrite -!(assoc (★)%I). apply const_elim_sep_l=>?.
  wp_focus (! _)%E.
  (* I think some evars here are better than repeating *everything* *)
  eapply (sts_fsaS _ (wp_fsa _)) with (N0:=N) (γ0:=γ); simpl;
    eauto with I ndisj.
  ecancel [sts_ownS γ _ _].
  apply forall_intro=>-[p I]. apply wand_intro_l. rewrite -!assoc.
  apply const_elim_sep_l=>Hs.
  rewrite {1}/barrier_inv =>/=. rewrite later_sep.
  eapply wp_load; eauto with I ndisj.
  ecancel [▷ l ↦{_} _]%I. strip_later.
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
    rewrite const_equiv // left_id -later_intro.
    ecancel_pvs [heap_ctx _; saved_prop_own _ _; Q -★ _; R -★ _; sts_ctx _ _ _]%I.
    apply sts_own_weaken; eauto using i_states_closed. }
  (* a High state: the comparison succeeds, and we perform a transition and
     return to the client *)
  rewrite [(_ ★ □ (_ → _ ))%I]sep_elim_l.
  rewrite -(exist_intro (State High (I ∖ {[ i ]}))) -(exist_intro ∅).
  change (i ∈ I) in Hs.
  rewrite const_equiv /=; last by eauto using wait_step.
  rewrite left_id -[(▷ barrier_inv _ _ _)%I]later_intro {2}/barrier_inv.
  rewrite -!assoc. apply sep_mono_r. rewrite /ress.
  rewrite !sep_exist_r. apply exist_mono=>Ψ.
  rewrite !(big_sepS_delete _ I i) //= !wand_True later_sep.
  ecancel [▷ Π★{set _} Ψ; Π★{set _} (λ _, saved_prop_own _ _)]%I.
  apply wand_intro_l.  set savedΨ := _ i (Ψ _). set savedQ := _ i Q.
  to_front [savedΨ; savedQ]. rewrite saved_prop_agree /=.
  wp_op; [|done]=> _. wp_if. rewrite !assoc. eapply wand_apply_r'; first done.
  eapply wand_apply_r'; first done.
  apply: (eq_rewrite (Ψ i) Q (λ x, x)%I); by eauto with I.
Qed.

Lemma recv_split E l P1 P2 :
  nclose N ⊆ E → 
  recv l (P1 ★ P2) ⊑ |={E}=> recv l P1 ★ recv l P2.
Proof.
  rename P1 into R1. rename P2 into R2. intros HN.
  rewrite {1}/recv /barrier_ctx. 
  apply exist_elim=>γ. rewrite sep_exist_r.  apply exist_elim=>P. 
  apply exist_elim=>Q. apply exist_elim=>i. rewrite -!(assoc (★)%I).
  apply const_elim_sep_l=>?. rewrite -pvs_trans'.
  (* I think some evars here are better than repeating *everything* *)
  eapply pvs_mk_fsa, (sts_fsaS _ pvs_fsa) with (N0:=N) (γ0:=γ); simpl;
    eauto with I ndisj.
  ecancel [sts_ownS γ _ _].
  apply forall_intro=>-[p I]. apply wand_intro_l. rewrite -!assoc.
  apply const_elim_sep_l=>Hs. rewrite /pvs_fsa.
  eapply sep_elim_True_l.
  { eapply saved_prop_alloc_strong with (x := R1) (G := I). }
  rewrite pvs_frame_r. apply pvs_strip_pvs. rewrite sep_exist_r.
  apply exist_elim=>i1. rewrite always_and_sep_l. rewrite -assoc.
  apply const_elim_sep_l=>Hi1. eapply sep_elim_True_l.
  { eapply saved_prop_alloc_strong with (x := R2) (G := I ∪ {[ i1 ]}). }
  rewrite pvs_frame_r. apply pvs_mono. rewrite sep_exist_r.
  apply exist_elim=>i2. rewrite always_and_sep_l. rewrite -assoc.
  apply const_elim_sep_l=>Hi2.
  rewrite ->not_elem_of_union, elem_of_singleton in Hi2.
  destruct Hi2 as [Hi2 Hi12]. change (i ∈ I) in Hs.
  (* Update to new state. *)
  rewrite -(exist_intro (State p ({[i1]} ∪ ({[i2]} ∪ (I ∖ {[i]}))))).
  rewrite -(exist_intro ({[Change i1 ]} ∪ {[ Change i2 ]})).
  rewrite [(■ sts.steps _ _)%I]const_equiv; last by eauto using split_step.
  rewrite left_id {1 3}/barrier_inv.
  (* FIXME ssreflect rewrite fails if there are evars around. Also, this is very slow because we don't have a proof mode. *)
  rewrite -(ress_split _ _ _ Q R1 R2); [|done..].
  rewrite {1}[saved_prop_own i1 _]always_sep_dup.
  rewrite {1}[saved_prop_own i2 _]always_sep_dup !later_sep.
  rewrite -![(▷ saved_prop_own _ _)%I]later_intro.
  ecancel [▷ l ↦ _; saved_prop_own i1 _; saved_prop_own i2 _ ;
           ▷ ress _ _ ; ▷ (Q -★ _) ; saved_prop_own i _]%I. 
  apply wand_intro_l. rewrite !assoc. rewrite /recv.
  rewrite -(exist_intro γ) -(exist_intro P) -(exist_intro R1) -(exist_intro i1).
  rewrite -(exist_intro γ) -(exist_intro P) -(exist_intro R2) -(exist_intro i2).
  rewrite [heap_ctx _]always_sep_dup [sts_ctx _ _ _]always_sep_dup.
  rewrite /barrier_ctx const_equiv // left_id.
  ecancel_pvs [saved_prop_own i1 _; saved_prop_own i2 _; heap_ctx _; heap_ctx _;
               sts_ctx _ _ _; sts_ctx _ _ _].
  rewrite !wand_diag later_True !right_id.
  rewrite -sts_ownS_op; eauto using i_states_closed.
  - apply sts_own_weaken;
      eauto using sts.closed_op, i_states_closed. set_solver.
  - set_solver.
Qed.

Lemma recv_weaken l P1 P2 :
  (P1 -★ P2) ⊑ (recv l P1 -★ recv l P2).
Proof.
  apply wand_intro_l. rewrite /recv. rewrite sep_exist_r. apply exist_mono=>γ.
  rewrite sep_exist_r. apply exist_mono=>P. rewrite sep_exist_r.
  apply exist_mono=>Q. rewrite sep_exist_r. apply exist_mono=>i.
  ecancel [barrier_ctx _ _ _; sts_ownS _ _ _; saved_prop_own _ _].
  strip_later. apply wand_intro_l. by rewrite !assoc wand_elim_r wand_elim_r.
Qed.

Lemma recv_mono l P1 P2 :
  P1 ⊑ P2 → recv l P1 ⊑ recv l P2.
Proof.
  intros HP%entails_wand. apply wand_entails. rewrite HP. apply recv_weaken.
Qed.

End proof.
