From prelude Require Export functions.
From algebra Require Export upred_big_op upred_tactics.
From program_logic Require Export sts saved_prop.
From program_logic Require Import hoare.
From heap_lang Require Export derived heap wp_tactics notation.
Import uPred.

Definition newchan := (λ: "", ref '0)%L.
Definition signal := (λ: "x", "x" <- '1)%L.
Definition wait := (rec: "wait" "x" :=if: !"x" = '1 then '() else "wait" "x")%L.

(** The STS describing the main barrier protocol. Every state has an index-set
    associated with it. These indices are actually [gname], because we use them
    with saved propositions. *)
Module barrier_proto.
  Inductive phase := Low | High.
  Record state := State { state_phase : phase; state_I : gset gname }.
  Add Printing Constructor state.
  Inductive token := Change (i : gname) | Send.

  Global Instance stateT_inhabited: Inhabited state := populate (State Low ∅).
  Global Instance Change_inj : Inj (=) (=) Change.
  Proof. by injection 1. Qed.

  Inductive prim_step : relation state :=
    | ChangeI p I2 I1 : prim_step (State p I1) (State p I2)
    | ChangePhase I : prim_step (State Low I) (State High I).

  Definition change_tok (I : gset gname) : set token :=
    mkSet (λ t, match t with Change i => i ∉ I | Send => False end).
  Definition send_tok (p : phase) : set token :=
    match p with Low => ∅ | High => {[ Send ]} end.
  Definition tok (s : state) : set token :=
    change_tok (state_I s) ∪ send_tok (state_phase s).
  Global Arguments tok !_ /.

  Canonical Structure sts := sts.STS prim_step tok.

  (* The set of states containing some particular i *)
  Definition i_states (i : gname) : set state :=
    mkSet (λ s, i ∈ state_I s).

  (* The set of low states *)
  Definition low_states : set state :=
    mkSet (λ s, if state_phase s is Low then True else False).

  Lemma i_states_closed i : sts.closed (i_states i) {[ Change i ]}.
  Proof.
    split.
    - move=>[p I]. rewrite /= !mkSet_elem_of /= =>HI.
      destruct p; set_solver by eauto.
    - (* If we do the destruct of the states early, and then inversion
         on the proof of a transition, it doesn't work - we do not obtain
         the equalities we need. So we destruct the states late, because this
         means we can use "destruct" instead of "inversion". *)
      move=>s1 s2. rewrite !mkSet_elem_of.
      intros Hs1 [T1 T2 Hdisj Hstep'].
      inversion_clear Hstep' as [? ? ? ? Htrans _ _ Htok].
      destruct Htrans; simpl in *; last done.
      move: Hs1 Hdisj Htok. rewrite elem_of_equiv_empty elem_of_equiv.
      move=> ? /(_ (Change i)) Hdisj /(_ (Change i)); move: Hdisj.
      rewrite elem_of_intersection elem_of_union !mkSet_elem_of.
      intros; apply dec_stable.
      destruct p; set_solver.
  Qed.

  Lemma low_states_closed : sts.closed low_states {[ Send ]}.
  Proof.
    split.
    - move=>[p I]. rewrite /= /tok !mkSet_elem_of /= =>HI.
      destruct p; set_solver.
    - move=>s1 s2. rewrite !mkSet_elem_of.
      intros Hs1 [T1 T2 Hdisj Hstep'].
      inversion_clear Hstep' as [? ? ? ? Htrans _ _ Htok].
      destruct Htrans; simpl in *; first by destruct p.
      set_solver.
  Qed.

  (* Proof that we can take the steps we need. *)
  Lemma signal_step I : sts.steps (State Low I, {[Send]}) (State High I, ∅).
  Proof. apply rtc_once. constructor; first constructor; set_solver. Qed.

  Lemma wait_step i I :
    i ∈ I →
    sts.steps (State High I, {[ Change i ]}) (State High (I ∖ {[ i ]}), ∅).
  Proof.
    intros. apply rtc_once.
    constructor; first constructor; simpl; [set_solver by eauto..|].
    (* TODO this proof is rather annoying. *)
    apply elem_of_equiv=>t. rewrite !elem_of_union.
    rewrite !mkSet_elem_of /change_tok /=.
    destruct t as [j|]; last set_solver.
    rewrite elem_of_difference elem_of_singleton.
    destruct (decide (i = j)); set_solver.
  Qed.

  Lemma split_step p i i1 i2 I :
    i ∈ I → i1 ∉ I → i2 ∉ I → i1 ≠ i2 →
    sts.steps
      (State p I, {[ Change i ]})
      (State p ({[i1]} ∪ ({[i2]} ∪ (I ∖ {[i]}))), {[ Change i1; Change i2 ]}).
  Proof.
    intros. apply rtc_once.
    constructor; first constructor; simpl.
    - destruct p; set_solver.
    (* This gets annoying... and I think I can see a pattern with all these proofs. Automatable? *)
    - apply elem_of_equiv=>t. destruct t; last set_solver.
      rewrite !mkSet_elem_of !not_elem_of_union !not_elem_of_singleton
        not_elem_of_difference elem_of_singleton !(inj_iff Change).
      destruct p; naive_solver.
    - apply elem_of_equiv=>t. destruct t as [j|]; last set_solver.
      rewrite !mkSet_elem_of !not_elem_of_union !not_elem_of_singleton
        not_elem_of_difference elem_of_singleton !(inj_iff Change).
      destruct (decide (i1 = j)) as [->|]; first tauto.
      destruct (decide (i2 = j)) as [->|]; intuition.
  Qed.

End barrier_proto.
(* I am too lazy to type the full module name all the time. But then
   why did we even put this into a module? Because some of the names 
   are so general.
   What we'd really like here is to import *some* of the names from
   the module into our namespaces. But Coq doesn't seem to support that...?? *)
Import barrier_proto.

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
  Proof. intros P1 P2 HP I1 I2 ->. rewrite /waiting. by setoid_rewrite HP. Qed.
  Global Instance barrier_inv_ne n l :
    Proper (dist n ==> pointwise_relation _ (dist n)) (barrier_inv l).
  Proof.
    intros P1 P2 HP [[] ]; rewrite /barrier_inv //=. by setoid_rewrite HP.
  Qed.
  Global Instance barrier_ctx_ne n γ l : Proper (dist n ==> dist n) (barrier_ctx γ l).
  Proof. intros P1 P2 HP. rewrite /barrier_ctx. by setoid_rewrite HP. Qed.
  Global Instance send_ne n l : Proper (dist n ==> dist n) (send l).
  Proof. intros P1 P2 HP. rewrite /send. by setoid_rewrite HP. Qed.
  Global Instance recv_ne n l : Proper (dist n ==> dist n) (recv l).
  Proof. intros R1 R2 HR. rewrite /recv. by setoid_rewrite HR. Qed.

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
      + move=> /= t. rewrite !mkSet_elem_of; intros [<-|<-]; set_solver.
      + rewrite !mkSet_elem_of; set_solver.
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
          rewrite !mkSet_elem_of; set_solver.
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
          rewrite !mkSet_elem_of; set_solver.
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

Section spec.
  Context {Σ : iFunctorG} `{!heapG Σ} `{!barrierG Σ}. 

  Local Notation iProp := (iPropG heap_lang Σ).

  (* TODO: Maybe notation for LocV (and Loc)? *)
  Lemma barrier_spec (heapN N : namespace) :
    heapN ⊥ N →
    ∃ recv send : loc -> iProp -n> iProp,
      (∀ P, heap_ctx heapN ⊑ {{ True }} newchan '() {{ λ v, ∃ l, v = LocV l ★ recv l P ★ send l P }}) ∧
      (∀ l P, {{ send l P ★ P }} signal (LocV l) {{ λ _, True }}) ∧
      (∀ l P, {{ recv l P }} wait (LocV l) {{ λ _, P }}) ∧
      (∀ l P Q, {{ recv l (P ★ Q) }} Skip {{ λ _, recv l P ★ recv l Q }}) ∧
      (∀ l P Q, (P -★ Q) ⊑ (recv l P -★ recv l Q)).
  Proof.
    intros HN.
    exists (λ l, CofeMor (recv heapN N l)), (λ l, CofeMor (send heapN N l)).
    split_and?; simpl.
    - intros P. apply: always_intro. apply impl_intro_r.
      rewrite -(newchan_spec heapN N P) // always_and_sep_r.
      apply sep_mono_r, forall_intro=>l; apply wand_intro_l.
      by rewrite right_id -(exist_intro l) const_equiv // left_id.
    - intros l P. apply ht_alt. by rewrite -signal_spec right_id.
    - intros l P. apply ht_alt.
      by rewrite -(wait_spec heapN N l P) wand_diag right_id.
    - intros l P Q. apply ht_alt. rewrite -(recv_split heapN N l P Q).
      apply sep_intro_True_r; first done. apply wand_intro_l. eauto with I.
    - intros l P Q. apply recv_strengthen.
  Qed.
End spec.
