From heap_lang Require Export lifting.
From algebra Require Import upred_big_op frac dec_agree.
From program_logic Require Export invariants ghost_ownership.
From program_logic Require Import ownership auth.
Import uPred.
(* TODO: The entire construction could be generalized to arbitrary languages that have
   a finmap as their state. Or maybe even beyond "as their state", i.e. arbitrary
   predicates over finmaps instead of just ownP. *)

Definition heapR : cmraT := mapR loc (fracR (dec_agreeR val)).

(** The CMRA we need. *)
Class heapG Σ := HeapG {
  heap_inG :> authG heap_lang Σ heapR;
  heap_name : gname
}.
(** The Functor we need. *)
Definition heapGF : gFunctor := authGF heapR.

Definition to_heap : state → heapR := fmap (λ v, Frac 1 (DecAgree v)).
Definition of_heap : heapR → state :=
  omap (mbind (maybe DecAgree ∘ snd) ∘ maybe2 Frac).

Section definitions.
  Context `{i : heapG Σ}.

  Definition heap_mapsto (l : loc) (q : Qp) (v: val) : iPropG heap_lang Σ :=
    auth_own heap_name {[ l := Frac q (DecAgree v) ]}.
  Definition heap_inv (h : heapR) : iPropG heap_lang Σ :=
    ownP (of_heap h).
  Definition heap_ctx (N : namespace) : iPropG heap_lang Σ :=
    auth_ctx heap_name N heap_inv.

  Global Instance heap_inv_proper : Proper ((≡) ==> (≡)) heap_inv.
  Proof. solve_proper. Qed.
  Global Instance heap_ctx_always_stable N : AlwaysStable (heap_ctx N).
  Proof. apply _. Qed.
End definitions.
Typeclasses Opaque heap_ctx heap_mapsto.

Notation "l ↦{ q } v" := (heap_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : uPred_scope.

Section heap.
  Context {Σ : gFunctors}.
  Implicit Types N : namespace.
  Implicit Types P Q : iPropG heap_lang Σ.
  Implicit Types Φ : val → iPropG heap_lang Σ.
  Implicit Types σ : state.
  Implicit Types h g : heapR.

  (** Conversion to heaps and back *)
  Global Instance of_heap_proper : Proper ((≡) ==> (=)) of_heap.
  Proof. solve_proper. Qed.
  Lemma from_to_heap σ : of_heap (to_heap σ) = σ.
  Proof.
    apply map_eq=>l. rewrite lookup_omap lookup_fmap. by case (σ !! l).
  Qed.
  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Lemma of_heap_insert l v h :
    of_heap (<[l:=Frac 1 (DecAgree v)]> h) = <[l:=v]> (of_heap h).
  Proof. by rewrite /of_heap -(omap_insert _ _ _ (Frac 1 (DecAgree v))). Qed.
  Lemma of_heap_singleton_op l q v h :
    ✓ ({[l := Frac q (DecAgree v)]} ⋅ h) →
    of_heap ({[l := Frac q (DecAgree v)]} ⋅ h) = <[l:=v]> (of_heap h).
  Proof.
    intros Hv. apply map_eq=> l'; destruct (decide (l' = l)) as [->|].
    - move: (Hv l). rewrite /of_heap lookup_insert
        lookup_omap (lookup_op _ h) lookup_singleton.
      case _:(h !! l)=>[[q' [v'|]|]|] //=; last by move=> [??].
      move=> [? /dec_agree_op_inv [->]]. by rewrite dec_agree_idemp.
    - rewrite /of_heap lookup_insert_ne // !lookup_omap.
      by rewrite (lookup_op _ h) lookup_singleton_ne // left_id.
  Qed.
  Lemma to_heap_insert l v σ :
    to_heap (<[l:=v]> σ) = <[l:=Frac 1 (DecAgree v)]> (to_heap σ).
  Proof. by rewrite /to_heap -fmap_insert. Qed.
  Lemma of_heap_None h l :
    ✓ h → of_heap h !! l = None → h !! l = None ∨ h !! l ≡ Some FracUnit.
  Proof.
    move=> /(_ l). rewrite /of_heap lookup_omap.
    by case: (h !! l)=> [[q [v|]|]|] //=; destruct 1; auto.
  Qed.
  Lemma heap_store_valid l h v1 v2 :
    ✓ ({[l := Frac 1 (DecAgree v1)]} ⋅ h) →
    ✓ ({[l := Frac 1 (DecAgree v2)]} ⋅ h).
  Proof.
    intros Hv l'; move: (Hv l'). destruct (decide (l' = l)) as [->|].
    - rewrite !lookup_op !lookup_singleton.
      case: (h !! l)=>[x|]; [|done]=> /frac_valid_inv_l=>-> //.
    - by rewrite !lookup_op !lookup_singleton_ne.
  Qed.
  Hint Resolve heap_store_valid.

  (** Allocation *)
  Lemma heap_alloc N E σ :
    authG heap_lang Σ heapR → nclose N ⊆ E →
    ownP σ ⊑ (|={E}=> ∃ _ : heapG Σ, heap_ctx N ∧ Π★{map σ} (λ l v, l ↦ v)).
  Proof.
    intros. rewrite -{1}(from_to_heap σ). etrans.
    { rewrite [ownP _]later_intro.
      apply (auth_alloc (ownP ∘ of_heap) N E (to_heap σ)); last done.
      apply to_heap_valid. }
    apply pvs_mono, exist_elim=> γ.
    rewrite -(exist_intro (HeapG _ _ γ)) /heap_ctx; apply and_mono_r.
    rewrite /heap_mapsto /heap_name.
    induction σ as [|l v σ Hl IH] using map_ind.
    { rewrite big_sepM_empty; apply True_intro. }
    rewrite to_heap_insert big_sepM_insert //.
    rewrite (map_insert_singleton_op (to_heap σ));
      last rewrite lookup_fmap Hl; auto.
    (* FIXME: investigate why we have to unfold auth_own here. *)
    by rewrite auth_own_op IH. 
  Qed.

  Context `{heapG Σ}.

  (** General properties of mapsto *)
  Lemma heap_mapsto_op_eq l q1 q2 v :
    (l ↦{q1} v ★ l ↦{q2} v)%I ≡ (l ↦{q1+q2} v)%I.
  Proof. by rewrite -auth_own_op map_op_singleton Frac_op dec_agree_idemp. Qed.

  Lemma heap_mapsto_op l q1 q2 v1 v2 :
    (l ↦{q1} v1 ★ l ↦{q2} v2)%I ≡ (v1 = v2 ∧ l ↦{q1+q2} v1)%I.
  Proof.
    destruct (decide (v1 = v2)) as [->|].
    { by rewrite heap_mapsto_op_eq const_equiv // left_id. }
    rewrite -auth_own_op map_op_singleton Frac_op dec_agree_ne //.
    apply (anti_symm (⊑)); last by apply const_elim_l.
    rewrite auth_own_valid map_validI (forall_elim l) lookup_singleton.
    rewrite option_validI frac_validI discrete_valid. by apply const_elim_r.
  Qed.

  Lemma heap_mapsto_op_split l q v :
    (l ↦{q} v)%I ≡ (l ↦{q/2} v ★ l ↦{q/2} v)%I.
  Proof. by rewrite heap_mapsto_op_eq Qp_div_2. Qed.

  (** Weakest precondition *)
  Lemma wp_alloc N E e v P Φ :
    to_val e = Some v →
    P ⊑ heap_ctx N → nclose N ⊆ E →
    P ⊑ (▷ ∀ l, l ↦ v -★ Φ (LocV l)) →
    P ⊑ #> Alloc e @ E {{ Φ }}.
  Proof.
    rewrite /heap_ctx /heap_inv=> ??? HP.
    trans (|={E}=> auth_own heap_name ∅ ★ P)%I.
    { by rewrite -pvs_frame_r -(auth_empty _ E) left_id. }
    apply wp_strip_pvs, (auth_fsa heap_inv (wp_fsa (Alloc e)))
      with N heap_name ∅; simpl; eauto with I.
    rewrite -later_intro. apply sep_mono_r,forall_intro=> h; apply wand_intro_l.
    rewrite -assoc left_id; apply const_elim_sep_l=> ?.
    rewrite -(wp_alloc_pst _ (of_heap h)) //.
    apply sep_mono_r; rewrite HP; apply later_mono.
    apply forall_mono=> l; apply wand_intro_l.
    rewrite always_and_sep_l -assoc; apply const_elim_sep_l=> ?.
    rewrite -(exist_intro (op {[ l := Frac 1 (DecAgree v) ]})).
    repeat erewrite <-exist_intro by apply _; simpl.
    rewrite -of_heap_insert left_id right_id.
    rewrite /heap_mapsto. ecancel [_ -★ Φ _]%I.
    rewrite -(map_insert_singleton_op h); last by apply of_heap_None.
    rewrite const_equiv; last by apply (map_insert_valid h).
    by rewrite left_id -later_intro.
  Qed.

  Lemma wp_load N E l q v P Φ :
    P ⊑ heap_ctx N → nclose N ⊆ E →
    P ⊑ (▷ l ↦{q} v ★ ▷ (l ↦{q} v -★ Φ v)) →
    P ⊑ #> Load (Loc l) @ E {{ Φ }}.
  Proof.
    rewrite /heap_ctx /heap_inv=> ?? HPΦ.
    apply (auth_fsa' heap_inv (wp_fsa _) id)
      with N heap_name {[ l := Frac q (DecAgree v) ]}; simpl; eauto with I.
    rewrite HPΦ{HPΦ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc; apply const_elim_sep_l=> ?.
    rewrite -(wp_load_pst _ (<[l:=v]>(of_heap h))) ?lookup_insert //.
    rewrite const_equiv // left_id.
    rewrite /heap_inv of_heap_singleton_op //.
    apply sep_mono_r, later_mono, wand_intro_l. by rewrite -later_intro.
  Qed.

  Lemma wp_store N E l v' e v P Φ :
    to_val e = Some v →
    P ⊑ heap_ctx N → nclose N ⊆ E →
    P ⊑ (▷ l ↦ v' ★ ▷ (l ↦ v -★ Φ (LitV LitUnit))) →
    P ⊑ #> Store (Loc l) e @ E {{ Φ }}.
  Proof.
    rewrite /heap_ctx /heap_inv=> ??? HPΦ.
    apply (auth_fsa' heap_inv (wp_fsa _) (alter (λ _, Frac 1 (DecAgree v)) l))
      with N heap_name {[ l := Frac 1 (DecAgree v') ]}; simpl; eauto with I.
    rewrite HPΦ{HPΦ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc; apply const_elim_sep_l=> ?.
    rewrite -(wp_store_pst _ (<[l:=v']>(of_heap h))) ?lookup_insert //.
    rewrite /heap_inv alter_singleton insert_insert !of_heap_singleton_op; eauto.
    rewrite const_equiv; last naive_solver.
    apply sep_mono_r, later_mono, wand_intro_l. by rewrite left_id -later_intro.
  Qed.

  Lemma wp_cas_fail N E l q v' e1 v1 e2 v2 P Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 →
    P ⊑ heap_ctx N → nclose N ⊆ E →
    P ⊑ (▷ l ↦{q} v' ★ ▷ (l ↦{q} v' -★ Φ (LitV (LitBool false)))) →
    P ⊑ #> CAS (Loc l) e1 e2 @ E {{ Φ }}.
  Proof.
    rewrite /heap_ctx /heap_inv=>????? HPΦ.
    apply (auth_fsa' heap_inv (wp_fsa _) id)
      with N heap_name {[ l := Frac q (DecAgree v') ]}; simpl; eauto 10 with I.
    rewrite HPΦ{HPΦ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc; apply const_elim_sep_l=> ?.
    rewrite -(wp_cas_fail_pst _ (<[l:=v']>(of_heap h))) ?lookup_insert //.
    rewrite const_equiv // left_id.
    rewrite /heap_inv !of_heap_singleton_op //.
    apply sep_mono_r, later_mono, wand_intro_l. by rewrite -later_intro.
  Qed.

  Lemma wp_cas_suc N E l e1 v1 e2 v2 P Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    P ⊑ heap_ctx N → nclose N ⊆ E →
    P ⊑ (▷ l ↦ v1 ★ ▷ (l ↦ v2 -★ Φ (LitV (LitBool true)))) →
    P ⊑ #> CAS (Loc l) e1 e2 @ E {{ Φ }}.
  Proof.
    rewrite /heap_ctx /heap_inv=> ???? HPΦ.
    apply (auth_fsa' heap_inv (wp_fsa _) (alter (λ _, Frac 1 (DecAgree v2)) l))
      with N heap_name {[ l := Frac 1 (DecAgree v1) ]}; simpl; eauto 10 with I.
    rewrite HPΦ{HPΦ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc; apply const_elim_sep_l=> ?.
    rewrite -(wp_cas_suc_pst _ (<[l:=v1]>(of_heap h))) //;
      last by rewrite lookup_insert.
    rewrite /heap_inv alter_singleton insert_insert !of_heap_singleton_op; eauto.
    rewrite lookup_insert const_equiv; last naive_solver.
    apply sep_mono_r, later_mono, wand_intro_l. by rewrite left_id -later_intro.
  Qed.
End heap.
