From heap_lang Require Export lifting.
From program_logic Require Export invariants ghost_ownership.
From program_logic Require Import ownership auth.
Import uPred.
(* TODO: The entire construction could be generalized to arbitrary languages that have
   a finmap as their state. Or maybe even beyond "as their state", i.e. arbitrary
   predicates over finmaps instead of just ownP. *)

Definition heapRA := mapRA loc (exclRA (leibnizC val)).

Class HeapInG Σ (i : gid) := heap_inG :> InG heap_lang Σ i (authRA heapRA).
Instance heap_inG_auth `{HeapInG Σ i} : AuthInG heap_lang Σ i heapRA.
Proof. split; apply _. Qed.

Definition to_heap : state → heapRA := fmap Excl.
Definition of_heap : heapRA → state := omap (maybe Excl).

(* TODO: Do we want to expose heap ownership based on the state, or the heapRA?
   The former does not expose the annoying "Excl", so for now I am going for
   that. We should be able to derive the lemmas we want for this, too. *)
Definition heap_mapsto {Σ} (i : gid) `{HeapInG Σ i}
    (γ : gname) (l : loc) (v : val) : iPropG heap_lang Σ :=
  auth_own i γ {[ l ↦ Excl v ]}.
Definition heap_inv {Σ} (i : gid) `{HeapInG Σ i}
  (h : heapRA) : iPropG heap_lang Σ := ownP (of_heap h).
Definition heap_ctx {Σ} (i : gid) `{HeapInG Σ i}
  (γ : gname) (N : namespace) : iPropG heap_lang Σ := auth_ctx i γ N (heap_inv i).

Section heap.
  Context {Σ : iFunctorG} (HeapI : gid) `{!HeapInG Σ HeapI}.
  Implicit Types N : namespace.
  Implicit Types P : iPropG heap_lang Σ.
  Implicit Types σ : state.
  Implicit Types h g : heapRA.
  Implicit Types γ : gname.

  (** Conversion to heaps and back *)
  Global Instance of_heap_proper : Proper ((≡) ==> (=)) of_heap.
  Proof. by intros ??; fold_leibniz=>->. Qed.
  Lemma from_to_heap σ : of_heap (to_heap σ) = σ.
  Proof.
    apply map_eq=>l. rewrite lookup_omap lookup_fmap. by case (σ !! l).
  Qed.
  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros n l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Lemma insert_of_heap l v h :
    <[l:=v]> (of_heap h) = of_heap (<[l:=Excl v]> h).
  Proof. by rewrite /of_heap -(omap_insert _ _ _ (Excl v)). Qed.
  Lemma of_heap_None h l :
    ✓ h → of_heap h !! l = None → h !! l = None ∨ h !! l ≡ Some ExclUnit.
  Proof.
    move=> /(_ O l). rewrite /of_heap lookup_omap.
    by case: (h !! l)=> [[]|]; auto.
  Qed.
  Lemma heap_singleton_inv_l h l v :
    ✓ ({[l ↦ Excl v]} ⋅ h) → h !! l = None ∨ h !! l ≡ Some ExclUnit.
  Proof.
    move=> /(_ O l). rewrite lookup_op lookup_singleton.
    by case: (h !! l)=> [[]|]; auto.
  Qed.

  (** Propers *)
  Global Instance heap_inv_proper : Proper ((≡) ==> (≡)) (heap_inv HeapI).
  Proof. intros h1 h2. by fold_leibniz=> ->. Qed.

  (** General properties of mapsto *)
  Lemma heap_mapsto_disjoint γ l v1 v2 :
    (heap_mapsto HeapI γ l v1 ★ heap_mapsto HeapI γ l v2)%I ⊑ False.
  Proof.
    rewrite /heap_mapsto -auto_own_op auto_own_valid map_op_singleton.
    rewrite map_validI (forall_elim l) lookup_singleton.
    by rewrite option_validI excl_validI.
  Qed.

  (* Rather weak, we need big separation to state something better here *)
  Lemma heap_alloc N σ : ownP σ ⊑ pvs N N (∃ γ, heap_ctx HeapI γ N).
  Proof.
    rewrite -{1}(from_to_heap σ).
    etransitivity;
      first apply (auth_alloc (ownP ∘ of_heap) N (to_heap σ)), to_heap_valid.
    apply pvs_mono, exist_mono; auto with I.
  Qed.

  (** Weakest precondition *)
  Lemma wp_alloc N E γ e v P Q :
    to_val e = Some v → nclose N ⊆ E →
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (▷ ∀ l, heap_mapsto HeapI γ l v -★ Q (LocV l)) →
    P ⊑ wp E (Alloc e) Q.
  Proof.
    rewrite /heap_ctx /heap_inv /heap_mapsto=> ?? Hctx HP.
    transitivity (pvs E E (auth_own HeapI γ ∅ ★ P))%I.
    { by rewrite -pvs_frame_r -(auth_empty E γ) left_id. }
    apply wp_strip_pvs, (auth_fsa (heap_inv HeapI) (wp_fsa (Alloc e)))
      with N γ ∅; simpl; eauto with I.
    apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc left_id; apply const_elim_sep_l=> ?.
    rewrite {1}[(▷ownP _)%I]pvs_timeless pvs_frame_r; apply wp_strip_pvs.
    rewrite /wp_fsa -(wp_alloc_pst _ (of_heap h)) //.
    apply sep_mono_r; rewrite HP; apply later_mono.
    apply forall_intro=> l; apply wand_intro_l; rewrite (forall_elim l).
    rewrite always_and_sep_l -assoc; apply const_elim_sep_l=> ?.
    rewrite -(exist_intro (op {[ l ↦ Excl v ]})).
    repeat erewrite <-exist_intro by apply _; simpl.
    rewrite insert_of_heap left_id right_id !assoc.
    apply sep_mono_l.
    rewrite -(map_insert_singleton_op h); last by apply of_heap_None.
    rewrite const_equiv ?left_id; last by apply (map_insert_valid h).
    apply later_intro.
  Qed.

  Lemma wp_load N E γ l v P Q :
    nclose N ⊆ E →
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_mapsto HeapI γ l v ★ ▷ (heap_mapsto HeapI γ l v -★ Q v)) →
    P ⊑ wp E (Load (Loc l)) Q.
  Proof.
    rewrite /heap_ctx /heap_inv /heap_mapsto=>HN ? HPQ.
    apply (auth_fsa' (heap_inv HeapI) (wp_fsa _) id)
      with N γ {[ l ↦ Excl v ]}; simpl; eauto with I.
    rewrite HPQ{HPQ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc; apply const_elim_sep_l=> ?.
    rewrite {1}[(▷ownP _)%I]pvs_timeless pvs_frame_r; apply wp_strip_pvs.
    rewrite -(wp_load_pst _ (<[l:=v]>(of_heap h))) ?lookup_insert //.
    rewrite const_equiv // left_id.
    rewrite -(map_insert_singleton_op h); last by eapply heap_singleton_inv_l.
    rewrite insert_of_heap.
    apply sep_mono_r, later_mono, wand_intro_l. by rewrite -later_intro.
  Qed.

  Lemma wp_store N E γ l v' e v P Q :
    to_val e = Some v → nclose N ⊆ E → 
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_mapsto HeapI γ l v' ★
          ▷ (heap_mapsto HeapI γ l v -★ Q (LitV LitUnit))) →
    P ⊑ wp E (Store (Loc l) e) Q.
  Proof.
    rewrite /heap_ctx /heap_inv /heap_mapsto=>? HN ? HPQ.
    apply (auth_fsa' (heap_inv HeapI) (wp_fsa _) (alter (λ _, Excl v) l))
      with N γ {[ l ↦ Excl v' ]}; simpl; eauto with I.
    rewrite HPQ{HPQ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc; apply const_elim_sep_l=> ?.
    rewrite {1}[(▷ownP _)%I]pvs_timeless pvs_frame_r; apply wp_strip_pvs.
    rewrite -(wp_store_pst _ (<[l:=v']>(of_heap h))) ?lookup_insert //.
    rewrite /heap_inv alter_singleton insert_insert.
    rewrite -!(map_insert_singleton_op h); try by eapply heap_singleton_inv_l.
    rewrite !insert_of_heap const_equiv;
      last (split; [naive_solver|by eapply map_insert_valid, cmra_valid_op_r]).
    apply sep_mono_r, later_mono, wand_intro_l. by rewrite left_id -later_intro.
  Qed.

  Lemma wp_cas_fail N E γ l v' e1 v1 e2 v2 P Q :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 →
    nclose N ⊆ E →
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_mapsto HeapI γ l v' ★
          ▷ (heap_mapsto HeapI γ l v' -★ Q (LitV (LitBool false)))) →
    P ⊑ wp E (Cas (Loc l) e1 e2) Q.
  Proof.
    rewrite /heap_ctx /heap_inv /heap_mapsto=>??? HN ? HPQ.
    apply (auth_fsa' (heap_inv HeapI) (wp_fsa _) id)
      with N γ {[ l ↦ Excl v' ]}; simpl; eauto 10 with I.
    rewrite HPQ{HPQ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc; apply const_elim_sep_l=> ?.
    rewrite {1}[(▷ownP _)%I]pvs_timeless pvs_frame_r; apply wp_strip_pvs.
    rewrite -(wp_cas_fail_pst _ (<[l:=v']>(of_heap h))) ?lookup_insert //.
    rewrite const_equiv // left_id.
    rewrite -(map_insert_singleton_op h); last by eapply heap_singleton_inv_l.
    rewrite insert_of_heap.
    apply sep_mono_r, later_mono, wand_intro_l. by rewrite -later_intro.
  Qed.

  Lemma wp_cas_suc N E γ l e1 v1 e2 v2 P Q :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    nclose N ⊆ E →
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_mapsto HeapI γ l v1 ★
          ▷ (heap_mapsto HeapI γ l v2 -★ Q (LitV (LitBool true)))) →
    P ⊑ wp E (Cas (Loc l) e1 e2) Q.
  Proof.
    rewrite /heap_ctx /heap_inv /heap_mapsto=> ?? HN ? HPQ.
    apply (auth_fsa' (heap_inv HeapI) (wp_fsa _) (alter (λ _, Excl v2) l))
      with N γ {[ l ↦ Excl v1 ]}; simpl; eauto 10 with I.
    rewrite HPQ{HPQ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc; apply const_elim_sep_l=> ?.
    rewrite {1}[(▷ownP _)%I]pvs_timeless pvs_frame_r; apply wp_strip_pvs.
    rewrite -(wp_cas_suc_pst _ (<[l:=v1]>(of_heap h))) ?lookup_insert //.
    rewrite /heap_inv alter_singleton insert_insert.
    rewrite -!(map_insert_singleton_op h); try by eapply heap_singleton_inv_l.
    rewrite !insert_of_heap const_equiv;
      last (split; [naive_solver|by eapply map_insert_valid, cmra_valid_op_r]).
    apply sep_mono_r, later_mono, wand_intro_l. by rewrite left_id -later_intro.
  Qed.
End heap.
