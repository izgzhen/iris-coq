From heap_lang Require Export lifting.
From algebra Require Import upred_big_op.
From program_logic Require Export invariants ghost_ownership.
From program_logic Require Import ownership auth.
Import uPred.
(* TODO: The entire construction could be generalized to arbitrary languages that have
   a finmap as their state. Or maybe even beyond "as their state", i.e. arbitrary
   predicates over finmaps instead of just ownP. *)

Definition heapRA : cmraT := mapRA loc (exclRA (leibnizC val)).
Definition heapGF : iFunctor := authGF heapRA.

Class heapG Σ := HeapG {
  heap_inG : inG heap_lang Σ (authRA heapRA);
  heap_name : gname
}.
Instance heap_authG `{i : heapG Σ} : authG heap_lang Σ heapRA :=
  {| auth_inG := heap_inG |}.

Definition to_heap : state → heapRA := fmap Excl.
Definition of_heap : heapRA → state := omap (maybe Excl).

(* heap_mapsto is defined strongly opaquely, to prevent unification from
matching it against other forms of ownership. *)
Definition heap_mapsto_def `{heapG Σ} (l : loc) (v: val) : iPropG heap_lang Σ :=
  auth_own heap_name {[ l := Excl v ]}.
(* Perform sealing *)
Module Type HeapMapstoSig.
  Parameter heap_mapsto : ∀ `{heapG Σ} (l : loc) (v: val), iPropG heap_lang Σ.
  Axiom heap_mapsto_eq : @heap_mapsto = @heap_mapsto_def.
End HeapMapstoSig.
Module Export HeapMapsto : HeapMapstoSig.
  Definition heap_mapsto := @heap_mapsto_def.
  Definition heap_mapsto_eq := Logic.eq_refl (@heap_mapsto).
End HeapMapsto. 

Definition heap_inv `{i : heapG Σ} (h : heapRA) : iPropG heap_lang Σ :=
  ownP (of_heap h).
Definition heap_ctx `{i : heapG Σ} (N : namespace) : iPropG heap_lang Σ :=
  auth_ctx heap_name N heap_inv.

Notation "l ↦ v" := (heap_mapsto l v) (at level 20) : uPred_scope.

Section heap.
  Context {Σ : iFunctorG}.
  Implicit Types N : namespace.
  Implicit Types P Q : iPropG heap_lang Σ.
  Implicit Types Φ : val → iPropG heap_lang Σ.
  Implicit Types σ : state.
  Implicit Types h g : heapRA.

  (** Conversion to heaps and back *)
  Global Instance of_heap_proper : Proper ((≡) ==> (=)) of_heap.
  Proof. by intros ??; fold_leibniz=>->. Qed.
  Lemma from_to_heap σ : of_heap (to_heap σ) = σ.
  Proof.
    apply map_eq=>l. rewrite lookup_omap lookup_fmap. by case (σ !! l).
  Qed.
  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros n l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Lemma of_heap_insert l v h : of_heap (<[l:=Excl v]> h) = <[l:=v]> (of_heap h).
  Proof. by rewrite /of_heap -(omap_insert _ _ _ (Excl v)). Qed.
  Lemma to_heap_insert l v σ : to_heap (<[l:=v]> σ) = <[l:=Excl v]> (to_heap σ).
  Proof. by rewrite /to_heap -fmap_insert. Qed.
  Lemma of_heap_None h l :
    ✓ h → of_heap h !! l = None → h !! l = None ∨ h !! l ≡ Some ExclUnit.
  Proof.
    move=> /(_ O l). rewrite /of_heap lookup_omap.
    by case: (h !! l)=> [[]|]; auto.
  Qed.
  Lemma heap_singleton_inv_l h l v :
    ✓ ({[l := Excl v]} ⋅ h) → h !! l = None ∨ h !! l ≡ Some ExclUnit.
  Proof.
    move=> /(_ O l). rewrite lookup_op lookup_singleton.
    by case: (h !! l)=> [[]|]; auto.
  Qed.

  (** Allocation *)
  Lemma heap_alloc E N σ :
    authG heap_lang Σ heapRA → nclose N ⊆ E →
    ownP σ ⊑ (|={E}=> ∃ _ : heapG Σ, heap_ctx N ∧ Π★{map σ} heap_mapsto).
  Proof.
    intros. rewrite heap_mapsto_eq -{1}(from_to_heap σ). etrans.
    { rewrite [ownP _]later_intro.
      apply (auth_alloc (ownP ∘ of_heap) E N (to_heap σ)); last done.
      apply to_heap_valid. }
    apply pvs_mono, exist_elim=> γ.
    rewrite -(exist_intro (HeapG _ _ γ)); apply and_mono_r.
    induction σ as [|l v σ Hl IH] using map_ind.
    { rewrite big_sepM_empty; apply True_intro. }
    rewrite to_heap_insert big_sepM_insert //.
    rewrite (map_insert_singleton_op (to_heap σ));
      last rewrite lookup_fmap Hl; auto.
    by rewrite auth_own_op IH.
  Qed.

  Context `{heapG Σ}.

  (** Propers *)
  Global Instance heap_inv_proper : Proper ((≡) ==> (≡)) heap_inv.
  Proof. intros h1 h2. by fold_leibniz=> ->. Qed.

  (** General properties of mapsto *)
  Lemma heap_mapsto_disjoint l v1 v2 : (l ↦ v1 ★ l ↦ v2)%I ⊑ False.
  Proof.
    rewrite heap_mapsto_eq -auth_own_op auth_own_valid map_op_singleton.
    rewrite map_validI (forall_elim l) lookup_singleton.
    by rewrite option_validI excl_validI.
  Qed.

  (** Weakest precondition *)
  Lemma wp_alloc N E e v P Φ :
    to_val e = Some v → nclose N ⊆ E →
    P ⊑ heap_ctx N →
    P ⊑ (▷ ∀ l, l ↦ v -★ Φ (LocV l)) →
    P ⊑ || Alloc e @ E {{ Φ }}.
  Proof.
    rewrite /heap_ctx /heap_inv heap_mapsto_eq=> ?? Hctx HP.
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
    rewrite -(exist_intro (op {[ l := Excl v ]})).
    repeat erewrite <-exist_intro by apply _; simpl.
    rewrite -of_heap_insert left_id right_id.
    ecancel [_ -★ Φ _]%I.
    rewrite -(map_insert_singleton_op h); last by apply of_heap_None.
    rewrite const_equiv ?left_id; last by apply (map_insert_valid h).
    apply later_intro.
  Qed.

  Lemma wp_load N E l v P Φ :
    nclose N ⊆ E →
    P ⊑ heap_ctx N →
    P ⊑ (▷ l ↦ v ★ ▷ (l ↦ v -★ Φ v)) →
    P ⊑ || Load (Loc l) @ E {{ Φ }}.
  Proof.
    rewrite /heap_ctx /heap_inv heap_mapsto_eq=>HN ? HPΦ.
    apply (auth_fsa' heap_inv (wp_fsa _) id)
      with N heap_name {[ l := Excl v ]}; simpl; eauto with I.
    rewrite HPΦ{HPΦ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc; apply const_elim_sep_l=> ?.
    rewrite -(wp_load_pst _ (<[l:=v]>(of_heap h))) ?lookup_insert //.
    rewrite const_equiv // left_id.
    rewrite -(map_insert_singleton_op h); last by eapply heap_singleton_inv_l.
    rewrite -of_heap_insert.
    apply sep_mono_r, later_mono, wand_intro_l. by rewrite -later_intro.
  Qed.

  Lemma wp_store N E l v' e v P Φ :
    to_val e = Some v → nclose N ⊆ E → 
    P ⊑ heap_ctx N →
    P ⊑ (▷ l ↦ v' ★ ▷ (l ↦ v -★ Φ (LitV LitUnit))) →
    P ⊑ || Store (Loc l) e @ E {{ Φ }}.
  Proof.
    rewrite /heap_ctx /heap_inv heap_mapsto_eq=>? HN ? HPΦ.
    apply (auth_fsa' heap_inv (wp_fsa _) (alter (λ _, Excl v) l))
      with N heap_name {[ l := Excl v' ]}; simpl; eauto with I.
    rewrite HPΦ{HPΦ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc; apply const_elim_sep_l=> ?.
    rewrite -(wp_store_pst _ (<[l:=v']>(of_heap h))) ?lookup_insert //.
    rewrite /heap_inv alter_singleton insert_insert.
    rewrite -!(map_insert_singleton_op h); try by eapply heap_singleton_inv_l.
    rewrite -!of_heap_insert const_equiv;
      last (split; [naive_solver|by eapply map_insert_valid, cmra_valid_op_r]).
    apply sep_mono_r, later_mono, wand_intro_l. by rewrite left_id -later_intro.
  Qed.

  Lemma wp_cas_fail N E l v' e1 v1 e2 v2 P Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 →
    nclose N ⊆ E →
    P ⊑ heap_ctx N →
    P ⊑ (▷ l ↦ v' ★ ▷ (l ↦ v' -★ Φ (LitV (LitBool false)))) →
    P ⊑ || Cas (Loc l) e1 e2 @ E {{ Φ }}.
  Proof.
    rewrite /heap_ctx /heap_inv heap_mapsto_eq=>??? HN ? HPΦ.
    apply (auth_fsa' heap_inv (wp_fsa _) id)
      with N heap_name {[ l := Excl v' ]}; simpl; eauto 10 with I.
    rewrite HPΦ{HPΦ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc; apply const_elim_sep_l=> ?.
    rewrite -(wp_cas_fail_pst _ (<[l:=v']>(of_heap h))) ?lookup_insert //.
    rewrite const_equiv // left_id.
    rewrite -(map_insert_singleton_op h); last by eapply heap_singleton_inv_l.
    rewrite -of_heap_insert.
    apply sep_mono_r, later_mono, wand_intro_l. by rewrite -later_intro.
  Qed.

  Lemma wp_cas_suc N E l e1 v1 e2 v2 P Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    nclose N ⊆ E →
    P ⊑ heap_ctx N →
    P ⊑ (▷ l ↦ v1 ★ ▷ (l ↦ v2 -★ Φ (LitV (LitBool true)))) →
    P ⊑ || Cas (Loc l) e1 e2 @ E {{ Φ }}.
  Proof.
    rewrite /heap_ctx /heap_inv heap_mapsto_eq=> ?? HN ? HPΦ.
    apply (auth_fsa' heap_inv (wp_fsa _) (alter (λ _, Excl v2) l))
      with N heap_name {[ l := Excl v1 ]}; simpl; eauto 10 with I.
    rewrite HPΦ{HPΦ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
    rewrite -assoc; apply const_elim_sep_l=> ?.
    rewrite -(wp_cas_suc_pst _ (<[l:=v1]>(of_heap h))) ?lookup_insert //.
    rewrite /heap_inv alter_singleton insert_insert.
    rewrite -!(map_insert_singleton_op h); try by eapply heap_singleton_inv_l.
    rewrite -!of_heap_insert const_equiv;
      last (split; [naive_solver|by eapply map_insert_valid, cmra_valid_op_r]).
    apply sep_mono_r, later_mono, wand_intro_l. by rewrite left_id -later_intro.
  Qed.
End heap.
