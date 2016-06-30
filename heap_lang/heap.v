From iris.heap_lang Require Export lifting.
From iris.algebra Require Import upred_big_op frac dec_agree.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
From iris.proofmode Require Import weakestpre.
Import uPred.
(* TODO: The entire construction could be generalized to arbitrary languages that have
   a finmap as their state. Or maybe even beyond "as their state", i.e. arbitrary
   predicates over finmaps instead of just ownP. *)

Definition heapUR : ucmraT := gmapUR loc (prodR fracR (dec_agreeR val)).

(** The CMRA we need. *)
Class heapG Σ := HeapG {
  heap_inG :> authG heap_lang Σ heapUR;
  heap_name : gname
}.
(** The Functor we need. *)
Definition heapGF : gFunctor := authGF heapUR.

Definition to_heap : state → heapUR := fmap (λ v, (1%Qp, DecAgree v)).
Definition of_heap : heapUR → state := omap (maybe DecAgree ∘ snd).

Section definitions.
  Context `{i : heapG Σ}.

  Definition heap_mapsto_def (l : loc) (q : Qp) (v: val) : iPropG heap_lang Σ :=
    auth_own heap_name {[ l := (q, DecAgree v) ]}.
  Definition heap_mapsto_aux : { x | x = @heap_mapsto_def }. by eexists. Qed.
  Definition heap_mapsto := proj1_sig heap_mapsto_aux.
  Definition heap_mapsto_eq : @heap_mapsto = @heap_mapsto_def :=
    proj2_sig heap_mapsto_aux.

  Definition heap_inv (h : heapUR) : iPropG heap_lang Σ :=
    ownP (of_heap h).
  Definition heap_ctx (N : namespace) : iPropG heap_lang Σ :=
    auth_ctx heap_name N heap_inv.

  Global Instance heap_inv_proper : Proper ((≡) ==> (⊣⊢)) heap_inv.
  Proof. solve_proper. Qed.
  Global Instance heap_ctx_persistent N : PersistentP (heap_ctx N).
  Proof. apply _. Qed.
End definitions.

Typeclasses Opaque heap_ctx heap_mapsto.
Instance: Params (@heap_inv) 1.
Instance: Params (@heap_mapsto) 4.
Instance: Params (@heap_ctx) 2.

Notation "l ↦{ q } v" := (heap_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : uPred_scope.

Section heap.
  Context {Σ : gFunctors}.
  Implicit Types N : namespace.
  Implicit Types P Q : iPropG heap_lang Σ.
  Implicit Types Φ : val → iPropG heap_lang Σ.
  Implicit Types σ : state.
  Implicit Types h g : heapUR.

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
    of_heap (<[l:=(1%Qp, DecAgree v)]> h) = <[l:=v]> (of_heap h).
  Proof. by rewrite /of_heap -(omap_insert _ _ _ (1%Qp, DecAgree v)). Qed.
  Lemma of_heap_singleton_op l q v h :
    ✓ ({[l := (q, DecAgree v)]} ⋅ h) →
    of_heap ({[l := (q, DecAgree v)]} ⋅ h) = <[l:=v]> (of_heap h).
  Proof.
    intros Hv. apply map_eq=> l'; destruct (decide (l' = l)) as [->|].
    - move: (Hv l). rewrite /of_heap lookup_insert
        lookup_omap (lookup_op _ h) lookup_singleton.
      case _:(h !! l)=>[[q' [v'|]]|] //=; last by move=> [??].
      move=> [? /dec_agree_op_inv [->]]. by rewrite dec_agree_idemp.
    - rewrite /of_heap lookup_insert_ne // !lookup_omap.
      by rewrite (lookup_op _ h) lookup_singleton_ne // left_id_L.
  Qed.
  Lemma to_heap_insert l v σ :
    to_heap (<[l:=v]> σ) = <[l:=(1%Qp, DecAgree v)]> (to_heap σ).
  Proof. by rewrite /to_heap -fmap_insert. Qed.
  Lemma of_heap_None h l : ✓ h → of_heap h !! l = None → h !! l = None.
  Proof.
    move=> /(_ l). rewrite /of_heap lookup_omap.
    by case: (h !! l)=> [[q [v|]]|] //=; destruct 1; auto.
  Qed.
  Lemma heap_store_valid l h v1 v2 :
    ✓ ({[l := (1%Qp, DecAgree v1)]} ⋅ h) →
    ✓ ({[l := (1%Qp, DecAgree v2)]} ⋅ h).
  Proof.
    intros Hv l'; move: (Hv l'). destruct (decide (l' = l)) as [->|].
    - rewrite !lookup_op !lookup_singleton.
      by case: (h !! l)=> [x|] // /Some_valid/exclusive_l.
    - by rewrite !lookup_op !lookup_singleton_ne.
  Qed.
  Hint Resolve heap_store_valid.

  (** Allocation *)
  Lemma heap_alloc N E σ :
    authG heap_lang Σ heapUR → nclose N ⊆ E →
    ownP σ ={E}=> ∃ _ : heapG Σ, heap_ctx N ∧ [★ map] l↦v ∈ σ, l ↦ v.
  Proof.
    intros. rewrite -{1}(from_to_heap σ). etrans.
    { rewrite [ownP _]later_intro.
      apply (auth_alloc (ownP ∘ of_heap) N E); auto using to_heap_valid. }
    apply pvs_mono, exist_elim=> γ.
    rewrite -(exist_intro (HeapG _ _ γ)) /heap_ctx; apply and_mono_r.
    rewrite heap_mapsto_eq /heap_mapsto_def /heap_name.
    induction σ as [|l v σ Hl IH] using map_ind.
    { rewrite big_sepM_empty; apply True_intro. }
    rewrite to_heap_insert big_sepM_insert //.
    rewrite (insert_singleton_op (to_heap σ));
      last by rewrite lookup_fmap Hl; auto.
    by rewrite auth_own_op IH.
  Qed.

  Context `{heapG Σ}.

  (** General properties of mapsto *)
  Global Instance heap_mapsto_timeless l q v : TimelessP (l ↦{q} v).
  Proof. rewrite heap_mapsto_eq /heap_mapsto_def. apply _. Qed.

  Lemma heap_mapsto_op_eq l q1 q2 v : l ↦{q1} v ★ l ↦{q2} v ⊣⊢ l ↦{q1+q2} v.
  Proof.
    by rewrite heap_mapsto_eq -auth_own_op op_singleton pair_op dec_agree_idemp.
  Qed.

  Lemma heap_mapsto_op l q1 q2 v1 v2 :
    l ↦{q1} v1 ★ l ↦{q2} v2 ⊣⊢ v1 = v2 ∧ l ↦{q1+q2} v1.
  Proof.
    destruct (decide (v1 = v2)) as [->|].
    { by rewrite heap_mapsto_op_eq pure_equiv // left_id. }
    rewrite heap_mapsto_eq -auth_own_op op_singleton pair_op dec_agree_ne //.
    apply (anti_symm (⊢)); last by apply pure_elim_l.
    rewrite auth_own_valid gmap_validI (forall_elim l) lookup_singleton.
    rewrite option_validI prod_validI frac_validI discrete_valid.
    by apply pure_elim_r.
  Qed.

  Lemma heap_mapsto_op_split l q v : l ↦{q} v ⊣⊢ (l ↦{q/2} v ★ l ↦{q/2} v).
  Proof. by rewrite heap_mapsto_op_eq Qp_div_2. Qed.

  (** Weakest precondition *)
  Lemma wp_alloc N E e v Φ :
    to_val e = Some v → nclose N ⊆ E →
    heap_ctx N ★ ▷ (∀ l, l ↦ v ={E}=★ Φ (LitV (LitLoc l))) ⊢ WP Alloc e @ E {{ Φ }}.
  Proof.
    iIntros {??} "[#Hinv HΦ]". rewrite /heap_ctx.
    iPvs (auth_empty heap_name) as "Hheap".
    iApply wp_pvs; iApply (auth_fsa heap_inv (wp_fsa _)); simpl; eauto.
    iFrame "Hinv Hheap". iIntros {h}. rewrite left_id.
    iIntros "[% Hheap]". rewrite /heap_inv.
    iApply wp_alloc_pst; first done. iFrame "Hheap". iNext.
    iIntros {l} "[% Hheap]"; iPvsIntro; iExists {[ l := (1%Qp, DecAgree v) ]}.
    rewrite -of_heap_insert -(insert_singleton_op h); last by apply of_heap_None.
    iFrame "Hheap". iSplitR; first iPureIntro.
    { by apply alloc_unit_singleton_local_update; first apply of_heap_None. }
    iIntros "Hheap". iApply "HΦ". by rewrite heap_mapsto_eq /heap_mapsto_def.
  Qed.

  Lemma wp_load N E l q v Φ :
    nclose N ⊆ E →
    heap_ctx N ★ ▷ l ↦{q} v ★ ▷ (l ↦{q} v ={E}=★ Φ v)
    ⊢ WP Load (Lit (LitLoc l)) @ E {{ Φ }}.
  Proof.
    iIntros {?} "[#Hh [Hl HΦ]]".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iApply wp_pvs; iApply (auth_fsa heap_inv (wp_fsa _)); simpl; eauto.
    iFrame "Hh Hl". iIntros {h} "[% Hl]". rewrite /heap_inv.
    iApply (wp_load_pst _ (<[l:=v]>(of_heap h)));first by rewrite lookup_insert.
    rewrite of_heap_singleton_op //. iFrame "Hl".
    iIntros "> Hown". iPvsIntro. iExists _; iSplit; first done.
    rewrite of_heap_singleton_op //. by iFrame.
  Qed.

  Lemma wp_store N E l v' e v Φ :
    to_val e = Some v → nclose N ⊆ E →
    heap_ctx N ★ ▷ l ↦ v' ★ ▷ (l ↦ v ={E}=★ Φ (LitV LitUnit))
    ⊢ WP Store (Lit (LitLoc l)) e @ E {{ Φ }}.
  Proof.
    iIntros {??} "[#Hh [Hl HΦ]]".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iApply wp_pvs; iApply (auth_fsa heap_inv (wp_fsa _)); simpl; eauto.
    iFrame "Hh Hl". iIntros {h} "[% Hl]". rewrite /heap_inv.
    iApply (wp_store_pst _ (<[l:=v']>(of_heap h))); rewrite ?lookup_insert //.
    rewrite insert_insert !of_heap_singleton_op; eauto. iFrame "Hl".
    iIntros "> Hown". iPvsIntro. iExists {[l := (1%Qp, DecAgree v)]}; iSplit.
    { iPureIntro; by apply singleton_local_update, exclusive_local_update. }
    rewrite of_heap_singleton_op //; eauto. by iFrame.
  Qed.

  Lemma wp_cas_fail N E l q v' e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 → nclose N ⊆ E →
    heap_ctx N ★ ▷ l ↦{q} v' ★ ▷ (l ↦{q} v' ={E}=★ Φ (LitV (LitBool false)))
    ⊢ WP CAS (Lit (LitLoc l)) e1 e2 @ E {{ Φ }}.
  Proof.
    iIntros {????} "[#Hh [Hl HΦ]]".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iApply wp_pvs; iApply (auth_fsa heap_inv (wp_fsa _)); simpl; eauto 10.
    iFrame "Hh Hl". iIntros {h} "[% Hl]". rewrite /heap_inv.
    iApply (wp_cas_fail_pst _ (<[l:=v']>(of_heap h))); rewrite ?lookup_insert //.
    rewrite of_heap_singleton_op //. iFrame "Hl".
    iIntros "> Hown". iPvsIntro. iExists _; iSplit; first done.
    rewrite of_heap_singleton_op //. by iFrame.
  Qed.

  Lemma wp_cas_suc N E l e1 v1 e2 v2 Φ :
    to_val e1 = Some v1 → to_val e2 = Some v2 → nclose N ⊆ E →
    heap_ctx N ★ ▷ l ↦ v1 ★ ▷ (l ↦ v2 ={E}=★ Φ (LitV (LitBool true)))
    ⊢ WP CAS (Lit (LitLoc l)) e1 e2 @ E {{ Φ }}.
  Proof.
    iIntros {???} "[#Hh [Hl HΦ]]".
    rewrite /heap_ctx heap_mapsto_eq /heap_mapsto_def.
    iApply wp_pvs; iApply (auth_fsa heap_inv (wp_fsa _)); simpl; eauto 10.
    iFrame "Hh Hl". iIntros {h} "[% Hl]". rewrite /heap_inv.
    iApply (wp_cas_suc_pst _ (<[l:=v1]>(of_heap h))); rewrite ?lookup_insert //.
    rewrite insert_insert !of_heap_singleton_op; eauto. iFrame "Hl".
    iIntros "> Hown". iPvsIntro. iExists {[l := (1%Qp, DecAgree v2)]}; iSplit.
    { iPureIntro; by apply singleton_local_update, exclusive_local_update. }
    rewrite of_heap_singleton_op //; eauto. by iFrame.
  Qed.
End heap.
