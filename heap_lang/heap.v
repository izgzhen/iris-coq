From heap_lang Require Export derived.
From program_logic Require Import ownership auth.
From heap_lang Require Import notation.
Import uPred.
(* TODO: The entire construction could be generalized to arbitrary languages that have
   a finmap as their state. Or maybe even beyond "as their state", i.e. arbitrary
   predicates over finmaps instead of just ownP. *)

Definition heapRA := mapRA loc (exclRA (leibnizC val)).

Class HeapInG Σ (i : gid) := heap_inG :> InG heap_lang Σ i (authRA heapRA).
Instance heap_inG_auth `{HeapInG Σ i} : AuthInG heap_lang Σ i heapRA.
Proof. split; apply _. Qed.

Definition to_heap : state → heapRA := fmap Excl.
Definition from_heap : heapRA → state := omap (maybe Excl).

(* TODO: Do we want to expose heap ownership based on the state, or the heapRA?
   The former does not expose the annoying "Excl", so for now I am going for
   that. We should be able to derive the lemmas we want for this, too. *)
Definition heap_own {Σ} (i : gid) `{HeapInG Σ i}
  (γ : gname) (σ : state) : iPropG heap_lang Σ := auth_own i γ (to_heap σ).
Definition heap_mapsto {Σ} (i : gid) `{HeapInG Σ i}
  (γ : gname) (l : loc) (v : val) : iPropG heap_lang Σ := heap_own i γ {[ l ↦ v ]}.
Definition heap_inv {Σ} (i : gid) `{HeapInG Σ i}
  (h : heapRA) : iPropG heap_lang Σ := ownP (from_heap h).
Definition heap_ctx {Σ} (i : gid) `{HeapInG Σ i}
  (γ : gname) (N : namespace) : iPropG heap_lang Σ := auth_ctx i γ N (heap_inv i).

Section heap.
  Context {Σ : iFunctorG} (HeapI : gid) `{!HeapInG Σ HeapI}.
  Implicit Types N : namespace.
  Implicit Types P : iPropG heap_lang Σ.
  Implicit Types σ : state.
  Implicit Types h g : heapRA.
  Implicit Types γ : gname.

  Lemma from_to_heap σ : from_heap (to_heap σ) = σ.
  Proof.
    apply map_eq=>l. rewrite lookup_omap lookup_fmap. by case (σ !! l).
  Qed.
  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros n l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Hint Resolve to_heap_valid.

  Global Instance heap_inv_proper : Proper ((≡) ==> (≡)) (heap_inv HeapI).
  Proof. intros h1 h2. by fold_leibniz=> ->. Qed.

  Lemma heap_own_op γ σ1 σ2 :
    (heap_own HeapI γ σ1 ★ heap_own HeapI γ σ2)%I
    ≡ (■ (σ1 ⊥ₘ σ2) ∧ heap_own HeapI γ (σ1 ∪ σ2))%I.
  Proof.
 (* TODO. *)
  Abort.

  Lemma heap_own_mapsto γ σ l v :
    (* TODO: Is this the best way to express "l ∉ dom σ"? *)
    (heap_own HeapI γ σ ★ heap_mapsto HeapI γ l v)%I
    ≡ (■ (σ !! l = None) ∧ heap_own HeapI γ (<[l:=v]>σ))%I.
  Proof. (* TODO. *)
  Abort.

  (* TODO: Do we want equivalence to a big sum? *)

  Lemma heap_alloc N σ :
    ownP σ ⊑ pvs N N (∃ γ, heap_ctx HeapI γ N ∧ heap_own HeapI γ σ).
  Proof. by rewrite -{1}[σ]from_to_heap -(auth_alloc _ N). Qed.

  Lemma wp_alloc_heap N E γ σ e v P Q :
    nclose N ⊆ E →  to_val e = Some v →
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_own HeapI γ σ ★
         ▷ (∀ l, σ !! l = None ∧ heap_own HeapI γ (<[l:=v]>σ) -★ Q (LocV l))) →
    P ⊑ wp E (Alloc e) Q.
  Proof.
    rewrite /heap_ctx /heap_own. intros HN Hval Hctx HP.
    set (LU (l : loc) := local_update_op (A:=heapRA) ({[ l ↦ Excl v ]})).
    eapply (auth_fsa (heap_inv HeapI) (wp_fsa _) _ (LU := LU)); simpl.
    { by eauto. } { by eauto. } { by eauto. }
    rewrite HP=>{HP Hctx HN}. apply sep_mono; first done.
    apply forall_intro=>hf. apply wand_intro_l. rewrite /heap_inv.
    rewrite -assoc. apply const_elim_sep_l=>Hv /=.
    rewrite {1}[(▷ownP _)%I]pvs_timeless !pvs_frame_r. apply wp_strip_pvs.
    rewrite -wp_alloc_pst; first (apply sep_mono; first done); try eassumption.
    apply later_mono, forall_intro=>l. rewrite (forall_elim l). apply wand_intro_l.
    rewrite -(exist_intro l) !left_id. rewrite always_and_sep_l -assoc.
    apply const_elim_sep_l=>Hfresh.
    assert (σ !! l = None) as Hfresh_σ.
    { move: Hfresh (Hv 0%nat l). rewrite /from_heap /to_heap lookup_omap.
      rewrite lookup_op !lookup_fmap.
      case _:(σ !! l)=>[v'|]/=; case _:(hf !! l)=>[[?||]|]/=; done. }
    rewrite const_equiv // const_equiv; last first.
    { move=>n l'. move:(Hv n l') Hfresh.
      rewrite /from_heap /to_heap !lookup_omap !lookup_op !lookup_fmap !Hfresh_σ /=.
      destruct (decide (l=l')).
      - subst l'. rewrite lookup_singleton !Hfresh_σ.
        case _:(hf !! l)=>[[?||]|]/=; done.
      - rewrite lookup_singleton_ne //.
        case _:(σ !! l')=>[?|]/=; case _:(hf !! l')=>[[?||]|]/=; done. }
    rewrite !left_id -later_intro.
    assert ({[l ↦ Excl v]} ⋅ to_heap σ = to_heap (<[l:=v]> σ)) as EQ.
    { apply: map_eq=>l'. rewrite lookup_op !lookup_fmap.
      destruct (decide (l=l')); simplify_map_equality.
      - rewrite lookup_insert. done.
      - rewrite !lookup_insert_ne // lookup_empty left_id. done. }
    rewrite EQ. apply sep_mono; last done. f_equiv. apply: map_eq=>l'. 
    move:(Hv 0%nat l') Hfresh. destruct (decide (l=l')); simplify_map_equality.
    - rewrite lookup_insert !lookup_omap !lookup_op !lookup_fmap lookup_insert.
      case _:(σ !! l')=>[?|]/=; case _:(hf !! l')=>[[?||]|]/=; done.
    - rewrite lookup_insert_ne // !lookup_omap !lookup_op !lookup_fmap lookup_insert_ne //.
  Qed.

  Lemma wp_load_heap N E γ σ l v P Q :
    σ !! l = Some v →
    nclose N ⊆ E →
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_own HeapI γ σ ★ ▷ (heap_own HeapI γ σ -★ Q v)) →
    P ⊑ wp E (Load (Loc l)) Q.
  Proof.
    rewrite /heap_ctx /heap_own. intros Hl HN Hctx HP.
    eapply (auth_fsa (heap_inv HeapI) (wp_fsa _) (λ _:(), id)); simpl; eauto.
    rewrite HP=>{HP Hctx HN}. apply sep_mono; first done.
    apply forall_intro=>hf. apply wand_intro_l. rewrite /heap_inv.
    rewrite -assoc. apply const_elim_sep_l=>Hv /=.
    rewrite {1}[(▷ownP _)%I]pvs_timeless !pvs_frame_r. apply wp_strip_pvs.
    rewrite -wp_load_pst; first (apply sep_mono; first done); last first.
    { move: (Hv 0%nat l). rewrite lookup_omap lookup_op lookup_fmap Hl /=.
      case _:(hf !! l)=>[[?||]|]; by auto. }
    apply later_mono, wand_intro_l.
    rewrite -(exist_intro ()) left_id const_equiv // left_id.
    by rewrite -later_intro.
  Qed.

  Lemma wp_load N E γ l v P Q :
    nclose N ⊆ E →
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_mapsto HeapI γ l v ★ ▷ (heap_mapsto HeapI γ l v -★ Q v)) →
    P ⊑ wp E (Load (Loc l)) Q.
  Proof.
    intros HN. rewrite /heap_mapsto. apply wp_load_heap; last done.
    by simplify_map_equality.
  Qed.

  Lemma wp_store_heap N E γ σ l v' e v P Q :
    σ !! l = Some v' → to_val e = Some v → 
    nclose N ⊆ E →
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_own HeapI γ σ ★ ▷ (heap_own HeapI γ (<[l:=v]>σ) -★ Q (LitV LitUnit))) →
    P ⊑ wp E (Store (Loc l) e) Q.
  Proof.
    rewrite /heap_ctx /heap_own. intros Hl Hval HN Hctx HP.
    eapply (auth_fsa (heap_inv HeapI) (wp_fsa _) (λ _:(), alter (λ _, Excl v) l)); simpl; eauto.
    rewrite HP=>{HP Hctx HN}. apply sep_mono; first done.
    apply forall_intro=>hf. apply wand_intro_l. rewrite /heap_inv.
    rewrite -assoc. apply const_elim_sep_l=>Hv /=.
    rewrite {1}[(▷ownP _)%I]pvs_timeless !pvs_frame_r. apply wp_strip_pvs.
    rewrite -wp_store_pst; first (apply sep_mono; first done); try eassumption; last first.
    { move: (Hv 0%nat l). rewrite lookup_omap lookup_op lookup_fmap Hl /=.
      case _:(hf !! l)=>[[?||]|]; by auto. }
    apply later_mono, wand_intro_l.
    rewrite -(exist_intro ()) const_equiv //; last first.
    (* TODO I think there are some general fin_map lemmas hiding in here. *)
    { split.
      - exists (Excl v'). by rewrite lookup_fmap Hl.
      - move=>n l'. move: (Hv n l'). rewrite !lookup_op.
        destruct (decide (l=l')); simplify_map_equality.
        + rewrite lookup_alter lookup_fmap Hl /=. case (hf !! l')=>[[?||]|]; by auto.
        + rewrite lookup_alter_ne //. }
    rewrite left_id -later_intro.
    assert (alter (λ _ : excl val, Excl v) l (to_heap σ) = to_heap (<[l:=v]> σ)) as EQ.
    { apply: map_eq=>l'. destruct (decide (l=l')); simplify_map_equality.
      + by rewrite lookup_alter /to_heap !lookup_fmap lookup_insert Hl /=.
      + rewrite lookup_alter_ne // !lookup_fmap lookup_insert_ne //. }
    rewrite !EQ. apply sep_mono; last done.
    f_equiv. apply: map_eq=>l'. move: (Hv 0%nat l'). destruct (decide (l=l')); simplify_map_equality.
    - rewrite /from_heap /to_heap lookup_insert lookup_omap !lookup_op.
      rewrite !lookup_fmap lookup_insert Hl.
      case (hf !! l')=>[[?||]|]; auto; contradiction.
    - rewrite /from_heap /to_heap lookup_insert_ne // !lookup_omap !lookup_op !lookup_fmap.
      rewrite lookup_insert_ne //.
  Qed.

  Lemma wp_store N E γ l v' e v P Q :
    to_val e = Some v → 
    nclose N ⊆ E → 
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_mapsto HeapI γ l v' ★ ▷ (heap_mapsto HeapI γ l v -★ Q (LitV LitUnit))) →
    P ⊑ wp E (Store (Loc l) e) Q.
  Proof.
    rewrite /heap_mapsto=>Hval HN Hctx HP. eapply wp_store_heap; try eassumption; last first.
    - rewrite HP. apply sep_mono; first done. by rewrite insert_singleton.
    - by rewrite lookup_insert.
  Qed.

  Lemma wp_cas_fail_heap N E γ σ l v' e1 v1 e2 v2 P Q :
    to_val e1 = Some v1 → to_val e2 = Some v2 → σ !! l = Some v' → v' ≠ v1 →
    nclose N ⊆ E →
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_own HeapI γ σ ★ ▷ (heap_own HeapI γ σ -★ Q 'false)) →
    P ⊑ wp E (Cas (Loc l) e1 e2) Q.
  Proof.
    rewrite /heap_ctx /heap_own. intros He1 He2 Hl Hne HN Hctx HP.
    eapply (auth_fsa (heap_inv HeapI) (wp_fsa _) (λ _:(), id)); simpl; eauto.
    { split_ands; eexists; eauto. }
    rewrite HP=>{HP Hctx HN}. apply sep_mono; first done.
    apply forall_intro=>hf. apply wand_intro_l. rewrite /heap_inv.
    rewrite -assoc. apply const_elim_sep_l=>Hv /=.
    rewrite {1}[(▷ownP _)%I]pvs_timeless !pvs_frame_r. apply wp_strip_pvs.
    rewrite -wp_cas_fail_pst; first (apply sep_mono; first done); try eassumption; last first.
    { move: (Hv 0%nat l). rewrite lookup_omap lookup_op lookup_fmap Hl /=.
      case _:(hf !! l)=>[[?||]|]; by auto. }
    apply later_mono, wand_intro_l.
    rewrite -(exist_intro ()) left_id const_equiv // left_id.
    by rewrite -later_intro.
  Qed.

  Lemma wp_cas_fail N E γ l v' e1 v1 e2 v2 P Q :
    to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 →
    nclose N ⊆ E →
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_mapsto HeapI γ l v' ★ ▷ (heap_mapsto HeapI γ l v' -★ Q 'false)) →
    P ⊑ wp E (Cas (Loc l) e1 e2) Q.
  Proof.
    rewrite /heap_mapsto=>???. eapply wp_cas_fail_heap; try eassumption.
    by simplify_map_equality.
  Qed.
End heap.
