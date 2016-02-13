From heap_lang Require Export derived.
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
Definition from_heap : heapRA → state := omap (maybe Excl).

Lemma from_to_heap σ : from_heap (to_heap σ) = σ.
Proof. apply map_eq=> l. rewrite lookup_omap lookup_fmap. by case (σ !! l). Qed.

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

  Global Instance heap_inv_proper : Proper ((≡) ==> (≡)) (heap_inv HeapI).
  Proof.
    move=>? ? EQ. rewrite /heap_inv /from_heap.
    (* TODO I guess we need some lemma about omap? *)
  Admitted. (* FIXME... I can't make progress otherwise... *)

  Lemma heap_own_op γ σ1 σ2 :
    (heap_own HeapI γ σ1 ★ heap_own HeapI γ σ2)%I
    ≡ (■ (σ1 ⊥ₘ σ2) ∧ heap_own HeapI γ (σ1 ∪ σ2))%I.
  Proof. (* TODO. *)
  Abort.

  Lemma heap_own_mapsto γ σ l v :
    (* TODO: Is this the best way to express "l ∉ dom σ"? *)
    (heap_own HeapI γ σ ★ heap_mapsto HeapI γ l v)%I
    ≡ (■ (σ !! l = None) ∧ heap_own HeapI γ (<[l:=v]>σ))%I.
  Proof. (* TODO. *)
  Abort.

  (* TODO: Prove equivalence to a big sum. *)

  Lemma heap_alloc N σ :
    ownP σ ⊑ pvs N N (∃ γ, heap_ctx HeapI γ N ∧ heap_own HeapI γ σ).
  Proof.
    rewrite -{1}[σ]from_to_heap.
    rewrite -(auth_alloc _ N); first done.
    move=>n l. rewrite lookup_fmap. by case _:(σ !! l)=>[v|] /=.
  Qed.

  Lemma wp_load_heap N E γ σ l v P Q :
    nclose N ⊆ E →
    σ !! l = Some v →
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_own HeapI γ σ ★ ▷ (heap_own HeapI γ σ -★ Q v)) →
    P ⊑ wp E (Load (Loc l)) Q.
  Proof.
    rewrite /heap_ctx /heap_own. intros HN Hl Hctx HP.
    eapply (auth_fsa (heap_inv HeapI) (wp_fsa (Load _) _) (λ _, True) id).
    { eassumption. } { eassumption. }
    rewrite HP=>{HP Hctx HN}. apply sep_mono; first done.
    apply forall_intro=>hf. apply wand_intro_l. rewrite /heap_inv.
    rewrite -assoc. apply const_elim_sep_l=>Hv /=.
    rewrite {1}[(▷ownP _)%I]pvs_timeless !pvs_frame_r. apply wp_strip_pvs.
    rewrite -wp_load_pst; first (apply sep_mono; first done); last first.
    { move: (Hv 0%nat l). rewrite lookup_omap lookup_op lookup_fmap Hl /=.
      case _:(hf !! l)=>[[v'||]|]; by auto. }
    apply later_mono, wand_intro_l. rewrite left_id const_equiv // left_id.
    by rewrite -later_intro.
  Unshelve.
  (* TODO Make it so that this becomes a goal, not shelved. *)
  { eexists. eauto. }
  Qed.

  Lemma wp_load N E γ l v P Q :
    nclose N ⊆ E →
    P ⊑ heap_ctx HeapI γ N →
    P ⊑ (heap_mapsto HeapI γ l v ★ ▷ (heap_mapsto HeapI γ l v -★ Q v)) →
    P ⊑ wp E (Load (Loc l)) Q.
  Proof.
    intros HN. rewrite /heap_mapsto. apply wp_load_heap; first done.
    by simplify_map_equality.
  Qed.
End heap.
