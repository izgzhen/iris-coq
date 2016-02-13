From heap_lang Require Export derived.
From program_logic Require Import ownership auth.
Import uPred.

(* TODO: The entire construction could be generalized to arbitrary languages that have
   a finmap as their state. Or maybe even beyond "as their state", i.e. arbitrary
   predicates over finmaps instead of just ownP. *)
Section heap.
  Definition heapRA := mapRA loc (exclRA (leibnizC val)).
  Context {Σ : iFunctorG} (HeapI : gid) `{!InG heap_lang Σ HeapI (authRA heapRA)}.
  Context (N : namespace).

  Implicit Types P : iPropG heap_lang Σ.
  Implicit Types σ : state.
  Implicit Types h g : heapRA.
  Implicit Types γ : gname.

  Local Instance heap_auth : AuthInG heap_lang Σ HeapI heapRA.
  Proof. split; intros; apply _. Qed.

  Notation to_heap σ := (Excl <$> σ).
  Definition from_heap : heapRA → state :=
    omap (λ e, if e is Excl v then Some v else None).

  Lemma from_to_heap σ : from_heap (to_heap σ) = σ.
  Proof.
    apply map_eq=>l. rewrite lookup_omap lookup_fmap.
    (* FIXME RJ: To do case-analysis on σ !! l, I need to do this weird
       "case _: ...". Neither destruct nor plain case work, I need the
       one that generates an equality - but I do not need the equality.
       This also happened in algebra/fin_maps.v. *)
    by case _:(σ !! l)=>[v|] /=.
  Qed.

  (* TODO: Do we want to expose heap ownership based on the state, or the heapRA?
     The former does not expose the annoying "Excl", so for now I am going for
     that. We should be able to derive the lemmas we want for this, too. *)
  Definition heap_own (γ : gname) (σ : state) : iPropG heap_lang Σ :=
    auth_own HeapI γ (to_heap σ).
  Definition heap_mapsto (γ : gname) (l : loc) (v : val) : iPropG heap_lang Σ :=
    heap_own γ {[ l ↦ v ]}.
  Definition heap_inv (h : heapRA) : iPropG heap_lang Σ :=
    ownP (from_heap h).
  Definition heap_ctx (γ : gname) : iPropG heap_lang Σ :=
    auth_ctx HeapI γ N heap_inv.

  Global Instance heap_inv_ne : Proper ((≡) ==> (≡)) heap_inv.
  Proof.
    move=>? ? EQ. rewrite /heap_inv /from_heap.
    (* TODO I guess we need some lemma about omap? *)
  Admitted. (* FIXME... I can't make progress otherwise... *)

  Lemma heap_own_op γ σ1 σ2 :
    (heap_own γ σ1 ★ heap_own γ σ2)%I ≡ (■(σ1 ⊥ₘ σ2) ∧ heap_own γ (σ1 ∪ σ2))%I.
  Proof. (* TODO. *)
  Abort.

  Lemma heap_own_mapsto γ σ l v :
    (* TODO: Is this the best way to express "l ∉ dom σ"? *)
    (heap_own γ σ ★ heap_mapsto γ l v)%I ≡ (■(σ !! l = None) ∧ heap_own γ (<[l:=v]>σ))%I.
  Proof. (* TODO. *)
  Abort.

  (* TODO: Prove equivalence to a big sum. *)

  Lemma heap_alloc σ :
    ownP σ ⊑ pvs N N (∃ γ, heap_ctx γ ∧ heap_own γ σ).
  Proof.
    rewrite -{1}[σ]from_to_heap.
    rewrite -(auth_alloc heap_inv N); first done.
    move=>n l. rewrite lookup_fmap. by case _:(σ !! l)=>[v|] /=.
  Qed.

  Lemma wp_load_heap E γ σ l v P Q :
    nclose N ⊆ E →
    σ !! l = Some v →
    P ⊑ heap_ctx γ →
    P ⊑ (heap_own γ σ ★ ▷ (heap_own γ σ -★ Q v)) →
    P ⊑ wp E (Load (Loc l)) Q.
  Proof.
    rewrite /heap_ctx /heap_own. intros HN Hl Hctx HP.
    eapply (auth_fsa heap_inv (wp_fsa (Load _) _) (λ _, True) id).
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
  { eexists. eauto. }
  { split; first by apply _. done. }
  Qed.

End heap.
