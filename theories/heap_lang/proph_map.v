From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Definition proph_map (P V : Type) `{Countable P} := gmap P (option V).
Definition proph_val_list (P V : Type) := list (P * V).

Section first_resolve.
  Context {P V : Type} `{Countable P}.
  Implicit Type pvs : proph_val_list P V.
  Implicit Type p : P.
  Implicit Type v : V.
  Implicit Type R : proph_map P V.

  (** The first resolve for [p] in [pvs] *)
  Definition first_resolve pvs p :=
    (map_of_list pvs : gmap P V) !! p.

  Definition first_resolve_in_list R pvs :=
    ∀ p v, p ∈ dom (gset _) R →
           first_resolve pvs p = Some v →
           R !! p = Some (Some v).

  Lemma first_resolve_insert pvs p R :
    first_resolve_in_list R pvs →
    p ∉ dom (gset _) R →
    first_resolve_in_list (<[p := first_resolve pvs p]> R) pvs.
  Proof.
    intros Hf Hnotin p' v' Hp'. rewrite (dom_insert_L R p) in Hp'.
    erewrite elem_of_union in Hp'. destruct Hp' as [->%elem_of_singleton | Hin] => [->].
    - by rewrite lookup_insert.
    - rewrite lookup_insert_ne; first auto. by intros ->.
  Qed.

  Lemma first_resolve_delete pvs p v R :
    first_resolve_in_list R ((p, v) :: pvs) →
    first_resolve_in_list (delete p R) pvs.
  Proof.
    intros Hfr p' v' Hpin Heq. rewrite dom_delete_L in Hpin. rewrite /first_resolve in Heq.
    apply elem_of_difference in Hpin as [Hpin Hne%not_elem_of_singleton].
    erewrite <- lookup_insert_ne in Heq; last done. rewrite lookup_delete_ne; eauto.
  Qed.

  Lemma first_resolve_eq R p v w pvs :
    first_resolve_in_list R ((p, v) :: pvs) →
    R !! p = Some w →
    w = Some v.
  Proof.
    intros Hfr Hlookup. specialize (Hfr p v (elem_of_dom_2 _ _ _ Hlookup)).
    rewrite /first_resolve lookup_insert in Hfr. rewrite Hfr in Hlookup; last done.
    inversion Hlookup. done.
  Qed.

End first_resolve.

Definition proph_mapUR (P V : Type) `{Countable P} : ucmraT :=
  gmapUR P $ exclR $ optionC $ leibnizC V.

Definition to_proph_map {P V} `{Countable P} (pvs : proph_map P V) : proph_mapUR P V :=
  fmap (λ v, Excl (v : option (leibnizC V))) pvs.

(** The CMRA we need. *)
Class proph_mapG (P V : Type) (Σ : gFunctors) `{Countable P} := ProphMapG {
  proph_map_inG :> inG Σ (authR (proph_mapUR P V));
  proph_map_name : gname
}.
Arguments proph_map_name {_ _ _ _ _} _ : assert.

Class proph_mapPreG (P V : Type) (Σ : gFunctors) `{Countable P} :=
  { proph_map_preG_inG :> inG Σ (authR (proph_mapUR P V)) }.

Definition proph_mapΣ (P V : Type) `{Countable P} : gFunctors :=
  #[GFunctor (authR (proph_mapUR P V))].

Instance subG_proph_mapPreG {Σ P V} `{Countable P} :
  subG (proph_mapΣ P V) Σ → proph_mapPreG P V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{pG : proph_mapG P V Σ}.

  Definition proph_map_auth (R : proph_map P V) : iProp Σ :=
    own (proph_map_name pG) (● (to_proph_map R)).

  Definition proph_map_ctx (pvs : proph_val_list P V) (ps : gset P) : iProp Σ :=
    (∃ R, ⌜first_resolve_in_list R pvs ∧
          dom (gset _) R ⊆ ps⌝ ∗
          proph_map_auth R)%I.

  Definition proph_mapsto_def (p : P) (v: option V) : iProp Σ :=
    own (proph_map_name pG) (◯ {[ p := Excl (v : option $ leibnizC V) ]}).
  Definition proph_mapsto_aux : seal (@proph_mapsto_def). by eexists. Qed.
  Definition proph_mapsto := proph_mapsto_aux.(unseal).
  Definition proph_mapsto_eq :
    @proph_mapsto = @proph_mapsto_def := proph_mapsto_aux.(seal_eq).

End definitions.

Local Notation "p ⥱ v" := (proph_mapsto p v) (at level 20, format "p ⥱ v") : bi_scope.
Local Notation "p ⥱ -" := (∃ v, p ⥱ v)%I (at level 20) : bi_scope.

Section to_proph_map.
  Context (P V : Type) `{Countable P}.
  Implicit Types p : P.
  Implicit Types R : proph_map P V.

  Lemma to_proph_map_valid R : ✓ to_proph_map R.
  Proof. intros l. rewrite lookup_fmap. by case (R !! l). Qed.

  Lemma to_proph_map_insert p v R :
    to_proph_map (<[p := v]> R) = <[p := Excl (v: option (leibnizC V))]> (to_proph_map R).
  Proof. by rewrite /to_proph_map fmap_insert. Qed.

  Lemma to_proph_map_delete p R :
    to_proph_map (delete p R) = delete p (to_proph_map R).
  Proof. by rewrite /to_proph_map fmap_delete. Qed.

  Lemma lookup_to_proph_map_None R p :
    R !! p = None → to_proph_map R !! p = None.
  Proof. by rewrite /to_proph_map lookup_fmap=> ->. Qed.

  Lemma proph_map_singleton_included R p v :
    {[p := Excl v]} ≼ to_proph_map R → R !! p = Some v.
  Proof.
    rewrite singleton_included=> -[v' []].
    rewrite /to_proph_map lookup_fmap fmap_Some_equiv=> -[v'' [Hp ->]].
    intros [=->]%Some_included_exclusive%leibniz_equiv_iff; first done; last done.
    apply excl_exclusive.
  Qed.
End to_proph_map.


Lemma proph_map_init `{proph_mapPreG P V PVS} pvs ps :
  (|==> ∃ _ : proph_mapG P V PVS, proph_map_ctx pvs ps)%I.
Proof.
  iMod (own_alloc (● to_proph_map ∅)) as (γ) "Hh".
  { apply: auth_auth_valid. exact: to_proph_map_valid. }
  iModIntro. iExists (ProphMapG P V PVS _ _ _ γ), ∅. iSplit; last by iFrame.
  iPureIntro. split =>//.
Qed.

Section proph_map.
  Context `{proph_mapG P V Σ}.
  Implicit Types p : P.
  Implicit Types v : option V.
  Implicit Types R : proph_map P V.

  (** General properties of mapsto *)
  Global Instance p_mapsto_timeless p v : Timeless (p ⥱ v).
  Proof. rewrite proph_mapsto_eq /proph_mapsto_def. apply _. Qed.

  Lemma proph_map_alloc R p v :
    p ∉ dom (gset _) R →
    proph_map_auth R ==∗ proph_map_auth (<[p := v]> R) ∗ p ⥱ v.
  Proof.
    iIntros (Hp) "HR". rewrite /proph_map_ctx proph_mapsto_eq /proph_mapsto_def.
    iMod (own_update with "HR") as "[HR Hl]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ _ (Excl $ (v : option (leibnizC _))))=> //.
      apply lookup_to_proph_map_None. apply (iffLR (not_elem_of_dom _ _) Hp). }
    iModIntro. rewrite /proph_map_auth to_proph_map_insert. iFrame.
  Qed.

  Lemma proph_map_remove R p v :
    proph_map_auth R -∗ p ⥱ v ==∗ proph_map_auth (delete p R).
  Proof.
    iIntros "HR Hp". rewrite /proph_map_ctx proph_mapsto_eq /proph_mapsto_def.
    rewrite /proph_map_auth to_proph_map_delete. iApply (own_update_2 with "HR Hp").
    apply auth_update_dealloc, (delete_singleton_local_update _ _ _).
  Qed.

  Lemma proph_map_valid R p v : proph_map_auth R -∗ p ⥱ v -∗ ⌜R !! p = Some v⌝.
  Proof.
    iIntros "HR Hp". rewrite /proph_map_ctx proph_mapsto_eq /proph_mapsto_def.
    iDestruct (own_valid_2 with "HR Hp")
      as %[HH%proph_map_singleton_included _]%auth_valid_discrete_2; auto.
  Qed.
End proph_map.
