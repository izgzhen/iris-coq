From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Import auth saved_prop.
From iris.proofmode Require Import tactics invariants ghost_ownership.
Import uPred.

(** The CMRAs we need. *)
Class boxG Λ Σ :=
  boxG_inG :> inG Λ Σ (prodR
    (authR (optionUR (exclR boolC)))
    (optionR (agreeR (laterC (iPrePropG Λ Σ))))).

Section box_defs.
  Context `{boxG Λ Σ} (N : namespace).
  Notation iProp := (iPropG Λ Σ).

  Definition box_own_auth (γ : gname) (a : auth (option (excl bool))) : iProp :=
    own γ (a, ∅).

  Definition box_own_prop (γ : gname) (P : iProp) : iProp :=
    own γ (∅:auth _, Some (to_agree (Next (iProp_unfold P)))).

  Definition box_inv (γ : gname) (P : iProp) : iProp :=
    (∃ b, box_own_auth γ (● Excl' b) ★ box_own_prop γ P ★ if b then P else True)%I.

  Definition box_slice (γ : gname) (P : iProp) : iProp :=
    inv N (box_inv γ P).

  Definition box (f : gmap gname bool) (P : iProp) : iProp :=
    (∃ Φ : gname → iProp,
      ▷ (P ≡ [★ map] γ ↦ b ∈ f, Φ γ) ★
      [★ map] γ ↦ b ∈ f, box_own_auth γ (◯ Excl' b) ★ box_own_prop γ (Φ γ) ★
                         inv N (box_inv γ (Φ γ)))%I.
End box_defs.

Instance: Params (@box_own_auth) 4.
Instance: Params (@box_own_prop) 4.
Instance: Params (@box_inv) 4.
Instance: Params (@box_slice) 5.
Instance: Params (@box) 5.

Section box.
Context `{boxG Λ Σ} (N : namespace).
Notation iProp := (iPropG Λ Σ).
Implicit Types P Q : iProp.

(* FIXME: solve_proper picks the eq ==> instance for Next. *)
Global Instance box_own_prop_ne n γ : Proper (dist n ==> dist n) (box_own_prop γ).
Proof. intros P P' HP. by rewrite /box_own_prop HP. Qed.
Global Instance box_inv_ne n γ : Proper (dist n ==> dist n) (box_inv γ).
Proof. solve_proper. Qed.
Global Instance box_slice_ne n γ : Proper (dist n ==> dist n) (box_slice N γ).
Proof. solve_proper. Qed.
Global Instance box_ne n f : Proper (dist n ==> dist n) (box N f).
Proof. solve_proper. Qed.
Global Instance box_slice_persistent γ P : PersistentP (box_slice N γ P).
Proof. apply _. Qed.

(* This should go automatic *)
Instance box_own_auth_timeless γ
  (a : auth (option (excl bool))) : TimelessP (box_own_auth γ a).
Proof. apply own_timeless, pair_timeless; apply _. Qed.

Lemma box_own_auth_agree γ b1 b2 :
  (box_own_auth γ (● Excl' b1) ★ box_own_auth γ (◯ Excl' b2)) ⊢ (b1 = b2).
Proof.
  rewrite /box_own_prop -own_op own_valid prod_validI /= and_elim_l.
  iIntros "Hb".
  by iDestruct "Hb" as % [[[] [=]%leibniz_equiv] ?]%auth_valid_discrete.
Qed.

Lemma box_own_auth_update E γ b1 b2 b3 :
  (box_own_auth γ (● Excl' b1) ★ box_own_auth γ (◯ Excl' b2))
  ⊢ |={E}=> (box_own_auth γ (● Excl' b3) ★ box_own_auth γ (◯ Excl' b3)).
Proof.
  rewrite /box_own_prop -!own_op.
  apply own_update, prod_update; simpl; last reflexivity.
  by apply (auth_local_update (λ _, Excl' b3)).
Qed.

Lemma box_own_agree γ Q1 Q2 :
  (box_own_prop γ Q1 ★ box_own_prop γ Q2) ⊢ ▷ (Q1 ≡ Q2).
Proof.
  rewrite /box_own_prop -own_op own_valid prod_validI /= and_elim_r.
  rewrite option_validI /= agree_validI agree_equivI later_equivI /=.
  iIntros "#HQ >". rewrite -{2}(iProp_fold_unfold Q1).
  iRewrite "HQ". by rewrite iProp_fold_unfold.
Qed.

Lemma box_alloc : True ⊢ box N ∅ True.
Proof.
  iIntros; iExists (λ _, True)%I; iSplit.
  - iNext. by rewrite big_sepM_empty.
  - by rewrite big_sepM_empty.
Qed.

Lemma box_insert f P Q :
  ▷ box N f P ⊢ |={N}=> ∃ γ, f !! γ = None ★
    box_slice N γ Q ★ ▷ box N (<[γ:=false]> f) (Q ★ P).
Proof.
  iIntros "H"; iDestruct "H" as {Φ} "[#HeqP Hf]".
  iPvs (own_alloc_strong (● Excl' false ⋅ ◯ Excl' false,
    Some (to_agree (Next (iProp_unfold Q)))) _ (dom _ f))
    as {γ} "[Hdom Hγ]"; first done.
  rewrite pair_split. iDestruct "Hγ" as "[[Hγ Hγ'] #HγQ]".
  iDestruct "Hdom" as % ?%not_elem_of_dom.
  iPvs (inv_alloc N _ (box_inv γ Q) with "[Hγ]") as "#Hinv"; first done.
  { iNext. iExists false. by repeat iSplit. }
  iPvsIntro; iExists γ; repeat iSplit; auto.
  iNext. iExists (<[γ:=Q]> Φ); iSplit.
  - iNext. iRewrite "HeqP". by rewrite big_sepM_fn_insert'.
  - rewrite (big_sepM_fn_insert (λ _ _ P',  _ ★ _ _ P' ★ _ _ (_ _ P')))%I //.
    iFrame "Hf Hγ'". by iSplit.
Qed.

Lemma box_delete f P Q γ :
  f !! γ = Some false →
  (box_slice N γ Q ★ ▷ box N f P) ⊢ |={N}=> ∃ P',
    ▷ ▷ (P ≡ (Q ★ P')) ★ ▷ box N (delete γ f) P'.
Proof.
  iIntros {?} "[#Hinv H]"; iDestruct "H" as {Φ} "[#HeqP Hf]".
  iExists ([★ map] γ'↦_ ∈ delete γ f, Φ γ')%I.
  iInv N as {b} "(Hγ & #HγQ &_)"; iPvsIntro; iNext.
  iDestruct (big_sepM_delete _ f _ false with "Hf")
    as "[[Hγ' #[HγΦ ?]] ?]"; first done.
  iDestruct (box_own_agree γ Q (Φ γ) with "[#]") as "HeqQ"; first by iSplit.
  iDestruct (box_own_auth_agree γ b false with "[#]")
    as "%"; subst; first by iFrame "Hγ".
  iSplitL "Hγ"; last iSplit.
  - iExists false; repeat iSplit; auto.
  - iNext. iRewrite "HeqP". iRewrite "HeqQ". by rewrite -big_sepM_delete.
  - iExists Φ; by iSplit; [iNext|].
Qed.

Lemma box_fill f γ P Q :
  f !! γ = Some false →
  (box_slice N γ Q ★ ▷ Q ★ ▷ box N f P) ⊢ |={N}=> ▷ box N (<[γ:=true]> f) P.
Proof.
  iIntros {?} "(#Hinv & HQ & H)"; iDestruct "H" as {Φ} "[#HeqP Hf]".
  iInv N as {b'} "(Hγ & #HγQ & _)"; iTimeless "Hγ".
  iDestruct (big_sepM_later _ f with "Hf") as "Hf".
  iDestruct (big_sepM_delete _ f _ false with "Hf")
    as "[[Hγ' #[HγΦ Hinv']] ?]"; first done; iTimeless "Hγ'".
  iPvs (box_own_auth_update _ γ b' false true with "[Hγ Hγ']")
    as "[Hγ Hγ']"; first by iFrame "Hγ".
  iPvsIntro; iNext; iSplitL "Hγ HQ"; first (iExists true; by iFrame "Hγ HQ").
  iExists Φ; iSplit.
  - by rewrite big_sepM_insert_override.
  - rewrite -insert_delete big_sepM_insert ?lookup_delete //.
    iFrame "Hγ'". by repeat iSplit.
Qed.

Lemma box_empty f P Q γ :
  f !! γ = Some true →
  (box_slice N γ Q ★ ▷ box N f P) ⊢ |={N}=> ▷ Q ★ ▷ box N (<[γ:=false]> f) P.
Proof.
  iIntros {?} "[#Hinv H]"; iDestruct "H" as {Φ} "[#HeqP Hf]".
  iInv N as {b} "(Hγ & #HγQ & HQ)"; iTimeless "Hγ".
  iDestruct (big_sepM_later _ f with "Hf") as "Hf".
  iDestruct (big_sepM_delete _ f _ true with "Hf")
    as "[[Hγ' #[HγΦ Hinv']] ?]"; first done; iTimeless "Hγ'".
  iDestruct (box_own_auth_agree γ b true with "[#]")
    as "%"; subst; first by iFrame "Hγ".
  iFrame "HQ".
  iPvs (box_own_auth_update _ γ true true false with "[Hγ Hγ']")
    as "[Hγ Hγ']"; first by iFrame "Hγ".
  iPvsIntro; iNext; iSplitL "Hγ"; first (iExists false; by repeat iSplit).
  iExists Φ; iSplit.
  - by rewrite big_sepM_insert_override.
  - rewrite -insert_delete big_sepM_insert ?lookup_delete //.
    iFrame "Hγ'". by repeat iSplit.
Qed.

Lemma box_fill_all f P Q :
  (box N f P ★ ▷ P) ⊢ |={N}=> box N (const true <$> f) P.
Proof.
  iIntros "[H HP]"; iDestruct "H" as {Φ} "[#HeqP Hf]".
  iExists Φ; iSplitR; first by rewrite big_sepM_fmap.
  rewrite eq_iff later_iff big_sepM_later; iDestruct ("HeqP" with "HP") as "HP".
  iCombine "Hf" "HP" as "Hf".
  rewrite big_sepM_fmap; iApply (pvs_big_sepM _ _ f).
  iApply (big_sepM_impl _ _ f); iFrame "Hf".
  iAlways; iIntros {γ b' ?} "[(Hγ' & #$ & #$) HΦ]".
  iInv N as {b} "[Hγ _]"; iTimeless "Hγ".
  iPvs (box_own_auth_update _ γ b b' true with "[Hγ Hγ']")
    as "[Hγ $]"; first by iFrame "Hγ".
  iPvsIntro; iNext; iExists true. by iFrame "HΦ Hγ".
Qed.

Lemma box_empty_all f P Q :
  map_Forall (λ _, (true =)) f →
  box N f P ⊢ |={N}=> ▷ P ★ box N (const false <$> f) P.
Proof.
  iIntros {?} "H"; iDestruct "H" as {Φ} "[#HeqP Hf]".
  iAssert ([★ map] γ↦b ∈ f, ▷ Φ γ ★ box_own_auth γ (◯ Excl' false) ★
    box_own_prop γ (Φ γ) ★ inv N (box_inv γ (Φ γ)))%I with "=>[Hf]" as "[HΦ ?]".
  { iApply (pvs_big_sepM _ _ f); iApply (big_sepM_impl _ _ f); iFrame "Hf".
    iAlways; iIntros {γ b ?} "(Hγ' & #$ & #$)".
    assert (true = b) as <- by eauto.
    iInv N as {b} "(Hγ & _ & HΦ)"; iTimeless "Hγ".
    iDestruct (box_own_auth_agree γ b true with "[#]")
      as "%"; subst; first by iFrame "Hγ".
    iPvs (box_own_auth_update _ γ true true false with "[Hγ Hγ']")
      as "[Hγ $]"; first by iFrame "Hγ".
    iPvsIntro; iNext. iFrame "HΦ". iExists false. by iFrame "Hγ"; iSplit. }
  iPvsIntro; iSplitL "HΦ".
  - rewrite eq_iff later_iff big_sepM_later. by iApply "HeqP".
  - iExists Φ; iSplit; by rewrite big_sepM_fmap.
Qed.
End box.

Typeclasses Opaque box_slice box.
