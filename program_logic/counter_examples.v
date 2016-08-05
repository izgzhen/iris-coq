From iris.algebra Require Import upred.
From iris.proofmode Require Import tactics.

(** This proves that we need the ▷ in a "Saved Proposition" construction with
name-dependend allocation. *)
Module savedprop. Section savedprop.
  Context (M : ucmraT).
  Notation iProp := (uPred M).
  Notation "¬ P" := (□ (P → False))%I : uPred_scope.
  Implicit Types P : iProp.

  (* Saved Propositions and view shifts. *)
  Context (sprop : Type) (saved : sprop → iProp → iProp).
  Hypothesis sprop_persistent : ∀ i P, PersistentP (saved i P).
  Hypothesis sprop_alloc_dep :
    ∀ (P : sprop → iProp), True =r=> (∃ i, saved i (P i)).
  Hypothesis sprop_agree : ∀ i P Q, saved i P ∧ saved i Q ⊢ P ↔ Q.

  (* Self-contradicting assertions are inconsistent *)
  Lemma no_self_contradiction P `{!PersistentP P} : □ (P ↔ ¬ P) ⊢ False.
  Proof.
    iIntros "#[H1 H2]".
    iAssert P as "#HP".
    { iApply "H2". iIntros "!# #HP". by iApply ("H1" with "[#]"). }
    by iApply ("H1" with "[#]").
  Qed.

  (* "Assertion with name [i]" is equivalent to any assertion P s.t. [saved i P] *)
  Definition A (i : sprop) : iProp := ∃ P, saved i P ★ □ P.
  Lemma saved_is_A i P `{!PersistentP P} : saved i P ⊢ □ (A i ↔ P).
  Proof.
    iIntros "#HS !#". iSplit.
    - iDestruct 1 as (Q) "[#HSQ HQ]".
      iApply (sprop_agree i P Q with "[]"); eauto.
    - iIntros "#HP". iExists P. by iSplit.
  Qed.

  (* Define [Q i] to be "negated assertion with name [i]". Show that this
     implies that assertion with name [i] is equivalent to its own negation. *)
  Definition Q i := saved i (¬ A i).
  Lemma Q_self_contradiction i : Q i ⊢ □ (A i ↔ ¬ A i).
  Proof. iIntros "#HQ !#". by iApply (saved_is_A i (¬A i)). Qed.

  (* We can obtain such a [Q i]. *)
  Lemma make_Q : True =r=> ∃ i, Q i.
  Proof. apply sprop_alloc_dep. Qed.

  (* Put together all the pieces to derive a contradiction. *)
  Lemma rvs_false : (True : uPred M) =r=> False.
  Proof.
    rewrite make_Q. apply uPred.rvs_mono. iDestruct 1 as (i) "HQ".
    iApply (no_self_contradiction (A i)). by iApply Q_self_contradiction.
  Qed.

  Lemma contradiction : False.
  Proof.
    apply (@uPred.adequacy M False 1); simpl.
    rewrite -uPred.later_intro. apply rvs_false.
  Qed.
End savedprop. End savedprop.

(** This proves that we need the ▷ when opening invariants. *)
(** We fork in [uPred M] for any M, but the proof would work in any BI. *)
Module inv. Section inv.
  Context (M : ucmraT).
  Notation iProp := (uPred M).
  Implicit Types P : iProp.

  (** Assumptions *)
  (* We have view shifts (two classes: empty/full mask) *)
  Context (pvs0 pvs1 : iProp → iProp).

  Hypothesis pvs0_intro : forall P, P ⊢ pvs0 P.

  Hypothesis pvs0_mono : forall P Q, (P ⊢ Q) → pvs0 P ⊢ pvs0 Q.
  Hypothesis pvs0_pvs0 : forall P, pvs0 (pvs0 P) ⊢ pvs0 P.
  Hypothesis pvs0_frame_l : forall P Q, P ★ pvs0 Q ⊢ pvs0 (P ★ Q).

  Hypothesis pvs1_mono : forall P Q, (P ⊢ Q) → pvs1 P ⊢ pvs1 Q.
  Hypothesis pvs1_pvs1 : forall P, pvs1 (pvs1 P) ⊢ pvs1 P.
  Hypothesis pvs1_frame_l : forall P Q, P ★ pvs1 Q ⊢ pvs1 (P ★ Q).

  Hypothesis pvs0_pvs1 : forall P, pvs0 P ⊢ pvs1 P.

  (* We have invariants *)
  Context (name : Type) (inv : name → iProp → iProp).
  Hypothesis inv_persistent : forall i P, PersistentP (inv i P).
  Hypothesis inv_alloc :
    forall (P : iProp), P ⊢ pvs1 (∃ i, inv i P).
  Hypothesis inv_open :
    forall i P Q R, (P ★ Q ⊢ pvs0 (P ★ R)) → (inv i P ★ Q ⊢ pvs1 R).

  (* We have tokens for a little "two-state STS": [start] -> [finish].
     state. [start] also asserts the exact state; it is only ever owned by the
     invariant.  [finished] is duplicable. *)
  Context (gname : Type).
  Context (start finished : gname → iProp).

  Hypothesis sts_alloc : True ⊢ pvs0 (∃ γ, start γ).
  Hypotheses start_finish : forall γ, start γ ⊢ pvs0 (finished γ).

  Hypothesis finished_not_start : forall γ, start γ ★ finished γ ⊢ False.

  Hypothesis finished_dup : forall γ, finished γ ⊢ finished γ ★ finished γ.

  (* We assume that we cannot view shift to false. *)
  Hypothesis soundness : ¬ (True ⊢ pvs1 False).

  (** Some general lemmas and proof mode compatibility. *)
  Lemma inv_open' i P R:
    inv i P ★ (P -★ pvs0 (P ★ pvs1 R)) ⊢ pvs1 R.
  Proof.
    iIntros "(#HiP & HP)". iApply pvs1_pvs1. iApply inv_open; last first.
    { iSplit; first done. iExact "HP". }
    iIntros "(HP & HPw)". by iApply "HPw".
  Qed.

  Lemma pvs1_intro P : P ⊢ pvs1 P.
  Proof. rewrite -pvs0_pvs1. apply pvs0_intro. Qed.

  Instance pvs0_mono' : Proper ((⊢) ==> (⊢)) pvs0.
  Proof. intros ?**. by apply pvs0_mono. Qed.
  Instance pvs0_proper : Proper ((⊣⊢) ==> (⊣⊢)) pvs0.
  Proof.
    intros P Q Heq.
    apply (anti_symm (⊢)); apply pvs0_mono; by rewrite ?Heq -?Heq.
  Qed.
  Instance pvs1_mono' : Proper ((⊢) ==> (⊢)) pvs1.
  Proof. intros ?**. by apply pvs1_mono. Qed.
  Instance pvs1_proper : Proper ((⊣⊢) ==> (⊣⊢)) pvs1.
  Proof.
    intros P Q Heq.
    apply (anti_symm (⊢)); apply pvs1_mono; by rewrite ?Heq -?Heq.
  Qed.

  Lemma pvs0_frame_r : forall P Q, (pvs0 P ★ Q) ⊢ pvs0 (P ★ Q).
  Proof.
    intros. rewrite comm pvs0_frame_l. apply pvs0_mono. by rewrite comm.
  Qed.
  Lemma pvs1_frame_r : forall P Q, (pvs1 P ★ Q) ⊢ pvs1 (P ★ Q).
  Proof.
    intros. rewrite comm pvs1_frame_l. apply pvs1_mono. by rewrite comm.
  Qed.

  Global Instance elim_pvs0_pvs0 P Q :
    ElimVs (pvs0 P) P (pvs0 Q) (pvs0 Q).
  Proof.
    rewrite /ElimVs. etrans; last eapply pvs0_pvs0.
    rewrite pvs0_frame_r. apply pvs0_mono. by rewrite uPred.wand_elim_r.
  Qed.

  Global Instance elim_pvs1_pvs1 P Q :
    ElimVs (pvs1 P) P (pvs1 Q) (pvs1 Q).
  Proof.
    rewrite /ElimVs. etrans; last eapply pvs1_pvs1.
    rewrite pvs1_frame_r. apply pvs1_mono. by rewrite uPred.wand_elim_r.
  Qed.

  Global Instance elim_pvs0_pvs1 P Q :
    ElimVs (pvs0 P) P (pvs1 Q) (pvs1 Q).
  Proof.
    rewrite /ElimVs. rewrite pvs0_pvs1. apply elim_pvs1_pvs1.
  Qed.

  Global Instance exists_split_pvs0 {A} P (Φ : A → iProp) :
    FromExist P Φ → FromExist (pvs0 P) (λ a, pvs0 (Φ a)).
  Proof.
    rewrite /FromExist=>HP. apply uPred.exist_elim=> a.
    apply pvs0_mono. by rewrite -HP -(uPred.exist_intro a).
  Qed.

  Global Instance exists_split_pvs1 {A} P (Φ : A → iProp) :
    FromExist P Φ → FromExist (pvs1 P) (λ a, pvs1 (Φ a)).
  Proof.
    rewrite /FromExist=>HP. apply uPred.exist_elim=> a.
    apply pvs1_mono. by rewrite -HP -(uPred.exist_intro a).
  Qed.

  (** Now to the actual counterexample. We start with a weird for of saved propositions. *)
  Definition saved (γ : gname) (P : iProp) : iProp :=
    ∃ i, inv i (start γ ∨ (finished γ ★ □P)).
  Global Instance : forall γ P, PersistentP (saved γ P) := _.

  Lemma saved_alloc (P : gname → iProp) :
    True ⊢ pvs1 (∃ γ, saved γ (P γ)).
  Proof.
    iIntros "". iVs (sts_alloc) as (γ) "Hs".
    iVs (inv_alloc (start γ ∨ (finished γ ★ □ (P γ))) with "[Hs]") as (i) "#Hi".
    { iLeft. done. }
    iApply pvs1_intro. iExists γ, i. done.
  Qed.

  Lemma saved_cast γ P Q :
    saved γ P ★ saved γ Q ★ □ P ⊢ pvs1 (□ Q).
  Proof.
    iIntros "(#HsP & #HsQ & #HP)". iDestruct "HsP" as (i) "HiP".
    iApply (inv_open' i). iSplit; first done.
    (* Can I state a view-shift and immediately run it? *)
    iIntros "HaP". iAssert (pvs0 (finished γ)) with "[HaP]" as "Hf".
    { iDestruct "HaP" as "[Hs | [Hf _]]".
      - by iApply start_finish.
      - by iApply pvs0_intro. }
    iVs "Hf" as "Hf". iDestruct (finished_dup with "Hf") as "[Hf Hf']".
    iApply pvs0_intro. iSplitL "Hf'"; first by eauto.
    (* Step 2: Open the Q-invariant. *)
    iClear "HiP". clear i. iDestruct "HsQ" as (i) "HiQ".
    iApply (inv_open' i). iSplit; first done.
    iIntros "[HaQ | [_ #HQ]]".
    { iExFalso. iApply finished_not_start. iSplitL "HaQ"; done. }
    iApply pvs0_intro. iSplitL "Hf".
    { iRight. by iSplitL "Hf". }
    by iApply pvs1_intro.
  Qed.

  (** And now we tie a bad knot. *)
  Notation "¬ P" := (□ (P -★ pvs1 False))%I : uPred_scope.
  Definition A i : iProp := ∃ P, ¬P ★ saved i P.
  Global Instance : forall i, PersistentP (A i) := _.

  Lemma A_alloc :
    True ⊢ pvs1 (∃ i, saved i (A i)).
  Proof. by apply saved_alloc. Qed.

  Lemma alloc_NA i :
    saved i (A i) ⊢ (¬A i).
  Proof.
    iIntros "#Hi !# #HA". iPoseProof "HA" as "HA'".
    iDestruct "HA'" as (P) "#[HNP Hi']".
    iVs ((saved_cast i) with "[]") as "HP".
    { iSplit; first iExact "Hi". iSplit; first iExact "Hi'". done. }
    by iApply "HNP".
  Qed.

  Lemma alloc_A i :
    saved i (A i) ⊢ A i.
  Proof.
    iIntros "#Hi". iPoseProof (alloc_NA with "Hi") as "HNA".
    iExists (A i). iSplit; done.
  Qed.

  Lemma contradiction : False.
  Proof.
    apply soundness. iIntros "".
    iVs A_alloc as (i) "#H".
    iPoseProof (alloc_NA with "H") as "HN".
    iApply "HN".
    iApply alloc_A. done.
  Qed.

End inv. End inv.
