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

  (* We have tokens for a little "three-state STS": [fresh] -> [start n] ->
     [finish n].  The [auth_*] tokens are in the invariant and assert an exact
     state. [fresh] also asserts the exact state; it is owned by threads (i.e.,
     there's a token needed to transition to [start].)  [started] and [finished]
     are *lower bounds*. We don't need "auth_finish" because the state will
     never change again, so [finished] is just as good. *)
  Context (auth_fresh fresh : iProp).
  Context (auth_start started finished : name → iProp).
  Hypothesis fresh_start :
    forall n, auth_fresh ★ fresh ⊢ pvs0 (auth_start n ★ started n).
  Hypotheses start_finish :
    forall n, auth_start n ⊢ pvs0 (finished n).

  Hypothesis fresh_not_start : forall n, auth_start n ★ fresh ⊢ False.
  Hypothesis fresh_not_finished : forall n, finished n ★ fresh ⊢ False.
  Hypothesis started_not_fresh : forall n, auth_fresh ★ started n ⊢ False.
  Hypothesis finished_not_start : forall n m, auth_start n ★ finished m ⊢ False.

  Hypothesis started_start_agree : forall n m, auth_start n ★ started m ⊢ n = m.
  Hypothesis started_finished_agree :
    forall n m, finished n ★ started m ⊢ n = m.
  Hypothesis finished_agree :
    forall n m, finished n ★ finished m ⊢ n = m.

  Hypothesis started_dup : forall n, started n ⊢ started n ★ started n.
  Hypothesis finished_dup : forall n, finished n ⊢ finished n ★ finished n.

  (* We have that we cannot view shift from the initial state to false
     (because the initial state is actually achievable). *)
  Hypothesis soundness : ¬ (auth_fresh ★ fresh ⊢ pvs1 False).

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

  (* "Weak box" -- a weak form of □ for non-persistent assertions. *)
  Definition wbox P : iProp :=
    ∃ Q, Q ★ □(Q → P) ★ □(Q → Q ★ Q).

  Lemma wbox_dup P :
    wbox P ⊢ wbox P ★ wbox P.
  Proof.
    iIntros "H". iDestruct "H" as (Q) "(HQ & #HP & #Hdup)".
    iDestruct ("Hdup" with "HQ") as "[HQ HQ']".
    iSplitL "HQ"; iExists Q; iSplit; eauto.
  Qed.

  Lemma wbox_out P :
    wbox P ⊢ P.
  Proof.
    iIntros "H". iDestruct "H" as (Q) "(HQ & #HP & _)".
    iApply "HP". done.
  Qed.

  (** Now to the actual counterexample. We start with a weird for of saved propositions. *)
  Definition saved (i : name) (P : iProp) : iProp :=
    ∃ F : name → iProp, P = F i ★ started i ★
      inv i (auth_fresh ∨ ∃ j, auth_start j ∨ (finished j ★ wbox (F j))).

  Lemma saved_dup i P :
    saved i P ⊢ saved i P ★ saved i P.
  Proof.
    iIntros "H". iDestruct "H" as (F) "(#? & Hs & #?)".
    iDestruct (started_dup with "Hs") as "[Hs Hs']". iSplitL "Hs".
    - iExists F. eauto.
    - iExists F. eauto.
  Qed.

  Lemma saved_alloc (P : name → iProp) :
    auth_fresh ★ fresh ⊢ pvs1 (∃ i, saved i (P i)).
  Proof.
    iIntros "[Haf Hf]". iVs (inv_alloc (auth_fresh ∨ ∃ j, auth_start j ∨ (finished j ★ wbox (P j))) with "[Haf]") as (i) "#Hi".
    { iLeft. done. }
    iExists i. iApply inv_open'. iSplit; first done. iIntros "[Haf|Has]"; last first.
    { iExFalso. iDestruct "Has" as (j) "[Has | [Haf _]]".
      - iApply fresh_not_start. iSplitL "Has"; done.
      - iApply fresh_not_finished. iSplitL "Haf"; done. }
    iVs ((fresh_start i) with "[Hf Haf]") as "[Has Hs]"; first by iFrame.
    iDestruct (started_dup with "Hs") as "[Hs Hs']".
    iApply pvs0_intro. iSplitR "Hs'".
    - iRight. iExists i. iLeft. done.
    - iApply pvs1_intro. iExists P. iSplit; first done. by iFrame.
  Qed.

  Lemma saved_cast i P Q :
    saved i P ★ saved i Q ★ wbox P ⊢ pvs1 (wbox Q).
  Proof.
    iIntros "(HsP & HsQ & HP)". iDestruct "HsP" as (FP) "(% & HsP & #HiP)".
    iApply (inv_open' i). iSplit; first done.
    iIntros "[HaP|HaP]".
    { iExFalso. iApply started_not_fresh. iSplitL "HaP"; done. }
    (* Can I state a view-shift and immediately run it? *)
    iAssert (pvs0 (finished i)) with "[HaP HsP]" as "Hf".
    { iDestruct "HaP" as (j) "[Hs | [Hf _]]".
      - iApply start_finish.
        iDestruct (started_start_agree with "[#]") as "%"; first by iSplitL "Hs".
        subst j. done.
      - iApply pvs0_intro.
        iDestruct (started_finished_agree with "[#]") as "%"; first by iSplitL "Hf".
        subst j. done. }
    iVs "Hf" as "Hf". iApply pvs0_intro.
    iDestruct (finished_dup with "Hf") as "[Hf Hf']". iSplitL "Hf' HP".
    { iRight. iExists i. iRight. subst. iSplitL "Hf'"; done. }
    iDestruct "HsQ" as (FQ) "(% & HsQ & HiQ)".
    iApply (inv_open' i). iSplit; first iExact "HiQ".
    iIntros "[HaQ | HaQ]".
    { iExFalso. iApply started_not_fresh. iSplitL "HaQ"; done. }
    iDestruct "HaQ" as (j) "[HaS | [Hf' HQ]]".
    { iExFalso. iApply finished_not_start. iSplitL "HaS"; done. }
    iApply pvs0_intro.
    iDestruct (finished_dup with "Hf'") as "[Hf' Hf'']".
    iDestruct (wbox_dup with "HQ") as "[HQ HQ']".
    iSplitL "Hf'' HQ'".
    { iRight. iExists j. iRight. by iSplitR "HQ'". }
    iPoseProof (finished_agree with "[#]") as "H".
    { iFrame "Hf Hf'". done. }
    iDestruct "H" as %<-. iApply pvs1_intro. subst Q. done.
  Qed.

  (** And now we tie a bad knot. *)
  Notation "¬ P" := (wbox (P -★ pvs1 False))%I : uPred_scope.
  Definition A i : iProp := ∃ P, ¬P ★ saved i P.
  Lemma A_dup i :
    A i ⊢ A i ★ A i.
  Proof.
    iIntros "HA". iDestruct "HA" as (P) "[HNP HsP]".
    iDestruct (wbox_dup with "HNP") as "[HNP HNP']".
    iDestruct (saved_dup with "HsP") as "[HsP HsP']".
    iSplitL "HNP HsP"; iExists P.
    - by iSplitL "HNP".
    - by iSplitL "HNP'".
  Qed.
  Lemma A_wbox i :
    A i ⊢ wbox (A i).
  Proof.
    iIntros "H". iExists (A i). iSplitL "H"; first done.
    iSplit; first by iIntros "!# ?". iIntros "!# HA".
    by iApply A_dup.
  Qed.

  Lemma A_alloc :
    auth_fresh ★ fresh ⊢ pvs1 (∃ i, saved i (A i)).
  Proof. by apply saved_alloc. Qed.

  Lemma alloc_NA i :
    saved i (A i) ⊢ (¬A i).
  Proof.
    iIntros "Hi". iExists (saved i (A i)). iSplitL "Hi"; first done.
    iSplit; last by (iIntros "!# ?"; iApply saved_dup).
    iIntros "!# Hi HAi".
    iDestruct (A_dup with "HAi") as "[HAi HAi']".
    iDestruct "HAi'" as (P) "[HNP Hi']".
    iVs ((saved_cast i) with "[Hi Hi' HAi]") as "HP".
    { iSplitL "Hi"; first done. iSplitL "Hi'"; first done. by iApply A_wbox. }
    iPoseProof (wbox_out with "HNP") as "HNP".
    iApply "HNP". iApply wbox_out. done.
  Qed.

  Lemma alloc_A i :
    saved i (A i) ⊢ A i.
  Proof.
    iIntros "Hi". iDestruct (saved_dup with "Hi") as "[Hi Hi']".
    iPoseProof (alloc_NA with "Hi") as "HNA".
    iExists (A i). iSplitL "HNA"; done.
  Qed.

  Lemma contradiction : False.
  Proof.
    apply soundness. iIntros "H".
    iVs (A_alloc with "H") as "H". iDestruct "H" as (i) "H".
    iDestruct (saved_dup with "H") as "[H H']".
    iPoseProof (alloc_NA with "H") as "HN".
    iPoseProof (wbox_out with "HN") as "HN".
    iApply "HN".
    iApply alloc_A. done.
  Qed.

End inv. End inv.
