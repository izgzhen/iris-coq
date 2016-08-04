From iris.algebra Require Import upred.
From iris.proofmode Require Import tactics.

(** This proves that we need the ▷ in a "Saved Proposition" construction with
    name-dependend allocation. *)
(** We fork in [uPred M] for any M, but the proof would work in any BI. *)
Section savedprop.
  Context (M : ucmraT).
  Notation iProp := (uPred M).
  Notation "¬ P" := (□ (P → False))%I : uPred_scope.
  Implicit Types P : iProp.

  (* Saved Propositions and view shifts. *)
  Context (sprop : Type) (saved : sprop → iProp → iProp) (pvs : iProp → iProp).
  Hypothesis pvs_mono : ∀ P Q, (P ⊢ Q) → pvs P ⊢ pvs Q.
  Hypothesis sprop_persistent : ∀ i P, PersistentP (saved i P).
  Hypothesis sprop_alloc_dep :
    ∀ (P : sprop → iProp), True ⊢ pvs (∃ i, saved i (P i)).
  Hypothesis sprop_agree : ∀ i P Q, saved i P ∧ saved i Q ⊢ P ↔ Q.

  (* Self-contradicting assertions are inconsistent *)
  Lemma no_self_contradiction P `{!PersistentP P} : □ (P ↔ ¬ P) ⊢ False.
  Proof. (* FIXME: Cannot destruct the <-> as two implications. iApply with <-> also does not work. *)
    rewrite /uPred_iff. iIntros "#[H1 H2]".
    iAssert P as "#HP".
    { iApply "H2". iIntros "! #HP". by iApply ("H1" with "[#]"). }
    by iApply ("H1" with "[#]").
  Qed.

  (* "Assertion with name [i]" is equivalent to any assertion P s.t. [saved i P] *)
  Definition A (i : sprop) : iProp := ∃ P, saved i P ★ □ P.
  Lemma saved_is_A i P `{!PersistentP P} : saved i P ⊢ □ (A i ↔ P).
  Proof.
    rewrite /uPred_iff. iIntros "#HS !". iSplit.
    - iDestruct 1 as (Q) "[#HSQ HQ]".
      iApply (sprop_agree i P Q with "[]"); eauto.
    - iIntros "#HP". iExists P. by iSplit.
  Qed.

  (* Define [Q i] to be "negated assertion with name [i]". Show that this
     implies that assertion with name [i] is equivalent to its own negation. *)
  Definition Q i := saved i (¬ A i).
  Lemma Q_self_contradiction i : Q i ⊢ □ (A i ↔ ¬ A i).
  Proof. iIntros "#HQ !". by iApply (saved_is_A i (¬A i)). Qed.

  (* We can obtain such a [Q i]. *)
  Lemma make_Q : True ⊢ pvs (∃ i, Q i).
  Proof. apply sprop_alloc_dep. Qed.

  (* Put together all the pieces to derive a contradiction. *)
  (* TODO: Have a lemma in upred.v that says that we cannot view shift to False. *)
  Lemma contradiction : True ⊢ pvs False.
  Proof.
    rewrite make_Q. apply pvs_mono. iDestruct 1 as (i) "HQ".
    iApply (no_self_contradiction (A i)). by iApply Q_self_contradiction.
  Qed.
End savedprop.
