From iris.algebra Require Import upred.
From iris.proofmode Require Import tactics.

(** This proves that we need the ▷ in a "Saved Proposition" construction with
    name-dependend allocation. *)
(** We fork in [uPred M] for any M, but the proof would work in any BI. *)
Section savedprop.
  Context (M : ucmraT).
  Notation iProp := (uPred M).
  Notation "¬ P" := (□(P → False))%I : uPred_scope.

  (* Saved Propositions. *)
  Context (sprop : Type) (saved : sprop → iProp → iProp).
  Hypothesis sprop_persistent : forall i P, PersistentP (saved i P).
  Hypothesis sprop_alloc_dep :
    forall (P : sprop → iProp), True ⊢ ∃ i, saved i (P i).
  Hypothesis sprop_agree :
    forall i P Q, saved i P ∧ saved i Q ⊢ P ↔ Q.

  (* Self-contradicting assertions are inconsistent *)
  Lemma no_self_contradiction (P : iProp) `{!PersistentP P} :
    □(P ↔ ¬ P) ⊢ False.
  Proof. (* FIXME: Cannot destruct the <-> as two implications. iApply with <-> also does not work. *)
    rewrite /uPred_iff. iIntros "#[H1 H2]". (* FIXME: Cannot iApply "H1". *)
    iAssert P as "#HP".
    { iApply "H2". iIntros "!#HP". by iApply ("H1" with "HP"). }
    by iApply ("H1" with "HP HP").
  Qed.

  (* "Assertion with name [i]" is equivalent to any assertion P s.t. [saved i P] *)
  Definition A (i : sprop) : iProp := ∃ P, saved i P ★ □P.
  Lemma saved_is_A i P `{!PersistentP P} : saved i P ⊢ □(A i ↔ P).
  Proof.
    rewrite /uPred_iff. iIntros "#HS !". iSplit.
    - iIntros "H". iDestruct "H" as (Q) "[#HSQ HQ]".
      iPoseProof (sprop_agree i P Q with "[]") as "Heq"; first by eauto.
      rewrite /uPred_iff. by iApply "Heq".
    - iIntros "#HP". iExists P. by iSplit.
  Qed.

  (* Define [Q i] to be "negated assertion with name [i]". Show that this
     implies that assertion with name [i] is equivalent to its own negation. *)
  Definition Q i := saved i (¬ A i).
  Lemma Q_self_contradiction i :
    Q i ⊢ □(A i ↔ ¬ A i).
  Proof.
    iIntros "#HQ". iApply (@saved_is_A i (¬ A i)%I _). (* FIXME: If we already introduced the box, this iApply does not work. *)
    done.
  Qed.

  (* We can obtain such a [Q i]. *)
  Lemma make_Q :
    True ⊢ ∃ i, Q i.
  Proof.
    apply sprop_alloc_dep.
  Qed.

  (* Put together all the pieces to derive a contradiction. *)
  Lemma contradiction : False.
  Proof.
    apply (@uPred.sound M). iIntros "".
    iPoseProof make_Q as "HQ". iDestruct "HQ" as (i) "HQ".
    iApply (@no_self_contradiction (A i) _).
    by iApply Q_self_contradiction.
  Qed.
End savedprop.


  

