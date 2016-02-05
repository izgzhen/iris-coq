Require Export algebra.auth.
Require Import program_logic.functor program_logic.language program_logic.weakestpre.

(* RJ: This is a work-in-progress playground.
   FIXME: Finish or remove. *)

Section auth.
  (* TODO what should be implicit, what explicit? *)
  Context {Λ : language}.
  Context {C : nat → cmraT}.
  Context (i : nat).
  Context {A : cmraT}.

  Hypothesis Ci : C i = authRA A.
  Let Σ : iFunctor := iprodF (mapF positive ∘ constF ∘ C).

  Definition tr (a : authRA A) : C i.
  rewrite Ci. exact a. Defined.
  Definition tr' (c : C i) : authRA A.
  rewrite -Ci. exact c. Defined.

  Lemma tr'_tr a :
    tr' $ tr a = a.
  Proof.
    rewrite /tr' /tr. by destruct Ci.
  Qed.

  Lemma tr_tr' c :
    tr $ tr' c = c.
  Proof.
    rewrite /tr' /tr. by destruct Ci.
  Qed.

  Lemma tr_proper : Proper ((≡) ==> (≡)) tr.
  Proof.
    move=>a1 a2 Heq. rewrite /tr. by destruct Ci.
  Qed.

  Lemma Ci_op (c1 c2: C i) :
    c1 ⋅ c2 = tr (tr' c1 ⋅ tr' c2).
  Proof.
    rewrite /tr' /tr. by destruct Ci.
  Qed.

  Definition Tr j {H : i = j} (c: C i) : C j.
  rewrite -H. exact c. Defined.

  (* FIXME RJ: I'd rather not have to specify Σ by hand here. *)
  Definition ownNothing : iProp Λ Σ := ownG (Σ:=Σ) (fun j => (∅ : mapRA positive (C j))).
  Definition ownA (p : positive) (a : authRA A) : iProp Λ Σ :=
    ownG (Σ:=Σ) (fun j => match decide (i = j) with
                                | left Heq => <[p:=Tr j (H:=Heq) $ tr a]>∅
                                | right Hneq => ∅ end).

  Lemma ownA_op p a1 a2 :
    (ownA p a1 ★ ownA p a2)%I ≡ ownA p (a1 ⋅ a2).
  Proof.
    rewrite /ownA -ownG_op. apply ownG_proper=>j /=.
    rewrite iprod_lookup_op. destruct (decide (i = j)).
    - move=>q. destruct e. rewrite lookup_op /=.
      destruct (decide (p = q)); first subst q.
      + rewrite !lookup_insert.
        rewrite /op /cmra_op /=. f_equiv.
        rewrite Ci_op. apply tr_proper.
        rewrite !tr'_tr. reflexivity.
      + by rewrite !lookup_insert_ne //.
    - by rewrite left_id.
  Qed.

End auth.

    
