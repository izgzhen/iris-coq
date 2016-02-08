Require Export algebra.auth algebra.functor.
Require Import program_logic.language program_logic.weakestpre.
Import uPred.

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

  Lemma A_val a :
    ✓a = ✓(tr a).
  Proof.
    rewrite /tr. by destruct Ci.
  Qed.

  (* FIXME RJ: I'd rather not have to specify Σ by hand here. *)
  Definition A2m (p : positive) (a : authRA A) : iGst Λ Σ :=
    iprod_singleton i (<[p:=tr a]>∅).
  Definition ownA (p : positive) (a : authRA A) : iProp Λ Σ :=
    ownG (Σ:=Σ) (A2m p a).

  Lemma ownA_op p a1 a2 :
    (ownA p a1 ★ ownA p a2)%I ≡ ownA p (a1 ⋅ a2).
  Proof.
    rewrite /ownA /A2m /iprod_singleton /iprod_insert -ownG_op. apply ownG_proper=>j /=.
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

  (* TODO: This also holds if we just have ✓a at the current step-idx, as Iris
     assertion. However, the map_updateP_alloc does not suffice to show this. *)
  Lemma ownA_alloc E a :
    ✓a → True ⊑ pvs E E (∃ p, ownA p a).
  Proof.
    intros Ha. set (P m := ∃ p, m = A2m p a).
    set (a' := tr a).
    rewrite -(pvs_mono _ _ (∃ m, ■P m ∧ ownG m)%I).
    - rewrite -pvs_updateP_empty //; [].
      subst P. eapply (iprod_singleton_updateP_empty i).
      + eapply map_updateP_alloc' with (x:=a'). subst a'.
        by rewrite -A_val.
      + simpl. move=>? [p [-> ?]]. exists p. done.
    - apply exist_elim=>m. apply const_elim_l.
      move=>[p ->] {P}. by rewrite -(exist_intro p).
  Qed.      
    
End auth.

