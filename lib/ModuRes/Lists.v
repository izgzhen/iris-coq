Require Import Ssreflect.ssreflect.
Require Import CSetoid List ListSet.

(* Stuff about lists that ought to be in the stdlib... *)
Lemma NoDup_app3 {T} (l1 l2 l3: list T):
  NoDup (l1 ++ l2 ++ l3) -> NoDup (l2 ++ l1 ++ l3).
Proof.
  revert l2 l3. induction l1; induction l2; intro l3; simpl; try tauto; [].
  move=>Hndup. change (NoDup (a0 :: l2 ++ (a::nil) ++ l1 ++ l3)).
  apply NoDup_cons; last first.
  - apply IHl2. eapply NoDup_remove_1. eassumption.
  - rewrite app_comm_cons in Hndup. apply NoDup_remove_2 in Hndup.
    move=>Hin. apply Hndup. clear -Hin. rewrite !in_app_iff. rewrite ->!in_app_iff in Hin.
    destruct Hin as [Hin|[[Hin|[]]|[Hin|Hin]]].
    + right. left. assumption.
    + left. left. assumption.
    + left. right. assumption.
    + right. right. assumption.
Qed.

Infix "∈" := In (at level 31, no associativity) : list_scope.

Section FilterDup.
  Context {K: Type} `{eqK : DecEq K}.

  (* Remove the None elements from the list, and duplicates *)
  Fixpoint filter_dupes (dupes l: list K) :=
    match l with
    | nil => nil
    | k::ks => if set_mem dec_eq k dupes then filter_dupes dupes ks
               else k::filter_dupes (k::dupes) ks
    end.

  Lemma filter_dupes_notin dupes l:
    forall k, k ∈ dupes -> ~(k ∈ filter_dupes dupes l).
  Proof.
    move:dupes. induction l; intros dupes k Hin_dupes.
    - move=>Hin_dom. destruct Hin_dom.
    - simpl. destruct (set_mem _ a dupes) eqn:EQsm.
      + apply IHl. assumption.
      + apply set_mem_complete1 in EQsm.
        move=>[EQ|Hin].
        * subst a. apply EQsm. apply Hin_dupes.
        * eapply IHl, Hin. right. assumption.
  Qed.

  Lemma filter_dupes_nodup dupes l:
    NoDup (filter_dupes dupes l).
  Proof.
    move:dupes. induction l; intros dupes; simpl.
    - apply NoDup_nil.
    - destruct (set_mem _ a dupes) eqn:EQsm.
      { apply IHl. }
      apply set_mem_complete1 in EQsm.
      apply NoDup_cons.
      + eapply filter_dupes_notin. left. reflexivity.
      + apply IHl.
  Qed.

  Lemma filter_dupes_in dupes l k:
    ~k ∈ dupes -> k ∈ l -> k ∈ filter_dupes dupes l.
  Proof.
    revert dupes; induction l; intros ? Hdupes Hdom; simpl.
    - exact Hdom.
    - destruct (dec_eq a k) as [EQ|NEQ].
      + subst. destruct (set_mem _ k dupes) eqn:EQsm.
        { exfalso. eapply Hdupes, set_mem_correct1. eassumption. }
        left. reflexivity.
      + destruct Hdom as [Heq|Hdom]; first contradiction.
        destruct (set_mem _ a dupes) eqn:EQsm.
        { eapply IHl; assumption. }
        right. apply IHl; try assumption. move=>[Heq|Hin]; first contradiction.
        apply Hdupes, Hin.
  Qed.

  Lemma filter_dupes_isin dupes l k:
    k ∈ filter_dupes dupes l -> ~k ∈ dupes /\ k ∈ l.
  Proof.
    revert dupes; induction l; intros ?; simpl; intros Hin.
    - destruct Hin.
    - destruct (set_mem _ a dupes) eqn:EQsm.
      { specialize (IHl _ Hin). tauto. }
      destruct (dec_eq a k) as [EQ|NEQ].
      + subst a.
        split; first (eapply set_mem_complete1; eassumption).
        left; reflexivity.
      + destruct Hin as [Heq|Hin]; first contradiction.
        specialize (IHl _ Hin). split; last tauto.
        destruct IHl as [Hind _]. move=>Hind'. apply Hind. right. assumption.
  Qed.

  Lemma filter_dupes_id dupes l:
    NoDup (dupes++l) ->
    filter_dupes dupes l = l.
  Proof.
    revert dupes; induction l; intros dupes Hndup; simpl.
    - reflexivity.
    - destruct (set_mem _ a dupes) eqn:EQsm.
      { exfalso. apply set_mem_correct1 in EQsm.
        apply NoDup_remove_2 in Hndup. apply Hndup.
        apply in_app_iff. left. assumption. }
      f_equal. apply IHl.
      revert Hndup. clear. change (NoDup(dupes ++ [a] ++ l) -> NoDup ([a] ++ dupes ++ l)).
      eapply NoDup_app3.
  Qed.
End FilterDup.

Section Fold.
  Context {V T: Type} {eqT: relation T} {eqRT: Equivalence eqT}.

  Section FoldExtRestr.
    (* The operation can change for elements that are not even in the list. *)
    Lemma fold_ext_restr op1 op2 (t1 t2: T) (l1 l2: list V):
      l1 = l2 -> t1 = t2 -> (forall k t, k ∈ l1 -> op1 k t = op2 k t) ->
      fold_right op1 t1 l1 = fold_right op2 t2 l2.
    Proof.
      move=>? ?. subst l2 t2. induction l1; intros Heqop.
      - reflexivity.
      - simpl. erewrite IHl1.
        + apply Heqop. left. reflexivity.
        + move=>k t Hin. apply Heqop. right. assumption.
    Qed.
  End FoldExtRestr.

  Section FoldExt.
    Context (op1 op2: V -> T -> T).
    Context {op1_proper: Proper (eq ==> eqT ==> eqT) op1}.
    Context {op2_proper: Proper (eq ==> eqT ==> eqT) op2}.
    Context {op_eq: forall v t, eqT (op1 v t) (op2 v t)}.

    Lemma fold_ext: forall t1 t2, eqT t1 t2 -> forall l, eqT (fold_right op1 t1 l) (fold_right op2 t2 l).
    Proof.
      intros ? ? EQt ?. induction l.
      - exact EQt.
      - simpl. rewrite IHl. apply op_eq.
    Qed.
  End FoldExt.

  Section FoldPerm.
    Context (op: V -> T -> T) {op_proper: Proper (eq ==> eqT ==> eqT) op}.

    Definition NoDup_Perm (l1 l2: list V): Prop :=
      NoDup l1 /\ NoDup l2 /\ (forall v, v ∈ l1 <-> v ∈ l2).
    
    Lemma NoDup_Perm_len l1 l2:
      NoDup_Perm l1 l2 -> length l1 = length l2.
    Proof.
      revert l2. induction l1; induction l2; intros [Hnod1 [Hnod2 Heq]]; admit.
    Qed.
    
    Lemma fold_perm (l1 l2: list V) (t1: T):
      NoDup_Perm l1 l2 ->
      eqT (fold_right op t1 l1) (fold_right op t1 l2).
    Proof.
      admit.
    Qed.
  End FoldPerm.
End Fold.
