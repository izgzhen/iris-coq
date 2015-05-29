Require Import Ssreflect.ssreflect.
Require Import Omega CSetoid List ListSet.

Set Bullet Behavior "Strict Subproofs".

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

  Lemma filter_dupes_ext dupes1 dupes2 l:
    (forall k, k ∈ dupes1 <-> k ∈ dupes2) ->
    filter_dupes dupes1 l = filter_dupes dupes2 l.
  Proof.
    revert dupes1 dupes2. induction l; intros ? ? Heq.
    - reflexivity.
    - simpl. destruct (set_mem dec_eq a dupes1) eqn:EQsm.
      + apply set_mem_correct1 in EQsm. apply Heq in EQsm.
        eapply set_mem_correct2 in EQsm. erewrite EQsm.
        now apply IHl.
      + apply set_mem_complete1 in EQsm. unfold set_In in EQsm.
        rewrite ->Heq in EQsm.
        eapply set_mem_complete2 in EQsm. erewrite EQsm.
        f_equal. apply IHl. move=>k. simpl.
        specialize (Heq k). tauto.
  Qed.

  Lemma filter_dupes_redundant dupes l a:
    ~a ∈ l ->
    filter_dupes (a::dupes) l = filter_dupes dupes l.
  Proof.
    revert dupes. induction l; intros dupes Hnin; simpl.
    - reflexivity.
    - destruct (dec_eq a0 a) as [EQ|NEQ].
      { exfalso. subst. apply Hnin. left. reflexivity. }
      destruct (set_mem dec_eq a0 dupes) eqn:EQsm.
      { apply IHl. move=>Hin. apply Hnin. right. assumption. }
      f_equal. etransitivity; last first.
      + eapply IHl. move=>Hin. apply Hnin. right. assumption.
      + apply filter_dupes_ext. move=>k. simpl. tauto.
  Qed.

End FilterDup.

Section ListMax.
  Definition list_max := fold_right max 0.

  Lemma list_gax_ge l n:
    In n l -> n <= list_max l.
  Proof.
    revert n. induction l; intros n HIn.
    - destruct HIn.
    - simpl. apply NPeano.Nat.max_le_iff. destruct HIn as [Heq|HIn].
      + left. subst. reflexivity.
      + right. now apply IHl.
  Qed.
End ListMax.

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
    Context {eqV: DecEq V}.

    Definition NoDup_Perm (l1 l2: list V): Prop :=
      NoDup l1 /\ NoDup l2 /\ (forall v, v ∈ l1 <-> v ∈ l2).

    Context (op: V -> T -> T) {op_proper: Proper (eq ==> eqT ==> eqT) op}.
    Context (op_comm: forall v1 v2, forall t, eqT (compose (op v1) (op v2) t) (compose (op v2) (op v1) t)).

    Lemma fold_tofront (l: list V) a (t1: T):
      NoDup l -> a ∈ l ->
      eqT (fold_right op t1 (a::filter_dupes [a] l)) (fold_right op t1 l).
    Proof.
      induction l; intros Hnod Hin.
      - exfalso. apply Hin.
      - simpl. destruct (dec_eq a0 a) as [EQ|NEQ].
        + subst a. apply op_proper; first reflexivity.
          rewrite filter_dupes_id; first reflexivity.
          assumption.
        + simpl. etransitivity; first now eapply op_comm.
          simpl. apply op_proper; first reflexivity.
          assert (Heq: filter_dupes [a0; a] l = filter_dupes [a] l).
          { apply filter_dupes_redundant. inversion Hnod; subst; assumption. }
          rewrite Heq. eapply IHl.
          * inversion Hnod; subst; assumption.
          * destruct Hin; last assumption. contradiction.
    Qed.
    
    Lemma fold_perm (l1 l2: list V) (t1: T):
      NoDup_Perm l1 l2 ->
      eqT (fold_right op t1 l1) (fold_right op t1 l2).
    Proof.
      revert l2. induction l1; intros l2 Hnodp;
      move:(Hnodp)=>[Hnod1 [Hnod2 Heq]].
      - destruct l2 as [|a l2]; first reflexivity.
        exfalso. destruct (Heq a) as [_ Hin]. apply Hin.
        left. reflexivity.
      - simpl.
        assert (Hin2: a ∈ l2).
        { apply Heq. left. reflexivity. }
        etransitivity; last first.
        + eapply fold_tofront; eassumption.
        + simpl. apply op_proper; first reflexivity.
          apply IHl1. split; last split; last split.
          * inversion Hnod1; subst; assumption.
          * apply filter_dupes_nodup.
          * move=>Hin. apply filter_dupes_in.
            { move=>[EQ|[]].
              inversion Hnod1; subst. contradiction. }
            apply Heq. right. assumption.
          * move=>Hin. apply filter_dupes_isin in Hin.
            destruct Hin as [Hneq Hin]. apply Heq in Hin.
            destruct Hin as [EQ|?]; last assumption.
            subst a. exfalso. apply Hneq. now left.
    Qed.
  End FoldPerm.
End Fold.
