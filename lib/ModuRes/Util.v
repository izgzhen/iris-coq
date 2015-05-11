Require Import Ssreflect.ssreflect.
Require Import Setoid SetoidClass.
Require Import List.

Ltac find_rewrite1 t0 t1 := match goal with
                            | H: t0 = t1 |- _ => rewrite-> H
                            | H: t0 == t1 |- _ => rewrite-> H
                            | H: t1 = t0 |- _ => rewrite<- H
                            | H: t1 == t0 |- _ => rewrite<- H
                            end.
Ltac find_rewrite2 t0 t1 t2 := find_rewrite1 t0 t1; find_rewrite1 t1 t2.
Ltac find_rewrite3 t0 t1 t2 t3 := find_rewrite2 t0 t1 t2; find_rewrite1 t2 t3.


Tactic Notation "ddes" constr(T) "at" integer_list(pos) "as" simple_intropattern(pat) "deqn:" ident(EQ) :=
  (generalize (@eq_refl _ (T)) as EQ; pattern (T) at pos;
   destruct (T) as pat; move => EQ).

Ltac split_conjs := repeat (match goal with [ |- _ /\ _ ] => split end).

(* TODO: Is this already defined somewhere? *)
Class DecEq (T : Type) := dec_eq : forall (t1 t2: T), {t1 = t2} + {t1 <> t2}.

(* Stuff that ought to be in the stdlib... *)
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
