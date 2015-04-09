Require Import Ssreflect.ssreflect.
Require Import SetoidTactics SetoidClass.

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

(* Reflexive, transitive closure of relations *)
Section ReflTransClosure.
  Context {T: Type} (R: relation T).
  Context {eqT: Setoid T} {R_proper: Proper (equiv ==> equiv ==> equiv) R}.

  Inductive refl_trans_closure : relation T :=
  | rt_refl ρ ρ' : equiv ρ ρ' -> refl_trans_closure ρ ρ'
  | rt_step ρ1 ρ2 ρ3 : R ρ1 ρ2 -> refl_trans_closure ρ2 ρ3 -> refl_trans_closure ρ1 ρ3.

  Global Instance refl_trans_closure_equiv: Proper (equiv ==> equiv ==> equiv) refl_trans_closure.
  Proof.
    apply proper_sym_impl_iff_2; try (now apply _).
    move=>r1 r2 EQr s1 s2 EQs H. revert r2 s2 EQr EQs. induction H; intros.
    - apply: rt_refl. by rewrite -EQr -EQs.
    - eapply rt_step.
      + rewrite -EQr; eassumption.
      + eapply IHrefl_trans_closure; eassumption || reflexivity.
  Qed.

  Lemma rt_trans ρ1 ρ2 ρ3 : refl_trans_closure ρ1 ρ2 -> refl_trans_closure ρ2 ρ3 -> refl_trans_closure ρ1 ρ3.
  Proof.
    revert ρ3. induction 1.
    - rewrite H. tauto.
    - move=>H'. eauto using refl_trans_closure.
  Qed.

  Lemma rt_onestep ρ1 ρ2: R ρ1 ρ2 -> refl_trans_closure ρ1 ρ2.
  Proof.
    move=>H.
    eapply rt_step; last eapply rt_refl.
    - eassumption.
    - reflexivity.
  Qed.
  
  Inductive n_closure : nat -> relation T :=
  | n_O ρ ρ' : equiv ρ ρ' -> n_closure O ρ ρ'
  | n_S ρ1 ρ2 ρ3 n
            (HS  : R ρ1 ρ2)
            (HSN : n_closure n ρ2 ρ3) :
      n_closure (S n) ρ1 ρ3.

  Lemma refl_trans_n {ρ1 ρ2} :
    refl_trans_closure ρ1 ρ2 -> exists n, n_closure n ρ1 ρ2.
  Proof.
    induction 1.
    - eexists. eauto using n_closure.
    - destruct IHrefl_trans_closure as [n IH]. eexists. eauto using n_closure.
  Qed.

  Lemma n_refl_trans {n ρ1 ρ2}:
    n_closure n ρ1 ρ2 -> refl_trans_closure ρ1 ρ2.
  Proof.
    induction 1; now eauto using refl_trans_closure.
  Qed.
End ReflTransClosure.
