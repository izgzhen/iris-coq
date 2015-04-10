Require Import Ssreflect.ssreflect.
Require Import CSetoid.

(* Reflexive, transitive closure of relations *)
Section ReflTransClosure.
  Context {T: Type} {eqT: Setoid T} (R: relation T).
  Context {R_proper: Proper (equiv ==> equiv ==> equiv) R}.

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
  | n_O ρ ρ' : ρ == ρ' -> n_closure O ρ ρ'
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

Section ReflTransClosureProps.
  Context {T: Type} {eqT: Setoid T}.

  Global Instance refl_trans_closure_r_equiv: Proper (equiv ==> equiv) refl_trans_closure.
  Proof.
    assert(Himpl: forall R1 R2, R1 == R2 -> forall t1 t2, refl_trans_closure R1 t1 t2 -> refl_trans_closure R2 t1 t2).
    { move=>R1 R2 EQR t1 t2. induction 1.
      - apply rt_refl. assumption.
      - eapply rt_step.
        + eapply EQR. eassumption.
        + assumption.
    }
    move=>R1 R2 EQR t1 t2.
    split; apply Himpl; assumption || symmetry; assumption.
  Qed.
End ReflTransClosureProps.    