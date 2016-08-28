From iris.algebra Require Import upred.
Import upred.

(* In this file we show that the rvs can be thought of a kind of
   step-indexed double-negation when our meta-logic is classical *)

(* To define this, we need a way to talk about iterated later modalities: *)
Definition uPred_laterN {M} (n : nat) (P : uPred M) : uPred M :=
  Nat.iter n uPred_later P.
Instance: Params (@uPred_laterN) 2.
Notation "▷^ n P" := (uPred_laterN n P)
  (at level 20, n at level 9, right associativity,
   format "▷^ n  P") : uPred_scope.

Definition uPred_nnvs {M} (P: uPred M) : uPred M :=
  ∀ n, (P -★ ▷^n False) -★ ▷^n False.

Notation "|=n=> Q" := (uPred_nnvs Q)
  (at level 99, Q at level 200, format "|=n=>  Q") : uPred_scope.
Notation "P =n=> Q" := (P ⊢ |=n=> Q)
  (at level 99, Q at level 200, only parsing) : C_scope.
Notation "P =n=★ Q" := (P -★ |=n=> Q)%I
  (at level 99, Q at level 200, format "P  =n=★  Q") : uPred_scope.

(* Our goal is to prove that:
  (1) |=n=> has (nearly) all the properties of the |=r=> modality that are used in Iris
  (2) If our meta-logic is classical, then |=n=> and |=r=> are equivalent
*)

Section rvs_nn.
Context {M : ucmraT}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.
Implicit Types x : M.
Import uPred.

(* Helper lemmas about iterated later modalities *)
Lemma laterN_big n a x φ: ✓{n} x →  a ≤ n → (▷^a (■ φ))%I n x → φ.
Proof.
  induction 2 as [| ?? IHle].
  - induction a; repeat (rewrite //= || uPred.unseal). 
    intros Hlater. apply IHa; auto using cmra_validN_S.
    move:Hlater; repeat (rewrite //= || uPred.unseal). 
  - intros. apply IHle; auto using cmra_validN_S.
    eapply uPred_closed; eauto using cmra_validN_S.
Qed.

Lemma laterN_small n a x φ: ✓{n} x →  n < a → (▷^a (■ φ))%I n x.
Proof.
  induction 2.
  - induction n as [| n IHn]; [| move: IHn];
      repeat (rewrite //= || uPred.unseal).
    naive_solver eauto using cmra_validN_S.
  - induction n as [| n IHn]; [| move: IHle];
      repeat (rewrite //= || uPred.unseal).
    red; rewrite //=. intros.
    eapply (uPred_closed _ _ (S n)); eauto using cmra_validN_S.
Qed.

(* First we prove that rvs implies nn *)
Lemma rvs_nn P: (|=r=> P) ⊢ |=n=> P.
Proof.
  split. rewrite /uPred_nnvs. repeat uPred.unseal. intros n x ? Hrvs a.
  red; rewrite //= => n' yf ??.
  edestruct Hrvs as (x'&?&?); eauto.
  case (decide (a ≤ n')).
  - intros Hle Hwand.
    exfalso. eapply laterN_big; last (uPred.unseal; eapply (Hwand n' x')); eauto.
    * rewrite comm. done. 
    * rewrite comm. done. 
  - intros; assert (n' < a). omega.
    move: laterN_small. uPred.unseal.
    naive_solver.
Qed.

Lemma nn_intro P : P =n=> P.
Proof. apply forall_intro=>?. apply wand_intro_l, wand_elim_l. Qed.
Lemma nn_mono P Q : (P ⊢ Q) → (|=n=> P) =n=> Q.
Proof.
  intros HPQ. apply forall_intro=>n.
  apply wand_intro_l.  rewrite -{1}HPQ.
  rewrite /uPred_nnvs (forall_elim n).
  apply wand_elim_r.
Qed.
(* Question: is there a clean direct proof of this? *)
(*
Lemma nn_trans P : (|=n=> |=n=> P) =n=> P.
Proof.
  apply forall_intro=>n. apply wand_intro_l.
  rewrite /uPred_nnvs.
  rewrite {1}(nn_intro (P -★ ▷^ n False)).
  rewrite /uPred_nnvs. rewrite comm (forall_elim n).
  apply wand_elim_r. Qed.
*)
Lemma nn_frame_r P R : (|=n=> P) ★ R =n=> P ★ R.
Proof.
  apply forall_intro=>n. apply wand_intro_r.
  rewrite (comm _ P) -wand_curry.
  rewrite /uPred_nnvs (forall_elim n).
  by rewrite -assoc wand_elim_r wand_elim_l.
Qed.
Lemma nn_ownM_updateP x (Φ : M → Prop) :
  x ~~>: Φ → uPred_ownM x =n=> ∃ y, ■ Φ y ∧ uPred_ownM y.
Proof. intros. rewrite -rvs_nn. by apply rvs_ownM_updateP. Qed.
Lemma except_last_nn P : ◇ (|=n=> P) ⊢ (|=n=> ◇ P).
Proof.
  rewrite /uPred_except_last. apply or_elim.
  - by rewrite -nn_intro -or_intro_l.
  - by apply nn_mono, or_intro_r. 
Qed.

(* Now we show, nn implies rvs, for which we need a classical axiom: *)
Require Coq.Logic.Classical_Pred_Type.
Lemma nn_rvs P:  (|=n=> P) ⊢ (|=r=> P).
Proof.
  rewrite /uPred_nnvs.
  split. uPred.unseal; red; rewrite //=.
  intros n x ? Hforall k yf Hle ?.
  apply Classical_Pred_Type.not_all_not_ex.
  intros Hfal.
  specialize (Hforall k k).
  eapply laterN_big; last (uPred.unseal; red; rewrite //=; eapply Hforall);
    eauto.
  red; rewrite //= => n' x' ???.
  case (decide (n' = k)); intros.
  - subst. exfalso. eapply Hfal. rewrite (comm op); eauto.
  - assert (n' < k). omega.
    move: laterN_small. uPred.unseal. naive_solver.
Qed.

(* Questions:
   1) Can one prove an adequacy theorem for the |=n=> modality without axioms?
   2) If not, can we prove a weakened form of adequacy, such as :

      Lemma adequacy' φ n : (True ⊢ Nat.iter n (λ P, |=n=> ▷ P) (■ φ)) → ¬¬ φ.

   3) Do the basic properties of the |=r=> modality (rvs_intro, rvs_mono, rvs_trans, rvs_frame_r,
      rvs_ownM_updateP, and adequacy) characterize |=r=>?
 *)
End rvs_nn.