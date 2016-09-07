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

Section rvs_nnvs.
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

(* It is easy to show that most of the basic properties of rvs that
   are used throughout Iris hold for nnvs. 

   In fact, the first three properties that follow hold for any
   modality of the form (- -★ Q) -★ Q for arbitrary Q. The situation
   here is slightly different, because nnvs is of the form 
   ∀ n, (- -★ (Q n)) -★ (Q n), but the proofs carry over straightforwardly.

 *)

Lemma nnvs_intro P : P =n=> P.
Proof. apply forall_intro=>?. apply wand_intro_l, wand_elim_l. Qed.
Lemma nnvs_mono P Q : (P ⊢ Q) → (|=n=> P) =n=> Q.
Proof.
  intros HPQ. apply forall_intro=>n.
  apply wand_intro_l.  rewrite -{1}HPQ.
  rewrite /uPred_nnvs (forall_elim n).
  apply wand_elim_r.
Qed.
Lemma nnvs_frame_r P R : (|=n=> P) ★ R =n=> P ★ R.
Proof.
  apply forall_intro=>n. apply wand_intro_r.
  rewrite (comm _ P) -wand_curry.
  rewrite /uPred_nnvs (forall_elim n).
  by rewrite -assoc wand_elim_r wand_elim_l.
Qed.
Lemma nnvs_ownM_updateP x (Φ : M → Prop) :
  x ~~>: Φ → uPred_ownM x =n=> ∃ y, ■ Φ y ∧ uPred_ownM y.
Proof. 
  intros Hrvs. split. rewrite /uPred_nnvs. repeat uPred.unseal. 
  intros n y ? Hown a.
  red; rewrite //= => n' yf ??.
  inversion Hown as (x'&Hequiv).
  edestruct (Hrvs n' (Some (x' ⋅ yf))) as (y'&?&?); eauto.
  { by rewrite //= assoc -(dist_le _ _ _ _ Hequiv). }
  case (decide (a ≤ n')).
  - intros Hle Hwand.
    exfalso. eapply laterN_big; last (uPred.unseal; eapply (Hwand n' (y' ⋅ x'))); eauto.
    * rewrite comm -assoc. done. 
    * rewrite comm -assoc. done. 
    * eexists. split; eapply uPred_mono; red; rewrite //=; eauto.
  - intros; assert (n' < a). omega.
    move: laterN_small. uPred.unseal.
    naive_solver.
Qed.

(* However, the transitivity property seems to be much harder to
   prove. This is surprising, because transitivity does hold for 
   modalities of the form (- -★ Q) -★ Q. What goes wrong when we quantify
   now over n? 
 *)

Remark nnvs_trans P: (|=n=> |=n=> P) ⊢ (|=n=> P).
Proof.
  rewrite /uPred_nnvs.
  apply forall_intro=>a. apply wand_intro_l.
  rewrite (forall_elim a).
  rewrite (nnvs_intro (P -★ _)).
  rewrite /uPred_nnvs.
  (* Oops -- the exponents of the later modality don't match up! *)
Abort.

(* Instead, we will need to prove this in the model. We start by showing that 
   nnvs is the limit of a the following sequence:

   (- -★ False) - ★ False,
   (- -★ ▷ False) - ★ ▷ False ∧ (- -★ False) - ★ False,
   (- -★ ▷^2 False) - ★ ▷^2 False ∧ (- -★ ▷ False) - ★ ▷ False ∧ (- -★ False) - ★ False,
   ...

   Then, it is easy enough to show that each of the uPreds in this sequence
   is transitive. It turns out that this implies that nnvs is transitive. *)
   

(* The definition of the sequence above: *)
Fixpoint uPred_nnvs_k {M} k (P: uPred M) : uPred M :=
  ((P -★ ▷^k False) -★ ▷^k False) ∧
  match k with 
    O => True
  | S k' => uPred_nnvs_k k' P
  end.

Notation "|=n=>_ k Q" := (uPred_nnvs_k k Q)
  (at level 99, k at level 9, Q at level 200, format "|=n=>_ k  Q") : uPred_scope.


(* One direction of the limiting process is easy -- nnvs implies nnvs_k for each k *)
Lemma nnvs_trunc1 k P: (|=n=> P) ⊢ |=n=>_k P.
Proof.
  induction k. 
  - rewrite /uPred_nnvs_k /uPred_nnvs. 
    rewrite (forall_elim 0) //= right_id //.
  - simpl. apply and_intro; auto.
    rewrite /uPred_nnvs. 
    rewrite (forall_elim (S k)) //=.
Qed.

Lemma nnvs_k_elim n k P: n ≤ k → ((|=n=>_k P) ★ (P -★ (▷^n False)) ⊢  (▷^n False))%I.
Proof.
  induction k.
  - inversion 1; subst; rewrite //= ?right_id. apply wand_elim_l.
  - inversion 1; subst; rewrite //= ?right_id.
    * rewrite and_elim_l. apply wand_elim_l.
    * rewrite and_elim_r IHk //.
Qed.

Lemma nnvs_k_unfold k P:
  (|=n=>_(S k) P) ⊣⊢ ((P -★ (▷^(S k) False)) -★ (▷^(S k) False)) ∧ (|=n=>_k P).
Proof. done.  Qed.
Lemma nnvs_k_unfold' k P n x:
  (|=n=>_(S k) P)%I n x ↔ (((P -★ (▷^(S k) False)) -★ (▷^(S k) False)) ∧ (|=n=>_k P))%I n x.
Proof. done.  Qed.

Lemma nnvs_k_weaken k P: (|=n=>_(S k) P) ⊢ |=n=>_k P.
Proof. by rewrite nnvs_k_unfold and_elim_r. Qed.

(* Now we are ready to show nnvs is the limit -- ie, for each k, it is within distance k
   of the kth term of the sequence *)
Lemma nnvs_nnvs_k_dist k P: (|=n=> P)%I ≡{k}≡ (|=n=>_k P)%I.
  split; intros n' x Hle Hx. split.
  - by apply (nnvs_trunc1 k).
  - revert n' x Hle Hx; induction k; intros n' x Hle Hx;
      rewrite ?nnvs_k_unfold' /uPred_nnvs.
    * rewrite //=. unseal.
      inversion Hle; subst.
      intros (HnnP&_) n k' x' ?? HPF.
      case (decide (k' < n)).
      ** move: laterN_small; uPred.unseal; naive_solver.
      ** intros. exfalso. eapply HnnP; eauto.
         assert (n ≤ k'). omega.
         intros n'' x'' ???.
         specialize (HPF n'' x''). exfalso.
         eapply laterN_big; last (unseal; eauto).
         eauto. omega.
    * inversion Hle; subst.
      ** unseal. intros (HnnP&HnnP_IH) n k' x' ?? HPF.
         case (decide (k' < n)).
         *** move: laterN_small; uPred.unseal; naive_solver.
         *** intros. exfalso. assert (n ≤ k'). omega.
             assert (n = S k ∨ n < S k) as [->|] by omega.
             **** eapply laterN_big; eauto; unseal. eapply HnnP; eauto.
             **** move:nnvs_k_elim. unseal. intros Hnnvsk. 
                  eapply laterN_big; eauto. unseal.
                  eapply (Hnnvsk n k); first omega; eauto.
                  exists x, x'. split_and!; eauto. eapply uPred_closed; eauto.
                  eapply cmra_validN_op_l; eauto.
      ** intros HP. eapply IHk; auto.
         move:HP. unseal. intros (?&?); naive_solver.
Qed.

(* nnvs_k has a number of structural properties, including transitivity *)
Lemma nnvs_k_intro k P: P ⊢ (|=n=>_k P).
Proof.
  induction k; rewrite //= ?right_id.
  - apply wand_intro_l. apply wand_elim_l.
  - apply and_intro; auto. 
    apply wand_intro_l. apply wand_elim_l.
Qed.

Lemma nnvs_k_mono k P Q: (P ⊢ Q) → (|=n=>_k P) ⊢ (|=n=>_k Q).
Proof.
  induction k; rewrite //= ?right_id=>HPQ. 
  - do 2 (apply wand_mono; auto).
  - apply and_mono; auto; do 2 (apply wand_mono; auto).
Qed.
Instance nnvs_k_mono' k: Proper ((⊢) ==> (⊢)) (@uPred_nnvs_k M k).
Proof. by intros P P' HP; apply nnvs_k_mono. Qed.

Instance nnvs_k_ne k n : Proper (dist n ==> dist n) (@uPred_nnvs_k M k).
Proof. induction k; rewrite //= ?right_id=>P P' HP; by rewrite HP. Qed.
Lemma nnvs_k_proper k P Q: (P ⊣⊢ Q) → (|=n=>_k P) ⊣⊢ (|=n=>_k Q).
Proof. intros HP; apply (anti_symm (⊢)); eapply nnvs_k_mono; by rewrite HP. Qed.
Instance nnvs_k_proper' k: Proper ((⊣⊢) ==> (⊣⊢)) (@uPred_nnvs_k M k).
Proof. by intros P P' HP; apply nnvs_k_proper. Qed.

Lemma nnvs_k_trans k P: (|=n=>_k |=n=>_k P) ⊢ (|=n=>_k P).
Proof.
  revert P.
  induction k; intros P.
  - rewrite //= ?right_id. apply wand_intro_l. 
    rewrite {1}(nnvs_k_intro 0 (P -★ False)%I) //= ?right_id. apply wand_elim_r. 
  - rewrite {2}(nnvs_k_unfold k P).
    apply and_intro.
    * rewrite (nnvs_k_unfold k P). rewrite and_elim_l.
      rewrite nnvs_k_unfold. rewrite and_elim_l.
      apply wand_intro_l. 
      rewrite {1}(nnvs_k_intro (S k) (P -★ ▷^(S k) (False)%I)).
      rewrite nnvs_k_unfold and_elim_l. apply wand_elim_r.
    * do 2 rewrite nnvs_k_weaken //.
Qed.

Lemma nnvs_trans P : (|=n=> |=n=> P) =n=> P.
Proof.
  split=> n x ? Hnn.
  eapply nnvs_nnvs_k_dist in Hnn; eauto.
  eapply (nnvs_k_ne (n) n ((|=n=>_(n) P)%I)) in Hnn; eauto;
    [| symmetry; eapply nnvs_nnvs_k_dist].
  eapply nnvs_nnvs_k_dist; eauto.
  by apply nnvs_k_trans.
Qed.

(* Now that we have shown nnvs has all of the desired properties of
   rvs, we go further and show it is in fact equivalent to rvs! The
   direction from rvs to nnvs is similar to the proof of
   nnvs_ownM_updateP *)

Lemma rvs_nnvs P: (|=r=> P) ⊢ |=n=> P.
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

(* However, the other direction seems to need a classical axiom: *)
Section classical.
Context (not_all_not_ex: ∀ (P : M → Prop), ¬ (∀ n : M, ¬ P n) → ∃ n : M, P n).
Lemma nnvs_rvs P:  (|=n=> P) ⊢ (|=r=> P).
Proof.
  rewrite /uPred_nnvs.
  split. uPred.unseal; red; rewrite //=.
  intros n x ? Hforall k yf Hle ?.
  apply not_all_not_ex.
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
End classical.

(* We might wonder whether we can prove an adequacy lemma for nnvs. We could combine
   the adequacy lemma for rvs with the previous result to get adquacy for nnvs, but 
   this would rely on the classical axiom we needed to prove the equivalence! Can
   we establish adequacy without axioms? Unfortunately not, because adequacy for 
   nnvs would imply double negation elimination, which is classical: *)

Lemma nnvs_dne φ: True ⊢ (|=n=> (■(¬¬ φ → φ)): uPred M)%I.
Proof.
  rewrite /uPred_nnvs. apply forall_intro=>n.
  apply wand_intro_l. rewrite ?right_id. 
  assert (∀ φ, ¬¬¬¬φ → ¬¬φ) by naive_solver.
  assert (Hdne: ¬¬ (¬¬φ → φ)) by naive_solver.
  split. unseal. intros n' ?? Hvs.
  case (decide (n' < n)).
  - intros. move: laterN_small. unseal. naive_solver.
  - intros. assert (n ≤ n'). omega. 
    exfalso. specialize (Hvs n' ∅).
    eapply Hdne. intros Hfal.
    eapply laterN_big; eauto. 
    unseal. rewrite right_id in Hvs *; naive_solver.
Qed.

(* Nevertheless, we can prove a weaker form of adequacy (which is equvialent to adequacy
   under classical axioms) directly without passing through the proofs for rvs: *)
Lemma adequacy_helper1 P n k x:
  ✓{S n + k} x → ¬¬ (Nat.iter (S n) (λ P, |=n=> ▷ P)%I P (S n + k) x) 
            → ¬¬ (∃ x', ✓{n + k} (x') ∧ Nat.iter n (λ P, |=n=> ▷ P)%I P (n + k) (x')).
Proof.
  revert k P x. induction n.
  - rewrite /uPred_nnvs. unseal=> k P x Hx Hf1 Hf2.
    eapply Hf1. intros Hf3.
    eapply (laterN_big (S k) (S k)); eauto.
    specialize (Hf3 (S k) (S k) ∅). rewrite right_id in Hf3 *. unseal.
    intros Hf3. eapply Hf3; eauto.
    intros ??? Hx'. rewrite left_id in Hx' *=> Hx'.
    unseal. 
    assert (n' < S k ∨ n' = S k) as [|] by omega.
    * intros. move:(laterN_small n' (S k) x' False). rewrite //=. unseal. intros Hsmall. 
      eapply Hsmall; eauto.
    * subst. intros. exfalso. eapply Hf2. exists x'. split; eauto using cmra_validN_S.
  - intros k P x Hx. rewrite ?Nat_iter_S_r. 
    replace (S (S n) + k) with (S n + (S k)) by omega.
    replace (S n + k) with (n + (S k)) by omega.
    intros. eapply IHn. replace (S n + S k) with (S (S n) + k) by omega. eauto.
    rewrite ?Nat_iter_S_r. eauto.
Qed.

Lemma adequacy_helper2 P n k x:
  ✓{S n + k} x → ¬¬ (Nat.iter (S n) (λ P, |=n=> ▷ P)%I P (S n + k) x) 
            → ¬¬ (∃ x', ✓{k} (x') ∧ Nat.iter 0 (λ P, |=n=> ▷ P)%I P k (x')).
Proof.
  revert x. induction n.
  - specialize (adequacy_helper1 P 0). rewrite //=. naive_solver.
  - intros ?? Hfal%adequacy_helper1; eauto using cmra_validN_S.
    intros Hfal'. eapply Hfal. intros (x''&?&?).
    eapply IHn; eauto.
Qed.

Lemma adequacy φ n : (True ⊢ Nat.iter n (λ P, |=n=> ▷ P) (■ φ)) → ¬¬ φ.
Proof.
  cut (∀ x, ✓{S n} x → Nat.iter n (λ P, |=n=> ▷ P)%I (■ φ)%I (S n) x → ¬¬φ).
  { intros help H. eapply (help ∅); eauto using ucmra_unit_validN.
    eapply H; try unseal; eauto using ucmra_unit_validN. red; rewrite //=. }
  destruct n.
  - rewrite //=; unseal; auto.
  - intros ??? Hfal.
    eapply (adequacy_helper2 _ n 1); (replace (S n + 1) with (S (S n)) by omega); eauto.
    unseal. intros (x'&?&Hphi). simpl in *.
    eapply Hfal. auto.
Qed.

(* Open question:

   Do the basic properties of the |=r=> modality (rvs_intro, rvs_mono, rvs_trans, rvs_frame_r,
      rvs_ownM_updateP, and adequacy) uniquely characterize |=r=>?
*)

End rvs_nnvs.