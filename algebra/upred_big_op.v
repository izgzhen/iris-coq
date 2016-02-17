From algebra Require Export upred.
From prelude Require Import gmap fin_collections.

(** * Big ops over lists *)
(* These are the basic building blocks for other big ops *)
Fixpoint uPred_big_and {M} (Ps : list (uPred M)) : uPred M:=
  match Ps with [] => True | P :: Ps => P ∧ uPred_big_and Ps end%I.
Instance: Params (@uPred_big_and) 1.
Notation "'Π∧' Ps" := (uPred_big_and Ps) (at level 20) : uPred_scope.
Fixpoint uPred_big_sep {M} (Ps : list (uPred M)) : uPred M :=
  match Ps with [] => True | P :: Ps => P ★ uPred_big_sep Ps end%I.
Instance: Params (@uPred_big_sep) 1.
Notation "'Π★' Ps" := (uPred_big_sep Ps) (at level 20) : uPred_scope.

(** * Other big ops *)
(** We use a type class to obtain overloaded notations *)
Definition uPred_big_sepM {M} `{Countable K} {A}
    (m : gmap K A) (P : K → A → uPred M) : uPred M :=
  uPred_big_sep (curry P <$> map_to_list m).
Instance: Params (@uPred_big_sepM) 6.
Notation "'Π★{map' m } P" := (uPred_big_sepM m P)
  (at level 20, m at level 10, format "Π★{map  m }  P") : uPred_scope.

Definition uPred_big_sepS {M} `{Countable A}
  (X : gset A) (P : A → uPred M) : uPred M := uPred_big_sep (P <$> elements X).
Instance: Params (@uPred_big_sepS) 5.
Notation "'Π★{set' X } P" := (uPred_big_sepS X P)
  (at level 20, X at level 10, format "Π★{set  X }  P") : uPred_scope.

(** * Always stability for lists *)
Class AlwaysStableL {M} (Ps : list (uPred M)) :=
  always_stableL : Forall AlwaysStable Ps.
Arguments always_stableL {_} _ {_}.

Section big_op.
Context {M : cmraT}.
Implicit Types Ps Qs : list (uPred M).
Implicit Types A : Type.

(* Big ops *)
Global Instance big_and_proper : Proper ((≡) ==> (≡)) (@uPred_big_and M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.
Global Instance big_sep_proper : Proper ((≡) ==> (≡)) (@uPred_big_sep M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

Global Instance big_and_ne n :
  Proper (Forall2 (dist n) ==> dist n) (@uPred_big_and M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.
Global Instance big_sep_ne n :
  Proper (Forall2 (dist n) ==> dist n) (@uPred_big_sep M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

Global Instance big_and_mono' : Proper (Forall2 (⊑) ==> (⊑)) (@uPred_big_and M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.
Global Instance big_sep_mono' : Proper (Forall2 (⊑) ==> (⊑)) (@uPred_big_sep M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

Global Instance big_and_perm : Proper ((≡ₚ) ==> (≡)) (@uPred_big_and M).
Proof.
  induction 1 as [|P Ps Qs ? IH|P Q Ps|]; simpl; auto.
  - by rewrite IH.
  - by rewrite !assoc (comm _ P).
  - etransitivity; eauto.
Qed.
Global Instance big_sep_perm : Proper ((≡ₚ) ==> (≡)) (@uPred_big_sep M).
Proof.
  induction 1 as [|P Ps Qs ? IH|P Q Ps|]; simpl; auto.
  - by rewrite IH.
  - by rewrite !assoc (comm _ P).
  - etransitivity; eauto.
Qed.

Lemma big_and_app Ps Qs : (Π∧ (Ps ++ Qs))%I ≡ (Π∧ Ps ∧ Π∧ Qs)%I.
Proof. by induction Ps as [|?? IH]; rewrite /= ?left_id -?assoc ?IH. Qed.
Lemma big_sep_app Ps Qs : (Π★ (Ps ++ Qs))%I ≡ (Π★ Ps ★ Π★ Qs)%I.
Proof. by induction Ps as [|?? IH]; rewrite /= ?left_id -?assoc ?IH. Qed.

Lemma big_and_contains Ps Qs : Qs `contains` Ps → (Π∧ Ps)%I ⊑ (Π∧ Qs)%I.
Proof.
  intros [Ps' ->]%contains_Permutation. by rewrite big_and_app uPred.and_elim_l.
Qed.
Lemma big_sep_contains Ps Qs : Qs `contains` Ps → (Π★ Ps)%I ⊑ (Π★ Qs)%I.
Proof.
  intros [Ps' ->]%contains_Permutation. by rewrite big_sep_app uPred.sep_elim_l.
Qed.

Lemma big_sep_and Ps : (Π★ Ps) ⊑ (Π∧ Ps).
Proof. by induction Ps as [|P Ps IH]; simpl; auto with I. Qed.

Lemma big_and_elem_of Ps P : P ∈ Ps → (Π∧ Ps) ⊑ P.
Proof. induction 1; simpl; auto with I. Qed.
Lemma big_sep_elem_of Ps P : P ∈ Ps → (Π★ Ps) ⊑ P.
Proof. induction 1; simpl; auto with I. Qed.

(* Big ops over finite maps *)
Section gmap.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types P : K → A → uPred M.

  Lemma big_sepM_mono P Q m1 m2 :
    m2 ⊆ m1 → (∀ x k, m2 !! k = Some x → P k x ⊑ Q k x) →
    (Π★{map m1} P) ⊑ (Π★{map m2} Q).
  Proof.
    intros HX HP. transitivity (Π★{map m2} P)%I.
    - by apply big_sep_contains, fmap_contains, map_to_list_contains.
    - apply big_sep_mono', Forall2_fmap, Forall2_Forall.
      apply Forall_forall=> -[i x] ? /=. by apply HP, elem_of_map_to_list.
  Qed.

  Global Instance big_sepM_ne m n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> (dist n))
           (uPred_big_sepM (M:=M) m).
  Proof.
    intros P1 P2 HP. apply big_sep_ne, Forall2_fmap.
    apply Forall2_Forall, Forall_true=> -[i x]; apply HP.
  Qed.
  Global Instance big_sepM_proper m :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (≡))
           (uPred_big_sepM (M:=M) m).
  Proof.
    intros P1 P2 HP; apply equiv_dist=> n.
    apply big_sepM_ne=> k x; apply equiv_dist, HP.
  Qed.
  Global Instance big_sepM_mono' m :
    Proper (pointwise_relation _ (pointwise_relation _ (⊑)) ==> (⊑))
           (uPred_big_sepM (M:=M) m).
  Proof. intros P1 P2 HP. apply big_sepM_mono; intros; [done|apply HP]. Qed.

  Lemma big_sepM_empty P : (Π★{map ∅} P)%I ≡ True%I.
  Proof. by rewrite /uPred_big_sepM map_to_list_empty. Qed.
  Lemma big_sepM_insert P (m : gmap K A) i x :
    m !! i = None → (Π★{map <[i:=x]> m} P)%I ≡ (P i x ★ Π★{map m} P)%I.
  Proof. intros ?; by rewrite /uPred_big_sepM map_to_list_insert. Qed.
  Lemma big_sepM_singleton P i x : (Π★{map {[i := x]}} P)%I ≡ (P i x)%I.
  Proof.
    rewrite -insert_empty big_sepM_insert/=; last auto using lookup_empty.
    by rewrite big_sepM_empty right_id.
  Qed.

  Lemma big_sepM_sep P Q m :
    (Π★{map m} (λ i x, P i x ★ Q i x))%I ≡ (Π★{map m} P ★ Π★{map m} Q)%I.
  Proof.
    rewrite /uPred_big_sepM. induction (map_to_list m); simpl;
      first by rewrite right_id.
    destruct a. rewrite IHl /= -!assoc. apply uPred.sep_proper; first done.
    rewrite !assoc [(_ ★ Q _ _)%I]comm -!assoc. apply uPred.sep_proper; done.
  Qed.
End gmap.

(* Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types P : A → uPred M.

  Lemma big_sepS_mono P Q X Y :
    Y ⊆ X → (∀ x, x ∈ Y → P x ⊑ Q x) → (Π★{set X} P) ⊑ (Π★{set Y} Q).
  Proof.
    intros HX HP. transitivity (Π★{set Y} P)%I.
    - by apply big_sep_contains, fmap_contains, elements_contains.
    - apply big_sep_mono', Forall2_fmap, Forall2_Forall.
      apply Forall_forall=> x ? /=. by apply HP, elem_of_elements.
  Qed.

  Lemma big_sepS_ne X n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (uPred_big_sepS (M:=M) X).
  Proof.
    intros P1 P2 HP. apply big_sep_ne, Forall2_fmap.
    apply Forall2_Forall, Forall_true=> x; apply HP.
  Qed.
  Lemma big_sepS_proper X :
    Proper (pointwise_relation _ (≡) ==> (≡)) (uPred_big_sepS (M:=M) X).
  Proof.
    intros P1 P2 HP; apply equiv_dist=> n.
    apply big_sepS_ne=> x; apply equiv_dist, HP.
  Qed.
  Lemma big_sepS_mono' X :
    Proper (pointwise_relation _ (⊑) ==> (⊑)) (uPred_big_sepS (M:=M) X).
  Proof. intros P1 P2 HP. apply big_sepS_mono; naive_solver. Qed.

  Lemma big_sepS_empty P : (Π★{set ∅} P)%I ≡ True%I.
  Proof. by rewrite /uPred_big_sepS elements_empty. Qed.
  Lemma big_sepS_insert P X x :
    x ∉ X → (Π★{set {[ x ]} ∪ X} P)%I ≡ (P x ★ Π★{set X} P)%I.
  Proof. intros. by rewrite /uPred_big_sepS elements_union_singleton. Qed.
  Lemma big_sepS_delete P X x :
    x ∈ X → (Π★{set X} P)%I ≡ (P x ★ Π★{set X ∖ {[ x ]}} P)%I.
  Proof.
    intros. rewrite -big_sepS_insert; last set_solver.
    by rewrite -union_difference_L; last set_solver.
  Qed.
  Lemma big_sepS_singleton P x : (Π★{set {[ x ]}} P)%I ≡ (P x)%I.
  Proof. intros. by rewrite /uPred_big_sepS elements_singleton /= right_id. Qed.

  Lemma big_sepS_sep P Q X :
    (Π★{set X} (λ x, P x ★ Q x))%I ≡ (Π★{set X} P ★ Π★{set X} Q)%I.
  Proof.
    rewrite /uPred_big_sepS. induction (elements X); simpl;
      first by rewrite right_id.
    rewrite IHl -!assoc. apply uPred.sep_proper; first done.
    rewrite !assoc [(_ ★ Q a)%I]comm -!assoc. apply uPred.sep_proper; done.
  Qed.
End gset.

(* Always stable *)
Local Notation AS := AlwaysStable.
Local Notation ASL := AlwaysStableL.
Global Instance big_and_always_stable Ps : ASL Ps → AS (Π∧ Ps).
Proof. induction 1; apply _. Qed.
Global Instance big_sep_always_stable Ps : ASL Ps → AS (Π★ Ps).
Proof. induction 1; apply _. Qed.

Global Instance nil_always_stable : ASL (@nil (uPred M)).
Proof. constructor. Qed.
Global Instance cons_always_stable P Ps : AS P → ASL Ps → ASL (P :: Ps).
Proof. by constructor. Qed.
Global Instance app_always_stable Ps Ps' : ASL Ps → ASL Ps' → ASL (Ps ++ Ps').
Proof. apply Forall_app_2. Qed.
Global Instance zip_with_always_stable {A B} (f : A → B → uPred M) xs ys :
  (∀ x y, AS (f x y)) → ASL (zip_with f xs ys).
Proof. unfold ASL=> ?; revert ys; induction xs=> -[|??]; constructor; auto. Qed.
End big_op.
