From algebra Require Export upred.
From prelude Require Import gmap fin_collections.
Import uPred.

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
    (m : gmap K A) (Φ : K → A → uPred M) : uPred M :=
  uPred_big_sep (curry Φ <$> map_to_list m).
Instance: Params (@uPred_big_sepM) 6.
Notation "'Π★{map' m } Φ" := (uPred_big_sepM m Φ)
  (at level 20, m at level 10, format "Π★{map  m }  Φ") : uPred_scope.

Definition uPred_big_sepS {M} `{Countable A}
  (X : gset A) (Φ : A → uPred M) : uPred M := uPred_big_sep (Φ <$> elements X).
Instance: Params (@uPred_big_sepS) 5.
Notation "'Π★{set' X } Φ" := (uPred_big_sepS X Φ)
  (at level 20, X at level 10, format "Π★{set  X }  Φ") : uPred_scope.

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
  - etrans; eauto.
Qed.
Global Instance big_sep_perm : Proper ((≡ₚ) ==> (≡)) (@uPred_big_sep M).
Proof.
  induction 1 as [|P Ps Qs ? IH|P Q Ps|]; simpl; auto.
  - by rewrite IH.
  - by rewrite !assoc (comm _ P).
  - etrans; eauto.
Qed.

Lemma big_and_app Ps Qs : (Π∧ (Ps ++ Qs))%I ≡ (Π∧ Ps ∧ Π∧ Qs)%I.
Proof. by induction Ps as [|?? IH]; rewrite /= ?left_id -?assoc ?IH. Qed.
Lemma big_sep_app Ps Qs : (Π★ (Ps ++ Qs))%I ≡ (Π★ Ps ★ Π★ Qs)%I.
Proof. by induction Ps as [|?? IH]; rewrite /= ?left_id -?assoc ?IH. Qed.

Lemma big_and_contains Ps Qs : Qs `contains` Ps → (Π∧ Ps)%I ⊑ (Π∧ Qs)%I.
Proof.
  intros [Ps' ->]%contains_Permutation. by rewrite big_and_app and_elim_l.
Qed.
Lemma big_sep_contains Ps Qs : Qs `contains` Ps → (Π★ Ps)%I ⊑ (Π★ Qs)%I.
Proof.
  intros [Ps' ->]%contains_Permutation. by rewrite big_sep_app sep_elim_l.
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
  Implicit Types Φ Ψ : K → A → uPred M.

  Lemma big_sepM_mono Φ Ψ m1 m2 :
    m2 ⊆ m1 → (∀ x k, m2 !! k = Some x → Φ k x ⊑ Ψ k x) →
    (Π★{map m1} Φ) ⊑ (Π★{map m2} Ψ).
  Proof.
    intros HX HΦ. trans (Π★{map m2} Φ)%I.
    - by apply big_sep_contains, fmap_contains, map_to_list_contains.
    - apply big_sep_mono', Forall2_fmap, Forall2_Forall.
      apply Forall_forall=> -[i x] ? /=. by apply HΦ, elem_of_map_to_list.
  Qed.

  Global Instance big_sepM_ne m n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> (dist n))
           (uPred_big_sepM (M:=M) m).
  Proof.
    intros Φ1 Φ2 HΦ. apply big_sep_ne, Forall2_fmap.
    apply Forall2_Forall, Forall_true=> -[i x]; apply HΦ.
  Qed.
  Global Instance big_sepM_proper m :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (≡))
           (uPred_big_sepM (M:=M) m).
  Proof.
    intros Φ1 Φ2 HΦ; apply equiv_dist=> n.
    apply big_sepM_ne=> k x; apply equiv_dist, HΦ.
  Qed.
  Global Instance big_sepM_mono' m :
    Proper (pointwise_relation _ (pointwise_relation _ (⊑)) ==> (⊑))
           (uPred_big_sepM (M:=M) m).
  Proof. intros Φ1 Φ2 HΦ. apply big_sepM_mono; intros; [done|apply HΦ]. Qed.

  Lemma big_sepM_empty Φ : (Π★{map ∅} Φ)%I ≡ True%I.
  Proof. by rewrite /uPred_big_sepM map_to_list_empty. Qed.
  Lemma big_sepM_insert Φ (m : gmap K A) i x :
    m !! i = None → (Π★{map <[i:=x]> m} Φ)%I ≡ (Φ i x ★ Π★{map m} Φ)%I.
  Proof. intros ?; by rewrite /uPred_big_sepM map_to_list_insert. Qed.
  Lemma big_sepM_singleton Φ i x : (Π★{map {[i := x]}} Φ)%I ≡ (Φ i x)%I.
  Proof.
    rewrite -insert_empty big_sepM_insert/=; last auto using lookup_empty.
    by rewrite big_sepM_empty right_id.
  Qed.

  Lemma big_sepM_sepM Φ Ψ m :
    (Π★{map m} (λ i x, Φ i x ★ Ψ i x))%I ≡ (Π★{map m} Φ ★ Π★{map m} Ψ)%I.
  Proof.
    rewrite /uPred_big_sepM.
    induction (map_to_list m) as [|[i x] l IH]; csimpl; rewrite ?right_id //.
    by rewrite IH -!assoc (assoc _ (Ψ _ _)) [(Ψ _ _ ★ _)%I]comm -!assoc.
  Qed.
  Lemma big_sepM_later Φ m : (▷ Π★{map m} Φ)%I ≡ (Π★{map m} (λ i x, ▷ Φ i x))%I.
  Proof.
    rewrite /uPred_big_sepM.
    induction (map_to_list m) as [|[i x] l IH]; csimpl; rewrite ?later_True //.
    by rewrite later_sep IH.
  Qed.
End gmap.

(* Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types Φ : A → uPred M.

  Lemma big_sepS_mono Φ Ψ X Y :
    Y ⊆ X → (∀ x, x ∈ Y → Φ x ⊑ Ψ x) → (Π★{set X} Φ) ⊑ (Π★{set Y} Ψ).
  Proof.
    intros HX HΦ. trans (Π★{set Y} Φ)%I.
    - by apply big_sep_contains, fmap_contains, elements_contains.
    - apply big_sep_mono', Forall2_fmap, Forall2_Forall.
      apply Forall_forall=> x ? /=. by apply HΦ, elem_of_elements.
  Qed.

  Lemma big_sepS_ne X n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (uPred_big_sepS (M:=M) X).
  Proof.
    intros Φ1 Φ2 HΦ. apply big_sep_ne, Forall2_fmap.
    apply Forall2_Forall, Forall_true=> x; apply HΦ.
  Qed.
  Lemma big_sepS_proper X :
    Proper (pointwise_relation _ (≡) ==> (≡)) (uPred_big_sepS (M:=M) X).
  Proof.
    intros Φ1 Φ2 HΦ; apply equiv_dist=> n.
    apply big_sepS_ne=> x; apply equiv_dist, HΦ.
  Qed.
  Lemma big_sepS_mono' X :
    Proper (pointwise_relation _ (⊑) ==> (⊑)) (uPred_big_sepS (M:=M) X).
  Proof. intros Φ1 Φ2 HΦ. apply big_sepS_mono; naive_solver. Qed.

  Lemma big_sepS_empty Φ : (Π★{set ∅} Φ)%I ≡ True%I.
  Proof. by rewrite /uPred_big_sepS elements_empty. Qed.
  Lemma big_sepS_insert Φ X x :
    x ∉ X → (Π★{set {[ x ]} ∪ X} Φ)%I ≡ (Φ x ★ Π★{set X} Φ)%I.
  Proof. intros. by rewrite /uPred_big_sepS elements_union_singleton. Qed.
  Lemma big_sepS_delete Φ X x :
    x ∈ X → (Π★{set X} Φ)%I ≡ (Φ x ★ Π★{set X ∖ {[ x ]}} Φ)%I.
  Proof.
    intros. rewrite -big_sepS_insert; last set_solver.
    by rewrite -union_difference_L; last set_solver.
  Qed.
  Lemma big_sepS_singleton Φ x : (Π★{set {[ x ]}} Φ)%I ≡ (Φ x)%I.
  Proof. intros. by rewrite /uPred_big_sepS elements_singleton /= right_id. Qed.

  Lemma big_sepS_sepS Φ Ψ X :
    (Π★{set X} (λ x, Φ x ★ Ψ x))%I ≡ (Π★{set X} Φ ★ Π★{set X} Ψ)%I.
  Proof.
    rewrite /uPred_big_sepS.
    induction (elements X) as [|x l IH]; csimpl; first by rewrite ?right_id.
    by rewrite IH -!assoc (assoc _ (Ψ _)) [(Ψ _ ★ _)%I]comm -!assoc.
  Qed.

  Lemma big_sepS_later Φ X : (▷ Π★{set X} Φ)%I ≡ (Π★{set X} (λ x, ▷ Φ x))%I.
  Proof.
    rewrite /uPred_big_sepS.
    induction (elements X) as [|x l IH]; csimpl; first by rewrite ?later_True.
    by rewrite later_sep IH.
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
