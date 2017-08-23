From iris.algebra Require Export big_op.
From iris.bi Require Export derived.
From stdpp Require Import countable fin_collections functions.
Set Default Proof Using "Type".

(* Notations *)
Notation "'[∗' 'list]' k ↦ x ∈ l , P" := (big_opL bi_sep (λ k x, P) l)
  (at level 200, l at level 10, k, x at level 1, right associativity,
   format "[∗  list]  k ↦ x  ∈  l ,  P") : bi_scope.
Notation "'[∗' 'list]' x ∈ l , P" := (big_opL bi_sep (λ _ x, P) l)
  (at level 200, l at level 10, x at level 1, right associativity,
   format "[∗  list]  x  ∈  l ,  P") : bi_scope.

Notation "'[∗]' Ps" :=
  (big_opL bi_sep (λ _ x, x) Ps) (at level 20) : bi_scope.

Notation "'[∧' 'list]' k ↦ x ∈ l , P" := (big_opL bi_and (λ k x, P) l)
  (at level 200, l at level 10, k, x at level 1, right associativity,
   format "[∧  list]  k ↦ x  ∈  l ,  P") : bi_scope.
Notation "'[∧' 'list]' x ∈ l , P" := (big_opL bi_and (λ _ x, P) l)
  (at level 200, l at level 10, x at level 1, right associativity,
   format "[∧  list]  x  ∈  l ,  P") : bi_scope.

Notation "'[∧]' Ps" :=
  (big_opL bi_and (λ _ x, x) Ps) (at level 20) : bi_scope.

Notation "'[∗' 'map]' k ↦ x ∈ m , P" := (big_opM bi_sep (λ k x, P) m)
  (at level 200, m at level 10, k, x at level 1, right associativity,
   format "[∗  map]  k ↦ x  ∈  m ,  P") : bi_scope.
Notation "'[∗' 'map]' x ∈ m , P" := (big_opM bi_sep (λ _ x, P) m)
  (at level 200, m at level 10, x at level 1, right associativity,
   format "[∗  map]  x  ∈  m ,  P") : bi_scope.

Notation "'[∗' 'set]' x ∈ X , P" := (big_opS bi_sep (λ x, P) X)
  (at level 200, X at level 10, x at level 1, right associativity,
   format "[∗  set]  x  ∈  X ,  P") : bi_scope.

Notation "'[∗' 'mset]' x ∈ X , P" := (big_opMS bi_sep (λ x, P) X)
  (at level 200, X at level 10, x at level 1, right associativity,
   format "[∗  mset]  x  ∈  X ,  P") : bi_scope.

(** * Properties *)
Module bi.
Import interface.bi derived.bi.
Section bi_big_op.
Context {PROP : bi}.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.

(** ** Big ops over lists *)
Section sep_list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.

  Lemma big_sepL_nil Φ : ([∗ list] k↦y ∈ nil, Φ k y) ⊣⊢ emp.
  Proof. done. Qed.
  Lemma big_sepL_nil' `{AffineBI PROP} P Φ : P ⊢ [∗ list] k↦y ∈ nil, Φ k y.
  Proof. apply (affine _). Qed.
  Lemma big_sepL_cons Φ x l :
    ([∗ list] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ∗ [∗ list] k↦y ∈ l, Φ (S k) y.
  Proof. by rewrite big_opL_cons. Qed.
  Lemma big_sepL_singleton Φ x : ([∗ list] k↦y ∈ [x], Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opL_singleton. Qed.
  Lemma big_sepL_app Φ l1 l2 :
    ([∗ list] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([∗ list] k↦y ∈ l1, Φ k y) ∗ ([∗ list] k↦y ∈ l2, Φ (length l1 + k) y).
  Proof. by rewrite big_opL_app. Qed.

  Lemma big_sepL_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊢ [∗ list] k ↦ y ∈ l, Ψ k y.
  Proof. apply big_opL_forall; apply _. Qed.
  Lemma big_sepL_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢ ([∗ list] k ↦ y ∈ l, Ψ k y).
  Proof. apply big_opL_proper. Qed.
  Lemma big_sepL_submseteq `{AffineBI PROP} (Φ : A → PROP) l1 l2 :
    l1 ⊆+ l2 → ([∗ list] y ∈ l2, Φ y) ⊢ [∗ list] y ∈ l1, Φ y.
  Proof.
    intros [l ->]%submseteq_Permutation. by rewrite big_sepL_app sep_elim_l.
  Qed.

  Global Instance big_sepL_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opL (@bi_sep PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opL_forall; apply _ || intros; apply Hf. Qed.
  Global Instance big_sep_mono' :
    Proper (Forall2 (⊢) ==> (⊢)) (big_opL (@bi_sep M) (λ _ P, P)).
  Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

  Lemma big_sepL_emp l : ([∗ list] k↦y ∈ l, emp) ⊣⊢ (emp : PROP).
  Proof. by rewrite big_opL_unit. Qed.

  Lemma big_sepL_lookup_acc Φ l i x :
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y) ⊢ Φ i x ∗ (Φ i x -∗ ([∗ list] k↦y ∈ l, Φ k y)).
  Proof.
    intros Hli. rewrite -(take_drop_middle l i x) // big_sepL_app /=.
    rewrite Nat.add_0_r take_length_le; eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite assoc -!(comm _ (Φ _ _)) -assoc. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepL_lookup Φ l i x `{!Absorbing (Φ i x)} :
    l !! i = Some x → ([∗ list] k↦y ∈ l, Φ k y) ⊢ Φ i x.
  Proof. intros. rewrite big_sepL_lookup_acc // sep_elim_l. Qed.

  Lemma big_sepL_elem_of (Φ : A → PROP) l x `{!Absorbing (Φ x)} :
    x ∈ l → ([∗ list] y ∈ l, Φ y) ⊢ Φ x.
  Proof.
    intros [i ?]%elem_of_list_lookup; eauto using (big_sepL_lookup (λ _, Φ)).
  Qed.

  Lemma big_sepL_fmap {B} (f : A → B) (Φ : nat → B → PROP) l :
    ([∗ list] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([∗ list] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opL_fmap. Qed.

  Lemma big_sepL_sepL Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x ∗ Ψ k x)
    ⊣⊢ ([∗ list] k↦x ∈ l, Φ k x) ∗ ([∗ list] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opL_opL. Qed.

  Lemma big_sepL_and Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x ∧ Ψ k x)
    ⊢ ([∗ list] k↦x ∈ l, Φ k x) ∧ ([∗ list] k↦x ∈ l, Ψ k x).
  Proof. auto using and_intro, big_sepL_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepL_persistently `{AffineBI PROP} Φ l :
    (□ [∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, □ Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_sepL_forall `{AffineBI PROP} Φ l :
    (∀ k x, Persistent (Φ k x)) →
    ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x).
  Proof.
    intros HΦ. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepL_lookup. }
    revert Φ HΦ. induction l as [|x l IH]=> Φ HΦ; [by auto using big_sepL_nil'|].
    rewrite big_sepL_cons. rewrite -persistent_and_sep_l; apply and_intro.
    - by rewrite (forall_elim 0) (forall_elim x) pure_True // True_impl.
    - rewrite -IH. apply forall_intro=> k; by rewrite (forall_elim (S k)).
  Qed.

  Lemma big_sepL_impl Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x) -∗
    ⬕ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x -∗ Ψ k x) -∗
    [∗ list] k↦x ∈ l, Ψ k x.
  Proof.
    apply wand_intro_l. revert Φ Ψ. induction l as [|x l IH]=> Φ Ψ /=.
    { by rewrite sep_elim_r. }
    rewrite bare_persistently_sep_dup -assoc [(⬕ _ ∗ _)%I]comm -!assoc assoc.
    apply sep_mono.
    - rewrite (forall_elim 0) (forall_elim x) pure_True // True_impl.
      by rewrite bare_persistently_elim wand_elim_l.
    - rewrite comm -(IH (Φ ∘ S) (Ψ ∘ S)) /=.
      apply sep_mono_l, bare_mono, persistently_mono.
      apply forall_intro=> k. by rewrite (forall_elim (S k)).
  Qed.

  Global Instance big_sepL_nil_persistent `{AffineBI PROP} Φ :
    Persistent ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL_persistent1 Φ l :
    (∀ k x, Persistent (Φ k x)) →
    l ≠ [] →
    Persistent ([∗ list] k↦x ∈ l, Φ k x).
  Proof.
    intros. rewrite /Persistent (big_opL_commute1 bi_persistently (R:=(≡))) //.
    apply big_opL_proper=> k y ?. by apply persistent_persistently.
  Qed.
  Global Instance big_sepL_persistent `{AffineBI PROP} Φ l :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∗ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
  Global Instance big_sepL_persistent_id `{AffineBI PROP} Ps :
    TCForall Persistent Ps → Persistent ([∗] Ps).
  Proof. induction 1; simpl; apply _. Qed.
End sep_list.

Section sep_list2.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.
  (* Some lemmas depend on the generalized versions of the above ones. *)

  Lemma big_sepL_zip_with {B C} Φ f (l1 : list B) (l2 : list C) :
    ([∗ list] k↦x ∈ zip_with f l1 l2, Φ k x)
    ⊣⊢ ([∗ list] k↦x ∈ l1, if l2 !! k is Some y then Φ k (f x y) else emp).
  Proof.
    revert Φ l2; induction l1 as [|x l1 IH]=> Φ [|y l2] //=.
    - by rewrite big_sepL_emp left_id.
    - by rewrite IH.
  Qed.
End sep_list2.

Section and_list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.

  Lemma big_andL_nil Φ : ([∧ list] k↦y ∈ nil, Φ k y) ⊣⊢ True.
  Proof. done. Qed.
  Lemma big_andL_nil' P Φ : P ⊢ [∧ list] k↦y ∈ nil, Φ k y.
  Proof. by apply pure_intro. Qed.
  Lemma big_andL_cons Φ x l :
    ([∧ list] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ∧ [∧ list] k↦y ∈ l, Φ (S k) y.
  Proof. by rewrite big_opL_cons. Qed.
  Lemma big_andL_singleton Φ x : ([∧ list] k↦y ∈ [x], Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opL_singleton. Qed.
  Lemma big_andL_app Φ l1 l2 :
    ([∧ list] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([∧ list] k↦y ∈ l1, Φ k y) ∧ ([∧ list] k↦y ∈ l2, Φ (length l1 + k) y).
  Proof. by rewrite big_opL_app. Qed.

  Lemma big_andL_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([∧ list] k ↦ y ∈ l, Φ k y) ⊢ [∧ list] k ↦ y ∈ l, Ψ k y.
  Proof. apply big_opL_forall; apply _. Qed.
  Lemma big_andL_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∧ list] k ↦ y ∈ l, Φ k y) ⊣⊢ ([∧ list] k ↦ y ∈ l, Ψ k y).
  Proof. apply big_opL_proper. Qed.
  Lemma big_andL_submseteq (Φ : A → PROP) l1 l2 :
    l1 ⊆+ l2 → ([∧ list] y ∈ l2, Φ y) ⊢ [∧ list] y ∈ l1, Φ y.
  Proof.
    intros [l ->]%submseteq_Permutation. by rewrite big_andL_app and_elim_l.
  Qed.

  Global Instance big_andL_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opL (@bi_and PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opL_forall; apply _ || intros; apply Hf. Qed.
  Global Instance big_and_mono' :
    Proper (Forall2 (⊢) ==> (⊢)) (big_opL (@bi_and M) (λ _ P, P)).
  Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

  Lemma big_andL_lookup Φ l i x `{!Absorbing (Φ i x)} :
    l !! i = Some x → ([∧ list] k↦y ∈ l, Φ k y) ⊢ Φ i x.
  Proof.
    intros. rewrite -(take_drop_middle l i x) // big_andL_app /=.
    rewrite Nat.add_0_r take_length_le;
      eauto using lookup_lt_Some, Nat.lt_le_incl, and_elim_l', and_elim_r'.
  Qed.

  Lemma big_andL_elem_of (Φ : A → PROP) l x `{!Absorbing (Φ x)} :
    x ∈ l → ([∧ list] y ∈ l, Φ y) ⊢ Φ x.
  Proof.
    intros [i ?]%elem_of_list_lookup; eauto using (big_andL_lookup (λ _, Φ)).
  Qed.

  Lemma big_andL_fmap {B} (f : A → B) (Φ : nat → B → PROP) l :
    ([∧ list] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([∧ list] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opL_fmap. Qed.

  Lemma big_andL_andL Φ Ψ l :
    ([∧ list] k↦x ∈ l, Φ k x ∧ Ψ k x)
    ⊣⊢ ([∧ list] k↦x ∈ l, Φ k x) ∧ ([∧ list] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opL_opL. Qed.

  Lemma big_andL_and Φ Ψ l :
    ([∧ list] k↦x ∈ l, Φ k x ∧ Ψ k x)
    ⊢ ([∧ list] k↦x ∈ l, Φ k x) ∧ ([∧ list] k↦x ∈ l, Ψ k x).
  Proof. auto using and_intro, big_andL_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_andL_persistently Φ l :
    (□ [∧ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∧ list] k↦x ∈ l, □ Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_andL_forall `{AffineBI PROP} Φ l :
    ([∧ list] k↦x ∈ l, Φ k x) ⊣⊢ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x).
  Proof.
    apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_andL_lookup. }
    revert Φ. induction l as [|x l IH]=> Φ; [by auto using big_andL_nil'|].
    rewrite big_andL_cons. apply and_intro.
    - by rewrite (forall_elim 0) (forall_elim x) pure_True // True_impl.
    - rewrite -IH. apply forall_intro=> k; by rewrite (forall_elim (S k)).
  Qed.

  Global Instance big_andL_nil_persistent Φ :
    Persistent ([∧ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_andL_persistent Φ l :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∧ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
End and_list.

(** ** Big ops over finite maps *)
Section gmap.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  Lemma big_sepM_mono Φ Ψ m :
    (∀ k x, m !! k = Some x → Φ k x ⊢ Ψ k x) →
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof. apply big_opM_forall; apply _ || auto. Qed.
  Lemma big_sepM_proper Φ Ψ m :
    (∀ k x, m !! k = Some x → Φ k x ⊣⊢ Ψ k x) →
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∗ map] k ↦ x ∈ m, Ψ k x).
  Proof. apply big_opM_proper. Qed.
  Lemma big_sepM_subseteq `{AffineBI PROP} Φ m1 m2 :
    m2 ⊆ m1 → ([∗ map] k ↦ x ∈ m1, Φ k x) ⊢ [∗ map] k ↦ x ∈ m2, Φ k x.
  Proof. intros. by apply big_sepL_submseteq, map_to_list_submseteq. Qed.

  Global Instance big_sepM_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opM (@bi_sep PROP) (K:=K) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_sepM_mono=> ???; apply Hf. Qed.

  Lemma big_sepM_empty Φ : ([∗ map] k↦x ∈ ∅, Φ k x) ⊣⊢ emp.
  Proof. by rewrite big_opM_empty. Qed.
  Lemma big_sepM_empty' `{AffineBI PROP} P Φ : P ⊢ [∗ map] k↦x ∈ ∅, Φ k x.
  Proof. rewrite big_sepM_empty. apply: affine. Qed.

  Lemma big_sepM_insert Φ m i x :
    m !! i = None →
    ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ∗ [∗ map] k↦y ∈ m, Φ k y.
  Proof. apply big_opM_insert. Qed.

  Lemma big_sepM_delete Φ m i x :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊣⊢ Φ i x ∗ [∗ map] k↦y ∈ delete i m, Φ k y.
  Proof. apply big_opM_delete. Qed.

  Lemma big_sepM_lookup_acc Φ m i x :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊢ Φ i x ∗ (Φ i x -∗ ([∗ map] k↦y ∈ m, Φ k y)).
  Proof.
    intros. rewrite big_sepM_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepM_lookup Φ m i x `{!Absorbing (Φ i x)} :
    m !! i = Some x → ([∗ map] k↦y ∈ m, Φ k y) ⊢ Φ i x.
  Proof. intros. by rewrite big_sepM_lookup_acc // sep_elim_l. Qed.

  Lemma big_sepM_lookup_dom (Φ : K → PROP) m i `{!Absorbing (Φ i)} :
    is_Some (m !! i) → ([∗ map] k↦_ ∈ m, Φ k) ⊢ Φ i.
  Proof. intros [x ?]. by eapply (big_sepM_lookup (λ i x, Φ i)). Qed.

  Lemma big_sepM_singleton Φ i x : ([∗ map] k↦y ∈ {[i:=x]}, Φ k y) ⊣⊢ Φ i x.
  Proof. by rewrite big_opM_singleton. Qed.

  Lemma big_sepM_fmap {B} (f : A → B) (Φ : K → B → PROP) m :
    ([∗ map] k↦y ∈ f <$> m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, Φ k (f y)).
  Proof. by rewrite big_opM_fmap. Qed.

  Lemma big_sepM_insert_override Φ m i x x' :
    m !! i = Some x → (Φ i x ⊣⊢ Φ i x') →
    ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, Φ k y).
  Proof. apply big_opM_insert_override. Qed.

  Lemma big_sepM_insert_override_1 Φ m i x x' :
    m !! i = Some x →
    ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y) ⊢
      (Φ i x' -∗ Φ i x) -∗ ([∗ map] k↦y ∈ m, Φ k y).
  Proof.
    intros ?. apply wand_intro_l.
    rewrite -insert_delete big_sepM_insert ?lookup_delete //.
    by rewrite assoc wand_elim_l -big_sepM_delete.
  Qed.

  Lemma big_sepM_insert_override_2 Φ m i x x' :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊢
      (Φ i x -∗ Φ i x') -∗ ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y).
  Proof.
    intros ?. apply wand_intro_l.
    rewrite {1}big_sepM_delete //; rewrite assoc wand_elim_l.
    rewrite -insert_delete big_sepM_insert ?lookup_delete //.
  Qed.

  Lemma big_sepM_fn_insert {B} (Ψ : K → A → B → PROP) (f : K → B) m i x b :
    m !! i = None →
       ([∗ map] k↦y ∈ <[i:=x]> m, Ψ k y (<[i:=b]> f k))
    ⊣⊢ (Ψ i x b ∗ [∗ map] k↦y ∈ m, Ψ k y (f k)).
  Proof. apply big_opM_fn_insert. Qed.

  Lemma big_sepM_fn_insert' (Φ : K → PROP) m i x P :
    m !! i = None →
    ([∗ map] k↦y ∈ <[i:=x]> m, <[i:=P]> Φ k) ⊣⊢ (P ∗ [∗ map] k↦y ∈ m, Φ k).
  Proof. apply big_opM_fn_insert'. Qed.

  Lemma big_sepM_sepM Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x ∗ Ψ k x)
    ⊣⊢ ([∗ map] k↦x ∈ m, Φ k x) ∗ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof. apply big_opM_opM. Qed.

  Lemma big_sepM_and Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x ∧ Ψ k x)
    ⊢ ([∗ map] k↦x ∈ m, Φ k x) ∧ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof. auto using and_intro, big_sepM_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepM_persistently `{AffineBI PROP} Φ m :
    (□ [∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, □ Φ k x).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_sepM_forall `{AffineBI PROP} Φ m :
    (∀ k x, Persistent (Φ k x)) →
    ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepM_lookup. }
    induction m as [|i x m ? IH] using map_ind; auto using big_sepM_empty'.
    rewrite big_sepM_insert // -persistent_and_sep_l. apply and_intro.
    - rewrite (forall_elim i) (forall_elim x) lookup_insert.
      by rewrite pure_True // True_impl.
    - rewrite -IH. apply forall_mono=> k; apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?.
      rewrite lookup_insert_ne; last by intros ?; simplify_map_eq.
      by rewrite pure_True // True_impl.
  Qed.

  Lemma big_sepM_impl Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    ⬕ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x -∗ Ψ k x) -∗
    [∗ map] k↦x ∈ m, Ψ k x.
  Proof.
    apply wand_intro_l. induction m as [|i x m ? IH] using map_ind.
    { by rewrite sep_elim_r. }
    rewrite !big_sepM_insert // bare_persistently_sep_dup.
    rewrite -assoc [(⬕ _ ∗ _)%I]comm -!assoc assoc. apply sep_mono.
    - rewrite (forall_elim i) (forall_elim x) pure_True ?lookup_insert //.
      by rewrite True_impl bare_persistently_elim wand_elim_l.
    - rewrite comm -IH /=.
      apply sep_mono_l, bare_mono, persistently_mono, forall_mono=> k.
      apply forall_mono=> y. apply impl_intro_l, pure_elim_l=> ?.
      rewrite lookup_insert_ne; last by intros ?; simplify_map_eq.
      by rewrite pure_True // True_impl.
  Qed.

  Global Instance big_sepM_empty_persistent `{AffineBI PROP} Φ :
    Persistent ([∗ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite /big_opM map_to_list_empty. apply _. Qed.
  Global Instance big_sepM_persistent `{AffineBI PROP} Φ m :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∗ map] k↦x ∈ m, Φ k x).
  Proof. intros. apply big_sepL_persistent=> _ [??]; apply _. Qed.
End gmap.


(** ** Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types Φ : A → PROP.

  Lemma big_sepS_mono Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊢ Ψ x) →
    ([∗ set] x ∈ X, Φ x) ⊢ [∗ set] x ∈ X, Ψ x.
  Proof. intros. apply big_opS_forall; apply _ || auto. Qed.
  Lemma big_sepS_proper Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊣⊢ Ψ x) →
    ([∗ set] x ∈ X, Φ x) ⊣⊢ ([∗ set] x ∈ X, Ψ x).
  Proof. apply big_opS_proper. Qed.
  Lemma big_sepS_subseteq `{AffineBI PROP} Φ X Y :
    Y ⊆ X → ([∗ set] x ∈ X, Φ x) ⊢ [∗ set] x ∈ Y, Φ x.
  Proof. intros. by apply big_sepL_submseteq, elements_submseteq. Qed.

  Global Instance big_sepS_mono' :
     Proper (pointwise_relation _ (⊢) ==> (=) ==> (⊢)) (big_opS (@bi_sep PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. by apply big_sepS_mono. Qed.

  Lemma big_sepS_empty Φ : ([∗ set] x ∈ ∅, Φ x) ⊣⊢ emp.
  Proof. by rewrite big_opS_empty. Qed.
  Lemma big_sepS_empty' `{!AffineBI PROP} P Φ : P ⊢ [∗ set] x ∈ ∅, Φ x.
  Proof. rewrite big_sepS_empty. apply: affine. Qed.

  Lemma big_sepS_insert Φ X x :
    x ∉ X → ([∗ set] y ∈ {[ x ]} ∪ X, Φ y) ⊣⊢ (Φ x ∗ [∗ set] y ∈ X, Φ y).
  Proof. apply big_opS_insert. Qed.

  Lemma big_sepS_fn_insert {B} (Ψ : A → B → PROP) f X x b :
    x ∉ X →
       ([∗ set] y ∈ {[ x ]} ∪ X, Ψ y (<[x:=b]> f y))
    ⊣⊢ (Ψ x b ∗ [∗ set] y ∈ X, Ψ y (f y)).
  Proof. apply big_opS_fn_insert. Qed.

  Lemma big_sepS_fn_insert' Φ X x P :
    x ∉ X → ([∗ set] y ∈ {[ x ]} ∪ X, <[x:=P]> Φ y) ⊣⊢ (P ∗ [∗ set] y ∈ X, Φ y).
  Proof. apply big_opS_fn_insert'. Qed.

  Lemma big_sepS_union Φ X Y :
    X ⊥ Y →
    ([∗ set] y ∈ X ∪ Y, Φ y) ⊣⊢ ([∗ set] y ∈ X, Φ y) ∗ ([∗ set] y ∈ Y, Φ y).
  Proof. apply big_opS_union. Qed.

  Lemma big_sepS_delete Φ X x :
    x ∈ X → ([∗ set] y ∈ X, Φ y) ⊣⊢ Φ x ∗ [∗ set] y ∈ X ∖ {[ x ]}, Φ y.
  Proof. apply big_opS_delete. Qed.

  Lemma big_sepS_elem_of Φ X x `{!Absorbing (Φ x)} :
    x ∈ X → ([∗ set] y ∈ X, Φ y) ⊢ Φ x.
  Proof. intros. rewrite big_sepS_delete; auto. Qed.

  Lemma big_sepS_elem_of_acc Φ X x :
    x ∈ X →
    ([∗ set] y ∈ X, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗ set] y ∈ X, Φ y)).
  Proof.
    intros. rewrite big_sepS_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepS_singleton Φ x : ([∗ set] y ∈ {[ x ]}, Φ y) ⊣⊢ Φ x.
  Proof. apply big_opS_singleton. Qed.

  Lemma big_sepS_filter' (P : A → Prop) `{∀ x, Decision (P x)} Φ X :
    ([∗ set] y ∈ filter P X, Φ y)
    ⊣⊢ ([∗ set] y ∈ X, if decide (P y) then Φ y else emp).
  Proof.
    induction X as [|x X ? IH] using collection_ind_L.
    { by rewrite filter_empty_L !big_sepS_empty. }
    destruct (decide (P x)).
    - rewrite filter_union_L filter_singleton_L //.
      rewrite !big_sepS_insert //; last set_solver.
      by rewrite decide_True // IH.
    - rewrite filter_union_L filter_singleton_not_L // left_id_L.
      by rewrite !big_sepS_insert // decide_False // IH left_id.
  Qed.

  Lemma big_sepS_filter_acc' (P : A → Prop) `{∀ y, Decision (P y)} Φ X Y :
    (∀ y, y ∈ Y → P y → y ∈ X) →
    ([∗ set] y ∈ X, Φ y) -∗
      ([∗ set] y ∈ Y, if decide (P y) then Φ y else emp) ∗
      (([∗ set] y ∈ Y, if decide (P y) then Φ y else emp) -∗ [∗ set] y ∈ X, Φ y).
  Proof.
    intros ?. destruct (proj1 (subseteq_disjoint_union_L (filter P Y) X))
      as (Z&->&?); first set_solver.
    rewrite big_sepS_union // big_sepS_filter'.
    by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepS_filter `{AffineBI PROP}
      (P : A → Prop) `{∀ x, Decision (P x)} Φ X :
    ([∗ set] y ∈ filter P X, Φ y) ⊣⊢ ([∗ set] y ∈ X, ⌜P y⌝ → Φ y).
  Proof. setoid_rewrite <-decide_emp. apply big_sepS_filter'. Qed.

  Lemma big_sepS_filter_acc `{AffineBI PROP}
      (P : A → Prop) `{∀ y, Decision (P y)} Φ X Y :
    (∀ y, y ∈ Y → P y → y ∈ X) →
    ([∗ set] y ∈ X, Φ y) -∗
      ([∗ set] y ∈ Y, ⌜P y⌝ → Φ y) ∗
      (([∗ set] y ∈ Y, ⌜P y⌝ → Φ y) -∗ [∗ set] y ∈ X, Φ y).
  Proof. intros. setoid_rewrite <-decide_emp. by apply big_sepS_filter_acc'. Qed.

  Lemma big_sepS_sepS Φ Ψ X :
    ([∗ set] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗ set] y ∈ X, Φ y) ∗ ([∗ set] y ∈ X, Ψ y).
  Proof. apply big_opS_opS. Qed.

  Lemma big_sepS_and Φ Ψ X :
    ([∗ set] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗ set] y ∈ X, Φ y) ∧ ([∗ set] y ∈ X, Ψ y).
  Proof. auto using and_intro, big_sepS_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepS_persistently `{AffineBI PROP} Φ X :
    □ ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, □ Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Lemma big_sepS_forall `{AffineBI PROP} Φ X :
    (∀ x, Persistent (Φ x)) → ([∗ set] x ∈ X, Φ x) ⊣⊢ (∀ x, ⌜x ∈ X⌝ → Φ x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepS_elem_of. }
    induction X as [|x X ? IH] using collection_ind_L; auto using big_sepS_empty'.
    rewrite big_sepS_insert // -persistent_and_sep_l. apply and_intro.
    - by rewrite (forall_elim x) pure_True ?True_impl; last set_solver.
    - rewrite -IH. apply forall_mono=> y. apply impl_intro_l, pure_elim_l=> ?.
      by rewrite pure_True ?True_impl; last set_solver.
  Qed.

  Lemma big_sepS_impl Φ Ψ X :
    ([∗ set] x ∈ X, Φ x) -∗
    ⬕ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x) -∗
    [∗ set] x ∈ X, Ψ x.
  Proof.
    apply wand_intro_l. induction X as [|x X ? IH] using collection_ind_L.
    { by rewrite sep_elim_r. }
    rewrite !big_sepS_insert // bare_persistently_sep_dup.
    rewrite -assoc [(⬕ _ ∗ _)%I]comm -!assoc assoc. apply sep_mono.
    - rewrite (forall_elim x) pure_True; last set_solver.
      by rewrite True_impl bare_persistently_elim wand_elim_l.
    - rewrite comm -IH /=. apply sep_mono_l, bare_mono, persistently_mono.
      apply forall_mono=> y. apply impl_intro_l, pure_elim_l=> ?.
      by rewrite pure_True ?True_impl; last set_solver.
  Qed.

  Global Instance big_sepS_empty_persistent `{AffineBI PROP} Φ :
    Persistent ([∗ set] x ∈ ∅, Φ x).
  Proof. rewrite /big_opS elements_empty. apply _. Qed.
  Global Instance big_sepS_persistent `{AffineBI PROP} Φ X :
    (∀ x, Persistent (Φ x)) → Persistent ([∗ set] x ∈ X, Φ x).
  Proof. rewrite /big_opS. apply _. Qed.
End gset.

Lemma big_sepM_dom `{Countable K} {A} (Φ : K → PROP) (m : gmap K A) :
  ([∗ map] k↦_ ∈ m, Φ k) ⊣⊢ ([∗ set] k ∈ dom _ m, Φ k).
Proof. apply big_opM_dom. Qed.


(** ** Big ops over finite multisets *)
Section gmultiset.
  Context `{Countable A}.
  Implicit Types X : gmultiset A.
  Implicit Types Φ : A → PROP.

  Lemma big_sepMS_mono Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊢ Ψ x) →
    ([∗ mset] x ∈ X, Φ x) ⊢ [∗ mset] x ∈ X, Ψ x.
  Proof. intros. apply big_opMS_forall; apply _ || auto. Qed.
  Lemma big_sepMS_proper Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊣⊢ Ψ x) →
    ([∗ mset] x ∈ X, Φ x) ⊣⊢ ([∗ mset] x ∈ X, Ψ x).
  Proof. apply big_opMS_proper. Qed.
  Lemma big_sepMS_subseteq `{AffineBI PROP} Φ X Y :
    Y ⊆ X → ([∗ mset] x ∈ X, Φ x) ⊢ [∗ mset] x ∈ Y, Φ x.
  Proof. intros. by apply big_sepL_submseteq, gmultiset_elements_submseteq. Qed.

  Global Instance big_sepMS_mono' :
     Proper (pointwise_relation _ (⊢) ==> (=) ==> (⊢)) (big_opMS (@bi_sep PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. by apply big_sepMS_mono. Qed.

  Lemma big_sepMS_empty Φ : ([∗ mset] x ∈ ∅, Φ x) ⊣⊢ emp.
  Proof. by rewrite big_opMS_empty. Qed.
  Lemma big_sepMS_empty' `{!AffineBI PROP} P Φ : P ⊢ [∗ mset] x ∈ ∅, Φ x.
  Proof. rewrite big_sepMS_empty. apply: affine. Qed.

  Lemma big_sepMS_union Φ X Y :
    ([∗ mset] y ∈ X ∪ Y, Φ y) ⊣⊢ ([∗ mset] y ∈ X, Φ y) ∗ [∗ mset] y ∈ Y, Φ y.
  Proof. apply big_opMS_union. Qed.

  Lemma big_sepMS_delete Φ X x :
    x ∈ X → ([∗ mset] y ∈ X, Φ y) ⊣⊢ Φ x ∗ [∗ mset] y ∈ X ∖ {[ x ]}, Φ y.
  Proof. apply big_opMS_delete. Qed.

  Lemma big_sepMS_elem_of Φ X x `{!Absorbing (Φ x)} :
    x ∈ X → ([∗ mset] y ∈ X, Φ y) ⊢ Φ x.
  Proof. intros. by rewrite big_sepMS_delete // sep_elim_l. Qed.

  Lemma big_sepMS_elem_of_acc Φ X x :
    x ∈ X →
    ([∗ mset] y ∈ X, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗ mset] y ∈ X, Φ y)).
  Proof.
    intros. rewrite big_sepMS_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepMS_singleton Φ x : ([∗ mset] y ∈ {[ x ]}, Φ y) ⊣⊢ Φ x.
  Proof. apply big_opMS_singleton. Qed.

  Lemma big_sepMS_sepMS Φ Ψ X :
    ([∗ mset] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗ mset] y ∈ X, Φ y) ∗ ([∗ mset] y ∈ X, Ψ y).
  Proof. apply big_opMS_opMS. Qed.

  Lemma big_sepMS_and Φ Ψ X :
    ([∗ mset] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗ mset] y ∈ X, Φ y) ∧ ([∗ mset] y ∈ X, Ψ y).
  Proof. auto using and_intro, big_sepMS_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepMS_persistently `{AffineBI PROP} Φ X :
    □ ([∗ mset] y ∈ X, Φ y) ⊣⊢ ([∗ mset] y ∈ X, □ Φ y).
  Proof. apply (big_opMS_commute _). Qed.

  Global Instance big_sepMS_empty_persistent `{AffineBI PROP} Φ :
    Persistent ([∗ mset] x ∈ ∅, Φ x).
  Proof. rewrite /big_opMS gmultiset_elements_empty. apply _. Qed.
  Global Instance big_sepMS_persistent `{AffineBI PROP} Φ X :
    (∀ x, Persistent (Φ x)) → Persistent ([∗ mset] x ∈ X, Φ x).
  Proof. rewrite /big_opMS. apply _. Qed.
End gmultiset.
End bi_big_op.

(** * Properties for step-indexed BIs*)
Section sbi_big_op.
Context {PROP : sbi}.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.

(** ** Big ops over lists *)
Section list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.

  Lemma big_sepL_later `{AffineBI PROP} Φ l :
    ▷ ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, ▷ Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_sepL_laterN `{AffineBI PROP} Φ n l :
    ▷^n ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, ▷^n Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Global Instance big_sepL_nil_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL_timeless `{!Timeless (emp%I : PROP)} Φ l :
    (∀ k x, Timeless (Φ k x)) → Timeless ([∗ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
  Global Instance big_sepL_timeless_id `{!Timeless (emp%I : PROP)} Ps :
    TCForall Timeless Ps → Timeless ([∗] Ps).
  Proof. induction 1; simpl; apply _. Qed.
End list.

(** ** Big ops over finite maps *)
Section gmap.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  Lemma big_sepM_later `{AffineBI PROP} Φ m :
    ▷ ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, ▷ Φ k x).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_sepM_laterN `{AffineBI PROP} Φ n m :
    ▷^n ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, ▷^n Φ k x).
  Proof. apply (big_opM_commute _). Qed.

  Global Instance big_sepM_nil_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite /big_opM map_to_list_empty. apply _. Qed.
  Global Instance big_sepM_timeless `{!Timeless (emp%I : PROP)} Φ m :
    (∀ k x, Timeless (Φ k x)) → Timeless ([∗ map] k↦x ∈ m, Φ k x).
  Proof. intros. apply big_sepL_timeless=> _ [??]; apply _. Qed.
End gmap.

(** ** Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types Φ : A → PROP.

  Lemma big_sepS_later `{AffineBI PROP} Φ X :
    ▷ ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, ▷ Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Lemma big_sepS_laterN `{AffineBI PROP} Φ n X :
    ▷^n ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, ▷^n Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Global Instance big_sepS_nil_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ set] x ∈ ∅, Φ x).
  Proof. rewrite /big_opS elements_empty. apply _. Qed.
  Global Instance big_sepS_timeless `{!Timeless (emp%I : PROP)} Φ X :
    (∀ x, Timeless (Φ x)) → Timeless ([∗ set] x ∈ X, Φ x).
  Proof. rewrite /big_opS. apply _. Qed.
End gset.

(** ** Big ops over finite multisets *)
Section gmultiset.
  Context `{Countable A}.
  Implicit Types X : gmultiset A.
  Implicit Types Φ : A → PROP.

  Lemma big_sepMS_later `{AffineBI PROP} Φ X :
    ▷ ([∗ mset] y ∈ X, Φ y) ⊣⊢ ([∗ mset] y ∈ X, ▷ Φ y).
  Proof. apply (big_opMS_commute _). Qed.

  Lemma big_sepMS_laterN `{AffineBI PROP} Φ n X :
    ▷^n ([∗ mset] y ∈ X, Φ y) ⊣⊢ ([∗ mset] y ∈ X, ▷^n Φ y).
  Proof. apply (big_opMS_commute _). Qed.

  Global Instance big_sepMS_nil_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ mset] x ∈ ∅, Φ x).
  Proof. rewrite /big_opMS gmultiset_elements_empty. apply _. Qed.
  Global Instance big_sepMS_timeless `{!Timeless (emp%I : PROP)} Φ X :
    (∀ x, Timeless (Φ x)) → Timeless ([∗ mset] x ∈ X, Φ x).
  Proof. rewrite /big_opMS. apply _. Qed.
End gmultiset.
End sbi_big_op.
End bi.

Hint Resolve bi.big_sepL_nil' bi.big_sepM_empty'
  bi.big_sepS_empty' bi.big_sepMS_empty' | 0.
