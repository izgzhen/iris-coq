From iris.algebra Require Export upred list cmra_big_op.
From iris.prelude Require Import gmap fin_collections functions.
Import uPred.

(** We define the following big operators:

- The operator [ [★] Ps ] folds [★] over the list [Ps].
  This operator is not a quantifier, so it binds strongly.
- The operator [ [★ list] k ↦ x ∈ l, P ] asserts that [P] holds separately for
  each element [x] at position [x] in the list [l]. This operator is a
  quantifier, and thus has the same precedence as [∀] and [∃].
- The operator [ [★ map] k ↦ x ∈ m, P ] asserts that [P] holds separately for
  each [k ↦ x] in the map [m]. This operator is a quantifier, and thus has the
  same precedence as [∀] and [∃].
- The operator [ [★ set] x ∈ X, P ] asserts that [P] holds separately for each
  [x] in the set [X]. This operator is a quantifier, and thus has the same
  precedence as [∀] and [∃]. *)

(** * Big ops over lists *)
(* These are the basic building blocks for other big ops *)
Fixpoint uPred_big_sep {M} (Ps : list (uPred M)) : uPred M :=
  match Ps with [] => True | P :: Ps => P ★ uPred_big_sep Ps end%I.
Instance: Params (@uPred_big_sep) 1.
Notation "'[★]' Ps" := (uPred_big_sep Ps) (at level 20) : uPred_scope.

(** * Other big ops *)
Definition uPred_big_sepL {M A} (l : list A)
  (Φ : nat → A → uPred M) : uPred M := [★] (imap Φ l).
Instance: Params (@uPred_big_sepL) 2.
Typeclasses Opaque uPred_big_sepL.
Notation "'[★' 'list' ] k ↦ x ∈ l , P" := (uPred_big_sepL l (λ k x, P))
  (at level 200, l at level 10, k, x at level 1, right associativity,
   format "[★  list ]  k ↦ x  ∈  l ,  P") : uPred_scope.
Notation "'[★' 'list' ] x ∈ l , P" := (uPred_big_sepL l (λ _ x, P))
  (at level 200, l at level 10, x at level 1, right associativity,
   format "[★  list ]  x  ∈  l ,  P") : uPred_scope.

Definition uPred_big_sepM {M} `{Countable K} {A}
    (m : gmap K A) (Φ : K → A → uPred M) : uPred M :=
  [★] (curry Φ <$> map_to_list m).
Instance: Params (@uPred_big_sepM) 6.
Typeclasses Opaque uPred_big_sepM.
Notation "'[★' 'map' ] k ↦ x ∈ m , P" := (uPred_big_sepM m (λ k x, P))
  (at level 200, m at level 10, k, x at level 1, right associativity,
   format "[★  map ]  k ↦ x  ∈  m ,  P") : uPred_scope.
Notation "'[★' 'map' ] x ∈ m , P" := (uPred_big_sepM m (λ _ x, P))
  (at level 200, m at level 10, x at level 1, right associativity,
   format "[★  map ]  x  ∈  m ,  P") : uPred_scope.

Definition uPred_big_sepS {M} `{Countable A}
  (X : gset A) (Φ : A → uPred M) : uPred M := [★] (Φ <$> elements X).
Instance: Params (@uPred_big_sepS) 5.
Typeclasses Opaque uPred_big_sepS.
Notation "'[★' 'set' ] x ∈ X , P" := (uPred_big_sepS X (λ x, P))
  (at level 200, X at level 10, x at level 1, right associativity,
   format "[★  set ]  x  ∈  X ,  P") : uPred_scope.

(** * Persistence and timelessness of lists of uPreds *)
Class PersistentL {M} (Ps : list (uPred M)) :=
  persistentL : Forall PersistentP Ps.
Arguments persistentL {_} _ {_}.

Class TimelessL {M} (Ps : list (uPred M)) :=
  timelessL : Forall TimelessP Ps.
Arguments timelessL {_} _ {_}.

(** * Properties *)
Section big_op.
Context {M : ucmraT}.
Implicit Types Ps Qs : list (uPred M).
Implicit Types A : Type.

(** ** Generic big ops over lists of upreds *)
Global Instance big_sep_proper : Proper ((≡) ==> (⊣⊢)) (@uPred_big_sep M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.
Global Instance big_sep_ne n : Proper (dist n ==> dist n) (@uPred_big_sep M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.
Global Instance big_sep_mono' : Proper (Forall2 (⊢) ==> (⊢)) (@uPred_big_sep M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

Global Instance big_sep_perm : Proper ((≡ₚ) ==> (⊣⊢)) (@uPred_big_sep M).
Proof.
  induction 1 as [|P Ps Qs ? IH|P Q Ps|]; simpl; auto.
  - by rewrite IH.
  - by rewrite !assoc (comm _ P).
  - etrans; eauto.
Qed.

Lemma big_sep_app Ps Qs : [★] (Ps ++ Qs) ⊣⊢ [★] Ps ★ [★] Qs.
Proof. by induction Ps as [|?? IH]; rewrite /= ?left_id -?assoc ?IH. Qed.

Lemma big_sep_contains Ps Qs : Qs `contains` Ps → [★] Ps ⊢ [★] Qs.
Proof.
  intros [Ps' ->]%contains_Permutation. by rewrite big_sep_app sep_elim_l.
Qed.
Lemma big_sep_elem_of Ps P : P ∈ Ps → [★] Ps ⊢ P.
Proof. induction 1; simpl; auto with I. Qed.

(** ** Persistence *)
Global Instance big_sep_persistent Ps : PersistentL Ps → PersistentP ([★] Ps).
Proof. induction 1; apply _. Qed.

Global Instance nil_persistent : PersistentL (@nil (uPred M)).
Proof. constructor. Qed.
Global Instance cons_persistent P Ps :
  PersistentP P → PersistentL Ps → PersistentL (P :: Ps).
Proof. by constructor. Qed.
Global Instance app_persistent Ps Ps' :
  PersistentL Ps → PersistentL Ps' → PersistentL (Ps ++ Ps').
Proof. apply Forall_app_2. Qed.

Global Instance fmap_persistent {A} (f : A → uPred M) xs :
  (∀ x, PersistentP (f x)) → PersistentL (f <$> xs).
Proof. intros. apply Forall_fmap, Forall_forall; auto. Qed.
Global Instance zip_with_persistent {A B} (f : A → B → uPred M) xs ys :
  (∀ x y, PersistentP (f x y)) → PersistentL (zip_with f xs ys).
Proof.
  unfold PersistentL=> ?; revert ys; induction xs=> -[|??]; constructor; auto.
Qed.
Global Instance imap_persistent {A} (f : nat → A → uPred M) xs :
  (∀ i x, PersistentP (f i x)) → PersistentL (imap f xs).
Proof.
  rewrite /PersistentL /imap=> ?. generalize 0. induction xs; constructor; auto.
Qed.

(** ** Timelessness *)
Global Instance big_sep_timeless Ps : TimelessL Ps → TimelessP ([★] Ps).
Proof. induction 1; apply _. Qed.

Global Instance nil_timeless : TimelessL (@nil (uPred M)).
Proof. constructor. Qed.
Global Instance cons_timeless P Ps :
  TimelessP P → TimelessL Ps → TimelessL (P :: Ps).
Proof. by constructor. Qed.
Global Instance app_timeless Ps Ps' :
  TimelessL Ps → TimelessL Ps' → TimelessL (Ps ++ Ps').
Proof. apply Forall_app_2. Qed.

Global Instance fmap_timeless {A} (f : A → uPred M) xs :
  (∀ x, TimelessP (f x)) → TimelessL (f <$> xs).
Proof. intros. apply Forall_fmap, Forall_forall; auto. Qed.
Global Instance zip_with_timeless {A B} (f : A → B → uPred M) xs ys :
  (∀ x y, TimelessP (f x y)) → TimelessL (zip_with f xs ys).
Proof.
  unfold TimelessL=> ?; revert ys; induction xs=> -[|??]; constructor; auto.
Qed.
Global Instance imap_timeless {A} (f : nat → A → uPred M) xs :
  (∀ i x, TimelessP (f i x)) → TimelessL (imap f xs).
Proof.
  rewrite /TimelessL /imap=> ?. generalize 0. induction xs; constructor; auto.
Qed.

(** ** Big ops over lists *)
Section list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → uPred M.

  Lemma big_sepL_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([★ list] k ↦ y ∈ l, Φ k y) ⊢ [★ list] k ↦ y ∈ l, Ψ k y.
  Proof.
    intros HΦ. apply big_sep_mono'.
    revert Φ Ψ HΦ. induction l as [|x l IH]=> Φ Ψ HΦ; first constructor.
    rewrite !imap_cons; constructor; eauto.
  Qed.
  Lemma big_sepL_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([★ list] k ↦ y ∈ l, Φ k y) ⊣⊢ ([★ list] k ↦ y ∈ l, Ψ k y).
  Proof.
    intros ?; apply (anti_symm (⊢)); apply big_sepL_mono;
      eauto using equiv_entails, equiv_entails_sym, lookup_weaken.
  Qed.

  Global Instance big_sepL_ne l n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> (dist n))
           (uPred_big_sepL (M:=M) l).
  Proof.
    intros Φ Ψ HΦ. apply big_sep_ne.
    revert Φ Ψ HΦ. induction l as [|x l IH]=> Φ Ψ HΦ; first constructor.
    rewrite !imap_cons; constructor. by apply HΦ. apply IH=> n'; apply HΦ.
  Qed.
  Global Instance big_sepL_proper' l :
    Proper (pointwise_relation _ (pointwise_relation _ (⊣⊢)) ==> (⊣⊢))
           (uPred_big_sepL (M:=M) l).
  Proof. intros Φ1 Φ2 HΦ. by apply big_sepL_proper; intros; last apply HΦ. Qed.
  Global Instance big_sepL_mono' l :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (⊢))
           (uPred_big_sepL (M:=M) l).
  Proof. intros Φ1 Φ2 HΦ. by apply big_sepL_mono; intros; last apply HΦ. Qed.

  Lemma big_sepL_nil Φ : ([★ list] k↦y ∈ nil, Φ k y) ⊣⊢ True.
  Proof. done. Qed.

  Lemma big_sepL_cons Φ x l :
    ([★ list] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ★ [★ list] k↦y ∈ l, Φ (S k) y.
  Proof. by rewrite /uPred_big_sepL imap_cons. Qed.

  Lemma big_sepL_singleton Φ x : ([★ list] k↦y ∈ [x], Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_sepL_cons big_sepL_nil right_id. Qed.

  Lemma big_sepL_app Φ l1 l2 :
    ([★ list] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([★ list] k↦y ∈ l1, Φ k y) ★ ([★ list] k↦y ∈ l2, Φ (length l1 + k) y).
  Proof. by rewrite /uPred_big_sepL imap_app big_sep_app. Qed.

  Lemma big_sepL_lookup Φ l i x :
    l !! i = Some x → ([★ list] k↦y ∈ l, Φ k y) ⊢ Φ i x.
  Proof.
    intros. rewrite -(take_drop_middle l i x) // big_sepL_app big_sepL_cons.
    rewrite Nat.add_0_r take_length_le; eauto using lookup_lt_Some, Nat.lt_le_incl.
    by rewrite sep_elim_r sep_elim_l.
  Qed.

  Lemma big_sepL_elem_of (Φ : A → uPred M) l x :
    x ∈ l → ([★ list] y ∈ l, Φ y) ⊢ Φ x.
  Proof.
    intros [i ?]%elem_of_list_lookup; eauto using (big_sepL_lookup (λ _, Φ)).
  Qed.

  Lemma big_sepL_fmap {B} (f : A → B) (Φ : nat → B → uPred M) l :
    ([★ list] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([★ list] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite /uPred_big_sepL imap_fmap. Qed.

  Lemma big_sepL_sepL Φ Ψ l :
    ([★ list] k↦x ∈ l, Φ k x ★ Ψ k x)
    ⊣⊢ ([★ list] k↦x ∈ l, Φ k x) ★ ([★ list] k↦x ∈ l, Ψ k x).
  Proof.
    revert Φ Ψ; induction l as [|x l IH]=> Φ Ψ.
    { by rewrite !big_sepL_nil left_id. }
    rewrite !big_sepL_cons IH.
    by rewrite -!assoc (assoc _ (Ψ _ _)) [(Ψ _ _ ★ _)%I]comm -!assoc.
  Qed.

  Lemma big_sepL_commute (Ψ: uPred M → uPred M) `{!Proper ((≡) ==> (≡)) Ψ} Φ l :
    Ψ True ⊣⊢ True →
    (∀ P Q, Ψ (P ★ Q) ⊣⊢ Ψ P ★ Ψ Q) →
    Ψ ([★ list] k↦x ∈ l, Φ k x) ⊣⊢ ([★ list] k↦x ∈ l, Ψ (Φ k x)).
  Proof.
    intros ??. revert Φ. induction l as [|x l IH]=> Φ //.
    by rewrite !big_sepL_cons -IH.
  Qed.
  Lemma big_sepL_op_commute {B : ucmraT}
      (Ψ: B → uPred M) `{!Proper ((≡) ==> (≡)) Ψ} (f : nat → A → B) l :
    Ψ ∅ ⊣⊢ True →
    (∀ x y, Ψ (x ⋅ y) ⊣⊢ Ψ x ★ Ψ y) →
    Ψ ([⋅ list] k↦x ∈ l, f k x) ⊣⊢ ([★ list] k↦x ∈ l, Ψ (f k x)).
  Proof.
    intros ??. revert f. induction l as [|x l IH]=> f //.
    by rewrite big_sepL_cons big_opL_cons -IH.
  Qed.
  Lemma big_sepL_op_commute1 {B : ucmraT}
      (Ψ: B → uPred M) `{!Proper ((≡) ==> (≡)) Ψ} (f : nat → A → B) l :
    (∀ x y, Ψ (x ⋅ y) ⊣⊢ Ψ x ★ Ψ y) →
    l ≠ [] →
    Ψ ([⋅ list] k↦x ∈ l, f k x) ⊣⊢ ([★ list] k↦x ∈ l, Ψ (f k x)).
  Proof.
    intros ??. revert f. induction l as [|x [|x' l'] IH]=> f //.
    { by rewrite big_sepL_singleton big_opL_singleton. }
    by rewrite big_sepL_cons big_opL_cons -IH.
  Qed.

  Lemma big_sepL_later Φ l :
    ▷ ([★ list] k↦x ∈ l, Φ k x) ⊣⊢ ([★ list] k↦x ∈ l, ▷ Φ k x).
  Proof. apply (big_sepL_commute _); auto using later_True, later_sep. Qed.

  Lemma big_sepL_always Φ l :
    (□ [★ list] k↦x ∈ l, Φ k x) ⊣⊢ ([★ list] k↦x ∈ l, □ Φ k x).
  Proof. apply (big_sepL_commute _); auto using always_pure, always_sep. Qed.

  Lemma big_sepL_always_if p Φ l :
    □?p ([★ list] k↦x ∈ l, Φ k x) ⊣⊢ ([★ list] k↦x ∈ l, □?p Φ k x).
  Proof. destruct p; simpl; auto using big_sepL_always. Qed.

  Lemma big_sepL_forall Φ l :
    (∀ k x, PersistentP (Φ k x)) →
    ([★ list] k↦x ∈ l, Φ k x) ⊣⊢ (∀ k x, l !! k = Some x → Φ k x).
  Proof.
    intros HΦ. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply big_sepL_lookup. }
    revert Φ HΦ. induction l as [|x l IH]=> Φ HΦ.
    { rewrite big_sepL_nil; auto with I. }
    rewrite big_sepL_cons. rewrite -always_and_sep_l; apply and_intro.
    - by rewrite (forall_elim 0) (forall_elim x) pure_equiv // True_impl.
    - rewrite -IH. apply forall_intro=> k; by rewrite (forall_elim (S k)).
  Qed.

  Lemma big_sepL_impl Φ Ψ l :
    □ (∀ k x, l !! k = Some x → Φ k x → Ψ k x) ∧ ([★ list] k↦x ∈ l, Φ k x)
    ⊢ [★ list] k↦x ∈ l, Ψ k x.
  Proof.
    rewrite always_and_sep_l. do 2 setoid_rewrite always_forall.
    setoid_rewrite always_impl; setoid_rewrite always_pure.
    rewrite -big_sepL_forall -big_sepL_sepL. apply big_sepL_mono; auto=> k x ?.
    by rewrite -always_wand_impl always_elim wand_elim_l.
  Qed.

  Global Instance big_sepL_nil_persistent Φ :
    PersistentP ([★ list] k↦x ∈ [], Φ k x).
  Proof. rewrite /uPred_big_sepL. apply _. Qed.
  Global Instance big_sepL_persistent Φ l :
    (∀ k x, PersistentP (Φ k x)) → PersistentP ([★ list] k↦x ∈ l, Φ k x).
  Proof. rewrite /uPred_big_sepL. apply _. Qed.

  Global Instance big_sepL_nil_timeless Φ :
    TimelessP ([★ list] k↦x ∈ [], Φ k x).
  Proof. rewrite /uPred_big_sepL. apply _. Qed.
  Global Instance big_sepL_timeless Φ l :
    (∀ k x, TimelessP (Φ k x)) → TimelessP ([★ list] k↦x ∈ l, Φ k x).
  Proof. rewrite /uPred_big_sepL. apply _. Qed.
End list.


(** ** Big ops over finite maps *)
Section gmap.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → uPred M.

  Lemma big_sepM_mono Φ Ψ m1 m2 :
    m2 ⊆ m1 → (∀ k x, m2 !! k = Some x → Φ k x ⊢ Ψ k x) →
    ([★ map] k ↦ x ∈ m1, Φ k x) ⊢ [★ map] k ↦ x ∈ m2, Ψ k x.
  Proof.
    intros HX HΦ. trans ([★ map] k↦x ∈ m2, Φ k x)%I.
    - by apply big_sep_contains, fmap_contains, map_to_list_contains.
    - apply big_sep_mono', Forall2_fmap, Forall_Forall2.
      apply Forall_forall=> -[i x] ? /=. by apply HΦ, elem_of_map_to_list.
  Qed.
  Lemma big_sepM_proper Φ Ψ m :
    (∀ k x, m !! k = Some x → Φ k x ⊣⊢ Ψ k x) →
    ([★ map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([★ map] k ↦ x ∈ m, Ψ k x).
  Proof.
    intros ?; apply (anti_symm (⊢)); apply big_sepM_mono;
      eauto using equiv_entails, equiv_entails_sym, lookup_weaken.
  Qed.

  Global Instance big_sepM_ne m n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> (dist n))
           (uPred_big_sepM (M:=M) m).
  Proof.
    intros Φ1 Φ2 HΦ. apply big_sep_ne, Forall2_fmap.
    apply Forall_Forall2, Forall_true=> -[i x]; apply HΦ.
  Qed.
  Global Instance big_sepM_proper' m :
    Proper (pointwise_relation _ (pointwise_relation _ (⊣⊢)) ==> (⊣⊢))
           (uPred_big_sepM (M:=M) m).
  Proof. intros Φ1 Φ2 HΦ. by apply big_sepM_proper; intros; last apply HΦ. Qed.
  Global Instance big_sepM_mono' m :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (⊢))
           (uPred_big_sepM (M:=M) m).
  Proof. intros Φ1 Φ2 HΦ. by apply big_sepM_mono; intros; last apply HΦ. Qed.

  Lemma big_sepM_empty Φ : ([★ map] k↦x ∈ ∅, Φ k x) ⊣⊢ True.
  Proof. by rewrite /uPred_big_sepM map_to_list_empty. Qed.

  Lemma big_sepM_insert Φ m i x :
    m !! i = None →
    ([★ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ★ [★ map] k↦y ∈ m, Φ k y.
  Proof. intros ?; by rewrite /uPred_big_sepM map_to_list_insert. Qed.

  Lemma big_sepM_delete Φ m i x :
    m !! i = Some x →
    ([★ map] k↦y ∈ m, Φ k y) ⊣⊢ Φ i x ★ [★ map] k↦y ∈ delete i m, Φ k y.
  Proof.
    intros. rewrite -big_sepM_insert ?lookup_delete //.
    by rewrite insert_delete insert_id.
  Qed.

  Lemma big_sepM_lookup Φ m i x :
    m !! i = Some x → ([★ map] k↦y ∈ m, Φ k y) ⊢ Φ i x.
  Proof. intros. by rewrite big_sepM_delete // sep_elim_l. Qed.

  Lemma big_sepM_singleton Φ i x : ([★ map] k↦y ∈ {[i:=x]}, Φ k y) ⊣⊢ Φ i x.
  Proof.
    rewrite -insert_empty big_sepM_insert/=; last auto using lookup_empty.
    by rewrite big_sepM_empty right_id.
  Qed.

  Lemma big_sepM_fmap {B} (f : A → B) (Φ : K → B → uPred M) m :
    ([★ map] k↦y ∈ f <$> m, Φ k y) ⊣⊢ ([★ map] k↦y ∈ m, Φ k (f y)).
  Proof.
    rewrite /uPred_big_sepM map_to_list_fmap -list_fmap_compose.
    f_equiv; apply reflexive_eq, list_fmap_ext. by intros []. done.
  Qed.

  Lemma big_sepM_insert_override (Φ : K → uPred M) m i x y :
    m !! i = Some x →
    ([★ map] k↦_ ∈ <[i:=y]> m, Φ k) ⊣⊢ ([★ map] k↦_ ∈ m, Φ k).
  Proof.
    intros. rewrite -insert_delete big_sepM_insert ?lookup_delete //.
    by rewrite -big_sepM_delete.
  Qed.

  Lemma big_sepM_fn_insert {B} (Ψ : K → A → B → uPred M) (f : K → B) m i x b :
    m !! i = None →
       ([★ map] k↦y ∈ <[i:=x]> m, Ψ k y (<[i:=b]> f k))
    ⊣⊢ (Ψ i x b ★ [★ map] k↦y ∈ m, Ψ k y (f k)).
  Proof.
    intros. rewrite big_sepM_insert // fn_lookup_insert.
    apply sep_proper, big_sepM_proper; auto=> k y ?.
    by rewrite fn_lookup_insert_ne; last set_solver.
  Qed.
  Lemma big_sepM_fn_insert' (Φ : K → uPred M) m i x P :
    m !! i = None →
    ([★ map] k↦y ∈ <[i:=x]> m, <[i:=P]> Φ k) ⊣⊢ (P ★ [★ map] k↦y ∈ m, Φ k).
  Proof. apply (big_sepM_fn_insert (λ _ _, id)). Qed.

  Lemma big_sepM_sepM Φ Ψ m :
       ([★ map] k↦x ∈ m, Φ k x ★ Ψ k x)
    ⊣⊢ ([★ map] k↦x ∈ m, Φ k x) ★ ([★ map] k↦x ∈ m, Ψ k x).
  Proof.
    rewrite /uPred_big_sepM.
    induction (map_to_list m) as [|[i x] l IH]; csimpl; rewrite ?right_id //.
    by rewrite IH -!assoc (assoc _ (Ψ _ _)) [(Ψ _ _ ★ _)%I]comm -!assoc.
  Qed.

  Lemma big_sepM_commute (Ψ: uPred M → uPred M) `{!Proper ((≡) ==> (≡)) Ψ} Φ m :
    Ψ True ⊣⊢ True →
    (∀ P Q, Ψ (P ★ Q) ⊣⊢ Ψ P ★ Ψ Q) →
    Ψ ([★ map] k↦x ∈ m, Φ k x) ⊣⊢ ([★ map] k↦x ∈ m, Ψ (Φ k x)).
  Proof.
    intros ??. rewrite /uPred_big_sepM.
    induction (map_to_list m) as [|[i x] l IH]; rewrite //= -?IH; auto.
  Qed.
  Lemma big_sepM_op_commute {B : ucmraT}
      (Ψ: B → uPred M) `{!Proper ((≡) ==> (≡)) Ψ} (f : K → A → B) m :
    Ψ ∅ ⊣⊢ True →
    (∀ x y, Ψ (x ⋅ y) ⊣⊢ Ψ x ★ Ψ y) →
    Ψ ([⋅ map] k↦x ∈ m, f k x) ⊣⊢ ([★ map] k↦x ∈ m, Ψ (f k x)).
  Proof.
    intros ??. rewrite /big_opM /uPred_big_sepM.
    induction (map_to_list m) as [|[i x] l IH]; rewrite //= -?IH; auto.
  Qed.
  Lemma big_sepM_op_commute1 {B : ucmraT}
      (Ψ: B → uPred M) `{!Proper ((≡) ==> (≡)) Ψ} (f : K → A → B) m :
    (∀ x y, Ψ (x ⋅ y) ⊣⊢ Ψ x ★ Ψ y) →
    m ≠ ∅ →
    Ψ ([⋅ map] k↦x ∈ m, f k x) ⊣⊢ ([★ map] k↦x ∈ m, Ψ (f k x)).
  Proof.
    rewrite -map_to_list_empty'. intros ??. rewrite /big_opM /uPred_big_sepM.
    induction (map_to_list m) as [|[i x] [|i' x'] IH];
      csimpl in *; rewrite ?right_id -?IH //.
  Qed.

  Lemma big_sepM_later Φ m :
    ▷ ([★ map] k↦x ∈ m, Φ k x) ⊣⊢ ([★ map] k↦x ∈ m, ▷ Φ k x).
  Proof. apply (big_sepM_commute _); auto using later_True, later_sep. Qed.

  Lemma big_sepM_always Φ m :
    (□ [★ map] k↦x ∈ m, Φ k x) ⊣⊢ ([★ map] k↦x ∈ m, □ Φ k x).
  Proof. apply (big_sepM_commute _); auto using always_pure, always_sep. Qed.

  Lemma big_sepM_always_if p Φ m :
    □?p ([★ map] k↦x ∈ m, Φ k x) ⊣⊢ ([★ map] k↦x ∈ m, □?p Φ k x).
  Proof. destruct p; simpl; auto using big_sepM_always. Qed.

  Lemma big_sepM_forall Φ m :
    (∀ k x, PersistentP (Φ k x)) →
    ([★ map] k↦x ∈ m, Φ k x) ⊣⊢ (∀ k x, m !! k = Some x → Φ k x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply big_sepM_lookup. }
    rewrite /uPred_big_sepM. setoid_rewrite <-elem_of_map_to_list.
    induction (map_to_list m) as [|[i x] l IH]; csimpl; auto.
    rewrite -always_and_sep_l; apply and_intro.
    - rewrite (forall_elim i) (forall_elim x) pure_equiv; last by left.
      by rewrite True_impl.
    - rewrite -IH. apply forall_mono=> k; apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?. rewrite pure_equiv; last by right.
      by rewrite True_impl.
  Qed.

  Lemma big_sepM_impl Φ Ψ m :
    □ (∀ k x, m !! k = Some x → Φ k x → Ψ k x) ∧ ([★ map] k↦x ∈ m, Φ k x)
    ⊢ [★ map] k↦x ∈ m, Ψ k x.
  Proof.
    rewrite always_and_sep_l. do 2 setoid_rewrite always_forall.
    setoid_rewrite always_impl; setoid_rewrite always_pure.
    rewrite -big_sepM_forall -big_sepM_sepM. apply big_sepM_mono; auto=> k x ?.
    by rewrite -always_wand_impl always_elim wand_elim_l.
  Qed.

  Global Instance big_sepM_empty_persistent Φ :
    PersistentP ([★ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite /uPred_big_sepM map_to_list_empty. apply _. Qed.
  Global Instance big_sepM_persistent Φ m :
    (∀ k x, PersistentP (Φ k x)) → PersistentP ([★ map] k↦x ∈ m, Φ k x).
  Proof. intros. apply big_sep_persistent, fmap_persistent=>-[??] /=; auto. Qed.

  Global Instance big_sepM_nil_timeless Φ :
    TimelessP ([★ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite /uPred_big_sepM map_to_list_empty. apply _. Qed.
  Global Instance big_sepM_timeless Φ m :
    (∀ k x, TimelessP (Φ k x)) → TimelessP ([★ map] k↦x ∈ m, Φ k x).
  Proof. intro. apply big_sep_timeless, fmap_timeless=> -[??] /=; auto. Qed.
End gmap.


(** ** Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types Φ : A → uPred M.

  Lemma big_sepS_mono Φ Ψ X Y :
    Y ⊆ X → (∀ x, x ∈ Y → Φ x ⊢ Ψ x) →
    ([★ set] x ∈ X, Φ x) ⊢ [★ set] x ∈ Y, Ψ x.
  Proof.
    intros HX HΦ. trans ([★ set] x ∈ Y, Φ x)%I.
    - by apply big_sep_contains, fmap_contains, elements_contains.
    - apply big_sep_mono', Forall2_fmap, Forall_Forall2.
      apply Forall_forall=> x ? /=. by apply HΦ, elem_of_elements.
  Qed.
  Lemma big_sepS_proper Φ Ψ X Y :
    X ≡ Y → (∀ x, x ∈ X → x ∈ Y → Φ x ⊣⊢ Ψ x) →
    ([★ set] x ∈ X, Φ x) ⊣⊢ ([★ set] x ∈ Y, Ψ x).
  Proof.
    move=> /collection_equiv_spec [??] ?; apply (anti_symm (⊢));
      apply big_sepS_mono; eauto using equiv_entails, equiv_entails_sym.
  Qed.

  Lemma big_sepS_ne X n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (uPred_big_sepS (M:=M) X).
  Proof.
    intros Φ1 Φ2 HΦ. apply big_sep_ne, Forall2_fmap.
    apply Forall_Forall2, Forall_true=> x; apply HΦ.
  Qed.
  Lemma big_sepS_proper' X :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (uPred_big_sepS (M:=M) X).
  Proof. intros Φ1 Φ2 HΦ. apply big_sepS_proper; naive_solver. Qed.
  Lemma big_sepS_mono' X :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (uPred_big_sepS (M:=M) X).
  Proof. intros Φ1 Φ2 HΦ. apply big_sepS_mono; naive_solver. Qed.

  Lemma big_sepS_empty Φ : ([★ set] x ∈ ∅, Φ x) ⊣⊢ True.
  Proof. by rewrite /uPred_big_sepS elements_empty. Qed.

  Lemma big_sepS_insert Φ X x :
    x ∉ X → ([★ set] y ∈ {[ x ]} ∪ X, Φ y) ⊣⊢ (Φ x ★ [★ set] y ∈ X, Φ y).
  Proof. intros. by rewrite /uPred_big_sepS elements_union_singleton. Qed.
  Lemma big_sepS_fn_insert {B} (Ψ : A → B → uPred M) f X x b :
    x ∉ X →
       ([★ set] y ∈ {[ x ]} ∪ X, Ψ y (<[x:=b]> f y))
    ⊣⊢ (Ψ x b ★ [★ set] y ∈ X, Ψ y (f y)).
  Proof.
    intros. rewrite big_sepS_insert // fn_lookup_insert.
    apply sep_proper, big_sepS_proper; auto=> y ??.
    by rewrite fn_lookup_insert_ne; last set_solver.
  Qed.
  Lemma big_sepS_fn_insert' Φ X x P :
    x ∉ X → ([★ set] y ∈ {[ x ]} ∪ X, <[x:=P]> Φ y) ⊣⊢ (P ★ [★ set] y ∈ X, Φ y).
  Proof. apply (big_sepS_fn_insert (λ y, id)). Qed.

  Lemma big_sepS_delete Φ X x :
    x ∈ X → ([★ set] y ∈ X, Φ y) ⊣⊢ Φ x ★ [★ set] y ∈ X ∖ {[ x ]}, Φ y.
  Proof.
    intros. rewrite -big_sepS_insert; last set_solver.
    by rewrite -union_difference_L; last set_solver.
  Qed.

  Lemma big_sepS_elem_of Φ X x : x ∈ X → ([★ set] y ∈ X, Φ y) ⊢ Φ x.
  Proof. intros. by rewrite big_sepS_delete // sep_elim_l. Qed.

  Lemma big_sepS_singleton Φ x : ([★ set] y ∈ {[ x ]}, Φ y) ⊣⊢ Φ x.
  Proof. intros. by rewrite /uPred_big_sepS elements_singleton /= right_id. Qed.

  Lemma big_sepS_sepS Φ Ψ X :
    ([★ set] y ∈ X, Φ y ★ Ψ y) ⊣⊢ ([★ set] y ∈ X, Φ y) ★ ([★ set] y ∈ X, Ψ y).
  Proof.
    rewrite /uPred_big_sepS.
    induction (elements X) as [|x l IH]; csimpl; first by rewrite ?right_id.
    by rewrite IH -!assoc (assoc _ (Ψ _)) [(Ψ _ ★ _)%I]comm -!assoc.
  Qed.

  Lemma big_sepS_commute (Ψ: uPred M → uPred M) `{!Proper ((≡) ==> (≡)) Ψ} Φ X :
    Ψ True ⊣⊢ True →
    (∀ P Q, Ψ (P ★ Q) ⊣⊢ Ψ P ★ Ψ Q) →
    Ψ ([★ set] x ∈ X, Φ x) ⊣⊢ ([★ set] x ∈ X, Ψ (Φ x)).
  Proof.
    intros ??. rewrite /uPred_big_sepS.
    induction (elements X) as [|x l IH]; rewrite //= -?IH; auto.
  Qed.
  Lemma big_sepS_op_commute {B : ucmraT}
      (Ψ: B → uPred M) `{!Proper ((≡) ==> (≡)) Ψ} (f : A → B) X :
    Ψ ∅ ⊣⊢ True →
    (∀ x y, Ψ (x ⋅ y) ⊣⊢ Ψ x ★ Ψ y) →
    Ψ ([⋅ set] x ∈ X, f x) ⊣⊢ ([★ set] x ∈ X, Ψ (f x)).
  Proof.
    intros ??. rewrite /big_opS /uPred_big_sepS.
    induction (elements X) as [|x l IH]; rewrite //= -?IH; auto.
  Qed.
  Lemma big_sepS_op_commute1 {B : ucmraT}
      (Ψ: B → uPred M) `{!Proper ((≡) ==> (≡)) Ψ} (f : A → B) X :
    (∀ x y, Ψ (x ⋅ y) ⊣⊢ Ψ x ★ Ψ y) →
    X ≢ ∅ →
    Ψ ([⋅ set] x ∈ X, f x) ⊣⊢ ([★ set] x ∈ X, Ψ (f x)).
  Proof.
    rewrite -elements_empty'. intros ??. rewrite /big_opS /uPred_big_sepS.
    induction (elements X) as [|x [|x' l] IH];
      csimpl in *; rewrite ?right_id -?IH //.
  Qed.

  Lemma big_sepS_later Φ X : ▷ ([★ set] y ∈ X, Φ y) ⊣⊢ ([★ set] y ∈ X, ▷ Φ y).
  Proof. apply (big_sepS_commute _); auto using later_True, later_sep. Qed.

  Lemma big_sepS_always Φ X : □ ([★ set] y ∈ X, Φ y) ⊣⊢ ([★ set] y ∈ X, □ Φ y).
  Proof. apply (big_sepS_commute _); auto using always_pure, always_sep. Qed.

  Lemma big_sepS_always_if q Φ X :
    □?q ([★ set] y ∈ X, Φ y) ⊣⊢ ([★ set] y ∈ X, □?q Φ y).
  Proof. destruct q; simpl; auto using big_sepS_always. Qed.

  Lemma big_sepS_forall Φ X :
    (∀ x, PersistentP (Φ x)) → ([★ set] x ∈ X, Φ x) ⊣⊢ (∀ x, ■ (x ∈ X) → Φ x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply big_sepS_elem_of. }
    rewrite /uPred_big_sepS. setoid_rewrite <-elem_of_elements.
    induction (elements X) as [|x l IH]; csimpl; auto.
    rewrite -always_and_sep_l; apply and_intro.
    - rewrite (forall_elim x) pure_equiv; last by left. by rewrite True_impl.
    - rewrite -IH. apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?. rewrite pure_equiv; last by right.
      by rewrite True_impl.
  Qed.

  Lemma big_sepS_impl Φ Ψ X :
      □ (∀ x, ■ (x ∈ X) → Φ x → Ψ x) ∧ ([★ set] x ∈ X, Φ x) ⊢ [★ set] x ∈ X, Ψ x.
  Proof.
    rewrite always_and_sep_l always_forall.
    setoid_rewrite always_impl; setoid_rewrite always_pure.
    rewrite -big_sepS_forall -big_sepS_sepS. apply big_sepS_mono; auto=> x ?.
    by rewrite -always_wand_impl always_elim wand_elim_l.
  Qed.

  Global Instance big_sepS_empty_persistent Φ : PersistentP ([★ set] x ∈ ∅, Φ x).
  Proof. rewrite /uPred_big_sepS elements_empty. apply _. Qed.
  Global Instance big_sepS_persistent Φ X :
    (∀ x, PersistentP (Φ x)) → PersistentP ([★ set] x ∈ X, Φ x).
  Proof. rewrite /uPred_big_sepS. apply _. Qed.

  Global Instance big_sepS_nil_timeless Φ : TimelessP ([★ set] x ∈ ∅, Φ x).
  Proof. rewrite /uPred_big_sepS elements_empty. apply _. Qed.
  Global Instance big_sepS_timeless Φ X :
    (∀ x, TimelessP (Φ x)) → TimelessP ([★ set] x ∈ X, Φ x).
  Proof. rewrite /uPred_big_sepS. apply _. Qed.
End gset.
End big_op.
