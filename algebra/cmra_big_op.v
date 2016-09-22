From iris.algebra Require Export cmra list.
From iris.prelude Require Import functions gmap.

(** The operator [ [⋅] Ps ] folds [⋅] over the list [Ps]. This operator is not a
quantifier, so it binds strongly.

Apart from that, we define the following big operators with binders build in:

- The operator [ [⋅ list] k ↦ x ∈ l, P ] folds over a list [l]. The binder [x]
  refers to each element at index [k].
- The operator [ [⋅ map] k ↦ x ∈ m, P ] folds over a map [m]. The binder [x]
  refers to each element at index [k].
- The operator [ [⋅ set] x ∈ X, P ] folds over a set [m]. The binder [x] refers
  to each element.

Since these big operators are like quantifiers, they have the same precedence as
[∀] and [∃]. *)

(** * Big ops over lists *)
(* This is the basic building block for other big ops *)
Fixpoint big_op {M : ucmraT} (xs : list M) : M :=
  match xs with [] => ∅ | x :: xs => x ⋅ big_op xs end.
Arguments big_op _ !_ /.
Instance: Params (@big_op) 1.
Notation "'[⋅]' xs" := (big_op xs) (at level 20) : C_scope.

(** * Other big ops *)
Definition big_opL {M : ucmraT} {A} (l : list A) (f : nat → A → M) : M :=
  [⋅] (imap f l).
Instance: Params (@big_opL) 2.
Typeclasses Opaque big_opL.
Notation "'[⋅' 'list' ] k ↦ x ∈ l , P" := (big_opL l (λ k x, P))
  (at level 200, l at level 10, k, x at level 1, right associativity,
   format "[⋅  list ]  k ↦ x  ∈  l ,  P") : C_scope.
Notation "'[⋅' 'list' ] x ∈ l , P" := (big_opL l (λ _ x, P))
  (at level 200, l at level 10, x at level 1, right associativity,
   format "[⋅  list ]  x  ∈  l ,  P") : C_scope.

Definition big_opM {M : ucmraT} `{Countable K} {A}
    (m : gmap K A) (f : K → A → M) : M :=
  [⋅] (curry f <$> map_to_list m).
Instance: Params (@big_opM) 6.
Typeclasses Opaque big_opM.
Notation "'[⋅' 'map' ] k ↦ x ∈ m , P" := (big_opM m (λ k x, P))
  (at level 200, m at level 10, k, x at level 1, right associativity,
   format "[⋅  map ]  k ↦ x  ∈  m ,  P") : C_scope.

Definition big_opS {M : ucmraT} `{Countable A}
  (X : gset A) (f : A → M) : M := [⋅] (f <$> elements X).
Instance: Params (@big_opS) 5.
Typeclasses Opaque big_opS.
Notation "'[⋅' 'set' ] x ∈ X , P" := (big_opS X (λ x, P))
  (at level 200, X at level 10, x at level 1, right associativity,
   format "[⋅  set ]  x  ∈  X ,  P") : C_scope.

(** * Properties about big ops *)
Section big_op.
Context {M : ucmraT}.
Implicit Types xs : list M.

(** * Big ops *)
Global Instance big_op_ne n : Proper (dist n ==> dist n) (@big_op M).
Proof. by induction 1; simpl; repeat apply (_ : Proper (_ ==> _ ==> _) op). Qed.
Global Instance big_op_proper : Proper ((≡) ==> (≡)) (@big_op M) := ne_proper _.

Lemma big_op_nil : [⋅] (@nil M) = ∅.
Proof. done. Qed.
Lemma big_op_cons x xs : [⋅] (x :: xs) = x ⋅ [⋅] xs.
Proof. done. Qed.
Lemma big_op_app xs ys : [⋅] (xs ++ ys) ≡ [⋅] xs ⋅ [⋅] ys.
Proof.
  induction xs as [|x xs IH]; simpl; first by rewrite ?left_id.
  by rewrite IH assoc.
Qed.

Lemma big_op_mono xs ys : Forall2 (≼) xs ys → [⋅] xs ≼ [⋅] ys.
Proof. induction 1 as [|x y xs ys Hxy ? IH]; simpl; eauto using cmra_mono. Qed.

Global Instance big_op_permutation : Proper ((≡ₚ) ==> (≡)) (@big_op M).
Proof.
  induction 1 as [|x xs1 xs2 ? IH|x y xs|xs1 xs2 xs3]; simpl; auto.
  - by rewrite IH.
  - by rewrite !assoc (comm _ x).
  - by trans (big_op xs2).
Qed.

Lemma big_op_contains xs ys : xs `contains` ys → [⋅] xs ≼ [⋅] ys.
Proof.
  intros [xs' ->]%contains_Permutation.
  rewrite big_op_app; apply cmra_included_l.
Qed.

Lemma big_op_delete xs i x : xs !! i = Some x → x ⋅ [⋅] delete i xs ≡ [⋅] xs.
Proof. by intros; rewrite {2}(delete_Permutation xs i x). Qed.

Lemma big_sep_elem_of xs x : x ∈ xs → x ≼ [⋅] xs.
Proof.
  intros [i ?]%elem_of_list_lookup. rewrite -big_op_delete //.
  apply cmra_included_l.
Qed.

(** ** Big ops over lists *)
Section list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types f g : nat → A → M.

  Lemma big_opL_mono f g l :
    (∀ k y, l !! k = Some y → f k y ≼ g k y) →
    ([⋅ list] k ↦ y ∈ l, f k y) ≼ [⋅ list] k ↦ y ∈ l, g k y.
  Proof.
    intros Hf. apply big_op_mono.
    revert f g Hf. induction l as [|x l IH]=> f g Hf; first constructor.
    rewrite !imap_cons; constructor; eauto.
  Qed.
  Lemma big_opL_proper f g l :
    (∀ k y, l !! k = Some y → f k y ≡ g k y) →
    ([⋅ list] k ↦ y ∈ l, f k y) ≡ ([⋅ list] k ↦ y ∈ l, g k y).
  Proof.
    intros Hf; apply big_op_proper.
    revert f g Hf. induction l as [|x l IH]=> f g Hf; first constructor.
    rewrite !imap_cons; constructor; eauto.
  Qed.

  Global Instance big_opL_ne l n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> (dist n))
           (big_opL (M:=M) l).
  Proof.
    intros f g Hf. apply big_op_ne.
    revert f g Hf. induction l as [|x l IH]=> f g Hf; first constructor.
    rewrite !imap_cons; constructor. by apply Hf. apply IH=> n'; apply Hf.
  Qed.
  Global Instance big_opL_proper' l :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (≡))
           (big_opL (M:=M) l).
  Proof. intros f1 f2 Hf. by apply big_opL_proper; intros; last apply Hf. Qed.
  Global Instance big_opL_mono' l :
    Proper (pointwise_relation _ (pointwise_relation _ (≼)) ==> (≼))
           (big_opL (M:=M) l).
  Proof. intros f1 f2 Hf. by apply big_opL_mono; intros; last apply Hf. Qed.

  Lemma big_opL_nil f : ([⋅ list] k↦y ∈ nil, f k y) = ∅.
  Proof. done. Qed.

  Lemma big_opL_cons f x l :
    ([⋅ list] k↦y ∈ x :: l, f k y) = f 0 x ⋅ [⋅ list] k↦y ∈ l, f (S k) y.
  Proof. by rewrite /big_opL imap_cons. Qed.

  Lemma big_opL_singleton f x : ([⋅ list] k↦y ∈ [x], f k y) ≡ f 0 x.
  Proof. by rewrite big_opL_cons big_opL_nil right_id. Qed.

  Lemma big_opL_app f l1 l2 :
    ([⋅ list] k↦y ∈ l1 ++ l2, f k y)
    ≡ ([⋅ list] k↦y ∈ l1, f k y) ⋅ ([⋅ list] k↦y ∈ l2, f (length l1 + k) y).
  Proof. by rewrite /big_opL imap_app big_op_app. Qed.

  Lemma big_opL_lookup f l i x :
    l !! i = Some x → f i x ≼ [⋅ list] k↦y ∈ l, f k y.
  Proof.
    intros. rewrite -(take_drop_middle l i x) // big_opL_app big_opL_cons.
    rewrite Nat.add_0_r take_length_le; eauto using lookup_lt_Some, Nat.lt_le_incl.
    eapply transitivity, cmra_included_r; eauto using cmra_included_l.
  Qed.

  Lemma big_opL_elem_of (f : A → M) l x : x ∈ l → f x ≼ [⋅ list] y ∈ l, f y.
  Proof.
    intros [i ?]%elem_of_list_lookup; eauto using (big_opL_lookup (λ _, f)).
  Qed.

  Lemma big_opL_fmap {B} (h : A → B) (f : nat → B → M) l :
    ([⋅ list] k↦y ∈ h <$> l, f k y) ≡ ([⋅ list] k↦y ∈ l, f k (h y)).
  Proof. by rewrite /big_opL imap_fmap. Qed.

  Lemma big_opL_opL f g l :
    ([⋅ list] k↦x ∈ l, f k x ⋅ g k x)
    ≡ ([⋅ list] k↦x ∈ l, f k x) ⋅ ([⋅ list] k↦x ∈ l, g k x).
  Proof.
    revert f g; induction l as [|x l IH]=> f g.
    { by rewrite !big_opL_nil left_id. }
    rewrite !big_opL_cons IH.
    by rewrite -!assoc (assoc _ (g _ _)) [(g _ _ ⋅ _)]comm -!assoc.
  Qed.
End list.


(** ** Big ops over finite maps *)
Section gmap.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types f g : K → A → M.

  Lemma big_opM_mono f g m1 m2 :
    m1 ⊆ m2 → (∀ k x, m2 !! k = Some x → f k x ≼ g k x) →
    ([⋅ map] k ↦ x ∈ m1, f k x) ≼ [⋅ map] k ↦ x ∈ m2, g k x.
  Proof.
    intros HX Hf. trans ([⋅ map] k↦x ∈ m2, f k x).
    - by apply big_op_contains, fmap_contains, map_to_list_contains.
    - apply big_op_mono, Forall2_fmap, Forall_Forall2.
      apply Forall_forall=> -[i x] ? /=. by apply Hf, elem_of_map_to_list.
  Qed.
  Lemma big_opM_proper f g m :
    (∀ k x, m !! k = Some x → f k x ≡ g k x) →
    ([⋅ map] k ↦ x ∈ m, f k x) ≡ ([⋅ map] k ↦ x ∈ m, g k x).
  Proof.
    intros Hf. apply big_op_proper, equiv_Forall2, Forall2_fmap, Forall_Forall2.
    apply Forall_forall=> -[i x] ? /=. by apply Hf, elem_of_map_to_list.
  Qed.

  Global Instance big_opM_ne m n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> (dist n))
           (big_opM (M:=M) m).
  Proof.
    intros f1 f2 Hf. apply big_op_ne, Forall2_fmap.
    apply Forall_Forall2, Forall_true=> -[i x]; apply Hf.
  Qed.
  Global Instance big_opM_proper' m :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (≡))
           (big_opM (M:=M) m).
  Proof. intros f1 f2 Hf. by apply big_opM_proper; intros; last apply Hf. Qed.
  Global Instance big_opM_mono' m :
    Proper (pointwise_relation _ (pointwise_relation _ (≼)) ==> (≼))
           (big_opM (M:=M) m).
  Proof. intros f1 f2 Hf. by apply big_opM_mono; intros; last apply Hf. Qed.

  Lemma big_opM_empty f : ([⋅ map] k↦x ∈ ∅, f k x) = ∅.
  Proof. by rewrite /big_opM map_to_list_empty. Qed.

  Lemma big_opM_insert f m i x :
    m !! i = None →
    ([⋅ map] k↦y ∈ <[i:=x]> m, f k y) ≡ f i x ⋅ [⋅ map] k↦y ∈ m, f k y.
  Proof. intros ?. by rewrite /big_opM map_to_list_insert. Qed.

  Lemma big_opM_delete f m i x :
    m !! i = Some x →
    ([⋅ map] k↦y ∈ m, f k y) ≡ f i x ⋅ [⋅ map] k↦y ∈ delete i m, f k y.
  Proof.
    intros. rewrite -big_opM_insert ?lookup_delete //.
    by rewrite insert_delete insert_id.
  Qed.

  Lemma big_opM_lookup f m i x :
    m !! i = Some x → f i x ≼ [⋅ map] k↦y ∈ m, f k y.
  Proof. intros. rewrite big_opM_delete //. apply cmra_included_l. Qed.

  Lemma big_opM_singleton f i x : ([⋅ map] k↦y ∈ {[i:=x]}, f k y) ≡ f i x.
  Proof.
    rewrite -insert_empty big_opM_insert/=; last auto using lookup_empty.
    by rewrite big_opM_empty right_id.
  Qed.

  Lemma big_opM_fmap {B} (h : A → B) (f : K → B → M) m :
    ([⋅ map] k↦y ∈ h <$> m, f k y) ≡ ([⋅ map] k↦y ∈ m, f k (h y)).
  Proof.
    rewrite /big_opM map_to_list_fmap -list_fmap_compose.
    f_equiv; apply reflexive_eq, list_fmap_ext. by intros []. done.
  Qed.

  Lemma big_opM_insert_override (f : K → M) m i x y :
    m !! i = Some x →
    ([⋅ map] k↦_ ∈ <[i:=y]> m, f k) ≡ ([⋅ map] k↦_ ∈ m, f k).
  Proof.
    intros. rewrite -insert_delete big_opM_insert ?lookup_delete //.
    by rewrite -big_opM_delete.
  Qed.

  Lemma big_opM_fn_insert {B} (g : K → A → B → M) (f : K → B) m i (x : A) b :
    m !! i = None →
      ([⋅ map] k↦y ∈ <[i:=x]> m, g k y (<[i:=b]> f k))
    ≡ (g i x b ⋅ [⋅ map] k↦y ∈ m, g k y (f k)).
  Proof.
    intros. rewrite big_opM_insert // fn_lookup_insert.
    apply cmra_op_proper', big_opM_proper; auto=> k y ?.
    by rewrite fn_lookup_insert_ne; last set_solver.
  Qed.
  Lemma big_opM_fn_insert' (f : K → M) m i x P :
    m !! i = None →
    ([⋅ map] k↦y ∈ <[i:=x]> m, <[i:=P]> f k) ≡ (P ⋅ [⋅ map] k↦y ∈ m, f k).
  Proof. apply (big_opM_fn_insert (λ _ _, id)). Qed.

  Lemma big_opM_opM f g m :
       ([⋅ map] k↦x ∈ m, f k x ⋅ g k x)
    ≡ ([⋅ map] k↦x ∈ m, f k x) ⋅ ([⋅ map] k↦x ∈ m, g k x).
  Proof.
    rewrite /big_opM.
    induction (map_to_list m) as [|[i x] l IH]; csimpl; rewrite ?right_id //.
    by rewrite IH -!assoc (assoc _ (g _ _)) [(g _ _ ⋅ _)]comm -!assoc.
  Qed.
End gmap.


(** ** Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types f : A → M.

  Lemma big_opS_mono f g X Y :
    X ⊆ Y → (∀ x, x ∈ Y → f x ≼ g x) →
    ([⋅ set] x ∈ X, f x) ≼ [⋅ set] x ∈ Y, g x.
  Proof.
    intros HX Hf. trans ([⋅ set] x ∈ Y, f x).
    - by apply big_op_contains, fmap_contains, elements_contains.
    - apply big_op_mono, Forall2_fmap, Forall_Forall2.
      apply Forall_forall=> x ? /=. by apply Hf, elem_of_elements.
  Qed.
  Lemma big_opS_proper f g X Y :
    X ≡ Y → (∀ x, x ∈ X → x ∈ Y → f x ≡ g x) →
    ([⋅ set] x ∈ X, f x) ≡ ([⋅ set] x ∈ Y, g x).
  Proof.
    intros HX Hf. trans ([⋅ set] x ∈ Y, f x).
    - apply big_op_permutation. by rewrite HX.
    - apply big_op_proper, equiv_Forall2, Forall2_fmap, Forall_Forall2.
      apply Forall_forall=> x ? /=.
      apply Hf; first rewrite HX; by apply elem_of_elements.
  Qed.

  Lemma big_opS_ne X n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (big_opS (M:=M) X).
  Proof.
    intros f1 f2 Hf. apply big_op_ne, Forall2_fmap.
    apply Forall_Forall2, Forall_true=> x; apply Hf.
  Qed.
  Lemma big_opS_proper' X :
    Proper (pointwise_relation _ (≡) ==> (≡)) (big_opS (M:=M) X).
  Proof. intros f1 f2 Hf. apply big_opS_proper; naive_solver. Qed.
  Lemma big_opS_mono' X :
    Proper (pointwise_relation _ (≼) ==> (≼)) (big_opS (M:=M) X).
  Proof. intros f1 f2 Hf. apply big_opS_mono; naive_solver. Qed.

  Lemma big_opS_empty f : ([⋅ set] x ∈ ∅, f x) = ∅.
  Proof. by rewrite /big_opS elements_empty. Qed.

  Lemma big_opS_insert f X x :
    x ∉ X → ([⋅ set] y ∈ {[ x ]} ∪ X, f y) ≡ (f x ⋅ [⋅ set] y ∈ X, f y).
  Proof. intros. by rewrite /big_opS elements_union_singleton. Qed.
  Lemma big_opS_fn_insert {B} (f : A → B → M) h X x b :
    x ∉ X →
       ([⋅ set] y ∈ {[ x ]} ∪ X, f y (<[x:=b]> h y))
    ≡ (f x b ⋅ [⋅ set] y ∈ X, f y (h y)).
  Proof.
    intros. rewrite big_opS_insert // fn_lookup_insert.
    apply cmra_op_proper', big_opS_proper; auto=> y ??.
    by rewrite fn_lookup_insert_ne; last set_solver.
  Qed.
  Lemma big_opS_fn_insert' f X x P :
    x ∉ X → ([⋅ set] y ∈ {[ x ]} ∪ X, <[x:=P]> f y) ≡ (P ⋅ [⋅ set] y ∈ X, f y).
  Proof. apply (big_opS_fn_insert (λ y, id)). Qed.

  Lemma big_opS_delete f X x :
    x ∈ X → ([⋅ set] y ∈ X, f y) ≡ f x ⋅ [⋅ set] y ∈ X ∖ {[ x ]}, f y.
  Proof.
    intros. rewrite -big_opS_insert; last set_solver.
    by rewrite -union_difference_L; last set_solver.
  Qed.

  Lemma big_opS_elem_of f X x : x ∈ X → f x ≼ [⋅ set] y ∈ X, f y.
  Proof. intros. rewrite big_opS_delete //. apply cmra_included_l. Qed.

  Lemma big_opS_singleton f x : ([⋅ set] y ∈ {[ x ]}, f y) ≡ f x.
  Proof. intros. by rewrite /big_opS elements_singleton /= right_id. Qed.

  Lemma big_opS_opS f g X :
    ([⋅ set] y ∈ X, f y ⋅ g y) ≡ ([⋅ set] y ∈ X, f y) ⋅ ([⋅ set] y ∈ X, g y).
  Proof.
    rewrite /big_opS.
    induction (elements X) as [|x l IH]; csimpl; first by rewrite ?right_id.
    by rewrite IH -!assoc (assoc _ (g _)) [(g _ ⋅ _)]comm -!assoc.
  Qed.
End gset.
End big_op.
