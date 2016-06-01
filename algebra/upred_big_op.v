From iris.algebra Require Export upred list.
From iris.prelude Require Import gmap fin_collections functions.
Import uPred.

(** We define the following big operators:

- The operators [ [★] Ps ] and [ [∧] Ps ] fold [★] and [∧] over the list [Ps].
  This operator is not a quantifier, so it binds strongly.
- The operator [ [★ map] k ↦ x ∈ m, P ] asserts that [P] holds separately for
  each [k ↦ x] in the map [m]. This operator is a quantifier, and thus has the
  same precedence as [∀] and [∃].
- The operator [ [★ set] x ∈ X, P ] asserts that [P] holds separately for each
  [x] in the set [X]. This operator is a quantifier, and thus has the same
  precedence as [∀] and [∃]. *)

(** * Big ops over lists *)
(* These are the basic building blocks for other big ops *)
Fixpoint uPred_big_and {M} (Ps : list (uPred M)) : uPred M :=
  match Ps with [] => True | P :: Ps => P ∧ uPred_big_and Ps end%I.
Instance: Params (@uPred_big_and) 1.
Notation "'[∧]' Ps" := (uPred_big_and Ps) (at level 20) : uPred_scope.
Fixpoint uPred_big_sep {M} (Ps : list (uPred M)) : uPred M :=
  match Ps with [] => True | P :: Ps => P ★ uPred_big_sep Ps end%I.
Instance: Params (@uPred_big_sep) 1.
Notation "'[★]' Ps" := (uPred_big_sep Ps) (at level 20) : uPred_scope.

(** * Other big ops *)
(** We use a type class to obtain overloaded notations *)
Definition uPred_big_sepM {M} `{Countable K} {A}
    (m : gmap K A) (Φ : K → A → uPred M) : uPred M :=
  [★] (curry Φ <$> map_to_list m).
Instance: Params (@uPred_big_sepM) 6.
Notation "'[★' 'map' ] k ↦ x ∈ m , P" := (uPred_big_sepM m (λ k x, P))
  (at level 200, m at level 10, k, x at level 1, right associativity,
   format "[★  map ]  k ↦ x  ∈  m ,  P") : uPred_scope.

Definition uPred_big_sepS {M} `{Countable A}
  (X : gset A) (Φ : A → uPred M) : uPred M := [★] (Φ <$> elements X).
Instance: Params (@uPred_big_sepS) 5.
Notation "'[★' 'set' ] x ∈ X , P" := (uPred_big_sepS X (λ x, P))
  (at level 200, X at level 10, x at level 1, right associativity,
   format "[★  set ]  x  ∈  X ,  P") : uPred_scope.

(** * Persistence of lists of uPreds *)
Class PersistentL {M} (Ps : list (uPred M)) :=
  persistentL : Forall PersistentP Ps.
Arguments persistentL {_} _ {_}.

(** * Properties *)
Section big_op.
Context {M : ucmraT}.
Implicit Types Ps Qs : list (uPred M).
Implicit Types A : Type.

(** ** Big ops over lists *)
Global Instance big_and_proper : Proper ((≡) ==> (⊣⊢)) (@uPred_big_and M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.
Global Instance big_sep_proper : Proper ((≡) ==> (⊣⊢)) (@uPred_big_sep M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

Global Instance big_and_ne n : Proper (dist n ==> dist n) (@uPred_big_and M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.
Global Instance big_sep_ne n : Proper (dist n ==> dist n) (@uPred_big_sep M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

Global Instance big_and_mono' : Proper (Forall2 (⊢) ==> (⊢)) (@uPred_big_and M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.
Global Instance big_sep_mono' : Proper (Forall2 (⊢) ==> (⊢)) (@uPred_big_sep M).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

Global Instance big_and_perm : Proper ((≡ₚ) ==> (⊣⊢)) (@uPred_big_and M).
Proof.
  induction 1 as [|P Ps Qs ? IH|P Q Ps|]; simpl; auto.
  - by rewrite IH.
  - by rewrite !assoc (comm _ P).
  - etrans; eauto.
Qed.
Global Instance big_sep_perm : Proper ((≡ₚ) ==> (⊣⊢)) (@uPred_big_sep M).
Proof.
  induction 1 as [|P Ps Qs ? IH|P Q Ps|]; simpl; auto.
  - by rewrite IH.
  - by rewrite !assoc (comm _ P).
  - etrans; eauto.
Qed.

Lemma big_and_app Ps Qs : [∧] (Ps ++ Qs) ⊣⊢ [∧] Ps ∧ [∧] Qs.
Proof. induction Ps as [|?? IH]; by rewrite /= ?left_id -?assoc ?IH. Qed.
Lemma big_sep_app Ps Qs : [★] (Ps ++ Qs) ⊣⊢ [★] Ps ★ [★] Qs.
Proof. by induction Ps as [|?? IH]; rewrite /= ?left_id -?assoc ?IH. Qed.

Lemma big_and_contains Ps Qs : Qs `contains` Ps → [∧] Ps ⊢ [∧] Qs.
Proof.
  intros [Ps' ->]%contains_Permutation. by rewrite big_and_app and_elim_l.
Qed.
Lemma big_sep_contains Ps Qs : Qs `contains` Ps → [★] Ps ⊢ [★] Qs.
Proof.
  intros [Ps' ->]%contains_Permutation. by rewrite big_sep_app sep_elim_l.
Qed.

Lemma big_sep_and Ps : [★] Ps ⊢ [∧] Ps.
Proof. by induction Ps as [|P Ps IH]; simpl; auto with I. Qed.

Lemma big_and_elem_of Ps P : P ∈ Ps → [∧] Ps ⊢ P.
Proof. induction 1; simpl; auto with I. Qed.
Lemma big_sep_elem_of Ps P : P ∈ Ps → [★] Ps ⊢ P.
Proof. induction 1; simpl; auto with I. Qed.

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
  Lemma big_sepM_proper Φ Ψ m1 m2 :
    m1 ≡ m2 → (∀ k x, m1 !! k = Some x → m2 !! k = Some x → Φ k x ⊣⊢ Ψ k x) →
    ([★ map] k ↦ x ∈ m1, Φ k x) ⊣⊢ ([★ map] k ↦ x ∈ m2, Ψ k x).
  Proof.
    (* FIXME: Coq bug since 8.5pl1. Without the @ in [@lookup_weaken] it gives
    File "./algebra/upred_big_op.v", line 114, characters 4-131:
    Anomaly: Uncaught exception Univ.AlreadyDeclared. Please report. *)
    intros [??] ?; apply (anti_symm (⊢)); apply big_sepM_mono;
      eauto using equiv_entails, equiv_entails_sym, @lookup_weaken.
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
    apply sep_proper, big_sepM_proper; auto=> k y ??.
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

  Lemma big_sepM_later Φ m :
    ▷ ([★ map] k↦x ∈ m, Φ k x) ⊣⊢ ([★ map] k↦x ∈ m, ▷ Φ k x).
  Proof.
    rewrite /uPred_big_sepM.
    induction (map_to_list m) as [|[i x] l IH]; csimpl; rewrite ?later_True //.
    by rewrite later_sep IH.
  Qed.

  Lemma big_sepM_always Φ m :
    (□ [★ map] k↦x ∈ m, Φ k x) ⊣⊢ ([★ map] k↦x ∈ m, □ Φ k x).
  Proof.
    rewrite /uPred_big_sepM.
    induction (map_to_list m) as [|[i x] l IH]; csimpl; rewrite ?always_const //.
    by rewrite always_sep IH.
  Qed.

  Lemma big_sepM_always_if p Φ m :
    □?p ([★ map] k↦x ∈ m, Φ k x) ⊣⊢ ([★ map] k↦x ∈ m, □?p Φ k x).
  Proof. destruct p; simpl; auto using big_sepM_always. Qed.

  Lemma big_sepM_forall Φ m :
    (∀ k x, PersistentP (Φ k x)) →
    ([★ map] k↦x ∈ m, Φ k x) ⊣⊢ (∀ k x, m !! k = Some x → Φ k x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, const_elim_l=> ?; by apply big_sepM_lookup. }
    rewrite /uPred_big_sepM. setoid_rewrite <-elem_of_map_to_list.
    induction (map_to_list m) as [|[i x] l IH]; csimpl; auto.
    rewrite -always_and_sep_l; apply and_intro.
    - rewrite (forall_elim i) (forall_elim x) const_equiv; last by left.
      by rewrite True_impl.
    - rewrite -IH. apply forall_mono=> k; apply forall_mono=> y.
      apply impl_intro_l, const_elim_l=> ?. rewrite const_equiv; last by right.
      by rewrite True_impl.
  Qed.

  Lemma big_sepM_impl Φ Ψ m :
    □ (∀ k x, m !! k = Some x → Φ k x → Ψ k x) ∧ ([★ map] k↦x ∈ m, Φ k x)
    ⊢ [★ map] k↦x ∈ m, Ψ k x.
  Proof.
    rewrite always_and_sep_l. do 2 setoid_rewrite always_forall.
    setoid_rewrite always_impl; setoid_rewrite always_const.
    rewrite -big_sepM_forall -big_sepM_sepM. apply big_sepM_mono; auto=> k x ?.
    by rewrite -always_wand_impl always_elim wand_elim_l.
  Qed.
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
    intros [??] ?; apply (anti_symm (⊢)); apply big_sepS_mono;
      eauto using equiv_entails, equiv_entails_sym.
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

  Lemma big_sepS_later Φ X : ▷ ([★ set] y ∈ X, Φ y) ⊣⊢ ([★ set] y ∈ X, ▷ Φ y).
  Proof.
    rewrite /uPred_big_sepS.
    induction (elements X) as [|x l IH]; csimpl; first by rewrite ?later_True.
    by rewrite later_sep IH.
  Qed.

  Lemma big_sepS_always Φ X : □ ([★ set] y ∈ X, Φ y) ⊣⊢ ([★ set] y ∈ X, □ Φ y).
  Proof.
    rewrite /uPred_big_sepS.
    induction (elements X) as [|x l IH]; csimpl; first by rewrite ?always_const.
    by rewrite always_sep IH.
  Qed.

  Lemma big_sepS_always_if q Φ X :
    □?q ([★ set] y ∈ X, Φ y) ⊣⊢ ([★ set] y ∈ X, □?q Φ y).
  Proof. destruct q; simpl; auto using big_sepS_always. Qed.

  Lemma big_sepS_forall Φ X :
    (∀ x, PersistentP (Φ x)) → ([★ set] x ∈ X, Φ x) ⊣⊢ (∀ x, ■ (x ∈ X) → Φ x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> x.
      apply impl_intro_l, const_elim_l=> ?; by apply big_sepS_elem_of. }
    rewrite /uPred_big_sepS. setoid_rewrite <-elem_of_elements.
    induction (elements X) as [|x l IH]; csimpl; auto.
    rewrite -always_and_sep_l; apply and_intro.
    - rewrite (forall_elim x) const_equiv; last by left. by rewrite True_impl.
    - rewrite -IH. apply forall_mono=> y.
      apply impl_intro_l, const_elim_l=> ?. rewrite const_equiv; last by right.
      by rewrite True_impl.
  Qed.

  Lemma big_sepS_impl Φ Ψ X :
      □ (∀ x, ■ (x ∈ X) → Φ x → Ψ x) ∧ ([★ set] x ∈ X, Φ x) ⊢ [★ set] x ∈ X, Ψ x.
  Proof.
    rewrite always_and_sep_l always_forall.
    setoid_rewrite always_impl; setoid_rewrite always_const.
    rewrite -big_sepS_forall -big_sepS_sepS. apply big_sepS_mono; auto=> x ?.
    by rewrite -always_wand_impl always_elim wand_elim_l.
  Qed.
End gset.

(** ** Persistence *)
Global Instance big_and_persistent Ps : PersistentL Ps → PersistentP ([∧] Ps).
Proof. induction 1; apply _. Qed.
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
Global Instance zip_with_persistent {A B} (f : A → B → uPred M) xs ys :
  (∀ x y, PersistentP (f x y)) → PersistentL (zip_with f xs ys).
Proof.
  unfold PersistentL=> ?; revert ys; induction xs=> -[|??]; constructor; auto.
Qed.
End big_op.
