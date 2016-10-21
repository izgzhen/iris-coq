From iris.algebra Require Export list cmra_big_op.
From iris.base_logic Require Export base_logic.
From iris.prelude Require Import gmap fin_collections functions.
Import uPred.

(* We make use of the bigops on CMRAs, so we first define a (somewhat ad-hoc)
CMRA structure on uPred. *)
Section cmra.
  Context {M : ucmraT}.

  Instance uPred_valid : Valid (uPred M) := λ P, ∀ n x, ✓{n} x → P n x.
  Instance uPred_validN : ValidN (uPred M) := λ n P,
    ∀ n' x, n' ≤ n → ✓{n'} x → P n' x.
  Instance uPred_op : Op (uPred M) := uPred_sep.
  Instance uPred_pcore : PCore (uPred M) := λ _, Some True%I.

  Instance uPred_validN_ne n : Proper (dist n ==> iff) (uPred_validN n).
  Proof. intros P Q HPQ; split=> H n' x ??; by apply HPQ, H. Qed.

  Lemma uPred_validN_alt n (P : uPred M) : ✓{n} P → P ≡{n}≡ True%I.
  Proof.
    unseal=> HP; split=> n' x ??; split; [done|].
    intros _. by apply HP.
  Qed.

  Lemma uPred_cmra_validN_op_l n P Q : ✓{n} (P ★ Q)%I → ✓{n} P.
  Proof.
    unseal. intros HPQ n' x ??.
    destruct (HPQ n' x) as (x1&x2&->&?&?); auto.
    eapply uPred_mono with x1; eauto using cmra_includedN_l.
  Qed.

  Lemma uPred_included P Q : P ≼ Q → Q ⊢ P.
  Proof. intros [P' ->]. apply sep_elim_l. Qed.

  Definition uPred_cmra_mixin : CMRAMixin (uPred M).
  Proof.
    apply cmra_total_mixin; try apply _ || by eauto.
    - intros n P Q ??. by cofe_subst.
    - intros P; split.
      + intros HP n n' x ?. apply HP.
      + intros HP n x. by apply (HP n).
    - intros n P HP n' x ?. apply HP; auto.
    - intros P. by rewrite left_id.
    - intros P Q _. exists True%I. by rewrite left_id.
    - intros n P Q. apply uPred_cmra_validN_op_l.
    - intros n P Q1 Q2 HP HPQ. exists True%I, P; split_and!.
      + by rewrite left_id.
      + move: HP; by rewrite HPQ=> /uPred_cmra_validN_op_l /uPred_validN_alt.
      + move: HP; rewrite HPQ=> /uPred_cmra_validN_op_l /uPred_validN_alt=> ->.
        by rewrite left_id.
  Qed.

  Canonical Structure uPredR :=
    CMRAT (uPred M) uPred_cofe_mixin uPred_cmra_mixin.

  Instance uPred_empty : Empty (uPred M) := True%I.

  Definition uPred_ucmra_mixin : UCMRAMixin (uPred M).
  Proof.
    split; last done.
    - by rewrite /empty /uPred_empty uPred_pure_eq.
    - intros P. by rewrite left_id.
  Qed.

  Canonical Structure uPredUR :=
    UCMRAT (uPred M) uPred_cofe_mixin uPred_cmra_mixin uPred_ucmra_mixin.

  Global Instance uPred_always_homomorphism : UCMRAHomomorphism uPred_always.
  Proof. split; [split|]. apply _. apply always_sep. apply always_pure. Qed.
  Global Instance uPred_always_if_homomorphism b :
    UCMRAHomomorphism (uPred_always_if b).
  Proof. split; [split|]. apply _. apply always_if_sep. apply always_if_pure. Qed.
  Global Instance uPred_later_homomorphism : UCMRAHomomorphism uPred_later.
  Proof. split; [split|]. apply _. apply later_sep. apply later_True. Qed.
  Global Instance uPred_except_0_homomorphism :
    CMRAHomomorphism uPred_except_0.
  Proof. split. apply _. apply except_0_sep. Qed.
  Global Instance uPred_ownM_homomorphism : UCMRAHomomorphism uPred_ownM.
  Proof. split; [split|]. apply _. apply ownM_op. apply ownM_empty'. Qed.
End cmra.

Arguments uPredR : clear implicits.
Arguments uPredUR : clear implicits.

(* Notations *)
Notation "'[★]' Ps" := (big_op (M:=uPredUR _) Ps) (at level 20) : uPred_scope.

Notation "'[★' 'list' ] k ↦ x ∈ l , P" := (big_opL (M:=uPredUR _) l (λ k x, P))
  (at level 200, l at level 10, k, x at level 1, right associativity,
   format "[★  list ]  k ↦ x  ∈  l ,  P") : uPred_scope.
Notation "'[★' 'list' ] x ∈ l , P" := (big_opL (M:=uPredUR _) l (λ _ x, P))
  (at level 200, l at level 10, x at level 1, right associativity,
   format "[★  list ]  x  ∈  l ,  P") : uPred_scope.

Notation "'[★' 'map' ] k ↦ x ∈ m , P" := (big_opM (M:=uPredUR _) m (λ k x, P))
  (at level 200, m at level 10, k, x at level 1, right associativity,
   format "[★  map ]  k ↦ x  ∈  m ,  P") : uPred_scope.
Notation "'[★' 'map' ] x ∈ m , P" := (big_opM (M:=uPredUR _) m (λ _ x, P))
  (at level 200, m at level 10, x at level 1, right associativity,
   format "[★  map ]  x  ∈  m ,  P") : uPred_scope.

Notation "'[★' 'set' ] x ∈ X , P" := (big_opS (M:=uPredUR _) X (λ x, P))
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

Global Instance big_sep_mono' :
  Proper (Forall2 (⊢) ==> (⊢)) (big_op (M:=uPredUR M)).
Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

Lemma big_sep_app Ps Qs : [★] (Ps ++ Qs) ⊣⊢ [★] Ps ★ [★] Qs.
Proof. by rewrite big_op_app. Qed.

Lemma big_sep_contains Ps Qs : Qs `contains` Ps → [★] Ps ⊢ [★] Qs.
Proof. intros. apply uPred_included. by apply: big_op_contains. Qed.
Lemma big_sep_elem_of Ps P : P ∈ Ps → [★] Ps ⊢ P.
Proof. intros. apply uPred_included. by apply: big_sep_elem_of. Qed.

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

  Lemma big_sepL_nil Φ : ([★ list] k↦y ∈ nil, Φ k y) ⊣⊢ True.
  Proof. done. Qed.
  Lemma big_sepL_cons Φ x l :
    ([★ list] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ★ [★ list] k↦y ∈ l, Φ (S k) y.
  Proof. by rewrite big_opL_cons. Qed.
  Lemma big_sepL_singleton Φ x : ([★ list] k↦y ∈ [x], Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opL_singleton. Qed.
  Lemma big_sepL_app Φ l1 l2 :
    ([★ list] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([★ list] k↦y ∈ l1, Φ k y) ★ ([★ list] k↦y ∈ l2, Φ (length l1 + k) y).
  Proof. by rewrite big_opL_app. Qed.

  Lemma big_sepL_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([★ list] k ↦ y ∈ l, Φ k y) ⊢ [★ list] k ↦ y ∈ l, Ψ k y.
  Proof. apply big_opL_forall; apply _. Qed.
  Lemma big_sepL_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([★ list] k ↦ y ∈ l, Φ k y) ⊣⊢ ([★ list] k ↦ y ∈ l, Ψ k y).
  Proof. apply big_opL_proper. Qed.

  Global Instance big_sepL_mono' l :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (⊢))
           (big_opL (M:=uPredUR M) l).
  Proof. intros f g Hf. apply big_opL_forall; apply _ || intros; apply Hf. Qed.

  Lemma big_sepL_lookup Φ l i x :
    l !! i = Some x → ([★ list] k↦y ∈ l, Φ k y) ⊢ Φ i x.
  Proof. intros. apply uPred_included. by apply: big_opL_lookup. Qed.

  Lemma big_sepL_elem_of (Φ : A → uPred M) l x :
    x ∈ l → ([★ list] y ∈ l, Φ y) ⊢ Φ x.
  Proof. intros. apply uPred_included. by apply: big_opL_elem_of. Qed.

  Lemma big_sepL_fmap {B} (f : A → B) (Φ : nat → B → uPred M) l :
    ([★ list] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([★ list] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opL_fmap. Qed.

  Lemma big_sepL_sepL Φ Ψ l :
    ([★ list] k↦x ∈ l, Φ k x ★ Ψ k x)
    ⊣⊢ ([★ list] k↦x ∈ l, Φ k x) ★ ([★ list] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opL_opL. Qed.

  Lemma big_sepL_later Φ l :
    ▷ ([★ list] k↦x ∈ l, Φ k x) ⊣⊢ ([★ list] k↦x ∈ l, ▷ Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_sepL_always Φ l :
    (□ [★ list] k↦x ∈ l, Φ k x) ⊣⊢ ([★ list] k↦x ∈ l, □ Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_sepL_always_if p Φ l :
    □?p ([★ list] k↦x ∈ l, Φ k x) ⊣⊢ ([★ list] k↦x ∈ l, □?p Φ k x).
  Proof. apply (big_opL_commute _). Qed.

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
  Proof. rewrite /big_opL. apply _. Qed.
  Global Instance big_sepL_persistent Φ l :
    (∀ k x, PersistentP (Φ k x)) → PersistentP ([★ list] k↦x ∈ l, Φ k x).
  Proof. rewrite /big_opL. apply _. Qed.
  Global Instance big_sepL_nil_timeless Φ :
    TimelessP ([★ list] k↦x ∈ [], Φ k x).
  Proof. rewrite /big_opL. apply _. Qed.
  Global Instance big_sepL_timeless Φ l :
    (∀ k x, TimelessP (Φ k x)) → TimelessP ([★ list] k↦x ∈ l, Φ k x).
  Proof. rewrite /big_opL. apply _. Qed.
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
    intros Hm HΦ. trans ([★ map] k↦x ∈ m2, Φ k x)%I.
    - apply uPred_included. apply: big_op_contains.
      by apply fmap_contains, map_to_list_contains.
    - apply big_opM_forall; apply _ || auto.
  Qed.
  Lemma big_sepM_proper Φ Ψ m :
    (∀ k x, m !! k = Some x → Φ k x ⊣⊢ Ψ k x) →
    ([★ map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([★ map] k ↦ x ∈ m, Ψ k x).
  Proof. apply big_opM_proper. Qed.

  Global Instance big_sepM_mono' m :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (⊢))
           (big_opM (M:=uPredUR M) m).
  Proof. intros f g Hf. apply big_opM_forall; apply _ || intros; apply Hf. Qed.

  Lemma big_sepM_empty Φ : ([★ map] k↦x ∈ ∅, Φ k x) ⊣⊢ True.
  Proof. by rewrite big_opM_empty. Qed.

  Lemma big_sepM_insert Φ m i x :
    m !! i = None →
    ([★ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ★ [★ map] k↦y ∈ m, Φ k y.
  Proof. apply: big_opM_insert. Qed.

  Lemma big_sepM_delete Φ m i x :
    m !! i = Some x →
    ([★ map] k↦y ∈ m, Φ k y) ⊣⊢ Φ i x ★ [★ map] k↦y ∈ delete i m, Φ k y.
  Proof. apply: big_opM_delete. Qed.

  Lemma big_sepM_lookup Φ m i x :
    m !! i = Some x → ([★ map] k↦y ∈ m, Φ k y) ⊢ Φ i x.
  Proof. intros. apply uPred_included. by apply: big_opM_lookup. Qed. 

  Lemma big_sepM_singleton Φ i x : ([★ map] k↦y ∈ {[i:=x]}, Φ k y) ⊣⊢ Φ i x.
  Proof. by rewrite big_opM_singleton. Qed.

  Lemma big_sepM_fmap {B} (f : A → B) (Φ : K → B → uPred M) m :
    ([★ map] k↦y ∈ f <$> m, Φ k y) ⊣⊢ ([★ map] k↦y ∈ m, Φ k (f y)).
  Proof. by rewrite big_opM_fmap. Qed.

  Lemma big_sepM_insert_override (Φ : K → uPred M) m i x y :
    m !! i = Some x →
    ([★ map] k↦_ ∈ <[i:=y]> m, Φ k) ⊣⊢ ([★ map] k↦_ ∈ m, Φ k).
  Proof. apply: big_opM_insert_override. Qed.

  Lemma big_sepM_fn_insert {B} (Ψ : K → A → B → uPred M) (f : K → B) m i x b :
    m !! i = None →
       ([★ map] k↦y ∈ <[i:=x]> m, Ψ k y (<[i:=b]> f k))
    ⊣⊢ (Ψ i x b ★ [★ map] k↦y ∈ m, Ψ k y (f k)).
  Proof. apply: big_opM_fn_insert. Qed.

  Lemma big_sepM_fn_insert' (Φ : K → uPred M) m i x P :
    m !! i = None →
    ([★ map] k↦y ∈ <[i:=x]> m, <[i:=P]> Φ k) ⊣⊢ (P ★ [★ map] k↦y ∈ m, Φ k).
  Proof. apply: big_opM_fn_insert'. Qed.

  Lemma big_sepM_sepM Φ Ψ m :
       ([★ map] k↦x ∈ m, Φ k x ★ Ψ k x)
    ⊣⊢ ([★ map] k↦x ∈ m, Φ k x) ★ ([★ map] k↦x ∈ m, Ψ k x).
  Proof. apply: big_opM_opM. Qed.

  Lemma big_sepM_later Φ m :
    ▷ ([★ map] k↦x ∈ m, Φ k x) ⊣⊢ ([★ map] k↦x ∈ m, ▷ Φ k x).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_sepM_always Φ m :
    (□ [★ map] k↦x ∈ m, Φ k x) ⊣⊢ ([★ map] k↦x ∈ m, □ Φ k x).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_sepM_always_if p Φ m :
    □?p ([★ map] k↦x ∈ m, Φ k x) ⊣⊢ ([★ map] k↦x ∈ m, □?p Φ k x).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_sepM_forall Φ m :
    (∀ k x, PersistentP (Φ k x)) →
    ([★ map] k↦x ∈ m, Φ k x) ⊣⊢ (∀ k x, m !! k = Some x → Φ k x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply big_sepM_lookup. }
    induction m as [|i x m ? IH] using map_ind; [rewrite ?big_sepM_empty; auto|].
    rewrite big_sepM_insert // -always_and_sep_l. apply and_intro.
    - rewrite (forall_elim i) (forall_elim x) lookup_insert.
      by rewrite pure_equiv // True_impl.
    - rewrite -IH. apply forall_mono=> k; apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?.
      rewrite lookup_insert_ne; last by intros ?; simplify_map_eq.
      by rewrite pure_equiv // True_impl.
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
  Proof. rewrite /big_opM map_to_list_empty. apply _. Qed.
  Global Instance big_sepM_persistent Φ m :
    (∀ k x, PersistentP (Φ k x)) → PersistentP ([★ map] k↦x ∈ m, Φ k x).
  Proof. intros. apply big_sep_persistent, fmap_persistent=>-[??] /=; auto. Qed.
  Global Instance big_sepM_nil_timeless Φ :
    TimelessP ([★ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite /big_opM map_to_list_empty. apply _. Qed.
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
    - apply uPred_included. apply: big_op_contains.
      by apply fmap_contains, elements_contains.
    - apply big_opS_forall; apply _ || auto.
  Qed.
  Lemma big_sepS_proper Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊣⊢ Ψ x) →
    ([★ set] x ∈ X, Φ x) ⊣⊢ ([★ set] x ∈ X, Ψ x).
  Proof. apply: big_opS_proper. Qed.

  Global Instance big_sepS_mono' X :
     Proper (pointwise_relation _ (⊢) ==> (⊢)) (big_opS (M:=uPredUR M) X).
  Proof. intros f g Hf. apply big_opS_forall; apply _ || intros; apply Hf. Qed.

  Lemma big_sepS_empty Φ : ([★ set] x ∈ ∅, Φ x) ⊣⊢ True.
  Proof. by rewrite big_opS_empty. Qed.

  Lemma big_sepS_insert Φ X x :
    x ∉ X → ([★ set] y ∈ {[ x ]} ∪ X, Φ y) ⊣⊢ (Φ x ★ [★ set] y ∈ X, Φ y).
  Proof. apply: big_opS_insert. Qed.

  Lemma big_sepS_fn_insert {B} (Ψ : A → B → uPred M) f X x b :
    x ∉ X →
       ([★ set] y ∈ {[ x ]} ∪ X, Ψ y (<[x:=b]> f y))
    ⊣⊢ (Ψ x b ★ [★ set] y ∈ X, Ψ y (f y)).
  Proof. apply: big_opS_fn_insert. Qed.

  Lemma big_sepS_fn_insert' Φ X x P :
    x ∉ X → ([★ set] y ∈ {[ x ]} ∪ X, <[x:=P]> Φ y) ⊣⊢ (P ★ [★ set] y ∈ X, Φ y).
  Proof. apply: big_opS_fn_insert'. Qed.

  Lemma big_sepS_delete Φ X x :
    x ∈ X → ([★ set] y ∈ X, Φ y) ⊣⊢ Φ x ★ [★ set] y ∈ X ∖ {[ x ]}, Φ y.
  Proof. apply: big_opS_delete. Qed.

  Lemma big_sepS_elem_of Φ X x : x ∈ X → ([★ set] y ∈ X, Φ y) ⊢ Φ x.
  Proof. intros. apply uPred_included. by apply: big_opS_elem_of. Qed. 

  Lemma big_sepS_singleton Φ x : ([★ set] y ∈ {[ x ]}, Φ y) ⊣⊢ Φ x.
  Proof. apply: big_opS_singleton. Qed.

  Lemma big_sepS_sepS Φ Ψ X :
    ([★ set] y ∈ X, Φ y ★ Ψ y) ⊣⊢ ([★ set] y ∈ X, Φ y) ★ ([★ set] y ∈ X, Ψ y).
  Proof. apply: big_opS_opS. Qed.

  Lemma big_sepS_later Φ X : ▷ ([★ set] y ∈ X, Φ y) ⊣⊢ ([★ set] y ∈ X, ▷ Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Lemma big_sepS_always Φ X : □ ([★ set] y ∈ X, Φ y) ⊣⊢ ([★ set] y ∈ X, □ Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Lemma big_sepS_always_if q Φ X :
    □?q ([★ set] y ∈ X, Φ y) ⊣⊢ ([★ set] y ∈ X, □?q Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Lemma big_sepS_forall Φ X :
    (∀ x, PersistentP (Φ x)) → ([★ set] x ∈ X, Φ x) ⊣⊢ (∀ x, ■ (x ∈ X) → Φ x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply big_sepS_elem_of. }
    induction X as [|x m ? IH] using collection_ind_L.
    { rewrite big_sepS_empty; auto. }
    rewrite big_sepS_insert // -always_and_sep_l. apply and_intro.
    - by rewrite (forall_elim x) pure_equiv ?True_impl; last set_solver.
    - rewrite -IH. apply forall_mono=> y. apply impl_intro_l, pure_elim_l=> ?.
      by rewrite pure_equiv ?True_impl; last set_solver.
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
  Proof. rewrite /big_opS elements_empty. apply _. Qed.
  Global Instance big_sepS_persistent Φ X :
    (∀ x, PersistentP (Φ x)) → PersistentP ([★ set] x ∈ X, Φ x).
  Proof. rewrite /big_opS. apply _. Qed.
  Global Instance big_sepS_nil_timeless Φ : TimelessP ([★ set] x ∈ ∅, Φ x).
  Proof. rewrite /big_opS elements_empty. apply _. Qed.
  Global Instance big_sepS_timeless Φ X :
    (∀ x, TimelessP (Φ x)) → TimelessP ([★ set] x ∈ X, Φ x).
  Proof. rewrite /big_opS. apply _. Qed.
End gset.
End big_op.
