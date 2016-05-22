From iris.algebra Require Import cmra option.
From iris.prelude Require Import list.
From iris.algebra Require Import upred.

Section cofe.
Context {A : cofeT}.

Instance list_dist : Dist (list A) := λ n, Forall2 (dist n).

Lemma list_dist_lookup n l1 l2 : l1 ≡{n}≡ l2 ↔ ∀ i, l1 !! i ≡{n}≡ l2 !! i.
Proof. setoid_rewrite dist_option_Forall2. apply Forall2_lookup. Qed.

Global Instance cons_ne n : Proper (dist n ==> dist n ==> dist n) (@cons A) := _.
Global Instance app_ne n : Proper (dist n ==> dist n ==> dist n) (@app A) := _.
Global Instance length_ne n : Proper (dist n ==> (=)) (@length A) := _.
Global Instance tail_ne n : Proper (dist n ==> dist n) (@tail A) := _.
Global Instance take_ne n : Proper (dist n ==> dist n) (@take A n) := _.
Global Instance drop_ne n : Proper (dist n ==> dist n) (@drop A n) := _.
Global Instance list_lookup_ne n i :
  Proper (dist n ==> dist n) (lookup (M:=list A) i).
Proof. intros ???. by apply dist_option_Forall2, Forall2_lookup. Qed.
Global Instance list_alter_ne n f i :
  Proper (dist n ==> dist n) f →
  Proper (dist n ==> dist n) (alter (M:=list A) f i) := _.
Global Instance list_insert_ne n i :
  Proper (dist n ==> dist n ==> dist n) (insert (M:=list A) i) := _.
Global Instance list_inserts_ne n i :
  Proper (dist n ==> dist n ==> dist n) (@list_inserts A i) := _.
Global Instance list_delete_ne n i :
  Proper (dist n ==> dist n) (delete (M:=list A) i) := _.
Global Instance option_list_ne n : Proper (dist n ==> dist n) (@option_list A).
Proof. intros ???; by apply Forall2_option_list, dist_option_Forall2. Qed.
Global Instance list_filter_ne n P `{∀ x, Decision (P x)} :
  Proper (dist n ==> iff) P →
  Proper (dist n ==> dist n) (filter (B:=list A) P) := _.
Global Instance replicate_ne n :
  Proper (dist n ==> dist n) (@replicate A n) := _.
Global Instance reverse_ne n : Proper (dist n ==> dist n) (@reverse A) := _.
Global Instance last_ne n : Proper (dist n ==> dist n) (@last A).
Proof. intros ???; by apply dist_option_Forall2, Forall2_last. Qed.
Global Instance resize_ne n :
  Proper (dist n ==> dist n ==> dist n) (@resize A n) := _.

Program Definition list_chain
    (c : chain (list A)) (x : A) (k : nat) : chain A :=
  {| chain_car n := from_option x (c n !! k) |}.
Next Obligation. intros c x k n i ?. by rewrite /= (chain_cauchy c n i). Qed.
Instance list_compl : Compl (list A) := λ c,
  match c 0 with
  | [] => []
  | x :: _ => compl ∘ list_chain c x <$> seq 0 (length (c 0))
  end.

Definition list_cofe_mixin : CofeMixin (list A).
Proof.
  split.
  - intros l k. rewrite equiv_Forall2 -Forall2_forall.
    split; induction 1; constructor; intros; try apply equiv_dist; auto.
  - apply _.
  - rewrite /dist /list_dist. eauto using Forall2_impl, dist_S.
  - intros n c; rewrite /compl /list_compl.
    destruct (c 0) as [|x l] eqn:Hc0 at 1.
    { by destruct (chain_cauchy c 0 n); auto with omega. }
    rewrite -(λ H, length_ne _ _ _ (chain_cauchy c 0 n H)); last omega.
    apply Forall2_lookup=> i; apply dist_option_Forall2.
    rewrite list_lookup_fmap. destruct (decide (i < length (c n))); last first.
    { rewrite lookup_seq_ge ?lookup_ge_None_2; auto with omega. }
    rewrite lookup_seq //= (conv_compl n (list_chain c _ _)) /=.
    by destruct (lookup_lt_is_Some_2 (c n) i) as [? ->].
Qed.
Canonical Structure listC := CofeT list_cofe_mixin.
Global Instance list_discrete : Discrete A → Discrete listC.
Proof. induction 2; constructor; try apply (timeless _); auto. Qed.

Global Instance nil_timeless : Timeless (@nil A).
Proof. inversion_clear 1; constructor. Qed.
Global Instance cons_timeless x l : Timeless x → Timeless l → Timeless (x :: l).
Proof. intros ??; inversion_clear 1; constructor; by apply timeless. Qed.
End cofe.

Arguments listC : clear implicits.

(** Functor *)
Instance list_fmap_ne {A B : cofeT} (f : A → B) n:
  Proper (dist n ==> dist n) f → Proper (dist n ==> dist n) (fmap (M:=list) f).
Proof. intros Hf l k ?; by eapply Forall2_fmap, Forall2_impl; eauto. Qed. 
Definition listC_map {A B} (f : A -n> B) : listC A -n> listC B :=
  CofeMor (fmap f : listC A → listC B).
Instance listC_map_ne A B n : Proper (dist n ==> dist n) (@listC_map A B).
Proof. intros f f' ? l; by apply Forall2_fmap, Forall_Forall2, Forall_true. Qed.

Program Definition listCF (F : cFunctor) : cFunctor := {|
  cFunctor_car A B := listC (cFunctor_car F A B);
  cFunctor_map A1 A2 B1 B2 fg := listC_map (cFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply listC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(list_fmap_id x).
  apply list_fmap_setoid_ext=>y. apply cFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -list_fmap_compose.
  apply list_fmap_setoid_ext=>y; apply cFunctor_compose.
Qed.

Instance listCF_contractive F :
  cFunctorContractive F → cFunctorContractive (listCF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply listC_map_ne, cFunctor_contractive.
Qed.
