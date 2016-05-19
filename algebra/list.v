From iris.algebra Require Import cmra option.
From iris.prelude Require Import list.
From iris.algebra Require Import upred.

Section cofe.
Context {A : cofeT}.

Instance list_dist : Dist (list A) := λ n, Forall2 (dist n).

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

(* CMRA *)
Section cmra.
  Context {A : cmraT}.
  Implicit Types l : list A.

  Instance list_core : Core (list A) := map core.

  Fixpoint list_op_fix (l1 l2 : list A) : list A :=
    match l1 with
    | [] => l2
    | x :: l1' =>
      match l2 with
      | [] => x :: l1'
      | y :: l2' => op x y :: list_op_fix l1' l2'
      end
    end.

  Instance list_op : Op (list A) := list_op_fix.

  Instance list_valid : Valid (list A) := Forall (λ x, ✓ x).
  Instance list_validN : ValidN (list A) := λ n, Forall (λ x, ✓{n} x).

  Lemma list_op_lookup i l1 l2 : (l1 ⋅ l2) !! i = l1 !! i ⋅ l2 !! i.
  Proof.
    revert i l2; induction l1 as [|a l1]; intros i [|z l2]; cbn; trivial.
    - destruct ((z :: l2) !! i); trivial.
    - destruct ((a :: l1) !! i); trivial.
    - destruct i; cbn; trivial.
  Qed.

  Lemma list_op_ne n (l l' l'' : list A) :
    l' ≡{n}≡ l'' → l ⋅ l' ≡{n}≡ l ⋅ l''.
  Proof.
    revert l' l''.
    induction l; cbn; trivial.
    destruct l'; destruct l''; inversion 1; subst; trivial.
    constructor; [apply cmra_op_ne|]; trivial.
    apply IHl; trivial.
  Qed.

  Lemma list_op_assoc (l l' l'' : list A) :  l ⋅ (l' ⋅ l'') ≡ l ⋅ l' ⋅ l''.
  Proof.
    revert l' l''.
    induction l; cbn; trivial.
    destruct l'; cbn; trivial.
    destruct l''; cbn; trivial.
    rewrite cmra_assoc; constructor; trivial.
  Qed.

  Lemma list_op_comm (l l' : list A) :  l ⋅ l' ≡ l' ⋅ l.
  Proof.
    revert l'.
    induction l; destruct l'; cbn; trivial.
    rewrite cmra_comm; constructor; trivial.
  Qed.

  Lemma list_op_core_l (l : list A) :  core l ⋅ l ≡ l.
  Proof.
    induction l; cbn; trivial.
    constructor; auto using cmra_core_l.
  Qed.

  Lemma list_included_app (x y : A) (l l' : list A) :
    (x :: l) ≼ (y :: l') ↔ (x  ≼ y) ∧ (l ≼ l').
  Proof.
    split.
    - intros [[|z l''] H].
      + inversion H; subst.
        split.
        * exists (core x); rewrite comm; rewrite cmra_core_l; trivial.
        * exists (core l); rewrite list_op_comm; rewrite list_op_core_l; trivial.
      + inversion H; subst. split.
        * exists z; trivial.
        * exists l''; trivial.
    - intros [[z H1] [l'' H2]].
      eexists (z :: l''); constructor; trivial.
  Qed.

  Lemma list_core_preserving (l l' : list A) : l ≼ l' → core l ≼ core l'.
  Proof.
    revert l'.
    induction l; destruct l'; cbn; trivial; intros H.
    - inversion H as [l'' H']; inversion H'; subst; cbn in *.
      eexists; cbn; trivial.
    - inversion H as [[|? ?] H']; inversion H'.
    - apply list_included_app; apply list_included_app in H.
      intuition auto using cmra_core_preserving.
  Qed.

  Lemma list_lookup_op l1 l2 i : (l1 ⋅ l2) !! i = l1 !! i ⋅ l2 !! i.
  Proof.
    revert l2 i; induction l1.
    - induction l2; cbn in *; trivial.
      destruct i as [|i]; cbn; trivial.
    - intros [| z l2] i; cbn.
      + destruct i as [|i]; cbn; trivial. destruct (l1 !! i); trivial.
      + destruct i as [|i]; cbn; trivial.
  Qed.

  Lemma list_lookup_core l i : core l !! i = core (l !! i).
  Proof. revert i; induction l; cbn; trivial. intros [|i]; cbn; trivial. Qed.

  Lemma list_included_spec (l1 l2 : list A) : l1 ≼ l2 ↔ ∀ i, l1 !! i ≼ l2 !! i.
  Proof.
    split.
    - revert l2; induction l1; intros [|z l2] H1; cbn; auto.
      + inversion H1; cbn in *.
        intros [|i]; [eexists (Some z)|eexists (l2 !! i)]; cbn; eauto.
        destruct (l2 !! i); trivial.
      + inversion H1; destruct x; cbn in *;
          match goal with [H : _ ≡ _ |- _] => inversion H end.
      + inversion H1; destruct x; cbn in *.
        * intros i; eexists None.
          match goal with [H : _ ≡ _ |- _] => rewrite H end.
          destruct ((a :: l1) !! i); trivial.
        * intros i.
          match goal with [H : _ ≡ _ |- _] => rewrite H end.
          destruct i; cbn; [eexists (Some c); trivial|].
          apply IHl1.
          exists x; trivial.
    - revert l2; induction l1; intros [|z l2] H1; cbn.
      + eexists []; trivial.
      + eexists; eauto; cbn; trivial.
      + specialize (H1 0); cbn in H1.
        inversion H1 as [x H1']; destruct x; inversion H1'.
      + set (H2 := H1 0); clearbody H2; cbn in H2.
        apply list_included_app; split.
        * inversion H2 as [x H2']; destruct x; inversion H2'; subst;
            [eexists|eexists (core a)]; eauto.
          rewrite comm; rewrite cmra_core_l; trivial.
        * apply IHl1. intros i; apply (H1 (S i)).
  Qed.

  Definition list_cmra_mixin : CMRAMixin (list A).
  Proof.
    split.
    - intros n l l' l'' H; apply list_op_ne; trivial.
    - intros n l l' H ;rewrite H; trivial.
    - intros n l l' H1 H2.
      apply (Forall2_Forall_r _ _ _ _ H1).
      apply Forall_forall => x H3 y H4.
      eapply Forall_forall in H2; [|eauto]; rewrite -H4; trivial.
    - intros l; split.
      + intros H n; apply Forall_forall => x H2.
        eapply Forall_forall in H2; [|eauto]; eapply cmra_valid_validN; trivial.
      + intros H; apply Forall_forall => x H2.
        apply cmra_valid_validN => n.
        eapply Forall_forall in H; eauto.
    - intros n l H. apply Forall_forall; intros.
      eapply Forall_forall in H; eauto using cmra_validN_S.
    - intros l l' l''; apply list_op_assoc.
    - intros l l'; apply list_op_comm.
    - intros l; induction l; [|constructor]; cbn; auto using cmra_core_l.
    - intros l; induction l; [|constructor]; cbn; auto using cmra_core_idemp.
    - apply list_core_preserving.
    - intros n l; induction l; intros [|z l'] H; cbn in *; auto.
      + constructor.
      + inversion H; subst; constructor.
        eapply cmra_validN_op_l; eauto.
        eapply IHl; eauto.
    - intros n l; induction l; intros [|z' l']; intros [|z'' l''] H1 H2;
        try (exfalso; inversion H2; fail); cbn in *.
      + eexists ([], []); repeat split; trivial; cbn in *.
      + eexists ([], _); repeat split; cbn in *; eauto.
      + eexists (_, []); repeat split; do 2 (cbn in *; eauto).
      + edestruct IHl as [[z1 z2] [H31 [H32 H33]]]; cbn in *.
        { inversion H1; trivial. }
        { inversion H2 as [|? ? ? ? H31 H32]; subst; exact H32. }
        edestruct (cmra_extend n a) as [[w1 w2] [H41 [H42 H43]]]; cbn in *.
        { inversion H1; trivial. }
        { inversion H2 as [|? ? ? ? H41 H42]; subst; exact H41. }
        eexists (w1 :: z1, w2 :: z2); repeat split; cbn.
        * inversion H2; subst; constructor;eauto.
        * constructor; auto.
        * constructor; auto.
  Qed.

  Global Instance empty_list {B : Type} : Empty (list B) := [].

  Canonical Structure listR : cmraT := CMRAT list_cofe_mixin list_cmra_mixin.

  Global Instance list_cmra_unit : CMRAUnit listR.
  Proof.
    split.
    - constructor.
    - intros h; reflexivity.
    - intros n H; inversion H; subst; trivial.
  Qed.

  Global Instance list_cmra_discrete : CMRADiscrete A → CMRADiscrete listR.
  Proof. split; [apply _|]. intros m H1.
         apply Forall_forall => x H2; eapply Forall_forall in H1.
         - apply cmra_discrete_valid; eauto. - trivial.
  Qed.

  (** Internalized properties *)
  Lemma list_equivI {M} l1 l2 : (l1 ≡ l2) ⊣⊢ (∀ i, l1 !! i ≡ l2 !! i : uPred M).
  Proof.
    uPred.unseal.
    constructor; split => H'.
    - induction H'; cbn; auto.
      + constructor.
      + intros [|i]; cbn; auto.
        constructor; auto.
    - revert l2 H'; induction l1; intros [|z l2] H'.
      + constructor.
      + specialize (H' 0); inversion H'.
      + specialize (H' 0); inversion H'.
      + constructor; auto.
        * specialize (H' 0); inversion H'; trivial.
        * apply IHl1. intros i; apply (H' (S i)).
  Qed.
  Lemma list_validI {M} l : (✓ l) ⊣⊢ (∀ i, ✓ (l !! i) : uPred M).
  Proof.
    uPred.unseal.
    constructor; split => H'.
    - induction H'; cbn; auto.
      + constructor.
      + intros [|i]; cbn; auto.
    - revert H'; induction l; intros H'.
      + constructor.
      + constructor; auto.
        * specialize (H' 0); trivial.
        * apply IHl. intros i; apply (H' (S i)).
  Qed.
End cmra.

Arguments listR : clear implicits.

Section properties.
  Context {A : cmraT}.
  Implicit Types l : list A.
  Implicit Types a : A.

  Lemma list_op_nil l : l ⋅ [] = l.
  Proof.
    destruct l; trivial.
  Qed.
  Lemma list_op_app l1 l2 l3 :
    length l2 ≤ length l1 → ((l1 ++ l3) ⋅ l2) = (l1 ⋅ l2) ++ l3.
  Proof.
    revert l2 l3; induction l1; cbn.
    - intros []; inversion 1. apply list_op_nil.
    - intros [] l3; inversion 1; cbn in *; auto with omega;
        apply (f_equal (cons _)); trivial; apply IHl1; trivial; auto with omega.
  Qed.

  Lemma list_lookup_validN n l i x : ✓{n} l → l !! i ≡{n}≡ Some x → ✓{n} x.
  Proof.
    intros H1 H2.
    destruct (l !! i) as [z|] eqn:Heq; inversion H2; subst.
    match goal with [H : _ ≡{n}≡ _ |- _] => rewrite -H end.
    eapply Forall_lookup in H1; eauto.
  Qed.
  Lemma list_lookup_valid l i x : ✓ l → l !! i ≡ Some x → ✓ x.
  Proof.
    intros H1 H2.
    destruct (l !! i) as [z|] eqn:Heq; inversion H2; subst.
    match goal with [H : _ ≡ _ |- _] => rewrite -H end.
    eapply Forall_lookup in H1; eauto.
  Qed.

  Global Instance list_persistent l : (∀ x : A, Persistent x) → Persistent l.
  Proof.
    intros H.
    apply equiv_Forall2, Forall2_lookup => i; rewrite list_lookup_core persistent.
    match goal with [|- option_Forall2 _ ?A ?B] => change B with A end.
    destruct (l !! i); constructor; trivial.
  Qed.

  (* Singleton list *)
  Global Instance list_singleton `{CMRAUnit A} : SingletonM nat A (list A) :=
    λ n x, (repeat ∅ n) ++ x :: [].

  Global Instance list_singleton_proper `{CMRAUnit A} i :
    Proper ((≡) ==> (≡)) (list_singleton i).
  Proof. intros x y Hx; induction i; constructor; trivial. Qed.

  Global Instance list_singleton_ne `{CMRAUnit A} n i :
    Proper ((dist n) ==> (dist n)) (list_singleton i).
  Proof. intros x y Hx; induction i; constructor; trivial. Qed.

  Lemma in_list_singleton `{CMRAUnit A} i z x : z ∈ {[i := x]} → z = ∅ ∨ z = x.
  Proof.
    induction i; cbn.
    - inversion_clear 1 as [|? ? ? H2]; [right | inversion H2]; trivial.
    - inversion 1; subst; [left|]; auto.
  Qed.
  Lemma list_Singleton_lookup `{CMRAUnit A} i x : {[ i := x ]} !! i = Some x.
  Proof.
    induction i; cbn; trivial.
  Qed.
  Lemma list_Singleton_lookup_2 `{CMRAUnit A} i j x :
    i ≠ j → {[ i := x ]} !! j = None ∨ {[ i := x ]} !! j = Some ∅.
  Proof. revert j; induction i; destruct j; cbn; auto with omega. Qed.
  Lemma list_singleton_validN `{CMRAUnit A} n i x : ✓{n} {[ i := x ]} ↔ ✓{n} x.
  Proof.
    split.
    - intros H'1; eapply (list_lookup_validN _ _ i); eauto.
      rewrite list_Singleton_lookup; trivial.
    - intros H'2. apply Forall_forall; intros z H'3.
        apply in_list_singleton in H'3; destruct H'3; subst; trivial.
        eapply cmra_valid_validN, cmra_unit_valid.
  Qed.
  Lemma list_singleton_valid `{CMRAUnit A} i x : ✓ ({[ i := x ]}) ↔ ✓ x.
  Proof. rewrite !cmra_valid_validN. by setoid_rewrite list_singleton_validN. Qed.

  Lemma list_core_singleton `{CMRAUnit A} i (x : A) :
    core ({[ i := x ]}) ≡ {[ i := core x ]}.
  Proof.
    induction i; trivial.
    unfold core, cmra_core; cbn.
    constructor; auto.
    etrans; [|apply cmra_core_l]; rewrite comm.
    rewrite cmra_unit_left_id; trivial.
  Qed.
  Lemma list_op_singleton `{CMRAUnit A} i (x y : A) :
    {[ i := x ]} ⋅ {[ i := y ]} ≡ ({[ i := x ⋅ y ]}).
  Proof.
    induction i; cbn; trivial.
    unfold op, cmra_op, list_op; cbn.
    constructor; auto.
    eapply cmra_unit_left_id; eauto.
  Qed.

  Global Instance list_singleton_persistent `{CMRAUnit A} i (x : A) :
  Persistent x → Persistent {[ i := x ]}.
  Proof. intros. by rewrite /Persistent list_core_singleton persistent. Qed.

  (* list update *)
  Lemma list_update_updateP (P : A → Prop) (Q : list A → Prop) l1 x l2 :
    x ~~>: P → (∀ y, P y → Q (l1 ++ y :: l2)) → l1 ++ x :: l2 ~~>: Q.
  Proof.
    intros Hx%option_updateP' HP n mf Hm.
    destruct (Hx n (mf !! (length l1))) as ([y|]&H1&H2); try done.
    { replace (Some x) with ((l1 ++ x :: l2) !! length l1).
      - rewrite -list_op_lookup.
        destruct (((l1 ++ x :: l2) ⋅ mf) !! length l1) eqn:Heq.
        + eapply Forall_lookup in Hm; eauto; trivial.
        + contradict Heq.
          rewrite list_op_lookup.
          rewrite lookup_app_r; trivial.
          replace (length l1 - length l1) with 0 by omega.
          match goal with
            [|- _ ⋅ ?A ≠ _] => destruct A; unfold op, cmra_op; cbn; congruence
          end.
      - rewrite lookup_app_r; trivial.
        replace (length l1 - length l1) with 0 by omega; trivial.
    }
    eexists. split.
    { apply HP; apply H1. }
    apply Forall_lookup => i z H'.
    rewrite list_op_lookup in H'.
    destruct (lt_dec i (length l1)).
    { rewrite lookup_app_l in H'; trivial.
      eapply Forall_lookup in Hm; eauto.
      rewrite list_op_lookup.
      rewrite lookup_app_l; eauto.
    }
    destruct (eq_nat_dec i (length l1)); subst.
    { rewrite lookup_app_r in H'; trivial.
      replace (length l1 - length l1) with 0 in H' by omega.
      cbn in H'.
      rewrite H' in H2; trivial.
    }
    {
      rewrite lookup_app_r in H'; try omega.
      destruct (i - length l1) as [|j] eqn:Heq; try omega.
      eapply Forall_lookup in Hm; eauto.
      rewrite list_op_lookup; trivial.
      erewrite (lookup_app_r _ _ i); auto with omega.
      rewrite Heq; trivial.
    }
  Qed.

  Lemma list_update_update l1 l2 x y : x ~~> y → (l1 ++ x :: l2) ~~> (l1 ++ y :: l2).
  Proof.
    rewrite !cmra_update_updateP => H; eauto using list_update_updateP with subst.
  Qed.

  Lemma list_op_add_unit `{CMRAUnit A} l n mf :
    ✓{n} (l ⋅ mf) → ✓{n} ((l ++ (repeat ∅ (length mf - length l))) ⋅ mf).
  Proof.
    revert l mf; induction l; [induction mf|]; cbn; trivial.
    - inversion_clear 1; subst; constructor.
      + rewrite cmra_unit_left_id; trivial.
      + replace (length mf) with (length mf - 0) by omega. apply IHmf; trivial.
    - intros [|z mf]; cbn.
      + rewrite ?list_op_nil app_nil_r; trivial.
      + inversion_clear 1; subst; constructor; trivial.
        apply IHl; trivial.
  Qed.
  Lemma list_allocate_lemma `{CMRAUnit A} l x n mf :
    ✓ x → ✓{n} (l ⋅ mf) → ✓{n} ((l ++ {[ (length mf - length l) := x]}) ⋅ mf).
  Proof.
    intros H1 H2. rewrite app_assoc. rewrite list_op_app.
    - apply Forall_app; split; [|repeat constructor; apply cmra_valid_validN; trivial].
      apply list_op_add_unit; trivial.
    - rewrite app_length repeat_length; omega.
  Qed.

  (* list allocate update *)
  Lemma list_alloc_updateP `{CMRAUnit A} (P : A → Prop) (Q : list A → Prop) l x :
    ✓ x → (∀ i, Q (l ++ {[ i := x]})) → l ~~>: Q.
  Proof.
    intros Hx HP n mf Hm.
    exists (l ++ {[ (length mf - length l) := x]}); split; auto using list_allocate_lemma.
  Qed.

  Lemma list_alloc_update `{CMRAUnit A} l x :
    ✓ x → l ~~>: λ l', ∃ i, l' = (l ++ {[ i := x]}).
  Proof. intros H1 n; eauto using list_allocate_lemma. Qed.

  (* Applying a local update at a position we own is a local update. *)
  Global Instance list_alter_update `{LocalUpdate A Lv L} i :
    LocalUpdate (λ L, ∃ x, L !! i = Some x ∧ Lv x) (alter L i).
  Proof.
    split; first apply _.
    intros n l1 l2 (x&Hix&?) Hm. apply Forall2_lookup => j.
    destruct (decide (i = j)) as [->|Heq].
    - revert l1 l2 Hix Hm.
      induction j; intros [|z l1] [|z' l2] Hix Hm; cbn;
        try congruence; try inversion Hix; subst.
      + constructor; trivial.
      + constructor.
        eapply local_updateN; eauto. inversion Hm; trivial.
      + unfold op, cmra_op; cbn.
        match goal with [|- option_Forall2 _ ?A ?A] => destruct A; constructor; trivial end.
      + unfold op, cmra_op; cbn.
        apply IHj; trivial.
        inversion Hm; trivial.
    - revert i Heq l1 l2 Hix Hm.
      induction j; intros i Heq [|z l1] [|z' l2] Hix Hm; cbn;
        try congruence; try inversion Hix; subst.
      + unfold op, cmra_op; destruct i; cbn; constructor; trivial.
      + unfold op, cmra_op; destruct i; cbn; constructor; trivial.
        inversion H2; subst.
        eapply local_updateN; eauto. inversion Hm; trivial.
      + unfold op, cmra_op; cbn.
        unfold op, cmra_op; destruct i; cbn;
          match goal with [|- option_Forall2 _ ?A ?A] =>
                          destruct A; constructor; trivial end.
      + unfold op, cmra_op; destruct i; cbn.
        * match goal with [|- option_Forall2 _ ?A ?A] =>
                          destruct A; constructor; trivial end.
        * apply IHj; eauto.
          inversion Hm; trivial.
  Qed.

  (* altering a singleton is just altering the underlying element. *)
  Lemma list_alter_singleton `{CMRAUnit A} {L : A → A} i x :
    alter L i {[i := x]} = {[i := L x]}.
  Proof.
    induction i; simpl; trivial.
    apply (f_equal (cons _)); simpl; trivial.
  Qed.

End properties.

(** Functor *)
Instance list_fmap_cmra_monotone {A B : cmraT} (f : A → B)
  `{!CMRAMonotone f} : CMRAMonotone (map f).
Proof.
  split; try apply _.
  - intros n l H1. induction l; inversion H1; constructor.
    + apply validN_preserving; trivial.
    + apply IHl; trivial.
  - intros l1 l2 H1.
    apply list_included_spec.
    intros i.
    do 2 rewrite list_lookup_fmap.
    apply included_preserving; eauto.
    typeclasses eauto.
    apply list_included_spec; trivial.
Qed.

Program Definition listRF (F : rFunctor) : rFunctor := {|
  rFunctor_car A B := listR (rFunctor_car F A B);
  rFunctor_map A1 A2 B1 B2 fg := listC_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros F ???? n f g Hfg; apply listC_map_ne, rFunctor_ne.
Qed.
Next Obligation.
  intros F ?? x; cbn in *.
  apply equiv_Forall2, Forall2_fmap_l, Forall_Forall2, Forall_forall;
    auto using rFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x; cbn in *.
  rewrite -list_fmap_compose.
  apply equiv_Forall2, Forall2_fmap, Forall_Forall2, Forall_forall.
  intros; apply rFunctor_compose.
Qed.
Instance listRF_contractive F :
  rFunctorContractive F → rFunctorContractive (listRF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply listC_map_ne, rFunctor_contractive.
Qed.