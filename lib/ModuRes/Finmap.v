Require Import MetricCore.
Require Import PreoMet.
Require Import Arith Min Max List.

Set Bullet Behavior "Strict Subproofs".

Module BoolDec.
  Definition U := bool.
  Definition eq_dec (x y : U) : { x = y } + {x <> y}.
  Proof.
    decide equality.
  Defined.
End BoolDec.

Module D := Coq.Logic.Eqdep_dec.DecidableEqDep(BoolDec).

Module CompDec.
  Definition U := comparison.
  Definition eq_dec (x y : U) : { x = y } + {x <> y}.
  Proof.
    decide equality.
  Defined.
End CompDec.

Module DC := Coq.Logic.Eqdep_dec.DecidableEqDep(CompDec).

Class Comparer (T : Type) := comp : T -> T -> comparison.
Class Order (T :Type) := leq : relation T.

Class comparable (T : Type) {cT : Comparer T} {ord : Order T} `{ord_part : PartialOrder _ (@eq T) leq} :=
  compat_compare : forall x y, match comp x y with
                                 | Lt => leq x y /\ x <> y
                                 | Eq => x = y
                                 | Gt => leq y x /\ x <> y
                               end.

Instance Comp_nat : Comparer nat := nat_compare.
Instance PreOrd_le : PreOrder le.
Proof.
  split.
  - intros x; auto.
  - intros x y z Hxy Hxz; eapply le_trans; eassumption.
Qed.
Instance PartOrd_nat : PartialOrder (@eq nat) le.
Proof.
  split; [intros; subst; split; reflexivity |].
  unfold Basics.flip; intros [HLe HLe']; auto with arith.
Qed.
Instance ord_nat : Order nat := le.
Instance comp_nat : comparable nat.
Proof.
  intros x y; remember (comp x y) as C; symmetry in HeqC; destruct C; unfold comp, Comp_nat in *.
  - apply nat_compare_eq; assumption.
  - rewrite <- nat_compare_lt in HeqC; split; unfold leq, ord_nat; omega.
  - rewrite <- nat_compare_gt in HeqC; split; unfold leq, ord_nat; omega.
Qed.

Infix "∈" := In (at level 40, no associativity).

Section Sortedness.
  Context {T} `{compT : comparable T}.

  Lemma comp_self_Eq k : comp k k = Eq.
  Proof.
    assert (HT := compat_compare k k); destruct (comp k k); intuition.
  Qed.

  Lemma comp_gt_Gt m k (HGt : leq m k /\ k <> m) : comp k m = Gt.
  Proof.
    assert (HT := compat_compare k m); destruct (comp k m); intuition.
    contradiction H2; assert (HT := ord_part k m); simpl in HT.
    apply <- HT; clear HT; split; assumption.
  Qed.

  Lemma comp_lt_Lt m k (HLt : leq k m /\ k <> m) : comp k m = Lt.
  Proof.
    assert (HT := compat_compare k m); destruct (comp k m); intuition.
    contradiction H2; assert (HT := ord_part k m); simpl in HT.
    apply <- HT; clear HT; split; assumption.
  Qed.

  Definition iseq (k1 k2 : T) : bool := match comp k1 k2 with Eq => true | _ => false end.
  Lemma iseq_eq k1 k2 : iseq k1 k2 = true <-> k1 = k2.
  Proof.
    unfold iseq; assert (HT := compat_compare k1 k2); destruct (comp k1 k2); intuition discriminate.
  Qed.

  Fixpoint inlst k xs :=
    match xs with
      | nil => false
      | x :: xs => (iseq k x || inlst k xs)%bool
    end.

  Lemma In_inlst k xs : inlst k xs = true <-> k ∈ xs.
  Proof.
    induction xs; simpl; [intuition discriminate |].
    rewrite Bool.orb_true_iff, IHxs; clear IHxs; intuition.
    - rewrite iseq_eq in H0; subst; tauto.
    - subst; unfold iseq; rewrite comp_self_Eq; auto.
  Qed.

  Lemma eq_sym_iff : forall T (x y : T), x = y <-> y = x.
  Proof.
    split; apply eq_sym; assumption.
  Qed.

  Lemma NIn_inlst k xs : inlst k xs = false <-> ~ (k ∈ xs).
    induction xs; simpl; [tauto |].
    rewrite Bool.orb_false_iff, IHxs, (eq_sym_iff _ a), <- iseq_eq; clear IHxs.
    destruct (iseq k a); intuition congruence.
  Qed.

  Inductive StrictSorted : list T -> Prop :=
  | SS_nil : StrictSorted nil
  | SS_sing : forall x, StrictSorted (x :: nil)
  | SS_cons : forall x x' xs (HS : StrictSorted (x' :: xs)) (HLt : comp x x' = Lt),
    StrictSorted (x :: x' :: xs).

  Lemma SS_tail x xs (HSS : StrictSorted (x :: xs)) : StrictSorted xs.
  Proof.
    inversion HSS; subst; assumption || apply SS_nil.
  Qed.

  Lemma comp_Lt_lt: forall m k, comp k m = Lt -> leq k m /\ k <> m. 
  Proof.
    intros m k H; assert (HT := compat_compare k m); rewrite H in HT; assumption.
  Qed.

  Lemma comp_Gt_gt: forall m k, comp k m = Gt -> leq m k /\ k <> m. 
  Proof.
    intros m k H; assert (HT := compat_compare k m); rewrite H in HT; assumption.
  Qed.

  Lemma Lt_trans: forall x y z, comp x y = Lt -> comp y z = Lt -> comp x z = Lt.
  Proof.
    intros; apply comp_lt_Lt; apply comp_Lt_lt in H; apply comp_Lt_lt in H0.
    split; [etransitivity; intuition eassumption |].
    intros abs; subst; contradiction (proj2 H); apply ord_part; split; tauto.
  Qed.
  
  Lemma Gt_trans: forall x y z, comp x y = Gt -> comp y z = Gt -> comp x z = Gt.
  Proof.
    intros; apply comp_gt_Gt; apply comp_Gt_gt in H; apply comp_Gt_gt in H0.
    split; [etransitivity; intuition eassumption |].
    intros abs; subst; contradiction (proj2 H); apply ord_part; split; tauto.
  Qed.

  Lemma StrictSorted_lt_notin k x xs (HLt : leq k x /\ k <> x)
        (HSS : StrictSorted (x :: xs)) : ~ (k ∈ (x :: xs)).
  Proof.
    induction xs; [simpl; intros [HEq | HC]; [subst |]; tauto |].
    inversion HSS; subst; simpl; intros HIn; apply IHxs; clear HSS IHxs; [| simpl; intuition].
    - clear HIn; inversion HS; subst; [apply SS_sing | apply SS_cons; [assumption |]].
      apply comp_lt_Lt; apply comp_Lt_lt in HLt0; apply comp_Lt_lt in HLt1. 
      split; [etransitivity; intuition eassumption |].
      intros HEq; subst; contradiction (proj2 HLt1); apply ord_part; split; tauto.
    - subst; apply comp_Lt_lt in HLt0; destruct HLt0; contradiction H0; apply ord_part; split; assumption.
  Qed.

  Lemma StrictSorted_lt_notin' k x xs (HLt : comp k x = Lt)
        (HSS : StrictSorted (x :: xs)) : ~ (k ∈ (x :: xs)).
  Proof.
    apply comp_Lt_lt in HLt; apply StrictSorted_lt_notin; assumption.
  Qed.
  
  Lemma StrictSorted_notin x xs (HSS : StrictSorted (x :: xs)) : ~ (x ∈ xs).
  Proof.
    destruct xs as [| y ys]; [tauto |]; apply StrictSorted_lt_notin'; [| eapply SS_tail; eassumption].
    inversion HSS; subst; assumption.
  Qed.

  Lemma last_cons (x y : T) xs : last (x :: xs) y = last xs x.
  Proof.
    revert x y; induction xs; intros; [reflexivity |].
    etransitivity; [apply IHxs |]; symmetry; apply IHxs.
  Qed.

  Lemma SS_last_le y x xs (HSS : StrictSorted (x :: xs)) (HIn : y ∈ (x :: xs)) :
    leq y (last xs x).
  Proof.
    revert x y HSS HIn; induction xs; intros.
    - destruct HIn; [subst; reflexivity | contradiction].
    - rewrite last_cons; inversion_clear HSS; apply comp_Lt_lt in HLt.
      simpl in HIn; destruct HIn as [HEq | HIn]; [subst |].
      + transitivity a; [tauto |].
        apply IHxs; [assumption | simpl; tauto].
      + apply IHxs; assumption.
  Qed.

End Sortedness.

Section Def.
  Context (K V : Type).

  Record FinDom `{compK : comparable K} :=
    mkFD {findom_t : list (K * V);
          findom_P : StrictSorted (map (@fst _ _) findom_t)}.

  Context `{compK : comparable K}.

  Fixpoint findom_lu f x : option V :=
    match f with
      | nil => None
      | (k, v) :: f =>
        match comp x k with
          | Lt => None
          | Eq => Some v
          | Gt => findom_lu f x
        end
    end.

  Definition findom_f f := findom_lu (findom_t f).
  Definition dom f := map (@fst _ _) (findom_t f).
  Definition codom f := map (@snd _ _) (findom_t f).
End Def.

Arguments mkFD [K V] {cT ord equ preo ord_part compK} _ _.
Arguments findom_t [K V] {cT ord equ preo ord_part compK} _.
Arguments findom_lu [K V] {cT} _ _.
Arguments dom [K V] {cT ord equ preo ord_part compK} f.
Arguments codom [K V] {cT ord equ preo ord_part compK} f.
Arguments findom_f [K V] {cT ord equ preo ord_part compK} f x.
Notation "K '-f>' V" := (FinDom K V) (at level 45).

Section FinDom.
  Context {K} `{compK : comparable K}.

  Coercion findom_f : FinDom >-> Funclass.

  Section Props.
    Context {V : Type} `{ev : Setoid V}.

    Program Definition fdEmpty : K -f> V := mkFD nil SS_nil.

    Lemma fdLookup_notin_strong k (f : K -f> V) : (~ (k ∈ dom f)) <-> f k = None.
    Proof.
      destruct f as [fs fP]; unfold findom_f, dom in *; simpl in *; induction fs; [firstorder |].
      destruct a as [m v]; assert (HT := compat_compare k m); simpl in *; destruct (comp k m); subst.
      - split; [intros HNIn; contradiction HNIn; tauto | inversion 1].
      - split; [reflexivity | intros _]; apply (StrictSorted_lt_notin _ _ _ HT fP).
      - apply SS_tail in fP; rewrite <- IHfs; [| assumption]; intuition.
    Qed.

    Lemma option_dec {A} (v : option A): {v = None} + {exists a, v = Some a}.
      destruct v ; eauto.
    Qed.
      
    Lemma option_None_eq (v : option V) : v == None -> v = None.
    Proof.
      assert (d := option_dec v) ; destruct d as [l | r]; [auto | destruct r as [x Hx] ; rewrite Hx ; inversion 1].
    Qed.

    Lemma fdLookup_notin k (f : K -f> V) : (~ (k ∈ dom f)) <-> f k == None.
    Proof.
      split ; intro H.
      + apply fdLookup_notin_strong in H ; rewrite H ; reflexivity.
      + apply option_None_eq in H ; apply fdLookup_notin_strong ; auto.
    Qed.
    
    Lemma fdLookup_in_strong : forall (f : K -f> V) k, k ∈ dom f <-> exists v, f k = Some v.
    Proof.
      destruct f as [fs fP]; unfold findom_f, dom; simpl; induction fs; intros; simpl.
      - intuition; destruct H as [x Hx]; inversion Hx.
      - destruct a as [kf vf]; assert (HT := compat_compare k kf); unfold findom_f in *; simpl in *; split; intros.
        + destruct (comp k kf); [exists vf ; reflexivity |..].
          * destruct H; [subst; firstorder |]; contradiction (StrictSorted_lt_notin _ _ _ HT fP); simpl; tauto.
          * apply -> IHfs; [| eapply SS_tail; eassumption]; destruct H; [subst; tauto | assumption].
        + destruct H as [v HEqv]; destruct (comp k kf); [subst; tauto | inversion HEqv |].
          right; apply <- IHfs; eauto using @SS_tail.
    Qed.    

    Lemma fdLookup_in : forall (f : K -f> V) k, k ∈ dom f <-> exists v, f k == Some v.
    Proof.
      destruct f as [fs fP]; unfold findom_f, dom; simpl map; simpl findom_t.
      induction fs; intros.
      - intuition; destruct H as [x Hx]; inversion Hx.
      - destruct a as [kf vf]; assert (HT := compat_compare k kf); unfold findom_f in *; simpl findom_lu in *; split; intros.
        + destruct (comp k kf); [exists vf ; reflexivity |..].
          * destruct H; [subst; firstorder |]; contradiction (StrictSorted_lt_notin _ _ _ HT fP); simpl; tauto.
          * apply -> IHfs; [| eapply SS_tail; eassumption]; destruct H; [subst; tauto | assumption].
        + destruct H as [v HEqv]; destruct (comp k kf); [simpl; subst; tauto | inversion HEqv |].
          right; apply <- IHfs; eauto using @SS_tail.
    Qed.    

    Fixpoint pre_upd (x : K * V) ys :=
      match ys with
        | nil => x :: nil
        | y :: ys' => match comp (fst x) (fst y) with
                        | Lt => x :: ys
                        | Eq => x :: ys'
                        | Gt => y :: pre_upd x ys'
                      end
      end.

    Program Definition fdUpdate k v (f : K -f> V) : K -f> V := mkFD (pre_upd (k, v) (findom_t f)) _.
    Next Obligation.
      destruct f as [fs fSS]; induction fs; simpl in *; [apply SS_sing |].
      destruct a as [kf vf]; simpl in *; assert (HT := compat_compare k kf); destruct (comp k kf);
        subst; simpl; [assumption | apply SS_cons; [assumption|apply comp_lt_Lt; assumption] |]. 
      assert (HR : match map (@fst _ _) (pre_upd (k, v) fs)
                     with nil => True | kn :: _ => leq kf kn /\ kf <> kn end).
      - assert (HNEq' : kf <> k) by (intros HEq; subst; tauto).
        destruct fs as [| [kn vn] fs']; inversion fSS; clear fSS IHfs; subst; simpl; [tauto |].
        destruct (comp k kn); simpl; apply comp_Lt_lt in HLt; tauto.
      - destruct (pre_upd (k, v) fs) as [| [kn vn] fs']; [apply SS_sing |]; simpl in *.
        apply comp_lt_Lt in HR; apply SS_cons; eauto using @SS_tail.
    Qed.
      
    Lemma fdUpdate_eq k v f : fdUpdate k v f k = Some v.
    Proof.
      destruct f as [fs fP]; unfold findom_f; simpl in *; clear fP;
        induction fs; simpl; [rewrite comp_self_Eq; reflexivity |].
      destruct a as [kf vf]; assert (HT := compat_compare k kf); simpl; destruct (comp k kf); simpl;
        try (rewrite comp_self_Eq; reflexivity).
      rewrite comp_gt_Gt; assumption.
    Qed.

    Lemma fdUpdate_neq k k' v f (Hneq : k <> k') : fdUpdate k v f k' = f k'.
    Proof.
      destruct f as [fs fP]; unfold findom_f; simpl in *; clear fP; induction fs; simpl.
        assert (HT := compat_compare k' k); destruct (comp k' k); subst; tauto.
      destruct a as [kf vf]; assert (HT := compat_compare k kf); simpl; destruct (comp k kf); simpl;
        [..| rewrite IHfs; reflexivity].
        subst; assert (HT := compat_compare k' kf); destruct (comp k' kf); subst; tauto.
      assert (HR := compat_compare k' k); destruct (comp k' k); subst; try tauto.
      assert (HQ := compat_compare k' kf); destruct (comp k' kf); try reflexivity; clear IHfs.
        subst; contradiction Hneq; apply ord_part; split; tauto.
      contradiction Hneq; apply ord_part; split; [etransitivity |]; intuition eassumption.
    Qed.

    Fixpoint pre_rem x (ys : list (K * V)) :=
      match ys with
        | nil => nil
        | y :: ys' => match comp x (fst y) with
                        | Eq => ys'
                        | Lt => ys
                        | Gt => y :: pre_rem x ys'
                      end
      end.

    Program Definition fdRemove k (f : K -f> V) : K -f> V := mkFD (pre_rem k (findom_t f)) _.
    Next Obligation.
      destruct f as [fs fP]; simpl; induction fs; simpl; [assumption |].
      destruct a as [kf vf]; assert (HT := compat_compare k kf); simpl; destruct (comp k kf); eauto using @SS_tail.
      specialize (IHfs (SS_tail _ _ fP)); simpl; clear HT.
      assert (HR : match map (@fst _ _) (pre_rem k fs)
                     with nil => True | kn :: _ => leq kf kn /\ kf <> kn end).
      - destruct fs as [| [kn vn] fs']; simpl in *; [trivial |].
        destruct (comp k kn); simpl; inversion fP; subst; apply comp_Lt_lt in HLt; try tauto.
        clear fP; destruct fs' as [| [km vm] fs']; simpl in *; [trivial |].
        inversion HS; subst; split; apply comp_Lt_lt in HLt0; [etransitivity; intuition eassumption | intros HEq; subst].
        contradiction (proj2 HLt); apply ord_part; split; tauto.
      - destruct (map (@fst _ _) (pre_rem k fs)) as [| kn fs']; [apply SS_sing | apply comp_lt_Lt in HR; apply SS_cons; assumption].
    Qed.

    Lemma fdRemove_eq t f : fdRemove t f t = None.
    Proof.
      destruct f as [fs fP]; simpl; induction fs; [reflexivity |].
      destruct a as [k v]; assert (HT := compat_compare t k); simpl in *; destruct (comp t k).
      - apply fdLookup_notin_strong, StrictSorted_notin; subst; unfold dom; simpl; rewrite comp_self_Eq; apply fP.
      - apply fdLookup_notin_strong; unfold findom_f, dom in *; simpl in *; rewrite comp_lt_Lt; [| assumption].
        apply StrictSorted_lt_notin; assumption.
      - unfold findom_f in *; simpl in *; rewrite comp_gt_Gt; [| assumption].
        simpl; rewrite comp_gt_Gt; [| assumption].
        eapply IHfs, SS_tail; eassumption.
    Qed.

    Lemma fdRemove_neq {t t'} f (Hneq : t <> t') : fdRemove t f t' = f t'.
    Proof.
      destruct f as [fs fP]; unfold findom_f; simpl; induction fs; [reflexivity |].
      destruct a as [k v]; assert (HT := compat_compare t k); simpl; destruct (comp t k); [| reflexivity |].
      - subst; assert (HQ := compat_compare t' k); destruct (comp t' k); subst; try tauto.
        apply (fdLookup_notin_strong _ (mkFD fs (SS_tail _ _ fP))); unfold dom; simpl in *.
        intros HT; eapply StrictSorted_lt_notin; eassumption || (simpl; tauto).
      - simpl; rewrite IHfs; [reflexivity |]; eapply SS_tail; eassumption.
    Qed.

    Program Fixpoint Indom_lookup k (f : list (K * V)) (HIn : inlst k (map (@fst _ _) f) = true) : V :=
      match f as f' return inlst k (map (@fst _ _) f') = true -> V with
        | nil => fun F => False_rect _ _
        | (k', v') :: fr => fun P =>
          match iseq k k' as b return (b || inlst k (map (@fst _ _) fr) = true)%bool -> V with
            | true => fun _ => v'
            | false => fun P => Indom_lookup k fr P
          end P
      end HIn.

    Lemma Indom_lookup_find k (f : K -f> V) (HIn : inlst k (dom f) = true) : Some (Indom_lookup _ _ HIn) = f k.
    Proof.
      destruct f as [fs fP]; unfold dom, findom_f in *; simpl in *; induction fs; [discriminate |].
      revert HIn; destruct a as [kf vf]; simpl in *; unfold iseq.
      assert (HT := compat_compare k kf); revert HT; destruct (comp k kf); intros; [subst; reflexivity |..].
      - contradict HIn; simpl; rewrite In_inlst.
        intros HIn; eapply StrictSorted_lt_notin; eassumption || (simpl; tauto).
      - eapply IHfs, SS_tail; eassumption.
    Qed.

    Lemma orb_right_intro a b (HT : b = true) : (a || b = true)%bool.
    Proof. subst b; apply Bool.orb_true_r. Qed.

    Fixpoint ind_app_map U (xs : list K)
      (I : forall x (HIn : inlst x xs = true), U) :=
      match xs as lst return (forall x (HIn : inlst x lst = true), U) -> list (K * U) with
        | nil => fun _ => nil
        | x :: xs => fun R => (x, R x (proj2 (In_inlst _ _) (in_eq x xs))) ::
                               ind_app_map U xs (fun y Y => R _ (orb_right_intro _ _ Y))
      end I.

    Lemma list_fst_map U xs I : map (@fst _ _) (ind_app_map U xs I) = xs.
    Proof. induction xs; [reflexivity |]; simpl; f_equal; apply IHxs. Qed.

    Program Definition findom_map U W (m : K -f> U) (f : forall x (HIn : inlst x (dom m) = true), W) : K -f> W :=
      mkFD (ind_app_map _ (dom m) f) _.
    Next Obligation.
      rewrite list_fst_map; apply m.
    Qed.

    Lemma ff (P : K -> nat -> Prop) (A : forall x n m, n <= m -> P x n -> P x m) (xs : list K) :
      (forall x, inlst x xs = true -> exists m, P x m) -> exists m, forall x, inlst x xs = true -> P x m.
    Proof.
      induction xs; intros; [exists 0; intros; discriminate |].
      specialize (IHxs (fun k HIn => H k (orb_right_intro _ _ HIn))); destruct IHxs as [m IH].
      specialize (H a (proj2 (In_inlst (compT := compK) _ _) (in_eq a xs))); destruct H as [k Hk].
      exists (max m k); intros t HIn; rewrite In_inlst in HIn; simpl in HIn; destruct HIn as [HEq | HIn];
        [subst | rewrite <- In_inlst in HIn]; eapply A; [| eassumption |..]; eauto using le_max_r, le_max_l.
    Qed.

    Lemma findom_fun_map U xs (I : forall x, inlst x xs = true -> U) x
      (HIn : inlst x xs = true) (HSS : StrictSorted xs) :
      findom_lu (ind_app_map _ xs I) x = Some (I _ HIn).
    Proof.
      induction xs; [discriminate |].
      simpl; assert (HT := compat_compare x a); destruct (comp x a).
      - subst; rewrite (D.UIP _ _ _ HIn); reflexivity.
      - contradiction (StrictSorted_lt_notin _ _ xs HT).
        rewrite <- In_inlst; assumption.
      - simpl in *; specialize (IHxs (fun y Y => I _ (orb_right_intro _ _ Y))).
        assert (HInT : inlst x xs = true) by (unfold iseq in HIn; rewrite comp_gt_Gt in HIn; assumption).
        specialize (IHxs HInT (SS_tail _ _ HSS)); simpl in IHxs; rewrite (D.UIP _ _ _ HIn) in IHxs; apply IHxs.
    Qed.

    Lemma findom_map_app U W (m : K -f> U) x (HIn : inlst x (dom m) = true)
      (f : forall x, (inlst x (dom m) = true) -> W) :
      findom_map _ _ m f x = Some (f x HIn).
    Proof.
      destruct m as [ms mP]; unfold findom_f; simpl; unfold dom in *; simpl in *.
      apply (findom_fun_map _ _ f); assumption.
    Qed.

    Lemma findom_fun_map_nf U xs (I : forall x, inlst x xs = true -> U) x
      (HNIn : inlst x xs = false) (HSS : StrictSorted xs) :
      findom_lu (ind_app_map _ xs I) x = None.
    Proof.
      induction xs; [reflexivity |].
      simpl; assert (HT := compat_compare x a); destruct (comp x a); [| reflexivity |].
      - simpl in HNIn; rewrite <- iseq_eq in HT; rewrite HT in HNIn; discriminate.
      - simpl in *; apply IHxs; [| eapply SS_tail; eassumption].
        destruct (iseq x a); [discriminate | apply HNIn].
    Qed.

    Lemma findom_map_app_nf U W (m : K -f> U) x (HNIn : inlst x (dom m) = false)
      (f : forall x, (inlst x (dom m) = true) -> W) :
      findom_map _ _ m f x = None.
    Proof.
      destruct m as [ms mP]; unfold findom_f; simpl; unfold dom in *; simpl in *.
      apply (findom_fun_map_nf _ _ f); assumption.
    Qed.

  End Props.

  Section Instances.
    Context {V} `{cV : pcmType V}.

    Definition equiv_fd (f1 f2 : K -f> V) := forall k, f1 k == f2 k.

    Global Instance equiv_fd_e: Equivalence equiv_fd.
    Proof.
      split.
      - intros m k; reflexivity.
      - intros m1 m2 HS k; symmetry; apply HS.
      - intros m1 m2 m3 H12 H23 k; etransitivity; [apply H12 | apply H23].
    Qed.
    
    Global Program Instance type_findom : Setoid (K -f> V) | 5:= mkType equiv_fd.

    Global Instance lookup_proper : Proper (equiv ==> eq ==> equiv) (findom_f (V := V)).
    Proof.
      intros f1 f2 HEqf k1 k2 HEqk; subst; apply HEqf.
    Qed.

    Definition dist_fd n (f1 f2 : K -f> V) :=
      match n with
        | O => True
        | S _ => forall k, f1 k = n = f2 k
      end.

    Global Program Instance metric_findom : metric (K -f> V) | 5 := mkMetr dist_fd.
    Next Obligation.
      revert n; intros [| n] f1 f2 EQf g1 g2 EQg; [reflexivity |]; split;
      intros EQ k; [symmetry in EQf, EQg |]; rewrite EQf, EQg; apply EQ.
    Qed.
    Next Obligation.
      split; intros HEq.
      - intros k; rewrite <- dist_refl; intros [| n]; [reflexivity; exact None | apply (HEq (S n) k) ].
      - intros [| n]; [reflexivity |]; intros k; generalize (S n); rewrite dist_refl; apply HEq.
    Qed.
    Next Obligation.
      revert n; intros [| n] x y HS; [reflexivity |]; intros k; symmetry; apply HS.
    Qed.
    Next Obligation.
      revert n; intros [| n] x y z Hxy Hyz; [reflexivity |]; intros k; etransitivity; [apply Hxy | apply Hyz].
    Qed.
    Next Obligation.
      destruct n as [| n]; [reflexivity |]; intros k; eapply dist_mono, H.
    Qed.

    Lemma domeq {m1 m2 : K -f> V} {n} (HEq : m1 = S n = m2) : dom m1 = dom m2.
    Proof.
      destruct m1 as [ms1 mP1]; destruct m2 as [ms2 mP2]; revert ms2 mP2 HEq; induction ms1; intros.
      { destruct ms2 as [| [kf vf] ms2]; [reflexivity |]; specialize (HEq kf); unfold findom_f in *; simpl in *.
        rewrite comp_self_Eq in HEq; contradiction HEq.
      }
      destruct a as [k1 v1]; destruct ms2 as [| [k2 v2] ms2].
      { specialize (HEq k1); unfold findom_f in *; simpl in *; rewrite comp_self_Eq in HEq; contradiction HEq.
      }
      assert (HEqk : k1 = k2).
      { assert (HT := compat_compare k1 k2); assert (HLt := HEq k1); assert (HGt := HEq k2);
          unfold findom_f in *; simpl in *; clear IHms1 HEq.
        rewrite comp_self_Eq in HLt; destruct (comp k1 k2); [assumption | contradiction HLt |].
        rewrite comp_lt_Lt, comp_self_Eq in HGt; [contradiction HGt | intuition].
      }
      subst; unfold dom; simpl; f_equal; simpl in *.
      apply IHms1 with (mP1 := SS_tail _ _ mP1) (mP2 := SS_tail _ _ mP2); intros k; clear IHms1.
      specialize (HEq k); unfold findom_f in *; simpl in *.
      assert (HT : mkFD ms1 (SS_tail _ _ mP1) k = S n = mkFD ms2 (SS_tail _ _ mP2) k); [| apply HT].
      assert (HT := compat_compare k k2); destruct (comp k k2); [subst | | assumption].
      { rewrite !(proj1 (fdLookup_notin_strong _ _)); [reflexivity |..]; unfold dom; simpl; apply StrictSorted_notin; assumption.
      }
      rewrite !(proj1 (fdLookup_notin_strong _ _)); [reflexivity |..]; unfold dom; simpl; intros HIn.
      { apply (StrictSorted_lt_notin _ _ _ HT mP2); simpl; tauto.
      }
      apply (StrictSorted_lt_notin _ _ _ HT mP1); simpl; tauto.
    Qed.

    Lemma finmap_chain_dom x n (σ : chain (K -f> V)) {σc : cchain σ} (HIn : In x (dom (σ 1))) : In x (dom (σ (S n))).
    Proof.
      revert σ σc HIn; induction n; intros; [assumption |].
      apply (IHn (cutn σ 1)); simpl; clear IHn; [apply _ |].
      rewrite fdLookup_in in HIn; destruct HIn as [v HLU].
      remember ((σ 2) x) as ov; symmetry in Heqov; destruct ov.
      - rewrite fdLookup_in; eexists; setoid_rewrite Heqov; reflexivity.
      - assert (HT := chain_cauchy σ _ 1 1 2 x).
        rewrite Heqov, HLU in HT; contradiction HT.
    Qed.

    Definition finmap_chainx (σ : chain (K -f> V)) {σc : cchain σ} x (HIn : x ∈ dom (σ 1)) :=
      fun n => Indom_lookup x (findom_t (σ (S n))) (proj2 (In_inlst _ _) (finmap_chain_dom _ _ _ HIn)).

    Program Instance finmap_chainx_cauchy (σ : chain (K -f> V)) {σc : cchain σ} x (HIn : x ∈ dom (σ 1)) :
      cchain (finmap_chainx σ x HIn) | 5.
    Next Obligation.
      unfold cchain; intros.
      assert (HT : Some (finmap_chainx σ x HIn i) = S n = Some (finmap_chainx σ x HIn j)); [| apply dist_mono, HT].
      unfold finmap_chainx; rewrite !Indom_lookup_find; apply (chain_cauchy σ σc (S n)); auto with arith.
    Qed.

    Definition findom_lub (σ : chain (K -f> V)) (σc : cchain σ) : K -f> V :=
      findom_map _ _ (σ 1) (fun x HLu => compl (finmap_chainx σ x (proj1 (In_inlst _ _) HLu))).

    Global Program Instance findom_cmetric : cmetric (K -f> V) | 5 := mkCMetr findom_lub.
    Next Obligation.
      intros [| n]; [exists 0; intros; exact I |].
      assert (HT : exists m, forall x, inlst x (dom (σ 1)) = true -> forall (X : inlst x (dom (σ 1)) = true) i,
        m < i -> σ i x = S n = Some (compl (finmap_chainx _ _ (proj1 (In_inlst _ _) X)))).
      { apply ff; intros; [apply H0; omega |].
        destruct (conv_cauchy (finmap_chainx _ _ (proj1 (In_inlst _ _) H)) (S n)) as [m P]; exists m;
          intros HIn [| i] HLe; [inversion HLe |].
        apply lt_n_Sm_le in HLe; specialize (P _ HLe); unfold finmap_chainx at 2 in P; simpl in P.
        erewrite <- Indom_lookup_find; unfold dist; simpl; rewrite <- P; apply umet_complete_extn; intros k; clear P; simpl.
        change (Some (finmap_chainx σ x (proj1 (In_inlst _ _) H) k) = S n = Some (finmap_chainx σ x (proj1 (In_inlst _ _) HIn) k)).
        unfold finmap_chainx; rewrite !Indom_lookup_find; reflexivity.
      }
      destruct HT as [m HT]; exists (S m); intros [| i] HLe k; [inversion HLe |].
      destruct (inlst k (dom (σ 1))) eqn: HIn.
      - specialize (HT _ HIn HIn (S i)); rewrite HT; [| auto with arith].
        unfold findom_lub; rewrite findom_map_app with (HIn := HIn); reflexivity.
      - assert (HInS := HIn); rewrite @domeq with (n := 0) (m2 := σ (S i)) in HInS;
        [| eapply chain_cauchy; auto with arith].
        rewrite !(proj1 (fdLookup_notin _ _)); [reflexivity | rewrite <- In_inlst; congruence |].
        unfold findom_lub, dom; simpl; rewrite list_fst_map, <- In_inlst; congruence.
    Qed.

    Local Existing Instance option_preo_bot.
    Local Existing Instance option_pcm_bot.

    Definition extOrd (m1 m2 : K -f> V) := forall k, m1 k ⊑ m2 k.

    Global Program Instance extOrd_preo : preoType (K -f> V) := mkPOType extOrd.
    Next Obligation.
      split.
      - intros m k; reflexivity.
      - intros m1 m2 m3 S12 S23 k; etransitivity; [apply (S12 k) | apply (S23 k) ].
    Qed.

    Definition chain_fin_app (σ : chain (K -f> V)) k : chain (option V) :=
      fun i => σ i k.
    Instance cchain_fin_app (σ : chain (K -f> V)) {σc : cchain σ} k : cchain (chain_fin_app σ k).
    Proof.
      intros n i j LEi LEj; unfold chain_fin_app.
      specialize (σc n i j LEi LEj).
      destruct n as [| n]; [apply dist_bound |].
      specialize (σc k); assumption.
    Qed.

    Lemma foo (σ : chain (K -f> V)) (σc : cchain σ) k :
      compl σ k == compl (chain_fin_app σ k).
    Proof.
      unfold compl, option_cmt, option_compl, chain_fin_app; simpl.
      generalize (@eq_refl _ (σ 1 k)) as EQs; pattern (σ 1 k) at 1 3; destruct (σ 1 k) as [vs |]; intros.
      - unfold findom_lub.
        assert (HIn : inlst k (dom (σ 1)) = true).
        { rewrite In_inlst, fdLookup_in_strong; exists vs; congruence. }
        rewrite findom_map_app with (HIn := HIn).
        unfold equiv; simpl; apply umet_complete_ext; intros.
        unfold unSome, finmap_chainx.
        generalize (@eq_refl _ (σ (S i) k)) as EQsi.
        pattern (σ (S i) k) at 1 3; destruct (σ (S i) k) as [vsi |]; intros; [| exfalso].
        + erewrite <- (Indom_lookup_find _ (σ (S i))) in EQsi.
          inversion EQsi; reflexivity.
        + assert (LEi : 1 <= S i) by auto with arith.
          specialize (σc 1 1 (S i) (le_n _) LEi k).
          rewrite <- EQs, <- EQsi in σc; contradiction σc.
      - unfold findom_lub.
        rewrite findom_map_app_nf; [reflexivity |].
        rewrite NIn_inlst, fdLookup_notin_strong; congruence.
    Qed.

    Global Instance findom_pcmType : pcmType (K -f> V).
    Proof.
      split.
      - intros s s' HEqs t t' HEqt; split; intros HSub k.
        + rewrite <- (HEqs k), <- (HEqt k); apply (HSub k).
        + rewrite (HEqs k), (HEqt k); apply (HSub k).
      - intros σ ρ σc ρc HSub k; rewrite !foo.
        eapply pcm_respC; [now auto with typeclass_instances | intros].
        unfold chain_fin_app; eapply HSub.
    Qed.

    Lemma dom_ext (m1 m2 : K -f> V) k (HSub : m1 ⊑ m2) (HIn : k ∈ dom m1) : k ∈ dom m2.
    Proof.
      destruct m1 as [ms1 mP1]; destruct m2 as [ms2 mP2]; specialize (HSub k); simpl in *.
      unfold findom_f, dom in *; simpl in *.
      induction ms1; simpl in *; [contradiction | destruct a as [k0 v0]; simpl in * ].
      assert (HT := compat_compare k k0); destruct (comp k k0); [subst k0 | |].
      - destruct (findom_lu ms2 k) as [v1 |] eqn: HFnd; [| contradiction HSub].
        clear -HFnd mP2 compK.
        assert (HT := fdLookup_in_strong (mkFD ms2 mP2) k); unfold dom, findom_f in HT; simpl in HT.
        rewrite HT; exists v1; assumption.
      - assert (HNIn := (StrictSorted_lt_notin _ _ _ HT mP1) HIn); contradiction.
      - destruct HIn as [HEq | HIn]; [destruct HT; congruence | apply SS_tail in mP1].
        apply IHms1; assumption.
    Qed.

  End Instances.

  Section Map.
    Context U V `{pcmU : pcmType U} `{cmV : pcmType V}.

    Program Definition pre_fdMap (f : U -> V) (m : K -f> U) : (K -f> V) :=
      mkFD (map (fun (a : K * U) => let (k, v) := a in (k, f v)) (findom_t m)) _.
    Next Obligation.
      destruct m as [ms mP]; simpl; induction ms as [| [k u]]; [apply SS_nil | simpl in *].
      destruct ms as [| [k' u'] ms]; [apply SS_sing | simpl in *].
      inversion mP; subst; apply SS_tail in mP; apply SS_cons; [apply IHms |]; assumption.
    Qed.

    Lemma pre_fdMap_dom_same f m : dom m = dom (pre_fdMap f m).
    Proof.
      destruct m as [ms mP]; unfold dom; simpl; clear mP; induction ms as [| [k u]]; [reflexivity |].
      simpl; f_equal; apply IHms.
    Qed.

    Lemma pre_fdMap_lookup f (m : K -f> U) k u (HFnd : m k = Some u) : (pre_fdMap f m) k = Some (f u).
    Proof.
      destruct m as [ms mP]; unfold findom_f in *; simpl in *; clear mP.
      induction ms as [| [k' u']]; [discriminate | simpl in *].
      assert (HT := compat_compare k k'); destruct (comp k k'); [subst k' | discriminate |].
      - inversion HFnd; subst u'; reflexivity.
      - apply IHms; assumption.
    Qed.

    Lemma pre_fdMap_lookup_nf f (m : K -f> U) k (HFnd : m k = None) : (pre_fdMap f m) k = None.
    Proof.
      apply fdLookup_notin_strong; rewrite <- pre_fdMap_dom_same; apply fdLookup_notin_strong; assumption.
    Qed.

    Program Definition fdMap (f : U -m> V) : (K -f> U) -m> (K -f> V) :=
      m[(pre_fdMap f)].
    Next Obligation.
      intros m1 m2 HEq; destruct n as [| n]; [apply dist_bound |]; intros k; simpl; specialize (HEq k).
      destruct (m1 k) as [u1 |] eqn: HFnd1; destruct (m2 k) as [u2 |] eqn: HFnd2; try contradiction HEq; [|].
      - rewrite pre_fdMap_lookup with (u := u1), pre_fdMap_lookup with (u := u2);
        [apply met_morph_nonexp |..]; assumption.
      - rewrite !pre_fdMap_lookup_nf; assumption.
    Qed.
    Next Obligation.
      intros m1 m2 Subm k; specialize (Subm k); destruct (m1 k) as [u1 |] eqn: HFnd1.
      - erewrite pre_fdMap_lookup by eassumption.
        destruct (m2 k) as [u2 |] eqn: HFnd2; [| contradiction Subm].
        erewrite pre_fdMap_lookup by eassumption.
        unfold pord in *; simpl in *.
        rewrite Subm; reflexivity.
      - rewrite pre_fdMap_lookup_nf by assumption; exact I.
    Qed.

    Global Instance fdMap_resp : Proper (equiv ==> equiv) fdMap.
    Proof.
      intros f1 f2 EQf m k; destruct (m k) as [u |] eqn: HFnd; simpl morph.
      - rewrite !pre_fdMap_lookup with (u := u) by assumption.
        rewrite EQf; apply morph_resp; reflexivity.
      - rewrite !pre_fdMap_lookup_nf by assumption; reflexivity.
    Qed.

    Global Instance fdMap_nonexp n : Proper (dist n ==> dist n) fdMap.
    Proof.
      intros f1 f2 EQf m; destruct n as [| n]; [apply dist_bound |]; intros k.
      simpl morph; destruct (m k) as [u |] eqn: HFnd.
      - rewrite !pre_fdMap_lookup with (u := u) by assumption.
        unfold dist; simpl; rewrite EQf; apply met_morph_nonexp; reflexivity.
      - rewrite !pre_fdMap_lookup_nf by assumption; reflexivity.
    Qed.

    Global Instance fdMap_monic : Proper (pord ==> pord) fdMap.
    Proof.
      intros f1 f2 Subf m k; simpl morph.
      destruct (m k) as [u |] eqn: HFnd.
      - erewrite !pre_fdMap_lookup by eassumption.
        unfold pord; simpl; apply (Subf u).
      - rewrite !pre_fdMap_lookup_nf by assumption.
        reflexivity.
    Qed.

    Notation "fd [ x -> v ]" := (fdUpdate x v fd) (at level 50, x at next level).
    Notation "fd \ x" := (fdRemove x fd) (at level 50).
    
    Lemma eq_SS : forall ks (fP fP' : StrictSorted ks), fP = fP'.
    Proof.
      clear -compK; induction ks; intros.
      + refine (match fP as fP in StrictSorted xs return
                      match xs return StrictSorted xs -> Prop with
                        | nil => fun fP => fP = fP'
                        | _ => fun _ => True
                      end fP with
                  | SS_nil => match fP' as gP in StrictSorted xs return
                                   match xs return StrictSorted xs -> Prop with
                                     | nil => fun gP => SS_nil = gP
                                     | _ => fun _ => True
                                   end gP with
                               | SS_nil => eq_refl
                               | _ => I
                             end
                  | _ => I
                end).
      + refine (match fP as fP in StrictSorted xs return
                      match xs return StrictSorted xs -> Prop with
                        | nil => fun _ => True
                        | k :: ks => fun fP =>
                                      forall fP' (IHks : forall fP fP' : StrictSorted ks, fP = fP'), fP = fP'
                      end fP with
                  | SS_nil => I
                  | SS_sing x => _
                  | SS_cons x x' xs HSS HLt => _
                end fP' IHks); clear -compK; intros.
        * refine (match fP' as fP in StrictSorted xs return
                        match xs return StrictSorted xs -> Prop with
                          | k :: nil => fun fP => SS_sing k = fP
                          | _ => fun _ => True
                        end fP with
                    | SS_sing x => eq_refl
                    | _ => I
                  end).
        * refine (match fP' as fP in StrictSorted xs return
                        match xs return StrictSorted xs -> Prop with
                          | x :: x' :: xs => fun fP => forall HSS HLt (IHks : forall fP fP' : StrictSorted (x' :: xs), fP = fP'), SS_cons x x' xs HSS HLt = fP
                          | _ => fun _ => True
                        end fP with
                    | SS_cons x x' xs HSS HLt => _
                    | _ => I
                  end HSS HLt IHks); clear -compK.
          intros; f_equal; [apply IHks | clear -compK].
          apply DC.UIP.
    Qed.          

    Lemma eq_fd (f g : K -f> V) (HEq : findom_t f = findom_t g) : f = g.
    Proof.
      destruct f; destruct g; simpl in *; subst; f_equal; apply eq_SS.
    Qed.

    Lemma fin_Ind : forall (P : (K -f> V) -> Prop)
                      (HNil : P fdEmpty)
                      (HExt : forall k v f, P f -> P (fdUpdate k v f)),
                    forall f, P f.
    Proof.
      clear dependent U.
      intros.
      destruct f as [fs fP].
      induction fs; simpl in *. 
      - assert ({| findom_t := nil; findom_P := fP |} = fdEmpty (V := V)) by (apply eq_fd; reflexivity); rewrite H; assumption.
      - destruct a as [k v]; simpl in *.
        inversion fP; subst; [destruct fs;[|discriminate]|].
        + specialize (HExt k v fdEmpty HNil). 
          unfold fdUpdate in HExt.
          unfold pre_upd in HExt. simpl in HExt.
          assert ({| findom_t := (k, v) :: nil; findom_P := fdUpdate_obligation_1 k v fdEmpty |} = {| findom_t := (k, v) :: nil; findom_P := fP |}) by (apply eq_fd; reflexivity). rewrite <- H; assumption.        
        + rewrite H1 in HS. specialize (HExt k v ({|findom_t := fs; findom_P := HS |}) (IHfs HS)).
          assert (findom_t (fdUpdate k v {| findom_t := fs; findom_P := HS |}) = (k,v)::fs).
          {
          unfold fdUpdate; simpl. 
          unfold pre_upd.          
          destruct fs; [discriminate|]. 
          inversion H1; subst; simpl (fst (k,v)).
          rewrite HLt; reflexivity.
          }
          assert ( fdUpdate k v {| findom_t := fs; findom_P := HS |} =
                   {| findom_t := (k, v) :: fs; findom_P := fP |}) by (apply eq_fd; assumption).
          rewrite <- H0; assumption.
Qed.

  End Map.

  Section Filter.
    Context V `{cmV : cmetric V}.

    Lemma filter_split A (p : A -> bool) x xs ys (HEq : x :: xs = filter p ys) :
      exists ysf, exists yst, ys = ysf ++ x :: yst /\ xs = filter p yst /\ filter p ysf = nil.
    Proof.
      induction ys; simpl in *; [discriminate |].
      destruct (p a) eqn: PA; [inversion HEq; subst | specialize (IHys HEq) ].
      + eexists nil; exists ys; tauto.
      + destruct IHys as [ysf [yst [EQ1 [EQ2 EQ3]]]]; exists (a :: ysf); exists yst.
        simpl; subst; rewrite PA; tauto.
    Qed.

    Lemma SS_app xs ys (HSS : StrictSorted (xs ++ ys)) :
      StrictSorted xs /\ StrictSorted ys.
    Proof.
      induction xs; simpl in *; [split; [apply SS_nil | assumption] |].
      assert (HSS' : StrictSorted xs /\ StrictSorted ys) by (eapply IHxs, SS_tail, HSS).
      clear IHxs; destruct HSS' as [HSSxs HSSys]; split; [| assumption]; clear HSSys.
      destruct xs; [apply SS_sing | apply SS_cons; [assumption |]].
      inversion HSS; subst; assumption.
    Qed.

    Program Definition fdFilter (p : V -> bool) (m : K -f> V) : K -f> V :=
      mkFD (filter (fun a : K * V => p (snd a)) (findom_t m)) _.
    Next Obligation.
      destruct m as [ms mP]; unfold findom_f in *; simpl in *.
      remember (filter (fun a => p (snd a)) ms) as ns.
      generalize dependent ms; induction ns; intros; [apply SS_nil |].
      apply filter_split in Heqns; destruct Heqns as [msf [mst [EQ1 [EQ2 _]]]]; subst.
      rewrite map_app in mP; apply SS_app in mP; destruct mP as [_ mP].
      specialize (IHns mst (SS_tail _ _ mP) (eq_refl _)).
      remember (filter (fun a => p (snd a)) mst) as ns; destruct ns; [apply SS_sing |].
      apply SS_cons; [assumption |]; clear IHns.
      apply filter_split in Heqns; destruct Heqns as [nsf [nst [EQ1 [EQ2 EQ3]]]]; subst.
      clear - mP compK; induction nsf; [simpl; inversion mP; subst; assumption |].
      apply IHnsf; clear IHnsf.
      destruct nsf; simpl in *.
      + inversion mP; subst; clear mP.
        inversion HS; subst; clear HS.
        apply comp_Lt_lt in HLt; apply comp_Lt_lt in HLt0; destruct HLt, HLt0.
        apply SS_cons; [assumption | apply comp_lt_Lt; split; [etransitivity; eassumption | ]].
        intros EQ; rewrite EQ in H.
        apply H2, ord_part; split; assumption.
      + inversion mP; subst; clear mP.
        inversion HS; subst; clear HS.
        apply comp_Lt_lt in HLt; apply comp_Lt_lt in HLt0; destruct HLt, HLt0.
        apply SS_cons; [assumption | apply comp_lt_Lt; split; [etransitivity; eassumption | ]].
        intros EQ; rewrite EQ in H.
        apply H2, ord_part; split; assumption.
    Qed.

  End Filter.

  Section MapProps.

    Context U V W `{pcmU : pcmType U} `{cmV : pcmType V} `{cmW : pcmType W}.

    Lemma fdMap_comp (f : U -m> V) (g : V -m> W) :
      (fdMap _ _ g ∘ fdMap _ _ f == fdMap _ _ (g ∘ f))%pm.
    Proof.
      intros m k; simpl morph.
      destruct (m k) as [u |] eqn: HFnd.
      - rewrite pre_fdMap_lookup with (u := u) by assumption.
        rewrite pre_fdMap_lookup with (u := f u); [reflexivity |].
        rewrite pre_fdMap_lookup with (u := u) by assumption; reflexivity.
      - rewrite !pre_fdMap_lookup_nf; [reflexivity |..]; try assumption; [].
        rewrite pre_fdMap_lookup_nf; reflexivity || assumption.
    Qed.

    Lemma fdMap_id : fdMap _ _ (pid U) == (pid (K -f> U)).
    Proof.
      intros w k; simpl morph.
      destruct (w k) as [v |] eqn: HFnd.
      - rewrite pre_fdMap_lookup with (u := v) by assumption; reflexivity.
      - rewrite pre_fdMap_lookup_nf by assumption; reflexivity.
    Qed.

    Context {extV : extensible V}.

    Definition Extend_fd (me md : K -f> V) :=
      findom_map _ _ me
                 (fun x (HIn : inlst x (dom me) = true) =>
                    let b := inlst x (dom md) in
                    let ve := Indom_lookup x (findom_t me) HIn in
                    match b as b return inlst x (dom md) = b -> V with
                      | true => fun eq => extend ve (Indom_lookup x (findom_t md) eq)
                      | false => fun _ => ve
                    end eq_refl).
    Local Obligation Tactic := idtac.

    Global Program Instance extensible_fd : extensible (K -f> V) := mkExtend Extend_fd.
    Next Obligation.
      clear dependent U; clear dependent W; intros; intros k; unfold Extend_fd.
      destruct (inlst k (dom ve)) eqn: HIne.
      - rewrite findom_map_app with (HIn := HIne).
        generalize (@eq_refl _ (inlst k (dom vd))) as HInd.
        pattern (inlst k (dom vd)) at 2 3; destruct (inlst k (dom vd)); intros.
        + specialize (HD k); specialize (HS k).
          rewrite <- Indom_lookup_find with (HIn := HIne).
          rewrite <- Indom_lookup_find with (HIn := HIne) in HS.
          rewrite <- Indom_lookup_find with (HIn := HInd) in HD.
          destruct (v k) as [vv |]; [| contradiction HD].
          unfold dist, pord in *; simpl in *.
          eapply extend_dist; eassumption.
        + rewrite Indom_lookup_find; reflexivity.
      - rewrite findom_map_app_nf by assumption.
        rewrite NIn_inlst, fdLookup_notin in HIne.
        rewrite HIne; reflexivity.
    Qed.
    Next Obligation.
      clear dependent U; clear dependent W; intros; intros k.
      specialize (HD k); destruct (vd k) as [v1 |] eqn: HFnd1; [| exact I].
      specialize (HS k); destruct (v k) as [v2 |]; [| contradiction HD].
      destruct (ve k) as [v3 |] eqn: HFnd2; [| contradiction HS].
      assert (HInd : inlst k (dom vd) = true) by (rewrite In_inlst, fdLookup_in_strong; eauto).
      assert (HIne : inlst k (dom ve) = true) by (rewrite In_inlst, fdLookup_in_strong; eauto).
      unfold extend, Extend_fd.
      rewrite findom_map_app with (HIn := HIne).
      generalize (@eq_refl _ (inlst k (dom vd))).
      pattern (inlst k (dom vd)) at 2 3; rewrite HInd; clear HInd; intros HInd.
      unfold dist, pord in *; simpl in *.
      rewrite <- Indom_lookup_find with (HIn := HInd) in HFnd1.
      inversion HFnd1; subst v1; clear HFnd1.
      rewrite <- Indom_lookup_find with (HIn := HIne) in HFnd2.
      inversion HFnd2; subst v3; clear HFnd2.
      eapply extend_sub; eassumption.
    Qed.

  End MapProps.
  
  Section Compose.
    Context {V : Type} `{ev : Setoid V} (op : V -> V -> V).
    Implicit Type (f : K -f> V) (k : K) (v : V).
    
    Definition upd (v0 : option V) v :=
            match v0 with Some v' => op v' v | _ => v end.
    
    Require Import Recdef.
    Function fdCompose f g { measure (fun g => length (findom_t g)) g} :=
        match findom_t g with
          | nil => f
          | (k , v) :: g' => 
                (fdCompose (fdUpdate k (upd (f k) v) f)  (fdRemove k g))
      end.
    Proof.
      - intros. simpl in *. rewrite teq. simpl.
        generalize (compat_compare k k). 
        destruct (comp k k); [omega| |]; intros; destruct H; exfalso; by try now auto.
    Defined.

    Lemma XM k0 k1: k0 = k1 \/ k0 <> k1.
    Proof.
      generalize (compat_compare k0 k1); destruct comp; 
      intros; subst; [by left | |]; destruct H; auto.
    Qed.
    
    Lemma FU k : comp k k = Eq.
    Proof.
      generalize (compat_compare k k); destruct comp; firstorder.
    Qed.
    
    Lemma fdRemove_head k0 v0 lg (SSg : StrictSorted (k0 :: map fst lg)) :
      fdRemove k0 {| findom_t := (k0, v0) :: lg; findom_P := SSg |} = mkFD lg (SS_tail _ _ SSg).
    Proof.
      eapply eq_fd.
      revert k0 v0 SSg; induction lg; intros; unfold fdRemove.
      - unfold pre_rem. simpl. by rewrite FU.
      - simpl. by rewrite FU.
    Qed.
    
    Lemma comp_flip_gl k1 k2 : comp k1 k2 = Gt -> comp k2 k1 = Lt.
    Proof.
      intros. apply comp_lt_Lt. destruct (comp_Gt_gt _ _ H); split; auto.
    Qed.
    
    Lemma comp_flip_lg k1 k2 : comp k1 k2 = Lt -> comp k2 k1 = Gt.
    Proof.
      intros. apply comp_gt_Gt. destruct (comp_Lt_lt _ _ H); split; auto.
    Qed.
    
    Lemma SS_Lt k k0 lg : StrictSorted (k0 :: lg) -> In k lg ->
                          comp k0 k = Lt.
    Proof.
      revert k k0; induction lg; intros.
      - by inversion H0.
      - inversion H. destruct H0; subst; first assumption.
        eapply Lt_trans; [ eassumption | by apply IHlg ].
    Qed.

    Lemma fdComposeP (DProper : Proper (equiv ==> equiv ==> equiv) op) f g k v: 
      fdCompose f g k == Some v
    <-> ((exists v1 v2, op v1 v2 == v /\ f k == Some v1 /\ g k == Some v2)
        \/ (f k == Some v /\ g k == None) 
        \/ (f k == None /\ g k == Some v)).
    Proof.
     destruct f as [lf SSf], g as [lg SSg].
     revert lf SSf.
     induction lg; intros.
      - rewrite fdCompose_equation. simpl. 
        split; intros.
        + right. left; split; now eauto.
        + destruct H as [[v1 [v2 [Hv [Hf Hg]]]]|[[Hf Hg]|[Hf Hg]]].
          * exfalso; by simpl in Hg.
          * exact Hf. 
          * exfalso; by simpl in Hg.
      - rewrite fdCompose_equation. destruct a; unfold fst, snd, findom_t. 
        simpl in SSg, SSf.
        rewrite fdRemove_head.
        split; intros.
        + apply IHlg in H. clear IHlg.
          destruct H as [[v1 [v2 [Hv [Hf Hg]]]]|[[Hf Hg]|[Hf Hg]]];
            fold (fdUpdate k0 (upd (mkFD _ SSf k0) v0) (mkFD _ (SSf))) in Hf.
          * unfold findom_f, findom_t in *.
            assert (comp k0 k = Lt).
            { destruct (comp k0 k) eqn:C; auto.
              - generalize (compat_compare k0 k). rewrite C; intros; subst. 
                assert (In k (map fst lg)).
                { change (In k (dom (mkFD _ (SS_tail _ _ SSg)))). apply fdLookup_in.
                  exists v2. exact Hg. }
                exfalso. eapply StrictSorted_notin; last exact H; now eauto.
              - assert (In k (map fst lg)).
                { change (In k (dom (mkFD _ (SS_tail _ _ SSg)))). apply fdLookup_in.
                  exists v2. exact Hg. }
                inversion SSg.
                + assert (lg = []) by (destruct lg; eauto; discriminate H2).
                  rewrite H0 in Hg. simpl in Hg. now auto.
                + subst. rewrite <- H2 in H.
                  exfalso. eapply StrictSorted_lt_notin; last (now eauto); eauto.
                  eapply comp_Lt_lt. eapply Lt_trans; eauto.
                  eapply comp_lt_Lt. destruct (comp_Gt_gt _ _ C); split; now auto.
            }
            left. exists v1 v2; split; first now auto.
            split; last first.
            { simpl findom_lu. rewrite comp_flip_lg; now eauto. }
            assert (fdUpdate k0 (upd (mkFD _ SSf k0) v0) (mkFD _ SSf) k == Some v1) by exact Hf.
            rewrite fdUpdate_neq in H0; first now eauto.
            by eapply comp_Lt_lt.
          * destruct (XM k k0); subst.
            { destruct (mkFD _ SSf k0) eqn:F;
                rewrite fdUpdate_eq in Hf;
                unfold upd in Hf.
              - left. exists v1 v0; split; first now eauto. split; eauto. reflexivity.
                unfold findom_f; simpl findom_lu. rewrite FU. reflexivity.
              - right. right; split; [reflexivity|]. 
                unfold findom_f; simpl findom_lu. by rewrite FU.
            } 
            { rewrite fdUpdate_neq in Hf by auto.
              right. left. split; first now auto. unfold findom_f; simpl findom_lu.
              destruct (comp k k0) eqn:C; [generalize (compat_compare k k0); rewrite C; intros; exfalso; auto | reflexivity | ].
              exact Hg. }
          * assert (IN : In k (dom (mkFD _ (SS_tail _ _ SSg)))).
            { eapply fdLookup_in. exists v. assumption. }
            assert (C : comp k0 k = Lt) by (eapply SS_Lt; eauto).
            assert (k0 <> k) by (generalize (compat_compare k0 k); rewrite C; intros []; auto).
            right. right. split. 
            { by rewrite fdUpdate_neq in Hf by auto. }
            { unfold findom_f; simpl findom_lu. rewrite comp_flip_lg by auto. exact Hg. }
        + 
          destruct H as [[v1 [v2 [Hv [Hf Hg]]]]|[[Hf Hg]|[Hf Hg]]];
          fold (fdUpdate k0 (upd (mkFD _ SSf k0) v0) (mkFD _ (SSf))) in *.
          * unfold findom_f in Hg; simpl findom_lu in Hg. 
            destruct (comp k k0) eqn:C.
            { generalize (compat_compare k k0); rewrite C; intros; subst.
              apply IHlg; clear IHlg. right. left.
              fold (fdUpdate k0 (upd (mkFD _ SSf k0) v0) (mkFD _ (SSf))) in *.
              split.
              - rewrite fdUpdate_eq.
                unfold upd. rewrite <- Hv. case: (_ k0) Hf. 
                + intros. simpl in Hf. simpl. rewrite Hf.
                  simpl in Hg. rewrite Hg. reflexivity.
                + intros F. by destruct F.
              - apply fdLookup_notin. by apply StrictSorted_notin. 
            }
            { by destruct Hg. }
            { apply IHlg; clear IHlg. left. exists v1 v2; split; auto.
              split; last assumption. 
              fold (fdUpdate k0 (upd (mkFD _ SSf k0) v0) (mkFD _ (SSf))) in *.
              rewrite fdUpdate_neq; last by apply comp_Lt_lt, comp_flip_gl. assumption.
            }
          * apply IHlg; clear IHlg. right. left.
            fold (fdUpdate k0 (upd (mkFD _ SSf k0) v0) (mkFD _ (SSf))) in *.
            unfold findom_f in Hg; simpl findom_lu in Hg.
            destruct (comp k k0) eqn:C.
            { by destruct Hg. }
            { split.
              - rewrite fdUpdate_neq; last by apply comp_Gt_gt, comp_flip_lg. assumption.
              - apply fdLookup_notin. intro. eapply StrictSorted_lt_notin; [|exact SSg|right; exact H].
                exact: comp_Lt_lt.
            }
            { split; last now auto. 
              rewrite fdUpdate_neq; last by apply comp_Lt_lt, comp_flip_gl. assumption.
            }
          * unfold findom_f in Hg; simpl findom_lu in Hg. 
            destruct (comp k k0) eqn:C.
            { generalize (compat_compare k k0); rewrite C; intros; subst.
              apply IHlg; clear IHlg. right. left. 
              fold (fdUpdate k0 (upd (mkFD _ SSf k0) v0) (mkFD _ (SSf))) in *.
              rewrite fdUpdate_eq. split.
              - unfold upd. rewrite <- Hg. case: (_ k0) Hf. 
                + intros. simpl in Hf. by destruct Hf.
                + reflexivity. 
              - apply fdLookup_notin. by apply StrictSorted_notin. 
            }
            { by destruct Hg. }
            { apply IHlg; clear IHlg. right. right.
              fold (fdUpdate k0 (upd (mkFD _ SSf k0) v0) (mkFD _ (SSf))) in *.
              split; last assumption.
              rewrite fdUpdate_neq; last by apply comp_Lt_lt, comp_flip_gl. assumption.
            }
    Qed.
    
    Lemma fdComposePN (DProper : Proper (equiv ==> equiv ==> equiv) op) f g k: 
      fdCompose f g k == None
    <-> (f k == None /\ g k == None).
    Proof.
      split; intros.
      - destruct (f k) as [vf|] eqn:F, (g k) as [vg|] eqn:G.
        + assert (f k == Some vf) by (rewrite F; reflexivity).
          assert (g k == Some vg) by (rewrite G; reflexivity).
          assert (fdCompose f g k == Some (op vf vg)).
          { apply fdComposeP; auto.
            left. do 2!eexists; repeat split; eauto. reflexivity. }
          rewrite H in H2. by destruct H2.
        + assert (f k == Some vf) by (rewrite F; reflexivity).
          assert (g k == None) by (rewrite G; reflexivity).
          assert (fdCompose f g k == Some vf).
          { apply fdComposeP; now auto. }
          rewrite H in H2. by destruct H2.
        + assert (f k == None) by (rewrite F; reflexivity).
          assert (g k == Some vg) by (rewrite G; reflexivity).
          assert (fdCompose f g k == Some vg).
          { apply fdComposeP; now auto. }
          rewrite H in H2. by destruct H2.
        + split; reflexivity. 
      - destruct H as [Hf Hg]. 
        destruct (fdCompose f g k) as [v|] eqn:F; last reflexivity.
        assert (fdCompose f g k == Some v) by (rewrite F; reflexivity).
        apply fdComposeP in H; last auto. 
        destruct H as [[v1 [v2 [Hv [H1 H2]]]]|[[H1 H2]|[H1 H2]]].
        + rewrite Hf in H1. by destruct H1.
        + rewrite Hf in H1. by destruct H1.
        + rewrite Hg in H2. by destruct H2.
    Qed.
        

          
  End Compose.

End FinDom.

Arguments fdMap {K cT ord equ preo ord_part compK U V eqT mT cmT pTA pcmU eqT0 mT0 cmT0 pTA0 cmV} _.
