Require Import ssreflect.
Require Import MetricCore.
Require Import PreoMet.
Require Import RA.
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
    rewrite -> Bool.orb_true_iff, IHxs; clear IHxs; intuition.
    - rewrite -> iseq_eq in H0; subst; tauto.
    - subst; unfold iseq; rewrite comp_self_Eq; auto.
  Qed.

  Lemma eq_sym_iff : forall T (x y : T), x = y <-> y = x.
  Proof.
    split; apply eq_sym; assumption.
  Qed.

  Lemma NIn_inlst k xs : inlst k xs = false <-> ~ (k ∈ xs).
    induction xs; simpl; [tauto |].
    rewrite -> Bool.orb_false_iff, IHxs, (eq_sym_iff _ a), <- iseq_eq; clear IHxs.
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

    Lemma option_dec {A} (v : option A): sumbool(v = None) (exists a, v = Some a).
    Proof.
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
      exists (max m k); intros t HIn; rewrite -> In_inlst in HIn; simpl in HIn; destruct HIn as [HEq | HIn];
        [subst | rewrite <- In_inlst in HIn]; eapply A; [| eassumption |..]; eauto using le_max_r, le_max_l.
    Qed.

    Lemma findom_fun_map U xs (I : forall x, inlst x xs = true -> U) x
      (HIn : inlst x xs = true) (HSS : StrictSorted xs) :
      findom_lu (ind_app_map _ xs I) x = Some (I _ HIn).
    Proof.
      induction xs; [discriminate |].
      simpl; assert (HT := compat_compare x a); destruct (comp x a).
      - subst; rewrite -> (D.UIP _ _ _ HIn); reflexivity.
      - contradiction (StrictSorted_lt_notin _ _ xs HT).
        rewrite <- In_inlst; assumption.
      - simpl in *; specialize (IHxs (fun y Y => I _ (orb_right_intro _ _ Y))).
        assert (HInT : inlst x xs = true) by (unfold iseq in HIn; rewrite comp_gt_Gt in HIn; assumption).
        specialize (IHxs HInT (SS_tail _ _ HSS)); simpl in IHxs; rewrite -> (D.UIP _ _ _ HIn) in IHxs; apply IHxs.
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
    
    Global Program Instance type_findom : Setoid (K -f> V) := mkType equiv_fd.

    Global Instance lookup_proper : Proper (equiv ==> eq ==> equiv) (findom_f (V := V)).
    Proof.
      intros f1 f2 HEqf k1 k2 HEqk; subst; apply HEqf.
    Qed.

    Definition dist_fd n (f1 f2 : K -f> V) :=
      match n with
        | O => True
        | S _ => forall k, f1 k = n = f2 k
      end.

    Global Program Instance metric_findom : metric (K -f> V) := mkMetr dist_fd.
    Next Obligation.
      revert n; intros [| n] f1 f2 EQf g1 g2 EQg; [reflexivity |]; split;
      intros EQ k; [symmetry in EQf, EQg |]; rewrite -> EQf, EQg; apply EQ.
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
        rewrite -> comp_lt_Lt, comp_self_Eq in HGt; [contradiction HGt | intuition].
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
      rewrite -> fdLookup_in in HIn; destruct HIn as [v HLU].
      remember ((σ 2) x) as ov; symmetry in Heqov; destruct ov.
      - rewrite fdLookup_in; eexists; setoid_rewrite Heqov; reflexivity.
      - assert (HT := chain_cauchy σ _ 1 1 2 x).
        rewrite -> Heqov, HLU in HT; contradiction HT.
    Qed.
    
    Program Definition finmap_chainx (σ : chain (K -f> V)) {σc : cchain σ} x (HIn : x ∈ dom (σ 1)) : chain V :=
      fun n => 
                         match σ (S n) x with
                           | None =>  _
                           | Some v => v
                         end.
    Next Obligation.
      exfalso.
      assert (Le1n : 1 <= S n) by omega.
      move: (σc _ _ _ Le1n (le_refl _) x).
      move/fdLookup_in_strong : HIn => [v ->]. by rewrite -Heq_anonymous.
    Defined.

    Program Instance finmap_chainx_cauchy (σ : chain (K -f> V)) {σc : cchain σ} x {HIn : x ∈ dom (σ 1)} :
      cchain (finmap_chainx σ x HIn).
    Next Obligation. 
      fold dist.
      destruct n as [|n]; first by apply dist_bound.
      unfold finmap_chainx.
      generalize (@eq_refl _ (σ (S i) x)); pattern (σ (S i) x) at 1 3.
      destruct (σ (S i) x) as [vi |] => [EQni|E]; last first. 
      { exfalso. eapply (fdLookup_notin_strong x (σ (S i))); [by symmetry|by eapply finmap_chain_dom]. }
      generalize (@eq_refl _ (σ (S j) x)); pattern (σ (S j) x) at 1 3.
      destruct (σ (S j) x) as [vj |] => [EQnj|E]; last first. 
      { exfalso. eapply (fdLookup_notin_strong x (σ (S j))); [by symmetry|by eapply finmap_chain_dom]. }
      move : (σc _ _ _ (le_S _ _ HLei) (le_S _ _ HLej) x). 
      by rewrite -EQni -EQnj. 
    Qed.
    
    Definition findom_lub (σ : chain (K -f> V)) (σc : cchain σ) : K -f> V :=
      findom_map _ _ (σ 1) (fun x HLu => compl (finmap_chainx σ x (proj1 (In_inlst _ _) HLu))).

    Global Program Instance findom_cmetric : cmetric (K -f> V) := mkCMetr findom_lub.
    Next Obligation.
      move => [| n] ; [now auto|]. 
      move => i LEi k.
      destruct (inlst k (dom (σ 1))) eqn: HIn.
      - rewrite /findom_lub findom_map_app.
        assert (HT := conv_cauchy (finmap_chainx σ k (proj1 (In_inlst k (dom (σ 1))) HIn)) (S n)).
        case EQi : (σ i k) => [vi|]; [|exfalso].
        + rewrite /dist /= -/dist. rewrite HT {HT}. 
          rewrite /finmap_chainx.
          generalize (@eq_refl _ (σ (S i) k)); pattern (σ (S i) k) at 1 3.
          destruct (σ (S i) k) as [vSi |] => [EQsi|EQsi]; [|exfalso].
          * have σc' := (σc (S n) (S i) i _ _ k) => {σc}. rewrite <- EQsi, EQi in σc'. 
            apply σc'; by omega.
          * have σc' := (σc (S n) (S i) i _ _ k) => {σc}. rewrite <- EQsi, EQi in σc'. 
            apply σc'; by omega.
        + clear HT. have σc' := (σc 1 1 i _ _ k) => {σc}. rewrite EQi in σc'. 
          move/In_inlst/fdLookup_in_strong : HIn σc' => [v1 ->] σc.
          apply σc; by omega.
      - rewrite /findom_lub findom_map_app_nf //.
        have σc' := σc 1 1 i _ _ k => {σc}.
        move/NIn_inlst/fdLookup_notin_strong : HIn σc' => -> σc'. 
        destruct (σ i k) => //. exfalso; apply σc'; omega.
    Qed.

    Local Existing Instance option_preo_bot.
    Local Existing Instance option_pcm_bot.

    Definition extOrd (m1 m2 : K -f> V) := forall k, m1 k ⊑ m2 k.

    Global Program Instance extOrd_preo : preoType (K -f> V) := mkPOType extOrd _.
    Next Obligation.
      split.
      - intros m k; reflexivity.
      - intros m1 m2 m3 S12 S23 k; etransitivity; [apply (S12 k) | apply (S23 k) ].
    Qed.
    Next Obligation.
      move=> f1 f2 Rf g1 g2 Rg H k.
      by rewrite -(Rf k) -(Rg k).
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
        { rewrite -> In_inlst, fdLookup_in_strong; exists vs; congruence. }
        rewrite -> findom_map_app with (HIn := HIn).
        unfold equiv; simpl; apply umet_complete_ext; intros.
        unfold unSome, finmap_chainx.
        generalize (@eq_refl _ (σ (S i) k)) as EQsi.
        pattern (σ (S i) k) at 1 3 7; destruct (σ (S i) k) as [vsi |]; intros; [| exfalso].
        + have HInSi : inlst k (dom (σ (S i))) = true.
          { apply In_inlst. apply finmap_chain_dom => //. exact/In_inlst. }
          rewrite <- (Indom_lookup_find _ (σ (S i)) HInSi) in EQsi.
          inversion EQsi; reflexivity.
        + assert (LEi : 1 <= S i) by auto with arith.
          specialize (σc 1 1 (S i) (le_n _) LEi k).
          rewrite <- EQs, <- EQsi in σc; contradiction σc.
      - unfold findom_lub.
        rewrite -> findom_map_app_nf; [reflexivity |].
        rewrite -> NIn_inlst, fdLookup_notin_strong; congruence.
    Qed.

    Global Instance findom_pcmType : pcmType (K -f> V).
    Proof.
      split.
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
      - rewrite -> pre_fdMap_lookup with (u := u1), pre_fdMap_lookup with (u := u2);
        [apply met_morph_nonexp |..]; assumption.
      - rewrite !pre_fdMap_lookup_nf; assumption.
    Qed.
    Next Obligation.
      intros m1 m2 Subm k; specialize (Subm k); destruct (m1 k) as [u1 |] eqn: HFnd1.
      - erewrite pre_fdMap_lookup by eassumption.
        destruct (m2 k) as [u2 |] eqn: HFnd2; [| contradiction Subm].
        erewrite pre_fdMap_lookup by eassumption.
        unfold pord in *; simpl in *.
        rewrite -> Subm; reflexivity.
      - rewrite -> pre_fdMap_lookup_nf by assumption; exact I.
    Qed.

    Global Instance fdMap_resp : Proper (equiv ==> equiv) fdMap.
    Proof.
      intros f1 f2 EQf m k; destruct (m k) as [u |] eqn: HFnd; simpl morph.
      - rewrite -> !pre_fdMap_lookup with (u := u) by assumption.
        rewrite EQf; apply morph_resp; reflexivity.
      - rewrite -> !pre_fdMap_lookup_nf by assumption; reflexivity.
    Qed.

    Global Instance fdMap_nonexp n : Proper (dist n ==> dist n) fdMap.
    Proof.
      intros f1 f2 EQf m; destruct n as [| n]; [apply dist_bound |]; intros k.
      simpl morph; destruct (m k) as [u |] eqn: HFnd.
      - rewrite -> !pre_fdMap_lookup with (u := u) by assumption.
        unfold dist; simpl; rewrite EQf; apply met_morph_nonexp; reflexivity.
      - rewrite -> !pre_fdMap_lookup_nf by assumption; reflexivity.
    Qed.

    Global Instance fdMap_monic : Proper (pord ==> pord) fdMap.
    Proof.
      intros f1 f2 Subf m k; simpl morph.
      destruct (m k) as [u |] eqn: HFnd.
      - erewrite !pre_fdMap_lookup by eassumption.
        unfold pord; simpl; apply (Subf u).
      - rewrite -> !pre_fdMap_lookup_nf by assumption.
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
      - rewrite -> pre_fdMap_lookup with (u := u) by assumption.
        rewrite -> pre_fdMap_lookup with (u := f u); [reflexivity |].
        rewrite -> pre_fdMap_lookup with (u := u) by assumption; reflexivity.
      - now rewrite !pre_fdMap_lookup_nf; [reflexivity |..]; try assumption; [].
    Qed.

    Lemma fdMap_id : fdMap _ _ (pid U) == (pid (K -f> U)).
    Proof.
      intros w k; simpl morph.
      destruct (w k) as [v |] eqn: HFnd.
      - rewrite -> pre_fdMap_lookup with (u := v) by assumption; reflexivity.
      - rewrite -> pre_fdMap_lookup_nf by assumption; reflexivity.
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
      - rewrite -> findom_map_app with (HIn := HIne).
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
      - rewrite -> findom_map_app_nf by assumption.
        rewrite -> NIn_inlst, fdLookup_notin in HIne.
        rewrite HIne; reflexivity.
    Qed.
    Next Obligation.
      clear dependent U; clear dependent W; intros; intros k.
      specialize (HD k); destruct (vd k) as [v1 |] eqn: HFnd1; [| exact I].
      specialize (HS k); destruct (v k) as [v2 |]; [| contradiction HD].
      destruct (ve k) as [v3 |] eqn: HFnd2; [| contradiction HS].
      assert (HInd : inlst k (dom vd) = true) by (rewrite -> In_inlst, fdLookup_in_strong; eauto).
      assert (HIne : inlst k (dom ve) = true) by (rewrite -> In_inlst, fdLookup_in_strong; eauto).
      unfold extend, Extend_fd.
      rewrite -> findom_map_app with (HIn := HIne).
      generalize (@eq_refl _ (inlst k (dom vd))).
      pattern (inlst k (dom vd)) at 2 3; rewrite -> HInd; clear HInd; intros HInd.
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
    Implicit Type (f g : K -f> V) (k : K) (v : V).
    
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

    Lemma fin_ind : 
      forall (P : K -f> V -> Prop),
       P fdEmpty ->
       (forall k v l (SSf : StrictSorted (k :: map fst l)), 
          let f := mkFD _ (SS_tail _ _ SSf) in
          let f' := mkFD ((k,v) :: l) SSf in
              P f -> P f') ->
       forall f : K -f> V, P f.
    Proof.
      move => P P0 IH [f].
      induction f as [|[k v] f] => SSf; first by rewrite (eq_SS _ SSf SS_nil). 
      apply: (IH _ _ _ SSf). exact: IHf.
    Qed.
    

    Context {DProper : Proper (equiv ==> equiv ==> equiv) op}.
    
    Lemma fdComposeP f g k v: 
      fdCompose f g k == Some v
    <-> ((exists v1 v2, op v1 v2 == v /\ f k == Some v1 /\ g k == Some v2)
        \/ (f k == Some v /\ g k == None) 
        \/ (f k == None /\ g k == Some v)).
    Proof.
     revert g f. elim/fin_ind => [f|k0 v0 l SSg g g' IHg f].
      - rewrite fdCompose_equation. simpl. 
        split; intros.
        + right. left; split; now eauto.
        + by case : H => [[v1 [v2 [Hv [Hf []]]]]|[[Hf Hg //]|[Hf []]]].
      - rewrite fdCompose_equation. 
        simpl in SSg. simpl findom_t; red.
        rewrite fdRemove_head; fold g. 
        split; intros.
        + case/IHg: H => [[v1 [v2 [Hv [Hf Hg]]]]|[[Hf Hg]|[Hf Hg]]];
            fold (fdUpdate k0 (upd (f k0) v0) (f)) in Hf.
          * unfold findom_f, findom_t in *.
            assert (comp k0 k = Lt).
            { destruct (comp k0 k) eqn:C; auto.
              - generalize (compat_compare k0 k). rewrite C; intros. subst k.
                assert (In k0 (map fst (findom_t g))).
                { apply fdLookup_in. exists v2. exact Hg. }
                exfalso. eapply StrictSorted_notin; last exact H; now eauto.
              - assert (In k (map fst (findom_t g))).
                { apply fdLookup_in. exists v2. exact Hg. }
                inversion SSg.
                + assert (l = []) by (destruct l; eauto; discriminate H2).
                  rewrite /= H0 in Hg. by destruct Hg. 
                + subst. rewrite /= -H2 in H.
                  exfalso. eapply StrictSorted_lt_notin; last (now eauto); eauto.
                  eapply comp_Lt_lt. eapply Lt_trans; eauto.
                  eapply comp_lt_Lt. destruct (comp_Gt_gt _ _ C); split; now auto.
            }
            left. exists v1 v2; split; first now auto.
            split; last first.
            { simpl findom_lu. rewrite comp_flip_lg; now eauto. }
            assert (fdUpdate k0 (upd (f k0) v0) f k == Some v1) by exact Hf.
            rewrite fdUpdate_neq in H0; first now eauto.
            by eapply comp_Lt_lt.
          * destruct (XM k k0); subst.
            { destruct (f k0) eqn:F;
                rewrite fdUpdate_eq in Hf;
                unfold upd in Hf.
              - left. exists v1 v0; split; first now eauto. split; eauto. reflexivity.
                unfold findom_f; simpl findom_lu. rewrite FU. reflexivity.
              - right. right; split; [reflexivity|]. 
                unfold findom_f; simpl findom_lu. by rewrite FU.
            } 
            { rewrite ->fdUpdate_neq in Hf by auto.
              right. left. split; first now auto. unfold findom_f; simpl findom_lu.
              destruct (comp k k0) eqn:C; [generalize (compat_compare k k0); rewrite C; intros; exfalso; auto | reflexivity | ].
              exact Hg. }
          * assert (IN : In k (dom (mkFD _ (SS_tail _ _ SSg)))).
            { eapply fdLookup_in. exists v. assumption. }
            assert (C : comp k0 k = Lt) by (eapply SS_Lt; eauto).
            assert (k0 <> k) by (generalize (compat_compare k0 k); rewrite C; intros []; auto).
            right. right. split. 
            { by rewrite ->fdUpdate_neq in Hf by auto. }
            { unfold findom_f; simpl findom_lu. rewrite ->comp_flip_lg by auto. exact Hg. }
        + 
          destruct H as [[v1 [v2 [Hv [Hf Hg]]]]|[[Hf Hg]|[Hf Hg]]];
          fold (fdUpdate k0 (upd (f k0) v0) f) in *.
          * unfold findom_f in Hg; simpl findom_lu in Hg. 
            destruct (comp k k0) eqn:C.
            { generalize (compat_compare k k0); rewrite C; intros; subst.
              apply IHg; right. left.
              fold (fdUpdate k0 (upd (f k0) v0) f) in *.
              split.
              - rewrite fdUpdate_eq.
                unfold upd. rewrite <- Hv. case: (_ k0) Hf. 
                + intros. simpl in Hf. simpl. rewrite Hf.
                  simpl in Hg. rewrite Hg. reflexivity.
                + intros F. by destruct F.
              - apply fdLookup_notin. by apply StrictSorted_notin. 
            }
            { by destruct Hg. }
            { apply IHg; left. exists v1 v2; split; auto.
              split; last assumption. 
              fold (fdUpdate k0 (upd (f k0) v0) f) in *.
              rewrite fdUpdate_neq; last by apply comp_Lt_lt, comp_flip_gl. assumption.
            }
          * apply IHg; right. left.
            fold (fdUpdate k0 (upd (f k0) v0) f) in *.
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
              apply IHg; right. left. 
              fold (fdUpdate k0 (upd (f k0) v0) f) in *.
              rewrite fdUpdate_eq. split.
              - unfold upd. rewrite <- Hg. case: (_ k0) Hf. 
                + intros. simpl in Hf. by destruct Hf.
                + reflexivity. 
              - apply fdLookup_notin. by apply StrictSorted_notin. 
            }
            { by destruct Hg. }
            { apply IHg; right. right.
              fold (fdUpdate k0 (upd (f k0) v0) f) in *.
              split; last assumption.
              rewrite fdUpdate_neq; last by apply comp_Lt_lt, comp_flip_gl. assumption.
            }
    Qed.
    
    Lemma fdComposePN f g k: 
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
          rewrite ->H in H2. by destruct H2.
        + assert (f k == Some vf) by (rewrite F; reflexivity).
          assert (g k == None) by (rewrite G; reflexivity).
          assert (fdCompose f g k == Some vf).
          { apply fdComposeP; now auto. }
          rewrite ->H in H2. by destruct H2.
        + assert (f k == None) by (rewrite F; reflexivity).
          assert (g k == Some vg) by (rewrite G; reflexivity).
          assert (fdCompose f g k == Some vg).
          { apply fdComposeP; now auto. }
          rewrite ->H in H2. by destruct H2.
        + split; reflexivity. 
      - destruct H as [Hf Hg]. 
        destruct (fdCompose f g k) as [v|] eqn:F; last reflexivity.
        assert (fdCompose f g k == Some v) by (rewrite F; reflexivity).
        apply fdComposeP in H; last auto. 
        destruct H as [[v1 [v2 [Hv [H1 H2]]]]|[[H1 H2]|[H1 H2]]].
        + rewrite ->Hf in H1. by destruct H1.
        + rewrite ->Hf in H1. by destruct H1.
        + rewrite ->Hg in H2. by destruct H2.
    Qed.
        
    Lemma fdCompose_sym (op_sym : forall v1 v2, op v1 v2 == op v2 v1) f g: 
      fdCompose f g == fdCompose g f.
    Proof.
      move => x.
      apply opt_eq_iff => v.
      split; move/fdComposeP => [[v1 [v2 [Hv [H1 H2]]]]|[[H1 H2]|[H1 H2]]]; apply/fdComposeP;
      try rewrite -> op_sym in Hv; eauto 10.
    Qed.
    
    Lemma fdCompose_PL f g x v:
      f x == Some v -> ((exists v2, fdCompose f g x == Some (op v v2) /\ g x == Some v2) 
                          \/ fdCompose f g x == Some v /\ g x == None).
    Proof.
      move => Hf. case Hg: (g x) => [v2|]; move/equivR in Hg.
      - left; eexists; split; last reflexivity. apply fdComposeP; left. do 2!eexists; repeat split; eauto; []; reflexivity. 
      - right; split; last reflexivity.
        apply fdComposeP; auto. 
    Qed.
    
    Lemma fdCompose_PR f g x v:
      g x == Some v -> ((exists v1, fdCompose f g x == Some (op v1 v) /\ f x == Some v1) 
                          \/ fdCompose f g x == Some v /\ f x == None).
    Proof.
      move => Hf. case Hg: (f x) => [v2|]; move/equivR in Hg.
      - left; eexists; split; last reflexivity. apply fdComposeP; left. do 2!eexists; repeat split; eauto; []; reflexivity. 
      - right; split; last reflexivity.
        apply fdComposeP; auto. 
    Qed.

    Lemma fdCompose_update_neq f g k v x (NEq : k <> x):
      fdCompose (fdUpdate k v f) g x == fdCompose f g x. 
    Proof.
      apply opt_eq_iff => v0.
      split => /fdComposeP => H; apply fdComposeP; move: H; rewrite -> fdUpdate_neq by auto; by []. 
    Qed.
    
    Lemma fdCompose_update_eq f g k v:
      fdCompose g (fdUpdate k v f) k == Some (upd (g k) v). 
    Proof.
      apply fdComposeP. rewrite fdUpdate_eq. case : (g k) => [vg|].  
      - left. simpl. do 2!eexists; repeat split; reflexivity.
      - right; right. split; first now auto. reflexivity.
    Qed.
    
    Lemma fdCompose_remove_neq f g k x (NEq : k <> x):
      fdCompose (fdRemove k f) g x == fdCompose f g x. 
    Proof.
      apply opt_eq_iff => v0.
      split => /fdComposeP => H; apply fdComposeP; move: H; rewrite -> fdRemove_neq by auto; by []. 
    Qed.
    
    Lemma fdCompose_remove_eq f g k:
      fdCompose (fdRemove k f) g k == g k. 
    Proof.
      case Hg : (g k) => [vg|].
      - apply fdComposeP. rewrite fdRemove_eq. right; right; split; [reflexivity|exact/equivR].
      - apply fdComposePN. rewrite fdRemove_eq. split; [reflexivity|exact/equivR].
    Qed.

  End Compose.

End FinDom.

Arguments fdMap {K cT ord equ preo ord_part compK U V eqT mT cmT pTA pcmU eqT0 mT0 cmT0 pTA0 cmV} _.

Section RA.
  Context {I : Type} {S : Type} `{CI : comparable I} `{RAS : RA S}.
  Implicit Type (i : I) (s : S) (f g : I -f> S).

  Local Open Scope ra_scope.
  
  Global Instance ra_type_finprod : Setoid (I -f> S) := _.
  Global Instance ra_unit_finprod : RA_unit (I -f> S) := fdEmpty.
  Global Instance ra_op_finprod : RA_op (I -f> S) := fdCompose (ra_op).
  Global Instance ra_valid_finprod : RA_valid (I -f> S) := fun f => forall i s, f i == Some s -> ra_valid s.
  
  
  Definition fdComposeP' := fdComposeP ra_op (DProper := ra_op_proper).
  Definition fdComposePN' := fdComposePN ra_op (DProper := ra_op_proper).
  Definition fdCompose_sym' := fdCompose_sym ra_op (DProper := ra_op_proper) (ra_op_comm).


  Global Instance ra_finprod : RA (I -f> S).
  Proof.
    split; repeat intro.
    - unfold ra_op, ra_op_finprod.
      eapply opt_eq_iff => v.
      split => /(fdComposeP').
      + move => [[v1 [v2 [Hv [Hx Hx0]]]]|[[Hx Hx0]|[Hx Hx0]]];
        apply fdComposeP'.
        * left. exists v1 v2; split; first (now auto); split; by rewrite -?H -?H0.
        * right. left. split; by rewrite -?H -?H0.
        * right. right. split; by rewrite -?H -?H0.
      + move => [[v1 [v2 [Hv [Hy Hy0]]]]|[[Hy Hy0]|[Hy Hy0]]];
        apply fdComposeP'.
        * left. exists v1 v2; split; first (now auto); split; by rewrite ?H ?H0.
        * right. left. split; by rewrite ?H ?H0.
        * right. right. split; by rewrite ?H ?H0.
    - unfold ra_op, ra_op_finprod.
      eapply opt_eq_iff => v.
      split => /(fdComposeP').
      + move => [[v1 [v2 [Hv [Hx Hx0]]]]|[[Hx Hx0]|[Hx Hx0]]];
        apply fdComposeP'.
        * apply fdComposeP' in Hx0.
          destruct Hx0 as [[v1' [v2' [Hv' [Hx' Hx'0]]]]|[[Hx' Hx'0]|[Hx' Hx'0]]].
          { left. exists (v1 · v1') v2'; split; last split; last auto.
            - rewrite -ra_op_assoc Hv'. exact Hv.
            - apply fdComposeP'. left. exists v1 v1'; repeat split; auto. reflexivity.
          }
          { right. left. split; auto. apply fdComposeP'. left. eexists; now eauto. }
          { left. exists v1 v2; repeat split; auto.
            apply fdComposeP'. now eauto. }
        * apply fdComposePN' in Hx0. destruct Hx0.
          right. left. split; last now auto.
          apply fdComposeP'. now auto. 
        * apply fdComposeP' in Hx0.
          destruct Hx0 as [[v1' [v2' [Hv' [Hx' Hx'0]]]]|[[Hx' Hx'0]|[Hx' Hx'0]]].
          { left. do 2!eexists; repeat split; [now eauto | | now eauto]. 
            apply fdComposeP'. now eauto. }
          { right. left. split; auto; []. apply fdComposeP'. now eauto. }
          { right. right. split; [|assumption]. now apply fdComposePN'. }
      + move => [[v1 [v2 [Hv [Hy Hy0]]]]|[[Hy Hy0]|[Hy Hy0]]];
        apply fdComposeP'.
        * apply fdComposeP' in Hy.
          destruct Hy as [[v1' [v2' [Hv' [Hy' Hy'0]]]]|[[Hy' Hy'0]|[Hy' Hy'0]]].
          { left. do 2!eexists; repeat split; [| |].
            - rewrite <- Hv, <- Hv', -> ra_op_assoc. reflexivity. 
            - assumption.
            - eapply fdComposeP'. left. do 2!eexists; split; eauto; []. reflexivity.
          }
          { left. do 2!eexists; repeat split; [eassumption| assumption |].
            eapply fdComposeP'. right; right. now eauto. }
          { right; right. split; first assumption. eapply fdComposeP'.
            left; now eauto. }
        * apply fdComposeP' in Hy.
          destruct Hy as [[v1' [v2' [Hv' [Hy' Hy'0]]]]|[[Hy' Hy'0]|[Hy' Hy'0]]].
          { left. do 2!eexists; repeat split; [| |].
            - exact Hv'.
            - assumption.
            - eapply fdComposeP'. now eauto. 
          }
          { right; left. split; first assumption. by eapply fdComposePN'. }
          { right; right. split; first assumption. eapply fdComposeP'.
            right; left; now eauto. }
        * apply fdComposePN' in Hy. destruct Hy.
          right; right; split; first assumption. apply fdComposeP'. now eauto. 
    - apply opt_eq_iff => v.
      split => /fdComposeP'; move => [[v1 [v2 [Hv [H1 H2]]]]|[[H1 H2]|[H1 H2]]];
        apply fdComposeP'; try (now eauto); 
        rewrite -> ra_op_comm in Hv; left; do 2!eexists; repeat split; eauto.
    - cut (forall v, (1 · t) k == v <-> t k == v).
      + intros. specialize (H ((1 · t) k)). symmetry. apply H. reflexivity.
      + move => [v|].
        * split; [move => /fdComposeP'; move => [[v1 [v2 [Hv [[] //]]]]|[[[] //]|[H1 H2 //]]]|].
          move=>Ht. apply fdComposeP'. by right; right.
        * split; [move/fdComposePN' => [] //|move => ?; apply fdComposePN'; split; now auto].
    - split; move => Hx k v Hy; apply (Hx k); by rewrite ?H // -?H.
    - by destruct H.
    - case Hi: (t2 i) => [v|]; apply equivR in Hi. 
      + apply (ra_op_valid (t2 := v)). apply (H i), fdComposeP'. 
        left; do 2!eexists; repeat split; eauto. reflexivity.
      + apply (H i). eapply fdComposeP'. by eauto.
  Qed.

  (* The RA order on finmaps is the same as the fpfun order over the RA order *)
  Lemma ra_pord_iff_ext_pord {f g}:
    pord (preoType:=pord_ra) f g <-> pord (preoType:=extOrd_preo) f g.
  Proof.
    split.
    - move => [h Hhf] x. specialize (Hhf x). 
      revert g f h x Hhf; apply : fin_ind => [f|k v l SSg g g' IHg f] h x Hhf.
      + case Hfx: (f x) => //=. 
        assert (f x = None).
        { case Hhfx : ((h · f) x).
          - move/equivR in Hhfx. by rewrite -> Hhf in Hhfx. 
          - move/equivR/fdComposePN' : Hhfx => []. by rewrite Hfx.
        }
        by rewrite H in Hfx.
      + case : (XM x k) Hhf => [-> <-|Hxk Hx].
        * case Hfk: (f k) => [a|//]; move/equivR in Hfk.
          { case (fdCompose_PR _ h _ _ _ Hfk) => [[v1 [-> _]]|[-> _]].
            - exists v1; reflexivity.
            - reflexivity. }
        * assert (Hg'x : g' x == None \/ g' x == g x).
          { unfold findom_f. simpl findom_lu. 
            case Cxk : (comp x k).
            - generalize (compat_compare x k). rewrite Cxk => ?; by subst x.
            - left; now auto.
            - right; now auto.
          } 
          case: Hg'x => [|Hg'x].
          { rewrite <- Hx. move/fdComposePN' => [_ ->]. reflexivity. }
          { rewrite -> Hg'x in *. eapply IHg. exact: Hx. }
    - revert g f.
      apply : fin_ind => [f|k v l SSg g g' IHg f].
      + move => H. eexists fdEmpty => x. apply fdComposePN'; split; first now auto.
        move: (H x). by case (f x).
      + move => H. 
        case Hfk : (f k) => [vf|].
        * have/IHg IH : (fdRemove k f ⊑ g).
          { move => x; fold g; case Cxk : (comp x k).
            - generalize (compat_compare x k); rewrite Cxk => ->. by rewrite fdRemove_eq.
            - rewrite fdRemove_neq; last by apply comp_Gt_gt, comp_flip_lg.
              move: (H x). unfold findom_f at 2; simpl findom_lu. rewrite Cxk.
              by case (f x).
            - rewrite fdRemove_neq; last by apply comp_Lt_lt, comp_flip_gl.
              move: (H x). unfold findom_f at 2; simpl findom_lu. by rewrite Cxk.
          } 
          move: (H k); rewrite Hfk. case Hgk' : (g' k) => [vg|//]. move => [vr Hvr].
          rewrite /findom_f [findom_lu _ k]/= FU /= in Hgk'. move/equivR => /= in Hgk'. 
          rewrite <- Hgk' in Hvr. clear Hgk'.
          move : IH => [h Hhf].
          exists (fdUpdate k vr h) => x.
          apply opt_eq_iff => vx. 
          split.
          { case Cxk : (comp x k).
            - generalize (compat_compare x k); rewrite Cxk; move => E; subst x.
              rewrite (fdCompose_sym' _ f k) fdCompose_update_eq Hfk [_ == _]/= ra_op_comm Hvr => <-.
              rewrite /findom_f [findom_lu _ k]/= FU. reflexivity.
            - rewrite fdCompose_update_neq; last by apply comp_Gt_gt, comp_flip_lg.
              move : (Hhf x).
              rewrite (fdCompose_sym' _ (fdRemove k _) x) fdCompose_remove_neq ?(fdCompose_sym' _ h) 
              => [-> Hg|];
                last by apply comp_Gt_gt, comp_flip_lg.
              exfalso. eapply StrictSorted_lt_notin; [apply comp_Lt_lt; eassumption|eassumption|right].
              change (x ∈ dom g). apply fdLookup_in. by eauto.
            - rewrite fdCompose_update_neq; last by apply comp_Lt_lt, comp_flip_gl.
              move : (Hhf x).
              rewrite (fdCompose_sym' _ (fdRemove k _) x) fdCompose_remove_neq ?(fdCompose_sym' _ h) 
              => [-> Hg|];
                last by apply comp_Lt_lt, comp_flip_gl.
              by rewrite /findom_f [findom_lu _ x]/= Cxk.
          } 
          { 
            rewrite [g' x]/findom_f [findom_lu _ x]/=.
            case Cxk : (comp x k) => [|//|].
            + generalize (compat_compare x k); rewrite Cxk; move => E; subst x.
              move => Hvx. rewrite /= in Hvx. rewrite <- Hvx.
              apply fdComposeP'. left; exists vr vf; repeat split; [now auto| |exact/equivR].
              rewrite fdUpdate_eq. reflexivity.
            + rewrite -/(g x) -Hhf.
              have Hhu : (forall v0, h x == v0 -> fdUpdate k vr h x == v0).
              { move => v0. rewrite fdUpdate_neq; first by []; by apply comp_Lt_lt, comp_flip_gl. }
              rewrite (fdCompose_sym' h _ x) fdCompose_remove_neq ?fdCompose_update_neq
                     ?(fdCompose_sym' _ h x) => //; by apply comp_Lt_lt, comp_flip_gl.
          }
       * have/IHg IH : (f ⊑ g).
         { move => x. move: (H x). rewrite /(findom_f g') [findom_lu _ x]/=.
           case Cxk : (comp x k) => [||//].
           + generalize (compat_compare x k); rewrite Cxk => E; subst x; by rewrite Hfk.
           + by case (f x).
         } 
         move: IH => [h Hfg].
         exists (fdUpdate k v h) => x.
         case Cxk : (comp x k) => [||]; rewrite [g' x]/findom_f [findom_lu (findom_t g') x]/= Cxk.
         { generalize (compat_compare x k); rewrite Cxk => E; subst x.
           apply fdComposeP'. right; left; split; [rewrite fdUpdate_eq; reflexivity|exact/equivR].
         }
         { rewrite fdCompose_update_neq; last by apply comp_Gt_gt, comp_flip_lg. 
           case Hhf : (_ x) => [vx|//].
           exfalso. eapply StrictSorted_lt_notin.
           - apply comp_Lt_lt; eassumption.
           - eassumption.
           - right. change (x ∈ dom g). apply fdLookup_in. eexists; now rewrite -Hfg Hhf.
         } 
         { rewrite fdCompose_update_neq; last by apply comp_Lt_lt, comp_flip_gl. 
           exact: Hfg. }
  Qed.
End RA.
Section CMRA.
  Context {I : Type} `{CI : comparable I}.
  Context {T: Type} `{cmraS: CMRA T}.
  
  Local Open Scope ra.

  Global Instance ra_finmap_pcm: pcmType (pTA:=pord_ra) (I -f> T).
  Proof.
    split. intros σ ρ σc ρc HC.
    apply ra_pord_iff_ext_pord.
    eapply pcm_respC; first by apply _.
    move=>i. apply ra_pord_iff_ext_pord. by apply: HC.
  Qed.

  Global Instance finmap_cmra : CMRA (I -f> T).
  Proof.
    split. move=>n f1 f2 EQf g1 g2 EQg.
    destruct n as [|n]; first by apply: dist_bound.
    move => k. 
    case Hf1g1: ((f1 · g1) k) => [v1|];
    case Hf2g2: ((f2 · g2) k) => [v2|];
      move : Hf1g1 Hf2g2 (EQf k) (EQg k) => // /equivR Hf1g1 /equivR Hf2g2.
    - move/fdComposeP : (Hf1g1) => [[vf1 [vg1 [<- [-> ->]]]]|[[-> ->]|[-> ->]]];
      move/fdComposeP : (Hf2g2) => [[vf2 [vg2 [<- [-> ->]]]]|[[-> ->]|[-> ->]]];
      move => // /= -> ->. reflexivity.
    - move/fdComposeP : (Hf1g1) => [[vf1 [vg1 [<- [-> ->]]]]|[[-> ->]|[-> ->]]];
        move/fdComposePN : (Hf2g2) => [-> ->];
        now move => // /= -> ->. 
    - move/fdComposePN : (Hf1g1) => [-> ->];
        move/fdComposeP : (Hf2g2) => [[vf2 [vg2 [<- [-> ->]]]]|[[-> ->]|[-> ->]]];
        now move => // /= -> ->. 
  Qed.
  
End CMRA.

Section RAMap.
  Context {I : Type} `{CI : comparable I}.
  Context {T U: Type} `{cmraT: CMRA T} `{cmraU: CMRA U}.

  Local Instance ra_force_pord_T: preoType (I -f> T) := pord_ra.
  Local Instance ra_force_pord_U: preoType (I -f> U) := pord_ra.

  Program Definition fdRAMap (f: T -m> U): (I -f> T) -m> (I -f> U) :=
    mkMUMorph (fdMap f) _.
  Next Obligation. (* If one day, this obligation disappears, then probably the instances are not working out anymore *)
    move=>x y EQxy. change (fdMap f x ⊑ fdMap f y).
    apply ra_pord_iff_ext_pord. apply ra_pord_iff_ext_pord in EQxy.
    by eapply mu_mono.
  Qed.

  Global Instance fdRAMap_resp: Proper (equiv ==> equiv) fdRAMap.
  Proof.
    move=>x y EQxy. change (fdMap x == fdMap y). by eapply fdMap_resp.
  Qed.
  Global Instance fdRAMap_nonexp n : Proper (dist n ==> dist n) fdRAMap.
  Proof.
    move=>x y EQxy. change (fdMap x = n = fdMap y). by eapply fdMap_nonexp.
  Qed.
  
End RAMap.

Section RAMapComp.
  Context {I : Type} `{CI : comparable I}.
  Context {T: Type} `{cmraT: CMRA T}.

  Lemma fdRAMap_id:
    fdRAMap (pid T) == pid (I -f> T).
  Proof.
    change (fdMap (pid T) == pid (I -f> T)).
    by eapply fdMap_id.
  Qed.

  Context {U: Type} `{cmraU: CMRA U}.
  Context {V: Type} `{cmraV: CMRA V}.

  Lemma fdRAMap_comp (f: T -m> U) (g: U -m> V):
    fdRAMap g ∘ fdRAMap f == fdRAMap (g ∘ f).
  Proof.
    change (fdMap g ∘ fdMap f == fdMap (g ∘ f)).
    by eapply fdMap_comp.
  Qed.

End RAMapComp.
