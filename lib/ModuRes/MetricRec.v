Require Import MetricCore.
Require Import Arith.

Module NatDec.
  Definition U := nat.
  Definition eq_dec := eq_nat_dec.
End NatDec.

Module D := Coq.Logic.Eqdep_dec.DecidableEqDep(NatDec).

(** A category enriched in complete bisected metric spaces and with a terminal object. *)

Class BC_morph T := tmorph : T -> T -> cmtyp.
Notation "u -t> v" := (tmorph u v) (at level 45, right associativity) : cat_scope.
Delimit Scope cat_scope with cat.
Open Scope cat_scope.
Class BC_term T := tto : T.
Class BC_terminal T {TA : BC_morph T} {TT : BC_term T} := tto_terminal t : t -t> tto.
Class BC_comp T {TA : BC_morph T} :=
  tcomp t0 t1 t2 : (t1 -t> t2) -n> (t0 -t> t1) -n> (t0 -t> t2).
Class BC_id T {TA : BC_morph T} := tid t : t -t> t.

Arguments tcomp {T TA BC_comp t0 t1 t2}.

Notation "f ∘ g" := (tcomp f g) (at level 40, left associativity) : cat_scope.
Notation "1" := tto : cat_scope.
Notation "! X" := (tto_terminal X) (at level 35) : cat_scope.

Class BaseCat T {TA : BC_morph T} {TO : BC_term T} {TT : BC_terminal T} {TC : BC_comp T} {TI : BC_id T} :=
  { tcomp_assoc {t0 t1 t2 t3} (f : t2 -t> t3) (g : t1 -t> t2) (h : t0 -t> t1) :
      f ∘ (g ∘ h) == (f ∘ g) ∘ h;
    tid_left  {t0 t1} (f : t0 -t> t1) : tid _ ∘ f == f;
    tid_right {t0 t1} (f : t0 -t> t1) : f ∘ tid _ == f;
    tto_term_unique : forall {t} (f g : t -t> 1), f == g}.

Section Definitions.
  Context {M} `{BaseCat M}.

  (** A functor F : Cᵒᵖ × C → C. Since the categories are enriched in metric
     spaces, the functor is also required to be enriched, meaning that the morphism
     part is actually a morphism of metric spaces, in this case meaning that it is
     a non-expansive function. *)
  Class BiFMap (F : M -> M -> M) :=
    fmorph : forall {m0 m1 m2 m3}, (m1 -t> m0) * (m2 -t> m3) -n> (F m0 m2 -t> F m1 m3).
  Class BiFunctor F {FM : BiFMap F} := mkFunctor
    { fmorph_comp : forall m0 m1 m2 m3 m4 m5 (f : m4 -t> m1) (g : m3 -t> m5) (h : m1 -t> m0) (k : m2 -t> m3),
        fmorph (f, g) ∘ fmorph (h, k) == fmorph (h ∘ f, g ∘ k);
      fmorph_id : forall m0 m1, fmorph (tid m0, tid m1) == tid _}.

  Definition retract {m0 m1} (f : m0 -t> m1) (g : m1 -t> m0) := g ∘ f == tid _.

  (** A Cauchy tower. See paper on M-categories for precise definition. *)
  Record Tower := mkTower
    { tow_objs : nat -> M;
      tow_morphs : forall i, tow_objs (S i) -t> tow_objs i;
      tow_morphsI : forall i, tow_objs i -t> tow_objs (S i);
      tow_retract : forall i, retract (tow_morphsI i) (tow_morphs i);
      tow_limitD : forall n i, n <= i -> tow_morphsI i ∘ tow_morphs i = n = tid _}.

  (** A cone to a Cauchy tower. *)
  Record Cone (T : Tower) := mkBaseCone
    { cone_t :> M;
      cone_m : forall i, cone_t -t> (tow_objs T i);
      cone_m_com : forall i, tow_morphs T i ∘ cone_m (S i) == cone_m i}.

  (** A cocone to a Cauchy tower. *)
  Record CoCone (T : Tower) := mkBaseCoCone
    { cocone_t :> M;
      cocone_m : forall i, tow_objs T i -t> cocone_t;
      cocone_m_com : forall i, cocone_m (S i) ∘ tow_morphsI T i == cocone_m i}.

  (** Limit of a Cauchy tower, i.e. a terminal cone in the category of cones to the chosen tower. *)
  Record Limit (T : Tower) := mkBaseLimit
    { lim_cone :> Cone T;
      lim_exists : forall C : Cone T, cone_t _ C -t> lim_cone;
      lim_com    : forall (C : Cone T) n, cone_m _ C n == cone_m _ lim_cone n ∘ lim_exists C;
      lim_unique : forall (C : Cone T) (h : cone_t _ C -t> lim_cone)
        (HEq : forall n, cone_m _ C n == cone_m _ lim_cone n ∘ h), h == lim_exists C}.

  (** A colimit of a Cauchy tower, i.e. an initial cocone in the category of cocones to the chosen tower. *)
  Record CoLimit (T : Tower) := mkBaseColimit
    { colim_cocone :> CoCone T;
      colim_exists : forall (C : CoCone T), cocone_t _ colim_cocone -t> C;
      colim_com    : forall (C : CoCone T) n, cocone_m _ C n == colim_exists C ∘ cocone_m _ colim_cocone n;
      colim_unique : forall (C : CoCone T) (h : cocone_t _ colim_cocone -t> C)
        (HEq : forall n, cocone_m _ C n == h ∘ cocone_m _ colim_cocone n), h == colim_exists C}.

End Definitions.

Module Type MCat.
  Parameter M : Type.
  Parameter MArr : BC_morph M.
  Parameter MTermO : BC_term M.
  Parameter MTermA : BC_terminal M.
  Parameter MComp  : BC_comp M.
  Parameter MId    : BC_id M.
  Parameter Cat : BaseCat M.

  (** An M-category in addition to being enriched in cbult and having a terminal
      object also has to have limits of all Cauchy towers. Hence the additional
      assumption for the following section. *)
  Parameter AllLimits : forall T : Tower, Limit T.
End MCat.

Module Type InputType(Cat : MCat).
  Import Cat.

  (** We assume we have a bifunctor and a map from the terminal object into
      F(1, 1) (1 being the terminal object). This is used to start the
      construction of the Cauchy tower. *)
  Parameter F : M -> M -> M.
  Parameter FArr : BiFMap F.
  Parameter FFun : BiFunctor F.
  Parameter tmorph_ne : 1 -t> (F 1 1).

  (** In addition, we assume the given functor is locally contractive. *)
  Parameter F_contractive : forall {m0 m1 m2 m3 : M}, contractive (@fmorph _ _ F _ m0 m1 m2 m3).
End InputType.

Module Type SolutionType(Cat : MCat)(M_cat : InputType(Cat)).
  Import Cat.
  Import M_cat.

  (** The solution of the recursive domain equation. We are not
      interested in the exact definitions of any of the following,
      hence defining them as opaque. *)
  Axiom DInfO : M.

  Axiom Fold : F DInfO DInfO -t> DInfO.
  Axiom Unfold : DInfO -t> (F DInfO DInfO).

  Axiom FU_id : Fold ∘ Unfold == tid DInfO.
  Axiom UF_id : Unfold ∘ Fold == tid (F DInfO DInfO).

  (** If [ı : DInf → F(DInf, DInf)] is the above isomorphism then
      [Δ = e ↦ ı ; F(e, e) ; ı⁻¹]. This function is contractive.
   *)
  Parameter (Δ : (DInfO -t> DInfO) -n> (DInfO -t> DInfO)).

  Axiom Δ_contra : contractive Δ.
End SolutionType.  
    
Module Solution(Cat : MCat)(M_cat : InputType(Cat)) : SolutionType(Cat)(M_cat).
  Import Cat.
  Import M_cat.

  Section RecursiveDomains.
    (** An image by a bifunctor of a retract pair is a retract pair, i.e. if f and g form a retract, meaning g ∘ f = id, then 
        F(f, g), F(g, f) also forms a retract pair. *)
    Lemma BiFuncRtoR {m0 m1} (f : m0 -t> m1) (g : m1 -t> m0) (HR : retract f g) :
      retract (fmorph (g, f)) (fmorph (f, g)).
    Proof.
      unfold retract in *; rewrite fmorph_comp, HR; apply fmorph_id.
    Qed.

    (** Iteration of a bifunctor starting from the terminal object. 
        F_0 = 1, F_{n+1} = F(F_n, F_n). This is used to construct the limiting cone. *)
    Fixpoint Diter n :=
      match n with
        | O => 1
        | S n => F (Diter n) (Diter n)
      end.

    (** Defining the injection projection pairs between F_n and F_{n+1} defined above. 
        f_0 = tmorph_ne, g_0 = unique map into 1, f_{n+1} = F(g_n, f_n) and g_{n+1} = F(f_n, g_n). *)
    Fixpoint Injection n : Diter n -t> Diter (S n) :=
      match n with
        | O => tmorph_ne
        | S n => fmorph (Projection n, Injection n)
      end
    with Projection n : Diter (S n) -t> Diter n :=
      match n with
        | O => ! _
        | S n => fmorph (Injection n, Projection n)
      end.

    (** All of the above defined at each stage define a retract pair. *)
    Lemma retract_IP : forall n, retract (Injection n) (Projection n).
    Proof.
      induction n; [apply tto_term_unique |].
      unfold retract in *; simpl; rewrite fmorph_comp, IHn; apply fmorph_id.
    Qed.
    
    (** Composing in the other direction, i.e. f_n ∘ g_n gives a decreasing
        sequence. This shows that for the maps defined above (f_n-s and g_n-s) the composition 
        f_n ∘ g_n forms a non-increasing sequence. *)
    Lemma IP_nonexp i j n (Hij : i <= j) (HReti : (Injection i ∘ Projection i) = n = tid _) :
      Injection j ∘ Projection j = n = tid _.
    Proof.
      induction Hij; [assumption | simpl].
      rewrite fmorph_comp, IHHij, fmorph_id; reflexivity.
    Qed.

    (** Using that additional assumption, we can show that the
        projection/injection pairs defined above form a Cauchy tower. *)
    Program Definition DTower : Tower := mkTower Diter Projection Injection _ _.
    Next Obligation. apply retract_IP. Qed.
    Next Obligation.
      revert i H; induction n; intros; [apply dist_bound |].
      destruct i; [inversion H | apply Le.le_S_n, IHn in H; clear IHn].
      simpl; rewrite fmorph_comp, <- fmorph_id; apply F_contractive.
      split; assumption.
    Qed.

    (** Now we use the assumption that the category in question has limits of
        all Cauchy towers, to get the proposed solution to our fixed point equation, DInf. *)
    Definition DInf := AllLimits DTower.

    (** Construction of various cones and cocones. The exact Cauchy tower is irrelevant, so it is a parameter. Later, DTower in the section will be instantiated by the above defined DTower. *)
    Section Tower.
      Variable DTower : Tower.

      (** This is just extending the projections and injections that work for
          one step, i.e. from n to n+1 or vice versa to more more steps. *)
      Fixpoint Projection_nm m n : tow_objs DTower (n + m) -t> tow_objs DTower m :=
        match n with
          | O => tid _
          | S n => Projection_nm m n ∘ tow_morphs DTower _
        end.

      Fixpoint Injection_nm m n : tow_objs DTower m -t> tow_objs DTower (n + m) :=
        match n with
          | O => tid _
          | S n => tow_morphsI DTower _ ∘ Injection_nm m n
        end.

      Definition DIter_coerce {n m} (EQ : n = m) : tow_objs DTower n -t> tow_objs DTower m.
      Proof. rewrite EQ; apply tid. Defined.

      Lemma lt_plus_minus {n m} (HLt : n < m) : m = m - n + n.
      Proof. omega. Qed.

      (** Using projections and injections we can go from object at n to object at m for any n, m. *)
      Definition t_nm n m : tow_objs DTower n -t> tow_objs DTower m :=
        match lt_eq_lt_dec n m with
          | inleft (left ee) => DIter_coerce (eq_sym (lt_plus_minus ee)) ∘ Injection_nm n (m - n)
          | inleft (right ee) => DIter_coerce ee
          | inright ee => Projection_nm m (n - m) ∘ DIter_coerce (lt_plus_minus ee)
        end.

      (** Coercions do not depend on the proofs of equality. *)
      Lemma DIter_coerce_simpl : forall n (Eq : n = n), DIter_coerce Eq = tid _.
      Proof.
        intros n EQ; unfold DIter_coerce, eq_rect_r; rewrite <- D.eq_rect_eq; auto.
      Qed.

      (** And is transitive. *)
      Lemma DIter_coerce_comp x y z (Eq1 : x = y) (Eq2 : y = z) :
        DIter_coerce Eq2 ∘ DIter_coerce Eq1 == DIter_coerce (trans_equal Eq1 Eq2).
      Proof.
        generalize Eq1; rewrite Eq1; clear x Eq1; intros Eq1.
        generalize Eq2; rewrite <- Eq2; clear z Eq2; intros Eq2.
        rewrite !DIter_coerce_simpl; apply tid_right.
      Qed.

      (** If n = m then the m'th component of the Cauchy tower is the same as if
          we compose the n'th with coercions. This really says that coercions are
          identities and that they are only needed to satisy the
          typechecker. Semantically, they are identites. *)
      Lemma tow_morphs_coerce m n (HEq : n = m) : tow_morphs DTower m ==
        DIter_coerce HEq ∘ tow_morphs DTower n ∘ DIter_coerce (eq_sym (eq_S _ _ HEq)).
      Proof. subst; rewrite !DIter_coerce_simpl, tid_right, tid_left; reflexivity. Qed.

      Lemma tow_morphsI_coerce m n (HEq : n = m) : tow_morphsI DTower m ==
        DIter_coerce (eq_S _ _ HEq) ∘ tow_morphsI DTower n ∘ DIter_coerce (eq_sym HEq).
      Proof. subst; rewrite !DIter_coerce_simpl, tid_left, tid_right; reflexivity. Qed.

      (** Projection (g) from m + (S k) to m is the same as the projection from
          S m + k to S k followed by another g, the element of Cauchy tower. Coerce
          is there to make the types work. *)
      Lemma Proj_left_comp : forall k m, Projection_nm m (S k) ==
        tow_morphs DTower m ∘ Projection_nm (S m) k ∘ DIter_coerce (plus_n_Sm _ _).
      Proof.
        induction k; intros; simpl in *.
        + rewrite DIter_coerce_simpl, tid_left, !tid_right; reflexivity.
        + rewrite IHk at 1. rewrite <- !tcomp_assoc. clear IHk.
          do 2 (apply equiv_morph; [reflexivity |]).
          rewrite (tow_morphs_coerce _ _ (plus_n_Sm _ _)).
          rewrite <- tcomp_assoc, DIter_coerce_comp.
          rewrite DIter_coerce_simpl, tid_right; reflexivity.
      Qed.

      (** The same as previous one, but for injections (i.e. f's). *)
      Lemma Inj_right_comp : forall k m, Injection_nm m (S k) ==
        DIter_coerce (sym_eq (plus_n_Sm k m)) ∘ Injection_nm (S m) k ∘ tow_morphsI DTower m.
      Proof.
        induction k; intros; simpl in *.
        + rewrite DIter_coerce_simpl, !tid_right, tid_left; reflexivity.
        + rewrite (IHk m), !tcomp_assoc; clear IHk.
          rewrite (tow_morphsI_coerce _ _ (plus_n_Sm _ _)).
          rewrite !tcomp_assoc, DIter_coerce_comp.
          rewrite DIter_coerce_simpl, tid_left; reflexivity.
      Qed.

      Lemma Injection_nm_coerce : forall m k n (HEq : k + n = m + n),
        Injection_nm n m == DIter_coerce HEq ∘ Injection_nm n k.
      Proof.
        induction m; intros.
        + destruct k; [| contradict HEq; omega]; simpl in *.
          rewrite DIter_coerce_simpl, tid_left; reflexivity.
        + destruct k; [contradict HEq; omega |].
          assert (HT : k + n = m + n) by omega.
          simpl; rewrite (IHm _ _ HT) at 1; clear IHm.
          rewrite !tcomp_assoc. apply equiv_morph; [| reflexivity].
          simpl in HEq; generalize HT HEq; rewrite HT; clear HEq HT; intros HEq HT.
          rewrite !DIter_coerce_simpl, tid_left, tid_right; reflexivity.
      Qed.

      Lemma Projection_nm_coerce : forall m k n (HEq : m + n = k + n),
        Projection_nm n m == Projection_nm n k ∘ DIter_coerce HEq.
      Proof.
        induction m; intros.
        + destruct k; [| contradict HEq; omega]; simpl in *.
          rewrite DIter_coerce_simpl, tid_left; reflexivity.
        + destruct k; [contradict HEq; omega |].
          assert (HT : m + n = k + n) by omega.
          simpl; rewrite (IHm _ _ HT) at 1; clear IHm.
          rewrite <- !tcomp_assoc. apply equiv_morph; [reflexivity |].
          simpl in HEq; generalize HT HEq; rewrite HT; clear HEq HT; intros HEq HT.
          rewrite !DIter_coerce_simpl, tid_left, tid_right; reflexivity.
      Qed.

      (** This lemma states that for each n, the morphisms t_nm n form a cone
          from F_n to {F_i}_'s together with g's. *)
      Lemma t_nmProjection n m : t_nm n m == tow_morphs DTower m ∘ t_nm n (S m).
      Proof.
        unfold t_nm; destruct (lt_eq_lt_dec n m) as [ [HLt | HEq] | HGt].
        + destruct (lt_eq_lt_dec n (S m)) as [ [HLtS | HC ] | HC]; try (contradict HC; omega).
          assert (HEq' : S (m - n) + n = S m - n + n) by omega.
          rewrite (Injection_nm_coerce _ _ _ HEq').
          simpl; rewrite !tcomp_assoc.
          apply equiv_morph; [| reflexivity].
          rewrite (tow_morphs_coerce _ _ (eq_sym (lt_plus_minus HLt))).
          do 2 rewrite <- tcomp_assoc with (f := DIter_coerce _ ∘ tow_morphs _ _).
          rewrite !DIter_coerce_comp.
          rewrite DIter_coerce_simpl, tid_right, <- tcomp_assoc, @tow_retract, tid_right; reflexivity.
        + destruct (lt_eq_lt_dec n (S m)) as [[HLtS | HC ] | HC]; try (contradict HC; omega).
          subst; assert (HEq : 1 + m = S m - m + m) by omega.
          rewrite (Injection_nm_coerce _ _ _ HEq); simpl.
          rewrite tid_right, (tcomp_assoc (DIter_coerce _)), DIter_coerce_comp.
          rewrite !DIter_coerce_simpl, tid_left, @tow_retract; reflexivity.
        + destruct (lt_eq_lt_dec n (S m)) as [[HC | HEq ] | HGtS]; try (contradict HC; omega).
          * subst; rewrite DIter_coerce_simpl, tid_right.
            assert (HEq : S m - m + m = 1 + m) by omega.
            rewrite (Projection_nm_coerce _ _ _ HEq); simpl.
            rewrite tid_left, <- tcomp_assoc, DIter_coerce_comp.
            rewrite DIter_coerce_simpl, tid_right; reflexivity.
          * assert (HEq : n - m + m = S (n - S m) + m) by omega.
            rewrite (Projection_nm_coerce _ _ _ HEq), Proj_left_comp, <- !tcomp_assoc.
            do 2 (apply equiv_morph; [reflexivity |]).
            rewrite !DIter_coerce_comp; remember (lt_plus_minus HGtS) as xx.
            rewrite (D.UIP _ _ _ xx); reflexivity.
      Qed.

      Lemma t_nn_ID: forall n, t_nm n n == tid _.
      Proof.
        intros n; unfold t_nm; destruct (lt_eq_lt_dec n n) as [[HC | HEq] | HC]; 
          (contradict HC; omega) || rewrite DIter_coerce_simpl; reflexivity.
      Qed.

      Lemma t_nmProjection2 n m (HLe : m <= n) : t_nm (S n) m == t_nm n m ∘ tow_morphs DTower n.
      Proof.
        remember (n - m) as k; revert n m HLe Heqk; induction k; intros.
        + assert (n = m) by omega; subst; simpl.
          rewrite t_nmProjection, !t_nn_ID, tid_left, tid_right; reflexivity.
        + destruct n; [discriminate |].
          rewrite (t_nmProjection (S (S n)) m), IHk, (t_nmProjection (S n) m); try omega.
          rewrite tcomp_assoc; reflexivity.
      Qed.

      (** This shows that for each m, λ k. t_nm k m form a cocone from F_i's with f's to F_m. *)
      Lemma t_nmEmbedding n m : t_nm n m == t_nm (S n) m ∘ tow_morphsI DTower n.
      Proof.
        unfold t_nm; destruct (lt_eq_lt_dec n m) as [[HLt | HEq] | HGt].
        + destruct (lt_eq_lt_dec (S n) m) as [[HLtS | HEq] | HC]; try (contradict HC; omega).
          * assert (HEq : S (m - S n) + n = m - n + n) by omega.
            rewrite (Injection_nm_coerce _ _ _ HEq), Inj_right_comp, !tcomp_assoc.
            do 2 rewrite <- tcomp_assoc with (g := (Injection_nm _ _)) (h := (tow_morphsI _ _)).
            apply equiv_morph; [| reflexivity].
            rewrite !DIter_coerce_comp; remember (Logic.eq_sym (lt_plus_minus HLtS)) as xx.
            rewrite (D.UIP _ _ _ xx); reflexivity.
          * subst; assert (HEq : 1 + n = S n - n + n) by omega.
            rewrite (Injection_nm_coerce _ _ _ HEq); simpl.
            rewrite tid_right, !tcomp_assoc; apply equiv_morph; [| reflexivity].
            rewrite DIter_coerce_comp, !DIter_coerce_simpl; reflexivity.
        + destruct (lt_eq_lt_dec (S n) m) as [[HC | HC] | HGtS]; try (contradict HC; omega).
          subst; rewrite DIter_coerce_simpl; assert (HEq : S m - m + m = 1 + m) by omega.
          rewrite (Projection_nm_coerce _ _ _ HEq); simpl.
          rewrite tid_left, <- (tcomp_assoc (tow_morphs _ _)), DIter_coerce_comp.
          rewrite DIter_coerce_simpl, tid_right, @tow_retract; reflexivity.
        + destruct (lt_eq_lt_dec (S n) m) as [[HC | HC] | HGtS]; try (contradict HC; omega).
          assert (HEq : S n - m + m = S (n - m) + m) by omega.
          rewrite (Projection_nm_coerce _ _ _ HEq), <- (tcomp_assoc (Projection_nm _ _)),
          DIter_coerce_comp; simpl.
          rewrite <- !tcomp_assoc; apply equiv_morph; [reflexivity |].
          rewrite (tow_morphs_coerce _ _ (lt_plus_minus HGt)), <- !tcomp_assoc.
          rewrite (tcomp_assoc _ _ (tow_morphsI _ _)), DIter_coerce_comp.
          rewrite DIter_coerce_simpl, tid_left, tow_retract, tid_right; reflexivity.
      Qed.

      Lemma t_nmEmbedding2 n m (HLe : n <= m) : t_nm n (S m) == tow_morphsI DTower m ∘ t_nm n m.
      Proof.
        remember (m - n) as k; revert n m HLe Heqk; induction k; intros.
        + assert (m = n) by omega; subst; rewrite t_nmEmbedding, !t_nn_ID, tid_right, tid_left; reflexivity.
        + destruct m; [discriminate |].
          rewrite (t_nmEmbedding n (S (S m))), IHk, (t_nmEmbedding n (S m)); try omega.
          rewrite tcomp_assoc; reflexivity.
      Qed.

      (** [coneN n] is a cone from F_n to the diagram {Fᵢ}ᵢ with g's (projections). *)
      Program Definition coneN n : Cone DTower := mkBaseCone _ (tow_objs DTower n) (t_nm n) _.
      Next Obligation. symmetry; apply t_nmProjection. Qed.

      Lemma coneCom_l (C : Cone DTower) n i (HLe : i <= n) : cone_m _ C i == t_nm n i ∘ cone_m _ C n.
      Proof.
        remember (n - i) as m; revert n i HLe Heqm; induction m; intros.
        + assert (n = i) by omega; subst; rewrite t_nn_ID, tid_left; reflexivity.
        + destruct n; [discriminate |]; rewrite t_nmProjection, <- tcomp_assoc, <- IHm; try omega.
          symmetry; apply cone_m_com.
      Qed.

      Lemma coconeCom_l (C : CoCone DTower) n i (HLe : n <= i) : cocone_m _ C n == cocone_m _ C i ∘ t_nm n i.
      Proof.
        remember (i - n) as m; revert n i HLe Heqm; induction m; intros.
        + assert (n = i) by omega; subst; rewrite t_nn_ID, tid_right; reflexivity.
        + destruct i; [discriminate |]; rewrite t_nmEmbedding, tcomp_assoc, <- IHm; try omega.
          symmetry; apply cocone_m_com.
      Qed.

      Lemma cone_coconeP (C : Cone DTower) (CC : CoCone DTower) n k (HLe : n <= k) :
        cocone_m _ CC n ∘ cone_m _ C n = n = cocone_m _ CC k ∘ cone_m _ C k.
      Proof.
        induction k; intros; inversion HLe; subst; [reflexivity | reflexivity |]; clear HLe.
        rewrite IHk; [| assumption]; clear IHk.
        rewrite <- cone_m_com, <- cocone_m_com, tcomp_assoc, <- (tcomp_assoc (cocone_m _ _ _)).
        rewrite tow_limitD, tid_right; [reflexivity | assumption].
      Qed.

      Arguments cone_t [_ _ _ _ _] _.
      Arguments lim_cone [_ _ _ _ _] _.
      Arguments cocone_t [_ _ _ _ _] _.
      Arguments colim_cocone [_ _ _ _ _] _.
      (** Given a Cauchy tower and a cone C ad a cocone CC to it we get a Cauchy chain of morphisms 
          from C to CC. This is used later to show the constructed limit is the solution. *)
      Definition chainPE (C : Cone DTower) (CC : CoCone DTower) : chain (cone_t C -t> cocone_t CC) :=
        fun n => cocone_m _ CC n ∘ cone_m _ C n.
      Lemma chainPE_cauchy (C : Cone DTower) (CC : CoCone DTower) : cchain (chainPE C CC).
      Proof.
        unfold cchain; intros.
        etransitivity; [| apply cone_coconeP; assumption].
        symmetry; apply cone_coconeP; assumption.
      Qed.

    End Tower.

    (** NOTE: DTower here is again the one defined by the iteration of a
              functor. In the section above it was a parameter with the same name. *)
    
    Definition α {T} := fun x => cone_t T (lim_cone _ x).
    Definition β {T} := fun x => cocone_t T (colim_cocone _ x).
    (** [coneN DTower n] defined above defines a cone from F_n to the tower (with projections). 
        Since DInf is defined as a limit, we get a morphism into it from F_n *)
    Definition Embeddings n : (tow_objs DTower n) -t> (α DInf) := lim_exists _ DInf (coneN DTower n).

    (** Projections from the proposed solution to F_n's. Since DInf is defined
        as the limit of DTower, this is just one of the accompanying projections. *) 
    Definition Projections n : α DInf -t> tow_objs DTower n := cone_m _ DInf n.

    Lemma coCom i : Embeddings (S i) ∘ Injection i == Embeddings i.
    Proof.
      unfold Embeddings; apply (lim_unique DTower (AllLimits DTower) (coneN DTower i)).
      intro n; simpl; rewrite tcomp_assoc, <- (lim_com _ (AllLimits DTower) (coneN DTower (S i))).
      simpl; rewrite t_nmEmbedding; reflexivity.
    Qed.

    (** The above defined embeddings also form a cocone to DInf *)
    Definition DCoCone : CoCone DTower := mkBaseCoCone _ (cone_t _ (AllLimits DTower)) Embeddings coCom.

    (** Embedding followed by a projection is always identity. This follows from
        the fact that we started with retractions in the Cauchy tower. *)
    Lemma retract_EP n : retract (Embeddings n) (Projections n).
    Proof.
      unfold retract, Projections, Embeddings.
      rewrite <- (lim_com _ (AllLimits DTower) (coneN DTower n) n); simpl; rewrite t_nn_ID; reflexivity.
    Qed.

    Lemma emp i j : Projections i ∘ Embeddings j == t_nm DTower j i.
    Proof.
      destruct (le_lt_dec i j) as [HLe | HLt].
      + unfold Projections; rewrite coneCom_l; [| eassumption].
        rewrite <- tcomp_assoc, retract_EP, tid_right; reflexivity.
      + assert (HT := coconeCom_l _ DCoCone); simpl in HT; rewrite (HT _ i); clear HT; [| omega].
        rewrite tcomp_assoc, retract_EP, tid_left; reflexivity.
    Qed.

    (** Given a cocone we get a Cauchy sequence of morphism from DInf to C. When
        instantiated with the cocone of embeddings (defined above) its limit will be
        the identity.  *)
    Local Instance chainPEc (C : CoCone DTower) : cchain (chainPE _ (AllLimits DTower) C) := chainPE_cauchy _ _ _.

    Lemma EP_id : compl (chainPE _ (AllLimits DTower) DCoCone) == tid _.
    Proof.
      assert (Z : forall n, cone_m _ (AllLimits DTower) n == cone_m _ (AllLimits DTower) n ∘ tid _)
        by (intros; rewrite tid_right; reflexivity); apply lim_unique in Z; rewrite Z; clear Z.
      apply (lim_unique _ (AllLimits DTower) (AllLimits DTower)); intros n.
      rewrite nonexp_continuous, (cut_complete_eq _ n); simpl.
      etransitivity; [symmetry; apply umet_complete_const |]; apply umet_complete_ext; intros i.
      simpl; change (cone_m DTower (AllLimits DTower) n == cone_m DTower (AllLimits DTower) n ∘
        (Embeddings (n + i) ∘ cone_m DTower (AllLimits DTower) (n + i))); rewrite tcomp_assoc.
      rewrite emp, coneCom_l; [reflexivity | omega].
    Qed.

    (** Showing that DInf is also a colimit. The unique morphism from it to other cocones is given by limits
        of chainPEc's defined above. *)
    Program Definition DCoLimit : CoLimit DTower := mkBaseColimit _ DCoCone (fun C => compl (chainPE _ (AllLimits DTower) C)) _ _.
    Next Obligation.
      rewrite (cut_complete_eq _ n), <- dist_refl; intros m.
      destruct (conv_cauchy (cutn (chainPE _ (AllLimits DTower) C) n) m) as [k Hk].
      specialize (Hk _ (le_n _)).
      assert (HT : forall m, Proper (dist m ==> dist m) (fun x : α DInf -t> cocone_t _ C => x ∘ Embeddings n))
        by (intros t e e' R; rewrite R; reflexivity).
      apply HT in Hk; clear HT. rewrite Hk; simpl morph.
      unfold cutn, chainPE.
      rewrite <- tcomp_assoc, emp.
      clear Hk; revert m; rewrite dist_refl, coconeCom_l; [reflexivity | omega].
    Qed.
    Next Obligation.
      rewrite <- (tid_right h), <- EP_id, nonexp_continuous; apply umet_complete_ext; intros i; simpl.
      unfold liftc, chainPE. rewrite tcomp_assoc, <- HEq; reflexivity.
    Qed.

    (** To show that DInf is a fixed point we define a cone and acocone to
        F(DInf, DInf) to later show that they are limits, therefore isomorphic to DInf. *)
    Program Definition ECoCone : CoCone DTower :=
      mkBaseCoCone _ (F (α DInf) (α DInf)) (fun i => fmorph (Projections i, Embeddings i) ∘ Injection i) _.
    Next Obligation.
      rewrite fmorph_comp, (cone_m_com _ (AllLimits DTower) i), (cocone_m_com _ DCoCone i); reflexivity.
    Qed.

    Program Definition FCone : Cone DTower :=
      mkBaseCone _ (F (α DInf) (α DInf)) (fun n => Projection n ∘ fmorph (Embeddings n, Projections n)) _.
    Next Obligation.
      apply equiv_morph; [reflexivity |].
      rewrite fmorph_comp, coCom, (cone_m_com _ (AllLimits DTower) i); reflexivity.
    Qed.

    (** Similar to chainPE, but this time a Cauchy chain from F(DInf, DInf). *)
    Local Instance chainFPE_c (C : CoCone DTower) : cchain (chainPE _ FCone C) := chainPE_cauchy _ _ _.

    (** F maps t_nm to t_(S n)(S m). Direct consequence of the way DTower is defined. *)
    Lemma morph_tnm n m : fmorph (t_nm DTower m n, t_nm DTower n m) == t_nm DTower (S n) (S m).
    Proof.
      destruct (le_lt_dec n m) as [HLe | HLt].
      + remember (m - n) as k; revert n m HLe Heqk; induction k; intros.
        * assert (m = n) by omega; subst; rewrite !t_nn_ID, fmorph_id; reflexivity.
        * destruct m; [discriminate |].
          rewrite t_nmProjection2, t_nmEmbedding2, <- fmorph_comp, IHk; try omega.
          rewrite (t_nmEmbedding2 _ _ (S m)); simpl; [reflexivity | omega].
      + assert (HLe : m <= n) by omega; clear HLt.
        remember (n - m) as k; revert n m HLe Heqk; induction k; intros.
        * assert (m = n) by omega; subst; rewrite !t_nn_ID, fmorph_id; reflexivity.
        * destruct n; [discriminate |].
          rewrite t_nmProjection2, t_nmEmbedding2, <- fmorph_comp, IHk; try omega.
          rewrite (t_nmProjection2 _ (S n)); [reflexivity | omega].
    Qed.

    (** The next two lemmas show that F(DInf, DInf) is in fact a colimit of the same diagram as DInf. *)
    Lemma EColCom (C : CoCone DTower) n :
      cocone_m _ C n == compl (chainPE _ FCone C) ∘ cocone_m _ ECoCone n.
    Proof.
      simpl morph; rewrite (cut_complete_eq _ n), <- dist_refl; intros m.
      destruct (conv_cauchy (cutn (chainPE _ FCone C) n) m) as [k Hk]; specialize (Hk _ (le_n _)).
      rewrite Hk; simpl morph; clear Hk; revert m; rewrite dist_refl.
      unfold chainPE, cutn; rewrite <- tcomp_assoc, coconeCom_l; [apply equiv_morph; [reflexivity |] | omega].
      rewrite t_nmProjection, t_nmEmbedding, <- morph_tnm; simpl.
      rewrite <- !tcomp_assoc; apply equiv_morph; [reflexivity |].
      rewrite tcomp_assoc, fmorph_comp, !emp; reflexivity.
    Qed.

    Lemma CoLimitUnique (C : CoCone DTower) (h : cocone_t _ ECoCone -t> cocone_t _ C)
      (HEq : forall n, cocone_m _ C n == h ∘ cocone_m _ ECoCone n) :
      h == compl (chainPE _ FCone C).
    Proof.
      transitivity (h ∘ fmorph (compl (chainPE _ (AllLimits DTower) DCoCone), compl (chainPE _ (AllLimits DTower) DCoCone)));
        [rewrite !EP_id, fmorph_id, tid_right; reflexivity |].
      rewrite <- pair_limit, (nonexp_continuous fmorph).
      rewrite nonexp_continuous, (cut_complete_eq (chainPE _ FCone C) 1). apply umet_complete_ext; intros i.
      unfold liftc, chain_pair, chainPE, cutn; simpl.
      rewrite fmorph_comp, coCom, (cone_m_com _ (AllLimits DTower) i); simpl in *.
      specialize (HEq (S i)); simpl in HEq; rewrite fmorph_comp, coCom, (cone_m_com _ (AllLimits DTower) i) in HEq.
      rewrite HEq, <- tcomp_assoc, fmorph_comp; reflexivity.
    Qed.

    Definition ECoLimit := mkBaseColimit _ ECoCone (fun C => compl (chainPE _ FCone C)) EColCom CoLimitUnique.

    Definition DInfO : M := α DInf.

    (** Since DInf and F(DInf, DInf) are colimits of the same cocone, we have functions back and forth.
        The next two lemmas then state that they are inverses of each other. This is a general categorical fact. *)
    Definition Fold : F (α DInf) (α DInf) -t> α DInf := colim_exists _ ECoLimit DCoCone.
    Definition Unfold : α DInf -t> F (α DInf) (α DInf) := colim_exists _ DCoLimit ECoCone.

    Lemma FU_id : Fold ∘ Unfold == tid _.
    Proof.
      transitivity (colim_exists _ DCoLimit DCoLimit).
      + apply (colim_unique _ DCoLimit DCoCone); intros n; unfold Fold, Unfold; simpl.
        rewrite (nonexp_cont2 _ _ _).
        rewrite (umet_complete_ext _ (chainPE _ (AllLimits DTower) DCoCone)), EP_id, tid_left; [reflexivity | intros i; simpl].
        unfold binaryLimit, chainPE; simpl.
        rewrite !tcomp_assoc, <- (tcomp_assoc (Embeddings i ∘ Projection i)).
        simpl; rewrite fmorph_comp.
        rewrite !retract_EP, fmorph_id, tid_right, <- (tcomp_assoc (Embeddings i)).
        rewrite retract_IP, tid_right; reflexivity.
      + symmetry; apply (colim_unique _ DCoLimit DCoLimit); intros n; rewrite tid_left; reflexivity.
    Qed.

    Local Instance cced : cchain (chainPE _ FCone DCoCone).
    Proof.
      unfold cchain, chainPE; intros.
        etransitivity; [symmetry; apply (cone_coconeP _ FCone DCoCone); assumption
                       | apply (cone_coconeP _ FCone DCoCone); assumption ].
    Qed.

    Lemma UF_id : Unfold ∘ Fold == tid _.
      transitivity (colim_exists _ ECoLimit ECoLimit).
      + apply (colim_unique _ ECoLimit ECoLimit); intros n; unfold Fold, Unfold; simpl.
        rewrite (nonexp_cont2 _ _ _).
        etransitivity; [symmetry; apply tid_left |].
        apply (morph_resp tcomp); unfold equiv; symmetry.
        rewrite <- fmorph_id, <- !EP_id, <- pair_limit, nonexp_continuous.
        rewrite (cut_complete_eq _ 1); apply umet_complete_ext; intros i; simpl.
        unfold chainPE, liftc, cutn, chain_pair, binaryLimit; simpl.
        replace (cone_m _ (AllLimits DTower) (S i)) with (Projections (S i)) by reflexivity.
        replace (cone_m _ (AllLimits DTower) i) with (Projections i) by reflexivity.
        rewrite !fmorph_comp, !coCom. rewrite !(cone_m_com _ (AllLimits DTower) i).
        rewrite <- tcomp_assoc, (tcomp_assoc (Projections (S i))).
        rewrite (retract_EP (S i)), tid_left, fmorph_comp; reflexivity.
      + symmetry; apply (colim_unique _ ECoLimit ECoLimit); intros n; rewrite tid_left; reflexivity.
    Qed.

    Local Obligation Tactic := intros; resp_set.

    (** If i : DInf → F(DInf, DInf) is the above isomorphism then Δ = e ↦ i ; F(e, e) ; i⁻¹.
        This function is contractive. This is called ▷ in 𝓢 example or the iCAP model, but that's not a valid token in Coq.  *)
    Program Definition Δ : (α DInf -t> α DInf) -n> (α DInf -t> α DInf) :=
      n[(fun e => Fold ∘ fmorph (e, e) ∘ Unfold)].

    Instance Δ_contra : contractive Δ.
    Proof.
      intros n f g HEq; simpl; rewrite F_contractive; [reflexivity |].
      rewrite HEq; reflexivity.
    Qed.

    (** The fixed point of Δ starting from identity is an identity. This is "minimal invariance" like statement. *)
    Lemma id_min : fixp Δ (tid _) == tid _.
    Proof.
      rewrite <- dist_refl; induction n; [apply dist_bound |].
      rewrite fixp_eq.
      (* Contractiveness does not expose its "Proper" bit, so can't rewrite directly. *)
      etransitivity; [apply Δ_contra, IHn |]; clear IHn.
      generalize (S n) as k; clear n; rewrite dist_refl.
      simpl; rewrite fmorph_id, tid_right.
      apply FU_id.
    Qed.

  End RecursiveDomains.

End Solution.

(* TODO, uniqueness of the solution. I.e., showing that it's a bifree algebra. *)
