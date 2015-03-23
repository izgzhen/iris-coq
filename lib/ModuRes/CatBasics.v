(** This module provides the basics to do category theory on metric spaces:
    Bundled types, indexed products on bundled types, and some functors. *)

Require Import ssreflect.
Require Import Arith Min Max.
Require Import MetricCore PreoMet.
Require Fin.

Module NatDec.
  Definition U := nat.
  Definition eq_dec := eq_nat_dec.
End NatDec.

Module D := Coq.Logic.Eqdep_dec.DecidableEqDep(NatDec).

(** This packs together all the
    ingredients of [type], i.e. the carrier set, the relation and the
    property that the relation is an equivalence relation. *)
Record eqType :=
  {eqtyp  :> Type;
   eqtype :  Setoid eqtyp}.
Instance eqType_proj_type {ET : eqType} : Setoid ET := eqtype _.
Definition fromType T `{eT : Setoid T} : eqType := Build_eqType T _.

Section IndexedProductsSetoid.
  Context {I : Type} {P : I -> eqType}.

  (** Equality on the indexed product. Essentially the same as for binary products, i.e. pointwise. *)
  Global Program Instance prodI_type : Setoid (forall i, P i) :=
    mkType (fun p1 p2 => forall i, p1 i == p2 i).
  Next Obligation.
    split.
    - intros X x; reflexivity.
    - intros X Y HS x; symmetry; apply HS.
    - intros X Y Z HPQ HQR x; etransitivity; [apply HPQ | apply HQR].
  Qed.

  Local Obligation Tactic := intros; resp_set || program_simpl.

  (** Projection functions. *)
  Program Definition mprojI (i : I) : (forall i, P i) -=> P i :=
    s[(fun X => X i)].

  Context {T: Type} `{eT : Setoid T}.

  (** Tupling into the indexed products. *)
  Program Definition mprodI (f : forall i, T -=> P i) : T -=> (forall i, P i) :=
    s[(fun t i => f i t)].

  Lemma mprod_projI (f : forall i, T -=> P i) i : mprojI i << mprodI f == f i.
  Proof. intros X; reflexivity. Qed.

  (** Product with the projections is an actual product. *)
  Lemma mprodI_unique (f : forall i, T -=> P i) (h : T -=> forall i, P i) :
    (forall i, mprojI i << h == f i) -> h == mprodI f.
  Proof.
    intros HEq x i; simpl; rewrite <- HEq; reflexivity.
  Qed.

End IndexedProductsSetoid.

Record Mtyp :=
  { mtyp  :> eqType;
    mmetr : metric mtyp}.
Instance mtyp_proj_metr {M : Mtyp} : metric M := mmetr M.
Definition mfromType (T : Type) `{mT : metric T} := Build_Mtyp (fromType T) _.

Record cmtyp :=
  { cmm  :> Mtyp;
    iscm :  cmetric cmm}.
Instance cmtyp_cmetric {M : cmtyp} : cmetric M | 0 := iscm M.
Definition cmfromType (T : Type) `{cT : cmetric T} := Build_cmtyp (mfromType T) _.


(** Indexed product, very similar to binary product. The metric is pointwise, the supremum. *)
Section MetricIndexed.
  Context {I : Type} {P : I -> Mtyp}.

  Local Obligation Tactic := intros; apply _ || resp_set || program_simpl.

  Definition distI n (a b : forall i, P i) := forall i, mprojI i a = n = mprojI i b.
  Global Arguments distI n a b /.

  Global Program Instance prodI_metr : metric (forall i, P i) :=
    mkMetr distI.
  Next Obligation.
    intros x y EQxy u v EQuv; split; intros EQ i; [symmetry in EQxy, EQuv |]; rewrite-> (EQxy i), (EQuv i); apply EQ.
  Qed.
  Next Obligation.
    split; intros HEq n.
    + rewrite <- dist_refl; intros m; apply (HEq m).
    + intros i; revert n; rewrite dist_refl; apply HEq.
  Qed.
  (*Next Obligation.
    intros x y HS i; symmetry; apply HS.
  Qed.*)
  Next Obligation.
    intros x y z Hxy Hyz i; etransitivity; [apply Hxy | apply Hyz].
  Qed.
  Next Obligation.
    eapply mono_dist, H; auto.
  Qed.
  Next Obligation.
    apply dist_bound.
  Qed.

  Program Definition MprojI (i : I) : (forall i, P i) -n> P i :=
    n[(mprojI i)].

  Context {T: Type} `{mT : metric T}.
  Program Definition MprodI (f : forall i, T -n> P i) : T -n> forall i, P i :=
    n[(mprodI f)].

  Lemma MprodI_proj f i : MprojI i <M< MprodI f == f i.
  Proof. intros x; reflexivity. Qed.

  Lemma MprodI_unique f g (HEq : forall i, MprojI i <M< g == f i) : g == MprodI f.
  Proof. apply (mprodI_unique f g HEq). Qed.

End MetricIndexed.

(** Indexed product of complete spaces is again a complete space. *)
Section CompleteIndexed.
  Context {I : Type} {P : I -> cmtyp}.

  Definition prodI_compl (σ : chain (forall i, P i)) (σc : cchain σ) (i : I) :=
    compl (liftc (MprojI i) σ).
  Arguments prodI_compl σ σc i /.
  Global Program Instance prodI_cmetric : cmetric (forall i, P i) :=
    mkCMetr prodI_compl.
  Next Obligation.
    intros n; exists n; intros m HLe i.
    destruct (conv_cauchy (liftc (MprojI i) σ) n) as [k Hk]; simpl in *.
    rewrite -> Hk; [| apply le_max_r]; clear Hk.
    unfold liftc; apply σc; eauto using le_trans, le_max_l.
  Qed.

End CompleteIndexed.

Section Chains_of_IProds.
  Context {I : Type} {P : I -> cmtyp} (σ : chain (forall i, P i)) {σc : cchain σ}.

  Global Instance dep_chain_app (x : I) : cchain (fun n => σ n x).
  Proof.
    unfold cchain; intros; apply σc; assumption.
  Qed.

  Lemma dep_chain_compl (x : I) :
    compl σ x == compl (fun n => σ n x).
  Proof.
    apply umet_complete_ext; intros n; reflexivity.
  Qed.

End Chains_of_IProds.

Record preotyp :=
  {ptyp   :> eqType;
   pprTyp :  preoType ptyp}.
Instance preotyp_pTyp {T : preotyp} : preoType T := pprTyp T.

Section IndexedProductsPreo.
  Local Open Scope predom_scope.
  Context {I : Type} {P : I -> preotyp}.

  Definition ordI (f1 f2 : forall i, P i) := forall i, f1 i ⊑ f2 i.

  Global Program Instance ordTypeI : preoType (forall i, P i) := mkPOType ordI _.
  Next Obligation.
    split.
    + intros f i; reflexivity.
    + intros f g h Hfg Hgh i; etransitivity; [apply Hfg | apply Hgh].
  Qed.
  Next Obligation.
    move=> f1 f2 EQf g1 g2 EQg LE i.
    by rewrite -(EQf i) -(EQg i).
  Qed.
    
  Program Definition ordProjI (i : I) : (forall i, P i) -m> P i :=
    mkMMorph (mprojI i) _.
  Next Obligation. intros x y HSub; apply HSub. Qed.

  Context {T: Type} `{pT : preoType T}.
  Program Definition ordProdI (f : forall i, T -m> P i) : T -m> forall i, P i :=
    mkMMorph (mprodI f) _.
  Next Obligation. intros x y HSub i; simpl; apply f; assumption. Qed.

  Lemma ordProdI_proj f i : ordProjI i ∘ ordProdI f ⊑ f i.
  Proof. intros x; reflexivity. Qed.
  Lemma ordProdI_proj_rev f i : f i ⊑ ordProjI i ∘ ordProdI f.
  Proof. intros x; reflexivity. Qed.

  Lemma ordProdI_unique f g (HEq : forall i, ordProjI i ∘ g ⊑ f i) : g ⊑ ordProdI f.
  Proof. intros x i; apply (HEq i x). Qed.

  Lemma ordProdI_unique_rev f g (HEq : forall i, f i ⊑ ordProjI i ∘ g) : ordProdI f ⊑ g.
  Proof. intros x i; apply (HEq i x). Qed.

End IndexedProductsPreo.

Global Arguments ordI {_ _} _ _ /.


Record pcmtyp :=
  { pcmt_cmt :> cmtyp;
    pcmt_PO  :  preoType pcmt_cmt;
    pcmt_T   :  pcmType pcmt_cmt}.

Instance proj_preoType {U : pcmtyp} : preoType U := pcmt_PO U.
Instance proj_pcmType  {U : pcmtyp} : pcmType U := pcmt_T U.
Definition pcmFromType (T : Type) `{pcmT : pcmType T} := Build_pcmtyp (cmfromType T) _ _.

Section IndexedProductsPCM.
  Context {I : Type} {P : I -> pcmtyp}.
  Local Obligation Tactic := intros; apply _ || mono_resp || program_simpl.

  (* We have to repeat those due to coercions not going into preotyp *)
  Definition pcOrdI (f1 f2 : forall i, P i) := forall i, f1 i ⊑ f2 i.

  Global Program Instance pcOrdTypeI : preoType (forall i, P i) :=
    mkPOType pcOrdI _.
  Next Obligation.
    split.
    + intros f i; reflexivity.
    + intros f g h Hfg Hgh i; etransitivity; [apply Hfg | apply Hgh].
  Qed.
  Next Obligation.
    move=> f1 f2 Rf g1 g2 Rg H i.
    rewrite -(Rf i) -(Rg i); exact: H.
  Qed.

  Global Instance pcmTypI : pcmType (forall i, P i).
  Proof.
    split.
    + intros σ ρ σc ρc SUBc i; eapply pcm_respC; [apply _ | intros n; simpl; apply SUBc].
  Qed.

  Program Definition pcmProjI (i : I) : (forall i, P i) -m> P i :=
    m[(MprojI _)].
  Next Obligation. intros x y HSub; apply HSub. Qed.

  Context {A} `{mA : pcmType A}.
  Program Definition pcmProdI (f : forall i, A -m> P i) : A -m> forall i, P i :=
    m[(MprodI f)].

  Lemma pcmProdI_proj f i : pcmProjI i ∘ pcmProdI f == f i.
  Proof. intros x; reflexivity. Qed.

  Lemma pcmProdI_unique f g (HEq : forall i, pcmProjI i ∘ g == f i) : g == pcmProdI f.
  Proof. apply (mprodI_unique f g HEq). Qed.

End IndexedProductsPCM.


Section Halving.
  Definition halveT (T: eqType): eqType := fromType (halve T).
  Definition halvedT {T}: eqtyp T -> eqtyp (halveT T) := fun h => halved h.
  Definition unhalvedT {T}: eqtyp (halveT T) -> eqtyp T := fun h => unhalved h.

  Definition halveM (T: Mtyp) : Mtyp := Build_Mtyp (halveT T) halve_metr.
  Definition halveCM (T: cmtyp): cmtyp := Build_cmtyp (halveM T) halve_cm.
End Halving.
Ltac unhalveT := repeat (unhalve || match goal with
                       | x: eqtyp (mtyp (cmm (halveCM _))) |- _ => destruct x as [x]
                       end).


(** Trivial extension of a nonexpansive morphism to monotone one on a
    metric space equipped with a trivial preorder. *)
Section DiscM_Defs.
  Context {U V} `{cmU : cmetric U} `{cmV : cmetric V}.

  Local Instance pt_disc P `{cmetric P} : preoType P | 2000 := disc_preo P.
  Local Instance pcm_disc P `{cmetric P} : pcmType P | 2000 := disc_pcm P.

  Definition disc_m (m : V -n> U) : V -m> U := m[(m)].

End DiscM_Defs.

Section DiscM_Props.
  Context U V W `{cmU : cmetric U} `{cmV : cmetric V} `{cmW : cmetric W}.

  Global Instance disc_equiv : Proper (equiv (A := U -n> V) ==> equiv) disc_m.
  Proof. resp_set. Qed.
  Global Instance disc_dist n : Proper (dist (T := U -n> V) n ==> dist n) disc_m.
  Proof. resp_set. Qed.

  Lemma disc_m_comp (f : V -n> W) (g : U -n> V) :
    disc_m (f <M< g) == disc_m f ∘ disc_m g.
  Proof. intros x; simpl morph; reflexivity. Qed.

  Lemma disc_m_id : disc_m (umid W) == pid W.
  Proof. intros x; simpl morph; reflexivity. Qed.

End DiscM_Props.

(* TODO RJ: What is this? Why is it here? Why am *I* here?
Section EvaluationClosure.
  Context {T} `{preoT : preoType T} (step : T -> T -> Prop).
  Definition irr t := forall t', ~ step t t'.

  Definition ext_step :=
    forall t1 t2 t2' (HSub : t1 ⊑ t2) (HStep : step t2 t2'),
    exists t1', step t1 t1' /\ t1' ⊑ t2'.
  Context (HES : ext_step) (HEI : Proper (pord --> impl) irr).

  Section Def.
    Variable (R : UPred T).

    Fixpoint pre_evalCl n t : Prop :=
      (irr t -> R n t) /\
      forall t' (HS : step t t'),
        match n with
          | O => True
          | S n => pre_evalCl n t'
        end.
    Program Definition evalCl := mkUPred pre_evalCl _.
    Next Obligation.
      intros m n t t' HLe HSubt HEv.
      revert m t t' HLe HSubt HEv; induction n; intros.
      - simpl; split; [| tauto].
        rewrite <- HSubt, HLe; destruct m; apply HEv.
      - destruct m as [| m]; [now inversion HLe |]; simpl; split; [| intros].
        rewrite <- HSubt, HLe; apply HEv.
        destruct (HES _ _ _ HSubt HS) as [t1 [HS' HSub]].
        simpl in HEv; apply proj2 in HEv.
        eapply IHn, HEv; eassumption || auto with arith.
    Qed.
    Lemma evalCl_simpl n t :
      evalCl n t == ((irr t -> R n t) /\ forall t' (HS : step t t'), (▹ evalCl)%up n t').
    Proof. destruct n; reflexivity. Qed.
    Opaque evalCl.

  End Def.

  Global Instance eval_equiv : Proper (equiv ==> equiv) evalCl.
  Proof.
    apply equiv_upred_simpl; [apply _ |]; intros R1 R2 n t EQR HEv; revert t HEv; induction n; intros.
    - rewrite -> evalCl_simpl in *; simpl; split; [| tauto]; destruct HEv as [HIrr _].
      rewrite <- EQR; assumption.
    - rewrite -> evalCl_simpl in HEv; destruct HEv as [HIrr HEv].
      rewrite evalCl_simpl; split; [rewrite <- EQR; assumption | intros].
      apply IHn, HEv, HS.
  Qed.

  Global Instance eval_dist n : Proper (dist n ==> dist n) evalCl.
  Proof.
    apply dist_upred_simpl; [apply _ |]; intros R1 R2 m t HLt EQR HEv;
    revert t HEv; induction m; intros.
    - rewrite -> evalCl_simpl in *; destruct HEv as [HIrr _]; simpl; split; [| tauto].
      intros HIrred; apply EQR, HIrr, HIrred; assumption.
    - rewrite -> evalCl_simpl in HEv; rewrite evalCl_simpl.
      split; [| intros; apply IHm, HEv, HS; now auto with arith].
      intros HIrr; apply EQR, HEv, HIrr; assumption.
  Qed.

  Global Instance eval_pord : Proper (pord ==> pord) evalCl.
  Proof.
    intros R1 R2 HSub n; induction n; intros t HEv.
    - rewrite -> evalCl_simpl in *; split; [rewrite <- HSub; apply HEv | simpl; tauto].
    - rewrite -> evalCl_simpl in *; split; [rewrite <- HSub; apply HEv |].
      intros; apply IHn, HEv, HS; now auto with arith.
  Qed.

  Definition rel_evalCl : UPred T -m> UPred T := m[(evalCl)].

End EvaluationClosure.
*)

Definition transfer {A} {T : A -> Type} {x y : A} (EQ : x = y) (t : T x) : T y :=
  eq_rect x T t y EQ.

Definition transfer_nat_eq {T : nat -> Type} (x : nat) (EQ : x = x) (t : T x) :
  transfer EQ t = t.
Proof.
  symmetry; apply D.eq_rect_eq.
Qed.

Section FiniteProducts.
  Context {T : cmtyp}.

  Definition FinI n := forall i : Fin.t n, T.

  (* Type context extension *)
  Definition extFinI {n} (RC : FinI n) (R : T) : FinI (S n) :=
    fun i =>  match i in Fin.t k return (match k with
                                             O => False
                                           | S m => FinI m -> T end) with
                | Fin.F1 n => fun _ => R
                | Fin.FS n i => fun RC => RC i
              end RC.

  Global Instance extFinI_equiv n : Proper (equiv ==> equiv ==> equiv) (@extFinI n).
  Proof.
    intros RC1 RC2 EQRC R1 R2 EQR i.
    refine (match i as i in Fin.t k return match k return Fin.t k -> Prop with
                                               O => fun _ => False
                                             | S m => fun i => forall (RC1 RC2 : FinI m),
                                                                 RC1 == RC2 ->
                                                                 extFinI RC1 R1 i == extFinI RC2 R2 i
                                           end i with
                Fin.F1 n => fun _ _ _ => EQR
              | Fin.FS n i => fun RC1 RC2 EQRC => EQRC i
            end RC1 RC2 EQRC).
  Qed.

  Global Instance extTC_dist n k : Proper (dist k ==> dist k ==> dist k) (@extFinI n).
  Proof.
    intros RC1 RC2 EQRC R1 R2 EQR i.
    refine (match i as i in Fin.t m return match m return Fin.t m -> Prop with
                                               O => fun _ => False
                                             | S m => fun i => forall (RC1 RC2 : FinI m),
                                                               RC1 = k = RC2 ->
                                                               extFinI RC1 R1 i = k = extFinI RC2 R2 i
                                           end i with
                Fin.F1 n => fun _ _ _ => EQR
              | Fin.FS n i => fun RC1 RC2 EQRC => EQRC i
            end RC1 RC2 EQRC).
  Qed.

  Fixpoint fin_sum_split {k n} (x : Fin.t (k + n)) : Fin.t k + Fin.t n :=
    match k return Fin.t (k + n) -> Fin.t k + Fin.t n with
      | 0 => fun x => inr x
      | S k => fun x =>
                 match x in Fin.t m return m = S k + n -> Fin.t (S k) + Fin.t n with
                   | Fin.F1 _ => fun _ => inl Fin.F1
                   | Fin.FS m x' => fun EQ =>
                                      match fin_sum_split (transfer (eq_add_S _ _ EQ) x') with
                                        | inl y => inl (Fin.FS y)
                                        | inr y => inr y
                                      end
                 end eq_refl
    end x.

  Definition extFinEnv {k n} (η : FinI k) (ρ : FinI n) : FinI (n + k) :=
    fun x => match fin_sum_split x with
               | inl y => ρ y
               | inr y => η y
             end.

  Global Instance extFinEnv_equiv k n :
    Proper (equiv ==> equiv ==> equiv) (@extFinEnv k n).
  Proof.
    intros η1 η2 EQη ρ1 ρ2 EQρ x; unfold extFinEnv.
    destruct (fin_sum_split x) as [y | y]; [apply EQρ | apply EQη].
  Qed.

  Global Instance extFinEnv_dist k m n :
    Proper (dist n ==> dist n ==> dist n) (@extFinEnv k m).
  Proof.
    intros η1 η2 EQη ρ1 ρ2 EQρ x; simpl; unfold extFinEnv.
    destruct (fin_sum_split x) as [y | y]; [apply EQρ | apply EQη].
  Qed.

  Definition empFinI : FinI 0 :=
    fun x => match x in Fin.t k return match k with
                                         | O => T
                                         | S n => True
                                       end with
               | Fin.F1 _ => I
               | Fin.FS _ _ => I
             end.

  Lemma FinI_invert_O (ρ : FinI 0) :
    ρ == empFinI.
  Proof.
    intros x; inversion x.
  Qed.

  Lemma extFinEnv_empR k (η : FinI k) : extFinEnv η empFinI == η.
  Proof.
    reflexivity.
  Qed.

  Definition FinI_tail {k} (ρ : FinI (S k)) : FinI k :=
    fun x => ρ (Fin.FS x).

  Lemma FinI_invert_S {k} (ρ : FinI (S k)) :
    ρ == extFinI (FinI_tail ρ) (ρ Fin.F1).
  Proof.
    intros x.
    refine (match x as x in Fin.t m return
                  match m return Fin.t m -> Prop with
                    | O => fun _ => False
                    | S n => fun x => forall (ρ : FinI (S n)),
                                      ρ x == extFinI (FinI_tail ρ) (ρ Fin.F1) x
                  end x with
              | Fin.F1 m => _
              | Fin.FS m y => _
            end ρ); intros.
    - simpl; reflexivity.
    - unfold FinI_tail; simpl.
      reflexivity.
  Qed.

  Lemma extFin_env_one {k m} (η : FinI k) (ρ : FinI m) R :
    extFinI (extFinEnv η ρ) R == extFinEnv η (extFinI ρ R).
  Proof.
    intros x.
    refine (match x as x in Fin.t i return
                  match i return Fin.t i -> Prop with
                    | O => fun _ => False
                    | S i => fun x => forall m k (η : FinI k) (ρ : FinI m)
                                             (HEq : S i = S m + k),
                                        extFinI (extFinEnv η ρ) R (transfer HEq x) ==
                                        extFinEnv η (extFinI ρ R) (transfer HEq x)
                  end x with
              | Fin.F1 n => fun m k η ρ EQ => _
              | Fin.FS n x => fun m k η ρ EQ => _
            end m k η ρ eq_refl).
    - simpl in EQ; assert (EQ' := eq_add_S _ _ EQ); subst n.
      rewrite !transfer_nat_eq.
      unfold extFinEnv; simpl.
      reflexivity.
    - simpl in EQ; assert (EQ' := eq_add_S _ _ EQ); subst n.
      rewrite transfer_nat_eq; clear EQ.
      unfold extFinEnv; simpl.
      destruct (fin_sum_split x0); simpl; reflexivity.
  Qed.

  Lemma extFinI_eq {n m} R (η : FinI m) (EQ : m = n) :
    extFinI (transfer EQ η) R = transfer (eq_S _ _ EQ) (extFinI η R).
  Proof.
    subst n; rewrite transfer_nat_eq; reflexivity.
  Qed.

  (* TODO: make it so this thing works as an instance, and the casts are less horrible *)
  Instance transfer_FinI_equiv n m (EQ : n = m) : Proper (equiv ==> equiv) (transfer (T := FinI) EQ).
  Proof.
    intros η1 η2 EQη; subst n; rewrite transfer_nat_eq; assumption.
  Qed.

  Lemma of_nat_lt_ext {n k} (HLt1 HLt2 : n < k) :
    Fin.of_nat_lt HLt1 = Fin.of_nat_lt HLt2.
  Proof.
    revert n HLt1 HLt2; induction k; intros; [inversion HLt1 |].
    destruct n as [| n]; simpl; [reflexivity |].
    f_equal; apply IHk.
  Qed.

  Lemma fin_split_left {n m k}
        (HLt : n < m) (HLt2 : n < m + k) :
    fin_sum_split (Fin.of_nat_lt HLt2) = inl (Fin.of_nat_lt HLt).
  Proof.
    revert n HLt HLt2; induction m; intros; [inversion HLt |].
    destruct n as [| n]; simpl in *.
    - eexists; reflexivity.
    - erewrite IHm; reflexivity.
  Qed.

  Lemma fin_split_right {n m k}
        (HLt : n < k) (HLt2 : m + n < m + k) :
    fin_sum_split (Fin.of_nat_lt HLt2) = inr (Fin.of_nat_lt HLt).
  Proof.
    induction m; intros; simpl in *; [f_equal; apply of_nat_lt_ext |].
    erewrite IHm; reflexivity.
  Qed.

  Lemma extFinEnv_lookup_left {n m k} (η : FinI k) (ρ : FinI m)
        (HLt : n < m) (HLt2 : n < m + k) :
    extFinEnv η ρ (Fin.of_nat_lt HLt2) == ρ (Fin.of_nat_lt HLt).
  Proof.
    unfold extFinEnv.
    erewrite fin_split_left; reflexivity.
  Qed.

  Lemma minus_le_lt {k m n} (HGe : m <= n) (HLt : n < m + k) :
    n - m < k.
  Proof.
    apply Plus.plus_lt_reg_l with m.
    replace (m + (n - m)) with n by auto with arith; assumption.
  Qed.

  Lemma extFinEnv_lookup_right {k m n} (η : FinI k) (ρ : FinI m)
        (HGe : m <= n) (HLt : n < m + k) :
    extFinEnv η ρ (Fin.of_nat_lt HLt) == η (Fin.of_nat_lt (minus_le_lt HGe HLt)).
  Proof.
    generalize (minus_le_lt HGe HLt) as HL'; intros.
    revert HLt; pattern n at 1 2; replace n with (m + (n - m)) by auto with arith; intros.
    unfold extFinEnv; erewrite fin_split_right; reflexivity.
  Qed.

  Lemma extFinEnv_lookup_right_sum {n m k} (η : FinI k) (ρ : FinI m)
        (HLt : n < k) (HLt2 : m + n < m + k) :
    extFinEnv η ρ (Fin.of_nat_lt HLt2) == η (Fin.of_nat_lt HLt).
  Proof.
    unfold extFinEnv.
    erewrite fin_split_right; reflexivity.
  Qed.

  Lemma transfer_lookup {m n k} (η : FinI m) (EQ : m = n) (LT : k < n) :
    transfer EQ η (Fin.of_nat_lt LT) = η (Fin.of_nat_lt (transfer (eq_sym EQ) LT)).
  Proof.
    subst; rewrite !transfer_nat_eq; reflexivity.
  Qed.

End FiniteProducts.

Global Arguments FinI : default implicits.
