(** This module provides some additional constructions on CBUlt. These
    are:
    - the "1/2" functor, which divides all the distances by 1/2,
      and so makes any locally non-expansive functor locally
      contractive,
    - an extension operation on the space Tᵏ, for k ∈ nat, as a
      non-expansive morphism. *)

Require Import MetricRec.
Require Export UPred.

Section Halving.
  Context (T : cmtyp).

  Definition dist_halve n :=
    match n with
      | O  => fun (_ _ : T) => True
      | S n => dist n
    end.

  Program Definition halve_metr : metric T := mkMetr dist_halve.
  Next Obligation.
    destruct n; [resp_set | simpl; apply _].
  Qed.
  Next Obligation.
    split; intros HEq.
    - apply dist_refl; intros n; apply (HEq (S n)).
    - intros [| n]; [exact I |]; revert n; apply dist_refl, HEq.
  Qed.
  Next Obligation.
    intros t1 t2 HEq; destruct n; [exact I |]; symmetry; apply HEq.
  Qed.
  Next Obligation.
    intros t1 t2 t3 HEq12 HEq23; destruct n; [exact I |]; etransitivity; [apply HEq12 | apply HEq23].
  Qed.
  Next Obligation.
    destruct n; [exact I | apply dist_mono, H].
  Qed.

  Definition halveM : Mtyp := Build_Mtyp T halve_metr.

  Instance halve_chain (σ : chain halveM) {σc : cchain σ} : cchain (fun n => σ (S n) : T).
  Proof.
    unfold cchain; intros.
    apply (chain_cauchy σ σc (S n)); auto with arith.
  Qed.

  Definition compl_halve (σ : chain halveM) (σc : cchain σ) :=
    compl (fun n => σ (S n)) (σc := halve_chain σ).

  Program Definition halve_cm : cmetric halveM := mkCMetr compl_halve.
  Next Obligation.
    intros [| n]; [exists 0; intros; exact I |].
    destruct (conv_cauchy _ (σc := halve_chain σ) n) as [m HCon].
    exists (S m); intros [| i] HLe; [inversion HLe |].
    apply HCon; auto with arith.
  Qed.

  Definition halve : cmtyp := Build_cmtyp halveM halve_cm.

End Halving.

Ltac unhalve :=
  match goal with
    | |- dist_halve _ ?n ?f ?g => destruct n as [| n]; [exact I | change (f = n = g) ]
    | |- ?f = ?n = ?g => destruct n as [| n]; [exact I | change (f = n = g) ]
  end.

(* TODO: Refactor the following so that one can make it work for PCM
         instantiation without a lot of extra work. *)
Require Import CBUltInst.

Section Halving_Fun.
  Context F {FA : BiFMap F} {FFun : BiFunctor F}.
  Local Obligation Tactic := intros; resp_set || eauto.

  Program Instance halveFMap : BiFMap (fun T1 T2 => halve (F T1 T2)) :=
    fun m1 m2 m3 m4 => lift2m (lift2s (fun ars ob => fmorph (F := F) ars ob) _ _) _ _.
  Next Obligation.
    intros p1 p2 EQp x; simpl; rewrite EQp; reflexivity.
  Qed.
  Next Obligation.
    intros e1 e2 EQ; simpl. unhalve.
    rewrite EQ; reflexivity.
  Qed.
  Next Obligation.
    intros p1 p2 EQ e; simpl; unhalve.
    apply dist_mono in EQ.
    rewrite EQ; reflexivity.
  Qed.

  Instance halveF : BiFunctor (fun T1 T2 => halve (F T1 T2)).
  Proof.
    split; intros.
    + intros T; simpl.
      apply (fmorph_comp _ _ _ _ _ _ _ _ _ _ T).
    + intros T; simpl.
      apply (fmorph_id _ _ T).
  Qed.

  Instance halve_contractive {m0 m1 m2 m3} :
    contractive (@fmorph _ _ (fun T1 T2 => halve (F T1 T2)) _ m0 m1 m2 m3).
  Proof.
    intros n p1 p2 EQ f; simpl.
    change ((fmorph (F := F) p1) f = n = (fmorph p2) f).
    rewrite EQ; reflexivity.
  Qed.

End Halving_Fun.

Module Type SimplInput(Cat : MCat).
  Import Cat.

  Parameter F : M -> M -> M.
  Parameter FArr : BiFMap F.
  Parameter FFun : BiFunctor F.

  Parameter F_ne : (1 -t> F 1 1)%cat.
End SimplInput.

Module InputHalve (S : SimplInput (CBUlt)) : InputType(CBUlt)
    with Definition F := fun T1 T2 => halve (S.F T1 T2).
  Import CBUlt.
  Local Existing Instance S.FArr.
  Local Existing Instance S.FFun.
  Local Open Scope cat_scope.

  Definition F T1 T2 := halve (S.F T1 T2).
  Definition FArr := halveFMap S.F.
  Definition FFun := halveF S.F.

  Definition tmorph_ne : 1 -t> F 1 1 :=
    umconst (S.F_ne tt : F 1 1).

  Definition F_contractive := @halve_contractive S.F _.
End InputHalve.

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

  Global Instance disc_equiv : Proper (equiv (T := U -n> V) ==> equiv) disc_m.
  Proof. resp_set. Qed.
  Global Instance disc_dist n : Proper (dist (T := U -n> V) n ==> dist n) disc_m.
  Proof. resp_set. Qed.

  Lemma disc_m_comp (f : V -n> W) (g : U -n> V) :
    disc_m (f <M< g) == disc_m f ∘ disc_m g.
  Proof. intros x; simpl morph; reflexivity. Qed.

  Lemma disc_m_id : disc_m (umid W) == pid W.
  Proof. intros x; simpl morph; reflexivity. Qed.

End DiscM_Props.

Section EvaluationClosure.
  Context {T} {preoT : preoType T} (step : T -> T -> Prop).
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
    - rewrite evalCl_simpl in *; simpl; split; [| tauto]; destruct HEv as [HIrr _].
      rewrite <- EQR; assumption.
    - rewrite evalCl_simpl in HEv; destruct HEv as [HIrr HEv].
      rewrite evalCl_simpl; split; [rewrite <- EQR; assumption | intros].
      apply IHn, HEv, HS.
  Qed.

  Global Instance eval_dist n : Proper (dist n ==> dist n) evalCl.
  Proof.
    apply dist_upred_simpl; [apply _ |]; intros R1 R2 m t HLt EQR HEv;
    revert t HEv; induction m; intros.
    - rewrite evalCl_simpl in *; destruct HEv as [HIrr _]; simpl; split; [| tauto].
      intros HIrred; apply EQR, HIrr, HIrred; assumption.
    - rewrite evalCl_simpl in HEv; rewrite evalCl_simpl.
      split; [| intros; apply IHm, HEv, HS; now auto with arith].
      intros HIrr; apply EQR, HEv, HIrr; assumption.
  Qed.

  Global Instance eval_pord : Proper (pord ==> pord) evalCl.
  Proof.
    intros R1 R2 HSub n; induction n; intros t HEv.
    - rewrite evalCl_simpl in *; split; [rewrite <- HSub; apply HEv | simpl; tauto].
    - rewrite evalCl_simpl in *; split; [rewrite <- HSub; apply HEv |].
      intros; apply IHn, HEv, HS; now auto with arith.
  Qed.

  Definition rel_evalCl : UPred T -m> UPred T := m[(evalCl)].

End EvaluationClosure.

Require Fin.

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
