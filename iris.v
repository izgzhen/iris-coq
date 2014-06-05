Require Import world_prop core_lang lang masks.
Require Import RecDom.PCM RecDom.UPred RecDom.BI RecDom.PreoMet RecDom.Finmap.

Module Iris (RP RL : PCM_T) (C : CORE_LANG RP).

  Module Import L  := Lang RP RL C.
  Module Import R <: PCM_T.
    Definition res := (RP.res * RL.res)%type.
    Instance res_op   : PCM_op res := _.
    Instance res_unit : PCM_unit res := _.
    Instance res_pcm  : PCM res := _.
  End R.
  Module Import WP := WorldProp R.

  Delimit Scope iris_scope with iris.
  Local Open Scope iris_scope.

  (** The final thing we'd like to check is that the space of
      propositions does indeed form a complete BI algebra.

      The following instance declaration checks that an instance of
      the complete BI class can be found for Props (and binds it with
      a low priority to potentially speed up the proof search).
   *)

  Instance Props_BI : ComplBI Props | 0 := _.
  Instance Props_Later : Later Props | 0 := _.

  (** And now we're ready to build the IRIS-specific connectives! *)

  Section Necessitation.
    (** Note: this could be moved to BI, since it's possible to define
        for any UPred over a monoid. **)

    Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

    Program Definition box : Props -n> Props :=
      n[(fun p => m[(fun w => mkUPred (fun n r => p w n (pcm_unit _)) _)])].
    Next Obligation.
      intros n m r s HLe _ Hp; rewrite HLe; assumption.
    Qed.
    Next Obligation.
      intros w1 w2 EQw m r HLt; simpl.
      eapply (met_morph_nonexp _ _ p); eassumption.
    Qed.
    Next Obligation.
      intros w1 w2 Subw n r; simpl.
      apply p; assumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w m r HLt; simpl.
      apply EQp; assumption.
    Qed.

  End Necessitation.

  (** "Internal" equality **)
  Section IntEq.
    Context {T} `{mT : metric T}.

    Program Definition intEqP (t1 t2 : T) : UPred res :=
      mkUPred (fun n r => t1 = S n = t2) _.
    Next Obligation.
      intros n1 n2 _ _ HLe _; apply mono_dist; now auto with arith.
    Qed.

    Definition intEq (t1 t2 : T) : Props := pcmconst (intEqP t1 t2).

    Instance intEq_equiv : Proper (equiv ==> equiv ==> equiv) intEqP.
    Proof.
      intros l1 l2 EQl r1 r2 EQr n r.
      split; intros HEq; do 2 red.
      - rewrite <- EQl, <- EQr; assumption.
      - rewrite EQl, EQr; assumption.
    Qed.

    Instance intEq_dist n : Proper (dist n ==> dist n ==> dist n) intEqP.
    Proof.
      intros l1 l2 EQl r1 r2 EQr m r HLt.
      split; intros HEq; do 2 red.
      - etransitivity; [| etransitivity; [apply HEq |] ];
        apply mono_dist with n; eassumption || now auto with arith.
      - etransitivity; [| etransitivity; [apply HEq |] ];
        apply mono_dist with n; eassumption || now auto with arith.
    Qed.

  End IntEq.

  Notation "t1 '===' t2" := (intEq t1 t2) (at level 70) : iris_scope.

  Section Invariants.

    (** Invariants **)
    Definition invP (i : nat) (p : Props) (w : Wld) : UPred res :=
      intEqP (w i) (Some (ı' p)).
    Program Definition inv i : Props -n> Props :=
      n[(fun p => m[(invP i p)])].
    Next Obligation.
      intros w1 w2 EQw; unfold equiv, invP in *.
      apply intEq_equiv; [apply EQw | reflexivity].
    Qed.
    Next Obligation.
      intros w1 w2 EQw; unfold invP; simpl morph.
      destruct n; [apply dist_bound |].
      apply intEq_dist; [apply EQw | reflexivity].
    Qed.
    Next Obligation.
      intros w1 w2 Sw; unfold invP; simpl morph.
      intros n r HP; do 2 red; specialize (Sw i); do 2 red in HP.
      destruct (w1 i) as [μ1 |]; [| contradiction].
      destruct (w2 i) as [μ2 |]; [| contradiction]; simpl in Sw.
      rewrite <- Sw; assumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w; unfold equiv, invP in *; simpl morph.
      apply intEq_equiv; [reflexivity |].
      rewrite EQp; reflexivity.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w; unfold invP; simpl morph.
      apply intEq_dist; [reflexivity |].
      apply dist_mono, (met_morph_nonexp _ _ ı'), EQp.
    Qed.

  End Invariants.

  Notation "□ p" := (box p) (at level 30, right associativity) : iris_scope.
  Notation "⊤" := (top : Props) : iris_scope.
  Notation "⊥" := (bot : Props) : iris_scope.
  Notation "p ∧ q" := (and p q : Props) (at level 40, left associativity) : iris_scope.
  Notation "p ∨ q" := (or p q : Props) (at level 50, left associativity) : iris_scope.
  Notation "p * q" := (sc p q : Props) (at level 40, left associativity) : iris_scope.
  Notation "p → q" := (BI.impl p q : Props) (at level 55, right associativity) : iris_scope.
  Notation "p '-*' q" := (si p q : Props) (at level 55, right associativity) : iris_scope.
  Notation "∀ x , p" := (all n[(fun x => p)] : Props) (at level 60, x ident, no associativity) : iris_scope.
  Notation "∃ x , p" := (all n[(fun x => p)] : Props) (at level 60, x ident, no associativity) : iris_scope.
  Notation "∀ x : T , p" := (all n[(fun x : T => p)] : Props) (at level 60, x ident, no associativity) : iris_scope.
  Notation "∃ x : T , p" := (all n[(fun x : T => p)] : Props) (at level 60, x ident, no associativity) : iris_scope.

  (** Ownership **)
  Definition ownR (r : res) : Props :=
    pcmconst (up_cr (pord r)).

  (** Physical part **)
  Definition ownRP (r : RP.res) : Props :=
    ownR (r, pcm_unit _).

  (** Logical part **)
  Definition ownRL (r : RL.res) : Props :=
    ownR (pcm_unit _, r).

  (** Proper ghost state: ownership of logical w/ possibility of undefined **)
  Definition ownL (r : option RL.res) : Props :=
    match r with
      | Some r => ownRL r
      | None => ⊥
    end.

  Lemma ores_equiv_eq (r1 r2 : option res) (HEq : r1 == r2) : r1 = r2.
  Proof.
    destruct r1 as [r1 |]; destruct r2 as [r2 |]; try contradiction;
    simpl in HEq; subst; reflexivity.
  Qed.

  (** Lemmas about box **)
  Lemma box_intro p q (Hpq : □ p ⊑ q) :
    □ p ⊑ □ q.
  Proof.
    intros w n r Hp; simpl; apply Hpq, Hp.
  Qed.

  Lemma box_elim p :
    □ p ⊑ p.
  Proof.
    intros w n r Hp; simpl in Hp.
    eapply uni_pred, Hp; [reflexivity |].
    exists r; now erewrite comm, pcm_op_unit by apply _.
  Qed.

  (** Ghost state ownership **)
  Lemma ownL_sc (u t : option RL.res) :
    ownL (u · t)%pcm == ownL u * ownL t.
  Proof.
    intros w n r; split; [intros Hut | intros [r1 [r2 [EQr [Hu Ht] ] ] ] ].
    - destruct (u · t)%pcm as [ut |] eqn: EQut; [| contradiction].
      do 13 red in Hut; rewrite <- Hut.
      destruct u as [u |]; [| now erewrite pcm_op_zero in EQut by apply _].
      assert (HT := comm (Some u) t); rewrite EQut in HT.
      destruct t as [t |]; [| now erewrite pcm_op_zero in HT by apply _]; clear HT.
      exists (pcm_unit RP.res, u) (pcm_unit RP.res, t).
      split; [unfold pcm_op, res_op, pcm_op_prod | split; do 13 red; reflexivity].
      now erewrite pcm_op_unit, EQut by apply _.
    - destruct u as [u |]; [| contradiction]; destruct t as [t |]; [| contradiction].
      destruct Hu as [ru EQu]; destruct Ht as [rt EQt].
      rewrite <- EQt, assoc, (comm (Some r1)) in EQr.
      rewrite <- EQu, assoc, <- (assoc (Some rt · Some ru)%pcm) in EQr.
      unfold pcm_op at 3, res_op at 4, pcm_op_prod at 1 in EQr.
      erewrite pcm_op_unit in EQr by apply _; clear EQu EQt.
      destruct (Some u · Some t)%pcm as [ut |];
        [| now erewrite comm, pcm_op_zero in EQr by apply _].
      destruct (Some rt · Some ru)%pcm as [rut |];
        [| now erewrite pcm_op_zero in EQr by apply _].
      exists rut; assumption.
  Qed.

  Section Erasure.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.

    (* First, we need to erase a finite map. This won't be pretty, for
       now, since the library does not provide enough
       constructs. Hopefully we can provide a fold that'd work for
       that at some point
     *)
    Fixpoint comp_list (xs : list res) : option res :=
      match xs with
        | nil => 1
        | (x :: xs)%list => Some x · comp_list xs
      end.

    Definition cod (m : nat -f> res) : list res := List.map snd (findom_t m).
    Definition erase (m : nat -f> res) : option res := comp_list (cod m).

    Lemma erase_remove (rs : nat -f> res) i r (HLu : rs i = Some r) :
      erase rs == Some r · erase (fdRemove i rs).
    Proof.
      destruct rs as [rs rsP]; unfold erase, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [discriminate |]; simpl comp_list; simpl in HLu.
      destruct (comp i j); [inversion HLu; reflexivity | discriminate |].
      simpl comp_list; rewrite IHrs by eauto using SS_tail.
      rewrite !assoc, (comm (Some s)); reflexivity.
    Qed.

    Lemma erase_insert_new (rs : nat -f> res) i r (HNLu : rs i = None) :
      Some r · erase rs == erase (fdUpdate i r rs).
    Proof.
      destruct rs as [rs rsP]; unfold erase, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [reflexivity | simpl comp_list; simpl in HNLu].
      destruct (comp i j); [discriminate | reflexivity |].
      simpl comp_list; rewrite <- IHrs by eauto using SS_tail.
      rewrite !assoc, (comm (Some r)); reflexivity.
    Qed.

    Lemma erase_insert_old (rs : nat -f> res) i r1 r2 r
          (HLu : rs i = Some r1) (HEq : Some r1 · Some r2 == Some r) :
      Some r2 · erase rs == erase (fdUpdate i r rs).
    Proof.
      destruct rs as [rs rsP]; unfold erase, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [discriminate |]; simpl comp_list; simpl in HLu.
      destruct (comp i j); [inversion HLu; subst; clear HLu | discriminate |].
      - simpl comp_list; rewrite assoc, (comm (Some r2)), <- HEq; reflexivity.
      - simpl comp_list; rewrite <- IHrs by eauto using SS_tail.
        rewrite !assoc, (comm (Some r2)); reflexivity.
    Qed.

    Global Instance preo_unit : preoType () := disc_preo ().

    Program Definition erasure (σ : state) (m : mask) (r s : option res) (w : Wld) : UPred () :=
      ▹ (mkUPred (fun n _ =>
                    erase_state (option_map fst (r · s)) σ
                    /\ exists rs : nat -f> res,
                         erase rs == s /\
                         forall i (Hm : m i),
                           (i ∈ dom rs <-> i ∈ dom w) /\
                           forall π ri (HLw : w i == Some π) (HLrs : rs i == Some ri),
                             ı π w n ri) _).
    Next Obligation.
      intros n1 n2 _ _ HLe _ [HES HRS]; split; [assumption |].
      setoid_rewrite HLe; eassumption.
    Qed.

    Global Instance erasure_equiv σ : Proper (meq ==> equiv ==> equiv ==> equiv ==> equiv) (erasure σ).
    Proof.
      intros m1 m2 EQm r r' EQr s s' EQs w1 w2 EQw [| n] []; [reflexivity |];
      apply ores_equiv_eq in EQr; apply ores_equiv_eq in EQs; subst r' s'.
      split; intros [HES [rs [HE HM] ] ]; (split; [tauto | clear HES; exists rs]).
      - split; [assumption | intros; apply EQm in Hm; split; [| setoid_rewrite <- EQw; apply HM, Hm] ].
        destruct (HM _ Hm) as [HD _]; rewrite HD; clear - EQw.
        rewrite fdLookup_in; setoid_rewrite EQw; rewrite <- fdLookup_in; reflexivity.
      - split; [assumption | intros; apply EQm in Hm; split; [| setoid_rewrite EQw; apply HM, Hm] ].
        destruct (HM _ Hm) as [HD _]; rewrite HD; clear - EQw.
        rewrite fdLookup_in; setoid_rewrite <- EQw; rewrite <- fdLookup_in; reflexivity.
    Qed.

    Global Instance erasure_dist n σ m r s : Proper (dist n ==> dist n) (erasure σ m r s).
    Proof.
      intros w1 w2 EQw [| n'] [] HLt; [reflexivity |]; destruct n as [| n]; [now inversion HLt |].
      split; intros [HES [rs [HE HM] ] ]; (split; [tauto | clear HES; exists rs]).
      - split; [assumption | split; [rewrite <- (domeq _ _ _ EQw); apply HM, Hm |] ].
        intros; destruct (HM _ Hm) as [_ HR]; clear HE HM Hm.
        assert (EQπ := EQw i); rewrite HLw in EQπ; clear HLw.
        destruct (w1 i) as [π' |]; [| contradiction]; do 3 red in EQπ.
        apply ı in EQπ; apply EQπ; [now auto with arith |].
        apply (met_morph_nonexp _ _ (ı π')) in EQw; apply EQw; [now auto with arith |].
        apply HR; [reflexivity | assumption].
      - split; [assumption | split; [rewrite (domeq _ _ _ EQw); apply HM, Hm |] ].
        intros; destruct (HM _ Hm) as [_ HR]; clear HE HM Hm.
        assert (EQπ := EQw i); rewrite HLw in EQπ; clear HLw.
        destruct (w2 i) as [π' |]; [| contradiction]; do 3 red in EQπ.
        apply ı in EQπ; apply EQπ; [now auto with arith |].
        apply (met_morph_nonexp _ _ (ı π')) in EQw; apply EQw; [now auto with arith |].
        apply HR; [reflexivity | assumption].
    Qed.

  End Erasure.

  Notation " p @ k " := ((p : UPred ()) k tt) (at level 60, no associativity).

  Section ViewShifts.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Obligation Tactic := intros.

Lemma erasure_not_empty σ m r s w k (HN : r · s == 0) :
  ~ erasure σ m r s w @ S k.
Proof.
  intros [HD _]; apply ores_equiv_eq in HN; setoid_rewrite HN in HD.
  now apply erase_state_nonzero in HD.
Qed.

    Program Definition preVS (m1 m2 : mask) (p : Props) (w : Wld) : UPred res :=
      mkUPred (fun n r => forall w1 rf s mf σ k (HSub : w ⊑ w1) (HLe : k < n)
                                 (HD : mf # m1 ∪ m2)
                                 (HE : erasure σ (m1 ∪ mf) (Some r · rf) s w1 @ S k),
                          exists w2 r' s',
                            w1 ⊑ w2 /\ p w2 (S k) r'
                            /\ erasure σ (m2 ∪ mf) (Some r' · rf) s' w2 @ S k) _.
    Next Obligation.
      intros n1 n2 r1 r2 HLe [rd HR] HP; intros.
      destruct (HP w1 (Some rd · rf) s mf σ k) as [w2 [r1' [s' [HW [HP' HE'] ] ] ] ];
        try assumption; [now eauto with arith | |].
      - eapply erasure_equiv, HE; try reflexivity.
        rewrite assoc, (comm (Some r1)), HR; reflexivity.
      - rewrite assoc, (comm (Some r1')) in HE'.
        destruct (Some rd · Some r1') as [r2' |] eqn: HR';
          [| apply erasure_not_empty in HE'; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        exists w2 r2' s'; split; [assumption | split; [| assumption] ].
        eapply uni_pred, HP'; [| exists rd; rewrite HR']; reflexivity.
    Qed.

    Program Definition pvs (m1 m2 : mask) : Props -n> Props :=
      n[(fun p => m[(preVS m1 m2 p)])].
    Next Obligation.
      intros w1 w2 EQw n r; split; intros HP w2'; intros.
      - eapply HP; try eassumption; [].
        rewrite EQw; assumption.
      - eapply HP; try eassumption; [].
        rewrite <- EQw; assumption.
    Qed.
    Next Obligation.
      intros w1 w2 EQw n' r HLt; destruct n as [| n]; [now inversion HLt |]; split; intros HP w2'; intros.
      - symmetry in EQw; assert (HDE := extend_dist _ _ _ _ EQw HSub).
        assert (HSE := extend_sub _ _ _ _ EQw HSub); specialize (HP (extend w2' w1)).
        edestruct HP as [w1'' [r' [s' [HW HH] ] ] ]; try eassumption; clear HP; [ | ].
        + eapply erasure_dist, HE; [symmetry; eassumption | now eauto with arith].
        + symmetry in HDE; assert (HDE' := extend_dist _ _ _ _ HDE HW).
          assert (HSE' := extend_sub _ _ _ _ HDE HW); destruct HH as [HP HE'];
          exists (extend w1'' w2') r' s'; split; [assumption | split].
          * eapply (met_morph_nonexp _ _ p), HP ; [symmetry; eassumption | now eauto with arith].
          * eapply erasure_dist, HE'; [symmetry; eassumption | now eauto with arith].
      - assert (HDE := extend_dist _ _ _ _ EQw HSub); assert (HSE := extend_sub _ _ _ _ EQw HSub); specialize (HP (extend w2' w2)).
        edestruct HP as [w1'' [r' [s' [HW HH] ] ] ]; try eassumption; clear HP; [ | ].
        + eapply erasure_dist, HE; [symmetry; eassumption | now eauto with arith].
        + symmetry in HDE; assert (HDE' := extend_dist _ _ _ _ HDE HW).
          assert (HSE' := extend_sub _ _ _ _ HDE HW); destruct HH as [HP HE'];
          exists (extend w1'' w2') r' s'; split; [assumption | split].
          * eapply (met_morph_nonexp _ _ p), HP ; [symmetry; eassumption | now eauto with arith].
          * eapply erasure_dist, HE'; [symmetry; eassumption | now eauto with arith].
    Qed.
    Next Obligation.
      intros w1 w2 EQw n r HP w2'; intros; eapply HP; try eassumption; [].
      etransitivity; eassumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w n r; split; intros HP w1; intros.
      - setoid_rewrite <- EQp; eapply HP; eassumption.
      - setoid_rewrite EQp; eapply HP; eassumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w n' r HLt; split; intros HP w1; intros.
      - edestruct HP as [w2 [r' [s' [HW [HP' HE'] ] ] ] ]; try eassumption; [].
        clear HP; repeat (eexists; try eassumption); [].
        apply EQp; [now eauto with arith | assumption].
      - edestruct HP as [w2 [r' [s' [HW [HP' HE'] ] ] ] ]; try eassumption; [].
        clear HP; repeat (eexists; try eassumption); [].
        apply EQp; [now eauto with arith | assumption].
    Qed.

    Definition vs (m1 m2 : mask) (p q : Props) : Props :=
      □ (p → pvs m1 m2 q).

  End ViewShifts.

  Section ViewShiftProps.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.

    Implicit Types (p q r : Props) (i : nat) (m : mask).

    Definition mask_sing i := mask_set mask_emp i True.

    Lemma vsOpen i p :
      valid (vs (mask_sing i) mask_emp (inv i p) (▹ p)).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ HInv w'; clear nn; intros.
      do 12 red in HInv; destruct (w i) as [μ |] eqn: HLu; [| contradiction].
      apply ı in HInv; rewrite (isoR p) in HInv.
      (* get rid of the invisible 1/2 *)
      do 8 red in HInv.
      destruct HE as [HES [rs [HE HM] ] ].
      destruct (rs i) as [ri |] eqn: HLr.
      - rewrite erase_remove with (i := i) (r := ri) in HE by assumption.
        assert (HR : Some r · rf · s == Some r · Some ri · rf · erase (fdRemove i rs))
          by (rewrite <- HE, assoc, <- (assoc (Some r)), (comm rf), assoc; reflexivity).
        apply ores_equiv_eq in HR; setoid_rewrite HR in HES; clear HR.
        destruct (Some r · Some ri) as [rri |] eqn: HR;
          [| erewrite !pcm_op_zero in HES by apply _; now apply erase_state_nonzero in HES].
        exists w' rri (erase (fdRemove i rs)); split; [reflexivity |].
        split; [| split; [assumption |] ].
        + simpl; eapply HInv; [now auto with arith |].
          eapply uni_pred, HM with i;
            [| exists r; rewrite <- HR | | | rewrite HLr]; try reflexivity; [|].
          * left; unfold mask_sing, mask_set.
            destruct (Peano_dec.eq_nat_dec i i); tauto.
          * specialize (HSub i); rewrite HLu in HSub.
            symmetry; destruct (w' i); [assumption | contradiction].
        + exists (fdRemove i rs); split; [reflexivity | intros j Hm].
          destruct Hm as [| Hm]; [contradiction |]; specialize (HD j); simpl in HD.
          unfold mask_sing, mask_set in HD; destruct (Peano_dec.eq_nat_dec i j);
          [subst j; contradiction HD; tauto | clear HD].
          rewrite fdLookup_in; setoid_rewrite (fdRemove_neq _ _ _ n0); rewrite <- fdLookup_in; now auto.
      - rewrite <- fdLookup_notin_strong in HLr; contradiction HLr; clear HLr.
        specialize (HSub i); rewrite HLu in HSub; clear - HM HSub.
        destruct (HM i) as [HD _]; [left | rewrite HD, fdLookup_in_strong; destruct (w' i); [eexists; reflexivity | contradiction] ].
        clear; unfold mask_sing, mask_set.
        destruct (Peano_dec.eq_nat_dec i i); tauto.
    Qed.

    Lemma vsClose i p :
      valid (vs mask_emp (mask_sing i) (inv i p * ▹ p) ⊤).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ [r1 [r2 [HR [HInv HP] ] ] ] w'; clear nn; intros.
      do 12 red in HInv; destruct (w i) as [μ |] eqn: HLu; [| contradiction].
      apply ı in HInv; rewrite (isoR p) in HInv.
      (* get rid of the invisible 1/2 *)
      do 8 red in HInv.
      destruct HE as [HES [rs [HE HM] ] ].
      exists w' (pcm_unit _) (Some r · s); split; [reflexivity | split; [exact I |] ].
      assert (HR' : Some r · rf · s = rf · (Some r · s))
        by (apply ores_equiv_eq; rewrite assoc, (comm rf); reflexivity).
      setoid_rewrite HR' in HES; erewrite pcm_op_unit by apply _.
      split; [assumption |].
      remember (match rs i with Some ri => ri | None => pcm_unit _ end) as ri eqn: EQri.
      destruct (Some ri · Some r) as [rri |] eqn: EQR.
      - exists (fdUpdate i rri rs); split; [| intros j Hm].
        + symmetry; rewrite <- HE; clear - EQR EQri; destruct (rs i) as [rsi |] eqn: EQrsi; subst;
          [eapply erase_insert_old; [eassumption | rewrite <- EQR; reflexivity] |].
          erewrite pcm_op_unit in EQR by apply _; rewrite EQR.
          now apply erase_insert_new.
        + specialize (HD j); unfold mask_sing, mask_set in *; simpl in Hm, HD.
          destruct (Peano_dec.eq_nat_dec i j);
            [subst j; clear Hm |
             destruct Hm as [Hm | Hm]; [contradiction | rewrite fdLookup_in_strong, fdUpdate_neq, <- fdLookup_in_strong by assumption; now auto] ].
          rewrite !fdLookup_in_strong, fdUpdate_eq.
          destruct n as [| n]; [now inversion HLe | simpl in HP].
          rewrite HSub in HP; specialize (HSub i); rewrite HLu in HSub.
          destruct (w' i) as [π' |]; [| contradiction].
          split; [intuition now eauto | intros].
          simpl in HLw, HLrs, HSub; subst ri0; rewrite <- HLw, <- HSub.
          apply HInv; [now auto with arith |].
          eapply uni_pred, HP; [now auto with arith |].
          assert (HT : Some ri · Some r1 · Some r2 == Some rri)
            by (rewrite <- EQR, <- HR, assoc; reflexivity); clear - HT.
          destruct (Some ri · Some r1) as [rd |];
            [| now erewrite pcm_op_zero in HT by apply _].
          exists rd; assumption.
      - destruct (rs i) as [rsi |] eqn: EQrsi; subst;
        [| erewrite pcm_op_unit in EQR by apply _; discriminate].
        contradiction (erase_state_nonzero σ); clear - HE HES EQrsi EQR.
        assert (HH : rf · (Some r · s) = 0); [clear HES | rewrite HH in HES; assumption].
        apply ores_equiv_eq; rewrite <- HE, erase_remove by eassumption.
        rewrite (assoc (Some r)), (comm (Some r)), EQR, comm.
        erewrite !pcm_op_zero by apply _; reflexivity.
    Qed.

    Lemma vsTrans p q r m1 m2 m3 (HMS : m2 ⊆ m1 ∪ m3) :
      vs m1 m2 p q ∧ vs m2 m3 q r ⊑ vs m1 m3 p r.
    Proof.
      intros w' n r1 [Hpq Hqr] w HSub; specialize (Hpq _ HSub); rewrite HSub in Hqr; clear w' HSub.
      intros np rp HLe HS Hp w1; intros; specialize (Hpq _ _ HLe HS Hp).
      edestruct Hpq as [w2 [rq [sq [HSw12 [Hq HEq] ] ] ] ]; try eassumption; [|].
      { (* XXX: possible lemma *)
        clear - HD HMS.
        intros j [Hmf Hm12]; apply (HD j); split; [assumption |].
        destruct Hm12 as [Hm1 | Hm2]; [left; assumption | apply HMS, Hm2].
      }
      clear HS; assert (HS : pcm_unit _ ⊑ rq) by (exists rq; now erewrite comm, pcm_op_unit by apply _).
      rewrite <- HLe, HSub in Hqr; specialize (Hqr _ HSw12); clear Hpq HE w HSub Hp.
      edestruct (Hqr (S k) _ HLe0 HS Hq w2) as [w3 [rR [sR [HSw23 [Hr HEr] ] ] ] ];
        try (reflexivity || eassumption); [now auto with arith | |].
      { (* XXX: possible lemma *)
        clear - HD HMS.
        intros j [Hmf Hm23]; apply (HD j); split; [assumption |].
        destruct Hm23 as [Hm2 | Hm3]; [apply HMS, Hm2 | right; assumption].
      }
      clear HEq Hq HS.
      setoid_rewrite HSw12; eauto 8.
    Qed.

    Lemma vsEnt p q m :
      □ (p → q) ⊑ vs m m p q.
    Proof.
      intros w' n r1 Himp w HSub; rewrite HSub in Himp; clear w' HSub.
      intros np rp HLe HS Hp w1; intros.
      exists w1 rp s; split; [reflexivity | split; [| assumption ] ].
      eapply Himp; [assumption | now eauto with arith | exists rp; now erewrite comm, pcm_op_unit by apply _ |].
      unfold lt in HLe0; rewrite HLe0, <- HSub; assumption.
    Qed.

    Lemma vsFrame p q r m1 m2 mf (HDisj : mf # m1 ∪ m2) :
      vs m1 m2 p q ⊑ vs (m1 ∪ mf) (m2 ∪ mf) (p * r) (q * r).
    Proof.
      intros w' n r1 HVS w HSub; specialize (HVS _ HSub); clear w' r1 HSub.
      intros np rpr HLe _ [rp [rr [HR [Hp Hr] ] ] ] w'; intros.
      assert (HS : pcm_unit _ ⊑ rp) by (exists rp; now erewrite comm, pcm_op_unit by apply _).
      specialize (HVS _ _ HLe HS Hp w' (Some rr · rf) s (mf ∪ mf0) σ k); clear HS.
      destruct HVS as [w'' [rq [s' [HSub' [Hq HEq] ] ] ] ]; try assumption; [| |].
      - (* disjointness of masks: possible lemma *)
        clear - HD HDisj; intros i [ [Hmf | Hmf] Hm12]; [eapply HDisj; now eauto |].
        eapply HD; split; [eassumption | tauto].
      - rewrite assoc, HR; eapply erasure_equiv, HE; try reflexivity; [].
        clear; intros i; tauto.
      - rewrite assoc in HEq; destruct (Some rq · Some rr) as [rqr |] eqn: HR';
        [| apply erasure_not_empty in HEq; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        exists w'' rqr s'; split; [assumption | split].
        + unfold lt in HLe0; rewrite HSub, HSub', <- HLe0 in Hr; exists rq rr.
          rewrite HR'; split; now auto.
        + eapply erasure_equiv, HEq; try reflexivity; [].
          clear; intros i; tauto.
    Qed.

    Lemma vsFalse m1 m2 :
      valid (vs m1 m2 ⊥ ⊥).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ HB; contradiction.
    Qed.

    Global Instance nat_type : Setoid nat := discreteType.
    Global Instance nat_metr : metric nat := discreteMetric.
    Global Instance nat_cmetr : cmetric nat := discreteCMetric.

    Program Definition inv' m : Props -n> {n : nat | m n} -n> Props :=
      n[(fun p => n[(fun n => inv n p)])].
    Next Obligation.
      intros i i' EQi; simpl in EQi; rewrite EQi; reflexivity.
    Qed.
    Next Obligation.
      intros i i' EQi; destruct n as [| n]; [apply dist_bound |].
      simpl in EQi; rewrite EQi; reflexivity.
    Qed.
    Next Obligation.
      intros p1 p2 EQp i; simpl morph.
      apply (morph_resp (inv (` i))); assumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp i; simpl morph.
      apply (inv (` i)); assumption.
    Qed.

    Lemma fresh_region (w : Wld) m (HInf : mask_infinite m) :
      exists i, m i /\ w i = None.
    Proof.
      destruct (HInf (S (List.last (dom w) 0%nat))) as [i [HGe Hm] ];
      exists i; split; [assumption |]; clear - HGe.
      rewrite <- fdLookup_notin_strong.
      destruct w as [ [| [n v] w] wP]; unfold dom in *; simpl findom_t in *; [tauto |].
      simpl List.map in *; rewrite last_cons in HGe.
      unfold ge in HGe; intros HIn; eapply Gt.gt_not_le, HGe.
      apply Le.le_n_S, SS_last_le; assumption.
    Qed.

    (* XXX: move up to definitions *)
    Definition injProp (P : Prop) : Props :=
      pcmconst (up_cr (const P)).

    Instance LP_mask m : LimitPreserving m.
    Proof.
      intros σ σc Hp; apply Hp.
    Qed.

    Lemma vsNewInv p m (HInf : mask_infinite m) :
      valid (vs m m (▹ p) (xist (inv' m p))).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ HP w'; clear nn; intros.
      destruct n as [| n]; [now inversion HLe | simpl in HP].
      rewrite HSub in HP; clear w HSub; rename w' into w.
      destruct (fresh_region w m HInf) as [i [Hm HLi] ].
      assert (HSub : w ⊑ fdUpdate i (ı' p) w).
      { intros j; destruct (Peano_dec.eq_nat_dec i j); [subst j; rewrite HLi; exact I|].
        now rewrite fdUpdate_neq by assumption.
      }
      exists (fdUpdate i (ı' p) w) (pcm_unit _) (Some r · s); split; [assumption | split].
      - exists (exist _ i Hm); do 16 red.
        unfold proj1_sig; rewrite fdUpdate_eq; reflexivity.
      - erewrite pcm_op_unit by apply _.
        assert (HR : rf · (Some r · s) = Some r · rf · s)
          by (apply ores_equiv_eq; rewrite assoc, (comm rf); reflexivity).
        destruct HE as [HES [rs [HE HM] ] ].
        split; [setoid_rewrite HR; assumption | clear HR].
        assert (HRi : rs i = None).
        { destruct (HM i) as [HDom _]; [tauto |].
          rewrite <- fdLookup_notin_strong, HDom, fdLookup_notin_strong; assumption.
        }
        exists (fdUpdate i r rs); split; [now rewrite <- erase_insert_new, HE by assumption | intros j Hm'].
        rewrite !fdLookup_in_strong; destruct (Peano_dec.eq_nat_dec i j).
        + subst j; rewrite !fdUpdate_eq; split; [intuition now eauto | intros].
          simpl in HLw, HLrs; subst ri; rewrite <- HLw, isoR, <- HSub.
          eapply uni_pred, HP; [now auto with arith | reflexivity].
        + rewrite !fdUpdate_neq, <- !fdLookup_in_strong by assumption.
          setoid_rewrite <- HSub.
          apply HM; assumption.
    Qed.

    (* XXX missing statements: NewGhost, GhostUpd, VSTimeless *)

  End ViewShiftProps.

  Section HoareTriples.
  (* Quadruples, really *)
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.
    Local Open Scope lang_scope.

    Global Instance expr_type : Setoid expr := discreteType.
    Global Instance expr_metr : metric expr := discreteMetric.
    Global Instance expr_cmetr : cmetric expr := discreteCMetric.
    Instance LP_isval : LimitPreserving is_value.
    Proof.
      intros σ σc HC; apply HC.
    Qed.

    Implicit Types (P Q R : Props) (i : nat) (m : mask) (e : expr) (w : Wld) (φ : value -n> Props) (r : res).

    Local Obligation Tactic := intros; eauto with typeclass_instances.

    Definition wpFP m (WP : expr -n> (value -n> Props) -n> Props) e φ w n r :=
      forall w' k s rf σ (HSw : w ⊑ w') (HLt : k < n)
             (HE : erasure σ m (Some r · rf) s w' @ S k),
        (forall (HV : is_value e),
         exists w'' r' s', w' ⊑ w'' /\ φ (exist _ e HV) w'' (S k) r'
                           /\ erasure σ m (Some r' · rf) s' w'' @ S k) /\
        (forall σ' ei ei' K (HDec : e = K [[ ei ]])
                (HStep : prim_step (ei, σ) (ei', σ')),
         exists w'' r' s', w' ⊑ w'' /\ WP (K [[ ei' ]]) φ w'' k r'
                           /\ erasure σ' m (Some r' · rf) s' w'' @ k) /\
        (forall e' K (HDec : e = K [[ fork e' ]]),
         exists w'' rfk rret s', w' ⊑ w''
                                 /\ WP (K [[ fork_ret ]]) φ w'' k rret
                                 /\ WP e' (umconst ⊤) w'' k rfk
                                 /\ erasure σ m (Some rfk · Some rret · rf) s' w'' @ k).

    Program Definition wpF m : (expr -n> (value -n> Props) -n> Props) -n> expr -n> (value -n> Props) -n> Props :=
      n[(fun WP => n[(fun e => n[(fun φ => m[(fun w => mkUPred (wpFP m WP e φ w) _)])])])].
    Next Obligation.
      intros n1 n2 r1 r2 HLe [rd EQr] Hp w' k s rf σ HSw HLt HE.
      rewrite <- EQr, (comm (Some rd)), <- assoc in HE.
      specialize (Hp w' k s (Some rd · rf) σ); destruct Hp as [HV [HS HF] ];
      [| now eauto with arith | ..]; try assumption; [].
      split; [clear HS HF | split; [clear HV HF | clear HV HS] ]; intros.
      - specialize (HV HV0); destruct HV as [w'' [r1' [s' [HSw' [Hφ HE'] ] ] ] ].
        rewrite assoc, (comm (Some r1')) in HE'.
        destruct (Some rd · Some r1') as [r2' |] eqn: HR;
          [| apply erasure_not_empty in HE'; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        exists w'' r2' s'; split; [assumption | split; [| assumption] ].
        eapply uni_pred, Hφ; [| eexists; rewrite <- HR]; reflexivity.
      - specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r1' [s' [HSw' [HWP HE'] ] ] ] ].
        rewrite assoc, (comm (Some r1')) in HE'.
        destruct k as [| k]; [exists w'' r1' s'; simpl erasure; tauto |].
        destruct (Some rd · Some r1') as [r2' |] eqn: HR;
          [| apply erasure_not_empty in HE'; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        exists w'' r2' s'; split; [assumption | split; [| assumption] ].
        eapply uni_pred, HWP; [| eexists; rewrite <- HR]; reflexivity.
      - specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret1 [s' [HSw' [HWR [HWF HE'] ] ] ] ] ] ].
        destruct k as [| k]; [exists w'' rfk rret1 s'; simpl erasure; tauto |].
        rewrite assoc, <- (assoc (Some rfk)), (comm (Some rret1)) in HE'.
        destruct (Some rd · Some rret1) as [rret2 |] eqn: HR;
          [| apply erasure_not_empty in HE'; [contradiction | now erewrite (comm _ 0), !pcm_op_zero by apply _] ].
        exists w'' rfk rret2 s'; repeat (split; try assumption); [].
        eapply uni_pred, HWR; [| eexists; rewrite <- HR]; reflexivity.
    Qed.
    Next Obligation.
      intros w1 w2 EQw n r; simpl.
      split; intros Hp w'; intros; eapply Hp; try eassumption.
      - rewrite EQw; assumption.
      - rewrite <- EQw; assumption.
    Qed.
    Next Obligation.
      intros w1 w2 EQw n' r HLt; simpl; destruct n as [| n]; [now inversion HLt |]; split; intros Hp w2'; intros.
      - symmetry in EQw; assert (EQw' := extend_dist _ _ _ _ EQw HSw); assert (HSw' := extend_sub _ _ _ _ EQw HSw); symmetry in EQw'.
        edestruct (Hp (extend w2' w1)) as [HV [HS HF] ]; try eassumption;
        [eapply erasure_dist, HE; [eassumption | now eauto with arith] |].
        split; [clear HS HF | split; [clear HV HF | clear HV HS] ]; intros.
        + specialize (HV HV0); destruct HV as [w1'' [r' [s' [HSw'' [Hφ HE'] ] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') r' s'; split; [assumption |].
          split; [| eapply erasure_dist, HE'; [eassumption | now eauto with arith] ].
          eapply (met_morph_nonexp _ _ (φ _)), Hφ; [eassumption | now eauto with arith].
        + specialize (HS _ _ _ _ HDec HStep); destruct HS as [w1'' [r' [s' [HSw'' [HWP HE'] ] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') r' s'; split; [assumption |].
          split; [| eapply erasure_dist, HE'; [eassumption | now eauto with arith] ].
          eapply (met_morph_nonexp _ _ (WP _ _)), HWP; [eassumption | now eauto with arith].
        + specialize (HF _ _ HDec); destruct HF as [w1'' [rfk [rret [s' [HSw'' [HWR [HWF HE'] ] ] ] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') rfk rret s'; split; [assumption |].
          split; [| split; [| eapply erasure_dist, HE'; [eassumption | now eauto with arith] ] ];
          eapply (met_morph_nonexp _ _ (WP _ _)); try eassumption; now eauto with arith.
      - assert (EQw' := extend_dist _ _ _ _ EQw HSw); assert (HSw' := extend_sub _ _ _ _ EQw HSw); symmetry in EQw'.
        edestruct (Hp (extend w2' w2)) as [HV [HS HF] ]; try eassumption;
        [eapply erasure_dist, HE; [eassumption | now eauto with arith] |].
        split; [clear HS HF | split; [clear HV HF | clear HV HS] ]; intros.
        + specialize (HV HV0); destruct HV as [w1'' [r' [s' [HSw'' [Hφ HE'] ] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') r' s'; split; [assumption |].
          split; [| eapply erasure_dist, HE'; [eassumption | now eauto with arith] ].
          eapply (met_morph_nonexp _ _ (φ _)), Hφ; [eassumption | now eauto with arith].
        + specialize (HS _ _ _ _ HDec HStep); destruct HS as [w1'' [r' [s' [HSw'' [HWP HE'] ] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') r' s'; split; [assumption |].
          split; [| eapply erasure_dist, HE'; [eassumption | now eauto with arith] ].
          eapply (met_morph_nonexp _ _ (WP _ _)), HWP; [eassumption | now eauto with arith].
        + specialize (HF _ _ HDec); destruct HF as [w1'' [rfk [rret [s' [HSw'' [HWR [HWF HE'] ] ] ] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') rfk rret s'; split; [assumption |].
          split; [| split; [| eapply erasure_dist, HE'; [eassumption | now eauto with arith] ] ];
          eapply (met_morph_nonexp _ _ (WP _ _)); try eassumption; now eauto with arith.
    Qed.
    Next Obligation.
      intros w1 w2 Sw n r; simpl; intros Hp w'; intros; eapply Hp; try eassumption.
      etransitivity; eassumption.
    Qed.
    Next Obligation.
      intros φ1 φ2 EQφ w n r; simpl.
      unfold wpFP; setoid_rewrite EQφ; reflexivity.
    Qed.
    Next Obligation.
      intros φ1 φ2 EQφ w k r HLt; simpl; destruct n as [| n]; [now inversion HLt |].
      split; intros Hp w'; intros; edestruct Hp as [HV [HS HF] ]; try eassumption; [|].
      - split; [| split]; intros.
        + clear HS HF; specialize (HV HV0); destruct HV as [w'' [r' [s' [HSw' [Hφ HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          apply EQφ, Hφ; now eauto with arith.
        + clear HV HF; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [s' [HSw' [Hφ HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          eapply (met_morph_nonexp _ _ (WP _)), Hφ; [symmetry; eassumption | now eauto with arith].
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [s' [HSw' [HWR [HWF HE'] ] ] ] ] ] ].
          exists w'' rfk rret s'; repeat (split; try assumption); [].
          eapply (met_morph_nonexp _ _ (WP _)), HWR; [symmetry; eassumption | now eauto with arith].
      - split; [| split]; intros.
        + clear HS HF; specialize (HV HV0); destruct HV as [w'' [r' [s' [HSw' [Hφ HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          apply EQφ, Hφ; now eauto with arith.
        + clear HV HF; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [s' [HSw' [Hφ HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          eapply (met_morph_nonexp _ _ (WP _)), Hφ; [eassumption | now eauto with arith].
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [s' [HSw' [HWR [HWF HE'] ] ] ] ] ] ].
          exists w'' rfk rret s'; repeat (split; try assumption); [].
          eapply (met_morph_nonexp _ _ (WP _)), HWR; [eassumption | now eauto with arith].
    Qed.
    Next Obligation.
      intros e1 e2 EQe φ w n r; simpl.
      simpl in EQe; subst e2; reflexivity.
    Qed.
    Next Obligation.
      intros e1 e2 EQe φ w k r HLt; destruct n as [| n]; [now inversion HLt | simpl].
      simpl in EQe; subst e2; reflexivity.
    Qed.
    Next Obligation.
      intros WP1 WP2 EQWP e φ w n r; simpl.
      unfold wpFP; setoid_rewrite EQWP; reflexivity.
    Qed.
    Next Obligation.
      intros WP1 WP2 EQWP e φ w k r HLt; destruct n as [| n]; [now inversion HLt | simpl].
      split; intros Hp w'; intros; edestruct Hp as [HF [HS HV] ]; try eassumption; [|].
      - split; [assumption | split; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [s' [HSw' [HWP HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          eapply (EQWP _ _ _), HWP; now eauto with arith.
        + clear HF HS; specialize (HV _ _ HDec); destruct HV as [w'' [rfk [rret [s' [HSw' [HWR [HWF HE'] ] ] ] ] ] ].
          exists w'' rfk rret s'; split; [assumption |].
          split; [| split; [| assumption] ]; eapply EQWP; try eassumption; now eauto with arith.
      - split; [assumption | split; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [s' [HSw' [HWP HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          eapply (EQWP _ _ _), HWP; now eauto with arith.
        + clear HF HS; specialize (HV _ _ HDec); destruct HV as [w'' [rfk [rret [s' [HSw' [HWR [HWF HE'] ] ] ] ] ] ].
          exists w'' rfk rret s'; split; [assumption |].
          split; [| split; [| assumption] ]; eapply EQWP; try eassumption; now eauto with arith.
    Qed.

    Instance contr_wpF m : contractive (wpF m).
    Proof.
      intros n WP1 WP2 EQWP e φ w k r HLt.
      split; intros Hp w'; intros; edestruct Hp as [HV [HS HF] ]; try eassumption; [|].
      - split; [assumption | split; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [s' [HSw' [HWP HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          eapply EQWP, HWP; now eauto with arith.
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [s' [HSw' [HWR [HWF HE'] ] ] ] ] ] ].
          exists w'' rfk rret s'; split; [assumption |].
          split; [| split; [| assumption] ]; eapply EQWP; try eassumption; now eauto with arith.
      - split; [assumption | split; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [s' [HSw' [HWP HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          eapply EQWP, HWP; now eauto with arith.
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [s' [HSw' [HWR [HWF HE'] ] ] ] ] ] ].
          exists w'' rfk rret s'; split; [assumption |].
          split; [| split; [| assumption] ]; eapply EQWP; try eassumption; now eauto with arith.
    Qed.

    Definition wp m : expr -n> (value -n> Props) -n> Props :=
      fixp (wpF m) (umconst (umconst ⊤)).

    Definition ht m P e φ := □ (P → wp m e φ).

  End HoareTriples.

  Section HoareTripleProperties.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.
    Local Open Scope lang_scope.

    Existing Instance LP_isval.

    Implicit Types (P Q R : Props) (i : nat) (m : mask) (e : expr) (φ : value -n> Props) (r : res).

    (** Ret **)
    Program Definition eqV v : value -n> Props :=
      n[(fun v' : value => v === v')].
    Next Obligation.
      intros v1 v2 EQv w n r; simpl in *; split; congruence.
    Qed.
    Next Obligation.
      intros v1 v2 EQv w m r HLt; destruct n as [| n]; [now inversion HLt | simpl in *].
      split; congruence.
    Qed.

    Lemma htRet e (HV : is_value e) m :
      valid (ht m ⊤ e (eqV (exist _ e HV))).
    Proof.
      intros w' nn rr w _ n r' _ _ _; clear w' nn rr.
      unfold wp; rewrite fixp_eq; fold (wp m).
      intros w'; intros; split; [| split]; intros.
      - exists w' r' s; split; [reflexivity | split; [| assumption] ].
        simpl; reflexivity.
      - assert (HT := values_stuck _ HV).
        eapply HT in HStep; [contradiction | eassumption].
      - subst e; assert (HT := fill_value _ _ HV); subst K.
        revert HV; rewrite fill_empty; intros.
        contradiction (fork_not_value _ HV).
    Qed.

    Implicit Type (C : Props).

    Lemma wpO m e φ w r : wp m e φ w O r.
    Proof.
      unfold wp; rewrite fixp_eq; fold (wp m); intros w'; intros; now inversion HLt.
    Qed.

    (** Bind **)
    Program Definition plugV m φ φ' K :=
      n[(fun v : value => ht m (φ v) (K [[` v]]) φ')].
    Next Obligation.
      intros v1 v2 EQv w n r; simpl.
      setoid_rewrite EQv at 1.
      simpl in EQv; rewrite EQv; reflexivity.
    Qed.
    Next Obligation.
      intros v1 v2 EQv; unfold ht; eapply (met_morph_nonexp _ _ box).
      eapply (impl_dist (ComplBI := Props_BI)).
      - apply φ; assumption.
      - destruct n as [| n]; [apply dist_bound | simpl in EQv].
        rewrite EQv; reflexivity.
    Qed.

    Lemma unit_min r : pcm_unit _ ⊑ r.
    Proof.
      exists r; now erewrite comm, pcm_op_unit by apply _.
    Qed.

    Definition wf_nat_ind := well_founded_induction Wf_nat.lt_wf.

    Lemma htBind P φ φ' K e m :
      ht m P e φ ∧ all (plugV m φ φ' K) ⊑ ht m P (K [[ e ]]) φ'.
    Proof.
      intros wz nz rz [He HK] w HSw n r HLe _ HP.
      specialize (He _ HSw _ _ HLe (unit_min _) HP).
      rewrite HSw, <- HLe in HK; clear wz nz HSw HLe HP.
      revert e w r He HK; induction n using wf_nat_ind; intros; rename H into IH.
      unfold wp; rewrite fixp_eq; fold (wp m).
      unfold wp in He; rewrite fixp_eq in He; fold (wp m) in He.
      destruct (is_value_dec e) as [HVal | HNVal]; [clear IH |].
      - intros w'; intros; edestruct He as [HV _]; try eassumption; [].
        clear He HE; specialize (HV HVal); destruct HV as [w'' [r' [s' [HSw' [Hφ HE] ] ] ] ].
        (* Fold the goal back into a wp *)
        setoid_rewrite HSw'.
        assert (HT : wp m (K [[ e ]]) φ' w'' (S k) r');
          [| unfold wp in HT; rewrite fixp_eq in HT; fold (wp m) in HT;
             eapply HT; [reflexivity | unfold lt; reflexivity | eassumption] ].
        clear HE; specialize (HK (exist _ e HVal)).
        do 30 red in HK; unfold proj1_sig in HK.
        apply HK; [etransitivity; eassumption | apply HLt | apply unit_min | assumption].
      - intros w'; intros; edestruct He as [_ [HS HF] ]; try eassumption; [].
        split; [intros HVal; contradiction HNVal; assert (HT := fill_value _ _ HVal);
                subst K; rewrite fill_empty in HVal; assumption | split; intros].
        + clear He HF HE; edestruct step_by_value as [K' EQK]; try eassumption; [].
          subst K0; rewrite <- fill_comp in HDec; apply fill_inj2 in HDec.
          edestruct HS as [w'' [r' [s' [HSw' [He HE] ] ] ] ]; try eassumption; [].
          subst e; clear HStep HS.
          do 3 eexists; split; [eassumption | split; [| eassumption] ].
          rewrite <- fill_comp; apply IH; try assumption; [].
          unfold lt in HLt; rewrite <- HSw', <- HSw, Le.le_n_Sn, HLt; apply HK.
        + clear He HS HE; edestruct fork_by_value as [K' EQK]; try eassumption; [].
          subst K0; rewrite <- fill_comp in HDec; apply fill_inj2 in HDec.
          edestruct HF as [w'' [rfk [rret [s' [HSw' [HWR [HWF HE] ] ] ] ] ] ];
            try eassumption; []; subst e; clear HF.
          do 4 eexists; split; [eassumption | split; [| split; eassumption] ].
          rewrite <- fill_comp; apply IH; try assumption; [].
          unfold lt in HLt; rewrite <- HSw', <- HSw, Le.le_n_Sn, HLt; apply HK.
    Qed.

    (** Consequence **)

    Program Definition vsLift m1 m2 φ φ' :=
      n[(fun v => vs m1 m2 (φ v) (φ' v))].
    Next Obligation.
      intros v1 v2 EQv; unfold vs.
      rewrite EQv; reflexivity.
    Qed.
    Next Obligation.
      intros v1 v2 EQv; unfold vs.
      rewrite EQv; reflexivity.
    Qed.

    Lemma htCons P P' φ φ' m e :
      vs m m P P' ∧ ht m P' e φ' ∧ all (vsLift m m φ' φ) ⊑ ht m P e φ.
    Proof.
      intros wz nz rz [ [HP He] Hφ] w HSw n r HLe _ Hp.
      specialize (HP _ HSw _ _ HLe (unit_min _) Hp).
      unfold wp; rewrite fixp_eq; fold (wp m).
      rewrite <- HLe, HSw in He, Hφ; clear wz nz HSw HLe Hp.
      intros w'; intros; edestruct HP with (mf := mask_emp) as [w'' [r' [s' [HSw' [Hp' HE'] ] ] ] ]; try eassumption;
      [intros j; tauto | eapply erasure_equiv, HE; try reflexivity; unfold mask_emp, const; intros j; tauto |].
      clear HP HE; rewrite HSw in He; specialize (He w'' HSw' _ r' HLt (unit_min _) Hp').
      setoid_rewrite HSw'.
      assert (HT : wp m e φ w'' (S k) r');
        [| unfold wp in HT; rewrite fixp_eq in HT; fold (wp m) in HT;
           eapply HT; [reflexivity | unfold lt; reflexivity |];
           eapply erasure_equiv, HE'; try reflexivity; unfold mask_emp, const; intros j; tauto ].
      unfold lt in HLt; rewrite HSw, HSw', <- HLt in Hφ; clear - He Hφ.
      (* Second phase of the proof: got rid of the preconditions,
         now induction takes care of the evaluation. *)
      rename r' into r; rename w'' into w.
      revert w r e He Hφ; generalize (S k) as n; clear k; induction n using wf_nat_ind.
      rename H into IH; intros; unfold wp; rewrite fixp_eq; fold (wp m).
      unfold wp in He; rewrite fixp_eq in He; fold (wp m).
      intros w'; intros; edestruct He as [HV [HS HF] ]; try eassumption; [].
      split; [intros HVal; clear HS HF IH | split; intros; [clear HV HF | clear HV HS] ].
      - clear He HE; specialize (HV HVal); destruct HV as [w'' [r' [s' [HSw' [Hφ' HE] ] ] ] ].
        eapply Hφ in Hφ'; [| etransitivity; eassumption | apply HLt | apply unit_min].
        clear w n HSw Hφ HLt; edestruct Hφ' with (mf := mask_emp) as [w [r'' [s'' [HSw [Hφ HE'] ] ] ] ];
        [reflexivity | apply le_n | intros j; tauto |
         eapply erasure_equiv, HE; try reflexivity; unfold mask_emp, const; intros j; tauto |].
        exists w r'' s''; split; [etransitivity; eassumption | split; [assumption |] ].
        eapply erasure_equiv, HE'; try reflexivity.
        unfold mask_emp, const; intros j; tauto.
      - clear HE He; edestruct HS as [w'' [r' [s' [HSw' [He HE] ] ] ] ];
        try eassumption; clear HS; fold (wp m) in He.
        do 3 eexists; split; [eassumption | split; [| eassumption] ].
        apply IH; try assumption; [].
        unfold lt in HLt; rewrite Le.le_n_Sn, HLt, <- HSw', <- HSw; apply Hφ.
      - clear HE He; fold (wp m) in HF; edestruct HF as [w'' [rfk [rret [s' [HSw' [HWF [HWR HE] ] ] ] ] ] ]; [eassumption |].
        clear HF; do 4 eexists; split; [eassumption | split; [| split; eassumption] ].
        apply IH; try assumption; [].
        unfold lt in HLt; rewrite Le.le_n_Sn, HLt, <- HSw', <- HSw; apply Hφ.
    Qed.

    Lemma htACons m m' e P P' φ φ'
          (HAt   : atomic e)
          (HSub  : m' ⊆ m) :
      vs m m' P P' ∧ ht m' P' e φ' ∧ all (vsLift m' m φ' φ) ⊑ ht m P e φ.
    Proof.
      intros wz nz rz [ [HP He] Hφ] w HSw n r HLe _ Hp.
      specialize (HP _ HSw _ _ HLe (unit_min _) Hp).
      unfold wp; rewrite fixp_eq; fold (wp m).
      split; [intros HV; contradiction (atomic_not_value e) |].
      split; [| intros; subst; contradiction (fork_not_atomic K e') ].
      intros; rewrite <- HLe, HSw in He, Hφ; clear wz nz HSw HLe Hp.
      edestruct HP with (mf := mask_emp) as [w'' [r' [s' [HSw' [Hp' HE'] ] ] ] ];
        [eassumption | eassumption | intros j; tauto |
         eapply erasure_equiv, HE; try reflexivity; unfold mask_emp, const; intros j; tauto |].
      clear HP HE; rewrite HSw0 in He; specialize (He w'' HSw' _ r' HLt (unit_min _) Hp').
      unfold lt in HLt; rewrite HSw0, <- HLt in Hφ; clear w n HSw0 HLt Hp'.
      unfold wp in He; rewrite fixp_eq in He; fold (wp m') in He.
      edestruct He as [_ [HS _] ];
        [reflexivity | unfold lt; reflexivity |
         eapply erasure_equiv, HE'; try reflexivity; unfold mask_emp, const; intros j; tauto |].
      edestruct HS as [w [r'' [s'' [HSw [He' HE] ] ] ] ]; try eassumption; clear He HS HE'.
      destruct k as [| k]; [exists w' r' s'; split; [reflexivity | split; [apply wpO | exact I] ] |].
      edestruct atomic_step as [EQk HVal]; try eassumption; subst K.
      rewrite fill_empty in *; subst ei.
      setoid_rewrite HSw'; setoid_rewrite HSw.
      rewrite HSw', HSw in Hφ; clear - HE He' Hφ HSub HVal.
      unfold wp in He'; rewrite fixp_eq in He'; fold (wp m') in He'.
      edestruct He' as [HV _]; [reflexivity | apply le_n | eassumption |].
      clear HE He'; specialize (HV HVal); destruct HV as [w' [r [s [HSw [Hφ' HE] ] ] ] ].
      eapply Hφ in Hφ'; [| assumption | apply Le.le_n_Sn | apply unit_min].
      clear Hφ; edestruct Hφ' with (mf := mask_emp) as [w'' [r' [s' [HSw' [Hφ HE'] ] ] ] ];
        [reflexivity | apply le_n | intros j; tauto |
         eapply erasure_equiv, HE; try reflexivity; unfold mask_emp, const; intros j; tauto |].
      clear Hφ' HE; exists w'' r' s'; split;
      [etransitivity; eassumption | split; [| eapply erasure_equiv, HE'; try reflexivity; unfold mask_emp, const; intros j; tauto] ].
      clear - Hφ; unfold wp; rewrite fixp_eq; fold (wp m).
      intros w; intros; split; [intros HVal' | split; intros; exfalso].
      - do 3 eexists; split; [reflexivity | split; [| eassumption] ].
        unfold lt in HLt; rewrite HLt, <- HSw.
        eapply φ, Hφ; [| apply le_n]; simpl; reflexivity.
      - eapply values_stuck; eassumption.
      - clear - HDec HVal; subst; assert (HT := fill_value _ _ HVal); subst.
        rewrite fill_empty in HVal; now apply fork_not_value in HVal.
    Qed.

    (** Framing **)

    Lemma htFrame m P R e φ :
      ht m P e φ ⊑ ht m (P * R) e (lift_bin sc φ (umconst R)).
    Proof.
      intros w n rz He w' HSw n' r HLe _ [r1 [r2 [EQr [HP HLR] ] ] ].
      specialize (He _ HSw _ _ HLe (unit_min _) HP).
      clear P w n rz HSw HLe HP; rename w' into w; rename n' into n.
      revert e w r1 r EQr HLR He; induction n using wf_nat_ind; intros; rename H into IH.
      unfold wp; rewrite fixp_eq; fold (wp m); intros w'; intros.
      unfold wp in He; rewrite fixp_eq in He; fold (wp m) in He.
      rewrite <- EQr, <- assoc in HE; edestruct He as [HV [HS HF] ]; try eassumption; [].
      clear He; split; [intros HVal; clear HS HF IH HE | split; intros; [clear HV HF HE | clear HV HS HE] ].
      - specialize (HV HVal); destruct HV as [w'' [r1' [s' [HSw' [Hφ HE] ] ] ] ].
        rewrite assoc in HE; destruct (Some r1' · Some r2) as [r' |] eqn: EQr';
        [| eapply erasure_not_empty in HE; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        do 3 eexists; split; [eassumption | split; [| eassumption] ].
        exists r1' r2; split; [now rewrite EQr' | split; [assumption |] ].
        unfold lt in HLt; rewrite HLt, <- HSw', <- HSw; apply HLR.
      - edestruct HS as [w'' [r1' [s' [HSw' [He HE] ] ] ] ]; try eassumption; []; clear HS.
        destruct k as [| k]; [exists w' r1' s'; split; [reflexivity | split; [apply wpO | exact I] ] |].
        rewrite assoc in HE; destruct (Some r1' · Some r2) as [r' |] eqn: EQr';
        [| eapply erasure_not_empty in HE; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        do 3 eexists; split; [eassumption | split; [| eassumption] ].
        eapply IH; try eassumption; [rewrite <- EQr'; reflexivity |].
        unfold lt in HLt; rewrite Le.le_n_Sn, HLt, <- HSw', <- HSw; apply HLR.
      - specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [s' [HSw' [HWF [HWR HE] ] ] ] ] ] ].
        destruct k as [| k]; [exists w' rfk rret s'; split; [reflexivity | split; [apply wpO | split; [apply wpO | exact I] ] ] |].
        rewrite assoc, <- (assoc (Some rfk)) in HE; destruct (Some rret · Some r2) as [rret' |] eqn: EQrret;
        [| eapply erasure_not_empty in HE; [contradiction | now erewrite (comm _ 0), !pcm_op_zero by apply _] ].
        do 4 eexists; split; [eassumption | split; [| split; eassumption] ].
        eapply IH; try eassumption; [rewrite <- EQrret; reflexivity |].
        unfold lt in HLt; rewrite Le.le_n_Sn, HLt, <- HSw', <- HSw; apply HLR.
    Qed.

    Lemma htAFrame m P R e φ
          (HAt : atomic e) :
      ht m P e φ ⊑ ht m (P * ▹ R) e (lift_bin sc φ (umconst R)).
    Proof.
      intros w n rz He w' HSw n' r HLe _ [r1 [r2 [EQr [HP HLR] ] ] ].
      specialize (He _ HSw _ _ HLe (unit_min _) HP).
      clear rz n HLe; unfold wp; rewrite fixp_eq; fold (wp m).
      clear w HSw; rename n' into n; rename w' into w; intros w'; intros.
      split; [intros; exfalso | split; intros; [| exfalso] ].
      - contradiction (atomic_not_value e).
      - destruct k as [| k];
        [exists w' r s; split; [reflexivity | split; [apply wpO | exact I] ] |].
        unfold wp in He; rewrite fixp_eq in He; fold (wp m) in He.
        rewrite <- EQr, <- assoc in HE.
        edestruct He as [_ [HeS _] ]; try eassumption; [].
        edestruct HeS as [w'' [r1' [s' [HSw' [He' HE'] ] ] ] ]; try eassumption; [].
        clear HE He HeS; rewrite assoc in HE'.
        destruct (Some r1' · Some r2) as [r' |] eqn: EQr';
          [| eapply erasure_not_empty in HE';
             [contradiction | now erewrite !pcm_op_zero by apply _] ].
        do 3 eexists; split; [eassumption | split; [| eassumption] ].
        edestruct atomic_step as [EQK HVal]; try eassumption; []; subst K.
        unfold lt in HLt; rewrite <- HLt, HSw, HSw' in HLR; simpl in HLR.
        clear - He' HVal EQr' HLR; rename w'' into w.
        unfold wp; rewrite fixp_eq; fold (wp m); intros w'; intros.
        split; [intros HVal' | split; intros; exfalso].
        + unfold wp in He'; rewrite fixp_eq in He'; fold (wp m) in He'.
          rewrite <- EQr', <- assoc in HE; edestruct He' as [HV _]; try eassumption; [].
          revert HVal'; rewrite fill_empty in *; intros; specialize (HV HVal').
          destruct HV as [w'' [r1'' [s'' [HSw' [Hφ HE'] ] ] ] ].
          rewrite assoc in HE'; destruct (Some r1'' · Some r2) as [r'' |] eqn: EQr'';
          [| eapply erasure_not_empty in HE';
             [contradiction | now erewrite !pcm_op_zero by apply _] ].
          do 3 eexists; split; [eassumption | split; [| eassumption] ].
          exists r1'' r2; split; [now rewrite EQr'' | split; [assumption |] ].
          unfold lt in HLt; rewrite <- HLt, HSw, HSw' in HLR; apply HLR.
        + rewrite fill_empty in HDec; eapply values_stuck; eassumption.
        + rewrite fill_empty in HDec; subst; clear -HVal.
          assert (HT := fill_value _ _ HVal); subst K; rewrite fill_empty in HVal.
          contradiction (fork_not_value e').
      - subst; clear -HAt; eapply fork_not_atomic; eassumption.
    Qed.

    (** Fork **)

    Lemma htFork m P R e :
      ht m P e (umconst ⊤) ⊑ ht m (P * ▹ R) (fork e) (lift_bin sc (eqV (exist _ fork_ret fork_ret_is_value)) (umconst R)).
    Proof.
      intros w n rz He w' HSw n' r HLe _ [r1 [r2 [EQr [HP HLR] ] ] ].
      specialize (He _ HSw _ _ HLe (unit_min _) HP).
      clear rz n HLe; unfold wp; rewrite fixp_eq; fold (wp m).
      clear w HSw; rename n' into n; rename w' into w; intros w'; intros.
      split; [intros; contradiction (fork_not_value e) | split; intros; [exfalso |] ].
      - assert (HT := fill_fork _ _ _ HDec); subst K; rewrite fill_empty in HDec; subst.
        eapply fork_stuck with (K := ε); [| eassumption]; reflexivity.
      - assert (HT := fill_fork _ _ _ HDec); subst K; rewrite fill_empty in HDec.
        apply fork_inj in HDec; subst e'; rewrite <- EQr in HE.
        unfold lt in HLt; rewrite <- HLt, <- Le.le_n_Sn, HSw in He.
        rewrite <- Le.le_n_Sn in HE.
        do 4 eexists; split; [reflexivity | split; [| split; eassumption] ].
        rewrite fill_empty; unfold wp; rewrite fixp_eq; fold (wp m).
        rewrite <- HLt, HSw in HLR; simpl in HLR.
        clear - HLR; intros w''; intros; split; [intros | split; intros; exfalso].
        + do 3 eexists; split; [reflexivity | split; [| eassumption] ].
          exists (pcm_unit _) r2; split; [now erewrite pcm_op_unit by apply _ |].
          split; [| unfold lt in HLt; rewrite <- HLt, HSw in HLR; apply HLR].
          simpl; reflexivity.
        + eapply values_stuck; eassumption || exact fork_ret_is_value.
        + assert (HV := fork_ret_is_value); rewrite HDec in HV; clear HDec.
          assert (HT := fill_value _ _ HV);subst K; rewrite fill_empty in HV.
          eapply fork_not_value; eassumption.
    Qed.

    (** Not stated: the Shift (timeless) rule *)

  End HoareTripleProperties.

End Iris.
