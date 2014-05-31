Require Import world_prop core_lang lang masks.
Require Import RecDom.PCM RecDom.UPred RecDom.BI RecDom.PreoMet RecDom.Finmap.

Module Iris (RP RL : PCM_T) (C : CORE_LANG RP).

  Module Import L  := Lang RP RL C.
  Module R <: PCM_T.
    Definition res := (RP.res * RL.res)%type.
    Instance res_op   : PCM_op res := _.
    Instance res_unit : PCM_unit res := _.
    Instance res_pcm  : PCM res := _.
  End R.
  Module Import WP := WorldProp R.

  Definition res := option R.res.

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
      n[(fun p => m[(fun w => mkUPred (fun n r => p w n 1%pcm) _)])].
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

    Program Definition intEq (t1 t2 : T) : Props := pcmconst (intEqP t1 t2).

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

  (** Ownership **)
  Definition own (r : res) : Props :=
    pcmconst (up_cr (pord r)).

  Definition injFst (r : option RP.res) : res :=
    option_map (fun r => (r, pcm_unit _)) r.
  Definition injSnd (r : option RL.res) : res :=
    option_map (fun r => (pcm_unit _, r)) r.

  (** Physical part **)
  Definition ownP (r : RP.res) : Props :=
    own (injFst (Some r)).

  (** Logical part **)
  Definition ownL (r : RL.res) : Props :=
    own (injSnd (Some r)).

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

  Section Erasure.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.
    Local Instance eqRes : Setoid res := discreteType.

    (* First, we need to erase a finite map. This won't be pretty, for
       now, since the library does not provide enough
       constructs. Hopefully we can provide a fold that'd work for
       that at some point
     *)
    Fixpoint comp_list (xs : list res) : res :=
      match xs with
        | nil => 1
        | (x :: xs)%list => x · comp_list xs
      end.

    Definition cod (m : nat -f> res) : list res := List.map snd (findom_t m).
    Definition erase (m : nat -f> res) : res := comp_list (cod m).

    Lemma erase_remove (rs : nat -f> res) i r (HLu : rs i = Some r) :
      erase rs = r · erase (fdRemove i rs).
    Proof.
      destruct rs as [rs rsP]; unfold erase, cod, findom_f in *; simpl in *.
      induction rs as [| [j s] ]; [discriminate |]; simpl in *.
      destruct (comp i j); [inversion HLu; reflexivity | discriminate |].
      simpl; rewrite IHrs by eauto using SS_tail.
      rewrite !assoc; f_equal; rewrite comm; reflexivity.
    Qed.

    Lemma erase_insert_new (rs : nat -f> res) i r (HNLu : rs i = None) :
      r · erase rs = erase (fdUpdate i r rs).
    Proof.
      destruct rs as [rs rsP]; unfold erase, cod, findom_f in *; simpl in *.
      induction rs as [| [j s] ]; simpl in *; [reflexivity |].
      destruct (comp i j); [discriminate | reflexivity |].
      simpl; rewrite <- IHrs by eauto using SS_tail.
      rewrite !assoc; f_equal; rewrite comm; reflexivity.
    Qed.

    Lemma erase_insert_old (rs : nat -f> res) i r1 r2 (HLu : rs i = Some r1) :
      r2 · erase rs = erase (fdUpdate i (r1 · r2) rs).
    Proof.
      destruct rs as [rs rsP]; unfold erase, cod, findom_f in *; simpl in *.
      induction rs as [| [j s] ]; [discriminate |]; simpl in *.
      destruct (comp i j); [inversion HLu; subst; clear HLu | discriminate |].
      - simpl; rewrite assoc, (comm r2); reflexivity.
      - simpl; rewrite <- IHrs by eauto using SS_tail.
        rewrite !assoc, (comm r2); reflexivity.
    Qed.

    Global Instance preo_unit : preoType () := disc_preo ().

    (* XXX: logical state omitted, since it looks weird. Also, later over the whole deal. *)
    Program Definition erasure (σ : state) (m : mask) (r s : res) (w : Wld) : UPred () :=
      ▹ (mkUPred (fun n _ =>
                    erase_state (option_map fst (r · s)) σ
                    /\ exists rs : nat -f> res,
                         erase rs = s /\
                         forall i (Hm : m i),
                           (i ∈ dom rs <-> i ∈ dom w) /\
                           forall π ri (HLw : w i == Some π) (HLrs : rs i == Some ri),
                             ı π w n ri) _).
    Next Obligation.
      intros n1 n2 _ _ HLe _ [HES HRS]; split; [assumption |].
      setoid_rewrite HLe; eassumption.
    Qed.

    Global Instance erasure_equiv σ : Proper (meq ==> eq ==> eq ==> equiv ==> equiv) (erasure σ).
    Proof.
      intros m1 m2 EQm r r' EQr s s' EQs w1 w2 EQw [| n] []; [reflexivity |]; subst r' s'.
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
    Local Existing Instance eqRes.

    Program Definition preVS (m1 m2 : mask) (p : Props) (w : Wld) : UPred res :=
      mkUPred (fun n r => forall w1 s rf mf σ k (HSub : w ⊑ w1) (HLe : k <= n)
                                 (HGt : k > 0) (HD : mf # m1 ∪ m2)
                                 (HE : erasure σ (m1 ∪ mf) (r · rf) s w1 @ k),
                          exists w2 r' s', w1 ⊑ w2 /\ p w2 k r' /\
                                           erasure σ (m2 ∪ mf) (r' · rf) s' w2 @ k) _.
    Next Obligation.
      intros n1 n2 r1 r2 HLe [rd HR] HP; intros.
      destruct (HP w1 s (rd · rf) mf σ k) as [w2 [r1' [s' [HW [HP' HE'] ] ] ] ]; try assumption; [| |].
      - etransitivity; eassumption.
      - rewrite assoc, (comm r1), HR; assumption.
      - exists w2 (rd · r1') s'; split; [assumption | split].
        + eapply uni_pred, HP'; [| eexists]; reflexivity.
        + rewrite (comm rd), <- assoc; assumption.
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
          exists (extend w1'' w2') r' s'; repeat split; [assumption | |].
          * eapply (met_morph_nonexp _ _ p), HP ; [symmetry; eassumption | now eauto with arith].
          * eapply erasure_dist, HE'; [symmetry; eassumption | now eauto with arith].
      - assert (HDE := extend_dist _ _ _ _ EQw HSub); assert (HSE := extend_sub _ _ _ _ EQw HSub); specialize (HP (extend w2' w2)).
        edestruct HP as [w1'' [r' [s' [HW HH] ] ] ]; try eassumption; clear HP; [ | ].
        + eapply erasure_dist, HE; [symmetry; eassumption | now eauto with arith].
        + symmetry in HDE; assert (HDE' := extend_dist _ _ _ _ HDE HW).
          assert (HSE' := extend_sub _ _ _ _ HDE HW); destruct HH as [HP HE'];
          exists (extend w1'' w2') r' s'; repeat split; [assumption | |].
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
        clear HP; repeat eexists; try eassumption; [].
        apply EQp; [now eauto with arith | assumption].
      - edestruct HP as [w2 [r' [s' [HW [HP' HE'] ] ] ] ]; try eassumption; [].
        clear HP; repeat eexists; try eassumption; [].
        apply EQp; [now eauto with arith | assumption].
    Qed.

    Definition vs (m1 m2 : mask) (p q : Props) : Props :=
      □ (p → pvs m1 m2 q).

  End ViewShifts.

  Section ViewShiftProps.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.
    Local Existing Instance eqRes.

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
      destruct k as [| k]; [now inversion HGt |].
      destruct HE as [HES [rs [HE HM] ] ].
      destruct (rs i) as [ri |] eqn: HLr.
      - exists w' (r · ri) (erase (fdRemove i rs)); split; [reflexivity | split; [| split] ].
        + simpl; eapply HInv; [now auto with arith |].
          specialize (HSub i); rewrite HLu in HSub.
          eapply uni_pred, HM with i; [| exists r | | | rewrite HLr]; try reflexivity; [|].
          * left; unfold mask_sing, mask_set.
            destruct (Peano_dec.eq_nat_dec i i); tauto.
          * symmetry; destruct (w' i); [assumption | contradiction].
        + rewrite <- assoc, (comm ri), assoc, <- (assoc _ ri), <- erase_remove, HE; assumption.
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

    (* XXX: move up *)
    Implicit Types (p q r : Props) (i : nat) (m : mask).

    Lemma vsClose i p :
      valid (vs mask_emp (mask_sing i) (inv i p * ▹ p) ⊤).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ [r1 [r2 [HR [HInv HP] ] ] ] w'; clear nn; intros.
      do 12 red in HInv; destruct (w i) as [μ |] eqn: HLu; [| contradiction].
      apply ı in HInv; rewrite (isoR p) in HInv.
      (* get rid of the invisible 1/2 *)
      do 8 red in HInv.
      destruct k as [| k]; [now inversion HGt |].
      destruct HE as [HES [rs [HE HM] ] ].
      exists w' 1 (r · s); split; [reflexivity | split; [exact I |] ].
      split; [erewrite pcm_op_unit, assoc, (comm rf) by apply _; assumption |].
      remember (match rs i with Some ri => ri | None => 1 end) as ri eqn: EQri.
      exists (fdUpdate i (ri · r) rs); split; intros.
      - clear -HE EQri; destruct (rs i) as [rsi |] eqn: EQrsi; subst;
        [erewrite erase_insert_old; [reflexivity | assumption] |].
        erewrite pcm_op_unit, erase_insert_new; [reflexivity | assumption | apply _].
      - specialize (HD i0); unfold mask_sing, mask_set in *; simpl in Hm, HD.
        destruct (Peano_dec.eq_nat_dec i i0); [subst i0; clear Hm | destruct Hm as [Hm | Hm]; [contradiction |] ].
        + split; intros.
          * specialize (HSub i); rewrite HLu in HSub.
            rewrite !fdLookup_in_strong, fdUpdate_eq; destruct (w' i);
            [intuition now eauto | contradiction].
          * rewrite fdUpdate_eq in HLrs; simpl in HLrs; subst ri0.
            destruct n as [| n]; [now inversion HLe |]; simpl in HP.
            rewrite <- HSub; specialize (HSub i); rewrite HLu in HSub.
            destruct (w' i) as [π' |]; [| contradiction]; simpl in HSub, HLw.
            rewrite <- HLw, <- HSub; apply HInv; [now auto with arith |].
            eapply uni_pred, HP; [now auto with arith |].
            subst r; rewrite assoc; eexists; reflexivity.
        + rewrite fdLookup_in_strong, fdUpdate_neq, <- fdLookup_in_strong by assumption.
          auto.
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
      clear HS; assert (HS : 1 ⊑ rq) by (exists rq; rewrite comm; apply pcm_op_unit, _).
      rewrite <- HLe, HSub in Hqr; specialize (Hqr _ HSw12); clear Hpq HE w HSub Hp.
      edestruct (Hqr k _ HLe0 HS Hq w2) as [w3 [rr [sr [HSw23 [Hr HEr] ] ] ] ];
        try (reflexivity || eassumption); [|].
      { (* XXX: possible lemma *)
        clear - HD HMS.
        intros j [Hmf Hm23]; apply (HD j); split; [assumption |].
        destruct Hm23 as [Hm2 | Hm3]; [apply HMS, Hm2 | right; assumption].
      }
      clear HEq Hq HS.
      setoid_rewrite HSw12; eauto 6.
    Qed.

    (* Warning: weak statement *)
    Lemma vsEnt p q m1 m2 (HEnt : p ⊑ q) :
      valid (vs m1 m2 p q).
    Proof.
    Admitted.

    Lemma vsFrame p q r m1 m2 mf (HDisj : mf # m1 ∪ m2) :
      vs m1 m2 p q ⊑ vs (m1 ∪ mf) (m2 ∪ mf) (p * r) (q * r).
    Proof.
      intros w' n r1 HVS w HSub; specialize (HVS _ HSub); clear w' r1 HSub.
      intros np rpr HLe _ [rp [rr [HR [Hp Hr] ] ] ] w'; intros.
      assert (HS : 1 ⊑ rp) by (exists rp; erewrite comm, pcm_op_unit by apply _; reflexivity).
      specialize (HVS _ _ HLe HS Hp w' s (rr · rf) (mf ∪ mf0) σ k); clear HS.
      destruct HVS as [w'' [rq [s' [HSub' [Hq HEq] ] ] ] ]; try assumption; [| |].
      - (* disjointness: possible lemma *)
        clear - HD HDisj; intros i [ [Hmf | Hmf] Hm12]; [eapply HDisj; now eauto |].
        eapply HD; split; [eassumption | tauto].
      - rewrite assoc, HR; eapply erasure_equiv, HE; try reflexivity; [].
        clear; intros i; tauto.
      - exists w'' (rq · rr) s'; split; [assumption | split].
        + rewrite HSub, HSub', <- HLe0 in Hr; exists rq rr; now auto.
        + rewrite <- assoc; eapply erasure_equiv, HEq; try reflexivity; [].
          clear; intros i; tauto.
    Qed.

    Lemma vsFalse m1 m2 :
      valid (vs m1 m2 ⊥ ⊥).
    Proof.
      intros pw nn r w _; clear r pw.
      intros n r _ _ HB; contradiction.
    Qed.

    (* XXX missing statements: NewInv, NewGhost, GhostUpd, VSTimeless *)

  End ViewShiftProps.

  Section HoareTriples.
  (* Quadruples, really *)
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.
    Local Open Scope lang_scope.
    Local Existing Instance eqRes.

    Global Instance expr_type : Setoid expr := discreteType.
    Global Instance expr_metr : metric expr := discreteMetric.

    Implicit Types (P Q R : Props) (i : nat) (m : mask) (e : expr) (w : Wld) (φ : value -n> Props) (r : res).

    Local Obligation Tactic := intros; eauto with typeclass_instances.

    Definition wpFP m (WP : expr -n> (value -n> Props) -n> Props) e φ w n r :=
      forall w' k s rf σ (HSw : w ⊑ w') (HLt : k < n)
             (HE : erasure σ m (r · rf) s w' @ S k),
        (forall (HV : is_value e),
         exists w'' r' s', w' ⊑ w'' /\ φ (exist _ e HV) w'' (S k) r'
                           /\ erasure σ m (r' · rf) s' w'' @ S k) /\
        (forall σ' ei ei' K (HDec : e = K [[ ei ]])
                (HStep : prim_step (ei, σ) (ei', σ')),
         exists w'' r' s', w' ⊑ w'' /\ WP (K [[ ei' ]]) φ w'' k r'
                           /\ erasure σ' m (r' · rf) s' w'' @ k) /\
        (forall e' K (HDec : e = K [[ e' ]]),
         exists w'' rfk rret s', w' ⊑ w'' /\ erasure σ m (rfk · rret · rf) s' w'' @ k
                                 /\ WP (K [[ fork_ret ]]) φ w'' k rret
                                 /\ WP e' (umconst ⊤) w'' k rfk).

    Program Definition wpF m : (expr -n> (value -n> Props) -n> Props) -n> expr -n> (value -n> Props) -n> Props :=
      n[(fun WP => n[(fun e => n[(fun φ => m[(fun w => mkUPred (wpFP m WP e φ w) _)])])])].
    Next Obligation.
      intros n1 n2 r1 r2 HLe [rd EQr] Hp w' k s rf σ HSw HLt HE.
      specialize (Hp w' k s (rd · rf) σ); destruct Hp as [HV [HS HF] ];
      [assumption | now eauto with arith | rewrite assoc, (comm r1), EQr; assumption |].
      split; [clear HS HF | split; [clear HV HF | clear HV HS] ]; intros.
      - specialize (HV HV0); destruct HV as [w'' [r' [s' [HSw' [Hφ HE'] ] ] ] ];
        exists w'' (r' · rd) s'; split; [assumption | split; [| rewrite <- assoc; assumption] ].
        eapply uni_pred, Hφ; [reflexivity | eexists; rewrite comm; reflexivity].
      - specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [s' [HSw' [HWP HE'] ] ] ] ];
        exists w'' (r' · rd) s'; split; [assumption | split; [| rewrite <- assoc; assumption] ].
        eapply uni_pred, HWP; [reflexivity | eexists; rewrite comm; reflexivity].
      - specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [s' [HSw' [HE' [HWR HWF] ] ] ] ] ] ];
        exists w'' rfk (rret · rd) s'; split; [assumption | split; [| split] ].
        + rewrite assoc in HE'; rewrite assoc; assumption.
        + eapply uni_pred, HWR; [reflexivity | eexists; rewrite comm; reflexivity].
        + assumption.
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
        + specialize (HF _ _ HDec); destruct HF as [w1'' [rfk [rret [s' [HSw'' [HE' [HWR HWF] ] ] ] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') rfk rret s'; split; [assumption |].
          split; [eapply erasure_dist, HE'; [eassumption | now eauto with arith] |].
          split; eapply (met_morph_nonexp _ _ (WP _ _)); try eassumption; now eauto with arith.
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
        + specialize (HF _ _ HDec); destruct HF as [w1'' [rfk [rret [s' [HSw'' [HE' [HWR HWF] ] ] ] ] ] ].
          assert (EQw'' := extend_dist _ _ _ _ EQw' HSw''); symmetry in EQw'';
          assert (HSw''' := extend_sub _ _ _ _ EQw' HSw'').
          exists (extend w1'' w2') rfk rret s'; split; [assumption |].
          split; [eapply erasure_dist, HE'; [eassumption | now eauto with arith] |].
          split; eapply (met_morph_nonexp _ _ (WP _ _)); try eassumption; now eauto with arith.
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
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [s' [HSw' [HE' [HWR HWF] ] ] ] ] ] ].
          exists w'' rfk rret s'; repeat (split; try assumption); [].
          eapply (met_morph_nonexp _ _ (WP _)), HWR; [symmetry; eassumption | now eauto with arith].
      - split; [| split]; intros.
        + clear HS HF; specialize (HV HV0); destruct HV as [w'' [r' [s' [HSw' [Hφ HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          apply EQφ, Hφ; now eauto with arith.
        + clear HV HF; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [s' [HSw' [Hφ HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          eapply (met_morph_nonexp _ _ (WP _)), Hφ; [eassumption | now eauto with arith].
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [s' [HSw' [HE' [HWR HWF] ] ] ] ] ] ].
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
        + clear HF HS; specialize (HV _ _ HDec); destruct HV as [w'' [rfk [rret [s' [HSw' [HE' [HWR HWF] ] ] ] ] ] ].
          exists w'' rfk rret s'; split; [assumption | split; [assumption |] ].
          split; eapply EQWP; try eassumption; now eauto with arith.
      - split; [assumption | split; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [s' [HSw' [HWP HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          eapply (EQWP _ _ _), HWP; now eauto with arith.
        + clear HF HS; specialize (HV _ _ HDec); destruct HV as [w'' [rfk [rret [s' [HSw' [HE' [HWR HWF] ] ] ] ] ] ].
          exists w'' rfk rret s'; split; [assumption | split; [assumption |] ].
          split; eapply EQWP; try eassumption; now eauto with arith.
    Qed.

    Instance contr_wpF m : contractive (wpF m).
    Proof.
      intros n WP1 WP2 EQWP e φ w k r HLt.
      split; intros Hp w'; intros; edestruct Hp as [HV [HS HF] ]; try eassumption; [|].
      - split; [assumption | split; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [s' [HSw' [HWP HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          eapply EQWP, HWP; now eauto with arith.
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [s' [HSw' [HE' [HWR HWF] ] ] ] ] ] ].
          exists w'' rfk rret s'; split; [assumption | split; [assumption |] ].
          split; eapply EQWP; try eassumption; now eauto with arith.
      - split; [assumption | split; intros].
        + clear HF HV; specialize (HS _ _ _ _ HDec HStep); destruct HS as [w'' [r' [s' [HSw' [HWP HE'] ] ] ] ].
          exists w'' r' s'; split; [assumption | split; [| assumption] ].
          eapply EQWP, HWP; now eauto with arith.
        + clear HV HS; specialize (HF _ _ HDec); destruct HF as [w'' [rfk [rret [s' [HSw' [HE' [HWR HWF] ] ] ] ] ] ].
          exists w'' rfk rret s'; split; [assumption | split; [assumption |] ].
          split; eapply EQWP; try eassumption; now eauto with arith.
    Qed.

    Definition wp m : expr -n> (value -n> Props) -n> Props :=
      fixp (wpF m) (umconst (umconst ⊤)).

    Definition ht m P e φ := □ (P → wp m e φ).

  End HoareTriples.

End Iris.
