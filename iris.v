Require Import world_prop core_lang lang masks.
Require Import RecDom.PCM RecDom.UPred RecDom.BI RecDom.PreoMet RecDom.Finmap.

Module Iris (RL : PCM_T) (C : CORE_LANG).

  Module Import L  := Lang C.
  Module Import R <: PCM_T.
    Definition res := (pcm_res_ex state * RL.res)%type.
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

  Lemma valid_iff p :
    valid p <-> (⊤ ⊑ p).
  Proof.
    split; intros Hp.
    - intros w n r _; apply Hp.
    - intros w n r; apply Hp; exact I.
  Qed.

  (** Ownership **)
  Definition ownR (r : res) : Props :=
    pcmconst (up_cr (pord r)).

  (** Physical part **)
  Definition ownRP (r : pcm_res_ex state) : Props :=
    ownR (r, pcm_unit _).

  (** Logical part **)
  Definition ownRL (r : RL.res) : Props :=
    ownR (pcm_unit _, r).

  (** Proper physical state: ownership of the machine state **)
  Instance state_type : Setoid state := discreteType.
  Instance state_metr : metric state := discreteMetric.
  Instance state_cmetr : cmetric state := discreteCMetric.

  Program Definition ownS : state -n> Props :=
    n[(fun s => ownRP (ex_own _ s))].
  Next Obligation.
    intros r1 r2 EQr. hnf in EQr. now rewrite EQr.
  Qed.
  Next Obligation.
    intros r1 r2 EQr; destruct n as [| n]; [apply dist_bound |].
    simpl in EQr. subst; reflexivity.
  Qed.

  (** Proper ghost state: ownership of logical w/ possibility of undefined **)
  Lemma ores_equiv_eq T `{pcmT : PCM T} (r1 r2 : option T) (HEq : r1 == r2) : r1 = r2.
  Proof.
    destruct r1 as [r1 |]; destruct r2 as [r2 |]; try contradiction;
    simpl in HEq; subst; reflexivity.
  Qed.

  Instance logR_metr : metric RL.res := discreteMetric.
  Instance logR_cmetr : cmetric RL.res := discreteCMetric.

  Program Definition ownL : (option RL.res) -n> Props :=
    n[(fun r => match r with
                  | Some r => ownRL r
                  | None => ⊥
                end)].
  Next Obligation.
    intros r1 r2 EQr; apply ores_equiv_eq in EQr; now rewrite EQr.
  Qed.
  Next Obligation.
    intros r1 r2 EQr; destruct n as [| n]; [apply dist_bound |].
    destruct r1 as [r1 |]; destruct r2 as [r2 |]; try contradiction; simpl in EQr; subst; reflexivity.
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

  Lemma box_top : ⊤ == □ ⊤.
  Proof.
    intros w n r; simpl; unfold const; reflexivity.
  Qed.

  (** Ghost state ownership **)
  Lemma ownL_sc (u t : option RL.res) :
    ownL (u · t)%pcm == ownL u * ownL t.
  Proof.
    intros w n r; split; [intros Hut | intros [r1 [r2 [EQr [Hu Ht] ] ] ] ].
    - destruct (u · t)%pcm as [ut |] eqn: EQut; [| contradiction].
      do 15 red in Hut; rewrite <- Hut.
      destruct u as [u |]; [| now erewrite pcm_op_zero in EQut by apply _].
      assert (HT := comm (Some u) t); rewrite EQut in HT.
      destruct t as [t |]; [| now erewrite pcm_op_zero in HT by apply _]; clear HT.
      exists (pcm_unit (pcm_res_ex state), u) (pcm_unit (pcm_res_ex state), t).
      split; [unfold pcm_op, res_op, pcm_op_prod | split; do 15 red; reflexivity].
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

  (** Timeless *)

  Definition timelessP (p : Props) w n :=
    forall w' k r (HSw : w ⊑ w') (HLt : k < n) (Hp : p w' k r), p w' (S k) r.

  Program Definition timeless (p : Props) : Props :=
    m[(fun w => mkUPred (fun n r => timelessP p w n) _)].
  Next Obligation.
    intros n1 n2 _ _ HLe _ HT w' k r HSw HLt Hp; eapply HT, Hp; [eassumption |].
    now eauto with arith.
  Qed.
  Next Obligation.
    intros w1 w2 EQw n rr; simpl; split; intros HT k r HLt;
    [rewrite <- EQw | rewrite EQw]; apply HT; assumption.
  Qed.
  Next Obligation.
    intros w1 w2 EQw k; simpl; intros _ HLt; destruct n as [| n]; [now inversion HLt |].
    split; intros HT w' m r HSw HLt' Hp.
    - symmetry in EQw; assert (HD := extend_dist _ _ _ _ EQw HSw); assert (HS := extend_sub _ _ _ _ EQw HSw).
      apply (met_morph_nonexp _ _ p) in HD; apply HD, HT, HD, Hp; now (assumption || eauto with arith).
    - assert (HD := extend_dist _ _ _ _ EQw HSw); assert (HS := extend_sub _ _ _ _ EQw HSw).
      apply (met_morph_nonexp _ _ p) in HD; apply HD, HT, HD, Hp; now (assumption || eauto with arith).
  Qed.
  Next Obligation.
    intros w1 w2 HSw n; simpl; intros _ HT w' m r HSw' HLt Hp.
    eapply HT, Hp; [etransitivity |]; eassumption.
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

    Definition erase_state (r: option res) σ: Prop := match r with
    | Some (ex_own s, _) => s = σ
    | _ => False
    end.

    Global Instance preo_unit : preoType () := disc_preo ().

    Program Definition erasure (σ : state) (m : mask) (r s : option res) (w : Wld) : UPred () :=
      ▹ (mkUPred (fun n _ =>
                    erase_state (r · s) σ
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

    Lemma erasure_not_empty σ m r s w k (HN : r · s == 0) :
      ~ erasure σ m r s w (S k) tt.
    Proof.
      intros [HD _]; apply ores_equiv_eq in HN; setoid_rewrite HN in HD.
      exact HD.
    Qed.

  End Erasure.

  Notation " p @ k " := ((p : UPred ()) k tt) (at level 60, no associativity).

  Section ViewShifts.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Obligation Tactic := intros.

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

    Lemma vsTimeless m p :
      timeless p ⊑ vs m m (▹ p) p.
    Proof.
      intros w' n r1 HTL w HSub; rewrite HSub in HTL; clear w' HSub.
      intros np rp HLe HS Hp w1; intros.
      exists w1 rp s; split; [reflexivity | split; [| assumption] ]; clear HE HD.
      destruct np as [| np]; [now inversion HLe0 |]; simpl in Hp.
      unfold lt in HLe0; rewrite HLe0.
      rewrite <- HSub; apply HTL, Hp; [reflexivity | assumption].
    Qed.

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
          [| erewrite !pcm_op_zero in HES by apply _; now contradiction].
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
        by (eapply ores_equiv_eq; rewrite assoc, (comm rf); reflexivity).
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
        clear - HE HES EQrsi EQR.
        assert (HH : rf · (Some r · s) = 0); [clear HES | rewrite HH in HES; contradiction].
        eapply ores_equiv_eq; rewrite <- HE, erase_remove by eassumption.
        rewrite (assoc (Some r)), (comm (Some r)), EQR, comm.
        erewrite !pcm_op_zero by apply _; reflexivity.
    Qed.

    Lemma vsTrans p q r m1 m2 m3 (HMS : m2 ⊆ m1 ∪ m3) :
      vs m1 m2 p q ∧ vs m2 m3 q r ⊑ vs m1 m3 p r.
    Proof.
      intros w' n r1 [Hpq Hqr] w HSub; specialize (Hpq _ HSub); rewrite HSub in Hqr; clear w' HSub.
      intros np rp HLe HS Hp w1; intros; specialize (Hpq _ _ HLe HS Hp).
      edestruct Hpq as [w2 [rq [sq [HSw12 [Hq HEq] ] ] ] ]; try eassumption; [|].
      { clear - HD HMS; intros j [Hmf Hm12]; apply (HD j); split; [assumption |].
        destruct Hm12 as [Hm1 | Hm2]; [left; assumption | apply HMS, Hm2].
      }
      clear HS; assert (HS : pcm_unit _ ⊑ rq) by (exists rq; now erewrite comm, pcm_op_unit by apply _).
      rewrite <- HLe, HSub in Hqr; specialize (Hqr _ HSw12); clear Hpq HE w HSub Hp.
      edestruct (Hqr (S k) _ HLe0 HS Hq w2) as [w3 [rR [sR [HSw23 [Hr HEr] ] ] ] ];
        try (reflexivity || eassumption); [now auto with arith | |].
      { clear - HD HMS; intros j [Hmf Hm23]; apply (HD j); split; [assumption |].
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

    Instance LP_optres (P : option RL.res -> Prop) : LimitPreserving P.
    Proof.
      intros σ σc HPc; simpl; unfold option_compl.
      generalize (@eq_refl _ (σ 1%nat)).
      pattern (σ 1%nat) at 1 3; destruct (σ 1%nat); [| intros HE; rewrite HE; apply HPc].
      intros HE; simpl; unfold discreteCompl, unSome.
      generalize (@eq_refl _ (σ 2)); pattern (σ 2) at 1 3; destruct (σ 2).
      + intros HE'; rewrite HE'; apply HPc.
      + intros HE'; exfalso; specialize (σc 1 1 2)%nat.
        rewrite <- HE, <- HE' in σc; contradiction σc; auto with arith.
    Qed.

    Definition ownLP (P : option RL.res -> Prop) : {s : option RL.res | P s} -n> Props :=
      ownL <M< inclM.

Lemma pcm_op_split rp1 rp2 rp sp1 sp2 sp :
  Some (rp1, sp1) · Some (rp2, sp2) == Some (rp, sp) <->
  Some rp1 · Some rp2 == Some rp /\ Some sp1 · Some sp2 == Some sp.
Proof.
  unfold pcm_op at 1, res_op at 2, pcm_op_prod at 1.
  destruct (Some rp1 · Some rp2) as [rp' |]; [| simpl; tauto].
  destruct (Some sp1 · Some sp2) as [sp' |]; [| simpl; tauto].
  simpl; split; [| intros [EQ1 EQ2]; subst; reflexivity].
  intros EQ; inversion EQ; tauto.
Qed.

    Lemma vsGhostUpd m rl (P : option RL.res -> Prop)
          (HU : forall rf (HD : rl · rf <> None), exists sl, P sl /\ sl · rf <> None) :
      valid (vs m m (ownL rl) (xist (ownLP P))).
    Proof.
      unfold ownLP; intros _ _ _ w _ n [rp' rl'] _ _ HG w'; intros.
      destruct rl as [rl |]; simpl in HG; [| contradiction].
      destruct HG as [ [rdp rdl] EQr]; rewrite pcm_op_split in EQr; destruct EQr as [EQrp EQrl].
      erewrite comm, pcm_op_unit in EQrp by apply _; simpl in EQrp; subst rp'.
      destruct (Some (rdp, rl') · rf · s) as [t |] eqn: EQt;
        [| destruct HE as [HES _]; setoid_rewrite EQt in HES; contradiction].
      assert (EQt' : Some (rdp, rl') · rf · s == Some t) by (rewrite EQt; reflexivity).
      clear EQt; rename EQt' into EQt.
      destruct rf as [ [rfp rfl] |]; [| now erewrite (comm _ 0), !pcm_op_zero in EQt by apply _].
      destruct s as [ [sp sl] |]; [| now erewrite (comm _ 0), pcm_op_zero in EQt by apply _].
      destruct (Some (rdp, rl') · Some (rfp, rfl)) as [ [rdfp rdfl] |] eqn: EQdf;
        setoid_rewrite EQdf in EQt; [| now erewrite pcm_op_zero in EQt by apply _].
      destruct (HU (Some rdl · Some rfl · Some sl)) as [rsl [HPrsl HCrsl] ].
      - intros HEq; destruct t as [tp tl]; apply pcm_op_split in EQt; destruct EQt as [_ EQt].
        assert (HT : Some (rdp, rl') · Some (rfp, rfl) == Some (rdfp, rdfl)) by (rewrite EQdf; reflexivity); clear EQdf.
        apply pcm_op_split in HT; destruct HT as [_ EQdf].
        now rewrite <- EQdf, <- EQrl, (comm (Some rdl)), <- (assoc (Some rl)), <- assoc, HEq in EQt.
      - destruct (rsl · Some rdl) as [rsl' |] eqn: EQrsl;
        [| contradiction HCrsl; eapply ores_equiv_eq; now erewrite !assoc, EQrsl, !pcm_op_zero by apply _ ].
        exists w' (rdp, rsl') (Some (sp, sl)); split; [reflexivity | split].
        + exists (exist _ rsl HPrsl); destruct rsl as [rsl |];
          [simpl | now erewrite pcm_op_zero in EQrsl by apply _].
          exists (rdp, rdl); rewrite pcm_op_split.
          split; [now erewrite comm, pcm_op_unit by apply _ | now rewrite comm, EQrsl].
        + destruct HE as [HES HEL]; split; [| assumption]; clear HEL.
          assert (HT := ores_equiv_eq _ _ _ EQt); setoid_rewrite EQdf in HES;
          setoid_rewrite HT in HES; clear HT; destruct t as [tp tl].
          destruct (rsl · (Some rdl · Some rfl · Some sl)) as [tl' |] eqn: EQtl;
          [| now contradiction HCrsl]; clear HCrsl.
          assert (HT : Some (rdp, rsl') · Some (rfp, rfl) · Some (sp, sl) = Some (tp, tl')); [| setoid_rewrite HT; apply HES].
          rewrite <- EQdf, <- assoc in EQt; clear EQdf; eapply ores_equiv_eq; rewrite <- assoc.
          destruct (Some (rfp, rfl) · Some (sp, sl)) as [ [up ul] |] eqn: EQu;
            setoid_rewrite EQu in EQt; [| now erewrite comm, pcm_op_zero in EQt by apply _].
          apply pcm_op_split in EQt; destruct EQt as [EQt _]; apply pcm_op_split; split; [assumption |].
          assert (HT : Some rfl · Some sl == Some ul);
            [| now rewrite <- EQrsl, <- EQtl, <- HT, !assoc].
          apply (proj2 (A := Some rfp · Some sp == Some up)), pcm_op_split.
          now erewrite EQu.
    Qed.
    (* The above proof is rather ugly in the way it handles the monoid elements,
       but it works *)

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
          by (eapply ores_equiv_eq; rewrite assoc, (comm rf); reflexivity).
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
      forall w' k s rf mf σ (HSw : w ⊑ w') (HLt : k < n) (HD : mf # m)
             (HE : erasure σ (m ∪ mf) (Some r · rf) s w' @ S k),
        (forall (HV : is_value e),
         exists w'' r' s', w' ⊑ w'' /\ φ (exist _ e HV) w'' (S k) r'
                           /\ erasure σ (m ∪ mf) (Some r' · rf) s' w'' @ S k) /\
        (forall σ' ei ei' K (HDec : e = K [[ ei ]])
                (HStep : prim_step (ei, σ) (ei', σ')),
         exists w'' r' s', w' ⊑ w'' /\ WP (K [[ ei' ]]) φ w'' k r'
                           /\ erasure σ' (m ∪ mf) (Some r' · rf) s' w'' @ k) /\
        (forall e' K (HDec : e = K [[ fork e' ]]),
         exists w'' rfk rret s', w' ⊑ w''
                                 /\ WP (K [[ fork_ret ]]) φ w'' k rret
                                 /\ WP e' (umconst ⊤) w'' k rfk
                                 /\ erasure σ (m ∪ mf) (Some rfk · Some rret · rf) s' w'' @ k).

    Program Definition wpF m : (expr -n> (value -n> Props) -n> Props) -n> expr -n> (value -n> Props) -n> Props :=
      n[(fun WP => n[(fun e => n[(fun φ => m[(fun w => mkUPred (wpFP m WP e φ w) _)])])])].
    Next Obligation.
      intros n1 n2 r1 r2 HLe [rd EQr] Hp w' k s rf mf σ HSw HLt HD HE.
      rewrite <- EQr, (comm (Some rd)), <- assoc in HE.
      specialize (Hp w' k s (Some rd · rf) mf σ); destruct Hp as [HV [HS HF] ];
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

  Section Soundness.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.
    Local Open Scope lang_scope.
    Local Open Scope list_scope.

    Inductive stepn : nat -> cfg -> cfg -> Prop :=
    | stepn_O ρ : stepn O ρ ρ
    | stepn_S ρ1 ρ2 ρ3 n
              (HS  : step ρ1 ρ2)
              (HSN : stepn n ρ2 ρ3) :
        stepn (S n) ρ1 ρ3.

    Inductive wptp (m : mask) (w : Wld) (n : nat) : tpool -> list res -> Prop :=
    | wp_emp : wptp m w n nil nil
    | wp_cons e r tp rs
              (WPE  : wp m e (umconst ⊤) w n r)
              (WPTP : wptp m w n tp rs) :
        wptp m w n (e :: tp) (r :: rs).

    (* Trivial lemmas about split over append *)
    Lemma wptp_app m w n tp1 tp2 rs1 rs2
          (HW1 : wptp m w n tp1 rs1)
          (HW2 : wptp m w n tp2 rs2) :
      wptp m w n (tp1 ++ tp2) (rs1 ++ rs2).
    Proof.
      induction HW1; [| constructor]; now trivial.
    Qed.

    Lemma wptp_app_tp m w n t1 t2 rs
          (HW : wptp m w n (t1 ++ t2) rs) :
      exists rs1 rs2, rs1 ++ rs2 = rs /\ wptp m w n t1 rs1 /\ wptp m w n t2 rs2.
    Proof.
      revert rs HW; induction t1; intros; inversion HW; simpl in *; subst; clear HW.
      - exists (@nil res) (@nil res); now auto using wptp.
      - exists (@nil res); simpl; now eauto using wptp.
      - apply IHt1 in WPTP; destruct WPTP as [rs1 [rs2 [EQrs [WP1 WP2] ] ] ]; clear IHt1.
        exists (r :: rs1) rs2; simpl; subst; now auto using wptp.
    Qed.

    Lemma comp_list_app rs1 rs2 :
      comp_list (rs1 ++ rs2) == comp_list rs1 · comp_list rs2.
    Proof.
      induction rs1; simpl comp_list; [now rewrite pcm_op_unit by apply _ |].
      now rewrite IHrs1, assoc.
    Qed.

    (* Closure under future worlds and smaller steps *)
    Lemma wptp_closure m (w1 w2 : Wld) n1 n2 tp rs
          (HSW : w1 ⊑ w2) (HLe : n2 <= n1)
          (HW : wptp m w1 n1 tp rs) :
      wptp m w2 n2 tp rs.
    Proof.
      induction HW; constructor; [| assumption].
      eapply uni_pred; [eassumption | reflexivity |].
      rewrite <- HSW; assumption.
    Qed.

    Definition wf_nat_ind := well_founded_induction Wf_nat.lt_wf.

    Lemma unfold_wp m :
      wp m == (wpF m) (wp m).
    Proof.
      unfold wp; apply fixp_eq.
    Qed.

    Lemma sound_tp m n k e e' tp tp' σ σ' φ w r rs s
          (HSN  : stepn n (e :: tp, σ) (e' :: tp', σ'))
          (HV   : is_value e')
          (HWE  : wp m e φ w (n + S k) r)
          (HWTP : wptp m w (n + S k) tp rs)
          (HE   : erasure σ m (Some r · comp_list rs) s w @ n + S k) :
      exists w' r' s',
        w ⊑ w' /\ φ (exist _ e' HV) w' (S k) r' /\ erasure σ' m (Some r') s' w' @ S k.
    Proof.
      revert e tp σ w r rs s HSN HWE HWTP HE; induction n using wf_nat_ind; rename H into HInd.
      intros; inversion HSN; subst; clear HSN.
      (* e is a value *)
      { rename e' into e; clear HInd HWTP; simpl plus in *; rewrite unfold_wp in HWE.
        edestruct (HWE w k) as [HVal _];
          [reflexivity | unfold lt; reflexivity | apply mask_emp_disjoint
           | rewrite mask_emp_union; eassumption |].
        specialize (HVal HV); destruct HVal as [w' [r' [s' [HSW [Hφ HE'] ] ] ] ].
        rewrite mask_emp_union in HE'; destruct (Some r' · comp_list rs) as [r'' |] eqn: EQr.
        - exists w' r'' s'; split; [assumption | split; [| assumption] ].
          eapply uni_pred, Hφ; [reflexivity |].
          rewrite ord_res_optRes; exists (comp_list rs); rewrite comm, EQr; reflexivity.
        - exfalso; eapply erasure_not_empty, HE'.
          now erewrite pcm_op_zero by apply _.
      }
      rename n0 into n; specialize (HInd n (le_n _)); inversion HS; subst; clear HS.
      (* atomic step *)
      { destruct t1 as [| ee t1]; inversion H0; subst; clear H0.
        (* step in e *)
        - simpl in HSN0; rewrite unfold_wp in HWE; edestruct (HWE w (n + S k)) as [_ [HS _] ];
          [reflexivity | apply le_n | apply mask_emp_disjoint | rewrite mask_emp_union; eassumption |].
          edestruct HS as [w' [r' [s' [HSW [HWE' HE'] ] ] ] ]; [reflexivity | eassumption | clear HS HWE HE].
          rewrite mask_emp_union in HE'; setoid_rewrite HSW; eapply HInd; try eassumption.
          eapply wptp_closure, HWTP; [assumption | now auto with arith].
        (* step in a spawned thread *)
        - apply wptp_app_tp in HWTP; destruct HWTP as [rs1 [rs2 [EQrs [HWTP1 HWTP2] ] ] ].
          inversion HWTP2; subst; clear HWTP2; rewrite unfold_wp in WPE.
          edestruct (WPE w (n + S k) s (Some r · comp_list (rs1 ++ rs0))) as [_ [HS _] ];
            [reflexivity | apply le_n | apply mask_emp_disjoint
             | eapply erasure_equiv, HE; try reflexivity; [apply mask_emp_union |] |].
          + rewrite !comp_list_app; simpl comp_list; unfold equiv.
            rewrite assoc, (comm (Some r0)), <- assoc; apply pcm_op_equiv; [reflexivity |].
            now rewrite assoc, (comm (Some r0)), <- assoc.
          + edestruct HS as [w' [r0' [s' [HSW [WPE' HE'] ] ] ] ];
            [reflexivity | eassumption | clear WPE HS].
            setoid_rewrite HSW; eapply HInd; try eassumption; [| |].
            * rewrite <- HSW; eapply uni_pred, HWE; [now auto with arith | reflexivity].
            * apply wptp_app; [eapply wptp_closure, HWTP1; [assumption | now auto with arith] |].
            constructor; [eassumption | eapply wptp_closure, WPTP; [assumption | now auto with arith] ].
          * eapply erasure_equiv, HE'; try reflexivity; [symmetry; apply mask_emp_union |].
            rewrite assoc, (comm (Some r0')), <- assoc; apply pcm_op_equiv; [reflexivity |].
            rewrite !comp_list_app; simpl comp_list.
            now rewrite assoc, (comm (comp_list rs1)), <- assoc.
      }
      (* fork *)
      destruct t1 as [| ee t1]; inversion H; subst; clear H.
      (* fork from e *)
      - simpl in HSN0; rewrite unfold_wp in HWE; edestruct (HWE w (n + S k)) as [_ [_ HF] ];
        [reflexivity | apply le_n | apply mask_emp_disjoint | rewrite mask_emp_union; eassumption |].
        specialize (HF _ _ eq_refl); destruct HF as [w' [rfk [rret [s' [HSW [HWE' [HWFK HE'] ] ] ] ] ] ].
        clear HWE HE; setoid_rewrite HSW; eapply HInd with (rs := rs ++ [rfk]); try eassumption; [|].
        + apply wptp_app; [| now auto using wptp].
          eapply wptp_closure, HWTP; [assumption | now auto with arith].
        + eapply erasure_equiv, HE'; try reflexivity; [symmetry; apply mask_emp_union |].
          rewrite (comm (Some rfk)), <- assoc; apply pcm_op_equiv; [reflexivity |].
          rewrite comp_list_app; simpl comp_list; rewrite comm.
          now erewrite (comm _ 1), pcm_op_unit by apply _.
      (* fork from a spawned thread *)
      - apply wptp_app_tp in HWTP; destruct HWTP as [rs1 [rs2 [EQrs [HWTP1 HWTP2] ] ] ].
        inversion HWTP2; subst; clear HWTP2; rewrite unfold_wp in WPE.
        edestruct (WPE w (n + S k) s (Some r · comp_list (rs1 ++ rs0))) as [_ [_ HF] ];
          [reflexivity | apply le_n | apply mask_emp_disjoint
           | eapply erasure_equiv, HE; try reflexivity; [apply mask_emp_union |] |].
        + rewrite assoc, (comm (Some r0)), <- assoc; apply pcm_op_equiv; [reflexivity |].
          rewrite !comp_list_app; simpl comp_list; now rewrite assoc, (comm (Some r0)), <- assoc.
        + specialize (HF _ _ eq_refl); destruct HF as [w' [rfk [rret [s' [HSW [WPE' [WPS HE'] ] ] ] ] ] ]; clear WPE.
          setoid_rewrite HSW; eapply HInd; try eassumption; [| |].
          * rewrite <- HSW; eapply uni_pred, HWE; [now auto with arith | reflexivity].
          * apply wptp_app; [eapply wptp_closure, HWTP1; [assumption | now auto with arith] |].
            constructor; [eassumption | apply wptp_app; [| now eauto using wptp] ].
            eapply wptp_closure, WPTP; [assumption | now auto with arith].
          * eapply erasure_equiv, HE'; try reflexivity; [symmetry; apply mask_emp_union |].
            rewrite (assoc _ (Some r)), (comm _ (Some r)), <- assoc.
            apply pcm_op_equiv; [reflexivity |].
            rewrite (comm (Some rfk)), <- assoc, comp_list_app; simpl comp_list.
            rewrite assoc, (comm _ (Some rret)), <- assoc.
            apply pcm_op_equiv; [reflexivity |].
            rewrite (comm (Some rfk)), !comp_list_app; simpl comp_list.
            rewrite assoc; apply pcm_op_equiv; [reflexivity |].
            now erewrite comm, pcm_op_unit by apply _.
    Qed.

    Lemma unit_min r : pcm_unit _ ⊑ r.
    Proof.
      exists r; now erewrite comm, pcm_op_unit by apply _.
    Qed.

    (** This is a (relatively) generic soundness statement; one can
        simplify it for certain classes of assertions (e.g.,
        independent of the worlds) and obtain easy corollaries. *)
    Theorem soundness m e p φ n k e' tp σ σ' w r s
            (HT  : valid (ht m p e φ))
            (HSN : stepn n ([e], σ) (e' :: tp, σ'))
            (HV  : is_value e')
            (HP  : p w (n + S k) r)
            (HE  : erasure σ m (Some r) s w @ n + S k) :
      exists w' r' s',
        w ⊑ w' /\ φ (exist _ e' HV) w' (S k) r' /\ erasure σ' m (Some r') s' w' @ S k.
    Proof.
      specialize (HT w (n + S k) r).
      eapply sound_tp; [eassumption | | constructor | eapply erasure_equiv, HE; try reflexivity; [] ].
      - apply HT in HP; try reflexivity; [eassumption | apply unit_min].
      - simpl comp_list; now erewrite comm, pcm_op_unit by apply _.
    Qed.

    Program Definition cons_pred (φ : value -=> Prop): value -n> Props :=
      n[(fun v => pcmconst (mkUPred (fun n r => φ v) _))].
    Next Obligation.
      firstorder.
    Qed.
    Next Obligation.
      intros x y  H_xy P n r. simpl. rewrite H_xy. tauto.
    Qed.
    Next Obligation.
      intros x y H_xy P m r. simpl in H_xy. destruct n.
      - intros LEZ. exfalso. omega.
      - intros _. simpl. assert(H_xy': equiv x y) by assumption. rewrite H_xy'. tauto.
    Qed.

    Theorem soundness_obs m e (φ : value -=> Prop) n e' tp σ σ'
            (HT  : valid (ht m (ownS σ) e (cons_pred φ)))
            (HSN : stepn n ([e], σ) (e' :: tp, σ'))
            (HV : is_value e') :
        φ (exist _ e' HV).
    Proof.
      edestruct (soundness _ _ _ _ _ 0 _ _ _ _ fdEmpty (ex_own _ σ, pcm_unit _) 1 HT HSN) as [w' [r' [s' [H_wle [H_phi _] ] ] ] ].
      - simpl. hnf. exists (pcm_unit _).
        rewrite pcm_op_unit by intuition. reflexivity.
      - rewrite Plus.plus_comm. simpl. split.
        + admit. (* TODO: rewrite comm. does not work though?? *)
        + exists (fdEmpty (V:=res)). simpl. split; [reflexivity|].
          intros i _. split; [tauto|].
          intros _ _ [].
      - exact H_phi.
    Qed.

  End Soundness.

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
      rewrite unfold_wp; intros w'; intros; split; [| split]; intros.
      - exists w' r' s; split; [reflexivity | split; [| assumption] ].
        simpl; reflexivity.
      - contradiction (values_stuck _ HV _ _ HDec).
        repeat eexists; eassumption.
      - subst e; assert (HT := fill_value _ _ HV); subst K.
        revert HV; rewrite fill_empty; intros.
        contradiction (fork_not_value _ HV).
    Qed.

    Lemma wpO m e φ w r : wp m e φ w O r.
    Proof.
      rewrite unfold_wp; intros w'; intros; now inversion HLt.
    Qed.

    (** Bind **)

    (** Quantification in the logic works over nonexpansive maps, so
        we need to show that plugging the value into the postcondition
        and context is nonexpansive. *)
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

    Lemma htBind P φ φ' K e m :
      ht m P e φ ∧ all (plugV m φ φ' K) ⊑ ht m P (K [[ e ]]) φ'.
    Proof.
      intros wz nz rz [He HK] w HSw n r HLe _ HP.
      specialize (He _ HSw _ _ HLe (unit_min _) HP).
      rewrite HSw, <- HLe in HK; clear wz nz HSw HLe HP.
      revert e w r He HK; induction n using wf_nat_ind; intros; rename H into IH.
      rewrite unfold_wp in He; rewrite unfold_wp.
      destruct (is_value_dec e) as [HVal | HNVal]; [clear IH |].
      - intros w'; intros; edestruct He as [HV _]; try eassumption; [].
        clear He HE; specialize (HV HVal); destruct HV as [w'' [r' [s' [HSw' [Hφ HE] ] ] ] ].
        (* Fold the goal back into a wp *)
        setoid_rewrite HSw'.
        assert (HT : wp m (K [[ e ]]) φ' w'' (S k) r');
          [| rewrite unfold_wp in HT; eapply HT; [reflexivity | unfold lt; reflexivity | eassumption | eassumption] ].
        clear HE; specialize (HK (exist _ e HVal)).
        do 30 red in HK; unfold proj1_sig in HK.
        apply HK; [etransitivity; eassumption | apply HLt | apply unit_min | assumption].
      - intros w'; intros; edestruct He as [_ [HS HF] ]; try eassumption; [].
        split; [intros HVal; contradiction HNVal; assert (HT := fill_value _ _ HVal);
                subst K; rewrite fill_empty in HVal; assumption | split; intros].
        + clear He HF HE; edestruct step_by_value as [K' EQK];
          [eassumption | repeat eexists; eassumption | eassumption |].
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

    (** Much like in the case of the plugging, we need to show that
        the map from a value to a view shift between the applied
        postconditions is nonexpansive *)
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
      specialize (HP _ HSw _ _ HLe (unit_min _) Hp); rewrite unfold_wp.
      rewrite <- HLe, HSw in He, Hφ; clear wz nz HSw HLe Hp.
      intros w'; intros; edestruct HP as [w'' [r' [s' [HSw' [Hp' HE'] ] ] ] ]; try eassumption; [now rewrite mask_union_idem |].
      clear HP HE; rewrite HSw in He; specialize (He w'' HSw' _ r' HLt (unit_min _) Hp').
      setoid_rewrite HSw'.
      assert (HT : wp m e φ w'' (S k) r');
        [| rewrite unfold_wp in HT; eapply HT; [reflexivity | apply le_n | eassumption | eassumption] ].
      unfold lt in HLt; rewrite HSw, HSw', <- HLt in Hφ; clear - He Hφ.
      (* Second phase of the proof: got rid of the preconditions,
         now induction takes care of the evaluation. *)
      rename r' into r; rename w'' into w.
      revert w r e He Hφ; generalize (S k) as n; clear k; induction n using wf_nat_ind.
      rename H into IH; intros; rewrite unfold_wp; rewrite unfold_wp in He.
      intros w'; intros; edestruct He as [HV [HS HF] ]; try eassumption; [].
      split; [intros HVal; clear HS HF IH | split; intros; [clear HV HF | clear HV HS] ].
      - clear He HE; specialize (HV HVal); destruct HV as [w'' [r' [s' [HSw' [Hφ' HE] ] ] ] ].
        eapply Hφ in Hφ'; [| etransitivity; eassumption | apply HLt | apply unit_min].
        clear w n HSw Hφ HLt; edestruct Hφ' as [w [r'' [s'' [HSw [Hφ HE'] ] ] ] ];
        [reflexivity | apply le_n | rewrite mask_union_idem; eassumption | eassumption |].
        exists w r'' s''; split; [etransitivity; eassumption | split; assumption].
      - clear HE He; edestruct HS as [w'' [r' [s' [HSw' [He HE] ] ] ] ];
        try eassumption; clear HS.
        do 3 eexists; split; [eassumption | split; [| eassumption] ].
        apply IH; try assumption; [].
        unfold lt in HLt; rewrite Le.le_n_Sn, HLt, <- HSw', <- HSw; apply Hφ.
      - clear HE He; edestruct HF as [w'' [rfk [rret [s' [HSw' [HWF [HWR HE] ] ] ] ] ] ]; [eassumption |].
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
      specialize (HP _ HSw _ _ HLe (unit_min _) Hp); rewrite unfold_wp.
      split; [intros HV; contradiction (atomic_not_value e) |].
      split; [| intros; subst; contradiction (fork_not_atomic K e') ].
      intros; rewrite <- HLe, HSw in He, Hφ; clear wz nz HSw HLe Hp.
      edestruct HP as [w'' [r' [s' [HSw' [Hp' HE'] ] ] ] ]; try eassumption; [|].
      { intros j [Hmf Hmm']; apply (HD j); split; [assumption |].
        destruct Hmm'; [| apply HSub]; assumption.
      }
      clear HP HE; rewrite HSw0 in He; specialize (He w'' HSw' _ r' HLt (unit_min _) Hp').
      unfold lt in HLt; rewrite HSw0, <- HLt in Hφ; clear w n HSw0 HLt Hp'.
      rewrite unfold_wp in He; edestruct He as [_ [HS _] ];
        [reflexivity | apply le_n | rewrite HSub; eassumption | eassumption |].
      edestruct HS as [w [r'' [s'' [HSw [He' HE] ] ] ] ]; try eassumption; clear He HS HE'.
      destruct k as [| k]; [exists w' r' s'; split; [reflexivity | split; [apply wpO | exact I] ] |].
      subst e; assert (HT := atomic_fill _ _ HAt); subst K.
      rewrite fill_empty in *; rename ei into e.
      setoid_rewrite HSw'; setoid_rewrite HSw.
      assert (HVal := atomic_step _ _ _ _ HAt HStep).
      rewrite HSw', HSw in Hφ; clear - HE He' Hφ HSub HVal HD.
      rewrite unfold_wp in He'; edestruct He' as [HV _];
      [reflexivity | apply le_n | rewrite HSub; eassumption | eassumption |].
      clear HE He'; specialize (HV HVal); destruct HV as [w' [r [s [HSw [Hφ' HE] ] ] ] ].
      eapply Hφ in Hφ'; [| assumption | apply Le.le_n_Sn | apply unit_min].
      clear Hφ; edestruct Hφ' as [w'' [r' [s' [HSw' [Hφ HE'] ] ] ] ];
        [reflexivity | apply le_n | | eassumption |].
      { intros j [Hmf Hmm']; apply (HD j); split; [assumption |].
        destruct Hmm'; [apply HSub |]; assumption.
      }
      clear Hφ' HE; exists w'' r' s'; split;
      [etransitivity; eassumption | split; [| eassumption] ].
      clear - Hφ; rewrite unfold_wp; intros w; intros; split; [intros HVal' | split; intros; exfalso].
      - do 3 eexists; split; [reflexivity | split; [| eassumption] ].
        unfold lt in HLt; rewrite HLt, <- HSw.
        eapply φ, Hφ; [| apply le_n]; simpl; reflexivity.
      - eapply values_stuck; [.. | repeat eexists]; eassumption.
      - clear - HDec HVal; subst; assert (HT := fill_value _ _ HVal); subst.
        rewrite fill_empty in HVal; now apply fork_not_value in HVal.
    Qed.

    (** Framing **)

    (** Helper lemma to weaken the region mask *)
    Lemma wp_mask_weaken m1 m2 e φ (HD : m1 # m2) :
      wp m1 e φ ⊑ wp (m1 ∪ m2) e φ.
    Proof.
      intros w n; revert w e φ; induction n using wf_nat_ind; rename H into HInd; intros w e φ r HW.
      rewrite unfold_wp; rewrite unfold_wp in HW; intros w'; intros.
      edestruct HW with (mf := mf ∪ m2) as [HV [HS HF] ]; try eassumption;
      [| eapply erasure_equiv, HE; try reflexivity; [] |].
      { intros j [ [Hmf | Hm'] Hm]; [apply (HD0 j) | apply (HD j) ]; tauto.
      }
      { clear; intros j; tauto.
      }
      clear HW HE; split; [intros HVal; clear HS HF HInd | split; [intros; clear HV HF | intros; clear HV HS] ].
      - specialize (HV HVal); destruct HV as [w'' [r' [s' [HSW [Hφ HE] ] ] ] ].
        do 3 eexists; split; [eassumption | split; [eassumption |] ].
        eapply erasure_equiv, HE; try reflexivity; [].
        intros j; tauto.
      - edestruct HS as [w'' [r' [s' [HSW [HW HE] ] ] ] ]; try eassumption; []; clear HS.
        do 3 eexists; split; [eassumption | split; [eapply HInd, HW; assumption |] ].
        eapply erasure_equiv, HE; try reflexivity; [].
        intros j; tauto.
      - destruct (HF _ _ HDec) as [w'' [rfk [rret [s' [HSW [HWR [HWF HE] ] ] ] ] ] ]; clear HF.
        do 4 eexists; split; [eassumption |].
        do 2 (split; [apply HInd; eassumption |]).
        eapply erasure_equiv, HE; try reflexivity; [].
        intros j; tauto.
    Qed.

    Lemma htFrame m m' P R e φ (HD : m # m') :
      ht m P e φ ⊑ ht (m ∪ m') (P * R) e (lift_bin sc φ (umconst R)).
    Proof.
      intros w n rz He w' HSw n' r HLe _ [r1 [r2 [EQr [HP HLR] ] ] ].
      specialize (He _ HSw _ _ HLe (unit_min _) HP).
      clear P w n rz HSw HLe HP; rename w' into w; rename n' into n.
      apply wp_mask_weaken; [assumption |]; revert e w r1 r EQr HLR He.
      induction n using wf_nat_ind; intros; rename H into IH.
      rewrite unfold_wp; rewrite unfold_wp in He; intros w'; intros.
      rewrite <- EQr, <- assoc in HE; edestruct He as [HV [HS HF] ]; try eassumption; [].
      clear He; split; [intros HVal; clear HS HF IH HE | split; intros; [clear HV HF HE | clear HV HS HE] ].
      - specialize (HV HVal); destruct HV as [w'' [r1' [s' [HSw' [Hφ HE] ] ] ] ].
        rewrite assoc in HE; destruct (Some r1' · Some r2) as [r' |] eqn: EQr';
        [| eapply erasure_not_empty in HE; [contradiction | now erewrite !pcm_op_zero by apply _] ].
        do 3 eexists; split; [eassumption | split; [| eassumption ] ].
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

    Lemma htAFrame m m' P R e φ
          (HD  : m # m')
          (HAt : atomic e) :
      ht m P e φ ⊑ ht (m ∪ m') (P * ▹ R) e (lift_bin sc φ (umconst R)).
    Proof.
      intros w n rz He w' HSw n' r HLe _ [r1 [r2 [EQr [HP HLR] ] ] ].
      specialize (He _ HSw _ _ HLe (unit_min _) HP).
      clear rz n HLe; apply wp_mask_weaken; [assumption |]; rewrite unfold_wp.
      clear w HSw; rename n' into n; rename w' into w; intros w'; intros.
      split; [intros; exfalso | split; intros; [| exfalso] ].
      - contradiction (atomic_not_value e).
      - destruct k as [| k];
        [exists w' r s; split; [reflexivity | split; [apply wpO | exact I] ] |].
        rewrite unfold_wp in He; rewrite <- EQr, <- assoc in HE.
        edestruct He as [_ [HeS _] ]; try eassumption; [].
        edestruct HeS as [w'' [r1' [s' [HSw' [He' HE'] ] ] ] ]; try eassumption; [].
        clear HE He HeS; rewrite assoc in HE'.
        destruct (Some r1' · Some r2) as [r' |] eqn: EQr';
          [| eapply erasure_not_empty in HE';
             [contradiction | now erewrite !pcm_op_zero by apply _] ].
        do 3 eexists; split; [eassumption | split; [| eassumption] ].
        subst e; assert (HT := atomic_fill _ _ HAt); subst K.
        rewrite fill_empty in *.
        unfold lt in HLt; rewrite <- HLt, HSw, HSw' in HLR; simpl in HLR.
        assert (HVal := atomic_step _ _ _ _ HAt HStep).
        clear - He' HVal EQr' HLR; rename w'' into w; rewrite unfold_wp; intros w'; intros.
        split; [intros HV; clear HVal | split; intros; exfalso].
        + rewrite unfold_wp in He'; rewrite <- EQr', <- assoc in HE; edestruct He' as [HVal _]; try eassumption; [].
          specialize (HVal HV); destruct HVal as [w'' [r1'' [s'' [HSw' [Hφ HE'] ] ] ] ].
          rewrite assoc in HE'; destruct (Some r1'' · Some r2) as [r'' |] eqn: EQr'';
          [| eapply erasure_not_empty in HE';
             [contradiction | now erewrite !pcm_op_zero by apply _] ].
          do 3 eexists; split; [eassumption | split; [| eassumption] ].
          exists r1'' r2; split; [now rewrite EQr'' | split; [assumption |] ].
          unfold lt in HLt; rewrite <- HLt, HSw, HSw' in HLR; apply HLR.
        + eapply values_stuck; [.. | repeat eexists]; eassumption.
        + subst; clear -HVal.
          assert (HT := fill_value _ _ HVal); subst K; rewrite fill_empty in HVal.
          contradiction (fork_not_value e').
      - subst; clear -HAt; eapply fork_not_atomic; eassumption.
    Qed.

    (** Fork **)
    Lemma htFork m P R e :
      ht m P e (umconst ⊤) ⊑ ht m (▹ P * ▹ R) (fork e) (lift_bin sc (eqV (exist _ fork_ret fork_ret_is_value)) (umconst R)).
    Proof.
      intros w n rz He w' HSw n' r HLe _ [r1 [r2 [EQr [HP HLR] ] ] ].
      destruct n' as [| n']; [apply wpO |].
      simpl in HP; specialize (He _ HSw _ _ (Le.le_Sn_le _ _ HLe) (unit_min _) HP).
      clear rz n HLe; rewrite unfold_wp.
      clear w HSw HP; rename n' into n; rename w' into w; intros w'; intros.
      split; [intros; contradiction (fork_not_value e) | split; intros; [exfalso |] ].
      - assert (HT := fill_fork _ _ _ HDec); subst K; rewrite fill_empty in HDec; subst.
        eapply fork_stuck with (K := ε); [| repeat eexists; eassumption ]; reflexivity.
      - assert (HT := fill_fork _ _ _ HDec); subst K; rewrite fill_empty in HDec.
        apply fork_inj in HDec; subst e'; rewrite <- EQr in HE.
        unfold lt in HLt; rewrite <- (le_S_n _ _ HLt), HSw in He.
        simpl in HLR; rewrite <- Le.le_n_Sn in HE.
        do 4 eexists; split; [reflexivity | split; [| split; eassumption] ].
        rewrite fill_empty; rewrite unfold_wp; rewrite <- (le_S_n _ _ HLt), HSw in HLR.
        clear - HLR; intros w''; intros; split; [intros | split; intros; exfalso].
        + do 3 eexists; split; [reflexivity | split; [| eassumption] ].
          exists (pcm_unit _) r2; split; [now erewrite pcm_op_unit by apply _ |].
          split; [| unfold lt in HLt; rewrite <- HLt, HSw in HLR; apply HLR].
          simpl; reflexivity.
        + eapply values_stuck; [exact fork_ret_is_value | eassumption | repeat eexists; eassumption].
        + assert (HV := fork_ret_is_value); rewrite HDec in HV; clear HDec.
          assert (HT := fill_value _ _ HV);subst K; rewrite fill_empty in HV.
          eapply fork_not_value; eassumption.
    Qed.

  End HoareTripleProperties.

  Section DerivedRules.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.
    Local Open Scope lang_scope.

    Existing Instance LP_isval.

    Implicit Types (P Q R : Props) (i : nat) (m : mask) (e : expr) (φ : value -n> Props) (r : res).

    Lemma vsFalse m1 m2 :
      valid (vs m1 m2 ⊥ ⊥).
    Proof.
      rewrite valid_iff, box_top.
      unfold vs; apply box_intro.
      rewrite <- and_impl, and_projR.
      apply bot_false.
    Qed.

  End DerivedRules.

End Iris.
