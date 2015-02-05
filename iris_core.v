Require Import world_prop core_lang lang masks.
Require Import ModuRes.PCM ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Module IrisRes (RL : PCM_T) (C : CORE_LANG) <: PCM_T.
  Import C.
  Definition res := (pcm_res_ex state * RL.res)%type.
  Instance res_op   : PCM_op res := _.
  Instance res_unit : PCM_unit res := _.
  Instance res_pcm  : PCM res := _.
End IrisRes.
  
Module IrisCore (RL : PCM_T) (C : CORE_LANG).
  Module Export L  := Lang C.
  Module Export R  := IrisRes RL C.
  Module Export WP := WorldProp R.

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
 
  
  (* Benchmark: How large is this type? *)
  (*Section Benchmark.
    Local Open Scope mask_scope.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.
    Local Open Scope lang_scope.

    Local Instance _bench_expr_type : Setoid expr := discreteType.
    Local Instance _bench_expr_metr : metric expr := discreteMetric.
    Local Instance _bench_cmetr : cmetric expr := discreteCMetric.

    Set Printing All.
    Check (expr -n> (value -n> Props) -n> Props).
    Check ((expr -n> (value -n> Props) -n> Props) -n> expr -n> (value -n> Props) -n> Props).
    Unset Printing All.
  End Benchmark.*)

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
  Notation "∃ x , p" := (xist n[(fun x => p)] : Props) (at level 60, x ident, no associativity) : iris_scope.
  Notation "∀ x : T , p" := (all n[(fun x : T => p)] : Props) (at level 60, x ident, no associativity) : iris_scope.
  Notation "∃ x : T , p" := (xist n[(fun x : T => p)] : Props) (at level 60, x ident, no associativity) : iris_scope.

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

  Lemma box_disj p q :
    □ (p ∨ q) == □ p ∨ □ q.
  Proof.
    intros w n r; reflexivity.
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

  Section WorldSatisfaction.
    Local Open Scope pcm_scope.
    Local Open Scope bi_scope.

    (* First, we need to compose the resources of a finite map. This won't be pretty, for
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
    Definition comp_map (m : nat -f> res) : option res := comp_list (cod m).

    Lemma comp_map_remove (rs : nat -f> res) i r (HLu : rs i = Some r) :
      comp_map rs == Some r · comp_map (fdRemove i rs).
    Proof.
      destruct rs as [rs rsP]; unfold comp_map, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [discriminate |]; simpl comp_list; simpl in HLu.
      destruct (comp i j); [inversion HLu; reflexivity | discriminate |].
      simpl comp_list; rewrite IHrs by eauto using SS_tail.
      rewrite !assoc, (comm (Some s)); reflexivity.
    Qed.

    Lemma comp_map_insert_new (rs : nat -f> res) i r (HNLu : rs i = None) :
      Some r · comp_map rs == comp_map (fdUpdate i r rs).
    Proof.
      destruct rs as [rs rsP]; unfold comp_map, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [reflexivity | simpl comp_list; simpl in HNLu].
      destruct (comp i j); [discriminate | reflexivity |].
      simpl comp_list; rewrite <- IHrs by eauto using SS_tail.
      rewrite !assoc, (comm (Some r)); reflexivity.
    Qed.

    Lemma comp_map_insert_old (rs : nat -f> res) i r1 r2 r
          (HLu : rs i = Some r1) (HEq : Some r1 · Some r2 == Some r) :
      Some r2 · comp_map rs == comp_map (fdUpdate i r rs).
    Proof.
      destruct rs as [rs rsP]; unfold comp_map, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [discriminate |]; simpl comp_list; simpl in HLu.
      destruct (comp i j); [inversion HLu; subst; clear HLu | discriminate |].
      - simpl comp_list; rewrite assoc, (comm (Some r2)), <- HEq; reflexivity.
      - simpl comp_list; rewrite <- IHrs by eauto using SS_tail.
        rewrite !assoc, (comm (Some r2)); reflexivity.
    Qed.

    Definition state_sat (r: option res) σ: Prop := match r with
    | Some (ex_own s, _) => s = σ
    | _ => False
                                                    end.

    Global Instance state_sat_dist : Proper (equiv ==> equiv ==> iff) state_sat.
    Proof.
      intros r1 r2 EQr σ1 σ2 EQσ; apply ores_equiv_eq in EQr. rewrite EQσ, EQr. tauto.
    Qed.

    Global Instance preo_unit : preoType () := disc_preo ().

    Program Definition wsat (σ : state) (m : mask) (r : option res) (w : Wld) : UPred () :=
      ▹ (mkUPred (fun n _ => exists rs : nat -f> res,
                    state_sat (r · (comp_map rs)) σ
                      /\ forall i (Hm : m i),
                           (i ∈ dom rs <-> i ∈ dom w) /\
                           forall π ri (HLw : w i == Some π) (HLrs : rs i == Some ri),
                             ı π w n ri) _).
    Next Obligation.
      intros n1 n2 _ _ HLe _ [rs [HLS HRS] ]. exists rs; split; [assumption|].
      setoid_rewrite HLe; eassumption.
    Qed.

    Global Instance wsat_equiv σ : Proper (meq ==> equiv ==> equiv ==> equiv) (wsat σ).
    Proof.
      intros m1 m2 EQm r r' EQr w1 w2 EQw [| n] []; [reflexivity |];
      apply ores_equiv_eq in EQr; subst r'.
      split; intros [rs [HE HM] ]; exists rs.
      - split; [assumption | intros; apply EQm in Hm; split; [| setoid_rewrite <- EQw; apply HM, Hm] ].
        destruct (HM _ Hm) as [HD _]; rewrite HD; clear - EQw.
        rewrite fdLookup_in; setoid_rewrite EQw; rewrite <- fdLookup_in; reflexivity.
      - split; [assumption | intros; apply EQm in Hm; split; [| setoid_rewrite EQw; apply HM, Hm] ].
        destruct (HM _ Hm) as [HD _]; rewrite HD; clear - EQw.
        rewrite fdLookup_in; setoid_rewrite <- EQw; rewrite <- fdLookup_in; reflexivity.
    Qed.

    Global Instance wsat_dist n σ m r : Proper (dist n ==> dist n) (wsat σ m r).
    Proof.
      intros w1 w2 EQw [| n'] [] HLt; [reflexivity |]; destruct n as [| n]; [now inversion HLt |].
      split; intros [rs [HE HM] ]; exists rs.
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

    Lemma wsat_not_empty σ m (r: option res) w k (HN : r == 0) :
      ~ wsat σ m r w (S k) tt.
    Proof.
      intros [rs [HD _] ]; apply ores_equiv_eq in HN. setoid_rewrite HN in HD.
      exact HD.
    Qed.

  End WorldSatisfaction.

  Notation " p @ k " := ((p : UPred ()) k tt) (at level 60, no associativity).

End IrisCore.
