Require Import Ssreflect.ssreflect Ssreflect.ssrfun Omega.
Require Import SPred PreoMet RA CMRA.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope ra_scope.
Local Open Scope predom_scope.

Section Agreement.
  (* This is more complex than above, and it does not require a decidable equality. However, it needs
     a metric. It also comes with a CMRA. *)
  Context {T} `{T_ty : Setoid T} {mT: metric T}.
  Local Open Scope ra_scope.
  Local Open Scope nat.

  Implicit Type (v: SPred).

  Definition cvChain v (ts: chain T): Prop :=
    forall n i (HLe: n <= i) (pv: v i), ts i = n = ts n.

  CoInductive ra_agree : Type :=
    ag_inj (v: SPred) (ts: chain T) (tsx: cvChain v ts).

  Global Instance ra_agree_unit : RA_unit ra_agree := fun x => x.
  Global Instance cmra_agree_valid : CMRA_valid _ :=
    fun x => match x with
             | ag_inj v _ _ => v
             end.
  Global Instance ra_agree_valid : RA_valid _ := compose valid_sp cmra_agree_valid.

(*  Local Ltac ra_ag_pi := match goal with
                           [H: dist ?n (?ts1 ?pv11) (?ts2 ?pv21) |- dist ?n (?ts1 ?pv12) (?ts2 ?pv22) ] =>
                           (* Also try with less rewrites, as some of the pvs apeparing in the goal may be existentials. *)
                           first [rewrite_pi pv12 pv11; rewrite_pi pv22 pv21; eexact H |
                                  rewrite_pi pv22 pv21; eexact H | rewrite_pi pv12 pv11; eexact H]
                         end. *)


  Program Definition ra_ag_compinj_valid {v1 v2} (ts1 ts2: chain T) (ts1x: cvChain v1 ts1) (ts2x: cvChain v2 ts2): SPred :=
    mkSPred (fun n => v1 n /\ v2 n /\ ts1 n = n = ts2 n) _ _.
  (* This has to be n-bounded equality for the operation to be non-expansive: A full equality at all step-indices here would become a proof obligation that we have to show based on just n-equality of our arguments. *)
  Next Obligation.
    split; last split; exact:dist_bound||exact:bpred.
  Qed.
  Next Obligation.
    intros n m ? (pv1 & pv2 & EQ). split; last split.
    - eapply dpred, pv1. assumption.
    - eapply dpred, pv2. assumption.
    - transitivity (ts2 n); last by eapply ts2x.
      transitivity (ts1 n); first by (symmetry; eapply ts1x).
      eapply mono_dist; eassumption.
  Qed.

  Lemma ra_ag_compinj_tsx {v1 v2} (ts1: chain T) (ts2: chain T) (ts1x: cvChain v1 ts1) (ts2x: cvChain v2 ts2):
    cvChain (ra_ag_compinj_valid ts1 ts2 ts1x ts2x) ts1.
  Proof.
    move=> n i HLe [pv1 [pv2 EQ]].
    eapply ts1x; assumption.
  Qed.

  Global Instance ra_ag_op : RA_op _ :=
    fun x y => match x, y with
               | ag_inj v1 ts1 ts1x, ag_inj v2 ts2 ts2x =>
                 ag_inj (ra_ag_compinj_valid ts1 ts2 ts1x ts2x) ts1
                        (ra_ag_compinj_tsx ts1 ts2 ts1x ts2x)
               end.
  Program Definition ra_ag_inj (t: T): ra_agree :=
    ag_inj top_sp (fun _ => t) (fun _ _ _ _ => _).
  Next Obligation.
    eapply dist_refl. reflexivity.
  Qed.
  
  Lemma ra_ag_inj_valid t:
    ra_agree_valid (ra_ag_inj t).
  Proof.
    intros n. exact I.
  Qed.

  Definition ra_agree_eq (x y: ra_agree): Prop :=
    match x, y with
    | ag_inj v1 ts1 _, ag_inj v2 ts2 _ => v1 == v2 /\ (forall n, v1 n -> ts1 n = n = ts2 n)
    (* Also, only the n-valid elements have to be only n-equal. Otherwise,
       commutativity breaks: n-valid here means that the arguments were
       n-equal. *)
    end.

  Local Ltac ra_ag_destr := repeat (match goal with [ x : ra_agree |- _ ] => destruct x end).

  Global Instance ra_agree_eq_equiv : Equivalence ra_agree_eq.
  Proof.
    split; repeat intro; ra_ag_destr; try (exact I || contradiction); [| |]. (* 3 goals left. *)
    - split; intros; reflexivity.
    - destruct H. split; intros; first by symmetry.
      symmetry. apply H0. rewrite H. assumption.
    - destruct H, H0.
      split; first (etransitivity; now eauto).
      intro; etransitivity; [now eapply H1 | ].
      eapply H2. rewrite -H. assumption.
  Qed.
  Global Instance ra_agree_type : Setoid ra_agree := mkType ra_agree_eq.

  Lemma ra_ag_dupl (x : ra_agree):
    x · x == x.
  Proof.
    ra_ag_destr. split.
    - split; simpl; first by firstorder. now firstorder.
    - move=>n ?. reflexivity.
  Qed.
  
  Global Instance ra_agree_res : RA ra_agree.
  Proof.
    split; repeat intro.
    - ra_ag_destr; [].
      destruct H as (HeqV1 & HeqT1), H0 as (HeqV2 & HeqT2).
      split.
      + split; intros (pv1 & pv2 & Heq).
        * move:(pv1)(pv2)=>pv1' pv2'. rewrite ->HeqV1 in pv1'. rewrite ->HeqV2 in pv2'.
          split; first assumption. split; first assumption.
          erewrite <-HeqT1, <-HeqT2 by assumption. eapply Heq; eassumption.
        * move:(pv1)(pv2)=>pv1' pv2'. rewrite <-HeqV1 in pv1'. rewrite <-HeqV2 in pv2'.
          split; first assumption. split; first assumption.
          rewrite ->HeqT1, ->HeqT2 by assumption. eapply Heq; eassumption.
      + intros n [pv1 [pv1' _]]. by apply: HeqT1.
    - ra_ag_destr; []. split.
      + intros n. rewrite /ra_ag_compinj_valid /=. split.
        * intros [pv1 [[pv2 [pv3 EQ']] EQ]].
          split_conjs; try assumption; []. by rewrite EQ.
        * intros [[pv1 [pv2 EQ']] [pv3 EQ]]. split_conjs; try assumption; [].
          by rewrite -EQ'.
      + intros n _. reflexivity.
    - ra_ag_destr. unfold ra_op, ra_ag_op. split.
      + intros n. rewrite /ra_ag_compinj_valid /=. split; intros; split_conjs; try tauto; symmetry; tauto.
      + intros n [pv1 [pv2 EQ]]. assumption.
    - eapply ra_ag_dupl.
    - ra_ag_destr; unfold ra_valid, ra_agree_valid in *; firstorder.
    - exists t'. reflexivity.
    - ra_ag_destr; unfold ra_valid, ra_agree_valid in *. split; first reflexivity.
      intros. reflexivity.
    - ra_ag_destr; unfold ra_valid, ra_agree_valid in *; firstorder.
    - ra_ag_destr; [].
      destruct (H n) as [Hn _]. assumption.
  Qed.

  Lemma ra_ag_pord (x y: ra_agree):
    x ⊑ y <-> y · x == y.
  Proof.
    split.
    - move=>[z EQ]. ra_ag_destr; destruct EQ as [EQv EQts]; split.
      + split.
        * intros (pv1 & pv2 & EQt). assumption.
        * intros pv0. hnf. move:(pv0). rewrite -{1}EQv. move=>[pv1 [pv2 EQ']].
          do 2 (split; first assumption). erewrite <-EQts by (simpl; tauto). assumption.
      + intros. reflexivity.
    - intros EQ. exists y. assumption.
  Qed.

  (* We also have a metric *)
  Definition ra_agree_dist n :=
    match n with
    | O => fun _ _ => True
    | S _ => fun x y => match x, y with
                        | ag_inj v1 ts1 _, ag_inj v2 ts2 _ =>
                          v1 = n = v2 /\ (forall n', n' <= n -> v1 n' -> ts1 n' = n' = ts2 n')
                        end
    end.

  Global Program Instance ra_agree_metric : metric ra_agree := mkMetr ra_agree_dist.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr. destruct H as [EQv1 EQts1], H0 as [EQv2 EQts2]. split; move=>[EQv EQts]; split.
    - rewrite -EQv1 -EQv2. assumption.
    - move=> n' HLe pv1. etransitivity; first (symmetry; eapply EQts1; by apply EQv1).
      etransitivity; last (eapply EQts2; by eapply EQv, EQv1). eapply EQts; first assumption.
      by apply EQv1.
    - rewrite EQv1 EQv2. assumption.
    - move=> n' HLe pv1. etransitivity; first (by eapply EQts1).
      etransitivity; last (symmetry; eapply EQts2; by eapply EQv2, EQv, EQv1).
      by eapply EQts, EQv1.
  Qed.
  Next Obligation.
    split.
    - intros Hall. ra_ag_destr.
      split.
      + eapply dist_refl. move=> [|n]; first by apply: dist_bound. destruct (Hall (S n)) as [EQ _].
        assumption.
      + intros n pv1. specialize (Hall (S n)). destruct n as [|n]; first by apply: dist_bound.
        now firstorder.
    - repeat intro. destruct n as [|n]; first by auto. ra_ag_destr; now firstorder.
  Qed.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr; now firstorder.
  Qed.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr.
    destruct H as [EQv1 EQts1], H0 as [EQv2 EQts2].
    split; first now firstorder. intros.
    etransitivity; first by eapply EQts1. by eapply EQts2, EQv1.
  Qed.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr. destruct H as [EQv EQts]. split.
    - move=>n' HLe. eapply EQv. omega.
    - move=>n'' HLe pv1. eapply EQts, pv1. omega.
  Qed.

  Global Instance ra_ag_op_dist n:
    Proper (dist n ==> dist n ==> dist n) ra_ag_op.
  Proof.
    move=>a1 aa2 EQa b1 b2 EQb. destruct n as [|n]; first by apply: dist_bound.
    ra_ag_destr; try firstorder; []. destruct EQa as [EQv1 EQts1], EQb as [EQv2 EQts2]. split.
    - move=>n' HLe. simpl. split; move=>[pv1 [pv2 EQ]].
      + split; first by apply EQv1. split; first by apply EQv2.
        etransitivity; first by (symmetry; eapply EQts1).
        etransitivity; last by (eapply EQts2). eassumption.
      + split; first by apply EQv1. split; first by apply EQv2.
        etransitivity; first by eapply EQts1, EQv1.
        etransitivity; last by (symmetry; eapply EQts2, EQv2). eassumption.
    - move=>n' HLe [pv1 [pv2 EQ]]. now eapply EQts1.
  Qed.

  Global Instance ra_ag_inj_dist n:
    Proper (dist n ==> dist n) ra_ag_inj.
  Proof.
    move=>t1 t2 EQt. destruct n as [|n]; first by apply: dist_bound.
    simpl. rewrite -/dist. split.
    - move=>? _. reflexivity.
    - move=>m Hle _. eapply mono_dist, EQt. omega.
  Qed.

  Lemma ra_ag_prod_dist x y n:
    cmra_valid (x · y) n ->
    x · y = n = x.
  Proof.
    move=>Hval.  destruct n as [|n]; first exact: dist_bound.
    unfold cmra_valid in Hval. ra_ag_destr. simpl in Hval.
    destruct Hval as [pv1 [pv2 Heq]].
    split.
    - move=>m Hle /=. split.
      + move=>_. eapply dpred, pv1. omega.
      + move=>_.
        split; first by (eapply dpred, pv1; omega).
        split; first by (eapply dpred, pv2; omega).
        etransitivity; last (etransitivity; first (eapply mono_dist, Heq; omega)).
        * symmetry. etransitivity; first now eapply tsx0. reflexivity.
        * etransitivity; first now eapply tsx. reflexivity.
    - intros. reflexivity.
  Qed.

  Program Definition ra_ag_vchain (σ: chain ra_agree) {σc: cchain σ} : chain SPred :=
    fun i => match σ (S i) with
             | ag_inj v' _ _ => v'
             end.

  Instance ra_ag_vchain_c (σ: chain ra_agree) {σc: cchain σ} : cchain (ra_ag_vchain σ).
  Proof.
    intros n j m HLe1 HLe2. destruct n as [|n]; first by apply: dist_bound. unfold ra_ag_vchain.
    ddes (σ (S j)) at 1 3 as [v1 ts1 tsx1] deqn:EQ1.
    ddes (σ (S m)) at 1 3 as [v2 ts2 tsx2] deqn:EQ2.
    cchain_eleq σ at (S j) (S m) lvl:(S n); move=>[EQv _].
    assumption.
  Qed.

  Lemma ra_ag_vchain_compl_n (σ: chain ra_agree) {σc: cchain σ} n:
    compl (ra_ag_vchain σ) n ->
    forall m k, m <= n -> k >= n -> ra_ag_vchain σ k m.
  Proof.
    move=>pv m k HLe HLe'.
    assert (HTv := conv_cauchy (ra_ag_vchain σ) (S n) _ (le_refl _)).
    apply HTv in pv; last by omega.
    clear HTv. move:pv. unfold ra_ag_vchain.
    ddes (σ (S (S n))) at 1 3 as [v1 ts1 tsx1] deqn:EQ1.
    ddes (σ (S k)) at 1 3 as [v2 ts2 tsx2] deqn:EQ2=>pv.
    cchain_eleq σ at (S (S n)) (S k) lvl:(S m); move=>[EQv _].
    apply EQv; first omega. eapply dpred; eassumption.
  Qed.

  Lemma ra_ag_vchain_ucompl_n (σ: chain ra_agree) {σc: cchain σ} n:
    ra_ag_vchain σ (S n) n ->
    compl (ra_ag_vchain σ) n.
  Proof.
    move=>pv.
    assert (HTv := conv_cauchy (ra_ag_vchain σ) (S n) _ (le_refl _)).
    apply HTv in pv; last by omega. assumption.
  Qed.

  Lemma ra_ag_vchain_n (σ: chain ra_agree) {σc: cchain σ} n m:
    ra_ag_vchain σ n m -> forall v' ts' tsx', σ (S n) = ag_inj v' ts' tsx' -> v' m.
  Proof.
    move=>pv v' ts' tsx' EQ. move:pv EQ.
    unfold ra_ag_vchain.
    ddes (σ (S n)) at 1 3 as [vSn tsSn tsxSSn] deqn:EQSSn.
    move=>pv EQ. rewrite EQ in EQSSn. injection EQSSn=>{EQSSn EQ}EQ. destruct EQ.
    move=><-. assumption.
  Qed.

  Definition ra_ag_tsdiag_n (σ : chain ra_agree) n: T :=
    match σ (S n) with
    | ag_inj v' ts' tsx' => ts' n
    end.

  Program Definition ra_ag_compl (σ : chain ra_agree) {σc : cchain σ} :=
    ag_inj (compl (ra_ag_vchain σ))
           (fun n => ra_ag_tsdiag_n σ n) _.
  Next Obligation.
    move=>n i HLe pv. simpl. rewrite -/dist.    
    assert (pvc: compl (ra_ag_vchain σ) i) by assumption.
    destruct n as [|n]; first by apply: dist_bound.
    unfold ra_ag_tsdiag_n.
    ddes (σ (S i)) at 1 3 as [vSi tsSi tsxSi] deqn:EQSi.
    ddes (σ (S (S n))) at 1 3 as [vSSn tsSSn tsxSSn] deqn:EQSSn.
    cchain_eleq σ at (S i) (S (S n)) lvl:(S (S n)); move=>[EQv EQts].
    assert (pv': vSi i).
    { move:pvc. move/ra_ag_vchain_compl_n. case/(_ i i _ _)/Wrap; [omega|].
      move/ra_ag_vchain_n=>H. eapply H. symmetry. eassumption. }
    etransitivity; last first.
    { eapply EQts; first omega. eapply dpred, pv'. assumption. }
    move:(tsxSi (S n) i). move/(_ _ pv')=>EQ.
    etransitivity; last eassumption. reflexivity.
  Qed.

  Global Program Instance ra_ag_cmt : cmetric ra_agree := mkCMetr ra_ag_compl.
  Next Obligation.
    intros [| n]; [now intros; apply dist_bound | unfold ra_ag_compl].
    intros i HLe. destruct (σ i) as [vi] eqn: EQi; split.
    - assert (HT:=conv_cauchy (ra_ag_vchain σ)).
      rewrite (HT (S n)). unfold ra_ag_vchain.
      ddes (σ (S i)) at 1 3 as [vSi tsSi tsxSi] deqn:EQSi.
      cchain_eleq σ at (S i) i lvl: (S n); move=>[EQv _]. assumption.
    - move=>j HLej pv1.
      destruct j as [|j]; first by apply: dist_bound.
      unfold ra_ag_tsdiag_n.
      rewrite /ra_ag_vchain /= in pv1. move:pv1.
      ddes (σ (S (S j))) at 1 3 6 as [vSSj tsSSj tsxSSj] deqn:EQSSj.
      intros pv1. cchain_eleq σ at (S (S j)) i lvl: (S j); move=>[EQv EQts].
      eapply EQts; first reflexivity. assumption.
  Qed.

  (* And we have a pcmType, too! *)
  Global Instance ra_ag_pcm: pcmType ra_agree.
  Proof.
    split. repeat intro. eapply ra_ag_pord. unfold compl, ra_ag_cmt, ra_ag_compl.
    assert (HT: forall n, ra_ag_vchain ρ n n -> ra_ag_tsdiag_n σ n = n = ra_ag_tsdiag_n ρ n).
    { move=>n pv. destruct n as [|n]; first by apply: dist_bound.
      unfold ra_ag_tsdiag_n.
      ddes (σ (S (S n))) at 1 3 as [vσn tsσn tsxσn] deqn:EQσn.
      ddes (ρ (S (S n))) at 1 3 as [vρn tsρn tsxρn] deqn:EQρn.
      specialize (H (S (S n))). rewrite ->ra_ag_pord in H.
      rewrite <-EQσn, <-EQρn, comm in H. destruct H as [EQv EQts].
      apply EQts. rewrite EQv. rewrite /ra_ag_vchain -EQρn in pv. assumption.
    }
    split.
    - move=>n. split; first by (intros (pv1 & pv2 & _); tauto).
      simpl. move=>pv. move:(pv). rewrite {1}/ra_ag_vchain. simpl.
      ddes (ρ (S n)) at 1 3 as [vρn tsρn tsxρn] deqn:EQρn.
      move=>pvρ.
      assert (pvσ: (ra_ag_vchain σ n) n).
      { unfold ra_ag_vchain.
        ddes (σ (S n)) at 1 3 as [vσn tsσn tsxσn] deqn:EQσn.
        specialize (H (S n)). rewrite ->ra_ag_pord, <-EQρn, <-EQσn, comm in H.
        destruct H as [EQv _]. rewrite <-EQv in pvρ. destruct pvρ as [pv1 _]. assumption. }
      do 2 (split; first assumption). symmetry. apply HT. assumption.
    - intros n (pv1 & pv2 & EQ). reflexivity.
  Qed.

  (* And finally, be ready for the CMRA *)
  Global Instance ra_ag_cmra : CMRA ra_agree.
  Proof.
    split.
    - now apply _.
    - by move=>[|n] t1 t2 EQt. 
    - move=>n t1 t2 EQt. destruct n as [|n]; first exact: dist_bound.
      ra_ag_destr; now firstorder.
    - move=>t. reflexivity.
    - move=> t1 t2. ra_ag_destr.
      move=>n [pv _]. exact pv.
  Qed.

  (* Provide a way to get an n-approximation of the element out of an n-valid agreement. *)
  Definition ra_ag_unInj x n: T :=
    match x with
    | ag_inj v ts _ => ts n
    end.

  Lemma ra_ag_unInj_dist x y n (HVal1: cmra_valid x n): (* we need validity, hence no "Proper" can be registered *)
    x = n = y -> ra_ag_unInj x n = n = ra_ag_unInj y n.
  Proof.
    move=>EQ. destruct n as [|n]; first exact: dist_bound.
    ra_ag_destr; now firstorder.
  Qed.

  Lemma ra_ag_unInj_move x n1 n2 (Hle: n1 <= n2) {HVal2: cmra_valid x n2}:
    ra_ag_unInj x n1 = n1 = ra_ag_unInj x n2.
  Proof.
    ra_ag_destr.
    rewrite /ra_ag_unInj. symmetry.
    etransitivity; last (etransitivity; first eapply (tsx n1 n2)); assumption || reflexivity.
  Qed.

  Lemma ra_ag_inj_unInj_ext x n (HVal: cmra_valid x n) t d:
    d · ra_ag_inj t = n = x -> ra_ag_unInj x n = n = t.
  Proof.
    rewrite comm.
    destruct x as [v ts tsx], d as [v' ts' tsx'] =>Heq.
    destruct n as [|n]; first exact: dist_bound. 
    unfold ra_ag_inj in Heq. destruct Heq as [EQv EQts]. unfold ra_ag_unInj.
    symmetry. eapply EQts; first reflexivity.
    eapply spredNE, HVal. symmetry. exact EQv.
  Qed.
  
  (* Provide a way to get the full T out of the agreement again. We don't need this, but I proved it before
     I realized. *)
  (* For this, we need a complete metric! *)
  Context {cmT: cmetric T}.

  Lemma ra_ag_tschain_c {v} (ts: chain T) (tsx: cvChain v ts) {HVal: ↓(ag_inj v ts tsx)} : cchain ts.
  Proof.
    intros n j m HLe1 HLe2. destruct n as [|n]; first by apply: dist_bound. 
    etransitivity; first by eapply (tsx (S n)).
    symmetry. etransitivity; first by eapply (tsx (S n)).
    reflexivity.
  Qed.

  Program Definition ra_ag_unInjFull x {HVal: ↓x}: T :=
    match x with
    | ag_inj v ts tsx => compl ts (σc:=ra_ag_tschain_c ts tsx (HVal:=_))
    end.

  Lemma ra_ag_unInjFull_dist x y {HVal1: ↓x} {HVal2: ↓y} n: (* The function is dependent, hence no "Proper" can be registered *)
    x = n = y -> ra_ag_unInjFull x (HVal:=HVal1) = n = ra_ag_unInjFull y (HVal:=HVal2).
  Proof.
    move=>EQ. destruct n as [|n]; first exact: dist_bound.
    destruct x as [xv xts xtsx].
    destruct y as [yv yts ytsx].
    destruct EQ as [_ EQts]. unfold ra_valid, ra_agree_valid in HVal1. unfold ra_valid, ra_agree_valid in HVal2.
    simpl. eapply umet_complete_extn. 
    eapply EQts.
    - reflexivity.
    - apply HVal1.
  Qed.

  (* Correctness of the embedding (and of the entire construction, really - together with the duplicability shown above) *)
  Lemma ra_ag_inj_unInjFull x {HVal: ↓x} t:
    ra_ag_inj t ⊑ x -> ra_ag_unInjFull x (HVal:=HVal) == t.
  Proof.
    rewrite ra_ag_pord comm. destruct x as [v ts tsx]=>Heq.
    unfold ra_ag_inj in Heq. destruct Heq as [EQv EQts]. simpl. rewrite <-(umet_complete_const t).
    apply umet_complete_ext=>i. symmetry.
    eapply EQts. rewrite EQv. apply HVal.
  Qed.

End Agreement.
Arguments ra_agree T {_ _} : clear implicits.

Section AgreementMap.
  Context {T U: Type} `{cmT: cmetric T} `{cmU: cmetric U}.
  Local Open Scope pumet_scope.

  Program Definition ra_agree_map (f: T -n> U): ra_agree T -m> ra_agree U :=
    m[(fun x => match x with
                | ag_inj v ts tsx => ag_inj v (compose f ts) _
                end)].
  Next Obligation.
    move=>n i HLe pv. simpl. eapply met_morph_nonexp. specialize (tsx n i HLe pv).
    rewrite tsx.
    eapply dist_refl. reflexivity.
  Qed.
  Next Obligation.
    move=> x y EQxy.
    destruct n as [|n]; first by apply: dist_bound.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); try (contradiction EQxy || reflexivity); [].
    destruct EQxy as [Hv Hts]. split; first assumption.
    move=>n' HLe pv1. specialize (Hts n' HLe pv1). unfold compose. rewrite Hts. reflexivity.
  Qed.
  Next Obligation.
    move=>x y EQxy. apply ra_ag_pord. apply ra_ag_pord in EQxy.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); try (contradiction EQxy || reflexivity); [].
    destruct EQxy as [EQv EQts]. split; first split.
    - intros (pv1 & pv2 & _). assumption.
    - move=>pv. move/EQv:(pv)=>[pv1 [pv2 EQ]]. do 2 (split; first assumption).
      unfold compose. rewrite EQ. reflexivity.
    - unfold compose. intros n [pv1 [pv2 EQ]]. reflexivity.
  Qed.

  Global Instance ra_agree_map_resp: Proper (equiv ==> equiv) ra_agree_map.
  Proof.
    move=> x1 x2 EQx y.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end).
    split; first reflexivity.
    move=>n pv1. rewrite EQx. unfold compose. reflexivity.
  Qed.
  Global Instance ra_agree_map_dist n: Proper (dist n ==> dist n) ra_agree_map.
  Proof.
    move=> x1 x2 EQx y.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end).
    destruct n as [|n]; first by apply: dist_bound.
    split; first reflexivity.
    move=>n' HLe pv1. rewrite /compose. eapply mono_dist; last first.
    - rewrite EQx. reflexivity.
    - omega.
  Qed.
End AgreementMap.

Section AgreementMapComp.
  Local Open Scope pumet_scope.
  Context {T: Type} `{cmT: cmetric T}.

  Lemma ra_agree_map_id:
    ra_agree_map (umid T) == (pid (ra_agree T)).
  Proof.
    intros x.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end).
    simpl. split; first reflexivity.
    reflexivity.
  Qed.
  
  Context {U V: Type} `{cmU: cmetric U} `{cmV: cmetric V}.

  Lemma ra_agree_map_comp (f: T -n> U) (g: U -n> V): 
    (ra_agree_map g) ∘ (ra_agree_map f) == ra_agree_map (g <M< f).
  Proof.
    intros x.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end).
    simpl. split; first reflexivity.
    intros. reflexivity.
  Qed.
End AgreementMapComp.
