Require Import Ssreflect.ssreflect Ssreflect.ssrfun Omega.
Require Import SPred PreoMet RA CMRA Axioms.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope ra_scope.
Local Open Scope predom_scope.

Section Agreement.
  (* This is more complex than above, and it does not require a decidable equality. However, it needs
     a metric. It also comes with a CMRA. *)
  Context T `{T_ty : Setoid T} {mT: metric T}.
  Local Open Scope ra_scope.
  Local Open Scope nat.

  Implicit Types (v: SPred).

  Definition vChain v: Type := forall n, v n -> T.
  Program Definition cvChain {v} (ts: vChain v): Prop :=
    forall n i (HLe: n <= i) (v: v i), ts i _ = n = ts n _.
  Next Obligation.
    eapply dpred; eassumption.
  Qed.
  
  Inductive ra_agree : Type :=
  | ag_inj (v: SPred) (ts: vChain v) (tsx: cvChain ts)
  | ag_unit.

  Global Instance ra_agree_unit : RA_unit _ := fun _ => ag_unit.
  Global Program Instance cmra_agree_valid : CMRA_valid _ :=
    fun x => match x with
             | ag_unit => sp_top
             | ag_inj valid _ _ => valid
             end.
  Global Instance ra_agree_valid : RA_valid _ := compose sp_full cmra_agree_valid.

  Local Ltac ra_ag_pi := match goal with
                           [H: dist ?n (?ts1 ?pv11) (?ts2 ?pv21) |- dist ?n (?ts1 ?pv12) (?ts2 ?pv22) ] =>
                           (* Also try with less rewrites, as some of the pvs apeparing in the goal may be existentials. *)
                           first [pi pv12 pv11; pi pv22 pv21; eexact H |
                                  pi pv22 pv21; eexact H | pi pv12 pv11; eexact H]
                         end.


  Program Definition ra_ag_compinj_valid {v1 v2} (ts1: vChain v1) (ts2: vChain v2) (ts1x: cvChain ts1) (ts2x: cvChain ts2): SPred :=
    mkSPred (fun n => exists (pv1: v1 n) (pv2: v2 n), ts1 _ pv1 = n = ts2 _ pv2) _.
  (* This has to be n-bounded equality for the operation to be non-expansive: A full equality at all step-indices here would become a proof obligation that we have to show based on just n-equality of our arguments. *)
  Next Obligation.
    intros n m ? (pv1 & pv2 & EQ). do 2 eexists.
    transitivity (ts2 n pv2); last by eapply ts2x.
    transitivity (ts1 n pv1); first by (symmetry; eapply ts1x).
    eapply mono_dist; eassumption.
  Qed.

  Program Definition ra_ag_compinj_ts {v1 v2} (ts1: vChain v1) (ts2: vChain v2) (ts1x: cvChain ts1) (ts2x: cvChain ts2):
    vChain (ra_ag_compinj_valid ts1 ts2 ts1x ts2x) :=
    fun n pv => ts1 n _.

  Lemma ra_ag_compinj_tsx {v1 v2} (ts1: vChain v1) (ts2: vChain v2) (ts1x: cvChain ts1) (ts2x: cvChain ts2):
    cvChain (ra_ag_compinj_ts ts1 ts2 ts1x ts2x).
  Proof.
    move=> n i HLe [pv1 [pv2 EQ]]. unfold ra_ag_compinj_ts.
    transitivity (ts1 i pv1); first by f_equiv. (* RJ: I have no idea why this works... *)
    move/(_ _ _ HLe pv1):(ts1x)=>ts1x'. ra_ag_pi.
  Qed.

  Global Instance ra_ag_op : RA_op _ :=
    fun x y => match x, y with
               | ag_inj v1 ts1 ts1x, ag_inj v2 ts2 ts2x =>
                 ag_inj (ra_ag_compinj_valid ts1 ts2 ts1x ts2x) (ra_ag_compinj_ts ts1 ts2 ts1x ts2x)
                        (ra_ag_compinj_tsx ts1 ts2 ts1x ts2x)

               | ag_unit, y => y
               | x, ag_unit => x
               end.
  Program Definition ra_ag_inj (t: T): ra_agree :=
    ag_inj sp_top (fun _ _ => t) (fun _ _ _ _ => _).
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
    | ag_inj v1 ts1 _, ag_inj v2 ts2 _ => v1 == v2 /\ (forall n pv1 pv2, ts1 n pv1 = n = ts2 n pv2)
    (* The equality on the ts looks way too strong. However,
       thanks to PI, this is actally the same as
       "if both are valid, then pv1 and pv2 agree somewhere". *)
    (* Also, only the n-valid elements have to be only n-equal. Otherwise,
       commutativity breaks: n-valid here means that the arguments were
       n-equal. *)
    | ag_unit, ag_unit => True
    | _, _ => False
    end.

  Local Ltac ra_ag_destr := repeat (match goal with [ x : ra_agree |- _ ] => destruct x end).
  Local Ltac ra_ag_auto := first [by firstorder | split; [by firstorder|intros n pv1 pv2; pi pv1 pv2; by firstorder ]].

  Global Instance ra_agree_eq_equiv : Equivalence ra_agree_eq.
  Proof.
    split; repeat intro; ra_ag_destr; try (exact I || contradiction); [| |]. (* 3 goals left. *)
    - split; first reflexivity. intros. pi pv1 pv2. reflexivity.
    - destruct H. split; intros; by symmetry.
    - destruct H, H0.
      split; first (etransitivity; now eauto).
      intro; etransitivity; [now eapply H1 | now eapply H2].
  Grab Existential Variables.
  { rewrite -H. assumption. }
  Qed.
  Global Instance ra_agree_type : Setoid ra_agree := mkType ra_agree_eq.
  Global Instance ra_agree_res : RA ra_agree.
  Proof.
    split; repeat intro.
    - ra_ag_destr; try ra_ag_auto; [].
      destruct H as (HeqV1 & HeqT1), H0 as (HeqV2 & HeqT2).
      split.
      + split; intros (pv1 & pv2 & Heq).
        * move:(pv1)(pv2)=>pv1' pv2'. rewrite ->HeqV1 in pv1'. rewrite ->HeqV2 in pv2'. exists pv1' pv2'.
          rewrite <-HeqT1, <-HeqT2. eapply Heq; eassumption.
        * move:(pv1)(pv2)=>pv1' pv2'. rewrite <-HeqV1 in pv1'. rewrite <-HeqV2 in pv2'. exists pv1' pv2'.
          rewrite ->HeqT1, ->HeqT2. eapply Heq; eassumption.
      + intros n pv1 pv2. by apply: HeqT1.
    - ra_ag_destr; try ra_ag_auto; []. simpl. unfold ra_ag_compinj_ts in *. split.
      + intros n. split.
        * intros [pv1 [[pv2 [pv3 EQ']] EQ]]. hnf. 
          assert (pv4: (ra_ag_compinj_valid ts1 ts0 tsx1 tsx0) n).
          { hnf. exists pv1 pv2. ra_ag_pi. }
          exists pv4 pv3. rewrite <-EQ'. ra_ag_pi.
        * intros [[pv1 [pv2 EQ']] [pv3 EQ]]. hnf. unfold ra_ag_compinj_ts in *.
          assert (pv4: (ra_ag_compinj_valid ts0 ts tsx0 tsx) n).
          { hnf. exists pv2 pv3. rewrite <-EQ'. ra_ag_pi. }
          exists pv1 pv4. ra_ag_pi.
      + intros n pv1 pv2. f_equiv. by eapply ProofIrrelevance.
    - ra_ag_destr; try ra_ag_auto; []. unfold ra_op, ra_ag_op. unfold ra_ag_compinj_ts in *. split.
      + split; intros (pv1 & pv2 & Heq); do 2 eexists; symmetry; eassumption.
      + intros n [pv1 [pv2 EQ]] [pv3 [pv4 EQ']]. unfold ra_ag_compinj_ts in *. ra_ag_pi.
    - ra_ag_destr; reflexivity.
    - ra_ag_destr; unfold ra_valid, ra_agree_valid in *; firstorder.
    - by exists ag_unit. 
    - ra_ag_destr; unfold ra_valid, ra_agree_valid in *; firstorder.
    - ra_ag_destr; try firstorder; last exact I; [].
      destruct (H n) as [Hn _]. assumption.
  Qed.

  Lemma ra_ag_pord (x y: ra_agree):
    x ⊑ y <-> x · y == y.
  Proof.
    split.
    - move=>[z EQ]. ra_ag_destr; try ra_ag_auto; [|]; destruct EQ as [EQv EQts]; split.
      +  unfold ra_ag_compinj_ts in *; split.
        * intros (pv1 & pv2 & EQt). assumption.
        * intros pv0. hnf. move:(pv0). rewrite -{1}EQv. move=>[pv1 [pv2 EQ']].
          exists pv2 pv0. erewrite <-EQts. symmetry. ra_ag_pi.
      + unfold ra_ag_compinj_ts in *; move=>n [pv1 [pv2 EQ]] pv3. ra_ag_pi.
      + split.
        * intros (pv1 & pv2 & EQt). assumption.
        * rewrite -{1}EQv. move=>pv1. do 2 eexists. eapply EQts.
      + unfold ra_ag_compinj_ts in *; move=>n [pv1 [pv2 EQt]] pv3. ra_ag_pi.
    - intros EQ. exists y. rewrite comm. assumption.
  Grab Existential Variables.
  { rewrite -EQv. assumption. }
  { assumption. }
  { do 2 eexists. eassumption. }
  Qed.

  Lemma ra_ag_dupl (x y: ra_agree):
    x · x == x.
  Proof.
    eapply ra_ag_pord. reflexivity.
  Qed.

  (* We also have a metric *)
  Definition ra_agree_dist n :=
    match n with
    | O => fun _ _ => True
    | S _ => fun x y => match x, y with
                        | ag_inj v1 ts1 _, ag_inj v2 ts2 _ =>
                          v1 = S n = v2 /\ (forall n' pv1 pv2, n' <= n -> ts1 n' pv1 = n' = ts2 n' pv2)
                                           (* be sure for n'' to be at a level where the validity equality actually means something: v1 = n = v2 means that they agree on n' and smaller! *)
                        | ag_unit, ag_unit => True
                        | _, _ => False
                        end
    end.

  Global Program Instance ra_agree_metric : metric ra_agree := mkMetr ra_agree_dist.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr; try ra_ag_auto; []. destruct H as [EQv1 EQts1], H0 as [EQv2 EQts2]. split; move=>[EQv EQts]; split.
    - rewrite -EQv1 -EQv2. assumption.
    - move=> n' pv1 pv2 HLe. etransitivity; first (symmetry; by eapply EQts1).
      etransitivity; last (by eapply EQts2). by eapply EQts.
    - rewrite EQv1 EQv2. assumption.
    - move=> n' pv1 pv2 HLe. etransitivity; first (by eapply EQts1).
      etransitivity; last (symmetry; by eapply EQts2). now eauto.
  Grab Existential Variables.
  { by rewrite -EQv2. }
  { by rewrite -EQv1. }
  { by rewrite EQv2. }
  { by rewrite EQv1. }
  Qed.
  Next Obligation.
    split.
    - intros Hall. ra_ag_destr; last exact I; try (specialize (Hall 1); now firstorder); [].
      split.
      + eapply dist_refl. move=> [|n]; first by apply: dist_bound. destruct (Hall (S n)) as [EQ _].
        apply dist_mono. assumption.
      + intros n pv1 pv2. specialize (Hall (S n)). destruct n as [|n]; first by apply: dist_bound.
        now firstorder.
    - repeat intro. destruct n as [|n]; first by auto. ra_ag_destr; now firstorder.
  Qed.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr; try firstorder; [].
    - symmetry. now eauto.
  Qed.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr; try firstorder; [].
    etransitivity; first by eapply H1. by eapply H2.
  Grab Existential Variables.
  { apply H; first omega. assumption. }
  Qed.
  Next Obligation.
    repeat intro. destruct n as [|n]; first by auto.
    ra_ag_destr; try firstorder; []. destruct H as [EQv EQts]. split.
    - move=>n' HLe. eapply EQv. omega.
    - move=>n'' pv1 pv2 HLe. eapply EQts. omega.
  Qed.

  Global Instance ra_ag_op_dist n:
    Proper (dist n ==> dist n ==> dist n) ra_ag_op.
  Proof.
    move=>a1 aa2 EQa b1 b2 EQb. destruct n as [|n]; first by apply: dist_bound.
    ra_ag_destr; try firstorder; []. destruct EQa as [EQv1 EQts1], EQb as [EQv2 EQts2]. split.
    - move=>n' HLe. split; move=>[pv1 [pv2 EQ]]; do 2 eexists.
      + etransitivity; first by (symmetry; eapply EQts1; omega).
        etransitivity; last by (eapply EQts2; omega). eassumption.
      + etransitivity; first by (eapply EQts1; omega).
        etransitivity; last by (symmetry; eapply EQts2; omega). eassumption.
    - unfold ra_ag_compinj_ts in *. move=>n' [pv1 [pv2 EQ]] [pv3 [pv4 EQ']] HLe.
      eapply EQts1. omega.
  Grab Existential Variables.
  { apply EQv2; assumption. }
  { apply EQv1; assumption. }
  { apply EQv2; assumption. }
  { apply EQv1; assumption. }
  Qed.

  Global Instance ra_ag_inj_dist n:
    Proper (dist n ==> dist n) ra_ag_inj.
  Proof.
    move=>t1 t2 EQt. destruct n as [|n]; first by apply: dist_bound.
    simpl. rewrite -/dist. split.
    - move=>? _. reflexivity.
    - move=>m _ _ Hle. eapply mono_dist, EQt. omega.
  Qed.


  Program Definition ra_ag_vchain (σ: chain ra_agree) {σc: cchain σ} v ts {tsx} {HNE : ag_inj v ts tsx = σ 1} : chain SPred :=
    fun i => match σ (S i) with
             | ag_unit => !
             | ag_inj v' _ _ => v'
             end.
  Next Obligation.
    cchain_eleq σ at 1 (S i) lvl:1=>EQ.
    apply EQ; omega.
  Qed.

  Instance ra_ag_vchain_c (σ: chain ra_agree) {σc: cchain σ} v ts {tsx} {HNE : ag_inj v ts tsx = σ 1} : cchain (ra_ag_vchain σ v ts (HNE:=HNE)).
  Proof.
    intros n j m HLe1 HLe2. destruct n as [|n]; first by apply: dist_bound. unfold ra_ag_vchain.
    cchain_discr σ (S j) at 1 3 as [v1 ts1 tsx1|] deqn:EQ1.
    cchain_discr σ (S m) at 1 3 as [v2 ts2 tsx2|] deqn:EQ2.
    cchain_eleq σ at (S j) (S m) lvl:(S n); move=>[EQv _].
    exact: dist_mono.
  Qed.

  Lemma ra_ag_vchain_compl_n (σ: chain ra_agree) {σc: cchain σ} v ts {tsx} {HNE : ag_inj v ts tsx = σ 1} n:
    compl (ra_ag_vchain σ v ts (HNE:=HNE)) n ->
    forall m k, m <= n -> k >= n -> ra_ag_vchain σ v ts (HNE:=HNE) k m.
  Proof.
    move=>pv m k HLe HLe'.
    assert (HTv := conv_cauchy (ra_ag_vchain σ v ts (HNE:=HNE)) (S n) _ (le_refl _)).
    apply HTv in pv; last by omega.
    clear HTv. move:pv. unfold ra_ag_vchain.
    cchain_discr σ (S (S n)) at 1 3 as [v1 ts1 tsx1|] deqn:EQ1.
    cchain_discr σ (S k) at 1 3 as [v2 ts2 tsx2|] deqn:EQ2=>pv.
    cchain_eleq σ at (S (S n)) (S k) lvl:(S m); move=>[EQv _].
    apply EQv; first omega. eapply dpred; eassumption.
  Qed.

  Lemma ra_ag_vchain_ucompl_n (σ: chain ra_agree) {σc: cchain σ} v ts {tsx} {HNE : ag_inj v ts tsx = σ 1} n:
    ra_ag_vchain σ v ts (HNE:=HNE) (S n) n ->
    compl (ra_ag_vchain σ v ts (HNE:=HNE)) n.
  Proof.
    move=>pv.
    assert (HTv := conv_cauchy (ra_ag_vchain σ v ts (HNE:=HNE)) (S n) _ (le_refl _)).
    apply HTv in pv; last by omega. assumption.
  Qed.

  Lemma ra_ag_vchain_n (σ: chain ra_agree) {σc: cchain σ} v ts {tsx} {HNE : ag_inj v ts tsx = σ 1} n m:
    ra_ag_vchain σ v ts (HNE:=HNE) n m -> forall v' ts' tsx', σ (S n) = ag_inj v' ts' tsx' -> v' m.
  Proof.
    move=>pv v' ts' tsx' EQ. move:pv EQ.
    unfold ra_ag_vchain.
    cchain_discr σ (S n) at 1 3 as [vSn tsSn tsxSSn|] deqn:EQSSn.
    move=>pv EQ. rewrite EQ in EQSSn. injection EQSSn=>{EQSSn EQ}EQ. destruct EQ.
    move=><-. assumption.
  Qed.

  Program Definition ra_ag_tsdiag_n (σ : chain ra_agree) {σc : cchain σ} v ts {tsx} {HNE : ag_inj v ts tsx = σ 1} n {pv: compl (ra_ag_vchain σ v ts (HNE:=HNE)) n}: T :=
    match σ (S n) with
    | ag_unit => !
    | ag_inj v' ts' tsx' => ts' n _
    end.
  Next Obligation.
    cchain_eleq σ at 1 (S n) lvl:1=>EQ.
    apply EQ; omega.
  Qed.
  Next Obligation.
    unfold ra_ag_vchain in pv. move: pv.
    cchain_discr σ (S (S n)) at 1 3 as [vSSn tsSSn tsxSSn|] deqn:EQ; move=>pv.
    cchain_eleq σ at (S n) (S (S n)) lvl:(S n); move=>[EQv _].
    apply EQv; first omega. assumption.
  Qed.

  Lemma ra_ag_tsdiag_n_pi (σ : chain ra_agree) {σc : cchain σ} v ts {tsx1 tsx2} {HNE1 : ag_inj v ts tsx1 = σ 1} {HNE2 : ag_inj v ts tsx2 = σ 1} n {pv1: compl (ra_ag_vchain σ v ts (HNE:=HNE1)) n} {pv2: compl (ra_ag_vchain σ v ts (HNE:=HNE2)) n}:
    ra_ag_tsdiag_n σ v ts n (HNE:=HNE1) (pv:=pv1) = ra_ag_tsdiag_n σ v ts n (HNE:=HNE2) (pv:=pv2).
  Proof.
    Set Printing Implicit.
    move: HNE1 HNE2 n pv1 pv2. pi tsx2 tsx1=>{tsx2} HNE1 HNE2.
    pi HNE2 HNE1=>{HNE2} n pv1 pv2.
    pi pv2 pv1. reflexivity.
    Unset Printing Implicit.
  Qed.

  Program Definition ra_ag_compl (σ : chain ra_agree) {σc : cchain σ} :=
    match σ 1 with
      | ag_unit => ag_unit
      | ag_inj v ts tsx => ag_inj (compl (ra_ag_vchain σ v ts (tsx:=tsx) (HNE:=_)))
                                  (fun n pv => ra_ag_tsdiag_n σ v ts n (pv:=pv)) _
    end.
  Next Obligation.
    move=>n i HLe pv. simpl. rewrite -/dist.    
    assert (pvc: compl (ra_ag_vchain σ v ts (HNE:=Heq_anonymous)) i).
    { Set Printing Implicit. clear -pv. unfold compl, sp_cmetric, sp_compl in *. simpl in *.
      erewrite (ProofIrrelevance _ _ Heq_anonymous) in pv. assumption. Unset Printing Implicit. }
    destruct n as [|n]; first by apply: dist_bound.
    unfold ra_ag_tsdiag_n.
    cchain_discr σ (S i) at 1 3 as [vSi tsSi tsxSi|] deqn:EQSi.
    cchain_discr σ (S (S n)) at 1 3 as [vSSn tsSSn tsxSSn|] deqn:EQSSn.
    cchain_eleq σ at (S i) (S (S n)) lvl:(S (S n)); move=>[EQv EQts].
    assert (pv': vSi i).
    { move:pvc. move/ra_ag_vchain_compl_n. case/(_ i i _ _)/Wrap; [omega|].
      move/ra_ag_vchain_n=>H. eapply H. symmetry. eassumption. }
    etransitivity; last first.
    { eapply EQts. omega. }
    move:(tsxSi (S n) i). move/(_ _ pv')=>EQ.
    etransitivity; last eassumption.
    eapply dist_refl. f_equiv. eapply ProofIrrelevance.
  Qed.

  Global Program Instance ra_ag_cmt : cmetric ra_agree := mkCMetr ra_ag_compl.
  Next Obligation.
    intros [| n]; [now intros; apply dist_bound | unfold ra_ag_compl].
    ddes (σ 1) at 1 3 as [v0 ts0 tsx0|] deqn:EQ1.
    - intros i HLe. destruct (σ i) as [vi |] eqn: EQi; [split| exfalso].
      + assert (HT:=conv_cauchy (ra_ag_vchain σ v0 ts0 (HNE:=ra_ag_compl_obligation_1 σ σc v0 _ _ EQ1))).
        assert (HLe': S (S n) <= S i) by omega.
        rewrite (HT (S i)). unfold ra_ag_vchain.
        cchain_discr σ (S (S i)) at 1 3 as [vSi tsSi tsxSi|] deqn:EQSi.
        cchain_eleq σ at (S (S i)) i lvl: (S n); move=>[EQv _]. assumption.
      + move=>j pv1 pv2 HLej.
        assert (HeqH := ra_ag_compl_obligation_1 σ σc v0 ts0 tsx0 EQ1).
        assert (pvc: compl (ra_ag_vchain σ v0 ts0 (HNE:=HeqH)) j).
        { Set Printing Implicit. clear -pv1. unfold compl, sp_cmetric, sp_compl in *. simpl in *.
          erewrite (ProofIrrelevance _ _ HeqH) in pv1. assumption. Unset Printing Implicit. }
        destruct j as [|j]; first by apply: dist_bound.
        unfold ra_ag_tsdiag_n.
        cchain_discr σ (S (S j)) at 1 3 as [vSSj tsSSj tsxSSj|]deqn:EQSSj.
        cchain_eleq σ at (S (S j)) i lvl: (S j); move=>[EQv EQts].
        eapply EQts. omega.
      + cchain_eleq σ at 1 i lvl:1=>EQ. apply EQ; omega.
    - intros j Hle. 
      cchain_eq σ at 1 j lvl:1. rewrite -EQ1.
      destruct (σ j); simpl; tauto.
  Qed.


  (* And we have a pcmType, too! *)
  Global Instance ra_ag_pcm: pcmType ra_agree.
  Proof.
    split. repeat intro. eapply ra_ag_pord. unfold compl, ra_ag_cmt, ra_ag_compl.
    ddes (ρ 1) at 1 3 7 as [ρv ρts|] deqn:Hρ; ddes (σ 1) at 1 3 as [σv σts|] deqn:Hσ; last first.
    - reflexivity.
    - simpl. specialize (H 1). rewrite ->ra_ag_pord, <-Hρ, <-Hσ in H. exact H.
    - reflexivity.
    - simpl.
      assert (HT: forall n pv1 pv2, ra_ag_tsdiag_n σ σv σts (HNE:=Hσ) (pv:=pv1) n = n = ra_ag_tsdiag_n ρ ρv ρts (HNE:=Hρ) (pv:=pv2) n).
      { move=>n pv1 pv2. destruct n as [|n]; first by apply: dist_bound.
        unfold ra_ag_tsdiag_n.
        cchain_discr σ (S (S n)) at 1 3 as [vσn tsσn tsxσn|] deqn:EQσn.
        cchain_discr ρ (S (S n)) at 1 3 as [vρn tsρn tsxρn|] deqn:EQρn.
        specialize (H (S (S n))). rewrite ->ra_ag_pord in H.
        rewrite <-EQσn, <-EQρn in H. destruct H as [EQv EQts].
        erewrite <-EQts. unfold ra_ag_compinj_ts. f_equiv. eapply ProofIrrelevance.
      }
      split.
      + move=>n. split; first by (intros (pv1 & pv2 & _); tauto).
        simpl. move=>pv. move:(pv). rewrite {1}/ra_ag_vchain. simpl.
        cchain_discr ρ (S (S n)) at 1 3 as [vρn tsρn tsxρn|] deqn:EQρn.
        move=>pvρ.
        assert (pvσ: (ra_ag_vchain σ σv σts (HNE:=Hσ) (S n)) n).
        { unfold ra_ag_vchain.
          cchain_discr σ (S (S n)) at 1 3 as [vσn tsσn tsxσn|] deqn:EQσn.
          specialize (H (S (S n))). rewrite ->ra_ag_pord, <-EQρn, <-EQσn in H.
          destruct H as [EQv _]. rewrite <-EQv in pvρ. destruct pvρ as [pv1 _]. assumption. }
        do 2 eexists. etransitivity; last (etransitivity; first by eapply HT).
        * eapply dist_refl. apply equivR. apply ra_ag_tsdiag_n_pi.
        * eapply dist_refl. apply equivR. apply ra_ag_tsdiag_n_pi.
      + intros n (pv1 & pv2 & EQ) pv3.
        etransitivity; last (etransitivity; first by eapply HT).
        * eapply dist_refl. apply equivR. apply ra_ag_tsdiag_n_pi.
        * eapply dist_refl. apply equivR. apply ra_ag_tsdiag_n_pi.
  Grab Existential Variables.
  { eapply ra_ag_vchain_ucompl_n. clear -pv1. erewrite (ProofIrrelevance _ _ Hσ) in pv1. assumption. }
  { eapply ra_ag_vchain_ucompl_n. clear -pv2. erewrite (ProofIrrelevance _ _ Hρ) in pv2. assumption. }
  { eapply ra_ag_vchain_ucompl_n. exact pvσ. }
  { eapply ra_ag_vchain_ucompl_n. erewrite (ProofIrrelevance _ _ Hρ) in pv. exact pv. }
  { assumption. }
  { erewrite (ProofIrrelevance _ _ Hσ). assumption. }
  { apply EQv. eapply ra_ag_vchain_n.
    - eapply ra_ag_vchain_compl_n with (m:=S n) (k:=S n); first (by eexact pv2); omega.
    - symmetry. eassumption. }
  Qed.

  (* And finally, be ready for the CMRA *)
  Global Instance ra_ag_cmra : CMRA ra_agree.
  Proof.
    split.
    - now apply _.
    - by move=>[|n] t1 t2 EQt. 
    - move=>n t1 t2 EQt. destruct n as [|n]; first exact: dist_bound.
      ra_ag_destr; try firstorder; [].
      move=>m Hle. rewrite /cmra_valid /=. destruct EQt as [EQv _]. apply EQv. omega.
    - move=>t. reflexivity.
    - move=> t1 t2. ra_ag_destr; try firstorder; last first.
      { move=>n H. exact I. }
      move=>n [pv _]. exact pv.
  Qed.

  (* Provide a way to get an n-approximation of the element out of an n-valid agreement. *)
  Program Definition ra_ag_unInjApprox x n {HVal: cmra_valid x n}: option T :=
    match x with
    | ag_unit => None
    | ag_inj v ts _ => Some (ts n _)
    end.

  Lemma ra_ag_unInjApprox_dist x y n {HVal1: cmra_valid x n} {HVal2: cmra_valid y n}: (* The function is dependent, hence no "Proper" can be registered *)
    x = n = y -> ra_ag_unInjApprox x n (HVal:=HVal1) = n = ra_ag_unInjApprox y n (HVal:=HVal2).
  Proof.
    move=>EQ. destruct n as [|n]; first exact: dist_bound.
    ra_ag_destr; now firstorder.
  Qed.

  Lemma ra_ag_inj_unInjApprox x n {HVal: cmra_valid x n} t:
    ra_ag_inj t ⊑ x -> ra_ag_unInjApprox x n (HVal:=HVal) = n = Some t.
  Proof.
    rewrite ra_ag_pord. destruct x as [v ts tsx|]=>Heq; last contradiction.
    unfold ra_ag_inj in Heq. destruct Heq as [EQv EQts]. unfold ra_ag_unInjApprox.
    destruct n as [|n]; first exact: dist_bound. simpl. symmetry. eapply EQts.
  Grab Existential Variables.
  { rewrite EQv. apply HVal. }
  Qed.
  
  (* Provide a way to get the full T out of the agreement again. We don't need this, but I proved it before
     I realized. *)
  (* For this, we need a complete metric! *)
  Context {cmT: cmetric T}.

  Program Definition ra_ag_tschain v (ts: vChain v) (tsx: cvChain ts) {HVal: ↓(ag_inj v ts tsx)}: chain T :=
    fun i => ts i _.

  Instance ra_ag_tschain_c v (ts: vChain v) (tsx: cvChain ts) {HVal: ↓(ag_inj v ts tsx)} : cchain (ra_ag_tschain v ts tsx (HVal:=HVal)).
  Proof.
    intros n j m HLe1 HLe2. destruct n as [|n]; first by apply: dist_bound. unfold ra_ag_tschain.
    etransitivity; first by eapply (tsx (S n)).
    symmetry. etransitivity; first by eapply (tsx (S n)).
    eapply dist_refl; apply equivR. f_equiv. eapply ProofIrrelevance.
  Qed.

  Program Definition ra_ag_unInj x {HVal: ↓x}: option T :=
    match x with
    | ag_unit => None
    | ag_inj v ts tsx => Some (compl (ra_ag_tschain v ts tsx (HVal:=_)))
    end.

  Lemma ra_ag_unInj_dist x y {HVal1: ↓x} {HVal2: ↓y} n: (* The function is dependent, hence no "Proper" can be registered *)
    x = n = y -> ra_ag_unInj x (HVal:=HVal1) = n = ra_ag_unInj y (HVal:=HVal2).
  Proof.
    move=>EQ. destruct n as [|n]; first exact: dist_bound.
    destruct x as [xv xts xtsx|]; last first.
    { destruct y as [v ts tsx|]; first contradiction EQ. reflexivity. }
    destruct y as [yv yts ytsx|]; last contradiction EQ.
    destruct EQ as [_ EQts]. unfold ra_valid, ra_agree_valid in HVal1. unfold ra_valid, ra_agree_valid in HVal2.
    simpl. eapply umet_complete_extn. unfold ra_ag_tschain.
    eapply EQts. reflexivity.
  Qed.

  (* Correctness of the embedding (and of the entire consruction, really - together with the duplicability shown above) *)
  Lemma ra_ag_inj_unInj x {HVal: ↓x} t:
    ra_ag_inj t ⊑ x -> ra_ag_unInj x (HVal:=HVal) == Some t.
  Proof.
    rewrite ra_ag_pord. destruct x as [v ts tsx|]=>Heq; last contradiction.
    unfold ra_ag_inj in Heq. destruct Heq as [EQv EQts]. simpl. rewrite <-(umet_complete_const t).
    apply umet_complete_ext=>i. unfold ra_ag_tschain. unfold ra_ag_compinj_ts in EQts. symmetry.
    eapply EQts. rewrite EQv. apply HVal.
  Qed.

End Agreement.

Section AgreementMap.
  Context {T U: Type} `{cmT: cmetric T} `{cmU: cmetric U}.
  Local Open Scope pumet_scope.

  Program Definition ra_agree_map (f: T -n> U): ra_agree T -m> ra_agree U :=
    m[(fun x => match x with
                | ag_inj v ts tsx => ag_inj U v (fun n => compose f (ts n)) _
                | ag_unit => ag_unit U
                end)].
  Next Obligation.
    move=>n i HLe pv. simpl. eapply met_morph_nonexp. specialize (tsx n i HLe pv).
    rewrite tsx.
    eapply dist_refl. f_equiv. by eapply ProofIrrelevance.
  Qed.
  Next Obligation.
    move=> x y EQxy.
    destruct n as [|n]; first by apply: dist_bound.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); try (contradiction EQxy || reflexivity); [].
    destruct EQxy as [Hv Hts]. split; first assumption.
    move=>n' pv1 pv2 HLe. specialize (Hts n' pv1 pv2 HLe). unfold compose. rewrite Hts. reflexivity.
  Qed.
  Next Obligation.
    move=>x y EQxy. apply ra_ag_pord. apply ra_ag_pord in EQxy.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); try (contradiction EQxy || reflexivity); [].
    destruct EQxy as [EQv EQts]. split; first split.
    - intros (pv1 & pv2 & _). assumption.
    - move=>pv. move/EQv:(pv)=>[pv1 [pv2 EQ]]. exists pv1 pv2. unfold compose. rewrite EQ. reflexivity.
    - unfold compose. intros n [pv1 [pv2 EQ]] pv3. unfold ra_ag_compinj_ts. eapply met_morph_nonexp.  rewrite -EQts /ra_ag_compinj_ts. f_equiv. by eapply ProofIrrelevance.
  Grab Existential Variables.
  { rewrite EQv. assumption. }
  Qed.

  Global Instance ra_agree_map_resp: Proper (equiv ==> equiv) ra_agree_map.
  Proof.
    move=> x1 x2 EQx y.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); last reflexivity.
    split; first reflexivity.
    move=>n pv1 pv2. rewrite EQx. unfold compose. repeat f_equiv. eapply ProofIrrelevance.
  Qed.
  Global Instance ra_agree_map_dist n: Proper (dist n ==> dist n) ra_agree_map.
  Proof.
    move=> x1 x2 EQx y.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); last reflexivity.
    destruct n as [|n]; first by apply: dist_bound.
    split; first reflexivity.
    move=>n' pv1 pv2 HLe. rewrite /compose. eapply mono_dist; last first.
    - rewrite EQx. repeat f_equiv. eapply ProofIrrelevance.
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
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); last reflexivity.
    simpl. split; first reflexivity.
    intros n pv1 pv2. repeat f_equiv. eapply ProofIrrelevance.
  Qed.
  
  Context {U V: Type} `{cmU: cmetric U} `{cmV: cmetric V}.

  Lemma ra_agree_map_comp (f: T -n> U) (g: U -n> V): 
    (ra_agree_map g) ∘ (ra_agree_map f) == ra_agree_map (g <M< f).
  Proof.
    intros x.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); last reflexivity.
    simpl. split; first reflexivity.
    intros n pv1 pv2. repeat f_equiv. eapply ProofIrrelevance.
  Qed.
End AgreementMapComp.
