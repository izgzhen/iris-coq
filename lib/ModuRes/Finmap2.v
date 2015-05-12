Require Import ssreflect.
Require Import MetricCore.
Require Import Axioms.
Require Import PreoMet.
Require Import RA CMRA SPred.
Require Import Arith Min Max List ListSet Lists.

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


Delimit Scope finmap_scope with fm.
Local Open Scope finmap_scope.
Local Open Scope general_if_scope.
Infix "∈" := In (at level 31, no associativity) : finmap_scope.

Section Def.
  Context {K V : Type}.

  Definition findom_bound (finmap: K -> option V) (findom: list K): Prop :=
    forall k, finmap k <> None <-> k ∈ findom.

  Record FinMap `{eqK : DecEq K} :=
    mkFD {finmap :> K -> option V;
          findom : list K;
          findom_b : findom_bound finmap findom}.

  Context `{eqK : DecEq K}.

  Definition dom (f: FinMap) := filter_dupes [] (findom f).

  Lemma dom_nodup (f: FinMap): NoDup (dom f).
  Proof.
    unfold dom. apply filter_dupes_nodup.
  Qed.

End Def.

Arguments mkFD [K V] {eqK} _ _ _.
Arguments FinMap K V {_} : clear implicits.
Arguments finmap [K V] {eqK} _ _.
Arguments findom [K V] {eqK} _.
Arguments dom [K V] {eqK} _.
Arguments findom_b [K V] {eqK} _ {k}.
Notation "K '-f>' V" := (FinMap K V) (at level 45).

Section FinDom.
  Context {K} `{eqK : DecEq K}.

  Section Props.
    Context {V : Type} `{ev : Setoid V}.

    Program Definition fdEmpty : K -f> V := mkFD (fun _ => None) nil _.
    Next Obligation.
      move=>k /=. split; last tauto. move=>H. now apply H.
    Qed.

    Lemma fdLookup_notin_strong k (f : K -f> V) : (~ (k ∈ dom f)) <-> f k = None.
    Proof.
      destruct f as [f fd fdb]; unfold dom in *; simpl in *. split.
      - destruct (f k) as [v|] eqn:EQf; last (move=>_; reflexivity).
        move=>Hin. exfalso. apply Hin=>{Hin}. apply filter_dupes_in; first tauto.
        apply fdb. rewrite EQf. discriminate.
      - move=>EQf Hin. apply filter_dupes_isin in Hin. eapply fdb; last eassumption. tauto.
    Qed.

    Lemma fdLookup_notin k (f : K -f> V) : (~ (k ∈ dom f)) <-> f k == None.
    Proof.
      split ; intro H.
      + apply fdLookup_notin_strong in H ; rewrite H ; reflexivity.
      + destruct (f k) as [v|] eqn:EQf; first (contradiction H).
        apply fdLookup_notin_strong. assumption.
    Qed.
    
    Lemma fdLookup_in_strong (f : K -f> V) k: k ∈ dom f <-> f k <> None.
    Proof.
      destruct f as [f fd fdb]; unfold dom; simpl. split.
      - move=>Hin. apply filter_dupes_isin in Hin.
        destruct (f k) as [v|] eqn:EQf; first discriminate. exfalso.
        eapply fdb; last eassumption. tauto.
      - move=>EQf. apply filter_dupes_in; first tauto. apply fdb. assumption.
    Qed.

    Lemma fdLookup_in : forall (f : K -f> V) k, k ∈ dom f <-> f k =/= None.
    Proof.
      simpl. split.
      - move=>Hin. eapply fdLookup_in_strong in Hin. move=>Heq.
        apply Hin. destruct (f k); contradiction || reflexivity.
      - move=>Hneq. apply fdLookup_in_strong. destruct (f k); first discriminate.
        exfalso. now apply Hneq. 
    Qed.

    (* The definition of the domain here is carefully tuned to make the recursion principle
       less painful. *)
    Definition fdStrongUpdate_dom k (v: option V) (f: K -f> V) :=
      match v with
      | Some _ => k::(dom f)
      | None => match (dom f) with [] => []
                          | k'::dom' => if dec_eq k k' then dom' else filter_dupes [k] (findom f) end
      end.
    Program Definition fdStrongUpdate k v (f : K -f> V) : K -f> V :=
      mkFD (fun k' => if dec_eq k k' then v else f k')
           (fdStrongUpdate_dom k v f)
           _.
    Next Obligation.
      move=>k'. simpl. unfold fdStrongUpdate_dom. destruct v as [v|]; destruct (dec_eq k k') as [EQ|NEQ]; split; intros Hin.
      - left. assumption.
      - discriminate.
      - right. apply fdLookup_in_strong. assumption.
      - apply fdLookup_in_strong. destruct Hin as [EQ|?]; last assumption. contradiction.
      - exfalso. now apply Hin.
      - exfalso. subst k'. destruct (dom f) as [|k' d] eqn:EQdf; first contradiction.
        destruct (dec_eq k k') as [EQ|NEQ].
        + subst k'. assert (Hndup := dom_nodup f). rewrite EQdf in Hndup. inversion Hndup; subst. contradiction.
        + eapply filter_dupes_notin, Hin. left. reflexivity.
      - apply fdLookup_in_strong in Hin. destruct (dom f) as [|k'' dom'] eqn:Hdom; first assumption.
        destruct (dec_eq k k'') as [EQ'|NEQ'].
        + subst k''. destruct Hin as [?|?]; first contradiction. assumption.
        + unfold dom in Hdom. rewrite -Hdom in Hin.
          apply filter_dupes_isin in Hin. apply filter_dupes_in.
          * move=>[EQk|[]]. contradiction.
          * tauto.
      - apply fdLookup_in_strong. destruct (dom f) as [|k'' dom'] eqn:Hdom; first assumption.
        destruct (dec_eq k k'') as [EQ'|NEQ'].
        + subst k''. right. assumption.
        + rewrite -Hdom /dom. apply filter_dupes_in; first tauto.
          apply filter_dupes_isin in Hin. tauto.
    Qed.
      
    Lemma fdStrongUpdate_eq k v f : fdStrongUpdate k v f k = v.
    Proof.
      simpl finmap. destruct (dec_eq k k) as [EQ|NEQ]; last (exfalso; now apply NEQ). reflexivity.
    Qed.

    Lemma fdStrongUpdate_neq k k' v f (Hneq : k <> k') : fdStrongUpdate k v f k' = f k'.
    Proof.
      simpl finmap. destruct (dec_eq k k') as [EQ|NEQ]; first contradiction. reflexivity.
    Qed.

    Program Definition fdLookup_indom f k (Hindom: k ∈ dom f): V :=
      match f k with
      | Some v => v
      | None => !
      end.
    Next Obligation.
      apply fdLookup_in_strong in Hindom. rewrite Heq_anonymous in Hindom. apply Hindom. reflexivity.
    Qed.

    Lemma fdLookup_indom_corr f k (Hindom: k ∈ dom f) v:
      fdLookup_indom f k Hindom = v <-> f k = Some v.
    Proof.
      split.
      - rewrite /fdLookup_indom. ddes (f k) at 1 3 as [v'|] deqn:EQf.
        + move=><-. now symmetry.
        + unfold False_rect. destruct (_:False).
      - rewrite /fdLookup_indom. ddes (f k) at 1 3 4 as [v'|] deqn:EQf.
        + by move=>[EQ].
        + move=>?. discriminate.
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

    Global Instance fdLookup_proper : Proper (equiv ==> eq ==> equiv) (finmap (V := V)).
    Proof.
      intros f1 f2 HEqf k1 k2 HEqk; subst; apply HEqf.
    Qed.

    Lemma dom_proper {f1 f2}:
      f1 == f2 -> (forall k, k ∈ dom f1 <-> k ∈ dom f2).
    Proof.
      move=>EQf k. split; rewrite !fdLookup_in; move=>Hin.
      - now rewrite -EQf.
      - now rewrite EQf.
    Qed.
    
    Lemma fdEmpty_dom f:
      f == fdEmpty <-> (forall k, ~k ∈ dom f).
    Proof.
      split.
      - move=>Hemp k Hin. apply (dom_proper Hemp) in Hin. exact Hin.
      - move=>Hemp k. destruct (f k) as [v|] eqn:EQf.
        + exfalso. apply (Hemp k). apply fdLookup_in_strong. rewrite EQf. discriminate.
        + reflexivity.
    Qed.

    Definition dist_fd n (f1 f2 : K -f> V) :=
      forall k, f1 k = n = f2 k.

    Global Program Instance metric_findom : metric (K -f> V) := mkMetr dist_fd.
    Next Obligation.
      revert n; intros [| n] f1 f2 EQf g1 g2 EQg; [reflexivity |]; split;
      intros EQ k; [symmetry in EQf, EQg |]; rewrite -> EQf, EQg; apply EQ.
    Qed.
    Next Obligation.
      split; intros HEq.
      - intros k; rewrite <- dist_refl; intros [| n]; [reflexivity; exact None | apply (HEq (S n) k) ].
      - intros n; intros k. apply dist_refl. apply HEq.
    Qed.
    Next Obligation.
      revert n; intros n x y HS; intros k; symmetry; apply HS.
    Qed.
    Next Obligation.
      revert n; intros n x y z Hxy Hyz; intros k; etransitivity; [apply Hxy | apply Hyz].
    Qed.
    Next Obligation.
      intros k; eapply dist_mono, H.
    Qed.
    Next Obligation.
      move=>k. apply dist_bound.
    Qed.
    
    Global Instance lookup_dist n : Proper (dist n ==> eq ==> dist n) (finmap (V := V)).
    Proof.
      intros f1 f2 HEqf k1 k2 HEqk; subst. 
      destruct n; first now auto.
      now apply HEqf.
    Qed.

    Definition finmap_chainx (σ : chain (K -f> V)) {σc : cchain σ} x : chain (option V) :=
      fun n => (σ n) x.

    Program Instance finmap_chainx_cauchy (σ : chain (K -f> V)) {σc : cchain σ} x :
      cchain (finmap_chainx σ x).
    Next Obligation.
      assert (σc':=σc).
      specialize (σc' n i j HLei HLej x). unfold finmap_chainx. assumption.
    Qed.
    
    Program Definition findom_lub (σ : chain (K -f> V)) (σc : cchain σ) : K -f> V :=
      mkFD (fun x => compl (finmap_chainx σ x)) (findom (σ 1)) _.
    Next Obligation.
      move=>k. assert(H:=conv_cauchy (finmap_chainx σ k) 1 1 (le_refl _)).
      split; move=>Hin.
      - simpl in Hin. assert (Hin': (finmap_chainx σ k) 1 <> None).
        { move=>EQ. rewrite EQ in H. apply Hin. symmetry in H. simpl in H.
          destruct (option_compl (finmap_chainx σ k)); first contradiction.
          reflexivity. }
        clear Hin. apply (findom_b (σ 1)). assumption.
      - simpl in H. destruct (option_compl (finmap_chainx σ k)); first discriminate.
        apply findom_b in Hin. rewrite /finmap_chainx in H. destruct ((σ 1) k); first contradiction.
        assumption.
    Qed.

    Global Program Instance findom_cmetric : cmetric (K -f> V) := mkCMetr findom_lub.
    Next Obligation.
      move => [| n] ; [now auto|]. 
      move => i LEi k. unfold findom_lub. simpl finmap.
      assert (H := conv_cauchy (finmap_chainx σ k) _ _ LEi). exact H.
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

    Global Instance findom_pcmType : pcmType (K -f> V).
    Proof.
      split.
      - intros σ ρ σc ρc HSub k.
        eapply pcm_respC; [now auto with typeclass_instances | intros].
        apply: HSub.
    Qed.

    Lemma dom_ext (m1 m2 : K -f> V) k (HSub : m1 ⊑ m2) (HIn : k ∈ dom m1) : k ∈ dom m2.
    Proof.
      specialize (HSub k).
      apply fdLookup_in in HIn.
      apply fdLookup_in. destruct (m2 k) as [v'|].
      - move=>[].
      - exfalso. apply HIn. destruct (m1 k); contradiction || reflexivity.
    Qed.

  End Instances.

  Section Map.
    Context {U V} `{pcmU : pcmType U} `{cmV : pcmType V}.

    Definition fdMap_pre (m : U -> V) (f: K -f> U) : K -> option V :=
      fun k => match (f k) with None => None | Some v => Some (m v) end.

    (* The nicest solution here would be to have a map on option... *)
    Program Definition fdMapRaw (m : U -> V) : (K -f> U) -> (K -f> V) :=
      fun f => mkFD (fdMap_pre m f) (findom f) _.
    Next Obligation.
      unfold fdMap_pre. move=>k /=. split; move=> Hneq; destruct (f k) eqn:EQf.
      - apply findom_b. rewrite EQf. discriminate.
      - exfalso. now apply Hneq.
      - discriminate.
      - exfalso. apply findom_b in Hneq. rewrite EQf in Hneq. now apply Hneq.
    Qed.
    
    Program Definition fdMapMorph (m : U -n> V) : (K -f> U) -n> (K -f> V) :=
      n[(fdMapRaw m)].
    Next Obligation.
      unfold fdMapRaw, fdMap_pre.
      intros m1 m2 HEq; destruct n as [| n]; [apply dist_bound |]; intros k; simpl; specialize (HEq k).
      destruct (m1 k) as [u1 |] eqn: HFnd1; destruct (m2 k) as [u2 |] eqn: HFnd2; try contradiction HEq; [|exact I].
      apply met_morph_nonexp. exact HEq.
    Qed.

    Program Definition fdMap (m : U -m> V) : (K -f> U) -m> (K -f> V) :=
      m[(fdMapMorph m)].
    Next Obligation.
      move=>f1 f2 EQf k.
      change (fdMapMorph m f1 k = n = fdMapMorph m f2 k).
      now apply (met_morph_nonexp (fdMapMorph m)).
    Qed.
    Next Obligation.
      unfold fdMapRaw, fdMap_pre. intros m1 m2 Subm k; specialize (Subm k); destruct (m1 k) as [u1 |] eqn: HFnd1.
      - rewrite /= HFnd1 /=. destruct (m2 k) as [u2 |] eqn: HFnd2; [| contradiction Subm].
        apply mu_mono, Subm.
      - rewrite /= HFnd1 /=. destruct (m2 k); exact I.
    Qed.

    Global Instance fdMap_resp : Proper (equiv ==> equiv) fdMap.
    Proof.
      intros f1 f2 EQf m k; rewrite /opt_eq /fdMap /= /fdMap_pre. destruct (m k).
      - apply EQf.
      - reflexivity.
    Qed.

    Global Instance fdMap_nonexp n : Proper (dist n ==> dist n) fdMap.
    Proof.
      intros f1 f2 EQf m k. destruct n as [|n]; first exact: dist_bound.
      rewrite /opt_eq /fdMap /= /fdMap_pre. destruct (m k).
      - apply EQf.
      - reflexivity.
    Qed.

    Global Instance fdMap_monic : Proper (pord ==> pord) fdMap.
    Proof.
      intros f1 f2 EQf m k; rewrite /opt_eq /fdMap /= /fdMap_pre. destruct (m k) as [u |] eqn: HFnd.
      - simpl. apply EQf.
      - reflexivity.
    Qed.

  End Map.

  Notation "fd [ x -> v ]" := (fdStrongUpdate x (Some v) fd) (at level 50, x at next level) : finmap_scope.
  Notation "fd \ x" := (fdStrongUpdate x None fd) (at level 50) : finmap_scope.

  Section MapProps.

    Context U V W `{pcmU : pcmType U} `{cmV : pcmType V} `{cmW : pcmType W}.

    Lemma fdMap_comp (f : U -m> V) (g : V -m> W) :
      (fdMap g ∘ fdMap f == fdMap (g ∘ f))%pm.
    Proof.
      intros m k. rewrite /= /fdMap /fdMapRaw /fdMap_pre /=.
      destruct (m k); reflexivity.
    Qed.

    Lemma fdMap_id : fdMap (pid U) == (pid (K -f> U)).
    Proof.
      intros w k; rewrite /= /fdMap /fdMap_pre /=.
      destruct (w k); reflexivity.
    Qed.
  End MapProps.

    
(*  Section Filter.
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

  End Filter.*)

  
(*  Section Compose.
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

  End Compose.*)

  Section Induction.
    Context {V : Type} `{eV : Setoid V}.

    Section Recursion.
      Context (T: (K -f> V) -> Type)
              (Text: forall (f1 f2: K -f> V), (forall k, f1 k = f2 k) -> dom f1 = dom f2 -> T f1 -> T f2)
              (Temp: T fdEmpty).
      (* TODO: Why can't I use the sugar for finmaps?? *)
      Context (Tstep: forall (k:K) (v:V) (f: K -f> V), ~(k ∈ dom f) -> T f -> T (fdStrongUpdate k (Some v) f)).

      Definition fdRectInner: forall l f, dom f = l -> T f.
      Proof.
        refine (fix F (l: list K) :=
                  match l as l return (forall f, dom f = l -> T f) with
                  | [] => fun f Hdom => Text fdEmpty f _ _ Temp
                  | k::l => fun f Hdom => let f' := f \ k in
                                          let Hindom: k ∈ dom f := _ in
                                          let v' := fdLookup_indom f k Hindom in
                                          Text (fdStrongUpdate k (Some v') f') f _ _
                                               (Tstep k v' f' _ (F l f' _))
                  end); clear F.
        - move=>k /=. symmetry. apply fdLookup_notin_strong. rewrite Hdom. tauto.
        - rewrite Hdom. reflexivity.
        - rewrite Hdom. left. reflexivity.
        - subst f'. move=>k'. destruct (dec_eq k k') as [EQ|NEQ].
          + subst k'. rewrite fdStrongUpdate_eq. subst v'. symmetry. eapply fdLookup_indom_corr.
            reflexivity.
          + erewrite !fdStrongUpdate_neq by assumption. reflexivity.
        - rewrite Hdom /f'. rewrite /dom /=. f_equal. rewrite /dom /= Hdom.
          destruct (dec_eq k k) as [_|NEQ]; last (exfalso; now apply NEQ).
          assert (Hnod := dom_nodup f). rewrite Hdom in Hnod.
          assert (Hfilt1: (filter_dupes [] l0) = l0).
          { apply filter_dupes_id. simpl. inversion Hnod; subst. assumption. }
          rewrite Hfilt1. apply filter_dupes_id. assumption.
        - subst f'. apply fdLookup_notin. rewrite fdStrongUpdate_eq. reflexivity.
        - subst f'. rewrite /dom /fdStrongUpdate /=.
          rewrite Hdom. destruct (dec_eq k k) as [_|NEQ]; last (exfalso; now apply NEQ).
          apply filter_dupes_id with (dupes:=[]); simpl.
          assert (Hno:= dom_nodup f). rewrite Hdom in Hno.
          inversion Hno; subst. assumption.
      Defined.

      Definition fdRect: forall f, T f :=
        fun f => fdRectInner (dom f) f eq_refl.
    End Recursion.

    (* No need to restrict this Lemma to fdRectInner - that just messes up the details. *)
    Lemma fdRectInner_eqL l l' f (Heq: dom f = l) (Heq': dom f = l')
          (T: (K -f> V) -> Type) (F: forall l (f: K -f> V), dom f = l -> T f) :
      F l f Heq = F l' f Heq'.
    Proof.
      assert (Heql: l = l').
      { transitivity (dom f); first symmetry; assumption. }
      revert Heq'.
      refine (match Heql in eq _ l'' return (forall Heq' : dom f = l'', F l f Heq = F l'' f Heq') with
              | eq_refl => _
              end).
      move=>Heq'. f_equal. apply ProofIrrelevance.
    Qed.

    Section Fold.
      Context {T: Type}.
      Context (Temp: T) (Tstep: K -> V -> T -> T).
      
      Definition fdFold: (K -f> V) -> T :=
        fdRect (fun _ => T) (fun _ _ _ _ => id) (Temp)
               (fun k v _ _ => Tstep k v).

      Lemma fdFoldEmpty: fdFold fdEmpty = Temp.
      Proof.
        reflexivity.
      Qed.

      Lemma fdRectInner_eqLF l1 f1 l2 f2 (Heq1: dom f1 = l1) (Heq2: dom f2 = l2):
        l1 = l2 -> (forall k, f1 k = f2 k) ->
        fdRectInner (fun _ => T) (fun _ _ _ _ => id) (Temp) (fun k v _ _ => Tstep k v) l1 f1 Heq1 =
        fdRectInner (fun _ => T) (fun _ _ _ _ => id) (Temp) (fun k v _ _ => Tstep k v) l2 f2 Heq2.
      Proof.
        move=>Heql. assert (Heq': dom f2 = l1).
        { now subst l2. }
        transitivity (fdRectInner (fun _ => T) (fun _ _ _ _ => id) (Temp) (fun k v _ _ => Tstep k v) l1 f2 Heq'); last first.
        { rewrite (fdRectInner_eqL l1 l2). reflexivity. }
        subst l2. clear Heql. revert f1 f2 Heq1 Heq' H. induction l1; intros f1 f2 Heq1 Heq2 Heqf.
        - reflexivity.
        - simpl. unfold id.
          assert (Hf: exists v, f1 a = Some v /\ f2 a = Some v).
          { destruct (f1 a) as [v|] eqn:EQf.
            - exists v. split; first reflexivity. rewrite -Heqf. assumption.
            - exfalso. apply fdLookup_notin_strong in EQf. apply EQf. rewrite Heq1.
              left. reflexivity. }
          destruct Hf as [v [Heqf1 Heqf2]].
          eapply fdLookup_indom_corr in Heqf1. erewrite Heqf1.
          eapply fdLookup_indom_corr in Heqf2. erewrite Heqf2.
          f_equal. eapply IHl1. move=>k.
          destruct (dec_eq a k) as [EQ|NEQ].
          + subst a. rewrite !fdStrongUpdate_eq. reflexivity.
          + erewrite !fdStrongUpdate_neq by assumption. now apply Heqf.
      Qed.

      Lemma fdFoldUpdate f k v:
        ~k ∈ (dom f) ->
        fdFold (fdStrongUpdate k (Some v) f) = Tstep k v (fdFold f).
      Proof.
        move=>Hindom. rewrite /fdFold /fdRect {2}/dom /=.
        assert (Hl: fdStrongUpdate k (Some v) f k = Some v).
        { apply fdStrongUpdate_eq. }
        eapply fdLookup_indom_corr in Hl. erewrite Hl.
        unfold id. f_equal.
        apply fdRectInner_eqLF.
        - apply filter_dupes_id. apply NoDup_cons.
          + exact Hindom.
          + apply filter_dupes_nodup.
        - move=>k'. destruct (dec_eq k k') as [EQ|NEQ].
          + subst k'. rewrite fdStrongUpdate_eq. symmetry. apply fdLookup_notin_strong. assumption.
          + erewrite !fdStrongUpdate_neq by assumption. reflexivity.
      Qed.

      (* Alternative, more direct formulation of fold. *)
      Definition fdFold'Inner fLookup k: T -> T :=
        fun t => match fLookup k with
                 | Some v => Tstep k v t
                 (* We know this case never happens, but that would be very annoying to make use of here. *)
                 | None => t end.
      Definition fdFold' (f: K -f> V): T :=
        fold_right (fdFold'Inner f) Temp (dom f).

      (* They are equivalent. *)
      Lemma fdFoldBehavior f:
        fdFold f = fdFold' f.
      Proof.
        revert f. elim/fdRect.
        - move=>f1 f2 EQf EQdom EQfd. etransitivity; last (etransitivity; first exact EQfd).
          + rewrite /fdFold /fdRect. apply fdRectInner_eqLF.
            * symmetry. assumption.
            * move=>k. symmetry. now apply EQf.
          + rewrite /fdFold' /fdFold'Inner. apply fold_ext_restr.
            * assumption.
            * reflexivity.
            * move=>k t _. rewrite EQf. reflexivity.
        - reflexivity.
        - move=>k v f Hnin Heq. erewrite fdFoldUpdate by assumption.
          rewrite /fdFold' /= /fdFold'Inner.
          destruct (dec_eq k k) as [_|NEQ]; last (exfalso; now apply NEQ). f_equal. rewrite Heq.
          rewrite /fdFold' /fdFold'Inner. apply fold_ext_restr.
          + symmetry. apply filter_dupes_id. apply NoDup_cons; first assumption.
            apply dom_nodup.
          + reflexivity.
          + clear -Hnin. move=>k' t Hin.
            destruct (dec_eq k k'); last reflexivity. exfalso.
            subst k'. contradiction.
      Qed.

    End Fold.

  Section FoldMorph.
    Context {T: Type} `{Setoid T}.

    Definition fdFoldMorph (Tstart: T) (Tstep: K -> V -=> T -=> T) (f: K -f> V) :=
      fdFold Tstart (fun k v t => Tstep k v t) f.

    Lemma fdFoldExtT: Proper (equiv ==> equiv (A := ) ==> equiv ==> equiv) fdFold.
    
    Context (Tstep1 Tstep2: K -> V -=> T -=> T).
    Context {Tstep_eq: forall k v t, eqT (Tstep1 k v t) (Tstep2 k v t)}.
    Context (Temp1 Temp2: T) {Temp_eq: eqT Temp1 Temp2}.

    

    (* We need the step function to preserve equivalence of states (T). Ouch. *)
    Lemma fdFoldExtT: Proper (equiv ==> equiv ==> eq ==> equiv) (@fdFold T).
    Proof.
      move=>Tstart1 Tstart2 EQTstart Tstep1 Tstep2 EQTstep f f' EQf. subst f'.
      rewrite !fdFoldBehavior. rewrite /fdFold'.
      etransitivity; last (etransitivity; first eapply fold_ext).
      f_equiv.
      eapply fold_ext. remember (dom f) as l. clear Heql.
      revert f. induction l; simpl; intros f.
      - assumption.
      - destruct (f a).
        + rewrite IHl. apply EQTstep.
        + apply IHl.
    Qed.
      

    Definition fdStep_comm (Tstep: K -> V -> T -> T): Prop :=
      forall (k1 k2:K) (v1 v2:V),
        compose (Tstep k1 v1) (Tstep k2 v2) == compose (Tstep k2 v2) (Tstep k1 v1).


    Section FoldExtPerm.
      Context (Temp: T) (Tstep: K -> V -> T -> T).
      Context (Tstep_proper: Proper (eq ==> equiv ==> equiv ==> equiv) Tstep) (Tstep_comm: fdStep_comm Tstep).
    
      Lemma fdFoldExtP: Proper (equiv (A:= K -f> V) ==> equiv) (fdFold Temp Tstep).
      Proof.
        move=>f1 f2 EQf. rewrite !fdFoldBehavior.
        rewrite /fdFold'. etransitivity; last eapply fold_perm.
        - rewrite -/fdFold'. eapply fdFoldExtT.
        

  End FoldExtensionality.

End FinDom.

(*Arguments fdMap {K cT ord equ preo ord_part compK U V eqT mT cmT pTA pcmU eqT0 mT0 cmT0 pTA0 cmV} _.*)

Section RA.
  Context {I : Type} {S : Type} `{eqI : DecEq I} `{RAS : RA S}.
  Implicit Type (i : I) (s : S) (f g : I -f> S).

  Local Open Scope ra_scope.
  
  Global Instance ra_type_finprod : Setoid (I -f> S) := _.
  Global Program Instance ra_unit_finprod : RA_unit (I -f> S) :=
    fdMapRaw ra_unit.

  Definition finprod_op (s1 s2: option S) :=
    match s1, s2 with
    | Some s1, Some s2 => Some (s1 · s2)
    | Some s1, None    => Some s1
    | None   , Some s2 => Some s2
    | None   , None    => None
    end.
  Global Program Instance ra_op_finprod : RA_op (I -f> S) :=
    fun f1 f2 => mkFD (fun i => finprod_op (f1 i) (f2 i)) (findom f1 ++ findom f2) _.
  Next Obligation.
    rewrite /finprod_op. move=>i /=.
    destruct (f1 i) as [s1|] eqn:EQf1; destruct (f2 i) as [s2|] eqn:EQf2; simpl; intros Hin; apply in_app_iff.
    - left. apply (findom_b f1). rewrite EQf1. discriminate.
    - left. apply (findom_b f1). rewrite EQf1. discriminate.
    - right. apply (findom_b f2). rewrite EQf2. discriminate.
    - exfalso. now apply Hin.
  Qed.
    
                                
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
    - cut (forall v, (1 t · t) k == v <-> t k == v).
      + intros. specialize (H ((1 t · t) k)). symmetry. apply H. reflexivity.
      + move => [v|].
        * split; [move => /fdComposeP'; move => [[v1 [v2 [Hv [[] //]]]]|[[[] //]|[H1 H2 //]]]|].
          move=>Ht. apply fdComposeP'. by right; right.
        * split; [move/fdComposePN' => [] //|move => ?; apply fdComposePN'; split; now auto].
    - split; move => Hx k v Hy; apply (Hx k); by rewrite ?H // -?H.
    - by exists (1 t') => k.
    - split; move => Hx k v Hy; apply (Hx k); by rewrite ?H // -?H.
    - split; move => Hx k v Hy; apply (Hx k); by rewrite ?H // -?H.
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

Section VIRA.
  Context {I : Type} `{CI : comparable I}.
  Context {T: Type} `{raT: RA T}.

  Global Instance vira_finmap: VIRA (I -f> T).
  Proof.
    eexists fdEmpty. move=>i s [].
  Qed.
    
End VIRA.


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

  Global Program Instance finmap_cmra_valid: CMRA_valid (I -f> T) :=
    fun f => mkSPred (fun n => forall i s, f i == Some s -> cmra_valid s n) _.
  Next Obligation.
    move=>n m Hle /= H i s EQ. eapply dpred; last eapply H; eassumption.
  Qed.
    
  Global Instance finmap_cmra : CMRA (I -f> T).
  Proof.
    split.
    - move=>n f1 f2 EQf g1 g2 EQg.
      destruct n as [|n]; first by apply: dist_bound.
      move => k. 
      case Hf1g1: ((f1 · g1) k) => [v1|];
      case Hf2g2: ((f2 · g2) k) => [v2|];
      move : Hf1g1 Hf2g2 (EQf k) (EQg k) => // /equivR Hf1g1 /equivR Hf2g2.
      + move/fdComposeP : (Hf1g1) => [[vf1 [vg1 [<- [-> ->]]]]|[[-> ->]|[-> ->]]];
        move/fdComposeP : (Hf2g2) => [[vf2 [vg2 [<- [-> ->]]]]|[[-> ->]|[-> ->]]];
        move => // /= -> ->. reflexivity.
      + move/fdComposeP : (Hf1g1) => [[vf1 [vg1 [<- [-> ->]]]]|[[-> ->]|[-> ->]]];
        move/fdComposePN : (Hf2g2) => [-> ->];
        now move => // /= -> ->. 
      + move/fdComposePN : (Hf1g1) => [-> ->];
        move/fdComposeP : (Hf2g2) => [[vf2 [vg2 [<- [-> ->]]]]|[[-> ->]|[-> ->]]];
        now move => // /= -> ->.
    - by move => [|n] f1 f2 D12.
    - move => [|n] f1 f2 D12 i LTin; first inversion LTin.
        unfold cmra_valid. 
      split => H1 k s Hk.
      + case Hk' : (f1 k) => [s'|]. 
        * eapply cmra_valid_dist, H1; [symmetry|eassumption|apply/equivR; eassumption].
          move : (D12 k). by rewrite Hk Hk'. 
        * move : (D12 k). by rewrite Hk Hk'. 
      + case Hk' : (f2 k) => [s'|]. 
        * eapply cmra_valid_dist, H1; [|eassumption|apply/equivR; eassumption].
          move : (D12 k). by rewrite Hk Hk'. 
        * move : (D12 k). by rewrite Hk Hk'. 
    - move => f1. split => [H k s H1|H i k s H1].
      + apply cmra_ra_valid. move => i. exact: (H i k s H1).
      + apply cmra_ra_valid. exact (H k s H1).
    - move=>f1 f2 n Hval /= i s H. 
      case H2 : (f2 i) => [s2|]; move/equivR in H2.
      + assert (fdCompose ra_op f1 f2 i == Some (ra_op s s2)). 
        { apply fdComposeP'. left; exists s s2; repeat split; now auto. }
        move/Hval in H0. by move/cmra_op_valid in H0.
      + assert (fdCompose ra_op f1 f2 i == Some s).
        { apply fdComposeP'. right; left; now auto. }
        move/Hval in H0. assumption.
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
