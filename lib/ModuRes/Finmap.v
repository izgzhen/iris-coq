Require Import Ssreflect.ssreflect Omega.
Require Import Arith Min Max List ListSet Lists.
Require Import MetricCore.
Require Import PreoMet.
Require Import RA CMRA SPred.

Set Bullet Behavior "Strict Subproofs".


Delimit Scope finmap_scope with fm.
Local Open Scope finmap_scope.
Local Open Scope general_if_scope.
Infix "∈" := In (at level 31, no associativity) : finmap_scope.

Section Def.
  Context {K V : Type}.

  Definition findom_bound (finmap: K -> option V) (findom: list K): Prop :=
    forall k, finmap k <> None -> k ∈ findom.
  Definition findom_approx (finmap: K -> option V) (findom: list K): Prop :=
    forall k, finmap k <> None <-> k ∈ findom.

  Record FinMap `{eqK : DecEq K} :=
    mkFD {finmap :> K -> option V;
          findom : list K;
          findom_b : findom_approx finmap findom}.

  Context `{eqK : DecEq K}.

  Definition dom (f: FinMap) := filter_dupes [] (findom f).

  Lemma dom_nodup (f: FinMap): NoDup (dom f).
  Proof.
    unfold dom. apply filter_dupes_nodup.
  Qed.

  Fixpoint filter_None (f: K -> option V) (l: list K) :=
    match l with
    | [] => []
    | k::l => match f k with
              | Some _ => k::(filter_None f l)
              | None   => filter_None f l
              end
    end.

  Lemma filter_None_isin f l k:
    k ∈ filter_None f l -> f k <> None.
  Proof.
    induction l.
    - intros [].
    - simpl. destruct (f a) eqn:EQf.
      + move=>[EQ|Hin].
        * subst a. rewrite EQf. discriminate.
        * apply IHl. exact Hin.
      + exact IHl.
  Qed.

  Lemma filter_None_in f l k:
    f k <> None -> k ∈ l -> k ∈ filter_None f l.
  Proof.
    induction l.
    - move=>_ [].
    - move=>Hneq [EQ|Hin].
      + subst a. simpl. destruct (f k); last (exfalso; now apply Hneq).
        left. reflexivity.
      + simpl. destruct (f a); first right; apply IHl; assumption.
  Qed.

  Program Definition mkFDbound (f: K -> option V) (l: list K)
          (Hbound: findom_bound f l) :=
    mkFD _ f (filter_None f l) _.
  Next Obligation.
    move=>k. split.
    - move=>Hnon. apply filter_None_in; first assumption.
      apply Hbound. assumption.
    - move/filter_None_isin. tauto.
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

    Lemma fdLookup_indom_pi f k (Hindom1: k ∈ dom f) (Hindom2: k ∈ dom f):
      fdLookup_indom f k Hindom1 = fdLookup_indom f k Hindom2.
    Proof.
      rewrite /fdLookup_indom. ddes (f k) at 1 3 7 as [v|] deqn:EQf.
      - reflexivity.
      - exfalso. apply fdLookup_in_strong in Hindom1. apply Hindom1. now rewrite -EQf.
    Qed.

  End Props.

  Section Instances.
    Context {V: Type}.

    Definition equal_fd (f1 f2 : K -f> V):Prop :=
      (forall k, f1 k = f2 k) /\ dom f1 = dom f2.

    Global Instance equal_fd_e: Equivalence equal_fd.
    Proof.
      split.
      - intros m. split; intros; reflexivity.
      - intros m1 m2 [Hf Hdom]. split; intros; symmetry; now auto.
      - intros m1 m2 m3 [Hf12 Hdom12] [Hf23 Hdom23]. split; intros; etransitivity; now eauto.
    Qed.

    Global Instance equal_fd_lookup:
      Proper (equal_fd ==> eq ==> eq) (finmap (eqK:=eqK)).
    Proof.
      move=>f1 f2 EQf k1 k2 EQk. subst k1. apply EQf.
    Qed.

    Global Instance equal_fd_dom:
      Proper (equal_fd ==> eq) (dom (eqK:=eqK)).
    Proof.
      move=>f1 f2 EQf. apply EQf.
    Qed.

    Context `{cV : pcmType V}.

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
      intros f1 f2 EQf g1 g2 EQg; split;
      intros EQ k; [symmetry in EQf, EQg |]; rewrite -> EQf, EQg; apply EQ.
    Qed.
    Next Obligation.
      split; intros HEq.
      - intros k; rewrite <- dist_refl; intros n. apply (HEq n k).
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
      mkFDbound (fun x => compl (finmap_chainx σ x)) (findom (σ 1)) _.
    Next Obligation.
      move=>k /= Hin.
      assert(H:=conv_cauchy (finmap_chainx σ k) 1 1 (le_refl _)).
      simpl in Hin. assert (Hin': (finmap_chainx σ k) 1 <> None).
      { move=>EQ. rewrite EQ in H. apply Hin. symmetry in H. simpl in H.
        destruct (option_compl (finmap_chainx σ k)); first contradiction.
        reflexivity. }
      clear Hin. apply (findom_b (σ 1)). assumption.
    Qed.

    Global Program Instance findom_cmetric : cmetric (K -f> V) := mkCMetr findom_lub.
    Next Obligation.
      move => n i LEi k. unfold findom_lub. simpl finmap.
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

  Section Update.
    Context {V: Type} `{eqV: Setoid V}.
    
    (* The definition of the domain here is carefully tuned to make the recursion principle
       less painful. *)
    Definition fdStrongUpdate_dom k (v: option V) (f: K -f> V) :=
      match v with
      | Some _ => k::(dom f)
      | None => match (dom f) with [] => []
                          | k'::dom' => if dec_eq k k' then dom' else filter_dupes [k] (dom f) end
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
          rewrite Hdom in Hin. apply filter_dupes_in.
          * move=>[EQk|[]]. contradiction.
          * assumption.
      - apply fdLookup_in_strong. destruct (dom f) as [|k'' dom'] eqn:Hdom; first assumption.
        destruct (dec_eq k k'') as [EQ'|NEQ'].
        + subst k''. right. assumption.
        + apply filter_dupes_isin in Hin. tauto.
    Qed.
      
    Lemma fdStrongUpdate_eq k v f : fdStrongUpdate k v f k = v.
    Proof.
      simpl finmap. rewrite DecEq_refl. reflexivity.
    Qed.

    Lemma fdStrongUpdate_neq k k' v f (Hneq : k <> k') : fdStrongUpdate k v f k' = f k'.
    Proof.
      simpl finmap. destruct (dec_eq k k') as [EQ|NEQ]; first contradiction. reflexivity.
    Qed.

    Lemma fdStrongUpdateShadow k v1 v2 f:
      fdStrongUpdate k v1 (fdStrongUpdate k v2 f) == fdStrongUpdate k v1 f.
    Proof.
      move=>i. simpl. destruct (dec_eq k i); reflexivity.
    Qed.

    Lemma fdStrongUpdateCommute k1 v1 k2 v2 f:
      k1 <> k2 -> fdStrongUpdate k1 v1 (fdStrongUpdate k2 v2 f) == fdStrongUpdate k2 v2 (fdStrongUpdate k1 v1 f).
    Proof.
      move=>Hineq i. simpl. destruct (dec_eq k1 i) as [EQ1|NEQ1], (dec_eq k2 i) as [EQ2|NEQ2]; try reflexivity; [].
      subst. exfalso. now apply Hineq.
    Qed.

    Global Instance fdStrongUpdate_equal k v:
      Proper (equal_fd ==> equal_fd) (fdStrongUpdate k v).
    Proof.
      move=>f1 f2 [Hf Hdom]. split.
      - move=>k'. simpl. rewrite Hf. reflexivity.
      - rewrite /fdStrongUpdate /dom /= /fdStrongUpdate_dom. rewrite Hdom. reflexivity.
    Qed.

  End Update.


  Section Map.
    Context {U V} `{pcmU : pcmType U} `{cmV : pcmType V}.

    Definition fdMap_pre (m : U -> V) (f: K -f> U) : K -> option V :=
      fun k => match (f k) with None => None | Some v => Some (m v) end.

    (* The nicest solution here would be to have a map on option... *)
    Program Definition fdMapRaw (m : U -> V) : (K -f> U) -> (K -f> V) :=
      fun f => mkFD (fdMap_pre m f) (findom f) _.
    Next Obligation.
      unfold fdMap_pre, findom_approx. move=>k. rewrite -(findom_b f).
      destruct (f k); last tauto.
      split; discriminate.
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

  Section Induction.
    Context {V : Type} `{eV : Setoid V}.

    Section Recursion.
      Context (T: (K -f> V) -> Type)
              (Text: forall (f1 f2: K -f> V), equal_fd f1 f2 -> T f1 -> T f2)
              (Temp: T fdEmpty).
      (* TODO: Why can't I use the sugar for finmaps?? *)
      Context (Tstep: forall (k:K) (v:V) (f: K -f> V), ~(k ∈ dom f) -> T f -> T (fdStrongUpdate k (Some v) f)).

      Definition fdRectInner: forall l f, dom f = l -> T f.
      Proof.
        refine (fix F (l: list K) :=
                  match l as l return (forall f, dom f = l -> T f) with
                  | [] => fun f Hdom => Text fdEmpty f _ Temp
                  | k::l' => fun f Hdom => let f' := f \ k in
                                           let Hindom: k ∈ dom f := _ in
                                           let v' := fdLookup_indom f k Hindom in
                                           Text (fdStrongUpdate k (Some v') f') f _
                                                (Tstep k v' f' _ (F l' f' _))
                  end); clear F.
        - split.
          + move=>k /=. symmetry. apply fdLookup_notin_strong. rewrite Hdom. tauto.
          + rewrite Hdom. reflexivity.
        - rewrite Hdom. left. reflexivity.
        - subst f'. split.
          + move=>k'. destruct (dec_eq k k') as [EQ|NEQ].
            * subst k'. rewrite fdStrongUpdate_eq. subst v'. symmetry. eapply fdLookup_indom_corr.
              reflexivity.
            * erewrite !fdStrongUpdate_neq by assumption. reflexivity.
          + rewrite Hdom /dom /=. f_equal. rewrite /dom /= Hdom.
            rewrite DecEq_refl.
            assert (Hnod := dom_nodup f). rewrite Hdom in Hnod.
            assert (Hfilt1: (filter_dupes [] l') = l').
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

    Section Fold.
      Context {T: Type}.
      Context (Temp: T) (Tstep: K -> V -> T -> T).
      
      Definition fdFold: (K -f> V) -> T :=
        fdRect (fun _ => T) (fun _ _ _ => id) (Temp)
               (fun k v _ _ => Tstep k v).

      Lemma fdFoldEmpty: fdFold fdEmpty = Temp.
      Proof.
        reflexivity.
      Qed.

      Lemma fdRectInner_eqLF l1 f1 l2 f2 (Heq1: dom f1 = l1) (Heq2: dom f2 = l2):
        l1 = l2 -> (forall k, f1 k = f2 k) ->
        fdRectInner (fun _ => T) (fun _ _ _ => id) (Temp) (fun k v _ _ => Tstep k v) l1 f1 Heq1 =
        fdRectInner (fun _ => T) (fun _ _ _ => id) (Temp) (fun k v _ _ => Tstep k v) l2 f2 Heq2.
      Proof.
        move=>Heql Heqf. assert (Heq': dom f2 = l1).
        { now subst l2. }
        revert f1 f2 l2 Heq' Heq1 Heq2 Heql Heqf. induction l1; intros.
        - destruct l2; last discriminate. reflexivity.
        - destruct l2; first discriminate. inversion Heql; subst; clear Heql.
          assert (Hf: exists v, f1 k = Some v /\ f2 k = Some v).
          { destruct (f1 k) as [v|] eqn:EQf.
            - exists v. split; first reflexivity. rewrite -Heqf. assumption.
            - exfalso. apply fdLookup_notin_strong in EQf. apply EQf. rewrite Heq1.
              left. reflexivity. }
          destruct Hf as [v [Heqf1 Heqf2]].
          simpl. f_equal. f_equal.
          + eapply fdLookup_indom_corr in Heqf1. erewrite Heqf1.
            eapply fdLookup_indom_corr in Heqf2. erewrite Heqf2.
            reflexivity.
          + apply IHl1.
            * rewrite /fdStrongUpdate /dom /=. rewrite Heq' DecEq_refl.
              eapply filter_dupes_id. simpl.
              move:(dom_nodup f2). rewrite Heq'. intros Hnd. inversion Hnd; subst. assumption.
            * reflexivity.
            * intros. destruct (dec_eq k k0) as [EQ|NEQ].
              { subst k0. rewrite !fdStrongUpdate_eq. reflexivity. }
              erewrite !fdStrongUpdate_neq by assumption. now apply Heqf.
      Qed.

      Global Instance fdFoldExtF:
        Proper (equal_fd ==> eq) fdFold.
      Proof.
        move=>f1 f2 [Heq Hdom]. rewrite /fdFold /fdRect. eapply fdRectInner_eqLF; assumption.
      Qed.

      Lemma fdFoldAdd f k v:
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

      Lemma fdFoldRedundantRemove f k:
        ~k ∈ (dom f) ->
        fdFold (fdStrongUpdate k None f) = fdFold f.
      Proof.
        move=>Hindom. eapply fdFoldExtF. split.
        - move=>k'. simpl. apply fdLookup_notin_strong in Hindom.
          destruct (dec_eq k k').
          + subst. now rewrite Hindom.
          + reflexivity.
        - rewrite /fdStrongUpdate /dom /= /dom. rewrite /dom in Hindom.
          destruct (filter_dupes [] (findom f)) as [|k' dom'] eqn:Hdom'.
          + reflexivity.
          + destruct (dec_eq k k') as [EQ|NEQ].
            * subst k'. exfalso. apply Hindom. now left.
            * erewrite filter_dupes_id by apply filter_dupes_nodup.
              erewrite filter_dupes_id; first reflexivity. simpl.
              constructor; first assumption.
              rewrite -Hdom'. apply filter_dupes_nodup.
      Qed.

      (* Alternative, more direct formulation of fold. *)
      Definition fdFold'Inner fLookup k: T -> T :=
        fun t => match fLookup k with
                 | Some v => Tstep k v t
                 (* We know this case never happens, but that would be very annoying to make use of here. *)
                 | None => t end.
      Definition fdFold' (f: K -f> V): T :=
        fold_right (fdFold'Inner f) Temp (dom f).

      Global Instance fdFold'ExtF:
        Proper (equal_fd ==> eq) fdFold'.
      Proof.
        move=>f1 f2 [Heq Hdom]. rewrite /fdFold' /fdFold'Inner. apply fold_ext_restr.
          + assumption.
          + reflexivity.
          + move=>k t _. rewrite Heq. reflexivity.
      Qed.


      (* They are equivalent. *)
      Lemma fdFoldBehavior f:
        fdFold f = fdFold' f.
      Proof.
        revert f. elim/fdRect.
        - move=>f1 f2 EQf EQfold. erewrite <-fdFoldExtF by eexact EQf.
          rewrite EQfold. rewrite EQf. reflexivity.
        - reflexivity.
        - move=>k v f Hnin Heq. erewrite fdFoldAdd by assumption.
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

    Section FoldExtStep.
      (* One can change the step function *)
      Context {T: Type} {eqT: relation T} {eqRT: Equivalence eqT}.

      Context (Tstep1 Tstep2: K -> V -> T -> T).
      Context {Tstep1_proper: Proper (eq ==> eq ==> eqT ==> eqT) Tstep1}.
      Context {Tstep2_proper: Proper (eq ==> eq ==> eqT ==> eqT) Tstep2}.
      Context {Tstep_eq: forall k v t, eqT (Tstep1 k v t) (Tstep2 k v t)}.

      Lemma fdFoldExtT:
        forall Temp1 Temp2, eqT Temp1 Temp2 ->
                            forall f, eqT (fdFold Temp1 Tstep1 f) (fdFold Temp2 Tstep2 f).
      Proof.
        move=>Temp1 Temp2 EQemp f.
        rewrite !fdFoldBehavior /fdFold'.
        apply fold_ext.
        - move=>k k' EQk v1 v2 EQv. subst k'. rewrite /fdFold'Inner. destruct (f k).
          + rewrite EQv. reflexivity.
          + assumption.
        - move=>k t. rewrite /fdFold'Inner. destruct (f k); last reflexivity.
          apply Tstep_eq.
        - assumption.
      Qed.
    End FoldExtStep.

    Section FoldExtPerm.        
      (* If the step function is commutative, one can change the finmap. *)
      Context {T: Type} `{Setoid T}.
      Context (Temp: T) (Tstep: K -> V -> T -> T).

      Definition fdStep_comm: Prop :=
        forall (k1 k2:K) (v1 v2:V),
          compose (Tstep k1 v1) (Tstep k2 v2) == compose (Tstep k2 v2) (Tstep k1 v1).

      Context (Tstep_comm: fdStep_comm).

      Global Instance fdFoldExtP {Tstep_proper: Proper (eq ==> equiv ==> equiv ==> equiv) Tstep}:
          Proper (equiv ==> equiv) (fdFold Temp Tstep).
      Proof.
        move=>f1 f2 EQf. rewrite !fdFoldBehavior /fdFold'.
        rewrite /fdFold'. etransitivity; last eapply fold_perm.
        - eapply fold_ext.
          + move=>k k' EQk v1 v2 EQv. subst k'. rewrite /fdFold'Inner.
            destruct (f1 k); last assumption. rewrite EQv. reflexivity.
          + move=>k t. rewrite /fdFold'Inner. specialize (EQf k). destruct (f1 k), (f2 k); try contradiction.
            * simpl in EQf. rewrite EQf. reflexivity.
            * reflexivity.
          + reflexivity.
        - move=>k k' EQk v1 v2 EQv. subst k'. rewrite /fdFold'Inner.
          destruct (f2 k); last assumption. rewrite EQv. reflexivity.
        - move=>v1 v2 t. rewrite /fdFold'Inner /=.
          destruct (f2 v1), (f2 v2); try reflexivity; [].
          apply Tstep_comm.
        - split; last split.
          + apply dom_nodup.
          + apply dom_nodup.
          + move=>k. rewrite !fdLookup_in_strong. specialize (EQf k).
            destruct (f1 k), (f2 k); try contradiction; last tauto; [].
            split; discriminate.
      Qed.
    End FoldExtPerm.

    Section FoldExtPermDist.
      (* The same, up to n-equality. TODO: Figure out a way not to repeat all this. *)
      Context {mV: metric V} {cmV: cmetric V}.
      Context {T: Type} `{cmetric T}.
      Context (Temp: T) (Tstep: K -> V -> T -> T).
      Context (Tstep_comm: fdStep_comm Tstep).
        
      Lemma fdFoldExtP_dist n {Tstep_proper: Proper (eq ==> dist n ==> dist n ==> dist n) Tstep}:
        Proper (dist n ==> dist n) (fdFold Temp Tstep).
      Proof.
        move=>f1 f2 EQf. rewrite !fdFoldBehavior /fdFold'.
        destruct n as [|n]; first exact:dist_bound.
        rewrite /fdFold'. etransitivity; last eapply fold_perm.
        - eapply fold_ext.
          + move=>k k' EQk v1 v2 EQv. subst k'. rewrite /fdFold'Inner.
            destruct (f1 k); last assumption. apply Tstep_proper; reflexivity || assumption.
          + move=>k t. rewrite /fdFold'Inner.
            specialize (EQf k). destruct (f1 k), (f2 k); try (now destruct EQf).
            * simpl in EQf. apply Tstep_proper; reflexivity || assumption.
          + reflexivity.
        - move=>k k' EQk v1 v2 EQv. subst k'. rewrite /fdFold'Inner.
          destruct (f2 k); last assumption. rewrite EQv. reflexivity.
        - move=>v1 v2 t. rewrite /fdFold'Inner /=.
          destruct (f2 v1), (f2 v2); try reflexivity; [].
          apply dist_refl, Tstep_comm.
        - split; last split.
          + apply dom_nodup.
          + apply dom_nodup.
          + move=>k. rewrite !fdLookup_in_strong. specialize (EQf k).
            destruct (f1 k), (f2 k); split; intro; try (assumption || discriminate || contradiction).
      Qed.
                  
    End FoldExtPermDist.

  End Induction.

  Section Compose.
    Context {V : Type} `{eV : Setoid V}.
    Context (op: option V -> option V -> option V).
    Context {op_nongen: op None None = None}.

    Program Definition fdCompose (f1 f2: K -f> V): K -f> V :=
      mkFDbound (fun i => op (f1 i) (f2 i)) (findom f1 ++ findom f2) _.
    Next Obligation.
      move=>k /= Hin. apply in_app_iff.
      destruct (f1 k) eqn:EQf1, (f2 k) eqn:EQf2.
      - left. apply findom_b. rewrite EQf1. discriminate.
      - left. apply findom_b. rewrite EQf1. discriminate.
      - right. apply findom_b. rewrite EQf2. discriminate.
      - contradiction.
    Qed.

    Lemma fdComposeRed (f1 f2: K -f> V) i:
      fdCompose f1 f2 i = op (f1 i) (f2 i).
    Proof.
      reflexivity.
    Qed.

  End Compose.

End FinDom.

(*Arguments fdMap {K cT ord equ preo ord_part compK U V eqT mT cmT pTA pcmU eqT0 mT0 cmT0 pTA0 cmV} _.*)

Section RA.
  Context {I : Type} {S : Type} `{eqI : DecEq I} `{RAS : RA S}.
  Implicit Type (i : I) (s : S) (f g : I -f> S).

  Local Open Scope ra_scope.
  Local Open Scope finmap_scope.
  
  Global Instance ra_type_finprod : Setoid (I -f> S) := _.
  Global Program Instance ra_unit_finprod : RA_unit (I -f> S) :=
    fdMapRaw ra_unit.

  Definition finprod_op (s1 s2: option S) :=
    match s1 with
    | None => s2
    | Some s1 => match s2 with
                   Some s2 => Some (s1 · s2)
                 | None    => Some s1
                 end
    end.
  Global Program Instance ra_op_finprod : RA_op (I -f> S) :=
    fdCompose finprod_op.                                
  Global Instance ra_valid_finprod : RA_valid (I -f> S) :=
    fun f => forall i, match f i with Some s => ra_valid s | None => True end.
  
  Global Instance ra_finprod : RA (I -f> S).
  Proof.
    split; repeat intro.
    - simpl. specialize (H k). specialize (H0 k).
      destruct (x k), (y k), (x0 k), (y0 k); try contradiction; simpl; try reflexivity; try assumption; [].
      simpl in H. simpl in H0. rewrite H H0. reflexivity.
    - simpl. destruct (t1 k), (t2 k), (t3 k); try reflexivity; [].
      simpl. rewrite assoc. reflexivity.
    - simpl. destruct (t1 k), (t2 k); try reflexivity; [].
      simpl. now rewrite comm.
    - simpl. rewrite /fdMap_pre. destruct (t k); last reflexivity.
      simpl. rewrite ra_op_unit. reflexivity.
    - simpl. specialize (H k). rewrite /fdMap_pre.
      destruct (x k), (y k); try (reflexivity || assumption); [].
      simpl in H. simpl. rewrite H. reflexivity.
    - pose (op := fun (os1 os2: option S) =>
                    match os1, os2 with
                    | Some s, Some s' => Some (proj1_sig (ra_unit_mono s s'))
                    | Some s, None    => None
                    | None  , Some s' => Some (ra_unit s')
                    | None  , None    => None end).
      exists (fdCompose op (op_nongen := eq_refl) t t').
      move=>k. simpl. rewrite /fdMap_pre /ra_op /=.
      destruct (t k), (t' k); simpl; try (reflexivity || tauto); [].
      move:(ra_unit_mono s s0)=>[t'' Heq] /=. assumption.
    - simpl. rewrite /fdMap_pre /ra_unit /= /fdMap_pre.
      destruct (t k); last reflexivity.
      apply option_eq_Some, ra_unit_idem.
    - split; rewrite /ra_valid /=; move =>Hval i; specialize (H i); specialize (Hval i); destruct (x i), (y i); try (contradiction || tauto); [|].
      + simpl in H. rewrite -H. assumption.
      + simpl in H. rewrite H. assumption.
    - move:(H i)=>{H}. rewrite /=. destruct (t1 i), (t2 i); simpl; try tauto; [].
      apply ra_op_valid.
  Qed.

  (* The RA order on finmaps is the same as the fpfun order over the RA order *)
  Lemma ra_pord_iff_ext_pord {f g}:
    pord (preoType:=pord_ra) f g <-> pord (preoType:=extOrd_preo) f g.
  Proof.
    split.
    { move => [h Hhf] i. move:(Hhf i)=>{Hhf} /=.
      destruct (f i), (g i), (h i); simpl; try tauto; [|].
      - move=>Heq. exists s1. assumption.
      - move=>Heq. rewrite Heq. reflexivity. }
    move:g f. apply: fdRect.
    - move=>f1 f2 [Heqf _] Hleeq f Hle.
      destruct (Hleeq f).
      + move=>k. rewrite (Heqf k). now apply Hle.
      + exists x. move=>k. rewrite -Heqf. apply H.
    - move=>f Hle. exists (fdEmpty (V:=S)). move=>k. simpl.
      specialize (Hle k). destruct (f k); last reflexivity.
      contradiction Hle.
    - move=>k v f Hnin IH g Hle. destruct (IH (fdStrongUpdate k None g)) as [h Hh]=>{IH}.
      + move=>i. destruct (dec_eq k i) as [EQ|NEQ].
        * subst i. rewrite fdStrongUpdate_eq. exact Logic.I.
        * erewrite fdStrongUpdate_neq by assumption.
          etransitivity; first now apply Hle.
          erewrite fdStrongUpdate_neq by assumption. reflexivity.
      + specialize (Hle k). rewrite fdStrongUpdate_eq in Hle. destruct (g k) eqn:EQg; last first.
        { exists (fdStrongUpdate k (Some v) h). move=>i /= {Hle}. specialize (Hh i). simpl in Hh.
          destruct (dec_eq k i) as [EQ|NEQ].
          - subst i. rewrite EQg. reflexivity.
          - assumption. }
        destruct Hle as [h' Hle].
        exists (fdStrongUpdate k (Some h') h). move=>i /=.
        specialize (Hh i). simpl in Hh. destruct (dec_eq k i) as [EQ|NEQ].
        * subst i. rewrite EQg. simpl. assumption.
        * assumption.
  Qed.
End RA.

Section VIRA.
  Context {I : Type} `{eqI : DecEq I}.
  Context {T: Type} `{raT: RA T}.

  Global Instance vira_finmap: VIRA (I -f> T).
  Proof.
    eexists fdEmpty. move=>i. exact Logic.I.
  Qed.
    
End VIRA.


Section CMRA.
  Context {I : Type} `{eqI : DecEq I}.
  Context {T: Type} `{cmraT: CMRA T}.
  
  Local Open Scope ra_scope.
  Local Open Scope finmap_scope.

  Global Instance ra_finmap_pcm: pcmType (pTA:=pord_ra) (I -f> T).
  Proof.
    split. intros σ ρ σc ρc HC.
    apply ra_pord_iff_ext_pord.
    eapply pcm_respC; first by apply _.
    move=>i. apply ra_pord_iff_ext_pord. by apply: HC.
  Qed.

  Definition finmap_cmra_valid_op (f: I -f> T) n :=
    forall i, match f i with Some s => cmra_valid s n
                        | None => True end.
                            
  Global Program Instance finmap_cmra_valid: CMRA_valid (I -f> T) :=
    fun f => p[(finmap_cmra_valid_op f)].
  Next Obligation.
    move=>i. destruct (f i); last tauto.
    exact: bpred.
  Qed.
  Next Obligation.
    move=>n m Hle /= H i. specialize (H i).
    destruct (f i); last tauto.
    eapply dpred, H. assumption.
  Qed.
    
  Global Instance finmap_cmra : CMRA (I -f> T).
  Proof.
    split.
    - move=>n f1 f2 EQf g1 g2 EQg k.
      destruct n as [|n]; first exact:dist_bound.
      specialize (EQf k). specialize (EQg k). simpl.
      destruct (f1 k), (f2 k), (g1 k), (g2 k); simpl; try (contradiction || assumption || tauto); [].
      simpl in EQf. simpl in EQg. rewrite EQf EQg. reflexivity.
    - move=>n f1 f2 EQf k.
      destruct n as [|n]; first exact:dist_bound.
      specialize (EQf k). rewrite /= /fdMap_pre.
      destruct (f1 k), (f2 k); try (contradiction || assumption); [].
      simpl in EQf. simpl. rewrite EQf. reflexivity.
    - move=>n f1 f2 EQf.
      destruct n as [|n]; first exact:dist_bound.
      move=>m Hle. split; move=>Hval i; specialize (EQf i); specialize (Hval i); destruct (f1 i), (f2 i); simpl; try (contradiction || tauto); [|].
      + simpl in EQf. eapply spredNE, Hval.
        eapply mono_dist; last (now rewrite EQf). omega.
      + simpl in EQf. eapply spredNE, Hval.
        eapply mono_dist; last (now rewrite EQf). omega.
    - move => f1. split => [H|H n] i. 
      + destruct (f1 i) eqn:EQf; last tauto.
        eapply cmra_ra_valid =>n.
        specialize (H n i). rewrite EQf in H. assumption.
      + specialize (H i). destruct (f1 i); last tauto.
        now apply cmra_ra_valid.
    - move=>t1 t2 n H i. move:(H i)=>{H}.
      rewrite /=. destruct (t1 i), (t2 i); simpl; try tauto; [].
      apply cmra_op_valid.
  Qed.

  Section CMRAExt.
    Context {cmraText: CMRAExt T}.

    (* It is crucial for the lower cmra_extend function to be called only once per element
       (or we would need proof irrelevance). So we first define both witnesses at once, and then
       show their projections constitute a finite partial function. *)
    Program Definition finmap_cmra_extend {n} {f1 f11 f12 f2: I -f> T}
            (EQf: f1 = S n = f2) (EQf1: f1 == f11 · f12) i : option T * option T :=
      match f1 i, f2 i with
      | Some t1, Some t2 => match f11 i, f12 i with
                            | Some t11, Some t12 => let E := cmra_extend (S n) t1 t11 t12 t2 _ _ in
                                                    (Some (projT1 E), Some (projT1 (projT2 E)))
                            | Some t11, None     => (Some t2, None)
                            | None    , Some t12 => (None, Some t2)
                            | None    , None     => (None, None) end
      (* Unfortunately, Program does not like us to use a wildcard here. *)
      | Some _ , None    => (None, None)
      | None   , Some _  => (None, None)
      | None   , None    => (None, None) end.
    Next Obligation.
      specialize (EQf i). rewrite -Heq_anonymous -Heq_anonymous0 in EQf.
      exact EQf.
    Qed.
    Next Obligation.
      specialize (EQf1 i). rewrite /ra_op /= -Heq_anonymous -Heq_anonymous1 -Heq_anonymous2 /= in EQf1.
      exact EQf1.
    Qed.

    Program Definition finmap_cmra_extend_t21 {n} {f1 f11 f12 f2: I -f> T}
            (EQf: f1 = S n = f2) (EQf1: f1 == f11 · f12) : I -f> T :=
      mkFDbound (fun i => fst (finmap_cmra_extend EQf EQf1 i)) (findom f1) _.
    Next Obligation.
      move=>k. rewrite -(findom_b f1) /finmap_cmra_extend.
      ddes (f1 k) at 1 3 11 as [v1|] deqn:EQf1v.
      - ddes (f2 k) at 1 3 as [v2|] deqn:EQf2v; last discriminate.
        ddes (f11 k) at 1 3 as [v11|] deqn:EQf11v.
        + ddes (f12 k) at 1 3 as [v12|] deqn:EQf12v; discriminate.
        + ddes (f12 k) at 1 3 as [v12|] deqn:EQf12v; discriminate.
      - ddes (f2 k) at 1 3 as [v2|] deqn:EQf2v; tauto.
    Qed.

    Program Definition finmap_cmra_extend_t22 {n} {f1 f11 f12 f2: I -f> T}
            (EQf: f1 = S n = f2) (EQf1: f1 == f11 · f12) : I -f> T :=
      mkFDbound (fun i => snd (finmap_cmra_extend EQf EQf1 i)) (findom f1) _.
    Next Obligation.
      move=>k. rewrite /findom_approx -(findom_b f1) /finmap_cmra_extend.
      ddes (f1 k) at 1 3 11 as [v1|] deqn:EQf1v.
      - ddes (f2 k) at 1 3 as [v2|] deqn:EQf2v.
        + ddes (f11 k) at 1 3 as [v11|] deqn:EQf11v; last discriminate.
          ddes (f12 k) at 1 3 as [v12|] deqn:EQf12v; discriminate.
        + discriminate.
      - ddes (f2 k) at 1 3 as [v2|] deqn:EQf2v; tauto.
    Qed.

    Global Instance finmap_CMRAExt: CMRAExt (I -f> T).
    Proof.
      intros n f1 f11 f12 f2 EQf EQf1. destruct n.
      { exists (1 f2) f2. split; last exact:dist_bound. now rewrite ra_op_unit. }
      exists (finmap_cmra_extend_t21 EQf EQf1).
      exists (finmap_cmra_extend_t22 EQf EQf1).
      cut (forall i, f2 i ==
                     finprod_op (finmap_cmra_extend_t21 EQf EQf1 i) (finmap_cmra_extend_t22 EQf EQf1 i) /\
                     f11 i = S n = finmap_cmra_extend_t21 EQf EQf1 i /\
                     f12 i = S n = finmap_cmra_extend_t22 EQf EQf1 i).
      { move=>Heq. split; last split.
        - move=>i. specialize (Heq i). tauto.
        - move=>i. specialize (Heq i). tauto.
        - move=>i. specialize (Heq i). tauto. }
      move=>i. rewrite /= /finmap_cmra_extend /=.
      ddes (f1 i) at 1 3 11 19 27 as [v1|] deqn:EQf1v.
      - ddes (f2 i) at 1 3 4 8 12 16 as [v2|] deqn:EQf2v; last first.
        { exfalso. specialize (EQf i). rewrite -EQf1v -EQf2v in EQf. exact EQf. }
        ddes (f11 i) at 1 3 11 19 20 28 as [v11|] deqn:EQf11v.
        + ddes (f12 i) at 1 3 7 11 15 16 as [v12|] deqn:EQf12v; simpl; last first.
          { specialize (EQf1 i). rewrite /ra_op /= -EQf1v -EQf11v -EQf12v /= in EQf1.
            specialize (EQf i). rewrite -EQf1v -EQf2v /= in EQf. split; first reflexivity.
            split; last tauto. rewrite -EQf1. assumption. }
          destruct (cmra_extend (S n) v1 v11 v12 v2
                                (finmap_cmra_extend_obligation_1 n f1 f11 f12 f2 EQf EQf1 i v1 v2
                                                                 EQf1v EQf2v v11 v12 EQf11v EQf12v)
                                (finmap_cmra_extend_obligation_2 n f1 f11 f12 f2 EQf EQf1 i v1 v2
                                                                 EQf1v EQf2v v11 v12 EQf11v EQf12v)) as [t21 [t22 [EQ2 [EQd1 EQd2]]]].
          simpl. split_conjs; assumption.
        + ddes (f12 i) at 1 3 7 11 15 16 as [v12|] deqn:EQf12v; simpl.
          { specialize (EQf1 i). rewrite /ra_op /= -EQf1v -EQf11v -EQf12v /= in EQf1.
            specialize (EQf i). rewrite -EQf1v -EQf2v /= in EQf. split; first reflexivity.
            split; first tauto. rewrite -EQf1. assumption. }
          exfalso. specialize (EQf1 i). rewrite /ra_op /= -EQf1v -EQf11v -EQf12v /= in EQf1. exact EQf1.
      - ddes (f2 i) at 1 3 4 8 12 16 as [v2|] deqn:EQf2v.
        + exfalso. specialize (EQf i). rewrite -EQf1v -EQf2v /= in EQf. exact EQf.
        + simpl. split; first tauto.
          specialize (EQf1 i). rewrite /ra_op /= -EQf1v /= in EQf1.
          destruct (f11 i), (f12 i); contradiction || split; reflexivity.
    Qed.
    
  End CMRAExt.
  
End CMRA.

Section RAMap.
  Context {I : Type} `{CI : DecEq I}.
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
  Context {I : Type} `{CI : DecEq I}.
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
