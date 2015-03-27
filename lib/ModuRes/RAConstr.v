Require Import Ssreflect.ssreflect Ssreflect.ssrfun Omega.
Require Import SPred PreoMet RA Axioms.

Local Open Scope ra_scope.
Local Open Scope predom_scope.

Set Bullet Behavior "Strict Subproofs".

(** These constructions are only for RA, so their equality is also defined locally. *)

(** The exclusive RA. *)
Section Exclusive.
  Context {T: Type} {eqT : Setoid T}.

  Inductive ex: Type :=
  | ex_own: T -> ex
  | ex_unit: ex
  | ex_bot: ex.

  Implicit Types (r s : ex) (t : T).

  Definition ex_eq r s: Prop :=
    match r, s with
      | ex_own t1, ex_own t2 => t1 == t2
      | ex_unit, ex_unit => True
      | ex_bot, ex_bot => True
      | _, _ => False
    end.

  Global Instance ra_equiv_ex : Equivalence ex_eq.
  Proof.
    split.
    - intros [t| |]; simpl; now auto.
    - intros [t1| |] [t2| |]; simpl; now auto.
    - intros [t1| |] [t2| |] [t3| |]; simpl; try now auto.
      + intros ? ?. etransitivity; eassumption.
  Qed.

  Global Program Instance ra_type_ex : Setoid ex :=
    mkType ex_eq.

  Global Instance ex_own_compat : Proper (equiv ==> equiv) ex_own.
  Proof. by move=> t1 t2 EQt. Qed.

  Global Instance ra_unit_ex : RA_unit _ := ex_unit.
  Global Instance ra_op_ex : RA_op _ :=
    fun r s =>
      match r, s with
        | ex_own _, ex_unit => r
        | ex_unit, ex_own _ => s
        | ex_unit, ex_unit   => ex_unit
        | _, _               => ex_bot
      end.
  Global Instance ra_valid_ex : RA_valid _ :=
    fun r => match r with
               | ex_bot => False
               | _      => True
             end.

  Global Instance ra_ex : RA ex.
  Proof.
    split.
    - intros [t1| |] [t2| |] Heqt [t'1| |] [t'2| |] Heqt'; simpl; now auto.
    - intros [s1| |] [s2| |] [s3| |]; reflexivity.
    - intros [s1| |] [s2| |]; reflexivity.
    - intros [s1| |]; reflexivity.
    - intros [t1| |] [t2| |] Heqt; unfold ra_valid; simpl in *; now auto.
    - reflexivity.
    - intros [t1| |] [t2| |]; unfold ra_valid; simpl; now auto.
  Qed.

  Lemma ra_sep_ex {t r} : ↓ex_own t · r -> r == 1.
  Proof. by case: r. Qed.

  Lemma ra_fps_ex_any t {r} (Hr : ↓r) : ex_own t ⇝ r.
  Proof. by move=> f /ra_sep_ex ->; rewrite ra_op_unit2. Qed.

  Lemma ra_fps_ex t t' : ex_own t ⇝ ex_own t'.
  Proof. exact: ra_fps_ex_any. Qed.

  Global Instance ra_can_ex : Cancellative ra_ex.
  Proof.
    case=>[t ||] a b Hv HEq.
    - by rewrite (ra_sep_ex Hv); move: Hv; rewrite -HEq=> /ra_sep_ex->; reflexivity.
    - by move: HEq; rewrite 2!ra_op_unit.
    - by exfalso.
  Qed.
End Exclusive.
Arguments ex T : clear implicits.


Section ExTests.
  Context {T : Type} {eqT : Setoid T}.
  Implicit Types (t : T).

  Goal forall t1 t2, t1 == t2 -> ex_own t1 == ex_own t2.
  Proof. move=> t1 t2 ->. reflexivity. Qed.

  Context {U} `{raU : RA U}.
  Implicit Types (u : U).
  
  Goal forall t1 t2 u, t1 == t2 -> (ex_own t1,u) ⊑ (ex_own t2,u).
  Proof. move=> t1 t2 u ->. reflexivity. Qed.

  Goal forall t u1 u2, u1 == u2 -> (ex_own t,u1) == (ex_own t,u2).
  Proof. move=> t u1 u2 ->. reflexivity. Qed.
End ExTests.

(** The authoritative RA. *)
Section Authoritative.
  Context {T} `{raT : RA T}.

  CoInductive auth := Auth of ex T * T.

  Implicit Types (x : ex T) (g t u : T) (r s : auth).

  Let auth_eq r s : Prop :=
    match r, s with
    | Auth p, Auth p' => p == p'
    end.

  Global Instance ra_equiv_auth : Equivalence auth_eq.
  Proof.
    split.
    - by move=> [p]; rewrite/auth_eq; reflexivity.
    - by move=> [p] [p']; rewrite/auth_eq; symmetry.
    - by move=> [p1] [p2] [p3]; rewrite/auth_eq; transitivity p2.
  Qed.
  Global Instance ra_type_auth : Setoid auth := mkType auth_eq.

  Section Compat.
    Variable R : relation (ex T * T).

    Let RA : relation auth := fun r1 r2 =>
      match r1, r2 with Auth p1, Auth p2 => R p1 p2 end.

    Global Instance auth_compat : Proper(R ==> RA) Auth.
    Proof. by move=> p1 p2 Rp. Qed.
  End Compat.

  Global Instance ra_unit_auth : RA_unit auth := Auth(ex_unit, 1).

  Global Instance ra_op_auth : RA_op auth := fun r s =>
    match r, s with Auth(x, t), Auth(x', t') => Auth(x·x', t·t') end.

  Global Instance ra_valid_auth : RA_valid auth := fun r =>
    match r with
    | Auth(ex_unit, t) => ↓t
    | Auth(ex_own g, t) => ↓g /\ ↓t /\ t ⊑ g
    | Auth(ex_bot, _) => False
    end.

  Global Instance ra_auth : RA auth.
  Proof.
    split.
    - move=> [[x1 t1]] [[x1' t1']] [/= Hx1 Ht1] [[x2 t2]] [[x2' t2']] [/= Hx2 Ht2].
      by rewrite Hx1 Ht1 Hx2 Ht2; split; reflexivity.
    - by move=> [[x1 t1]] [[x2 t2]] [[x3 t3]] /=; split; rewrite assoc; reflexivity.
    - by move=> [[x1 t1]] [[x2 t2]] /=; split; rewrite comm; reflexivity.
    - by move=> [[x t]] /=; split; rewrite ra_op_unit; reflexivity.
    - move=> [[x t]] [[x' t']] [/= Hx Ht].
      rewrite/ra_valid/ra_valid_auth.
      move: Hx; case: x=>[g||]; case: x'=>[g'||] => //= Hg.
      + by rewrite Ht Hg.
      + by rewrite Ht.
    - rewrite/ra_unit/ra_unit_auth/ra_valid/ra_valid_auth; exact: ra_valid_unit.
    - move=> [[x t]] [[x' t']]. rewrite /ra_op/ra_op_auth/ra_valid/ra_valid_auth.
      case: x=>[g||]; case: x'=>[g'||] //=.
      + move=>[Hg [Htv [t'' Ht]]]; split; [done | split; [exact: ra_op_valid Htv |]].
        exists (t'' · t'); by rewrite -assoc [t' · _]comm.
      + move=>[_ [Htv _]]; exact: ra_op_valid Htv.
      + exact: ra_op_valid.
  Qed.

  Lemma ra_sep_auth {t u x u'} :
    ↓Auth(ex_own t, u) · Auth(x, u') -> ↓t /\ x == 1 /\ ↓u · u' /\ u · u' ⊑ t.
  Proof.
    case: x=>[g||]; [done | | done].
    rewrite {1}/ra_valid/ra_valid_auth {1}/ra_op/ra_op_auth.
    by move=> [Ht [HSep HLe]].
  Qed.

  Definition auth_side_cond t u t' : Prop :=
    ↓t · u -> forall tf, t · tf ⊑ t · u -> t' · tf ⊑ t' · u.

  Lemma ra_fps_auth {t u t'} (SIDE : auth_side_cond t u t') (Hu' : ↓t' · u) :
    Auth(ex_own(t · u), t) ⇝ Auth(ex_own(t' · u), t').
  Proof.
    move=> [[xf tf]] /ra_sep_auth [Htu [Hxf [Htf HLe]]].
    rewrite/ra_valid/ra_valid_auth [Auth _ · _]/ra_op/ra_op_auth.
    move: Hxf; case: xf=>[g||] H; [done| clear H |done].	(* i.e., "rewrite Hxf" despite the match. *)
    rewrite {1}/ra_op/ra_op_ex.
    split; first done.
    set LE' := _ ⊑ _; suff HLe': LE'.
    { split; last done; move: Hu'; move: HLe'=>[t'' <-]. exact: ra_op_valid2. }
    exact: SIDE.
  Qed.

  Lemma ra_fps_auth_canc {HC : Cancellative raT} t {u t'} (Hu' : ↓t' · u) :
    Auth(ex_own(t · u), t) ⇝ Auth(ex_own(t' · u), t').
  Proof.
    apply: ra_fps_auth Hu'.
    move=> Hu tf HLe.
    apply: (ra_op_mono (prefl t')).
    exact: ra_cancel_ord HLe.
  Qed.

  Definition ra_local_action (act : T -=> T) : Prop :=
    forall t tf, ↓act t -> ↓t · tf -> act(t · tf) == act t · tf.

  Lemma ra_fps_auth_local {act t u} (HL : ra_local_action act) (Hu' : ↓act t · u) :
    Auth(ex_own(t · u), t) ⇝ Auth(ex_own(act t · u), act t).
  Proof.
    apply: ra_fps_auth (Hu').
    move/(_ t _ (ra_op_valid Hu')): HL => HL {Hu'}.
    move=> Hu tf [w HEq]; exists w.
    move: HEq; rewrite comm -assoc => HEq; rewrite comm -assoc.
    rewrite -(HL _ Hu).
    move: Hu; rewrite -HEq => Hu; rewrite -(HL _ Hu).
    by reflexivity.
  Qed.
End Authoritative.
Arguments auth : clear implicits.
(*
Notation "• g" := (Auth (ex_own g,1)) (at level 48) : ra_scope.
Notation "∘ t" := (Auth (1,t)) (at level 48) : ra_scope.
*)

Section AuthTests.
  Context {T : Type} `{raT : RA T}.
  Implicit Types (x : ex T) (t : T).
  
  Goal forall x t1 t2, t1 == t2 -> Auth(x,t1) == Auth(x,t2).
  Proof. move=> x t1 t2 EQt. rewrite EQt. reflexivity. Qed.

  Goal forall x1 x2 t, x1 == x2 -> Auth(x1,t) == Auth(x2,t).
  Proof. move=> x1 x2 t EQx. rewrite EQx. reflexivity. Qed.
End AuthTests.


Section DecAgreement.
  Context T `{T_ty : Setoid T} (eq_dec : forall x y, {x == y} + {x =/= y}).
  Local Open Scope ra_scope.

  Inductive ra_dagree : Type :=
    | dag_bottom
    | dag_unit
    | dag_inj (t : T).

  Global Instance ra_unit_dagree : RA_unit _ := dag_unit.
  Global Instance ra_valid_dag : RA_valid _ :=
           fun x => match x with dag_bottom => False | _ => True end.
  Global Instance ra_op_dag : RA_op _ :=
    fun x y => match x, y with
               | dag_inj t1, dag_inj t2 =>
                   if eq_dec t1 t2 is left _ then dag_inj t1 else dag_bottom
               | dag_bottom , y => dag_bottom
               | x , dag_bottom => dag_bottom
               | dag_unit, y => y
               | x, dag_unit => x
             end.

  Definition ra_eq_dag (x y: ra_dagree): Prop :=
    match x,y with
      | dag_inj t1, dag_inj t2 => t1 == t2
      | x, y => x = y
    end.


  Global Instance ra_equivalence_agree : Equivalence ra_eq_dag.
  Proof.
    split; intro; intros; destruct x; try (destruct y; try destruct z); simpl; try reflexivity;
    simpl in *; try inversion H; try inversion H0; try rewrite <- H; try rewrite <- H0; try firstorder.
  Qed.
  Global Instance ra_type_dagree : Setoid ra_dagree := mkType ra_eq_dag.
  Global Instance res_dagree : RA ra_dagree.
  Proof.
    split; repeat intro.
    - repeat (match goal with [ x : ra_dagree |- _ ] => destruct x end);
      simpl in *; try reflexivity; try rewrite H; try rewrite H0; try reflexivity;
      try inversion H; try inversion H0; compute;
      destruct (eq_dec t2 t0), (eq_dec t1 t); simpl; auto; exfalso;
      [ rewrite <- H, -> e in c | rewrite -> H, -> e in c; symmetry in c]; contradiction.
    - repeat (match goal with [ x : ra_dagree |- _ ] => destruct x end);
      simpl in *; auto; try reflexivity; compute; try destruct (eq_dec _ _); 
      try reflexivity;
      destruct (eq_dec t0 t), (eq_dec t1 t0), (eq_dec t1 t); simpl; auto; 
      try reflexivity;
      try (rewrite <- e in c; contradiction); now exfalso; eauto.
    - destruct t1, t2; try reflexivity; compute; destruct (eq_dec t0 t), (eq_dec t t0);
      try reflexivity; auto; try contradiction; symmetry in e; contradiction.
    - destruct t; reflexivity.
    - destruct x, y; simpl; firstorder; now inversion H.
    - now constructor.
    - destruct t1, t2; try contradiction; now constructor.
  Qed.

End DecAgreement.

Section Agreement.
  (* This is more complex than above, and it does not require a decidable equality. However, it needs
     a metric. It also comes with a CMRA. *)
  Context T `{T_ty : Setoid T} {mT: metric T}.
  Local Open Scope ra_scope.

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

  Global Instance ra_agree_unit : RA_unit _ := ag_unit.
  Global Instance ra_agree_valid : RA_valid _ :=
    fun x => match x with
             | ag_unit => True
             | ag_inj valid _ _ => sp_full valid
             end.

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
    - firstorder.
    - ra_ag_destr; try firstorder; []. intro n. destruct (H n) as [Hn _]. assumption.
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
    | S n' => fun x y => match x, y with
                        | ag_inj v1 ts1 _, ag_inj v2 ts2 _ =>
                          v1 = n = v2 /\ (forall n'' pv1 pv2, n'' <= n' -> ts1 n'' pv1 = n'' = ts2 n'' pv2)
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
    - intros Hall. ra_ag_destr; last exact I; try (specialize (Hall (S O)); now firstorder); [].
      split.
      + eapply dist_refl. move=> [|n]; first by apply: dist_bound. destruct (Hall (S n)) as [EQ _]. assumption.
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

  Lemma ra_ag_op_dist n:
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

  (* And a complete metric! *)
  Context {cmT: cmetric T}.

  Tactic Notation "cchain_eq" constr(σ) "at" constr(P1) constr(P2) "lvl:" constr(L) :=
    let le1 := fresh in
    let le2 := fresh in
    assert (le1: L <= P1) by omega; assert (le2: L <= P2) by omega;
    match goal with
    | [ σc: cchain σ |- _ ] => move/(_ _ _ _ le1 le2):(σc)
    end; clear le1 le2.

  Tactic Notation "cchain_eleq" constr(σ) "at" constr(P1) constr(P2) "lvl:" constr(L) :=
    let eq := fresh in
    cchain_eq σ at P1 P2 lvl:L =>eq;
      match goal with
      | [ H : _ = σ P1 |- _ ] => rewrite <-H in eq
      | [ H : σ P1 = _ |- _ ] => rewrite ->H in eq
      end;
      match goal with
      | [ H : _ = σ P2 |- _ ] => rewrite <-H in eq
      | [ H : σ P2 = _ |- _ ] => rewrite ->H in eq
      end;
      move:eq.

  Tactic Notation "cchain_discr" constr(σ) constr(P) "at" integer_list(pos) "as" simple_intropattern(pat) "deqn:" ident(EQ) :=
    (generalize (@eq_refl _ (σ P)) as EQ; pattern (σ P) at pos;
     destruct (σ P) as pat; move => EQ);
    last (exfalso; match goal with
                   | [ H : _ = σ (S O) |- _ ] => let EQ2 := fresh in
                                                 cchain_eleq σ at (S O) (P) lvl:(S O)=>EQ2; eapply EQ2; omega
                   end).


  Program Definition ra_ag_vchain (σ: chain ra_agree) {σc: cchain σ} v ts {tsx} {HNE : ag_inj v ts tsx = σ (S O)} : chain SPred :=
    fun i => match σ (S i) with
             | ag_unit => !
             | ag_inj v' _ _ => v'
             end.
  Next Obligation.
    cchain_eleq σ at (S O) (S i) lvl:(S O)=>EQ.
    apply EQ; omega.
  Qed.

  Instance ra_ag_vchain_c (σ: chain ra_agree) {σc: cchain σ} v ts {tsx} {HNE : ag_inj v ts tsx = σ (S O)} : cchain (ra_ag_vchain σ v ts (HNE:=HNE)).
  Proof.
    intros n j m HLe1 HLe2. destruct n as [|n]; first by apply: dist_bound. unfold ra_ag_vchain.
    cchain_discr σ (S j) at 1 3 as [v1 ts1 tsx1|] deqn:EQ1.
    cchain_discr σ (S m) at 1 3 as [v2 ts2 tsx2|] deqn:EQ2.
    cchain_eleq σ at (S j) (S m) lvl:(S n); move=>[EQv _].
    assumption.
  Qed.

  Lemma ra_ag_vchain_compl_n (σ: chain ra_agree) {σc: cchain σ} v ts {tsx} {HNE : ag_inj v ts tsx = σ (S O)} n:
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

  Lemma ra_ag_vchain_ucompl_n (σ: chain ra_agree) {σc: cchain σ} v ts {tsx} {HNE : ag_inj v ts tsx = σ (S O)} n:
    ra_ag_vchain σ v ts (HNE:=HNE) (S n) n ->
    compl (ra_ag_vchain σ v ts (HNE:=HNE)) n.
  Proof.
    move=>pv.
    assert (HTv := conv_cauchy (ra_ag_vchain σ v ts (HNE:=HNE)) (S n) _ (le_refl _)).
    apply HTv in pv; last by omega. assumption.
  Qed.

  Lemma ra_ag_vchain_n (σ: chain ra_agree) {σc: cchain σ} v ts {tsx} {HNE : ag_inj v ts tsx = σ (S O)} n m:
    ra_ag_vchain σ v ts (HNE:=HNE) n m -> forall v' ts' tsx', σ (S n) = ag_inj v' ts' tsx' -> v' m.
  Proof.
    move=>pv v' ts' tsx' EQ. move:pv EQ.
    unfold ra_ag_vchain.
    cchain_discr σ (S n) at 1 3 as [vSn tsSn tsxSSn|] deqn:EQSSn.
    move=>pv EQ. rewrite EQ in EQSSn. injection EQSSn=>{EQSSn EQ}EQ. destruct EQ.
    move=><-. assumption.
  Qed.

  Program Definition ra_ag_tsdiag_n (σ : chain ra_agree) {σc : cchain σ} v ts {tsx} {HNE : ag_inj v ts tsx = σ (S O)} n {pv: compl (ra_ag_vchain σ v ts (HNE:=HNE)) n}: T :=
    match σ (S n) with
    | ag_unit => !
    | ag_inj v' ts' tsx' => ts' n _
    end.
  Next Obligation.
    cchain_eleq σ at (S O) (S n) lvl:(S O)=>EQ.
    apply EQ; omega.
  Qed.
  Next Obligation.
    unfold ra_ag_vchain in pv. move: pv.
    cchain_discr σ (S (S n)) at 1 3 as [vSSn tsSSn tsxSSn|] deqn:EQ; move=>pv.
    cchain_eleq σ at (S n) (S (S n)) lvl:(S n); move=>[EQv _].
    apply EQv; first omega. assumption.
  Qed.

  Lemma ra_ag_tsdiag_n_pi (σ : chain ra_agree) {σc : cchain σ} v ts {tsx1 tsx2} {HNE1 : ag_inj v ts tsx1 = σ (S O)} {HNE2 : ag_inj v ts tsx2 = σ (S O)} n {pv1: compl (ra_ag_vchain σ v ts (HNE:=HNE1)) n} {pv2: compl (ra_ag_vchain σ v ts (HNE:=HNE2)) n}:
    ra_ag_tsdiag_n σ v ts n (HNE:=HNE1) (pv:=pv1) = ra_ag_tsdiag_n σ v ts n (HNE:=HNE2) (pv:=pv2).
  Proof.
    Set Printing Implicit.
    move: HNE1 HNE2 n pv1 pv2. pi tsx2 tsx1=>{tsx2} HNE1 HNE2.
    pi HNE2 HNE1=>{HNE2} n pv1 pv2.
    pi pv2 pv1. reflexivity.
    Unset Printing Implicit.
  Qed.

  Program Definition ra_ag_compl (σ : chain ra_agree) {σc : cchain σ} :=
    match σ (S O) with
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
    ddes (σ (S O)) at 1 3 as [v0 ts0 tsx0|] deqn:EQ1.
    - intros i HLe. destruct (σ i) as [vi |] eqn: EQi; [split| exfalso].
      + assert (HT:=conv_cauchy (ra_ag_vchain σ v0 ts0 (HNE:=ra_ag_compl_obligation_1 σ σc v0 _ _ EQ1))).
        rewrite HT. unfold ra_ag_vchain.
        cchain_discr σ (S i) at 1 3 as [vSi tsSi tsxSi|] deqn:EQSi.
        cchain_eleq σ at (S i) i lvl: (S n); move=>[EQv _]. assumption.
      + move=>j pv1 pv2 HLej.
        assert (HeqH := ra_ag_compl_obligation_1 σ σc v0 ts0 tsx0 EQ1).
        assert (pvc: compl (ra_ag_vchain σ v0 ts0 (HNE:=HeqH)) j).
        { Set Printing Implicit. clear -pv1. unfold compl, sp_cmetric, sp_compl in *. simpl in *.
          erewrite (ProofIrrelevance _ _ HeqH) in pv1. assumption. Unset Printing Implicit. }
        destruct j as [|j]; first by apply: dist_bound.
        unfold ra_ag_tsdiag_n.
        cchain_discr σ (S (S j)) at 1 3 as [vSSj tsSSj tsxSSj|]deqn:EQSSj.
        cchain_eleq σ at (S (S j)) i lvl: (S (S j)); move=>[EQv EQts].
        eapply EQts. omega.
      + cchain_eleq σ at (S O) i lvl:(S O)=>EQ. apply EQ; omega.
    - intros j Hle. 
      cchain_eq σ at (S O) j lvl:(S O). rewrite -EQ1.
      destruct (σ j); simpl; tauto.
  Qed.


  (* And we have a pcmType, too! *)
  Global Instance ra_ag_pcm: pcmType ra_agree.
  Proof.
    split. repeat intro. eapply ra_ag_pord. unfold compl, ra_ag_cmt, ra_ag_compl.
    ddes (ρ (S O)) at 1 3 7 as [ρv ρts|] deqn:Hρ; ddes (σ (S O)) at 1 3 as [σv σts|] deqn:Hσ; last first.
    - reflexivity.
    - simpl. specialize (H (S O)). rewrite ->ra_ag_pord, <-Hρ, <-Hσ in H. exact H.
    - rewrite ra_op_unit. reflexivity.
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
        do 2 eexists. etransitivity; last (etransitivity; first eapply HT).
        * eapply dist_refl. apply equivR. apply ra_ag_tsdiag_n_pi.
        * eapply dist_refl. apply equivR. apply ra_ag_tsdiag_n_pi.
      + intros n (pv1 & pv2 & EQ) pv3.
        etransitivity; last (etransitivity; first eapply HT).
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
  Global Instance ra_ag_cmra : CMRA ra_agree := Build_CMRA _ _ _ _.
  Proof.
    exact ra_ag_op_dist.
  Qed.

  (* Provide a way to get a T out of the agreement again. *)
  Program Definition ra_ag_unInj x {HVal: ↓x}: option T :=
    match x with
    | ag_unit => None
    | ag_inj v ts tsx => Some (ts 2 _)
    end.

  Lemma ra_ag_unInj_dist x y {HVal1: ↓x} {HVal2: ↓y} n: (* The function is dependent, hence no "Proper" can be registered *)
    x = n = y -> ra_ag_unInj x (HVal:=HVal1) = n = ra_ag_unInj y (HVal:=HVal2).
  Proof.
    (* TODO *)
  Abort.

End Agreement.

Section AgreementMap.
  Context {T U: Type} `{cmT: cmetric T} `{cmU: cmetric U}.
  Local Open Scope pumet_scope.

  Program Definition ra_agree_map (f: T -n> U): ra_agree T -m> ra_agree U :=
    m[(fun x => match x with
                | ag_inj v ts => ag_inj U v (compose f ts)
                | ag_unit => ag_unit U
                end)].
  Next Obligation.
    move=> x y EQxy.
    destruct n as [|n]; first by apply: dist_bound.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); try (contradiction EQxy || reflexivity); [].
    destruct EQxy as [Hv Hts]. split; first assumption.
    move=>pv1 pv2. specialize (Hts pv1 pv2). unfold compose. rewrite Hts. reflexivity.
  Qed.
  Next Obligation.
    move=>x y EQxy. apply ra_ag_pord. apply ra_ag_pord in EQxy.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); try (contradiction EQxy || reflexivity); [].
    destruct EQxy as [EQv EQts]. split; first split.
    - intros (pv1 & pv2 & _). assumption.
    - rewrite <-EQv. intros (pv1 & pv2 & EQ). exists pv1 pv2. unfold compose. rewrite EQ. reflexivity.
    - unfold compose. intros [pv1 [pv2 EQ]] pv3. f_equiv. erewrite <-EQts. f_equiv. by eapply ProofIrrelevance.
  Grab Existential Variables.
  { rewrite EQv. assumption. }
  Qed.

  Global Instance ra_agree_map_resp: Proper (equiv ==> equiv) ra_agree_map.
  Proof.
    move=> x1 x2 EQx y.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); last reflexivity.
    split; first reflexivity.
    move=>pv1 pv2. rewrite EQx. unfold compose. repeat f_equiv. eapply ProofIrrelevance.
  Qed.
  Global Instance ra_agree_map_dist n: Proper (dist n ==> dist n) ra_agree_map.
  Proof.
    move=> x1 x2 EQx y.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); last reflexivity.
    destruct n as [|n]; first by apply: dist_bound.
    split; first reflexivity.
    move=>pv1 pv2. rewrite EQx. unfold compose. repeat f_equiv. eapply ProofIrrelevance.
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
    intros pv1 pv2. repeat f_equiv. eapply ProofIrrelevance.
  Qed.
  
  Context {U V: Type} `{cmU: cmetric U} `{cmV: cmetric V}.

  Lemma ra_agree_map_comp (f: T -n> U) (g: U -n> V): 
    (ra_agree_map g) ∘ (ra_agree_map f) == ra_agree_map (g <M< f).
  Proof.
    intros x.
    repeat (match goal with [ x : ra_agree _ |- _ ] => destruct x end); last reflexivity.
    simpl. split; first reflexivity.
    intros pv1 pv2. repeat f_equiv. eapply ProofIrrelevance.
  Qed.
End AgreementMapComp.

Section IndexedProduct.
  (* I is the index type (domain), S the type of the components (codomain) *)
  Context {I : Type} {S : forall (i : I), Type}
          {tyS : forall i, Setoid (S i)}
          {uS : forall i, RA_unit (S i)}
          {opS : forall i, RA_op (S i)}
          {vS : forall i, RA_valid (S i)}
          {raS : forall i, RA (S i)}.
  Local Open Scope ra_scope.

  Definition ra_res_infprod := forall (i : I), S i.

  Implicit Type (i : I) (f g : ra_res_infprod).

  Definition ra_eq_infprod := fun f g => forall i, f i == g i.
  Global Instance ra_equiv_infprod : Equivalence ra_eq_infprod.
  Proof. split; repeat intro; [ | rewrite (H i) | rewrite -> (H i), (H0 i) ]; reflexivity. Qed.

  Global Instance ra_type_infprod : Setoid ra_res_infprod | 15 := mkType ra_eq_infprod. (* low priority, this is a fairly generic type... *)
  Global Instance ra_unit_infprod : RA_unit ra_res_infprod := fun i => 1.
  Global Instance ra_op_infprod : RA_op ra_res_infprod := fun f g i => f i · g i.
  Global Instance ra_valid_infprod : RA_valid ra_res_infprod := fun f => forall i, ↓ (f i).
  Global Instance ra_infprod : RA ra_res_infprod.
  Proof.
    split; repeat intro.
    - exact: ra_op_proper.
    - compute; now rewrite -> (assoc (T := S i) (t1 i) (t2 i) (t3 i)).
    - compute; now rewrite -> (comm (T :=S i) (t1 i) (t2 i)).
    - compute; now rewrite -> (ra_op_unit (RA := raS i) (t := t i)).
    - compute; intros; split; intros; by move/(_ i): H0; rewrite (H i).
    - now eapply (ra_valid_unit (RA := raS i)).
    - eapply (ra_op_valid (RA := raS i)); now eauto.
  Qed.
End IndexedProduct.


Section HomogeneousProduct.
  (* I is the index type (domain), S the type of the components (codomain) *)
  Context {I : Type} {S : Type} `{RA S}.

  Global Instance ra_homprod : RA (forall (i : I), S).
  Proof. now eapply ra_infprod; auto. Qed.
End HomogeneousProduct.
